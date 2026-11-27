import JPEG2000.Bytes
import JPEG2000.Header
import Spec.DWT53

/-!
# Fast inverse 5/3 wavelet (in-place lifting on `Int32` planes)

Plan.md §5.2 "DWT", §5.4 (fixed width with a checked slow path), §6 item 5 (row pass, then
column pass over batches of columns); T.800 Annex F.3 (`IDWT`, `2D_SR`, `2D_INTERLEAVE`,
`HOR_SR`, `VER_SR`, `1D_SR`, `1D_EXTR`, `1D_FILTR_5-3R`, equations F-4, F-5, F-6) and
Annex B.5 (resolution rectangles `⌈tc / 2^(NL−r)⌉`).

## Layout (the interface Tier-1 / Tier-2 write into)

The input is one tile-component plane of size `(tcx1 − tcx0) × (tcy1 − tcy0)` holding the
sub-bands in the *Mallat layout* (as OpenJPEG's tile-component buffer): for every level the
resolution rectangle `R = [u0, u1) × [v0, v1)` occupies the top-left `W × H` corner
(`W = u1 − u0`, `H = v1 − v0`); with `sn = ⌈u1/2⌉ − ⌈u0/2⌉` low columns and
`sv = ⌈v1/2⌉ − ⌈v0/2⌉` low rows,

* LL (the next coarser resolution) is at `[0, sn) × [0, sv)`,
* HL at `[sn, W) × [0, sv)`, LH at `[0, sn) × [sv, H)`, HH at `[sn, W) × [sv, H)`,

each band stored from its first band coordinate (`bandRect` of `JPEG2000.Tier2.Geometry`).
Band sample `(bx, by)` of HL at level `nb` therefore sits at plane position
`(sn + bx − hl.x0, by − hl.y0)`, etc. (`Layout` below gives the per-level numbers). After
`idwt53` the plane holds the reconstructed tile-component samples, row-major from
`(tcx0, tcy0)`.

## Algorithm

From the coarsest level to the finest: each row of `R` is loaded *interleaved* into a
scratch buffer (low samples at absolute even positions, high samples at odd ones — the
parity of `u0` decides which comes first), lifted in place (F-5 on even positions, then
F-6 on odd positions, mirrored neighbours at both ends = F-4 extension) and stored back;
then batches of up to 8 columns are loaded row by row (contiguous reads), lifted per column
and stored back.

## Numbers

Cells are `Int32`; each lifting step is computed in `Int64` from `Int32` operands, so it is
exact (`|l + r + 2| < 2^33`); narrowing back to `Int32` is checked (a flag, no branch in the
loop). Analytic bound, for reference: if every input satisfies `|y| ≤ B`, F-5 gives
`|x_even| ≤ B + (2B + 2)/4` and F-6 `|x_odd| ≤ B + |x_even|`, i.e. one 1-D pass grows the
magnitude by at most `2.5B + 2`; with `B < 2^(bitdepth + guard + NL)` (Annex E) an 8-bit,
NL = 5 stream stays far below `2^31`. Whenever any narrowing would overflow, the whole
tile-component is recomputed by the slow path: the `Int` specification `Spec.DWT53.srMulti`
(materialised level by level), saturated to `Int32` at the end. Saturation is harmless for
the decoder: the following stage clamps to the component's bit depth, whose range lies
inside `Int32`.

## Correspondence with the spec

`toDec` reads the Mallat-layout plane as a `Spec.DWT53.Dec` (absolute band coordinates);
the slow path is `Spec.DWT53.srMulti` on it. Proved: the `Int64` lifting steps are exact
(`upd_exact`, `pred_exact`), and the in-place 1-D kernel computes `1D_SR` exactly whenever
its overflow flag stays set (`lift1d_eq_sr1d`, every length, offset and start parity).
Tested, not proved (`Tests/DWT53.lean`): the row/column load–store loops (Mallat layout ↔
interleaved order) and the level composition, i.e. `idwt53Fast = idwt53Spec` on planes.
-/

namespace JPEG2000.DWT53

open JPEG2000.Bytes
open JPEG2000.Header (Rect)

/-- The error location of this module. -/
def loc : Location := .at .dwt

/-- A plane viewed as a flat buffer of exactly `n` cells (the size lives in the type, so
the loops below need no size lemmas; the subtype is erased at run time). -/
abbrev Buf (n : Nat) := { p : Plane // p.width * p.height = n }

/-- Reads cell `i` of a buffer (no run-time bounds check). -/
@[inline] def Buf.get {n : Nat} (b : Buf n) (i : Nat) (h : i < n) : Int32 :=
  b.1.get i (by rw [b.2]; exact h)

/-- Writes cell `i` of a buffer in place (no run-time bounds check). -/
@[inline] def Buf.set {n : Nat} (b : Buf n) (i : Nat) (v : Int32) (h : i < n) : Buf n :=
  ⟨b.1.set i v (by rw [b.2]; exact h), b.2⟩

/-- Row-major index bound: `y < h → x < w → y·w + x < w·h`. -/
theorem idx_lt {x y w h : Nat} (hx : x < w) (hy : y < h) : y * w + x < w * h := by
  have : (y + 1) * w ≤ h * w := Nat.mul_le_mul_right _ hy
  rw [Nat.succ_mul] at this
  rw [Nat.mul_comm w h]; omega

/-! ## 1-D lifting kernel -/

/-- Left neighbour of position `i` with the F-4 mirror at the start: `1` for `i = 0`. -/
@[inline] def lnb (i : Nat) : Nat := if i = 0 then 1 else i - 1

/-- Right neighbour of position `i < n` with the F-4 mirror at the end: `n − 2` for
`i = n − 1`. -/
@[inline] def rnb (n i : Nat) : Nat := if i + 1 < n then i + 1 else i - 1

/-- One lifting pass over cells `[off, off + n)` (`n ≥ 2`), visiting `i, i + 2, …`:
`upd = true` is F-5 (`x −= ⌊(l + r + 2)/4⌋`), `upd = false` is F-6 (`x += ⌊(l + r)/2⌋`),
where `l, r` are the neighbours mirrored at both ends (F-4). `ok` becomes `false` if a
result does not fit in `Int32`. -/
def liftPass {N : Nat} (upd : Bool) (off n : Nat) (hN : off + n ≤ N) (hn : 2 ≤ n)
    (b : Buf N) (i : Nat) (ok : Bool) : Buf N × Bool :=
  if hi : i < n then
    let l := lnb i
    let r := rnb n i
    have hl : l < n := by simp only [l, lnb]; split <;> omega
    have hr : r < n := by simp only [r, rnb]; split <;> omega
    let xl := (b.get (off + l) (by omega)).toInt64
    let xr := (b.get (off + r) (by omega)).toInt64
    let xi := (b.get (off + i) (by omega)).toInt64
    let v : Int64 := if upd then xi - ((xl + xr + 2) >>> 2) else xi + ((xl + xr) >>> 1)
    let w := v.toInt32
    liftPass upd off n hN hn (b.set (off + i) w (by omega)) (i + 2) (ok && w.toInt64 == v)
  else (b, ok)
termination_by n - i

/-- `1D_SR` (F.3.6) in place on cells `[off, off + n)` holding interleaved coefficients
whose first has absolute parity `par` (0 even, 1 odd). Length 1 at an odd position is
halved (`⌊y/2⌋`); length ≥ 2 runs F-5 on the even positions then F-6 on the odd ones. -/
def lift1d {N : Nat} (off n par : Nat) (hN : off + n ≤ N) (b : Buf N) (ok : Bool) :
    Buf N × Bool :=
  if hn : 2 ≤ n then
    let (b, ok) := liftPass true off n hN hn b (par % 2) ok
    liftPass false off n hN hn b ((par + 1) % 2) ok
  else if h1 : n = 1 then
    if par % 2 = 1 then
      (b.set off (b.get off (by omega) >>> 1) (by omega), ok)
    else (b, ok)
  else (b, ok)

/-! ## Row and column passes -/

/-- Source position (in the Mallat layout) of interleaved index `i` of a range starting at
absolute `a0` with `sn` low samples: `i/2` if `a0 + i` is even, else `sn + i/2`. -/
@[inline] def srcIdx (a0 sn i : Nat) : Nat := if (a0 + i) % 2 = 0 then i / 2 else sn + i / 2

/-- `srcIdx` stays in the range `[0, a1 − a0)` when `sn = ⌈a1/2⌉ − ⌈a0/2⌉`. -/
theorem srcIdx_lt {a0 a1 i : Nat} (hi : i < a1 - a0) :
    srcIdx a0 ((a1 + 1) / 2 - (a0 + 1) / 2) i < a1 - a0 := by
  simp only [srcIdx]; split <;> omega

/-- Loads row `y` of the level `[u0, u1)` interleaved into `tmp[0, W)`. -/
def loadRow {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (u0 u1 y : Nat) (hW : u1 - u0 ≤ pw)
    (hy : y < N / pw) (P : Buf N) (hT : u1 - u0 ≤ T) (tmp : Buf T) (i : Nat) : Buf T :=
  if hi : i < u1 - u0 then
    let s := srcIdx u0 ((u1 + 1) / 2 - (u0 + 1) / 2) i
    have hs : s < u1 - u0 := srcIdx_lt hi
    let v := P.get (y * pw + s) (by rw [hN]; exact idx_lt (by omega) hy)
    loadRow pw hN u0 u1 y hW hy P hT (tmp.set i v (by omega)) (i + 1)
  else tmp
termination_by u1 - u0 - i

/-- Stores `tmp[0, W)` to row `y` (positions `[0, W)`). -/
def storeRow {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (W y : Nat) (hW : W ≤ pw)
    (hy : y < N / pw) (tmp : Buf T) (hT : W ≤ T) (P : Buf N) (i : Nat) : Buf N :=
  if hi : i < W then
    let v := tmp.get i (by omega)
    storeRow pw hN W y hW hy tmp hT (P.set (y * pw + i) v (by rw [hN]; exact idx_lt (by omega) hy))
      (i + 1)
  else P
termination_by W - i

/-- `HOR_SR` (F.3.4) on rows `y, …, v1 − v0 − 1` of the level `[u0, u1) × [v0, v1)`. -/
def rowPass {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (u0 u1 H : Nat) (hW : u1 - u0 ≤ pw)
    (hH : H ≤ N / pw) (hT : u1 - u0 ≤ T) (P : Buf N) (tmp : Buf T) (ok : Bool) (y : Nat) :
    Buf N × Buf T × Bool :=
  if hy : y < H then
    let tmp := loadRow pw hN u0 u1 y hW (by omega) P hT tmp 0
    let (tmp, ok) := lift1d 0 (u1 - u0) (u0 % 2) (by omega) tmp ok
    let P := storeRow pw hN (u1 - u0) y hW (by omega) tmp hT P 0
    rowPass pw hN u0 u1 H hW hH hT P tmp ok (y + 1)
  else (P, tmp, ok)
termination_by H - y

/-- Loads, for interleaved row index `i` onwards, the `bw` columns `x, …, x + bw − 1` of the
level `[v0, v1)` into `tmp` (column `c` at `[c·H, c·H + H)`, `H = v1 − v0`); reads are
row-contiguous. -/
def loadCols {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (v0 v1 x bw : Nat)
    (hx : x + bw ≤ pw) (hH : v1 - v0 ≤ N / pw) (hT : bw * (v1 - v0) ≤ T) (P : Buf N)
    (tmp : Buf T) (i c : Nat) : Buf T :=
  if hi : i < v1 - v0 then
    if hc : c < bw then
      let s := srcIdx v0 ((v1 + 1) / 2 - (v0 + 1) / 2) i
      have hs : s < v1 - v0 := srcIdx_lt hi
      let v := P.get (s * pw + (x + c)) (by rw [hN]; exact idx_lt (by omega) (by omega))
      have : c * (v1 - v0) + i < bw * (v1 - v0) := by
        have := idx_lt (x := i) (y := c) (w := v1 - v0) (h := bw) hi hc
        rw [Nat.mul_comm (v1 - v0) bw] at this; exact this
      loadCols pw hN v0 v1 x bw hx hH hT P (tmp.set (c * (v1 - v0) + i) v (by omega)) i (c + 1)
    else loadCols pw hN v0 v1 x bw hx hH hT P tmp (i + 1) 0
  else tmp
termination_by (v1 - v0 - i, bw - c)

/-- Stores the `bw` lifted columns of `tmp` back to plane columns `x, …, x + bw − 1`,
rows `[0, H)`. -/
def storeCols {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (H x bw : Nat)
    (hx : x + bw ≤ pw) (hH : H ≤ N / pw) (hT : bw * H ≤ T) (tmp : Buf T) (P : Buf N)
    (i c : Nat) : Buf N :=
  if hi : i < H then
    if hc : c < bw then
      have : c * H + i < bw * H := by
        have := idx_lt (x := i) (y := c) (w := H) (h := bw) hi hc
        rw [Nat.mul_comm H bw] at this; exact this
      let v := tmp.get (c * H + i) (by omega)
      storeCols pw hN H x bw hx hH hT tmp
        (P.set (i * pw + (x + c)) v (by rw [hN]; exact idx_lt (by omega) (by omega))) i (c + 1)
    else storeCols pw hN H x bw hx hH hT tmp P (i + 1) 0
  else P
termination_by (H - i, bw - c)

/-- Lifts the `bw` columns held in `tmp` (column `c` at `[c·H, c·H + H)`), from `c`. -/
def liftCols {T : Nat} (H par bw : Nat) (hT : bw * H ≤ T) (tmp : Buf T) (ok : Bool)
    (c : Nat) : Buf T × Bool :=
  if hc : c < bw then
    have : c * H + H ≤ bw * H := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
    let (tmp, ok) := lift1d (c * H) H par (by omega) tmp ok
    liftCols H par bw hT tmp ok (c + 1)
  else (tmp, ok)
termination_by bw - c

/-- Width of a column batch. -/
def batch : Nat := 8

/-- `VER_SR` (F.3.5) on columns `x, …, W − 1` of the level `[0, W) × [v0, v1)`, in batches
of up to `batch` columns. -/
def colPass {N T : Nat} (pw : Nat) (hN : N = pw * (N / pw)) (W v0 v1 : Nat) (hW : W ≤ pw)
    (hH : v1 - v0 ≤ N / pw) (hT : batch * (v1 - v0) ≤ T) (P : Buf N) (tmp : Buf T)
    (ok : Bool) (x : Nat) : Buf N × Buf T × Bool :=
  if hx : x < W then
    let bw := min batch (W - x)
    have hbw : bw * (v1 - v0) ≤ T :=
      Nat.le_trans (Nat.mul_le_mul_right _ (Nat.min_le_left _ _)) hT
    have hxb : x + bw ≤ pw := by omega
    let tmp := loadCols pw hN v0 v1 x bw hxb hH hbw P tmp 0 0
    let (tmp, ok) := liftCols (v1 - v0) (v0 % 2) bw hbw tmp ok 0
    let P := storeCols pw hN (v1 - v0) x bw hxb hH hbw tmp P 0 0
    have : 0 < bw := by simp only [bw, batch]; omega
    colPass pw hN W v0 v1 hW hH hT P tmp ok (x + bw)
  else (P, tmp, ok)
termination_by W - x

/-! ## Levels and the entry point -/

/-- The next coarser resolution rectangle: `⌈· / 2⌉` on every coordinate (B-14/B-15). -/
def halfRect (r : Rect) : Rect :=
  { x0 := (r.x0 + 1) / 2, y0 := (r.y0 + 1) / 2, x1 := (r.x1 + 1) / 2, y1 := (r.y1 + 1) / 2 }

/-- The rectangle of resolution `NL − k`: `halfRect` applied `k` times to `tc`. -/
def halfN (tc : Rect) : Nat → Rect
  | 0 => tc
  | k + 1 => halfRect (halfN tc k)

/-- The rectangle of the plane is at least as wide/high as every coarser level. -/
theorem halfN_le (tc : Rect) (k : Nat) :
    (halfN tc k).x1 - (halfN tc k).x0 ≤ tc.x1 - tc.x0 ∧
    (halfN tc k).y1 - (halfN tc k).y0 ≤ tc.y1 - tc.y0 := by
  induction k with
  | zero => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | succ k ih => simp only [halfN, halfRect]; omega

/-- Runs levels `k, k − 1, …, 1` (level `k` rebuilds the rectangle `halfN tc (k − 1)` from
its LL `halfN tc k` and the three detail bands). -/
def levels {N T : Nat} (tc : Rect) (pw : Nat) (hN : N = pw * (N / pw))
    (hpw : tc.x1 - tc.x0 ≤ pw) (hph : tc.y1 - tc.y0 ≤ N / pw)
    (hT : batch * (tc.y1 - tc.y0) ≤ T) (hT2 : tc.x1 - tc.x0 ≤ T) :
    Nat → Buf N → Buf T → Bool → Buf N × Bool
  | 0, P, _, ok => (P, ok)
  | k + 1, P, tmp, ok =>
    let r := halfN tc k
    have hr : r.x1 - r.x0 ≤ tc.x1 - tc.x0 ∧ r.y1 - r.y0 ≤ tc.y1 - tc.y0 := halfN_le tc k
    let (P, tmp, ok) := rowPass pw hN r.x0 r.x1 (r.y1 - r.y0) (by omega) (by omega) (by omega)
      P tmp ok 0
    let (P, tmp, ok) := colPass pw hN (r.x1 - r.x0) r.y0 r.y1 (by omega) (by omega)
      (Nat.le_trans (Nat.mul_le_mul_left _ hr.2) hT) P tmp ok 0
    levels tc pw hN hpw hph hT hT2 k P tmp ok

/-! ## Slow path: the `Int` specification -/

open JPEG2000.Spec.DWT53 (Grid Dec srMulti)

/-- The spec rectangle of a `Rect`. -/
def specRect (r : Rect) : Spec.DWT53.Rect :=
  { u0 := r.x0, u1 := r.x1, v0 := r.y0, v1 := r.y1 }

/-- A plane cell as an `Int` (0 outside the plane or at negative coordinates). -/
def cellInt (p : Plane) (x y : Int) : Int :=
  if 0 ≤ x ∧ 0 ≤ y ∧ x < p.width then
    match p.get? (y.toNat * p.width + x.toNat) with
    | some v => v.toInt
    | none => 0
  else 0

/-- The Mallat-layout plane of tile-component `tc` read as a spec decomposition with `nl`
levels: level `l` (1 … nl) has detail bands at the offsets given by the rectangle
`R = halfN tc (l − 1)` (`sn`, `sv` = size of its LL `halfN tc l`); band coordinates are
absolute (`⌊u0/2⌋ …` for HL/HH columns, `⌈u0/2⌉ …` for LL/LH columns). -/
def toDec (p : Plane) (tc : Rect) (nl : Nat) : Dec :=
  let bands := fun (l : Nat) =>
    let R := halfN tc (l - 1)
    let L := halfN tc l
    let sn : Int := L.x1 - L.x0
    let sv : Int := L.y1 - L.y0
    let hx0 : Int := R.x0 / 2
    let hy0 : Int := R.y0 / 2
    let lx0 : Int := L.x0
    let ly0 : Int := L.y0
    ((⟨fun u v => cellInt p (sn + u - hx0) (v - ly0)⟩ : Grid),
     (⟨fun u v => cellInt p (u - lx0) (sv + v - hy0)⟩ : Grid),
     (⟨fun u v => cellInt p (sn + u - hx0) (sv + v - hy0)⟩ : Grid))
  let L := halfN tc nl
  { ll := ⟨fun u v => cellInt p (u - (L.x0 : Int)) (v - (L.y0 : Int))⟩,
    details := (List.range nl).map fun i => bands (i + 1) }

/-- Saturates an `Int` to the `Int32` range. -/
def sat32 (z : Int) : Int32 :=
  if z < -2147483648 then Int32.ofInt (-2147483648)
  else if 2147483647 < z then Int32.ofInt 2147483647 else Int32.ofInt z

/-- Writes `g (x0 + x) (y0 + y)` (saturated) into every cell of a `w × h` plane. -/
def ofGrid (g : Grid) (x0 y0 : Int) (w h : Nat) : Plane := Id.run do
  let mut out : Buf (w * h) := ⟨Plane.zero w h, rfl⟩
  for hy : y in [0:h] do
    for hx : x in [0:w] do
      out := out.set (y * w + x) (sat32 (g.get (x0 + x) (y0 + y)))
        (idx_lt hx.upper hy.upper)
  return out.1

/-- Slow path: the `Int` specification `Spec.DWT53.srMulti` on `toDec`, saturated to
`Int32`. -/
def idwt53Spec (p : Plane) (tc : Rect) (nl : Nat) : Plane :=
  let g := srMulti (specRect tc) nl (toDec p tc nl)
  ofGrid g tc.x0 tc.y0 p.width p.height

/-- Fast path: in-place lifting; `none` if some intermediate value does not fit `Int32`.
`p` must be `(tc.x1 − tc.x0) × (tc.y1 − tc.y0)`. -/
def idwt53Fast (p : Plane) (tc : Rect) (nl : Nat) : Option Plane :=
  if hw : p.width = tc.x1 - tc.x0 ∧ p.height = tc.y1 - tc.y0 then
    if hz : p.width = 0 ∨ p.height = 0 then some p
    else
      let pw := p.width
      let N := pw * p.height
      have hpw : 0 < pw := by omega
      have hdiv : N / pw = p.height := by simp only [N]; rw [Nat.mul_div_cancel_left _ hpw]
      have hN : N = pw * (N / pw) := by rw [hdiv]
      let T := max pw (batch * p.height)
      let tmp : Buf T := ⟨Plane.zero T 1, Nat.mul_one T⟩
      let (P, ok) := levels tc pw hN (by omega) (by rw [hdiv]; omega)
        (by simp only [T]; rw [← hw.2]; exact Nat.le_max_right _ _)
        (by simp only [T]; omega) nl ⟨p, rfl⟩ tmp true
      if ok then some P.1 else none
  else none

/-- `IDWT` (F.3.1) with the 5/3 reversible filter on one tile-component: `p` holds the
sub-bands of `nl` decomposition levels of the tile-component rectangle `tc` in the Mallat
layout (module doc); the result holds the reconstructed samples. Fast `Int32` lifting,
falling back to the exact `Int` specification (saturated to `Int32`) when an intermediate
value would overflow. Errors when the plane's size differs from `tc`'s. -/
def idwt53 (p : Plane) (tc : Rect) (nl : Nat) : Except Error Plane :=
  if p.width = tc.x1 - tc.x0 ∧ p.height = tc.y1 - tc.y0 then
    match idwt53Fast p tc nl with
    | some q => .ok q
    | none => .ok (idwt53Spec p tc nl)
  else .error (.malformed loc
    s!"DWT plane {p.width}×{p.height} differs from tile-component {tc.x1 - tc.x0}×{tc.y1 - tc.y0}")

/-! ## The 1-D kernel computes `1D_SR` exactly (fast = spec, one dimension) -/

section KernelProof

open JPEG2000.Spec.DWT53 (Sig Sym sr1d ext unupdate unpredict)

/-- `>>> 2` on `Int64` is floor division by 4. -/
private theorem shr2 (x : Int64) : (x >>> 2).toInt = x.toInt / 4 := by
  show (Int64.shiftRight x 2).toInt = _
  simp only [Int64.shiftRight, BitVec.sshiftRight']
  rw [← Int64.toInt_toBitVec]
  show (BitVec.sshiftRight _ _).toInt = _
  rw [BitVec.toInt_sshiftRight, Int64.toInt_toBitVec, Int.shiftRight_eq_div_pow]
  rfl

/-- `>>> 1` on `Int64` is floor division by 2. -/
private theorem shr1 (x : Int64) : (x >>> 1).toInt = x.toInt / 2 := by
  show (Int64.shiftRight x 1).toInt = _
  simp only [Int64.shiftRight, BitVec.sshiftRight']
  rw [← Int64.toInt_toBitVec]
  show (BitVec.sshiftRight _ _).toInt = _
  rw [BitVec.toInt_sshiftRight, Int64.toInt_toBitVec, Int.shiftRight_eq_div_pow]
  rfl

/-- `>>> 1` on `Int32` is floor division by 2. -/
private theorem shr1_32 (x : Int32) : (x >>> 1).toInt = x.toInt / 2 := by
  show (Int32.shiftRight x 1).toInt = _
  simp only [Int32.shiftRight, BitVec.sshiftRight']
  rw [← Int32.toInt_toBitVec]
  show (BitVec.sshiftRight _ _).toInt = _
  rw [BitVec.toInt_sshiftRight, Int32.toInt_toBitVec, Int.shiftRight_eq_div_pow]
  rfl

/-- `bmod 2^64` is the identity on small integers. -/
private theorem bm64 (z : Int) (h1 : -2^62 ≤ z) (h2 : z < 2^62) : z.bmod (2^64) = z := by
  apply Int.bmod_eq_of_le <;> omega

/-- The `Int64` F-5 step on `Int32` operands is exact (no `Int64` overflow). -/
theorem upd_exact (a b c : Int32) :
    (c.toInt64 - ((a.toInt64 + b.toInt64 + 2) >>> 2)).toInt
      = c.toInt - (a.toInt + b.toInt + 2) / 4 := by
  have ha1 := a.toInt_lt; have ha2 := a.le_toInt
  have hb1 := b.toInt_lt; have hb2 := b.le_toInt
  have hc1 := c.toInt_lt; have hc2 := c.le_toInt
  rw [Int64.toInt_sub, shr2, Int64.toInt_add, Int64.toInt_add, Int32.toInt_toInt64,
    Int32.toInt_toInt64, Int32.toInt_toInt64]
  have h2 : (2 : Int64).toInt = 2 := rfl
  rw [h2, bm64 (a.toInt + b.toInt) (by omega) (by omega),
    bm64 (a.toInt + b.toInt + 2) (by omega) (by omega)]
  rw [bm64 _ (by omega) (by omega)]

/-- The `Int64` F-6 step on `Int32` operands is exact (no `Int64` overflow). -/
theorem pred_exact (a b c : Int32) :
    (c.toInt64 + ((a.toInt64 + b.toInt64) >>> 1)).toInt = c.toInt + (a.toInt + b.toInt) / 2 := by
  have ha1 := a.toInt_lt; have ha2 := a.le_toInt
  have hb1 := b.toInt_lt; have hb2 := b.le_toInt
  have hc1 := c.toInt_lt; have hc2 := c.le_toInt
  rw [Int64.toInt_add, shr1, Int64.toInt_add, Int32.toInt_toInt64, Int32.toInt_toInt64,
    Int32.toInt_toInt64]
  rw [bm64 (a.toInt + b.toInt) (by omega) (by omega)]
  rw [bm64 _ (by omega) (by omega)]

/-- A checked narrowing keeps the value. -/
theorem narrow_exact (v : Int64) (h : v.toInt32.toInt64 = v) : v.toInt32.toInt = v.toInt := by
  rw [← Int32.toInt_toInt64, h]

/-- Reading a buffer cell after a write. -/
theorem Buf.get_set {N : Nat} (b : Buf N) (i : Nat) (v : Int32) (h : i < N) (j : Nat)
    (hj : j < N) : (b.set i v h).get j hj = if i = j then v else b.get j hj := by
  by_cases hij : i = j
  · subst hij
    simp only [Buf.get, Buf.set, ↓reduceIte]
    exact Plane.get_set_self _ _ _ _ _
  · simp only [Buf.get, Buf.set, hij, ↓reduceIte]
    exact Plane.get_set_ne _ _ _ _ _ _ hij

/-- The value one lifting pass writes at position `k` from the values `g`. -/
def passVal (upd : Bool) (n : Nat) (g : Nat → Int) (k : Nat) : Int :=
  if upd then g k - (g (lnb k) + g (rnb n k) + 2) / 4 else g k + (g (lnb k) + g (rnb n k)) / 2

/-- The accumulated flag only goes from `true` to `false`. -/
theorem liftPass_ok {N : Nat} (upd : Bool) (off n : Nat) (hN : off + n ≤ N) (hn : 2 ≤ n)
    (b : Buf N) (i : Nat) (ok : Bool) (h : (liftPass upd off n hN hn b i ok).2 = true) :
    ok = true := by
  rw [liftPass] at h
  split at h
  · have := liftPass_ok upd off n hN hn _ _ _ h
    simp only [Bool.and_eq_true] at this
    exact this.1
  · exact h
termination_by n - i

/-- One lifting pass, when its flag stays `true`, writes `passVal` (computed from the
values before the pass) at every position of its parity class and leaves the others. -/
theorem liftPass_spec {N : Nat} (upd : Bool) (off n : Nat) (hN : off + n ≤ N) (hn : 2 ≤ n)
    (g : Nat → Int) (b : Buf N) (i : Nat) (ok : Bool)
    (H : ∀ k (hk : k < n), (b.get (off + k) (by omega)).toInt =
      if k % 2 = i % 2 ∧ k < i then passVal upd n g k else g k)
    (hok : (liftPass upd off n hN hn b i ok).2 = true) :
    ∀ k (hk : k < n), ((liftPass upd off n hN hn b i ok).1.get (off + k) (by omega)).toInt =
      if k % 2 = i % 2 then passVal upd n g k else g k := by
  rw [liftPass] at hok ⊢
  split
  · rename_i hi
    simp only [hi, ↓reduceDIte] at hok
    have hok0 := liftPass_ok upd off n hN hn _ _ _ hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok0
    have hrec := liftPass_spec upd off n hN hn g _ (i + 2) _ ?_ hok
    · intro k hk
      rw [hrec k hk]
      simp only [Nat.add_mod_right]
    · intro k hk
      rw [Buf.get_set]
      by_cases hki : off + i = off + k
      · have hk' : k = i := by omega
        subst hk'
        simp only [↓reduceIte, Nat.add_mod_right, Nat.lt_add_right_iff_pos, and_self,
          show 0 < 2 by omega]
        rw [narrow_exact _ hok0.2]
        have hl := H (lnb k) (by unfold lnb; split <;> omega)
        have hr := H (rnb n k) (by unfold rnb; split <;> omega)
        have hc := H k hk
        have hpl : ¬ (lnb k % 2 = k % 2 ∧ lnb k < k) := by unfold lnb; split <;> omega
        have hpr : ¬ (rnb n k % 2 = k % 2 ∧ rnb n k < k) := by unfold rnb; split <;> omega
        simp only [hpl, hpr, Nat.lt_irrefl, and_false, ↓reduceIte] at hl hr hc
        cases upd
        · simp only [Bool.false_eq_true, ↓reduceIte, passVal]
          rw [pred_exact, hl, hr, hc]
        · simp only [↓reduceIte, passVal]
          rw [upd_exact, hl, hr, hc]
      · simp only [hki, ↓reduceIte]
        rw [H k hk]
        have hne : k ≠ i := by omega
        by_cases hp : k % 2 = i % 2
        · have : k < i ↔ k < i + 2 := by omega
          simp only [hp, Nat.add_mod_right, true_and, this]
        · simp only [hp, Nat.add_mod_right, false_and]
  · rename_i hi
    intro k hk
    rw [H k hk]
    by_cases hp : k % 2 = i % 2
    · simp only [hp, true_and, show k < i by omega, ↓reduceIte]
    · simp only [hp, false_and, ↓reduceIte]
termination_by n - i

/-- `unupdate` preserves the symmetries. -/
theorem unupdate_sym {i0 L : Int} {f : Sig} (h : Sym i0 L f) : Sym i0 L (unupdate f) := by
  obtain ⟨hm, hp⟩ := h
  constructor
  · intro j
    simp only [unupdate]
    have e1 : 2 * i0 - j - 1 = 2 * i0 - (j + 1) := by omega
    have e2 : 2 * i0 - j + 1 = 2 * i0 - (j - 1) := by omega
    have hpar : (2 * i0 - j) % 2 = 0 ↔ j % 2 = 0 := by omega
    rw [e1, e2, hm, hm, hm]
    by_cases hj : j % 2 = 0
    · simp only [hj, hpar.mpr hj, ↓reduceIte]; omega
    · have : ¬ (2 * i0 - j) % 2 = 0 := fun h => hj (hpar.mp h)
      simp only [hj, this, ↓reduceIte]
  · intro j
    simp only [unupdate]
    have e1 : j + 2 * L - 1 = (j - 1) + 2 * L := by omega
    have e2 : j + 2 * L + 1 = (j + 1) + 2 * L := by omega
    have hpar : (j + 2 * L) % 2 = 0 ↔ j % 2 = 0 := by omega
    rw [e1, e2, hp, hp, hp]
    by_cases hj : j % 2 = 0
    · simp only [hj, hpar.mpr hj, ↓reduceIte]
    · have : ¬ (j + 2 * L) % 2 = 0 := fun h => hj (hpar.mp h)
      simp only [hj, this, ↓reduceIte]

/-- For a symmetric signal, the left neighbour of position `k` is the cell `lnb k`. -/
theorem sym_left {i0 : Int} {n : Nat} {f : Sig} (hf : Sym i0 ((n : Int) - 1) f)
    (k : Nat) (hk : k < n) : f (i0 + k - 1) = f (i0 + (lnb k : Nat)) := by
  unfold lnb
  split
  · rename_i h0
    subst h0
    rw [← hf.1 (i0 + ((0 : Nat) : Int) - 1)]; congr 1; omega
  · congr 1; omega

/-- For a symmetric signal, the right neighbour of position `k < n` is the cell `rnb n k`. -/
theorem sym_right {i0 : Int} {n : Nat} {f : Sig} (hf : Sym i0 ((n : Int) - 1) f) (hn : 2 ≤ n)
    (k : Nat) (hk : k < n) : f (i0 + k + 1) = f (i0 + (rnb n k : Nat)) := by
  unfold rnb
  split
  · congr 1; omega
  · rename_i h
    have hk' : k = n - 1 := by omega
    subst hk'
    have e1 := hf.2 (i0 + ((n - 1 : Nat) : Int) + 1 - 2 * ((n : Int) - 1))
    rw [show i0 + ((n - 1 : Nat) : Int) + 1 - 2 * ((n : Int) - 1) + 2 * ((n : Int) - 1)
      = i0 + ((n - 1 : Nat) : Int) + 1 by omega] at e1
    rw [e1, ← hf.1]
    congr 1; omega

/-- **Fast = spec, 1-D kernel.** If `lift1d` keeps its flag, every cell holds exactly
`1D_SR` (`Spec.DWT53.sr1d`) of the input cells, for every length and every absolute start
`i0` of parity `par`. -/
theorem lift1d_eq_sr1d {N : Nat} (off n par : Nat) (hN : off + n ≤ N) (b : Buf N) (ok : Bool)
    (i0 : Int) (hpar : i0 % 2 = (par % 2 : Nat)) (y : Sig)
    (hy : ∀ k (hk : k < n), (b.get (off + k) (by omega)).toInt = y (i0 + k))
    (hok : (lift1d off n par hN b ok).2 = true) :
    ∀ k (hk : k < n), ((lift1d off n par hN b ok).1.get (off + k) (by omega)).toInt =
      sr1d i0 (i0 + n) y (i0 + k) := by
  intro k hk
  by_cases hn : 2 ≤ n
  · simp only [lift1d, hn, ↓reduceDIte] at hok ⊢
    -- Pass 1 (F-5 on the even class), then pass 2 (F-6 on the odd class).
    let g : Nat → Int := fun m => y (i0 + m)
    let s1 := liftPass true off n hN hn b (par % 2) ok
    have hok1 : s1.2 = true := liftPass_ok false off n hN hn _ _ _ hok
    have H1 := liftPass_spec true off n hN hn g b (par % 2) ok (by
      intro m hm; rw [hy m hm]
      have : ¬ (m % 2 = par % 2 % 2 ∧ m < par % 2) := by omega
      simp only [this, ↓reduceIte, g]) hok1
    let g2 : Nat → Int := fun m => if m % 2 = par % 2 % 2 then passVal true n g m else g m
    have H2 := liftPass_spec false off n hN hn g2 s1.1 ((par + 1) % 2) s1.2 (by
      intro m hm; rw [H1 m hm]
      have : ¬ (m % 2 = (par + 1) % 2 % 2 ∧ m < (par + 1) % 2) := by omega
      simp only [this, ↓reduceIte, g2]) hok
    rw [H2 k hk]
    -- The spec side.
    have hne : ¬ i0 + (n : Int) ≤ i0 := by omega
    have hn1 : ¬ i0 + (n : Int) = i0 + 1 := by omega
    have hl : i0 + 2 ≤ i0 + (n : Int) := by omega
    simp only [sr1d, hne, hn1, ↓reduceIte]
    have hE := JPEG2000.Spec.DWT53.ext_sym hl y
    have hU := unupdate_sym hE
    rw [show i0 + (n : Int) - i0 - 1 = (n : Int) - 1 by omega] at hE hU
    have hEk : ∀ m, m < n → ext i0 (i0 + n) y (i0 + m) = g m := by
      intro m hm
      simp only [ext, g]
      rw [JPEG2000.Spec.DWT53.pse_id (by omega) (by omega)]
    -- Values of `unupdate (ext y)` on the even class.
    have hUk : ∀ m, m < n → m % 2 = par % 2 →
        unupdate (ext i0 (i0 + n) y) (i0 + m) = passVal true n g m := by
      intro m hm hpm
      have hev : (i0 + (m : Int)) % 2 = 0 := by omega
      simp only [unupdate, hev, ↓reduceIte, passVal]
      rw [show i0 + (m : Int) - 1 = i0 + m - 1 from rfl, sym_left hE m hm,
        sym_right hE hn m hm, hEk m hm, hEk (lnb m) (by unfold lnb; split <;> omega),
        hEk (rnb n m) (by unfold rnb; split <;> omega)]
    by_cases hpk : k % 2 = (par + 1) % 2 % 2
    · -- odd position: F-6
      have hod : (i0 + (k : Int)) % 2 = 1 := by omega
      simp only [hpk, ↓reduceIte, passVal, Bool.false_eq_true, unpredict, hod]
      have hkc : ¬ k % 2 = par % 2 % 2 := by omega
      have hl2 : lnb k % 2 = par % 2 % 2 := by unfold lnb; split <;> omega
      have hr2 : rnb n k % 2 = par % 2 % 2 := by unfold rnb; split <;> omega
      have hodd : ¬ (i0 + (k : Int)) % 2 = 0 := by omega
      simp only [g2, hkc, hl2, hr2, ↓reduceIte]
      rw [sym_left hU k hk, sym_right hU hn k hk,
        hUk (lnb k) (by unfold lnb; split <;> omega) (by omega),
        hUk (rnb n k) (by unfold rnb; split <;> omega) (by omega)]
      simp only [unupdate, hodd, ↓reduceIte, hEk k hk]
    · -- even position: F-5 only
      have hev : (i0 + (k : Int)) % 2 = 0 := by omega
      have hkc : k % 2 = par % 2 % 2 := by omega
      simp only [↓reduceIte, g2, hkc, unpredict, show ¬ (i0 + (k : Int)) % 2 = 1 by omega,
        show ¬ (par % 2 % 2 = (par + 1) % 2 % 2) by omega]
      rw [hUk k hk (by omega)]
  · -- lengths 0 and 1
    have hn' : n = 1 := by omega
    subst hn'
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [sr1d, ↓reduceIte, show i0 + ((1 : Nat) : Int) = i0 + 1 by omega]
    simp only [lift1d, show ¬ 2 ≤ 1 by omega, ↓reduceDIte]
    have hy0 := hy 0 (by omega)
    simp only [Nat.add_zero] at hy0
    simp only [Nat.add_zero, show ¬ i0 + 1 ≤ i0 by omega, ↓reduceIte]
    by_cases hp : par % 2 = 1
    · have : ¬ i0 % 2 = 0 := by omega
      simp only [hp, ↓reduceIte, this, Buf.get_set]
      rw [shr1_32, hy0]
    · have : i0 % 2 = 0 := by omega
      simp only [hp, ↓reduceIte, this]
      rw [hy0]

end KernelProof

end JPEG2000.DWT53
