import JPEG2000.Tier2.Geometry

/-!
# Fast Tier-1: flag-word layout and context look-up tables (T.800 D.3, Tables D.1–D.4)

Plan.md §4 (C3), §5.2 "Tier-1 / EBCOT", §6 item 4 ("one flag word per coefficient with the
8-neighbourhood significance and sign bits pre-merged, context lookup = one table index").
Task 3.4a.

The fast Tier-1 decoder (`JPEG2000.Tier1.Decode`) keeps one `UInt32` flag word per
coefficient. This module fixes the bit layout and builds, from an independent transcription
of Tables D.1–D.3 written over that layout, the look-up tables that turn a flag word into a
context with one array read:

* `zcFor b` — 256 entries per sub-band orientation, indexed by the low byte of the flag word
  (the eight neighbour significance bits): the zero-coding context 0–8 of Table D.1.
* `scLut` — 256 entries indexed by `scIndex f` (the four horizontal/vertical neighbour
  significance bits and their four sign bits): `ctx <<< 1 ||| XORbit` with `ctx` 9–13 of
  Table D.3 and the contributions of Table D.2.
* `mrCtxOf f` — Table D.4 (contexts 14–16) from the `REF` bit and the eight significance
  bits; computed, no table.

`JPEG2000/` does not import `Spec/`; the agreement of every table entry with
`Spec.Tier1.zcContext`, `Spec.Tier1.scContext`/`signContribution` and `Spec.Tier1.mrContext`
is checked exhaustively in `Tests/Tier1Fast.lean`.

## Flag word layout (bit by bit)

| bit | name | meaning |
|---|---|---|
| 0 | `SIG_N`  | north neighbour `(x, y−1)` is significant |
| 1 | `SIG_W`  | west neighbour `(x−1, y)` is significant |
| 2 | `SIG_E`  | east neighbour `(x+1, y)` is significant |
| 3 | `SIG_S`  | south neighbour `(x, y+1)` is significant |
| 4 | `SIG_NW` | north-west neighbour is significant |
| 5 | `SIG_NE` | north-east neighbour is significant |
| 6 | `SIG_SW` | south-west neighbour is significant |
| 7 | `SIG_SE` | south-east neighbour is significant |
| 8 | `NEG_N`  | north neighbour is significant and negative |
| 9 | `NEG_W`  | west neighbour is significant and negative |
| 10 | `NEG_E` | east neighbour is significant and negative |
| 11 | `NEG_S` | south neighbour is significant and negative |
| 12 | `SIG`   | this coefficient is significant (σ) |
| 13 | `NEG`   | this coefficient is negative (meaningful once `SIG`) |
| 14 | `VIS`   | coded in the significance propagation pass of the current bit-plane |
| 15 | `REF`   | has had at least one magnitude refinement (Table D.4 "not first") |
| 16–31 | — | always 0 |

Invariant (what the simulation relation of task 3.6 states): for an interior coefficient,
bits 12–15 are its own `sig`, `sign ∧ sig`, `visited`, `refined`, and bits 0–11 are the
corresponding `sig` / `sig ∧ sign` bits of its neighbours (0 for a neighbour outside the
code-block, as Annex D requires). The decoder maintains bits 0–11 of the eight neighbours on
every significance change, so no neighbour is ever read while coding.

The bit order is chosen so that the zero-coding index is the low byte (`f.toUInt8`) and the
sign-coding index is `(f &&& 0xF) ||| ((f >>> 4) &&& 0xF0)` (bits 0–3, then bits 8–11).
-/

namespace JPEG2000.Tier1

open JPEG2000.Tier2.Geometry (Band)

/-! ## Flag bits -/

/-- Bit 0: the north neighbour is significant. -/
@[inline] def SIG_N : UInt32 := 0x1
/-- Bit 1: the west neighbour is significant. -/
@[inline] def SIG_W : UInt32 := 0x2
/-- Bit 2: the east neighbour is significant. -/
@[inline] def SIG_E : UInt32 := 0x4
/-- Bit 3: the south neighbour is significant. -/
@[inline] def SIG_S : UInt32 := 0x8
/-- Bit 4: the north-west neighbour is significant. -/
@[inline] def SIG_NW : UInt32 := 0x10
/-- Bit 5: the north-east neighbour is significant. -/
@[inline] def SIG_NE : UInt32 := 0x20
/-- Bit 6: the south-west neighbour is significant. -/
@[inline] def SIG_SW : UInt32 := 0x40
/-- Bit 7: the south-east neighbour is significant. -/
@[inline] def SIG_SE : UInt32 := 0x80
/-- Bit 8: the north neighbour is significant and negative. -/
@[inline] def NEG_N : UInt32 := 0x100
/-- Bit 9: the west neighbour is significant and negative. -/
@[inline] def NEG_W : UInt32 := 0x200
/-- Bit 10: the east neighbour is significant and negative. -/
@[inline] def NEG_E : UInt32 := 0x400
/-- Bit 11: the south neighbour is significant and negative. -/
@[inline] def NEG_S : UInt32 := 0x800
/-- Bit 12: this coefficient is significant. -/
@[inline] def SIG : UInt32 := 0x1000
/-- Bit 13: this coefficient is negative. -/
@[inline] def NEG : UInt32 := 0x2000
/-- Bit 14: coded in this bit-plane's significance propagation pass. -/
@[inline] def VIS : UInt32 := 0x4000
/-- Bit 15: refined at least once. -/
@[inline] def REF : UInt32 := 0x8000
/-- The eight neighbour significance bits (0–7). -/
@[inline] def SIG_NBRS : UInt32 := 0xFF

/-! ## Transcription of Tables D.1–D.4 over the flag layout -/

/-- Bit `i` of `n` as `0/1`. -/
def bitOf (n i : Nat) : Nat := n / 2 ^ i % 2

/-- Table D.1, LL and LH columns: context from `ΣH`, `ΣV`, `ΣD`. -/
def zcLLLH (h v d : Nat) : Nat :=
  if h ≥ 2 then 8
  else if h = 1 then (if v ≥ 1 then 7 else if d ≥ 1 then 6 else 5)
  else if v ≥ 2 then 4
  else if v = 1 then 3
  else if d ≥ 2 then 2
  else if d = 1 then 1
  else 0

/-- Table D.1, HH column: context from `ΣH + ΣV` and `ΣD`. -/
def zcHHcol (hv d : Nat) : Nat :=
  if d ≥ 3 then 8
  else if d = 2 then (if hv ≥ 1 then 7 else 6)
  else if d = 1 then (if hv ≥ 2 then 5 else if hv = 1 then 4 else 3)
  else if hv ≥ 2 then 2
  else if hv = 1 then 1
  else 0

/-- Zero-coding context (Table D.1) for orientation `b` and the eight neighbour significance
bits `n` (bits 0–7 of the flag word). HL is the LL/LH column with `ΣH`, `ΣV` exchanged. -/
def zcOf (b : Band) (n : Nat) : Nat :=
  let h := bitOf n 1 + bitOf n 2
  let v := bitOf n 0 + bitOf n 3
  let d := bitOf n 4 + bitOf n 5 + bitOf n 6 + bitOf n 7
  match b with
  | .LL | .LH => zcLLLH h v d
  | .HL => zcLLLH v h d
  | .HH => zcHHcol (h + v) d

/-- Signed contribution of one neighbour: `0` if insignificant, `−1` if negative, `+1`
otherwise. -/
def contribOf (sig neg : Nat) : Int := if sig = 1 then (if neg = 1 then -1 else 1) else 0

/-- Table D.2: the contribution of a pair of neighbours is their summed contributions clamped
to `[−1, 1]`. -/
def pairContrib (a b : Int) : Int := max (-1) (min 1 (a + b))

/-- Sign-coding entry for index `n` of `scIndex`: bits 0–3 = significance of N, W, E, S,
bits 4–7 = their sign bits. Result `ctx * 2 + XORbit` (Table D.3). -/
def scOf (n : Nat) : Nat :=
  let hc := pairContrib (contribOf (bitOf n 1) (bitOf n 5)) (contribOf (bitOf n 2) (bitOf n 6))
  let vc := pairContrib (contribOf (bitOf n 0) (bitOf n 4)) (contribOf (bitOf n 3) (bitOf n 7))
  let (ctx, x) : Nat × Nat :=
    if hc = 1 then (if vc = 1 then (13, 0) else if vc = 0 then (12, 0) else (11, 0))
    else if hc = 0 then (if vc = 1 then (10, 0) else if vc = 0 then (9, 0) else (10, 1))
    else (if vc = 1 then (11, 1) else if vc = 0 then (12, 1) else (13, 1))
  ctx * 2 + x

/-! ## The look-up tables -/

/-- The 256-entry zero-coding table of orientation `b` (index: low byte of the flag word). -/
def zcTable (b : Band) : ByteArray := ⟨Array.ofFn (n := 256) fun i => (zcOf b i.val).toUInt8⟩

/-- Every zero-coding table has 256 entries. -/
theorem zcTable_size (b : Band) : (zcTable b).size = 256 := Array.size_ofFn

/-- Zero-coding table, LL. -/
def zcLL : ByteArray := zcTable .LL
/-- Zero-coding table, HL. -/
def zcHL : ByteArray := zcTable .HL
/-- Zero-coding table, LH. -/
def zcLH : ByteArray := zcTable .LH
/-- Zero-coding table, HH. -/
def zcHH : ByteArray := zcTable .HH

/-- The (precomputed) zero-coding table of orientation `b`. -/
def zcFor : Band → ByteArray
  | .LL => zcLL
  | .HL => zcHL
  | .LH => zcLH
  | .HH => zcHH

/-- `zcFor b` is `zcTable b`. -/
theorem zcFor_eq (b : Band) : zcFor b = zcTable b := by cases b <;> rfl

/-- Every `zcFor b` has 256 entries. -/
theorem zcFor_size (b : Band) : (zcFor b).size = 256 := by rw [zcFor_eq]; exact zcTable_size b

/-- The 256-entry sign-coding table: `ctx <<< 1 ||| XORbit` (Tables D.2, D.3). -/
def scLut : ByteArray := ⟨Array.ofFn (n := 256) fun i => (scOf i.val).toUInt8⟩

/-- `scLut` has 256 entries. -/
theorem scLut_size : scLut.size = 256 := Array.size_ofFn

/-- The sign-coding index of a flag word: neighbour significance bits N, W, E, S (bits 0–3)
followed by their sign bits (bits 8–11 moved to 4–7). -/
@[inline] def scIndex (f : UInt32) : UInt8 :=
  ((f &&& (0xF : UInt32)) ||| ((f >>> (4 : UInt32)) &&& (0xF0 : UInt32))).toUInt8

/-- Zero-coding context of flag word `f` with table `t` (256 entries). -/
@[inline] def zcCtx (t : ByteArray) (ht : t.size = 256) (f : UInt32) : Nat :=
  (t.get f.toUInt8.toNat (by rw [ht]; exact UInt8.toNat_lt _)).toNat

/-- Sign-coding entry `ctx <<< 1 ||| XORbit` of flag word `f`. -/
@[inline] def scEntry (f : UInt32) : UInt8 :=
  scLut.get (scIndex f).toNat (by rw [scLut_size]; exact UInt8.toNat_lt _)

/-- Table D.4: magnitude-refinement context of flag word `f`: 16 if already refined, else 15
with a significant neighbour, else 14. -/
@[inline] def mrCtxOf (f : UInt32) : Nat :=
  if f &&& REF != 0 then 16 else if f &&& SIG_NBRS != 0 then 15 else 14

end JPEG2000.Tier1
