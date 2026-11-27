import Spec.Resources.TileColorLoops
import Spec.Resources.TileArithmetic
import Spec.NativeResources
import Spec.NativePlacement
import Spec.TileDispatch
import Spec.Resources.HeaderWork

/-!
# Native tile colour and placement charges (Plan.md §§3–5, 7, S3; T.800 B.2–3, G.1–3)

The meters price visits to cells, rows and component descriptors, including the
entered prefix on error. A compact raster slot costs four payload bytes. A wide
integer slot costs the parameter `B`, permitting a separate representation and
operand-width model. Descriptor slots cost one unit. These are logical raster
and vector charges; runtime object headers, allocator capacity and bit-operation
timings require a machine model. Wavelet reconstruction produces the retained
inputs. JP2 mapping consumes the completed codestream image in a later stage.
-/

namespace JPEG2000.Spec.Resources.TileColorPlacement

open JPEG2000.Header JPEG2000.Bytes JPEG2000.NativeOutput
open JPEG2000.Tier2.Geometry (TileCompGeom rectArea)
open JPEG2000.TileDispatch (Spatial)
open JPEG2000.IrreversibleDispatch (pack packRows)

/-- Native raster domain before G.1. -/
def area (s : Source) := s.width * s.height

/-- All pre-colour rasters in component order, including the passthrough tail. -/
def retained (ps : Array Spatial) := (ps.toList.map (fun p => area p.source)).sum

private abbrev IPlane := JPEG2000.IrreversibleDispatch.Spatial

private theorem spatial_area (s : IPlane) : rectArea s.rect = area s.source := by
  cases s with
  | compact r f p hw hh => simp only [area, JPEG2000.IrreversibleDispatch.Spatial.source, JPEG2000.IrreversibleDispatch.Spatial.rect, rectArea, Source.width, Source.height, hw, hh]
  | wide => rfl

private def optBind {α β : Type} (x : Option α × Nat) (f : α → Option β × Nat) :
    Option β × Nat :=
  match x.1 with
  | none => (none,x.2)
  | some a => let y := f a; (y.1,x.2+y.2)

private theorem opt_value {α β : Type} (x : Option α × Nat) (f : α → Option β × Nat) :
    (optBind x f).1 = x.1.bind (fun a => (f a).1) := by
  cases x with | mk x n => cases x <;> rfl

private theorem opt_bound {α β : Type} (x : Option α × Nat) (f : α → Option β × Nat)
    (a b : Nat) (hx : x.2 ≤ a) (hf : ∀ v, (f v).2 ≤ b) : (optBind x f).2 ≤ a+b := by
  unfold optBind
  split
  · omega
  · exact Nat.add_le_add hx (hf _)

/-- One attempted channel pack reserves the entire zero plane, even if the
first value overflows. Each evaluated cell pays for its row, predecessor loads
and a potential store. The zero fill pushes four bytes per slot. -/
def measurePack (r : Rect) (F inputs : Nat) (f : Nat → Int) : Option IPlane × Nat :=
  (pack r F f, 8*rectArea r + (2+inputs)*packVisits f (rectArea r))

private theorem pack_bound (r : Rect) (F reads : Nat) (f : Nat → Int) (h : reads ≤ 3) :
    (measurePack r F reads f).2 ≤ 13*rectArea r := by
  have hc := (packRows_work f (rectArea r) (Nat.le_refl _) ⟨Plane.zero r.width r.height,rfl⟩).1
  have hm := Nat.mul_le_mul (show 2+reads ≤ 5 by omega) hc
  dsimp only [measurePack]
  omega

/-- Evaluate the three separate row traversals of compact ICT in decoder order.
Failure of green retains red's charge; failure of blue retains both predecessors. -/
def compactMeter (y cb cr : IPlane) : Option (IPlane × IPlane × IPlane) × Nat :=
  match y,cb,cr with
  | .compact .., .compact .., .compact .. =>
    optBind (measurePack y.rect y.bits 2 fun i => JPEG2000.WideICT.red (y.fixed i) (cr.fixed i)) fun r =>
    optBind (measurePack cb.rect y.bits 3 fun i => JPEG2000.WideICT.green (y.fixed i) (cb.fixed i) (cr.fixed i)) fun g =>
    optBind (measurePack cr.rect y.bits 2 fun i => JPEG2000.WideICT.blue (y.fixed i) (cb.fixed i)) fun b =>
    (some (r,g,b),0)
  | _,_,_ => (none,0)

/-- Compact ICT counts every attempted pack, for all successful and failing prefixes. -/
theorem compactICT_work (y cb cr : IPlane) :
    (compactMeter y cb cr).1 = JPEG2000.IrreversibleDispatch.compactICT y cb cr ∧
    (compactMeter y cb cr).2 ≤ 13*(rectArea y.rect + rectArea cb.rect + rectArea cr.rect) := by
  cases y <;> cases cb <;> cases cr <;> try exact ⟨rfl,Nat.zero_le _⟩
  constructor
  · simp only [compactMeter,opt_value,measurePack,JPEG2000.IrreversibleDispatch.compactICT,bind,pure,
      Option.bind]
  · dsimp only [compactMeter]
    calc
      _ ≤ 13*rectArea _ + (13*rectArea _ + (13*rectArea _ + 0)) :=
        opt_bound _ _ _ _ (pack_bound _ _ _ _ (by decide)) fun _ =>
        opt_bound _ _ _ _ (pack_bound _ _ _ _ (by decide)) fun _ =>
        opt_bound _ _ _ _ (pack_bound _ _ _ _ (by decide)) fun _ => Nat.le_refl 0
      _ = _ := by omega

/-- Promotion in `Spatial.toWide` reads one packed cell and constructs one
integer-vector cell. Already-wide peers share their pre-colour backing. -/
def promotion (B : Nat) : IPlane → Nat
  | .compact r .. => (2+B)*rectArea r
  | .wide _ => 0

private theorem promotion_le (B : Nat) (p : IPlane) : promotion B p ≤ (2+B)*rectArea p.rect := by
  cases p <;> first | exact Nat.le_refl _ | exact Nat.zero_le _

private def promoteMeter (B : Nat) : IPlane → JPEG2000.WideICT.Component × Nat
  | .wide p => (p,0)
  | .compact r f p hw hh =>
    let m := tabulate (N := rectArea r) fun i => (p.get i.val (by rw [hw,hh]; exact i.isLt)).toInt
    (⟨⟨r,m.1⟩,f⟩,(2+B)*m.2)

private theorem promote_work (B : Nat) (s : IPlane) : promoteMeter B s = (s.toWide,promotion B s) := by
  cases s with
  | wide => rfl
  | compact => simp only [promoteMeter,tabulate_work]; rfl

private def matrix (B : Nat) (y cb cr : JPEG2000.WideICT.Component)
    (h : JPEG2000.WideReversible.SameShape y.rect cb.rect cr.rect) :=
  have hb : rectArea cb.rect = rectArea y.rect := by simp only [rectArea,h.1,h.2.1]
  have hr : rectArea cr.rect = rectArea y.rect := by simp only [rectArea,h.2.2.1,h.2.2.2]
  let red := tabulate fun i : Fin (rectArea y.rect) =>
    JPEG2000.WideICT.red y.samples[i] (cr.samples[i.val]'(by simpa only [hr] using i.isLt))
  let green := tabulate fun i : Fin (rectArea cb.rect) =>
    JPEG2000.WideICT.green (y.samples[i.val]'(by simpa only [hb] using i.isLt)) cb.samples[i]
      (cr.samples[i.val]'(by rw [hr,← hb]; exact i.isLt))
  let blue := tabulate fun i : Fin (rectArea cr.rect) =>
    JPEG2000.WideICT.blue (y.samples[i.val]'(by simpa only [hr] using i.isLt))
      (cb.samples[i.val]'(by rw [hb,← hr]; exact i.isLt))
  let out : JPEG2000.WideICT.Component × JPEG2000.WideICT.Component × JPEG2000.WideICT.Component :=
    (⟨⟨y.rect,red.1⟩,y.fracBits⟩,⟨⟨cb.rect,green.1⟩,y.fracBits⟩,⟨⟨cr.rect,blue.1⟩,y.fracBits⟩)
  (out,(4+B)*red.2 + (5+B)*green.2 + (4+B)*blue.2)

private def wideICTMeter (B : Nat) (L : Limits) (y cb cr : JPEG2000.WideICT.Component) :
    Except Error (JPEG2000.WideICT.Component × JPEG2000.WideICT.Component × JPEG2000.WideICT.Component) × Nat :=
  match L.check (.at .mct) .workSamples (rectArea y.rect+rectArea cb.rect+rectArea cr.rect) with
  | .error e => (.error e,0)
  | .ok _ =>
    if h : JPEG2000.WideICT.Compatible y cb cr then
      let t := matrix B y cb cr h.1
      (.ok t.1,t.2)
    else (.error (.malformed (.at .mct) "incompatible wide ICT component grids or fractional bits"),0)

private theorem wideICT_work (B : Nat) (L : Limits) (y cb cr : JPEG2000.WideICT.Component) :
    (wideICTMeter B L y cb cr).1 = JPEG2000.WideICT.ictInverse L y cb cr ∧
    (wideICTMeter B L y cb cr).2 ≤ (4+B)*rectArea y.rect + (5+B)*rectArea cb.rect + (4+B)*rectArea cr.rect := by
  unfold wideICTMeter JPEG2000.WideICT.ictInverse
  cases L.check (.at .mct) .workSamples _ with
  | error => exact ⟨rfl,Nat.zero_le _⟩
  | ok u =>
    cases u; simp only [Equiv.ok_bind]
    split <;> try exact ⟨rfl,Nat.zero_le _⟩
    simp only [matrix,tabulate_work]
    exact ⟨rfl,Nat.le_refl _⟩

/-- Work and storage from the compact attempt and optional wide retry. The three
`Vector.ofFn` domains of `WideICT.colour` are red, green and blue respectively.
Their row evaluations cost two, three and two input reads plus one result slot,
one row call and one store. -/
def ictMeter (B : Nat) (L : Limits) (y cb cr : IPlane) : Except Error (IPlane × IPlane × IPlane) × Nat :=
  let cells := rectArea y.rect + rectArea cb.rect + rectArea cr.rect
  match L.check (.at .mct) .workSamples cells with
  | .error e => (.error e,0)
  | .ok _ =>
    if JPEG2000.WideReversible.SameShape y.rect cb.rect cr.rect ∧ JPEG2000.WideICT.Ordered y.rect ∧
        JPEG2000.WideICT.Ordered cb.rect ∧ JPEG2000.WideICT.Ordered cr.rect ∧ cb.bits = y.bits ∧ cr.bits = y.bits then
      let trial := compactMeter y cb cr
      match trial.1 with
      | some rgb => (.ok rgb,trial.2)
      | none =>
        let wy := promoteMeter B y
        let wb := promoteMeter B cb
        let wr := promoteMeter B cr
        let out := wideICTMeter B L wy.1 wb.1 wr.1
        (out.1.map (fun (r,g,b) => (.wide r,.wide g,.wide b)), trial.2 + wy.2 + wb.2 + wr.2 + out.2)
    else (.error (.malformed (.at .mct) "incompatible ICT component grids or fractional bits"),0)

/-- Both ICT attempts are charged together, even when the last compact channel
overflows. Incompatible geometry and the aggregate limit check precede raster work. -/
theorem ict_work (B : Nat) (L : Limits) (y cb cr : IPlane) :
    let m := ictMeter B L y cb cr
    m.1 = JPEG2000.IrreversibleDispatch.ict L y cb cr ∧
      m.2 ≤ (20+2*B)*(rectArea y.rect + rectArea cb.rect + rectArea cr.rect) := by
  obtain ⟨val,bound⟩ := compactICT_work y cb cr
  dsimp only [ictMeter,JPEG2000.IrreversibleDispatch.ict]
  cases hc : L.check (.at .mct) .workSamples _ with
  | error => exact ⟨rfl,Nat.zero_le _⟩
  | ok u =>
    cases u
    simp only [Equiv.ok_bind]
    split <;> try exact ⟨rfl,Nat.zero_le _⟩
    rw [← val]
    cases (compactMeter y cb cr).1 with
    | some rgb =>
      refine ⟨rfl,Nat.le_trans bound (Nat.mul_le_mul_right _ (by omega))⟩
    | none =>
      simp only [promote_work]
      obtain ⟨wide,cost⟩ := wideICT_work B L y.toWide cb.toWide cr.toWide
      have shape (p : IPlane) : p.toWide.rect = p.rect := by cases p <;> rfl
      rw [shape,shape,shape] at cost
      refine ⟨?_,?_⟩
      · rw [wide]; cases JPEG2000.WideICT.ictInverse L y.toWide cb.toWide cr.toWide <;> rfl
      · have hy := promotion_le B y
        have hb := promotion_le B cb
        have hr := promotion_le B cr
        simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc] at *
        omega

private def packedRCT (a b c : Plane) : Except Error (Source × Source × Source) × Nat :=
  if h : b.width = a.width ∧ b.height = a.height ∧ c.width = a.width ∧ c.height = a.height then
    let t := map3Meter JPEG2000.MCT.rctSample (N := a.width*a.height) ⟨a,rfl⟩
      ⟨b,by rw [h.1,h.2.1]⟩ ⟨c,by rw [h.2.2.1,h.2.2.2]⟩ 0
    (.ok (.plane t.1.1.val,.plane t.1.2.1.val,.plane t.1.2.2.val),19*t.2)
  else (.error (.malformed JPEG2000.MCT.loc
    s!"component transform on planes {a.width}×{a.height}, {b.width}×{b.height}, {c.width}×{c.height}"),0)

private theorem packed_rct (a b c : Plane) :
    (packedRCT a b c).1 = (JPEG2000.MCT.rctInverse a b c >>= fun (r,g,blue) => pure (.plane r,.plane g,.plane blue)) ∧
    (packedRCT a b c).2 ≤ 19*(a.width*a.height) := by
  unfold packedRCT JPEG2000.MCT.rctInverse JPEG2000.MCT.apply3
  split <;> try exact ⟨rfl,Nat.zero_le _⟩
  rw [map3_work]
  exact ⟨rfl,Nat.le_refl _⟩

/-- Meter the packed-eligibility scan before RCT and the packed three-cell loop.
A lazy result borrows all three predecessors; its individual reads are charged at
placement. Packed writes may use another four-byte slot for each channel. -/
def rctMeter (L : Limits) (y cb cr : Source) : Except Error (Source × Source × Source) × Nat :=
  match L.check (.at .mct) .workSamples (area y + area cb + area cr) with
  | .error e => (.error e,0)
  | .ok _ =>
    if cb.width = y.width ∧ cb.height = y.height ∧ cr.width = y.width ∧ cr.height = y.height then
      match y,cb,cr with
      | .plane a,.plane b,.plane c =>
        let test := scan (fun i => JPEG2000.ReversibleDispatch.fitsRGB
          (JPEG2000.ReversibleDispatch.rgbAt (.plane a) (.plane b) (.plane c) i)) (a.width*a.height)
        if test.1 then
          let rgb := packedRCT a b c
          (rgb.1,4*test.2+rgb.2)
        else (.ok (JPEG2000.ReversibleDispatch.views (.plane a) (.plane b) (.plane c)),4*test.2)
      | a,b,c => (.ok (JPEG2000.ReversibleDispatch.views a b c),0)
    else (.error (.malformed (.at .mct)
      s!"component transform on planes {y.width}×{y.height}, {cb.width}×{cb.height}, {cr.width}×{cr.height}"),0)

/-- The RCT bound covers a full eligibility scan followed by materialization,
or the prefix before falling back to the views. -/
theorem rct_work (L : Limits) (y cb cr : Source) :
    (rctMeter L y cb cr).1 = JPEG2000.ReversibleDispatch.colour L y cb cr ∧
    (rctMeter L y cb cr).2 ≤ 8*(area y + area cb + area cr) := by
  unfold rctMeter JPEG2000.ReversibleDispatch.colour area
  cases L.check (.at .mct) .workSamples _ with
  | error => exact ⟨rfl,Nat.zero_le _⟩
  | ok u =>
    cases u
    simp only [Equiv.ok_bind]
    split <;> try exact ⟨rfl,Nat.zero_le _⟩
    rename_i shape
    cases y <;> cases cb <;> cases cr <;> try exact ⟨rfl,Nat.zero_le _⟩
    rename_i a b c
    obtain ⟨eq,visits⟩ := colourFits_work (.plane a) (.plane b) (.plane c) (a.width*a.height)
    obtain ⟨bw,bh,cw,ch⟩ := shape
    dsimp only [Source.width,Source.height] at bw bh cw ch ⊢
    rw [← eq]
    split
    · refine ⟨?_,?_⟩
      · exact (packed_rct ..).1
      · have kernel := (packed_rct a b c).2
        rw [bw,bh,cw,ch]; dsimp only; omega
    · exact ⟨rfl,by rw [bw,bh,cw,ch]; dsimp only; omega⟩


private def replaceRGB (ps : Array Spatial) (rgb : Source × Source × Source) :=
  (((ps.map (·.source)).setIfInBounds 0 rgb.1).setIfInBounds 1 rgb.2.1).setIfInBounds 2 rgb.2.2

private def completeRGB (ps : Array Spatial) (m : Except Error (Source × Source × Source) × Nat) :=
  match m.1 with
  | .error e => (Except.error e,3+m.2)
  | .ok rgb => (Except.ok (replaceRGB ps rgb),6+m.2+8*ps.size)

/-- The tile's real transform selection. Account for the descriptor map and the
three indexed updates, conservatively allowing a vector copy on each update.
Extra components pass through the single map without a raster traversal. -/
def sourcesMeter (B : Nat) (L : Limits) (mct : Bool) (ps : Array Spatial) :
    Except Error (Array Source) × Nat :=
  if !mct then (.ok (ps.map (·.source)),2*ps.size)
  else match ps[0]?,ps[1]?,ps[2]? with
  | some (Spatial.rev y), some (Spatial.rev cb), some (Spatial.rev cr) => completeRGB ps (rctMeter L y cb cr)
  | some (Spatial.irrev y), some (Spatial.irrev cb), some (Spatial.irrev cr) =>
    let m := ictMeter B L y cb cr
    completeRGB ps (m.1.map (fun (r,g,b) => (r.source,g.source,b.source)),m.2)
  | _, _, _ => (.error (.malformed (.at .mct) "inconsistent colour transform components"),3)

private theorem firstThree {ps : Array Spatial} {a b c : Spatial}
    (h0 : ps[0]? = some a) (h1 : ps[1]? = some b) (h2 : ps[2]? = some c) :
    area a.source + area b.source + area c.source ≤ retained ps := by
  rcases ps with ⟨xs⟩
  cases xs with | nil => contradiction | cons x xs =>
    cases xs with | nil => contradiction | cons y xs =>
      cases xs with | nil => contradiction | cons z xs =>
        cases h0; cases h1; cases h2
        change area x.source + area y.source + area z.source ≤ (xs.cons z |>.cons y |>.cons x |>.map (fun p => area p.source)).sum
        simp only [List.map_cons,List.sum_cons]
        omega

private theorem complete_value (ps : Array Spatial) (m : Except Error (Source × Source × Source) × Nat) :
    (completeRGB ps m).1 = (m.1 >>= fun rgb => pure (replaceRGB ps rgb)) := by
  unfold completeRGB; cases m.1 <;> rfl

private theorem complete_bound (ps : Array Spatial) (m : Except Error (Source × Source × Source) × Nat) :
    (completeRGB ps m).2 ≤ 6 + 8*ps.size + m.2 := by
  unfold completeRGB; cases m.1 <;> dsimp only <;> omega

/-- Both real colour modes and all rejection paths, including absent or mixed
input triples. This bound holds independently of colour success and counts all
pre-colour component areas exactly once in its domain. -/
theorem sources_work (B : Nat) (L : Limits) (mct : Bool) (ps : Array Spatial) :
    (sourcesMeter B L mct ps).1 = JPEG2000.TileDispatch.sources L mct ps ∧
    (sourcesMeter B L mct ps).2 ≤ 6 + 8*ps.size + (20+2*B)*retained ps := by
  unfold sourcesMeter JPEG2000.TileDispatch.sources
  split
  · exact ⟨rfl,by dsimp only; omega⟩
  · dsimp only
    split
    · rename_i y cb cr hy hb hr
      obtain ⟨eq,le⟩ := rct_work L y cb cr
      have dom := firstThree hy hb hr
      change area y + area cb + area cr ≤ _ at dom
      have cap := Nat.mul_le_mul (show 8 ≤ 20+2*B by omega) dom
      exact ⟨by rw [complete_value,eq,hy,hb,hr]; rfl, by have := complete_bound ps (rctMeter L y cb cr); omega⟩
    · rename_i y cb cr hy hb hr
      obtain ⟨eq,le⟩ := ict_work B L y cb cr
      rw [spatial_area, spatial_area, spatial_area] at le
      have dom := firstThree hy hb hr
      change area y.source + area cb.source + area cr.source ≤ _ at dom
      have cap := Nat.mul_le_mul_left (20+2*B) dom
      refine ⟨?_,?_⟩
      · rw [complete_value]
        dsimp only
        rw [eq,hy,hb,hr]
        dsimp only
        cases JPEG2000.IrreversibleDispatch.ict L y cb cr <;> rfl
      · apply Nat.le_trans (complete_bound ..)
        dsimp only
        omega
    · refine ⟨?_,by dsimp only; omega⟩
      split <;> first | rfl | grind

/-- Meter the component traversal common to `TileDispatch.tile` and
`NativeOutput.writeTile`. An exception carries the charge of the current
callback and all preceding pushes. -/
def componentLoop {α β : Type} (xs : Array α)
    (f : (j : Nat) → α → j < xs.size → Except Error β × Nat) :
    (k j : Nat) → k+j = xs.size → Array β → Except Error (Array β) × Nat
  | 0, _, _, acc => (.ok acc,0)
  | k+1, j, h, acc =>
    let t := f j xs[j] (by omega)
    match t.1 with
    | .error e => (.error e,t.2+1)
    | .ok v =>
      let tail := componentLoop xs f k (j+1) (by omega) (acc.push v)
      (tail.1,t.2+1+tail.2)

private theorem loop_value {α β : Type} (xs : Array α)
    (f : (j : Nat) → α → j < xs.size → Except Error β × Nat)
    (k j : Nat) (h : k+j = xs.size) (acc : Array β) :
    (componentLoop xs f k j h acc).1 =
      Array.mapFinIdxM.map xs (fun i v hi => (f i v hi).1) k j h acc := by
  induction k generalizing j acc with
  | zero => rfl
  | succ k ih =>
    simp only [componentLoop,Array.mapFinIdxM.map]
    cases (f j xs[j] (by omega)).1 with
    | error => rfl
    | ok => exact ih ..

private theorem loop_bound {α β : Type} (xs : Array α)
    (f : (j : Nat) → α → j < xs.size → Except Error β × Nat)
    (cost : Nat → Nat) (hf : ∀ j (hj : j < xs.size), (f j xs[j] hj).2+1 ≤ cost j)
    (k j : Nat) (h : k+j = xs.size) (acc : Array β) :
    (componentLoop xs f k j h acc).2 ≤ ((List.range' j k).map cost).sum := by
  induction k generalizing j acc with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    simp only [componentLoop,List.range'_succ,List.map_cons,List.sum_cons]
    have here := hf j (by omega)
    split
    · dsimp only; omega
    · exact Nat.add_le_add here (ih ..)

private theorem range_sum {α : Type} (xs : Array α) (f : α → Nat) (cost : Nat → Nat)
    (hf : ∀ j (hj : j < xs.size), cost j = f xs[j]) :
    ((List.range' 0 xs.size).map cost).sum = (xs.toList.map f).sum := by
  congr 1
  apply List.ext_getElem <;> simp
  exact fun i hi _ => hf i hi

private theorem linear_sum {α : Type} (xs : List α) (cost : α → Nat) (u v : Nat) :
    (xs.map fun x => u+v*cost x).sum = u*xs.length + v*(xs.map cost).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.mul_succ,Nat.mul_add]; omega

private def grid (g : Progression.Layout) (red i : Nat) := Assemble.reduceRect (g.comp i).rect red

private theorem grid_area (g : Progression.Layout) (red i : Nat) (hi : i < g.comps.size) :
    rectArea (grid g red i) = rectArea (Assemble.reduceRect g.comps[i].rect red) := by
  simp [grid,Progression.Layout.comp,Array.getD_eq_getD_getElem?,hi]

private theorem grid_sum (g : Progression.Layout) (red u v : Nat) :
    ((List.range' 0 g.numComps).map (fun j => u+v*rectArea (grid g red j))).sum =
      u*g.numComps + v*Resources.tileCells g red := by
  unfold Progression.Layout.numComps
  rw [range_sum g.comps (fun tc => u+v*rectArea (Assemble.reduceRect tc.rect red)) (fun j => u+v*rectArea (grid g red j))
      (fun j hj => by rw [grid_area _ _ _ hj]), linear_sum]
  rfl


private theorem ok_right {α β : Type} {P : α → β → Prop} {x : α} {v : Except Error β}
    (rel : Tier2Equiv.Res P (.ok x) v) : ∃ y, v = .ok y ∧ P x y := by
  cases v with
  | ok y => exact ⟨y,rfl,rel⟩
  | error => contradiction

private theorem result_area {L : Limits} {data : ByteArray} {h : Header} {t red : Nat}
    {g : Progression.Layout} {c : Coding} {a : Option JPEG2000.Tier2.Packet.TileCodeBlocks}
    {b : Option Spec.Tier2.TileOut} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,c)) (stores : TileDispatch.Packets L h data t a b)
    (i : Fin g.numComps) {v : Spatial} (ok : JPEG2000.TileDispatch.component L h data g c a i red = .ok v) :
    area v.source = rectArea (grid g red i) := by
  have rel := TileDispatch.parsed_component parsed layout stores i red
  dsimp only at rel
  rw [ok] at rel
  obtain ⟨z,hz,eq⟩ := ok_right rel
  rw [WideAssembly.tileComp_eq_finish] at hz
  obtain ⟨q,_,last⟩ := Tier2Equiv.bind_ok hz
  cases last
  have source := eq.centered
  unfold area
  rw [source.1,source.2.1]
  unfold Decode.idwt
  split <;> rfl

private def collectStep (B : Nat) (L : Limits) (h : Header) (data : ByteArray)
    (g : Progression.Layout) (c : Coding) (a : Option JPEG2000.Tier2.Packet.TileCodeBlocks)
    (red j : Nat) (_ : TileCompGeom) (hj : j < g.comps.size) :=
  let call := JPEG2000.TileDispatch.component L h data g c a ⟨j,hj⟩ red
  (call, match call with
    | .ok p => (4+B)*area p.source
    | .error _ => 0)

/-- The prefix of component outputs retained before colour or before a later
component fails. The source raster of every returned component is charged at
a common upper price for packed and arbitrary-width cells. Wavelet internals
belong to the producer's separate charge. -/
def preColourMeter (B : Nat) (L : Limits) (h : Header) (data : ByteArray)
    (g : Progression.Layout) (c : Coding) (a : Option JPEG2000.Tier2.Packet.TileCodeBlocks) (red : Nat) :=
  let m := componentLoop g.comps (collectStep B L h data g c a red) g.numComps 0 rfl #[]
  (m.1,g.numComps+m.2)

private theorem pre_value (B : Nat) (L : Limits) (h : Header) (data : ByteArray)
    (g : Progression.Layout) (c : Coding) (a : Option JPEG2000.Tier2.Packet.TileCodeBlocks) (red : Nat) :
    (preColourMeter B L h data g c a red).1 = g.comps.mapFinIdxM
      (fun i _ hi => JPEG2000.TileDispatch.component L h data g c a ⟨i,hi⟩ red) := by
  exact loop_value g.comps (collectStep B L h data g c a red) g.comps.size 0 rfl #[]

/-- Component-vector reservation and visited prefix, including the live
predecessors on a later error. Success also identifies the exact combined
retained raster domain for the colour dispatcher. -/
theorem preColour_work (B : Nat) {L : Limits} {data : ByteArray} {h : Header} {t red : Nat}
    {g : Progression.Layout} {c : Coding} {a : Option JPEG2000.Tier2.Packet.TileCodeBlocks}
    {b : Option Spec.Tier2.TileOut} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,c)) (stores : TileDispatch.Packets L h data t a b) :
    let m := preColourMeter B L h data g c a red
    m.2 ≤ 2*g.numComps + (4+B)*Resources.tileCells g red ∧
      ∀ ps, m.1 = .ok ps → ps.size = g.numComps ∧ retained ps = Resources.tileCells g red := by
  refine ⟨?_,?_⟩
  · have step (j : Nat) (hj : j < g.comps.size) :
        (collectStep B L h data g c a red j g.comps[j] hj).2 + 1 ≤ 1+(4+B)*rectArea (grid g red j) := by
      unfold collectStep
      cases ok : JPEG2000.TileDispatch.component L h data g c a ⟨j,hj⟩ red with
      | error => dsimp only; omega
      | ok v => dsimp only; rw [result_area parsed layout stores _ ok]; dsimp only; omega
    have cap := loop_bound _ _ _ step g.numComps 0 rfl #[]
    rw [grid_sum] at cap
    dsimp only [preColourMeter]
    omega
  · intro ps ok
    rw [pre_value] at ok
    have sim := TileDispatch.components_equiv parsed layout stores red
    rw [ok] at sim
    obtain ⟨_,_,hs⟩ := ok_right sim
    refine ⟨hs.1,?_⟩
    have dom := range_sum ps (fun p => area p.source) (fun j => rectArea (grid g red j)) (by
      intro i hi
      obtain ⟨comp,geo⟩ := hs.2.2 i hi
      have plane := comp.centered
      unfold area
      rw [plane.1,plane.2.1,geo.2.1,geo.2.2]
      rfl)
    rw [hs.1] at dom
    rw [retained,← dom]
    simpa using grid_sum g red 0 1

/-- The native tile entry point with structural charges for the admission fold,
the retained spatial vector and its colour continuation. -/
def tileMeter (B : Nat) (L : Limits) (h : Header) (data : ByteArray)
    (g : Progression.Layout) (c : Coding) (a : Option JPEG2000.Tier2.Packet.TileCodeBlocks)
    (red : Nat) : Except Error (Array Source) × Nat :=
  match L.check Assemble.loc .workSamples
      (g.comps.foldl (fun n tc => n+rectArea (Assemble.reduceRect tc.rect red)) 0) with
  | .error e => (.error e,g.numComps)
  | .ok _ =>
    let p := preColourMeter B L h data g c a red
    match p.1 with
    | .error e => (.error e,g.numComps+p.2)
    | .ok ps =>
      let rgb := sourcesMeter B L (c.mctApplies h.siz) ps
      (rgb.1,g.numComps+p.2+rgb.2)

/-- Per parsed native tile, including rejection by the aggregate guard, the
component prefix or the colour step. Both packed and wide retries are covered
by the same tile-area allowance. -/
theorem tile_work (B : Nat) {L : Limits} {data : ByteArray} {h : Header} {t red : Nat}
    {g : Progression.Layout} {c : Coding} {a : Option JPEG2000.Tier2.Packet.TileCodeBlocks}
    {b : Option Spec.Tier2.TileOut} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,c)) (stores : TileDispatch.Packets L h data t a b) :
    let m := tileMeter B L h data g c a red
    m.1 = JPEG2000.TileDispatch.tile L h data g c a red ∧
    m.2 ≤ 6 + 11*L.maxComponents + (24+3*B)*L.maxWorkSamples := by
  have count := (HeaderWork.layout_budget parsed layout).1
  have fold : (g.comps.foldl (fun n tc => n+rectArea (Assemble.reduceRect tc.rect red)) 0) =
      Resources.tileCells g red := Resources.array_foldl_sum _ _ (fun _ _ => rfl) _
  dsimp only [tileMeter,JPEG2000.TileDispatch.tile]
  rw [fold]
  cases guard : L.check Assemble.loc .workSamples (Resources.tileCells g red) with
  | error => exact ⟨rfl, by dsimp only; omega⟩
  | ok u =>
    cases u
    have areaBound : Resources.tileCells g red ≤ L.maxWorkSamples := (Limits.check_eq_ok_iff ..).1 guard
    have cap := Nat.mul_le_mul_left (24+3*B) areaBound
    obtain ⟨pre,domain⟩ := preColour_work B parsed layout stores (red := red)
    simp only [Equiv.ok_bind,← pre_value B]
    cases run : (preColourMeter B L h data g c a red).1 with
    | error => exact ⟨rfl,by dsimp only; simp only [Nat.add_mul,Nat.mul_assoc] at *; omega⟩
    | ok ps =>
      obtain ⟨len,areas⟩ := domain ps run
      obtain ⟨equiv,colour⟩ := sources_work B L (c.mctApplies h.siz) ps
      rw [len,areas] at colour
      exact ⟨equiv,by dsimp only; simp only [Nat.add_mul,Nat.mul_assoc] at *; omega⟩


private theorem fill_dims {N : Nat} (f : Fin N → Int32) (n : Nat) (hn : n ≤ N) (p : JPEG2000.DWT53.Buf N) :
    (fill f n hn p).val.width = p.val.width ∧ (fill f n hn p).val.height = p.val.height := by
  induction n generalizing p with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => exact ih _ _

private theorem map_dims {N : Nat} (f : Int32 → Int32) (p : JPEG2000.DWT53.Buf N) (i : Nat) :
    (JPEG2000.MCT.map1 f p i).val.width = p.val.width ∧ (JPEG2000.MCT.map1 f p i).val.height = p.val.height := by
  rw [JPEG2000.MCT.map1]
  split
  · exact map_dims f _ (i+1)
  · exact ⟨rfl,rfl⟩
termination_by N-i

private def exactMeter (s : Source) (r : NativeSampleRange) (F : Nat) : Plane × Nat :=
  let f := fun i => Int32.ofInt (((JPEG2000.WideOutput.prepare r F).sample (s.read i)).val)
  let m := raster (N := area s) (fun i (p : JPEG2000.DWT53.Buf (area s)) => p.set i (f i) i.isLt)
    (area s) (Nat.le_refl _) ⟨Plane.zero s.width s.height,rfl⟩
  (m.1.val,8*area s + 7*m.2)

private theorem exact_work (s : Source) (r : NativeSampleRange) (F : Nat) (fits) :
    (exactMeter s r F).1 = exactTile s r fits F ∧ (exactMeter s r F).2 = 15*area s ∧
    (exactMeter s r F).1.width = s.width ∧ (exactMeter s r F).1.height = s.height := by
  dsimp only [exactMeter]
  rw [fill_work]
  exact ⟨rfl,by dsimp only; omega,fill_dims ..⟩

/-- Both compact G.1 kernels share the packed map domain. Conservatively charge
a four-byte scratch slot per cell even when the map reuses its input. Exact G.1
allocates and zeroes the tile, then fills it through a potentially lazy source. -/
def narrowMeter (s : Source) (r : NativeSampleRange) (F : Nat) : Plane × Nat :=
  match s with
  | .exact .. => exactMeter s r F
  | .plane p =>
    match JPEG2000.MCT.DcShift.make r.signed r.depth F with
    | .error _ => exactMeter (.plane p) r F
    | .ok dc =>
      let t := map1Meter (if F = 0 then dc.rev else dc.irrev) (N := p.width*p.height) ⟨p,rfl⟩ 0
      (t.1.val,7*t.2)

private theorem narrow_work (s : Source) (r : NativeSampleRange) (F : Nat) (fits) :
    let m := narrowMeter s r F
    m.1 = narrowTile s r fits F ∧ m.2 ≤ 15*area s ∧ m.1.width = s.width ∧ m.1.height = s.height := by
  have ew (q : Source) := exact_work q r F fits
  cases s with
  | exact => exact ⟨(ew _).1,Nat.le_of_eq (ew _).2.1,(ew _).2.2⟩
  | plane p =>
    dsimp only [narrowMeter,narrowTile]
    cases JPEG2000.MCT.DcShift.make r.signed r.depth F with
    | error => exact ⟨(ew _).1,Nat.le_of_eq (ew _).2.1,(ew _).2.2⟩
    | ok dc => dsimp only; rw [map1_work]; split <;> exact ⟨rfl,by change 7*(p.width*p.height) ≤ 15*(p.width*p.height); omega,map_dims ..⟩

private def compactBlit (d s : Plane) (ox oy : Nat) : Except Error Plane × Nat :=
  if ox + s.width ≤ d.width ∧ oy + s.height ≤ d.height then
    let t := rows s ox oy s.height 0 d
    (.ok t.1,t.2.1+3*t.2.2)
  else (.error (.malformed Assemble.loc
    s!"tile-component {s.width}×{s.height} at ({ox}, {oy}) outside the component plane {d.width}×{d.height}"),0)

private theorem compact_blit (d s : Plane) (ox oy : Nat) :
    (compactBlit d s ox oy).1 = Assemble.blit d s ox oy ∧
    (compactBlit d s ox oy).2 ≤ s.height+3*(s.width*s.height) := by
  unfold compactBlit Assemble.blit
  split
  · rw [blitRows_work]
    exact ⟨rfl,Nat.le_refl _⟩
  · exact ⟨rfl,Nat.zero_le _⟩

private def wideBlit (L : Limits) (d : WidePlane) (s : Source) (ox oy F : Nat) : Except Error WidePlane × Nat :=
  let loc := Location.at .decode
  let cells := d.width*d.height
  match L.check loc .workSamples cells with
  | .error e => (.error e,0)
  | .ok _ => match L.check loc .decodedBytes (cells*bytesPerSample d.range.depth) with
    | .error e => (.error e,0)
    | .ok _ =>
      if fit : ox+s.width ≤ d.width ∧ oy+s.height ≤ d.height then
        let step := fun (i : Fin (area s)) (p : WideDst s.width s.height ox oy d.range) =>
          let v := (JPEG2000.WideOutput.prepare d.range F).sample (s.read i)
          let q := p.val.set (JPEG2000.WideOutput.destIndex p.val.width s.width ox oy i) v.val
            (JPEG2000.WideOutput.destIndex_lt p.property.1 p.property.2.1 i.isLt)
            (by rw [p.property.2.2]; exact v.property)
          (⟨q,p.property⟩ : WideDst s.width s.height ox oy d.range)
        let t := raster step (area s) (Nat.le_refl _) ⟨d,fit.1,fit.2,rfl⟩
        (.ok t.1.val,7*t.2)
      else (.error (.malformed loc "wide tile-component outside the component plane"),0)

private theorem wide_blit (L : Limits) (d : WidePlane) (s : Source) (ox oy F : Nat) :
    (wideBlit L d s ox oy F).1 = JPEG2000.WideOutput.blit L (.at .decode) d s.width s.height ox oy F s.read ∧
    (wideBlit L d s ox oy F).2 ≤ 7*area s := by
  dsimp only [wideBlit,JPEG2000.WideOutput.blit]
  cases L.check (.at .decode) .workSamples _ with
  | error => exact ⟨rfl,Nat.zero_le _⟩
  | ok u =>
    cases u
    cases L.check (.at .decode) .decodedBytes _ with
    | error => exact ⟨rfl,Nat.zero_le _⟩
    | ok u =>
      cases u
      simp only [Equiv.ok_bind]
      split <;> try exact ⟨rfl,Nat.zero_le _⟩
      rename_i fit
      have eq := blitCells_work ox oy d.range (JPEG2000.WideOutput.prepare d.range F) s.read (area s)
        (Nat.le_refl _) (⟨d,fit.1,fit.2,rfl⟩ : WideDst s.width s.height ox oy d.range)
      exact ⟨congrArg Except.ok (congrArg Prod.fst eq),Nat.le_of_eq (congrArg (fun m => 7*m.2) eq)⟩

private def thenMeter {α β : Type} (m : Except Error α × Nat) (f : α → Except Error β × Nat) :
    Except Error β × Nat :=
  match m.1 with
  | .error e => (.error e,m.2)
  | .ok x => let t := f x; (t.1,m.2+t.2)

private theorem then_value {α β : Type} (m : Except Error α × Nat) (f : α → Except Error β × Nat) :
    (thenMeter m f).1 = (m.1 >>= fun x => (f x).1) := by
  unfold thenMeter; cases m.1 <;> rfl

private theorem then_bound {α β : Type} (m : Except Error α × Nat) (f : α → Except Error β × Nat)
    (b : Nat) (hf : ∀ x, (f x).2 ≤ b) : (thenMeter m f).2 ≤ m.2+b := by
  unfold thenMeter; cases m.1 <;> dsimp only
  · omega
  · exact Nat.add_le_add_left (hf _) _

/-- Follow the writer's shape, destination budget and storage checks. The exact
compact tile is charged even if the following blit or final packaging rejects. -/
def writeComponentMeter (L : Limits) (d : OutputComponent) (r : Rect) (F : Nat) (s : Source) :
    Except Error OutputComponent × Nat :=
  if !fitsTile d.rect r s then
    (.error (.malformed (.at .decode) "tile-component shape or offset outside the reduced image"),0)
  else
    let ox := r.x0-d.rect.x0
    let oy := r.y0-d.rect.y0
    match d.storage with
    | .wide p => thenMeter (wideBlit L p s ox oy F) fun q => (finish d.rect d.format d.precision (.wide q),0)
    | .narrow p =>
      let n := d.rect.width*d.rect.height
      thenMeter (L.check (.at .decode) .workSamples n,0) fun _ =>
      thenMeter (L.check (.at .decode) .decodedBytes (n*bytesPerSample d.format.depth.toNat),0) fun _ =>
      let rng : NativeSampleRange := ⟨_,d.format.signed,d.precision,_,_,rfl,rfl⟩
      let m := narrowMeter s rng F
      let b := thenMeter (compactBlit p m.1 ox oy) fun q => (finish d.rect d.format d.precision (.narrow q),0)
      (b.1,m.2+b.2)

/-- The compact writer visits at most one G.1 and one copy domain, plus one
outer entry per row. The wide writer fuses G.1 with its single cell loop. Up
to three retained inputs and one RCT evaluation per source read are included. -/
theorem writeComponent_work (L : Limits) (d : OutputComponent) (r : Rect) (F : Nat) (s : Source) :
    let m := writeComponentMeter L d r F s
    m.1 = writeComponent L d r F s ∧ m.2 ≤ r.height+18*rectArea r := by
  dsimp only [writeComponentMeter,writeComponent]
  cases geom : fitsTile d.rect r s with
  | false => exact ⟨rfl,Nat.zero_le _⟩
  | true =>
    have dims := geom
    simp only [fitsTile,Bool.and_eq_true,beq_iff_eq] at dims
    have hw := dims.1.2
    have hh := dims.2
    have ha : area s = rectArea r := by simp only [area,rectArea,hw,hh]
    simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte]
    split
    · rename_i p hs
      obtain ⟨eq,le⟩ := wide_blit L p s (r.x0-d.rect.x0) (r.y0-d.rect.y0) F
      refine ⟨?_,?_⟩
      · simp only [then_value,eq]
        split <;> rename_i q hq <;> rw [hs] at hq <;> cases hq <;> rfl
      · apply Nat.le_trans (then_bound _ _ 0 (fun _ => Nat.le_refl 0))
        omega
    · rename_i p hs
      let rng : NativeSampleRange := ⟨_,d.format.signed,d.precision,_,_,rfl,rfl⟩
      have hc := d.valid
      simp only [hs,Storage.matches,Bool.and_eq_true] at hc
      have fits : -2147483648 ≤ rng.lo ∧ rng.hi ≤ 2147483647 := by simpa [compact,rng] using hc.2
      obtain ⟨exactTileEq,cost,w,h⟩ := narrow_work s rng F fits
      have bl := compact_blit p (narrowMeter s rng F).1 (r.x0-d.rect.x0) (r.y0-d.rect.y0)
      refine ⟨?_,?_⟩
      · simp only [then_value]
        simp only [rng] at exactTileEq bl
        rw [bl.1,exactTileEq]
        split <;> rename_i q hq <;> rw [hs] at hq <;> cases hq <;> rfl
      · apply Nat.le_trans (then_bound _ _ (r.height+18*rectArea r) ?_) (Nat.le_of_eq (Nat.zero_add _))
        intro _
        apply Nat.le_trans (then_bound _ _ (r.height+18*rectArea r) ?_) (Nat.le_of_eq (Nat.zero_add _))
        intro _
        dsimp only
        have finishCost := then_bound (compactBlit p (narrowMeter s rng F).1 (r.x0-d.rect.x0) (r.y0-d.rect.y0))
          (fun q => (finish d.rect d.format d.precision (.narrow q),0)) 0 (fun _ => Nat.le_refl 0)
        have blcost := bl.2
        rw [w,h,hw,hh] at blcost
        change _ ≤ r.height + 3 * rectArea r at blcost
        change (narrowMeter s rng F).2 + (thenMeter (compactBlit p (narrowMeter s rng F).1 _ _)
          (fun q => (finish d.rect d.format d.precision (.narrow q),0))).2 ≤ _
        omega


private def writeStep (L : Limits) (s : Marker.SIZ) (red : Nat) (g : Progression.Layout)
    (ds : Array OutputComponent) (ps : Array Source) (bits : Nat → Nat)
    (counts : ds.size = s.components.size ∧ ds.size = g.numComps ∧ ds.size = ps.size)
    (i : Nat) (d : OutputComponent) (hi : i < ds.size) : Except Error OutputComponent × Nat :=
  let tc := g.comp i
  let c := s.components[i]'(counts.1 ▸ hi)
  if d.format != c || d.rect != Assemble.reduceRect (compRect (imageRect s) c) red then
    (.error (.malformed (.at .decode) "output component disagrees with SIZ or reduction"),0)
  else if red > tc.params.levels then
    (.error (.unsupported (.at .decode) "resolution reduction exceeds tile-component levels"),0)
  else
    let F := if tc.params.transform == .reversible53 then 0 else bits i
    writeComponentMeter L d (grid g red i) F (ps[i]'(counts.2.2 ▸ hi))

/-- Meter of the native component writer. The count check precedes its vector
reservation and traversal. The default scale is the public codestream scale. -/
def writeTileMeter (L : Limits) (s : Marker.SIZ) (red : Nat) (g : Progression.Layout) (coding : Coding)
    (ds : Array OutputComponent) (ps : Array Source)
    (bits : Nat → Nat := Assemble.fracBitsOf s (coding.mctApplies s)) : Except Error (Array OutputComponent) × Nat :=
  match L.check (.at .decode) .decompLevels red with
  | .error e => (.error e,0)
  | .ok _ =>
    if hc : ds.size = s.components.size ∧ ds.size = g.numComps ∧ ds.size = ps.size then
      let m := componentLoop ds (writeStep L s red g ds ps bits hc) ds.size 0 rfl #[]
      (m.1,ds.size+m.2)
    else (.error (.malformed (.at .decode) "tile and output component counts disagree"),0)

private theorem span (a b d : Nat) : cdiv b d - cdiv a d ≤ b-a := by
  cases d with
  | zero => simp [cdiv]
  | succ d =>
    have mult : b-a ≤ (b-a)*(d+1) := by rw [Nat.mul_succ]; omega
    have bound := Nat.div_le_div_right (c := d+1)
      (show b+(d+1)-1 ≤ (a+(d+1)-1)+(b-a)*(d+1) by omega)
    rw [Nat.add_mul_div_right _ _ (Nat.succ_pos d)] at bound
    exact Nat.sub_le_of_le_add (by simpa [cdiv,Nat.add_comm] using bound)

private theorem row_cap {L : Limits} {data : ByteArray} {h : Header} {t : Nat}
    {g : Progression.Layout} {c : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,c)) (red i : Nat) (hi : i < g.numComps) :
    (grid g red i).height ≤ L.maxImageSide := by
  obtain ⟨count,all⟩ := NativePlacement.tile_grid (red := red) parsed layout
  obtain ⟨_,_,_,lower,_,upper⟩ := all i hi
  let d := JPEG2000.Decode.compImageRect h.siz (h.siz.components[i]'(count ▸ hi)) red
  have within : (grid g red i).height ≤ d.height := by
    change _ - _ ≤ _ - _
    exact Nat.le_trans (Nat.sub_le_sub_right upper _) (Nat.sub_le_sub_left lower _)
  have reduced : d.height ≤ (compRect (imageRect h.siz) (h.siz.components[i]'(count ▸ hi))).height := span ..
  exact Nat.le_trans within (Nat.le_trans reduced (Nat.le_trans (span ..) (Resources.parse_within parsed).2.2.1.2.1))

/-- The actual `writeTile` on every destination and source vector after parsed
layout selection. The exact error is preserved. Independently of success, all
entered G.1 kernels and both blitters across components fit the combined grid
budget, with a separate side term for zero-width tiles. -/
theorem writeTile_work {L : Limits} {data : ByteArray} {h : Header} {t red : Nat}
    {g : Progression.Layout} {c : Coding} (parsed : Header.parse L data = .ok h)
    (layout : Progression.Layout.ofHeader h t = .ok (g,c)) (ds : Array OutputComponent)
    (ps : Array Source) (bits : Nat → Nat) :
    let m := writeTileMeter L h.siz red g c ds ps bits
    m.1 = writeTile L h.siz red g c ds ps bits ∧
    m.2 ≤ (2+L.maxImageSide)*g.numComps + 18*Resources.tileCells g red := by
  dsimp only [writeTileMeter,writeTile]
  cases L.check (.at .decode) .decompLevels red with
  | error => exact ⟨rfl,Nat.zero_le _⟩
  | ok u =>
    cases u
    simp only [Equiv.ok_bind]
    split <;> try exact ⟨rfl,Nat.zero_le _⟩
    rename_i counts
    dsimp only
    refine ⟨?_,?_⟩
    · rw [loop_value]
      unfold Array.mapFinIdxM
      congr 1
      funext j d hj
      unfold writeStep
      dsimp only
      split <;> try rfl
      split <;> try rfl
      exact (writeComponent_work ..).1
    · have step (j : Nat) (hj : j < ds.size) :
          (writeStep L h.siz red g ds ps bits counts j ds[j] hj).2+1 ≤
            (1+L.maxImageSide)+18*rectArea (grid g red j) := by
        have height := row_cap parsed layout red j (counts.2.1 ▸ hj)
        dsimp only [writeStep]
        split <;> try (dsimp only; omega)
        split <;> try (dsimp only; omega)
        exact Nat.le_trans (Nat.add_le_add_right (writeComponent_work ..).2 1) (by omega)
      have bound := loop_bound ds _ _ step ds.size 0 rfl #[]
      conv at bound => rhs; rw [counts.2.1,grid_sum]
      have n := counts.2.1
      simp only [Nat.add_mul] at *
      omega

/-- Placement at the ordinary codestream continuation. The successful centred
producer has already checked the sum of reduced tile-component areas. The bound
allows a placement failure at any component of the supplied destination. -/
theorem centeredTile_placement {L : Limits} {data : ByteArray} {h : Header} {t red : Nat}
    {store : Option JPEG2000.Tier2.Packet.TileCodeBlocks} {out : JPEG2000.Decode.CenteredTile}
    (parsed : Header.parse L data = .ok h) (ok : JPEG2000.Decode.centeredTile L h data red t store = .ok out)
    (ds : Array OutputComponent) :
    let m := writeTileMeter L h.siz red out.layout out.coding ds out.sources
    m.1 = writeTile L h.siz red out.layout out.coding ds out.sources ∧
    m.2 ≤ (2+L.maxImageSide)*L.maxComponents + 18*L.maxWorkSamples := by
  obtain ⟨layout,cells⟩ := NativeResources.centeredTile_work ok
  have count := (HeaderWork.layout_budget parsed layout).1
  obtain ⟨eq,bound⟩ := writeTile_work parsed layout (red := red) ds out.sources
    (Assemble.fracBitsOf h.siz (out.coding.mctApplies h.siz))
  exact ⟨eq,Nat.le_trans bound (Nat.add_le_add (Nat.mul_le_mul_left _ count) (Nat.mul_le_mul_left _ cells))⟩


/-- A pre-colour physical raster. The wide reader captures exactly the indexed
integer array produced by reconstruction. -/
inductive Backing where
  /-- Four-byte cells, with the plane's byte-length invariant. -/
  | compact (p : Plane)
  /-- A vector of integer cells on the reduced grid. -/
  | wide (w h : Nat) (v : Vector Int (w*h))

/-- Reading a physical backing costs one array cell lookup (four packed bytes
for a compact cell). No earlier colour callback is stored in this reader. -/
def Backing.source : Backing → Source
  | .compact p => .plane p
  | .wide w h v => .exact w h v.get

/-- Logical payload, parameterised by the representation price of an integer. -/
def Backing.payload (B : Nat) : Backing → Nat
  | .compact p => p.data.size
  | .wide _ _ v => B*v.toArray.size

private theorem backing_payload (B : Nat) (p : Backing) : p.payload B ≤ (4+B)*area p.source := by
  cases p with
  | compact p => simp only [Backing.payload,p.size_eq,area,Backing.source,Source.width,Source.height,Nat.add_mul]; omega
  | wide w h v => simp only [Backing.payload,area,Backing.source,Source.width,Source.height,v.size_toArray,Nat.add_mul]; omega

private def Direct (s : Source) := ∃ p : Backing, p.source = s

private theorem direct_irrev (p : IPlane) : Direct p.source := by
  cases p with
  | compact _ _ p _ _ => exact ⟨.compact p,rfl⟩
  | wide p => exact ⟨.wide _ _ p.samples,rfl⟩

private theorem direct_component {L : Limits} {h : Header} {data : ByteArray} {g : Progression.Layout}
    {c : Coding} {a : Option JPEG2000.Tier2.Packet.TileCodeBlocks} {i : Fin g.numComps} {red : Nat} {p : Spatial}
    (ok : JPEG2000.TileDispatch.component L h data g c a i red = .ok p) : Direct p.source := by
  unfold JPEG2000.TileDispatch.component at ok
  split at ok
  · generalize step : JPEG2000.ReversibleDispatch.component L data h.siz g c a i red = v at ok
    cases v <;> try contradiction
    cases ok
    unfold JPEG2000.ReversibleDispatch.component JPEG2000.ReversibleDispatch.tileComp at step
    dsimp only at step
    split at step <;> try contradiction
    split at step
    · cases step
      exact ⟨.compact _,rfl⟩
    · obtain ⟨band,_,read⟩ := Tier2Equiv.bind_ok step
      unfold JPEG2000.ReversibleDispatch.wideSource at read
      obtain ⟨v,_,spatial⟩ := Tier2Equiv.bind_ok read
      split at spatial <;> try contradiction
      rename_i size
      cases spatial
      exact ⟨.wide _ _ ⟨v,size⟩,rfl⟩
  · generalize step : JPEG2000.IrreversibleDispatch.component L data (g.comp i)
      (h.siz.components.getD i default).depth.toNat (Assemble.fracBitsOf h.siz (c.mctApplies h.siz) i)
      red ((a.map (·.comps.getD i #[])).getD #[]) = v at ok
    cases v <;> cases ok
    exact direct_irrev _

/-- The only native post-colour reader forms, with witnesses to the shared
predecessors. In the RGB case the channel selects one projection of the same
three direct rasters. G.1 invokes this reader once per written sample. -/
inductive Reader (ps : Array Spatial) : Source → Prop where
  /-- A packed plane or a directly indexed integer raster. -/
  | direct (p : Backing) : Reader ps p.source
  /-- One evaluation of a G.2 view on the original triple, including each of
  its three predecessor reads. -/
  | view (y cb cr : Backing)
      (hy : ps[0]? = some (.rev y.source)) (hb : ps[1]? = some (.rev cb.source))
      (hr : ps[2]? = some (.rev cr.source)) (s : Source)
      (channel : let v := JPEG2000.ReversibleDispatch.views y.source cb.source cr.source
        s = v.1 ∨ s = v.2.1 ∨ s = v.2.2) : Reader ps s

private theorem rct_readers {ps : Array Spatial} {y cb cr : Source}
    (hy : ps[0]? = some (.rev y)) (hb : ps[1]? = some (.rev cb)) (hr : ps[2]? = some (.rev cr))
    (dy : Direct y) (db : Direct cb) (dr : Direct cr) {L : Limits} {q : Source × Source × Source}
    (ok : JPEG2000.ReversibleDispatch.colour L y cb cr = .ok q) :
    Reader ps q.1 ∧ Reader ps q.2.1 ∧ Reader ps q.2.2 := by
  have views :
      let v := JPEG2000.ReversibleDispatch.views y cb cr
      Reader ps v.1 ∧ Reader ps v.2.1 ∧ Reader ps v.2.2 := by
    obtain ⟨y,rfl⟩ := dy
    obtain ⟨cb,rfl⟩ := db
    obtain ⟨cr,rfl⟩ := dr
    exact ⟨.view y cb cr hy hb hr _ (.inl rfl),.view y cb cr hy hb hr _ (.inr (.inl rfl)),
      .view y cb cr hy hb hr _ (.inr (.inr rfl))⟩
  unfold JPEG2000.ReversibleDispatch.colour at ok
  obtain ⟨_,_,tail⟩ := Tier2Equiv.bind_ok ok
  split at tail <;> try contradiction
  cases y <;> cases cb <;> cases cr <;> try (cases tail; exact views)
  dsimp only at tail
  split at tail
  · obtain ⟨⟨r,g,b⟩,_,last⟩ := Tier2Equiv.bind_ok tail
    cases last
    exact ⟨.direct (.compact r),.direct (.compact g),.direct (.compact b)⟩
  · cases tail; exact views

private theorem source_readers {L : Limits} {mct : Bool} {ps : Array Spatial} {out : Array Source}
    (pre : ∀ p ∈ ps, Direct p.source) (ok : JPEG2000.TileDispatch.sources L mct ps = .ok out) :
    ∀ s ∈ out, Reader ps s := by
  have direct {p : Source} (d : Direct p) : Reader ps p := by obtain ⟨p,rfl⟩ := d; exact .direct p
  have init : ∀ s ∈ ps.map (·.source), Reader ps s := by
    intro s hs
    obtain ⟨p,hp,rfl⟩ := Array.mem_map.mp hs
    exact direct (pre p hp)
  have replace (r g b : Source) (dr : Reader ps r) (dg : Reader ps g) (db : Reader ps b) :
      ∀ s ∈ replaceRGB ps (r,g,b), Reader ps s := by
    intro s hs
    rcases Array.mem_or_eq_of_mem_setIfInBounds hs with hs | rfl
    · rcases Array.mem_or_eq_of_mem_setIfInBounds hs with hs | rfl
      · rcases Array.mem_or_eq_of_mem_setIfInBounds hs with hs | rfl
        · exact init _ hs
        · exact dr
      · exact dg
    · exact db
  unfold JPEG2000.TileDispatch.sources at ok
  split at ok
  · cases ok; exact init
  dsimp only at ok
  split at ok <;> try contradiction
  · rename_i y cb cr hy hb hr
    obtain ⟨rgb,col,ret⟩ := Tier2Equiv.bind_ok ok
    cases ret
    obtain ⟨r,g,b⟩ := rct_readers hy hb hr (pre _ (Array.mem_of_getElem? hy)) (pre _ (Array.mem_of_getElem? hb))
      (pre _ (Array.mem_of_getElem? hr)) col
    exact replace _ _ _ r g b
  · obtain ⟨⟨r,g,b⟩,_,ret⟩ := Tier2Equiv.bind_ok ok
    cases ret
    exact replace _ _ _ (direct (direct_irrev r)) (direct (direct_irrev g)) (direct (direct_irrev b))

private theorem loop_members {α β : Type} {xs : Array α}
    (f : (j : Nat) → α → j < xs.size → Except Error β) (P : β → Prop)
    (hf : ∀ i (hi : i < xs.size) q, f i xs[i] hi = .ok q → P q)
    {ys : Array β} (ok : xs.mapFinIdxM f = .ok ys) : ∀ y ∈ ys, P y := by
  have all (k j : Nat) (len : k+j=xs.size) (acc : Array β) (init : ∀ x ∈ acc, P x)
      (run : Array.mapFinIdxM.map xs f k j len acc = .ok ys) : ∀ y ∈ ys, P y := by
    induction k generalizing j acc with
    | zero => cases run; exact init
    | succ k ih =>
      rw [Array.mapFinIdxM.map] at run
      obtain ⟨x,head,tail⟩ := Tier2Equiv.bind_ok run
      apply ih _ _ _ _ tail
      intro y hy
      rcases Array.mem_push.mp hy with hy | rfl
      · exact init _ hy
      · exact hf _ _ _ head
  exact all xs.size 0 rfl #[] (by simp) ok

private theorem backing_list (B : Nat) (ps : List Spatial) (all : ∀ p ∈ ps, Direct p.source) :
    ∃ bs : List Backing, bs.map Backing.source = ps.map Spatial.source ∧
      (bs.map (Backing.payload B)).sum ≤ (4+B)*(ps.map (fun p => area p.source)).sum := by
  induction ps with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons p ps ih =>
    obtain ⟨head,eq⟩ := all p (by simp)
    obtain ⟨tail,src,bound⟩ := ih (fun p hp => all p (by simp [hp]))
    refine ⟨head :: tail,by simp only [List.map_cons,eq,src],?_⟩
    simp only [List.map_cons,List.sum_cons,Nat.mul_add]
    exact Nat.add_le_add (eq ▸ backing_payload B head) bound

/-- The physical predecessor vector at the public entry point, including the
precise origins of its readers. All components share the one tile allowance.
A lazy RGB access stops after the three directly indexed predecessor planes. -/
theorem centeredTile_reads (B : Nat) {L : Limits} {data : ByteArray} {h : Header} {t red : Nat}
    {a : Option JPEG2000.Tier2.Packet.TileCodeBlocks} {b : Option Spec.Tier2.TileOut} {out : JPEG2000.Decode.CenteredTile}
    (parsed : Header.parse L data = .ok h) (stores : TileDispatch.Packets L h data t a b)
    (ok : JPEG2000.Decode.centeredTile L h data red t a = .ok out) :
    ∃ ps : Array Spatial,
      (preColourMeter B L h data out.layout out.coding a red).1 = .ok ps ∧
      ps.size ≤ L.maxComponents ∧ retained ps ≤ L.maxWorkSamples ∧
      (∃ bs : List Backing, bs.map Backing.source = ps.toList.map Spatial.source ∧
        (bs.map (Backing.payload B)).sum ≤ (4+B)*L.maxWorkSamples) ∧
      ∀ s ∈ out.sources, Reader ps s := by
  have admitted := NativeResources.centeredTile_work ok
  obtain ⟨⟨g,c⟩,layout,tail⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨src,tile,last⟩ := Tier2Equiv.bind_ok tail
  cases last
  obtain ⟨_,_,comp⟩ := Tier2Equiv.bind_ok tile
  obtain ⟨ps,run,colour⟩ := Tier2Equiv.bind_ok comp
  have provenance : ∀ p ∈ ps, Direct p.source := loop_members _ _ (fun _ _ _ => direct_component) run
  have meter : (preColourMeter B L h data g c a red).1 = .ok ps := (pre_value ..).trans run
  obtain ⟨n,cells⟩ := (preColour_work B parsed layout stores).2 ps meter
  refine ⟨ps,meter,n ▸ (HeaderWork.layout_budget parsed layout).1,cells ▸ admitted.2,?_,source_readers provenance colour⟩
  obtain ⟨bs,eq,le⟩ := backing_list B ps.toList (fun p hp => provenance p (by simpa using hp))
  exact ⟨bs,eq,Nat.le_trans le (Nat.mul_le_mul_left _ (cells ▸ admitted.2 : retained ps ≤ L.maxWorkSamples))⟩


/-- Once the header layout is selected, compose the two callbacks used by
`Decode.nativeFromHeader`. Component reconstruction is invoked to obtain its
actual results; only its returned rasters and descriptor traversal are priced. -/
def nativeTileMeter (B : Nat) (L : Limits) (h : Header) (data : ByteArray)
    (red : Nat) (g : Progression.Layout) (c : Coding) (store : Option JPEG2000.Tier2.Packet.TileCodeBlocks)
    (ds : Array OutputComponent) :=
  thenMeter (tileMeter B L h data g c store red) fun ps => writeTileMeter L h.siz red g c ds ps

/-- The ordinary centred-tile / G.1 continuation preserves the exact decoder
result, and the combined charge is bounded on both sides of every rejection.
`B` is the charge per wide integer payload. Output backing already allocated by
`allocOutput` has its independent physical bound in `NativeResources`. -/
theorem native_tile_work (B : Nat) {L : Limits} {h : Header} {data : ByteArray} {red t : Nat}
    {g : Progression.Layout} {c : Coding} {a : Option JPEG2000.Tier2.Packet.TileCodeBlocks} {b : Option Spec.Tier2.TileOut}
    (parsed : Header.parse L data = .ok h) (layout : Progression.Layout.ofHeader h t = .ok (g,c))
    (stores : TileDispatch.Packets L h data t a b) (ds : Array OutputComponent) :
    let m := nativeTileMeter B L h data red g c a ds
    m.1 = (JPEG2000.Decode.centeredTile L h data red t a >>= fun out =>
      writeTile L h.siz red out.layout out.coding ds out.sources) ∧
    m.2 ≤ 6+(13+L.maxImageSide)*L.maxComponents+(42+3*B)*L.maxWorkSamples := by
  obtain ⟨value,charge⟩ := tile_work B parsed layout stores (red := red)
  dsimp only [nativeTileMeter,thenMeter]
  cases run : (tileMeter B L h data g c a red).1 with
  | error e =>
    rw [run] at value
    refine ⟨by simp [JPEG2000.Decode.centeredTile,layout,← value,bind,Except.bind],?_⟩
    dsimp only
    simp only [Nat.add_mul] at *
    omega
  | ok ps =>
    rw [run] at value
    have centered : JPEG2000.Decode.centeredTile L h data red t a = .ok ⟨g,c,ps,0⟩ := by
      simp [JPEG2000.Decode.centeredTile,layout,← value,bind,Except.bind,pure,Except.pure]
    obtain ⟨writer,placed⟩ := centeredTile_placement parsed centered ds
    refine ⟨by rw [centered]; exact writer,?_⟩
    dsimp only at placed ⊢
    simp only [Nat.add_mul] at *
    omega


/-- The full G.1 source domain and its conservative G.2 predecessor-read
allowance across all written channels. Each lazy view can evaluate one RCT and
read the same index of three direct rasters (`centeredTile_reads`, `view_reads`).
A writer stopping on a prefix consumes at most this full domain. -/
theorem placement_read_domain {L : Limits} {data : ByteArray} {h : Header} {t red : Nat}
    {a : Option JPEG2000.Tier2.Packet.TileCodeBlocks} {b : Option Spec.Tier2.TileOut} {out : JPEG2000.Decode.CenteredTile}
    (parsed : Header.parse L data = .ok h) (stores : TileDispatch.Packets L h data t a b)
    (ok : JPEG2000.Decode.centeredTile L h data red t a = .ok out) :
    (out.sources.toList.map area).sum = Resources.tileCells out.layout red ∧
    (out.sources.toList.map (fun s => 3*area s)).sum ≤ 3*L.maxWorkSamples := by
  have sim := TileDispatch.parsed_tile parsed stores (red := red)
  rw [ok] at sim
  obtain ⟨_,_,rel⟩ := ok_right sim
  obtain ⟨_,src,_,_⟩ := rel.cells
  have dom := range_sum out.sources area (fun j => rectArea (grid out.layout red j)) (by
    intro i hi
    obtain ⟨plane,geo,_⟩ := src.2.2 i hi
    unfold area
    rw [plane.1,plane.2.1,geo.2.1,geo.2.2]
    rfl)
  rw [src.1] at dom
  have eq : (out.sources.toList.map area).sum = Resources.tileCells out.layout red := by
    rw [← dom]; simpa using grid_sum out.layout red 0 1
  have linear := linear_sum out.sources.toList area 0 3
  simp only [Nat.zero_add,Nat.zero_mul,eq] at linear
  exact ⟨eq,linear ▸ Nat.mul_le_mul_left 3 (NativeResources.centeredTile_work ok).2⟩


/-- Byte count for one signed-magnitude integer, rounded up to a whole byte. -/
def signedBytes (x : Int) := (x.natAbs.log2 + 2 + 7) / 8

/-- Maximum signed-magnitude bytes in a retained native component cell before MCT. -/
def componentBytes (L : Limits) := (374 + 540*L.maxDecompLevels + 7) / 8

/-- Packed backing keeps its stored bytes. For a wide vector, sum the rounded
signed-magnitude sizes of its actual integer cells. -/
def Backing.logicalBytes : Backing → Nat
  | .compact p => p.data.size
  | .wide w h v => (List.ofFn (fun i : Fin (w*h) => signedBytes (v.get i))).sum

private theorem cappedSum (xs : List Nat) (n : Nat) (each : ∀ x ∈ xs, x ≤ n) :
    xs.sum ≤ n*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have a := each x (by simp)
    have b := ih (fun y hy => each y (by simp [hy]))
    simp only [List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

private theorem logical_le (L : Limits) (b : Backing)
    (bits : ∀ j, (b.source.read j).natAbs.log2+2 ≤ 374+540*L.maxDecompLevels) :
    b.logicalBytes ≤ b.payload (componentBytes L) := by
  cases b with
  | compact p => exact Nat.le_refl _
  | wide w h v =>
    simp only [Backing.logicalBytes,Backing.payload,Vector.size_toArray]
    apply Nat.le_trans (cappedSum _ (componentBytes L) ?_)
    · simp [List.length_ofFn]
    intro n mem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
    have width := bits i
    change (v.get i).natAbs.log2 + 2 ≤ _ at width
    unfold signedBytes componentBytes
    omega

/-- Applies to a completed component even when the next component rejects:
a direct physical backing exists and its logical integer bytes fit the area charge. -/
theorem component_backing_bytes {L : Limits} {h : Header} {data : ByteArray} {t red : Nat}
    {g : Progression.Layout} {c : Coding} {a : Option JPEG2000.Tier2.Packet.TileCodeBlocks}
    (parsed : Header.parse L data = .ok h) (layout : Progression.Layout.ofHeader h t = .ok (g,c))
    (i : Fin g.numComps) {p : Spatial} (ok : JPEG2000.TileDispatch.component L h data g c a i red = .ok p) :
    ∃ b : Backing, b.source = p.source ∧ b.logicalBytes ≤ (4+componentBytes L)*area p.source := by
  obtain ⟨b,eq⟩ := direct_component ok
  have bits := Resources.component_signed_width parsed layout i a red ok
  rw [← eq] at bits ⊢
  exact ⟨b,rfl, Nat.le_trans (logical_le L b bits) (backing_payload _ b)⟩

private theorem logicalSum (L : Limits) (bs : List Backing)
    (each : ∀ b ∈ bs, b.logicalBytes ≤ b.payload (componentBytes L)) :
    (bs.map Backing.logicalBytes).sum ≤ (bs.map (Backing.payload (componentBytes L))).sum := by
  induction bs with
  | nil => exact Nat.le_refl _
  | cons b bs ih =>
    exact Nat.add_le_add (each b (by simp)) (ih (fun v hv => each v (by simp [hv])))

/-- The direct predecessors retained by a successfully centred tile have a
combined logical payload bounded in bytes, including wide cells at their actual
signed widths and the original sources shared by a lazy RCT reader. -/
theorem centeredTile_backing_bytes {L : Limits} {h : Header} {data : ByteArray} {t red : Nat}
    {a : Option JPEG2000.Tier2.Packet.TileCodeBlocks} {b : Option Spec.Tier2.TileOut}
    {out : JPEG2000.Decode.CenteredTile} (parsed : Header.parse L data = .ok h)
    (stores : TileDispatch.Packets L h data t a b) (ok : JPEG2000.Decode.centeredTile L h data red t a = .ok out) :
    ∃ (ps : Array Spatial) (bs : List Backing),
      (preColourMeter (componentBytes L) L h data out.layout out.coding a red).1 = .ok ps ∧
      bs.map Backing.source = ps.toList.map Spatial.source ∧
      (bs.map Backing.logicalBytes).sum ≤ (4+componentBytes L)*L.maxWorkSamples ∧
      ∀ s ∈ out.sources, Reader ps s := by
  obtain ⟨ps,run,_,_,⟨bs,eq,cap⟩,reads⟩ := centeredTile_reads (componentBytes L) parsed stores ok
  refine ⟨ps,bs,run,eq,Nat.le_trans (logicalSum L bs ?_) cap,reads⟩
  have layout := (NativeResources.centeredTile_work ok).1
  rw [pre_value] at run
  have widths := loop_members _ (fun p : Spatial => ∀ j, (p.source.read j).natAbs.log2+2 ≤
    374 + 540*L.maxDecompLevels) (fun i hi _ h => Resources.component_signed_width parsed layout ⟨i,hi⟩ a red h) run
  intro v hv
  have member : v.source ∈ ps.toList.map Spatial.source := eq ▸ List.mem_map.mpr ⟨v,hv,rfl⟩
  obtain ⟨p,hp,src⟩ := List.mem_map.mp member
  have bits := widths p (by simpa using hp)
  rw [src] at bits
  exact logical_le L v bits

end JPEG2000.Spec.Resources.TileColorPlacement
