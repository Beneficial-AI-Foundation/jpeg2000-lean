import Spec.Resources.PacketTraversal
import Spec.Resources.HeaderWork

/-!
# Packet work at the public codestream entry point

Plan.md §§3–5, 7 (S3), T.800 Annex B. Admission errors have an empty packet
trace. Once the native output grids exist, the trace includes the actual tile
reconstruction and placement callbacks, including any prefix preceding an error.
-/

namespace JPEG2000.Spec.Resources.PublicPacketWork

open PacketTraversal

/-- The production prefix that admits a reduction, parses the header and allocates
the native destinations before attempting the first packet. -/
def prepareTiles (L : Limits) (data : ByteArray) (reduce : Nat) :
    Except Error (Header.Header × Array JPEG2000.NativeOutput.OutputComponent) := do
  L.check JPEG2000.Decode.loc .decompLevels reduce
  let h ← Header.parse L data
  let initial ← JPEG2000.NativeOutput.allocOutput L h.siz reduce
  return (h, initial)

/-- Observe packet positions and admitted passes during a public native decode. -/
def measure (L : Limits) (data : ByteArray) (reduce : Nat) : Measured TileVisit CodestreamImage :=
  before (prepareTiles L data reduce) fun (h, initial) =>
    measureTiles L h data initial (JPEG2000.Decode.centeredTile L h data reduce) (·.saturated)
      (fun dst t => JPEG2000.NativeOutput.writeTile L h.siz reduce t.layout t.coding dst t.sources)
      (fun ds sat => ⟨h, reduce, ds.map .native, sat⟩)

/-- The instrumented outcome is the public result, including every diagnostic.
Tile visits, packet attempts, physical positions, progression work and admitted
coding passes obey their budgets on both success and rejection. -/
theorem decode_packet_work (L : Limits) (data : ByteArray) (reduce : Nat) :
    let m := measure L data reduce
    m.2 = decodeCodestream L data reduce ∧ m.1.length ≤ L.maxTiles ∧
      imageAttempts m.1 ≤ imagePositions m.1 ∧ imagePositions m.1 + imageTests m.1 ≤ imageCharge m.1 ∧
      imageCharge m.1 ≤ L.maxTiles * L.maxPackets ∧ imagePasses m.1 ≤ L.maxCodingPasses := by
  simp only [measure, prepareTiles, decodeCodestream, JPEG2000.Decode.nativeFromHeader]
  cases hc : L.check JPEG2000.Decode.loc .decompLevels reduce with
  | error e => simp [before, bind, Except.bind, imageAttempts, imagePositions, imageTests, imageCharge, imagePasses]
  | ok u =>
    cases hp : Header.parse L data with
    | error e => simp [before, bind, Except.bind, imageAttempts, imagePositions, imageTests, imageCharge, imagePasses]
    | ok h =>
      cases ha : JPEG2000.NativeOutput.allocOutput L h.siz reduce with
      | error e => simp [before, bind, Except.bind, imageAttempts, imagePositions, imageTests, imageCharge, imagePasses, ha]
      | ok initial =>
        simp only [before, bind, Except.bind, ha]
        refine ⟨measureTiles_erase hp .., ?_⟩
        obtain ⟨_, _, tiles, _, calls, positions, _, cost, passes⟩ :=
          measureTiles_bounds hp initial (JPEG2000.Decode.centeredTile L h data reduce) (·.saturated)
            (fun dst t => JPEG2000.NativeOutput.writeTile L h.siz reduce t.layout t.coding dst t.sources)
            (fun ds sat => (⟨h, reduce, ds.map .native, sat⟩ : CodestreamImage))
        exact ⟨tiles, calls, positions, cost, passes⟩

/-- Any admission failure reaches both public APIs with its original diagnostic
and an empty packet trace, including header and output allocation failures. -/
theorem admission_error {L : Limits} {data : ByteArray} {opts : DecodeOptions} {e : Error}
    (rejected : prepareTiles L data opts.reduce = .error e) :
    measure L data opts.reduce = ([], .error e) ∧
    decodeCodestream L data opts.reduce = .error e ∧ JPEG2000.decode L data opts = .error e := by
  have empty : measure L data opts.reduce = ([], .error e) := by
    simp [measure, rejected, before]
  have raw := (decode_packet_work L data opts.reduce).1
  rw [empty] at raw
  refine ⟨empty, raw.symm, ?_⟩
  simp [JPEG2000.decode, raw.symm, bind, Except.bind]

/-- When reduction or input length is excessive, the reduction check takes
precedence. The input-size diagnostic points to byte zero of the container. -/
theorem admission_excess {L : Limits} {data : ByteArray} {red : Nat}
    (over : L.maxDecompLevels < red ∨ L.maxInputBytes < data.size) :
    prepareTiles L data red = .error (if L.maxDecompLevels < red then
      .limitExceeded JPEG2000.Decode.loc .decompLevels red L.maxDecompLevels
    else .limitExceeded (.atOffset .box 0) .inputBytes data.size L.maxInputBytes) := by
  by_cases levels : L.maxDecompLevels < red
  · simp [prepareTiles, Limits.check, Limits.checkLe, Limits.bound, levels,
      Nat.not_le_of_lt levels, bind, Except.bind]
  · have input := HeaderWork.parse_input_excess (over.resolve_left levels)
    simp [prepareTiles, Limits.check, Limits.checkLe, Limits.bound, levels,
      Nat.le_of_not_lt levels, input, bind, Except.bind]

end JPEG2000.Spec.Resources.PublicPacketWork
