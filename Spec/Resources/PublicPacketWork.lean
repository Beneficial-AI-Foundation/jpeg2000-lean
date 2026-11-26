import Spec.Resources.PacketTraversal
import JPEG2000.Decode

/-!
# Packet work at the public codestream entry point

Plan.md §§3–5, 7 (S3), T.800 Annex B. Admission errors have an empty packet
trace. Once the native output grids exist, the trace includes the actual tile
reconstruction and placement callbacks, including any prefix preceding an error.
-/

namespace JPEG2000.Spec.Resources.PublicPacketWork

open PacketTraversal

/-- Observe packet positions and admitted passes during a public native decode. -/
def measure (L : Limits) (data : ByteArray) (reduce : Nat) : Measured TileVisit CodestreamImage :=
  before (L.check JPEG2000.Decode.loc .decompLevels reduce) fun _ =>
  before (Header.parse L data) fun h =>
  before (JPEG2000.NativeOutput.allocOutput L h.siz reduce) fun initial =>
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
  simp only [measure, decodeCodestream, JPEG2000.Decode.nativeFromHeader]
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

end JPEG2000.Spec.Resources.PublicPacketWork
