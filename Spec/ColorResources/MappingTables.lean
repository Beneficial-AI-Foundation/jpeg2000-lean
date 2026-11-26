import Spec.ColorResources.Palette
import Spec.Resources.HeaderWork

/-!
# Retained JP2 mapping tables (Plan.md §§3–5, 7, S3; T.800 I.5.3.3–6)

A retained CMAP has one entry per four bytes of its box body. Each retained
colour specification came from a separately counted child box of JP2H.
-/

namespace JPEG2000.Spec.ColorResources.MappingPrefix

open JPEG2000 JPEG2000.Color JPEG2000.Box JPEG2000.Bytes
open Tier2Equiv (bind_ok)
open Resources.HeaderWork (readBox_extent)

/-- Counts of retained colour specifications and CMAP entries, including absent boxes. -/
def Retained (L : Limits) (bytes : Nat) (hdr : Option Jp2Header) : Prop :=
  ((hdr.map Jp2Header.colr).getD #[]).size ≤ L.maxBoxes ∧
  ((hdr.bind Jp2Header.cmap).getD #[]).size ≤ bytes / 4

private theorem cmap_size {b es} (h : parseCmap b = .ok es) :
    es.size ≤ b.body.data.size / 4 := by
  have many {α : Type} (f : Reader → Except Error (α × Reader)) :
      ∀ k r acc out, readMany f r acc k = .ok out → out.1.size = acc.size+k := by
    intro k
    induction k with
    | zero => intro _ _ _ h; cases h; rfl
    | succ k ih =>
      intro r acc out h
      rw [readMany] at h
      obtain ⟨⟨v,t⟩,_,h⟩ := bind_ok h
      rw [ih _ _ _ h, Array.size_push]; omega
  unfold parseCmap at h
  dsimp only at h
  split at h <;> try contradiction
  obtain ⟨⟨a,t⟩,ha,h⟩ := bind_ok h
  cases h
  have len : a.size = b.body.remaining / 4 := by simpa using many _ _ _ _ _ ha
  rw [len]
  apply Nat.div_le_div_right
  exact Nat.le_trans (Nat.sub_le ..) b.body.stop_le

private theorem added {L a b out} (ok : addHeaderBox L a b = .ok out)
    (cm : (a.cmap.getD #[]).size ≤ b.body.data.size / 4) :
    out.colr.size ≤ a.colr.size+1 ∧ (out.cmap.getD #[]).size ≤ b.body.data.size / 4 := by
  unfold addHeaderBox at ok
  repeat' first
    | (split at ok <;> try contradiction)
    | (obtain ⟨_, _, ok⟩ := bind_ok ok)
  all_goals cases ok
  all_goals exact ⟨by simp, by first | exact cm | exact cmap_size (by assumption)⟩

private theorem children {L : Limits} :
    ∀ k r a n out, a.colr.size ≤ min n L.maxBoxes →
      (a.cmap.getD #[]).size ≤ r.data.size / 4 →
      headerLoop L r a n k = .ok out →
      out.1.colr.size ≤ L.maxBoxes ∧ (out.1.cmap.getD #[]).size ≤ r.data.size / 4
  | 0,r,a,n,out,hc,hm,ok => by
    simp only [headerLoop] at ok
    split at ok <;> cases ok
    exact ⟨Nat.le_trans hc (Nat.min_le_right ..),hm⟩
  | k+1,r,a,n,out,hc,hm,ok => by
    rw [headerLoop] at ok
    split at ok
    · cases ok; exact ⟨Nat.le_trans hc (Nat.min_le_right ..),hm⟩
    · obtain ⟨u,hcheck,ok⟩ := bind_ok ok
      obtain ⟨⟨b,t⟩,hb,ok⟩ := bind_ok ok
      obtain ⟨a',ha,ok⟩ := bind_ok ok
      have same := readBox_extent hb
      obtain ⟨h₁,h₂⟩ := added ha (same.2.1 ▸ hm)
      have bound : n+1 ≤ L.maxBoxes := (Limits.check_eq_ok_iff ..).mp hcheck
      rw [← same.2.2.1]
      apply children k _ _ _ _ _ _ ok
      · omega
      · simpa only [same.2.2.1, same.2.1] using h₂

private theorem jp2h {L b n h} (ok : parseJp2h L b n = .ok h) :
    Retained L b.body.data.size (some h.1) := by
  unfold parseJp2h at ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨⟨a,n'⟩,ha,ok⟩ := bind_ok ok
  have g := children _ _ _ _ _ (Nat.zero_le _) (Nat.zero_le _) ha
  dsimp only at ok
  repeat' first | (split at ok <;> try contradiction) | (obtain ⟨_,_,ok⟩ := bind_ok ok)
  all_goals cases ok; exact g

private theorem top {L : Limits} :
    ∀ k r h n out, Retained L r.data.size h → topLoop L r h n k = .ok out →
      Retained L r.data.size (some out.1)
  | 0,r,h,n,out,g,ok => by simp only [topLoop] at ok; split at ok <;> contradiction
  | k+1,r,h,n,out,g,ok => by
    rw [topLoop] at ok
    split at ok <;> try contradiction
    obtain ⟨_,_,ok⟩ := bind_ok ok
    obtain ⟨⟨b,t⟩,hb,ok⟩ := bind_ok ok
    have same := readBox_extent hb
    dsimp only at ok
    split at ok
    · split at ok <;> try contradiction
      cases ok; exact g
    · rw [← same.2.2.1]
      split at ok
      · obtain ⟨⟨a,n'⟩,ha,ok⟩ := bind_ok ok
        exact top k _ _ _ _ (by simpa [same.2.1,same.2.2.1] using jp2h ha) ok
      · exact top k _ _ _ _ (same.2.2.1 ▸ g) ok

private theorem file_bounds {L data c} (ok : parseFile L data = .ok c) :
    Retained L data.size c.header := by
  obtain ⟨a,aux,h⟩ := bind_ok ok
  unfold parseFileAux at aux
  obtain ⟨_,_,aux⟩ := bind_ok aux
  split at h <;> cases h
  split at aux
  · cases aux; simp [Retained]
  · dsimp only at aux
    split at aux <;> try contradiction
    rename_i sigread
    obtain ⟨⟨sig,r⟩,hs,aux⟩ := bind_ok aux
    cases hs
    simp only [pure_bind] at aux
    split at aux <;> try contradiction
    obtain ⟨⟨v,t⟩,hv,aux⟩ := bind_ok aux
    split at aux <;> try contradiction
    obtain ⟨⟨fb,u⟩,hf,aux⟩ := bind_ok aux
    split at aux <;> try contradiction
    obtain ⟨ft,_,aux⟩ := bind_ok aux
    obtain ⟨⟨h,cs⟩,hr,aux⟩ := bind_ok aux
    cases aux
    have g := top _ _ _ _ _ (by simp [Retained]) hr
    have ⟨_,_,hfirst,_⟩ := readBox_extent sigread
    simpa only [(readBox_extent hf).2.2.1,hfirst,
      Reader.ofByteArray] using g

private theorem header_bounds {L data h} (ok : Header.parse L data = .ok h) :
    Retained L data.size (h.container.bind Container.header) := by
  obtain ⟨c,hc,ok⟩ := bind_ok ok
  unfold Header.parseCodestreamIn at ok
  obtain ⟨r,_,ok⟩ := bind_ok ok
  obtain ⟨⟨mh,r⟩,_,ok⟩ := bind_ok ok
  obtain ⟨_,_,ok⟩ := bind_ok ok
  obtain ⟨defaults,_,ok⟩ := bind_ok ok
  obtain ⟨⟨tlm,ppm⟩,_,ok⟩ := bind_ok ok
  repeat obtain ⟨_,_,ok⟩ := bind_ok ok
  cases ok
  by_cases present : c.fileType.isSome = true
  · simpa only [present, ↓reduceIte, Option.bind_some] using file_bounds hc
  · simp [present, Retained]

/-- A successful native result retains at most one colour box per admitted box
and one CMAP entry per four input bytes. -/
theorem retained_counts {L data reduce d} (ok : decodeCodestream L data reduce = .ok d) :
    Retained L data.size (d.header.container.bind Container.header) ∧
    d.header.siz.components.size ≤ L.maxComponents ∧ d.comps.size ≤ L.maxComponents := by
  obtain ⟨_,_,tail⟩ := bind_ok ok
  obtain ⟨h,hp,_⟩ := bind_ok tail
  have same := (CodestreamDispatch.native_geometry hp ok).1
  have count := (Resources.HeaderWork.parse_storage hp).2.1
  have shape := (NativeResources.decodeCodestream_resources ok).geometry.1
  rw [same] at shape ⊢
  simp only [JPEG2000.NativeOutput.layout, Array.size_map] at shape
  exact ⟨header_bounds hp,count,shape ▸ count⟩

end JPEG2000.Spec.ColorResources.MappingPrefix
