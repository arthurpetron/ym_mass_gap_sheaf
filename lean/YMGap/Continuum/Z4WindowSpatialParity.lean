/-
# Three-layer temporal support has a unique binary parity continuation

The exact spatial incidences at the four window slices are a, a+b,
b+c, and c. Distinct faces make a,b,c zero or one. If the two endpoint
charges are also bits, even total charge forces all five bits equal.
No cycle classification or geometric path is assumed.
-/

import YMGap.Continuum.Z4TemporalSpatialIncidence

namespace YMGap.Continuum.Z4WindowSpatialParity

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4ThreeCutSaturation
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry
open YMGap.Continuum.Z4UnitCubeIncidenceParity

theorem cut_outside_window (margin time : Nat)
    (h0 : time ≠ margin) (h1 : time ≠ margin+1) (h2 : time ≠ margin+2) :
    ∀ faces : List Z4Plaq, (∀ f, f ∈ faces → window margin f = true) → cut time faces = []
  | [], _ => rfl
  | f::fs, hw => by
    have hc : crosses time f = false := by
      cases he : crosses time f with
      | false => rfl
      | true =>
        have ht := (of_decide_eq_true he).2
        rcases window_times (hw f List.mem_cons_self) with h | h | h
        · exact False.elim (h0 (ht.symm.trans h))
        · exact False.elim (h1 (ht.symm.trans h))
        · exact False.elim (h2 (ht.symm.trans h))
    simpa only [cut, List.filter_cons, hc] using
      cut_outside_window margin time h0 h1 h2 fs (fun g hg => hw g (List.mem_cons_of_mem f hg))

theorem spatial_bottom (margin : Nat) (link : Z4Link) (hd : link.2 ≠ .x3)
    (faces : List Z4Plaq) (hw : ∀ f, f ∈ faces → window margin f = true) :
    faceIncidenceCount (atTime margin link) faces = cutCount margin link faces := by
  have ht := fun f hf => window_temporal (hw f hf)
  cases margin with
  | zero => exact spatial_zero link hd faces ht
  | succ n =>
    have hs := spatial_next n link hd faces ht
    have hz : cutCount n link faces = 0 := by
      rw [cutCount, cut_outside_window (n+1) n (by omega) (by omega) (by omega) faces hw]
      rfl
    simpa only [hz, Nat.add_zero] using hs

theorem spatial_top (margin : Nat) (link : Z4Link) (hd : link.2 ≠ .x3)
    (faces : List Z4Plaq) (hw : ∀ f, f ∈ faces → window margin f = true) :
    faceIncidenceCount (atTime (margin+3) link) faces = cutCount (margin+2) link faces := by
  have ht := fun f hf => window_temporal (hw f hf)
  have hs := spatial_next (margin+2) link hd faces ht
  have hz : cutCount (margin+3) link faces = 0 := by
    rw [cutCount, cut_outside_window margin (margin+3) (by omega) (by omega) (by omega) faces hw]
    rfl
  simpa only [show (margin+2)+1 = margin+3 by omega, hz, Nat.zero_add] using hs

theorem binary_strip (lo a b c hi : Nat) (hlo : lo ≤ 1) (ha : a ≤ 1)
    (hb : b ≤ 1) (hc : c ≤ 1) (hhi : hi ≤ 1)
    (h0 : (lo+a) % 2 = 0) (h1 : (a+b) % 2 = 0)
    (h2 : (b+c) % 2 = 0) (h3 : (c+hi) % 2 = 0) :
    a = lo ∧ b = lo ∧ c = lo ∧ hi = lo := by
  have eq_bits (u v : Nat) (hu : u ≤ 1) (hv : v ≤ 1)
      (hp : (u+v) % 2 = 0) : u = v := by
    have hu' : u = 0 ∨ u = 1 := by omega
    have hv' : v = 0 ∨ v = 1 := by omega
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl <;> simp_all
  have hla := eq_bits lo a hlo ha h0
  have hab := eq_bits a b ha hb h1
  have hbc := eq_bits b c hb hc h2
  have hch := eq_bits c hi hc hhi h3
  exact ⟨hla.symm, hab.symm.trans hla.symm,
    hbc.symm.trans (hab.symm.trans hla.symm),
    hch.symm.trans (hbc.symm.trans (hab.symm.trans hla.symm))⟩

theorem window_parity_unique (margin : Nat) (link : Z4Link) (hd : link.2 ≠ .x3)
    (faces : List Z4Plaq) (hn : faces.Nodup) (hw : ∀ f, f ∈ faces → window margin f = true)
    (lo hi : Nat) (hlo : lo ≤ 1) (hhi : hi ≤ 1)
    (h0 : (lo + faceIncidenceCount (atTime margin link) faces) % 2 = 0)
    (h1 : faceIncidenceCount (atTime (margin+1) link) faces % 2 = 0)
    (h2 : faceIncidenceCount (atTime (margin+2) link) faces % 2 = 0)
    (h3 : (faceIncidenceCount (atTime (margin+3) link) faces + hi) % 2 = 0) :
    cutCount margin link faces = lo ∧ cutCount (margin+1) link faces = lo ∧
      cutCount (margin+2) link faces = lo ∧ hi = lo := by
  have ht := fun f hf => window_temporal (hw f hf)
  rw [spatial_bottom margin link hd faces hw] at h0
  rw [spatial_next margin link hd faces ht] at h1
  have hs := spatial_next (margin+1) link hd faces ht
  rw [show (margin+1)+1 = margin+2 by omega] at hs
  rw [hs] at h2
  rw [spatial_top margin link hd faces hw] at h3
  exact binary_strip lo _ _ _ hi hlo
    (cutCount_le_one margin link faces hn) (cutCount_le_one (margin+1) link faces hn)
    (cutCount_le_one (margin+2) link faces hn) hhi h0 (by omega) (by omega) h3

end YMGap.Continuum.Z4WindowSpatialParity

#print axioms YMGap.Continuum.Z4WindowSpatialParity.cut_outside_window
#print axioms YMGap.Continuum.Z4WindowSpatialParity.spatial_bottom
#print axioms YMGap.Continuum.Z4WindowSpatialParity.spatial_top
#print axioms YMGap.Continuum.Z4WindowSpatialParity.binary_strip
#print axioms YMGap.Continuum.Z4WindowSpatialParity.window_parity_unique
