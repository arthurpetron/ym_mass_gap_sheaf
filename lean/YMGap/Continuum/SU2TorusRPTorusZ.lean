/-
# Torus RP (d9w): the torus `∫ Π T_K` in `torusLinks` order equals the layout one

`lay_perm`: `torusLinks (2M) ~ Pt ++ Ct ++ Θ Pt`. With `perm_haar` this gives `torus_Z`: the actual torus
integral `∫_{|torusLinks|} Π_{torusPlaquettes} T_K[torusLinks]` equals the same product taken in layout order.
Observables and Θ are not transported yet.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPSwap
import YMGap.Continuum.SU2TorusRPPlaqSplit
import YMGap.Continuum.SU2TorusRPLayoutBounds
import YMGap.Continuum.SU2TorusRPPermExt

namespace YMGap.Continuum.SU2TorusRPTorusZ

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusRPGeom (reflLink linkSide)
open YMGap.Continuum.SU2TorusRPChoosePC (Pt Ct mem_Pt mem_Ct lay_nodup)
open YMGap.Continuum.SU2TorusRPSwap (plaqL perm_haar)

variable {M : Nat} (hM : 1 ≤ M)

theorem mem_tl (ℓ : Z4Link) : ℓ ∈ torusLinks (2 * M) ↔ InBox (2 * M) ℓ.1 := mem_torusLinks _ ℓ.1 ℓ.2

include hM in
theorem lay_perm : (torusLinks (2 * M)).Perm (Pt M ++ Ct M ++ (Pt M).map (reflLink M)) := by
  refine YMGap.Continuum.SU2TorusRPPermExt.perm_ext' _ _ (torusLinks_nodup _) (lay_nodup hM) fun ℓ => ⟨fun h => ?_,
    fun h => ?_⟩
  · exact YMGap.Continuum.SU2TorusRPLayoutBounds.mem_lay hM (Pt M) (Ct M)
      (fun ℓ hb hs => (mem_Ct ℓ).2 ⟨hb, hs⟩) (fun ℓ hb hs => (mem_Pt ℓ).2 ⟨hb, hs⟩) ℓ ((mem_tl ℓ).1 h)
  · refine (mem_tl ℓ).2 ?_
    rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · exact ((mem_Pt ℓ).1 h).1
      · exact ((mem_Ct ℓ).1 h).1
    · obtain ⟨x, hx, e⟩ := List.mem_map.1 h
      rw [← e]; exact YMGap.Continuum.SU2TorusRPMirGeom.refl_box hM x ((mem_Pt x).1 hx).1

include hM in
theorem plaqL_mem (p : Z4Plaq) (hp : p ∈ torusPlaquettes (2 * M)) : ∀ ℓ ∈ plaqL (2 * M) p, ℓ ∈ torusLinks (2 * M) := by
  have hb := (YMGap.Continuum.SU2TorusRPPlaqSplit.mem_tp p).1 hp
  have h0 : 0 < 2 * M := by omega
  intro ℓ hℓ
  unfold plaqL at hℓ
  rcases List.mem_cons.1 hℓ with e | hℓ
  · rw [e]; exact (mem_tl _).2 hb
  rcases List.mem_cons.1 hℓ with e | hℓ
  · rw [e]; exact (mem_tl _).2 (tAdd_inBox h0 hb _)
  rcases List.mem_cons.1 hℓ with e | hℓ
  · rw [e]; exact (mem_tl _).2 (tAdd_inBox h0 hb _)
  rcases List.mem_cons.1 hℓ with e | hℓ
  · rw [e]; exact (mem_tl _).2 hb
  exact absurd hℓ List.not_mem_nil

include hM in
/-- The actual torus `T_K` integral in `torusLinks` order equals the layout-order integral. -/
theorem torus_Z (β : Q') (K : Nat) :
    (quaternionHaar (torusLinks (2 * M)).length
        (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (torusLinks (2 * M)) (2 * M) β K)
          (torusPlaquettes (2 * M)))).eqv
      (quaternionHaar (Pt M ++ Ct M ++ (Pt M).map (reflLink M)).length
        (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (Pt M ++ Ct M ++ (Pt M).map (reflLink M)) (2 * M) β K)
          (torusPlaquettes (2 * M)))) := by
  rw [← (lay_perm hM).length_eq]
  exact perm_haar (2 * M) β K _ (lay_perm hM) (torusLinks_nodup _) (plaqL_mem hM)

end YMGap.Continuum.SU2TorusRPTorusZ

#print axioms YMGap.Continuum.SU2TorusRPTorusZ.lay_perm
#print axioms YMGap.Continuum.SU2TorusRPTorusZ.torus_Z
