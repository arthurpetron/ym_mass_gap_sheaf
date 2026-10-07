/-
# Torus RP (f4): bilinearity of the RP form and Cauchy–Schwarz for link observables

`rpB` is additive and `Q'`-homogeneous in each argument (`bil_add_l/r`, `bil_smul_l/r`). With `rpB_symm`,
`torus_rp` at `s·e + t·e'` and `cs_q`, this gives `torus_cs_obs`:
`rpB F G · rpB F G ≤ rpB F F · rpB G G` for `F = eval e`, `G = eval e'` on positive links (truncated T_K weight,
fixed K). Constructive (rational polarization), with no reals and no Classical.
-/

import YMGap.Continuum.SU2TorusRPSym
import YMGap.Continuum.BF4CompactActionCPOrder
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.SU2TorusRPBil

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_refl pe_symm pe_haar pe_comm pe_mulR pe_mulL pe_append pe_assoc)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusRPSubst (pe_smul)
open YMGap.Continuum.SU2TorusRPObs (Obs eval OnLinks thetaT)
open YMGap.Continuum.SU2TorusRPCSShape (rpB)

theorem cmul_eq (c : Q') (Z : RatPoly) : polyMul [([], c)] Z = polySmul c Z := by
  unfold polyMul polySmul
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

theorem mul_app_l (A B Y : RatPoly) : polyMul (A ++ B) Y = polyMul A Y ++ polyMul B Y := by
  unfold polyMul; rw [List.flatMap_append]

theorem mul_app_r (n : Nat) (A Y Z : RatPoly) : PE n (polyMul A (Y ++ Z)) (polyMul A Y ++ polyMul A Z) := by
  refine pe_trans n (pe_comm n _ _) ?_
  rw [mul_app_l]
  exact pe_append n (pe_comm n _ _) (pe_comm n _ _)

theorem mul_smul_l (n : Nat) (c : Q') (A Y : RatPoly) : PE n (polyMul (polySmul c A) Y) (polySmul c (polyMul A Y)) := by
  rw [← cmul_eq, ← cmul_eq]; exact pe_assoc n _ _ _

theorem mul_smul_r (n : Nat) (c : Q') (A Y : RatPoly) : PE n (polyMul A (polySmul c Y)) (polySmul c (polyMul A Y)) :=
  pe_trans n (pe_comm n _ _) (pe_trans n (mul_smul_l n c Y A) (pe_smul n c (pe_comm n _ _)))

variable {M : Nat} (hM : 1 ≤ M) (β : Q') (K : Nat)

theorem hR : YMGap.Continuum.SU2TorusRPSubst.RingSub (torusLinks (2 * M)).length (thetaT hM) :=
  (YMGap.Continuum.SU2TorusRPMatch.thetaT_like hM).ring

theorem bil_add_l (X₁ X₂ Y : RatPoly) :
    (rpB hM β K (polyAdd X₁ X₂) Y).eqv (rpB hM β K X₁ Y + rpB hM β K X₂ Y) := by
  unfold rpB
  refine Q'.eqv_trans _ _ _ (pe_haar _ (pe_mulR _ _ (pe_mulR _ Y ((hR hM).add X₁ X₂)))) ?_
  show (quaternionHaar _ (polyMul (polyMul (thetaT hM X₁ ++ thetaT hM X₂) Y) _)).eqv _
  rw [mul_app_l, mul_app_l]
  exact YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_append _ _ _

theorem bil_add_r (X Y₁ Y₂ : RatPoly) :
    (rpB hM β K X (polyAdd Y₁ Y₂)).eqv (rpB hM β K X Y₁ + rpB hM β K X Y₂) := by
  unfold rpB
  refine Q'.eqv_trans _ _ _ (pe_haar _ (pe_mulR _ _ (mul_app_r _ (thetaT hM X) Y₁ Y₂))) ?_
  rw [mul_app_l]
  exact YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_append _ _ _

theorem bil_smul_l (c : Q') (X Y : RatPoly) : (rpB hM β K (polySmul c X) Y).eqv (c * rpB hM β K X Y) := by
  unfold rpB
  refine Q'.eqv_trans _ _ _ (pe_haar _ (pe_mulR _ _ (pe_trans _ (pe_mulR _ Y ((hR hM).smul c X))
    (mul_smul_l _ c _ Y)))) ?_
  refine Q'.eqv_trans _ _ _ (pe_haar _ (mul_smul_l _ c _ _)) ?_
  exact YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_polySmul _ _ _

theorem bil_smul_r (c : Q') (X Y : RatPoly) : (rpB hM β K X (polySmul c Y)).eqv (c * rpB hM β K X Y) := by
  unfold rpB
  refine Q'.eqv_trans _ _ _ (pe_haar _ (pe_mulR _ _ (mul_smul_r _ c _ Y))) ?_
  refine Q'.eqv_trans _ _ _ (pe_haar _ (mul_smul_l _ c _ _)) ?_
  exact YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_polySmul _ _ _

end YMGap.Continuum.SU2TorusRPBil

#print axioms YMGap.Continuum.SU2TorusRPBil.bil_add_l
#print axioms YMGap.Continuum.SU2TorusRPBil.bil_add_r
#print axioms YMGap.Continuum.SU2TorusRPBil.bil_smul_l
#print axioms YMGap.Continuum.SU2TorusRPBil.bil_smul_r
