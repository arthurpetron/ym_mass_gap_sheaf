/-
# Torus RP, K → ∞ step 2: telescoping the plaquette product and the Haar-level Cauchy bound

* `tele`: `Π_p (F_p ++ D_p) ≡PE Π_p F_p ++ E`, with an explicit error polynomial `E`.
* `l1_E`: `l1 E ≤ eb Λ δ |ps|`, where `eb Λ δ (m+1) = Λ·eb m + δ·Λ^m`, given `l1 F_p, l1 (F_p ++ D_p) ≤ Λ` and
  `l1 D_p ≤ δ`.
* `haar_diff`: `|∫ A·Π(F+D) − ∫ A·Π F| ≤ l1 A · eb Λ δ |ps|`.
-/

import YMGap.Continuum.SU2TorusRPKTail

namespace YMGap.Continuum.SU2TorusRPKProd

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_refl pe_trans pe_symm pe_append pe_haar)
open YMGap.Continuum.SU2TorusRPSubst (pe_mul2)
open YMGap.Continuum.SU2HaarL1Activity (l1 l1_nonneg l1_mul l1_add_le prodPoly prod_l1 haar_abs)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)

variable (F D : Z4Plaq → RatPoly)

/-- Telescoping error `E`. -/
def E : List Z4Plaq → RatPoly
  | [] => []
  | p :: ps => polyAdd (polyMul (F p) (E ps)) (polyMul (D p) (prodPoly (fun q => polyAdd (F q) (D q)) ps))

theorem tele (n : Nat) : ∀ ps : List Z4Plaq,
    PE n (prodPoly (fun q => polyAdd (F q) (D q)) ps) (polyAdd (prodPoly F ps) (E F D ps))
  | [] => by show PE n polyOne (polyOne ++ []); rw [List.append_nil]; exact pe_refl _ _
  | p :: ps => by
    show PE n (polyMul (F p ++ D p) (prodPoly (fun q => polyAdd (F q) (D q)) ps))
      (polyMul (F p) (prodPoly F ps) ++ (polyMul (F p) (E F D ps) ++
        polyMul (D p) (prodPoly (fun q => polyAdd (F q) (D q)) ps)))
    rw [YMGap.Continuum.SU2TorusRPBil.mul_app_l, ← List.append_assoc]
    exact pe_append n (pe_trans n (pe_mul2 n (pe_refl n _) (tele n ps))
      (YMGap.Continuum.SU2TorusRPBil.mul_app_r n _ _ _)) (pe_refl n _)

/-- Error envelope `eb Λ δ`. -/
def eb (Λ δ : Q') : Nat → Q'
  | 0 => 0
  | m + 1 => Λ * eb Λ δ m + δ * Λ ^ m

theorem l1_E {Λ δ : Q'} (hΛ : (0 : Q') ≤ Λ) (hδ : (0 : Q') ≤ δ) (hF : ∀ p, l1 (F p) ≤ Λ)
    (hF' : ∀ p, l1 (polyAdd (F p) (D p)) ≤ Λ) (hD : ∀ p, l1 (D p) ≤ δ) :
    ∀ ps : List Z4Plaq, l1 (E F D ps) ≤ eb Λ δ ps.length
  | [] => Q'.le_refl' 0
  | p :: ps => Q'.le_trans' _ _ _ (l1_add_le _ _) (YMGap.Constructive.ExpNeg.add_le_add2
      (Q'.le_trans' _ _ _ (l1_mul _ _) (Q'.mul_le_mul_of_nonneg (hF p) (l1_E hΛ hδ hF hF' hD ps) hΛ (l1_nonneg _)))
      (Q'.le_trans' _ _ _ (l1_mul _ _) (Q'.mul_le_mul_of_nonneg (hD p) (prod_l1 _ Λ hΛ hF' ps) hδ (l1_nonneg _))))

theorem haar_diff (n : Nat) (A : RatPoly) {Λ δ : Q'} (hΛ : (0 : Q') ≤ Λ) (hδ : (0 : Q') ≤ δ) (hF : ∀ p, l1 (F p) ≤ Λ)
    (hF' : ∀ p, l1 (polyAdd (F p) (D p)) ≤ Λ) (hD : ∀ p, l1 (D p) ≤ δ) (ps : List Z4Plaq) :
    Q'.abs (quaternionHaar n (polyMul A (prodPoly (fun q => polyAdd (F q) (D q)) ps)) +
      -quaternionHaar n (polyMul A (prodPoly F ps))) ≤ l1 A * eb Λ δ ps.length := by
  have h1 : (quaternionHaar n (polyMul A (prodPoly (fun q => polyAdd (F q) (D q)) ps))).eqv
      (quaternionHaar n (polyMul A (prodPoly F ps)) + quaternionHaar n (polyMul A (E F D ps))) :=
    Q'.eqv_trans _ _ _ (pe_haar n (pe_trans n (pe_mul2 n (pe_refl n A) (tele F D n ps))
      (YMGap.Continuum.SU2TorusRPBil.mul_app_r n _ _ _)))
      (YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_append _ _ _)
  have h2 : (quaternionHaar n (polyMul A (prodPoly (fun q => polyAdd (F q) (D q)) ps)) +
      -quaternionHaar n (polyMul A (prodPoly F ps))).eqv (quaternionHaar n (polyMul A (E F D ps))) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' h1 (Q'.eqv_refl _))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.add_comm_eqv _ _) (Q'.eqv_refl _))
        (YMGap.Continuum.SU2PolymerActivityBound.add_neg_cancel_q _ _))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (YMGap.Constructive.ExpNeg.abs_eqv_congr h2)) ?_
  exact Q'.le_trans' _ _ _ (haar_abs n _) (Q'.le_trans' _ _ _ (l1_mul _ _)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (l1_E F D hΛ hδ hF hF' hD ps) (l1_nonneg _)))

end YMGap.Continuum.SU2TorusRPKProd

#print axioms YMGap.Continuum.SU2TorusRPKProd.haar_diff
