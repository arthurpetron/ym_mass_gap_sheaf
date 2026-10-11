/-
# Selected ORIGINAL Haar coercivity at its OWN conditional partition

Project the complete original-action pointwise payment by the EXISTING
in-place finite Haar schedule. Finite selected Jensen is based at its OWN
partition at the unchanged retained assignment. No interacting factor is
independently integrated or discarded; identity normalization is not W/Z.

The explicit error is 256*(1-q)*(L+3*k*F)/(N+1). This finite conditional
estimate still requires explicit cutoff removal and the produced conditional
partition floor before a logarithmic UV estimate. It is not a source-relative
signed response bound, physical scaling, spectral gap or continuum result.
-/

import YMGap.Continuum.BF4ExactSlabOriginalProductEntropyCoercivity
import YMGap.Continuum.QuaternionHaarFamilyFiniteEntropy

namespace YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarEntropyCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS (evalRatPoly_smul evalRatPoly_one)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail (faceScalar)
open YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds
  (normalizedHeatProduct normalizedFloor_positive normalizedHeatProduct_bounds)
open YMGap.Continuum.SU2HeatJacobiOriginalCoercivity (coercivityCutoff)
open YMGap.Continuum.SU2HeatJacobiActiveFactorCount (activeFactorCount)
open YMGap.Continuum.RegularizedLogPolynomial (partialSum)
open YMGap.Continuum.RegularizedLogFiniteCoercivity (third)
open YMGap.Continuum.RegularizedLogFiniteProductCoercivity (selectedCount selectedDefectSum)
open YMGap.Continuum.BF4ExactSlabOriginalProductEntropyCoercivity
open YMGap.Continuum.QuaternionHaarFiniteEntropy (entropyStage entropyStage_eval)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject familyProject_add)
open YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder (familyProject_pointwise_mono)
open YMGap.Continuum.QuaternionHaarFamilyFiniteEntropy
  (familyProject_constant_eval familyProject_smul_eval family_partial_jensen)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem tc {a b c : Q'} (h : a ≈ b) (k : b ≈ c) : a ≈ c :=
  Q'.eqv_trans _ _ _ h k

private theorem eval_constant (rho : Nat → Q') (c : Q') :
    evalRatPoly rho (polySmul c polyOne) ≈ c :=
  tc (evalRatPoly_smul rho c polyOne)
    (tc (Q'.mul_eqv_congr_left _ _ _ (evalRatPoly_one rho)) (Q'.mul_one_eqv c))

private theorem scalar_defect_eval (rho : Nat → Q') (p : RatPoly) :
    evalRatPoly rho (polyAdd polyOne (polySmul (-1) p)) ≈ 1-evalRatPoly rho p :=
  tc (evalRatPoly_add rho polyOne (polySmul (-1) p))
    (Q'.add_eqv_congr' (evalRatPoly_one rho)
      (tc (evalRatPoly_smul rho (-1) p)
        (tc (Q'.neg_mul_eqv 1 (evalRatPoly rho p))
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (evalRatPoly rho p))))))

private theorem single_defect_eval (extent id : Nat) (qs : Nat → UnitNorm) :
    evalRatPoly (environment qs) (polyAdd polyOne (polySmul (-1) (faceScalar extent id))) ≈
      faceDefect extent qs id :=
  scalar_defect_eval (environment qs) (faceScalar extent id)

/-- Polynomial sum of selected actual face defects, retaining occurrences. -/
def selectedFaceDefectPolynomial (extent : Nat) (selected : Nat → Bool) : List Nat → RatPoly
  | [] => polyZero
  | id::ids => match selected id with
    | false => selectedFaceDefectPolynomial extent selected ids
    | true => polyAdd (polyAdd polyOne (polySmul (-1) (faceScalar extent id)))
        (selectedFaceDefectPolynomial extent selected ids)

/-- Literal evaluation pin for the selected defect sum on the SAME assignment. -/
theorem selectedFaceDefectPolynomial_eval (extent : Nat) (selected : Nat → Bool)
    (qs : Nat → UnitNorm) : ∀ ids : List Nat,
    evalRatPoly (environment qs) (selectedFaceDefectPolynomial extent selected ids) ≈
      selectedDefectSum (faceDefect extent qs) selected ids
  | [] => Q'.eqv_refl 0
  | id::ids => by
      cases hs : selected id with
      | false => simpa only [selectedFaceDefectPolynomial, selectedDefectSum, hs] using
          selectedFaceDefectPolynomial_eval extent selected qs ids
      | true => simpa only [selectedFaceDefectPolynomial, selectedDefectSum, hs] using
          (tc (evalRatPoly_add _ _ _)
            (Q'.add_eqv_congr' (single_defect_eval extent id qs)
              (selectedFaceDefectPolynomial_eval extent selected qs ids)))

/-- OWN partition of the complete original normalized weight under the actual
selected Haar schedule, at the unchanged retained assignment. -/
def originalSelectedPartition (q : Q') (hq0 : (0 : Q') < q)
    (K extent : Nat) (ids slots : List Nat) (qs : Nat → UnitNorm) : Q' :=
  evalRatPoly (environment qs) (familyProject slots (normalizedHeatProduct q hq0 K extent ids))

private theorem projected_rhs_eval (slots : List Nat) (W : RatPoly)
    (N : Nat) (c b e : Q') (rho : Nat → Q') :
    evalRatPoly rho (familyProject slots
      (polySmul c (polyAdd (polyAdd (entropyStage N W) (polySmul b W)) (polySmul e polyOne)))) ≈
      c*(evalRatPoly rho (familyProject slots (entropyStage N W))+
        b*evalRatPoly rho (familyProject slots W)+e) := by
  refine tc (familyProject_smul_eval slots c _ rho) (Q'.mul_eqv_congr_left _ _ _ ?_)
  rw [familyProject_add, familyProject_add]
  exact tc (evalRatPoly_add _ _ _)
    (Q'.add_eqv_congr'
      (tc (evalRatPoly_add _ _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (familyProject_smul_eval slots b W rho)))
      (familyProject_constant_eval slots e rho))

/-- Finite selected-Haar estimate for the SAME complete original action.
The Jensen term is evaluated at OWN selected Z, not the full Haar partition. -/
theorem original_selected_haar_coercivity_finite {q : Q'}
    (hq0 : (0 : Q') < q) (hq : Q'.mkPos 16 17 (by decide) ≤ q)
    (hq1 : q < (1 : Q')) (K extent : Nat) (ids slots : List Nat)
    (selected : Nat → Bool) (qs : Nat → UnitNorm)
    (hK : coercivityCutoff q ≤ K+1) (N : Nat) (hN : 1 ≤ N) :
    evalRatPoly (environment qs) (familyProject slots
        (polyMul (normalizedHeatProduct q hq0 K extent ids)
          (selectedFaceDefectPolynomial extent selected ids))) ≤
      (256*(1-q))*(partialSum (originalSelectedPartition q hq0 K extent ids slots qs) N+
        (3*partialSum third N)*Q'.ofNat (selectedCount selected ids)*
          originalSelectedPartition q hq0 K extent ids slots qs+
        (Q'.ofNat ids.length+3*Q'.ofNat (activeFactorCount q-1)*
          Q'.ofNat (selectedCount selected ids))*Q'.invSucc N) := by
  let W := normalizedHeatProduct q hq0 K extent ids
  let D := selectedFaceDefectPolynomial extent selected ids
  let c := (256 : Q')*(1-q)
  let b := (3*partialSum third N)*Q'.ofNat (selectedCount selected ids)
  let e := (Q'.ofNat ids.length+3*Q'.ofNat (activeFactorCount q-1)*
    Q'.ofNat (selectedCount selected ids))*Q'.invSucc N
  let R := polySmul c (polyAdd (polyAdd (entropyStage N W) (polySmul b W)) (polySmul e polyOne))
  have hR (heads : Nat → UnitNorm) : evalRatPoly (environment heads) R ≈
      c*(partialSum (evalRatPoly (environment heads) W) N+b*evalRatPoly (environment heads) W+e) :=
    tc (evalRatPoly_smul _ _ _) (Q'.mul_eqv_congr_left _ _ _
      (tc (evalRatPoly_add _ _ _)
        (Q'.add_eqv_congr'
          (tc (evalRatPoly_add _ _ _)
            (Q'.add_eqv_congr' (entropyStage_eval N W _) (evalRatPoly_smul _ _ _)))
          (eval_constant _ e))))
  have hpoint (heads : Nat → UnitNorm) :
      evalRatPoly (environment heads) (polyMul W D) ≤ evalRatPoly (environment heads) R :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (tc (evalRatPoly_mul _ _ _)
        (Q'.mul_eqv_congr_left _ _ _ (selectedFaceDefectPolynomial_eval extent selected heads ids))))
      (Q'.le_trans' _ _ _
        (original_selected_product_coercivity_finite hq0 hq hq1 K extent ids selected heads hK N hN)
        (Q'.ge_of_eqv (hR heads)))
  have hp := familyProject_pointwise_mono slots (polyMul W D) R hpoint qs
  have hKf : SU2PointwiseHeatStrictFloor.finiteCutoff q ≤ K+1 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hK
  have hu (heads : Nat → UnitNorm) : evalRatPoly (environment heads) W ≤ (1 : Q') :=
    (normalizedHeatProduct_bounds hq0 hq1 K extent ids hKf heads).2
  have hj := family_partial_jensen slots W hu qs N
  have hc : (0 : Q') ≤ c := Q'.mul_nonneg _ _ (by decide)
    (Q'.le_of_lt (HKPos.one_sub_pos hq1))
  exact Q'.le_trans' _ _ _ hp
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (projected_rhs_eval slots W N c b e (environment qs)))
      (Q'.mul_le_mul_of_nonneg_left _ _ c
        (Q'.add_le_add_right _ _ _ (Q'.add_le_add_right _ _ _ hj)) hc))

end YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarEntropyCoercivity

#print axioms YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarEntropyCoercivity.selectedFaceDefectPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarEntropyCoercivity.selectedFaceDefectPolynomial_eval
#print axioms YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarEntropyCoercivity.originalSelectedPartition
#print axioms YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarEntropyCoercivity.original_selected_haar_coercivity_finite
