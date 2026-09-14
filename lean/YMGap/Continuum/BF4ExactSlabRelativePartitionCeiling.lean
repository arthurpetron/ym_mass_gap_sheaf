/-
# Upper relative comparison for the original shared-link partition

Inserting only the removed faces costs (1+delta)^|removed|. Both the
background and full partition are the original Haar integrals. No cost
proportional to the ambient volume is introduced. All coupling guards remain
explicit, and the result alone does not bound a connected numerator.
-/

import YMGap.Continuum.BF4ExactSlabRelativePartitionBound
import YMGap.Continuum.TotalMajorantClose

namespace YMGap.Continuum.BF4ExactSlabRelativePartitionCeiling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

def removalCeiling (w : Q') (count : Nat) : Q' := (1+heatRemainderBound w)^count

theorem removalCeiling_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (count : Nat) :
    (0 : Q') ≤ removalCeiling w count := Q'.pow_nonneg _
      (Q'.zero_le_add _ _ Q'.zero_le_one (heatRemainderBound_nonnegative hw)) count

section SmallNome

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hdelta : heatRemainderBound w ≤ 1)
include hw0 hw1 hsmall hdelta

theorem relative_ceiling (K extent : Nat) (background : List Nat)
    (hb : ∀ id, id ∈ background → id ∈ slabPhysicalFaceEdges extent) :
    ∀ removed : List Nat, (∀ id, id ∈ removed → id ∈ slabPhysicalFaceEdges extent) →
      heatProductHaar w (boundaryCompleteSlabLinks extent).length extent (removed++background) K ≤
        removalCeiling w removed.length * heatProductHaar w (boundaryCompleteSlabLinks extent).length extent background K
  | [], _ => Q'.ge_of_eqv (Q'.one_mul_eqv _)
  | id::removed, hi => by
    have ht : ∀ j, j ∈ removed → j ∈ slabPhysicalFaceEdges extent := fun j hj => hi j (List.mem_cons_of_mem id hj)
    have hbg : ∀ j, j ∈ removed++background → j ∈ slabPhysicalFaceEdges extent := by
      intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · exact ht j hj
      · exact hb j hj
    have h := insertFace_upper hw0 hw1 hsmall extent id (hi id List.mem_cons_self) K
      (faceProductCertificate hw0 hw1 hsmall hdelta K extent (removed++background) hbg)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))
      (Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (relative_ceiling K extent background hb removed ht)
          (Q'.zero_le_add _ _ Q'.zero_le_one (heatRemainderBound_nonnegative hw0)))
        (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))))

theorem relative_square_ceiling (K extent : Nat) (removed background : List Nat)
    (hr : ∀ id, id ∈ removed → id ∈ slabPhysicalFaceEdges extent)
    (hb : ∀ id, id ∈ background → id ∈ slabPhysicalFaceEdges extent) :
    partitionSquare w K extent (removed++background) ≤
      (removalCeiling w removed.length * removalCeiling w removed.length) * partitionSquare w K extent background := by
  let f := removalCeiling w removed.length
  let z := heatProductHaar w (boundaryCompleteSlabLinks extent).length extent background K
  let Z := heatProductHaar w (boundaryCompleteSlabLinks extent).length extent (removed++background) K
  have hz : (0 : Q') ≤ z := (faceProductCertificate hw0 hw1 hsmall hdelta K extent background hb).haar_nonnegative
  have hZ : (0 : Q') ≤ Z := (faceProductCertificate hw0 hw1 hsmall hdelta K extent (removed++background)
    (fun j hj => (List.mem_append.mp hj).elim (hr j) (hb j))).haar_nonnegative
  have hfz := Q'.mul_nonneg _ _ (removalCeiling_nonnegative hw0 removed.length) hz
  have h := relative_ceiling hw0 hw1 hsmall hdelta K extent background hb removed hr
  have hs := Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ h hZ)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ h hfz)
  exact Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
    (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
    (by decide) (fun i => if i=0 then f else z)))

theorem relative_square_ceiling_perm (K extent : Nat) (removed background full : List Nat)
    (hr : ∀ id, id ∈ removed → id ∈ slabPhysicalFaceEdges extent)
    (hb : ∀ id, id ∈ background → id ∈ slabPhysicalFaceEdges extent)
    (hperm : (removed++background).Perm full) :
    partitionSquare w K extent full ≤
      (removalCeiling w removed.length * removalCeiling w removed.length) * partitionSquare w K extent background := by
  have he := haar_of_coeff (blocks := (boundaryCompleteSlabLinks extent).length)
    (polynomialProduct_perm (faceHeatPolynomial w K extent) hperm)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ he) (Q'.mul_eqv_congr_left _ _ _ he)))
    (relative_square_ceiling hw0 hw1 hsmall hdelta K extent removed background hr hb)

/-- A bounded removal count controls the SAME full partition at every cutoff and extent. -/
theorem relative_square_bounded_count (K extent count : Nat) (removed background full : List Nat)
    (hr : ∀ id, id ∈ removed → id ∈ slabPhysicalFaceEdges extent)
    (hb : ∀ id, id ∈ background → id ∈ slabPhysicalFaceEdges extent)
    (hperm : (removed++background).Perm full) (hc : removed.length ≤ count) :
    partitionSquare w K extent full ≤
      (1+heatRemainderBound w)^(count+count) * partitionSquare w K extent background := by
  have hpow := TotalMajorantClose.q_pow_mono
    (Q'.add_le_self_of_nonneg 1 _ (heatRemainderBound_nonnegative hw0)) (Nat.add_le_add hc hc)
  have hs := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.pow_add_eqv (1+heatRemainderBound w) removed.length removed.length)) hpow
  exact Q'.le_trans' _ _ _ (relative_square_ceiling_perm hw0 hw1 hsmall hdelta K extent removed background full hr hb hperm)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hs (SumOfSquares.q_mul_self_nonneg _))

end SmallNome
end YMGap.Continuum.BF4ExactSlabRelativePartitionCeiling

#print axioms YMGap.Continuum.BF4ExactSlabRelativePartitionCeiling.removalCeiling
#print axioms YMGap.Continuum.BF4ExactSlabRelativePartitionCeiling.removalCeiling_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabRelativePartitionCeiling.relative_ceiling
#print axioms YMGap.Continuum.BF4ExactSlabRelativePartitionCeiling.relative_square_ceiling
#print axioms YMGap.Continuum.BF4ExactSlabRelativePartitionCeiling.relative_square_ceiling_perm
#print axioms YMGap.Continuum.BF4ExactSlabRelativePartitionCeiling.relative_square_bounded_count
