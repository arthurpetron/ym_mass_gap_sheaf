/-
# Original partition comparison with cost only for removed faces

The one-face Haar comparison iterates relative to the SAME background
partition: (1-delta)^|removed| Z_background <= Z_full. Squaring retains
the exact spectator partition square. No whole-volume partition floor or
reciprocal ceiling is used. Shared links remain in the original action.
-/

import YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
import YMGap.Continuum.BF4ExactSlabSpectatorResummation

namespace YMGap.Continuum.BF4ExactSlabRelativePartitionBound

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

def removalFloor (w : Q') (count : Nat) : Q' := (1 + -heatRemainderBound w)^count

theorem removalFloor_nonnegative {w : Q'} (hd : heatRemainderBound w ≤ 1) (count : Nat) :
    (0 : Q') ≤ removalFloor w count := Q'.pow_nonneg _ (Q'.sub_nonneg_of_le hd) count

/-- Strict floor at the existing pilot, for every finite removal count. -/
theorem existingNome_removalFloor_pos : ∀ count,
    (0 : Q') < removalFloor BF4ExactSlabPlaquetteSmallNomeCertificate.nome count
  | 0 => by decide
  | n+1 => Q'.mul_pos (by decide) (existingNome_removalFloor_pos n)

section SmallNome

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hdelta : heatRemainderBound w ≤ 1)
include hw0 hw1 hsmall hdelta

theorem relative_floor (K extent : Nat) (background : List Nat)
    (hb : ∀ id, id ∈ background → id ∈ slabPhysicalFaceEdges extent) :
    ∀ removed : List Nat, (∀ id, id ∈ removed → id ∈ slabPhysicalFaceEdges extent) →
      removalFloor w removed.length * heatProductHaar w (boundaryCompleteSlabLinks extent).length extent background K ≤
        heatProductHaar w (boundaryCompleteSlabLinks extent).length extent (removed++background) K
  | [], _ => Q'.le_of_eqv (Q'.one_mul_eqv _)
  | id :: removed, hi => by
      have ht : ∀ j, j ∈ removed → j ∈ slabPhysicalFaceEdges extent := fun j hj => hi j (List.mem_cons_of_mem id hj)
      have hbg : ∀ j, j ∈ removed++background → j ∈ slabPhysicalFaceEdges extent := by
        intro j hj
        rcases List.mem_append.mp hj with hj | hj
        · exact ht j hj
        · exact hb j hj
      have h := insertFace_lower hw0 hw1 hsmall extent id (hi id List.mem_cons_self) K
        (faceProductCertificate hw0 hw1 hsmall hdelta K extent (removed++background) hbg)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _ (relative_floor K extent background hb removed ht) (Q'.sub_nonneg_of_le hdelta))
          (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))))

theorem relative_square_floor (K extent : Nat) (removed background : List Nat)
    (hr : ∀ id, id ∈ removed → id ∈ slabPhysicalFaceEdges extent)
    (hb : ∀ id, id ∈ background → id ∈ slabPhysicalFaceEdges extent) :
    (removalFloor w removed.length * removalFloor w removed.length) * partitionSquare w K extent background ≤
      partitionSquare w K extent (removed++background) := by
  let f := removalFloor w removed.length
  let z := heatProductHaar w (boundaryCompleteSlabLinks extent).length extent background K
  let Z := heatProductHaar w (boundaryCompleteSlabLinks extent).length extent (removed++background) K
  have hz : (0 : Q') ≤ z := (faceProductCertificate hw0 hw1 hsmall hdelta K extent background hb).haar_nonnegative
  have hfz : (0 : Q') ≤ f*z := Q'.mul_nonneg _ _ (removalFloor_nonnegative hdelta _) hz
  have h := relative_floor hw0 hw1 hsmall hdelta K extent background hb removed hr
  have hZ : (0 : Q') ≤ Z := Q'.le_trans' _ _ _ hfz h
  have hs := Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ h hfz)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ h hZ)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (by decide) (fun i => if i = 0 then f else z))) hs

theorem relative_square_floor_perm (K extent : Nat) (removed background full : List Nat)
    (hr : ∀ id, id ∈ removed → id ∈ slabPhysicalFaceEdges extent)
    (hb : ∀ id, id ∈ background → id ∈ slabPhysicalFaceEdges extent)
    (hperm : (removed++background).Perm full) :
    (removalFloor w removed.length * removalFloor w removed.length) * partitionSquare w K extent background ≤
      partitionSquare w K extent full := by
  have he := haar_of_coeff (blocks := (boundaryCompleteSlabLinks extent).length)
    (polynomialProduct_perm (faceHeatPolynomial w K extent) hperm)
  exact Q'.le_trans' _ _ _ (relative_square_floor hw0 hw1 hsmall hdelta K extent removed background hr hb)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ he) (Q'.mul_eqv_congr_left _ _ _ he)))

end SmallNome
end YMGap.Continuum.BF4ExactSlabRelativePartitionBound

#print axioms YMGap.Continuum.BF4ExactSlabRelativePartitionBound.removalFloor
#print axioms YMGap.Continuum.BF4ExactSlabRelativePartitionBound.removalFloor_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabRelativePartitionBound.existingNome_removalFloor_pos
#print axioms YMGap.Continuum.BF4ExactSlabRelativePartitionBound.relative_floor
#print axioms YMGap.Continuum.BF4ExactSlabRelativePartitionBound.relative_square_floor
#print axioms YMGap.Continuum.BF4ExactSlabRelativePartitionBound.relative_square_floor_perm
