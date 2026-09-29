/-
# Shared-face determinant and the original two-link normalizer

The four-copy interaction weight is exactly the collar of the two selected
links. Its exterior weight is exactly the original detached action. These
pins are proved by finite face partitions, not cancellation of a polynomial
factor. The signed numerator therefore lives on the actual background used
by the constructed inverse and original conditional projection.
-/

import YMGap.Continuum.BF4ExactSlabTwoLinkFourCopy
import YMGap.Continuum.BF4ExactSlabBlockCovarianceNormalizer

namespace YMGap.Continuum.BF4ExactSlabTwoLinkNormalizerPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabSharedFaceGeometry
open YMGap.Continuum.BF4ExactSlabTwoLinkFourCopy
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockCompletedInverse
open YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
open YMGap.Continuum.BF4ExactSlabBlockCovarianceNormalizer
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

theorem detached_eq_neither (extent : Nat) (left right : Z4Link) :
    detached extent [left, right] = neitherIds extent left right := by
  change (slabPhysicalFaceEdges extent).filter (detachedTest extent [left, right] []) =
    (((slabPhysicalFaceEdges extent).filter (fun id =>
      !(decide (left ∈ edgesOf (slabPlaquetteAt extent id) ∧
        right ∈ edgesOf (slabPlaquetteAt extent id))))).filter (fun id =>
      !(decide (left ∈ edgesOf (slabPlaquetteAt extent id))))).filter (fun id =>
      !(decide (right ∈ edgesOf (slabPlaquetteAt extent id))))
  simp only [List.filter_filter]
  apply List.filter_congr
  intro id _
  simp only [detachedTest, disjointTest, faceLinks, List.flatMap_nil,
    List.flatMap_cons, List.append_nil, List.all_cons, List.all_nil, Bool.and_true]
  by_cases hl : left ∈ edgesOf (slabPlaquetteAt extent id) <;>
    by_cases hr : right ∈ edgesOf (slabPlaquetteAt extent id) <;> simp [hl, hr]

theorem collar_perm (extent : Nat) (left right : Z4Link) :
    (collar extent [left, right]).Perm
      ((sharedIds extent left right ++ leftOnlyIds extent left right) ++
        rightOnlyIds extent left right) := by
  have hp := ((retained_partition extent left right).append_left
    (sharedIds extent left right)).trans (shared_retained_partition extent left right)
  have hc := region_partition extent [left, right] [] (slabPhysicalFaceEdges extent)
  change ((collar extent [left, right]) ++ detached extent [left, right]).Perm _ at hc
  rw [detached_eq_neither] at hc
  apply (List.perm_append_right_iff (neitherIds extent left right)).mp
  simpa only [List.append_assoc] using hc.trans hp.symm

theorem background_pin (w : Q') (K extent : Nat) (left right : Z4Link) :
    background w K extent [left, right] = neitherHeat w K extent left right := by
  unfold background neitherHeat
  rw [detached_eq_neither]

theorem collarHeat_pin (w : Q') (K extent : Nat) (left right : Z4Link) :
    RatPolyCoeffEqv (collarHeat w K extent [left, right])
      (interactionWeight w K extent left right) := by
  have h := (polynomialProduct_perm (faceHeatPolynomial w K extent)
    (collar_perm extent left right)).trans ((polynomialProduct_append _ _ _).trans
      ((polynomialProduct_append _ _ _).mul_right _))
  exact h.trans (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.mul (.var 1) (.var 2)) (.var 0)) (by decide)
    (fun | 0 => sharedHeat w K extent left right
         | 1 => leftOnlyHeat w K extent left right
         | _ => rightOnlyHeat w K extent left right))

theorem normalizer_pin (w : Q') (K extent : Nat) (left right : Z4Link) :
    RatPolyCoeffEqv (normalizer w K extent [left, right])
      (familyProject [(boundaryCompleteSlabLinks extent).idxOf left,
        (boundaryCompleteSlabLinks extent).idxOf right]
        (interactionWeight w K extent left right)) :=
  familyProject_congr _ (collarHeat_pin w K extent left right)

theorem insertedNormalizer_pin (w : Q') (K extent : Nat) (left right : Z4Link)
    (p : RatPoly) :
    RatPolyCoeffEqv (insertedNormalizer w K extent [left, right] p)
      (familyProject [(boundaryCompleteSlabLinks extent).idxOf left,
        (boundaryCompleteSlabLinks extent).idxOf right]
        (polyMul (interactionWeight w K extent left right) p)) :=
  familyProject_congr _ (((collarHeat_pin w K extent left right).mul_left p).trans
    (RatPolyCoeffEqv.mul_comm _ _))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (left right : Z4Link)

local notation "G" => backgroundData hw0 hw1 K extent hK [left, right]
local notation "F" => fullData hw0 hw1 K extent hK
local notation "ids" => slots extent [left, right]
local notation "W" => interactionWeight w K extent left right

theorem covarianceVector_interaction_pin (p q : (F).V) :
    RatPolyCoeffEqv (covarianceVector hw0 hw1 K extent hK [left, right] p q).val
      (covarianceNumerator ids W p.val q.val) := by
  have h := collarHeat_pin w K extent left right
  exact (covarianceVector_pin hw0 hw1 K extent hK [left, right] p q).trans
    (((familyProject_congr _ h).mul (familyProject_congr _ (h.mul_right _))).add
      (RatPolyCoeffEqv.neg ((familyProject_congr _ (h.mul_right _)).mul
        (familyProject_congr _ (h.mul_right _)))))

private theorem supported_neg {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- The literal determinant numerator, not a separately chosen model vector. -/
def interactionCovarianceVector (p q : (F).V) : (G).V :=
  ⟨covarianceNumerator ids W p.val q.val, by
    have hW := supported_polyMul (supported_polyMul
      (heatProduct_supported w K extent (leftOnlyIds extent left right))
      (heatProduct_supported w K extent (rightOnlyIds extent left right)))
      (sharedHeat_supported w K extent left right)
    exact supported_add
      (supported_polyMul (familyProject_supported _ hW)
        (familyProject_supported _ (supported_polyMul hW (supported_polyMul p.property q.property))))
      (supported_neg (supported_polyMul
        (familyProject_supported _ (supported_polyMul hW p.property))
        (familyProject_supported _ (supported_polyMul hW q.property))))⟩

/-- The signed shared-face numerator divided by the actual union normalizer
equals the original union-centered covariance. This is ordinary full-action
L2, not OS, and is not yet a two-projection angle estimate. -/
theorem interaction_covariance_normalizer_pair
    (hleft : left ∈ boundaryCompleteSlabLinks extent)
    (hright : right ∈ boundaryCompleteSlabLinks extent) (p q : (F).V) :
    let hl : ∀ link, link ∈ [left, right] → link ∈ boundaryCompleteSlabLinks extent := by
      intro link hlink
      rcases List.mem_cons.mp hlink with rfl | hlink
      · exact hleft
      · exact (List.mem_singleton.mp hlink) ▸ hright
    let C := conditionalProjection hw0 hw1 K extent hK [left, right] hl;
    (G).cinnerCompl
      (inverseState hw0 hw1 K extent hK [left, right] hl
        (interactionCovarianceVector hw0 hw1 K extent hK left right p q))
      (embedV G (backgroundUnit hw0 hw1 K extent hK [left, right])) =
    CReal.RCsub ((F).cinnerCompl (embedV F p) (embedV F q))
      ((F).cinnerCompl (C (embedV F p)) (C (embedV F q))) := by
  dsimp only
  rw [← inverseState_rad hw0 hw1 K extent hK [left, right] _
    (show (G).rad (covarianceVector hw0 hw1 K extent hK [left, right] p q)
      (interactionCovarianceVector hw0 hw1 K extent hK left right p q) from
      rad_of_veq G (covarianceVector_interaction_pin hw0 hw1 K extent hK left right p q))]
  exact covariance_normalizer_projection hw0 hw1 K extent hK [left, right] _ p q

#print axioms detached_eq_neither
#print axioms collar_perm
#print axioms background_pin
#print axioms collarHeat_pin
#print axioms normalizer_pin
#print axioms insertedNormalizer_pin
#print axioms covarianceVector_interaction_pin
#print axioms interactionCovarianceVector
#print axioms interaction_covariance_normalizer_pair

end YMGap.Continuum.BF4ExactSlabTwoLinkNormalizerPin
