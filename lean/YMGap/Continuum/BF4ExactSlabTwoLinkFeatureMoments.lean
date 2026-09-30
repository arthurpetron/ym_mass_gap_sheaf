/-
# Exact shared-interaction features for the original two-link law

The feature index is only the term list of sharedHeat. Both one-sided action
factors stay inside their Haar moments, the detached weight stays outside
once, and D is still the actual original union normalizer. The same feature
list computes D, N_f, N_g and N_fg for all opposite-block-independent tests.

The resulting signed determinant is pinned to covarianceVector, the input
of the existing completed inverse-normalizer identity. No positive or small
matrix bound, exterior discretization, uniform cutoff rank or OS gap follows
from this algebraic reduction.
-/

import YMGap.Continuum.BF4ExactSlabTwoLinkNormalizerPin
import YMGap.Continuum.SU2QuaternionSeparableConditionalMoments

namespace YMGap.Continuum.BF4ExactSlabTwoLinkFeatureMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabSharedFaceGeometry
open YMGap.Continuum.BF4ExactSlabTwoLinkFourCopy
open YMGap.Continuum.BF4ExactSlabTwoLinkNormalizerPin
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockCovarianceNormalizer
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica
open YMGap.Continuum.SU2QuaternionSeparableConditionalMoments
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable (w : Q') (K extent : Nat) (left right : Z4Link)

local notation "a" => List.idxOf left (boundaryCompleteSlabLinks extent)
local notation "b" => List.idxOf right (boundaryCompleteSlabLinks extent)
local notation "W" => interactionWeight w K extent left right

/-- Each summand retains the full one-sided action and test. -/
def moments (f g : RatPoly) : RatPoly :=
  featureMoment a b (leftOnlyHeat w K extent left right)
    (rightOnlyHeat w K extent left right) f g (sharedHeat w K extent left right)

variable (hleft : left ∈ boundaryCompleteSlabLinks extent)
  (hright : right ∈ boundaryCompleteSlabLinks extent) (hlinks : left ≠ right)

include hleft hright hlinks

theorem moment_pin (f g : RatPoly)
    (hf : QuaternionBlockIndependent b f) (hg : QuaternionBlockIndependent a g) :
    RatPolyCoeffEqv (familyProject [a, b] (polyMul W (polyMul f g)))
      (moments w K extent left right f g) :=
  weighted_moment a b (fun he => hlinks (idxOf_injective_on_members hleft hright he))
    _ _ f g (leftOnly_independent_right w K extent left right hright)
    (rightOnly_independent_left w K extent left right hleft) hf hg _

theorem inserted_product_feature_pin (f g : RatPoly)
    (hf : QuaternionBlockIndependent b f) (hg : QuaternionBlockIndependent a g) :
    RatPolyCoeffEqv (insertedNormalizer w K extent [left, right] (polyMul f g))
      (moments w K extent left right f g) :=
  (insertedNormalizer_pin w K extent left right (polyMul f g)).trans
    (moment_pin w K extent left right hleft hright hlinks f g hf hg)

theorem normalizer_feature_pin :
    RatPolyCoeffEqv (normalizer w K extent [left, right])
      (moments w K extent left right polyOne polyOne) := by
  have hone : RatPolyCoeffEqv (polyMul W (polyMul polyOne polyOne)) W :=
    ((RatPolyCoeffEqv.mul_one polyOne).mul_left W).trans (RatPolyCoeffEqv.mul_one W)
  exact (normalizer_pin w K extent left right).trans
    ((familyProject_congr [a, b] hone).symm.trans
      (moment_pin w K extent left right hleft hright hlinks polyOne polyOne
        (quaternionBlockIndependent_polyOne b) (quaternionBlockIndependent_polyOne a)))

theorem inserted_left_feature_pin (f : RatPoly) (hf : QuaternionBlockIndependent b f) :
    RatPolyCoeffEqv (insertedNormalizer w K extent [left, right] f)
      (moments w K extent left right f polyOne) :=
  (insertedNormalizer_pin w K extent left right f).trans
    ((familyProject_congr [a, b] ((RatPolyCoeffEqv.mul_one f).mul_left W)).symm.trans
      (moment_pin w K extent left right hleft hright hlinks f polyOne hf
        (quaternionBlockIndependent_polyOne a)))

theorem inserted_right_feature_pin (g : RatPoly) (hg : QuaternionBlockIndependent a g) :
    RatPolyCoeffEqv (insertedNormalizer w K extent [left, right] g)
      (moments w K extent left right polyOne g) :=
  (insertedNormalizer_pin w K extent left right g).trans
    ((familyProject_congr [a, b] ((RatPolyCoeffEqv.one_mul g).mul_left W)).symm.trans
      (moment_pin w K extent left right hleft hright hlinks polyOne g
        (quaternionBlockIndependent_polyOne b) hg))

/-- The full marginal retains the actual detached weight exactly once. -/
theorem full_marginal_feature_pin (f g : RatPoly)
    (hf : QuaternionBlockIndependent b f) (hg : QuaternionBlockIndependent a g) :
    RatPolyCoeffEqv
      (familyProject (slots extent [left, right])
        (polyMul (polyMul f g) (fullWeight w K extent)))
      (polyMul (neitherHeat w K extent left right) (moments w K extent left right f g)) := by
  have hl : ∀ link, link ∈ [left, right] → link ∈ boundaryCompleteSlabLinks extent := by
    intro link hlink
    rcases List.mem_cons.mp hlink with rfl | hlink
    · exact hleft
    · exact (List.mem_singleton.mp hlink) ▸ hright
  have hp := full_inserted_marginal_pin w K extent [left, right] hl (polyMul f g)
  rw [background_pin] at hp
  exact hp.trans ((inserted_product_feature_pin w K extent left right
    hleft hright hlinks f g hf hg).mul_left _)

omit hleft hright hlinks in
/-- All four moment sums use the same sharedHeat term list. -/
def signedFeatureNumerator (f g : RatPoly) : RatPoly :=
  polyAdd
    (polyMul (moments w K extent left right polyOne polyOne)
      (moments w K extent left right f g))
    (polyNeg (polyMul (moments w K extent left right f polyOne)
      (moments w K extent left right polyOne g)))

/-- Pin directly to the existing input of the constructed completed inverse.
This preserves the signed subtraction; it is not an estimate of either term. -/
theorem covarianceVector_feature_pin
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hK : headCutoff w ≤ K)
    (p q : (fullData hw0 hw1 K extent hK).V)
    (hp : QuaternionBlockIndependent b p.val) (hq : QuaternionBlockIndependent a q.val) :
    RatPolyCoeffEqv
      (covarianceVector hw0 hw1 K extent hK [left, right] p q).val
      (signedFeatureNumerator w K extent left right p.val q.val) := by
  have hD := (normalizer_pin w K extent left right).symm.trans
    (normalizer_feature_pin w K extent left right hleft hright hlinks)
  have hfg := moment_pin w K extent left right hleft hright hlinks p.val q.val hp hq
  have hf := (insertedNormalizer_pin w K extent left right p.val).symm.trans
    (inserted_left_feature_pin w K extent left right hleft hright hlinks p.val hp)
  have hg := (insertedNormalizer_pin w K extent left right q.val).symm.trans
    (inserted_right_feature_pin w K extent left right hleft hright hlinks q.val hq)
  exact (covarianceVector_interaction_pin hw0 hw1 K extent hK left right p q).trans
    ((hD.mul hfg).add (RatPolyCoeffEqv.neg (hf.mul hg)))

#print axioms moment_pin
#print axioms inserted_product_feature_pin
#print axioms normalizer_feature_pin
#print axioms inserted_left_feature_pin
#print axioms inserted_right_feature_pin
#print axioms full_marginal_feature_pin
#print axioms covarianceVector_feature_pin

end YMGap.Continuum.BF4ExactSlabTwoLinkFeatureMoments
