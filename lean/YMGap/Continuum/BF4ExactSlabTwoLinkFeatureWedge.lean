/-
# Cancel feature diagonals in the ORIGINAL conditional covariance

Cauchy--Binet rewrites the same signed covariance numerator as a sum over
unordered positions in the shared interaction's feature list. Every pair is
a product of two antisymmetric minors; a feature paired with itself vanishes.
The one-sided action factors and shared-term coefficients remain inside the
actual moments. No absolute values, scalar normalizer floor or exterior
sampling are introduced.

The mixed term in the existing covariance-certificate budget can therefore
be replaced by this canceled expression. A supplied certificate is transported
back to the ORIGINAL budget, whose existing verifier uses the actual inverse
normalizer. No certificate, positivity of individual minors, useful rho,
cutoff-uniform rank, completed strict gap or continuum theorem is produced.
-/

import YMGap.Continuum.RatPolyTwoByTwoCauchyBinet
import YMGap.Continuum.BF4ExactSlabTwoLinkFeatureMoments
import YMGap.Continuum.BF4ExactSlabBlockCovarianceCertificate

namespace YMGap.Continuum.BF4ExactSlabTwoLinkFeatureWedge

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabSharedFaceGeometry
open YMGap.Continuum.BF4ExactSlabTwoLinkFourCopy
open YMGap.Continuum.BF4ExactSlabTwoLinkFeatureMoments
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockCovarianceNormalizer
open YMGap.Continuum.BF4ExactSlabBlockCovarianceCertificate
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionSeparableConditionalMoments
open YMGap.Continuum.RatPolyTwoByTwoCauchyBinet
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

private theorem featureMoment_as_productSum (a b : Nat) (L R f g : RatPoly)
    (K : RatPoly) :
    featureMoment a b L R f g K =
      productSum (leftMoment a b L f) (rightMoment b R g) K := by
  induction K with
  | nil => rfl
  | cons t K ih => simp only [featureMoment, productSum, ih]

variable (w : Q') (K extent : Nat) (left right : Z4Link)

local notation "a" => List.idxOf left (boundaryCompleteSlabLinks extent)
local notation "b" => List.idxOf right (boundaryCompleteSlabLinks extent)
local notation "L" => leftOnlyHeat w K extent left right
local notation "R" => rightOnlyHeat w K extent left right

/-- One pair per unordered pair of shared-feature POSITIONS. The original
coefficient is already in leftMoment; no second coefficient is inserted. -/
def wedgeNumerator (f g : RatPoly) : RatPoly :=
  pairSum (leftMoment a b L polyOne) (leftMoment a b L f)
    (rightMoment b R polyOne) (rightMoment b R g)
    (sharedHeat w K extent left right)

/-- Exact finite-list cancellation, before any positivity or norm estimate. -/
theorem signedFeatureNumerator_wedge_pin (f g : RatPoly) :
    RatPolyCoeffEqv (signedFeatureNumerator w K extent left right f g)
      (wedgeNumerator w K extent left right f g) := by
  unfold signedFeatureNumerator moments wedgeNumerator
  simp only [featureMoment_as_productSum]
  exact determinant_eq_pairSum _ _ _ _ _

variable (hleft : left ∈ boundaryCompleteSlabLinks extent)
  (hright : right ∈ boundaryCompleteSlabLinks extent) (hlinks : left ≠ right)
  (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hK : headCutoff w <= K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "G" => backgroundData hw0 hw1 K extent hK [left, right]
local notation "N" => covarianceVector hw0 hw1 K extent hK [left, right]

include hleft hright hlinks in
/-- The same original covariance vector, with its actual D and mean terms,
not a covariance of a replacement shared-heat-only law. -/
theorem covarianceVector_wedge_pin (p q : (F).V)
    (hp : QuaternionBlockIndependent b p.val) (hq : QuaternionBlockIndependent a q.val) :
    RatPolyCoeffEqv (N p q).val (wedgeNumerator w K extent left right p.val q.val) :=
  (covarianceVector_feature_pin w K extent left right hleft hright hlinks
    hw0 hw1 hK p q hp hq).trans
    (signedFeatureNumerator_wedge_pin w K extent left right p.val q.val)

/-- Only the mixed term is changed. The two original diagonal covariance
vectors stay intact; opposite-block independence is NOT imposed on p,p or q,q. -/
def wedgeBudget (rho : Q') (p q : (F).V) : RatPoly :=
  polyAdd (polySmul rho (polyAdd (N p p).val (N q q).val))
    (polyNeg (polySmul 2 (wedgeNumerator w K extent left right p.val q.val)))

include hleft hright hlinks in
theorem covarianceBudget_wedge_pin (rho : Q') (p q : (F).V)
    (hp : QuaternionBlockIndependent b p.val) (hq : QuaternionBlockIndependent a q.val) :
    RatPolyCoeffEqv (covarianceBudget hw0 hw1 K extent hK [left, right] rho p q).val
      (wedgeBudget w K extent left right hw0 hw1 hK rho p q) := by
  change RatPolyCoeffEqv
    (polyAdd (polySmul rho (polyAdd (N p p).val (N q q).val))
      (polySmul (-1) (polySmul 2 (N p q).val))) _
  exact (RatPolyCoeffEqv.refl _).add
    ((QuaternionHaarAngularCarrier.neg_smul _).symm.trans
      (RatPolyCoeffEqv.neg ((covarianceVector_wedge_pin w K extent left right
        hleft hright hlinks hw0 hw1 hK p q hp hq).smul 2)))

include hleft hright hlinks in
/-- A witness for the canceled polynomial is accepted by the EXISTING
inverse_covariance_bound verifier, with the same rho and actual normalizer.
This transports supplied algebraic data; it does not construct smallness. -/
def certificate_of_wedgeBudget (rho : Q') (p q : (F).V)
    (hp : QuaternionBlockIndependent b p.val) (hq : QuaternionBlockIndependent a q.val)
    (P : Certificate (boundaryCompleteSlabLinks extent).length
      (wedgeBudget w K extent left right hw0 hw1 hK rho p q)) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (covarianceBudget hw0 hw1 K extent hK [left, right] rho p q).val :=
  Certificate.ofCoeff (covarianceBudget_wedge_pin w K extent left right
    hleft hright hlinks hw0 hw1 hK rho p q hp hq) P

/-- Swap tests, NOT the integrated link list or its normalizer. -/
theorem covarianceVector_symm (p q : (F).V) :
    RatPolyCoeffEqv (N p q).val (N q p).val := by
  refine (covarianceVector_pin hw0 hw1 K extent hK [left, right] p q).trans
    (RatPolyCoeffEqv.trans ?_
      (covarianceVector_pin hw0 hw1 K extent hK [left, right] q p).symm)
  exact ((familyProject_congr _ ((RatPolyCoeffEqv.mul_comm _ _).mul_left _)).mul_left _).add
    (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_comm _ _))

/-- The original symmetric budget keeps the SAME ordered union. -/
theorem covarianceBudget_symm (rho : Q') (p q : (F).V) :
    RatPolyCoeffEqv (covarianceBudget hw0 hw1 K extent hK [left, right] rho p q).val
      (covarianceBudget hw0 hw1 K extent hK [left, right] rho q p).val :=
  ((RatPolyCoeffEqv.add_comm _ _).smul rho).add
    (((covarianceVector_symm w K extent left right hw0 hw1 hK p q).smul 2).smul (-1))

include hleft hright hlinks in
/-- Predictions of left/right are independent of left/right respectively,
so use the feature formula on q,p and transport back to p,q. The link list
remains [left,right] throughout; no permutation of integrations is assumed. -/
def certificate_of_reversed_wedgeBudget (rho : Q') (p q : (F).V)
    (hp : QuaternionBlockIndependent a p.val) (hq : QuaternionBlockIndependent b q.val)
    (P : Certificate (boundaryCompleteSlabLinks extent).length
      (wedgeBudget w K extent left right hw0 hw1 hK rho q p)) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (covarianceBudget hw0 hw1 K extent hK [left, right] rho p q).val :=
  Certificate.ofCoeff (covarianceBudget_symm w K extent left right hw0 hw1 hK rho p q)
    (certificate_of_wedgeBudget w K extent left right hleft hright hlinks
      hw0 hw1 hK rho q p hq hp P)

#print axioms wedgeNumerator
#print axioms signedFeatureNumerator_wedge_pin
#print axioms covarianceVector_wedge_pin
#print axioms wedgeBudget
#print axioms covarianceBudget_wedge_pin
#print axioms certificate_of_wedgeBudget
#print axioms covarianceVector_symm
#print axioms covarianceBudget_symm
#print axioms certificate_of_reversed_wedgeBudget

end YMGap.Continuum.BF4ExactSlabTwoLinkFeatureWedge
