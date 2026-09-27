/-
# Original-action conditional variance numerator

The polynomial D*N(p^2)-N(p)^2 uses the actual integrated incident heat D
and the actual inserted numerator N. Its two-copy identity and positive
certificate retain all shared exterior variables. The untouched complementary
action B is itself certified after deleting the unused head, so the SAME
retained-exterior energy is nonnegative without a scalar floor substitution.

This is D^2 times normalized conditional variance before integrating the exterior. It
is NOT the unweighted Haar fluctuation of the incident heat, and it is NOT
by itself the normalized residual energy: that would retain a factor 1/D.
No strict coercivity, weak-coupling rate, spatial limit, OS gap or continuum
claim is made here.
-/

import YMGap.Continuum.SU2QuaternionConditionalVarianceReplica
import YMGap.Continuum.BF4ExactSlabStarFullActionProbe

namespace YMGap.Continuum.BF4ExactSlabStarVarianceReplica

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift (RatPolyTermwiseEqv)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionConditionalVarianceReplica
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) := (boundaryCompleteSlabLinks extent).length

variable (w : Q') (K extent : Nat) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

/-- The head weight is the exact product of the original incident faces. -/
def headWeight : RatPoly :=
  reindexQuaternionPolynomial (linkHeadSwap extent link hl) (incidentHeat w K extent link)

def headInput (p : RatPoly) : RatPoly :=
  reindexQuaternionPolynomial (linkHeadSwap extent link hl) p

/-- The signed subtraction is performed before any tail estimate. -/
def varianceNumerator (p : RatPoly) : RatPoly :=
  polyAdd
    (polyMul (normalizer w K extent link hl)
      (insertedNormalizer w K extent link hl (polyMul p p)))
    (polyNeg (polyMul (insertedNormalizer w K extent link hl p)
      (insertedNormalizer w K extent link hl p)))

private theorem inserted_pin (p : RatPoly) :
    RatPolyCoeffEqv (insertedNormalizer w K extent link hl p)
      (partialHaarHead (polyMul (headWeight w K extent link hl) (headInput extent link hl p))) := by
  unfold insertedNormalizer headWeight headInput
  rw [reindexQuaternionPolynomial_mul]
  exact partialHaarHead_congr (RatPolyCoeffEqv.mul_comm _ _)

theorem varianceNumerator_pin (p : RatPoly) :
    RatPolyCoeffEqv (varianceNumerator w K extent link hl p)
      (determinant (headWeight w K extent link hl) (headInput extent link hl p)) := by
  have hs := inserted_pin w K extent link hl (polyMul p p)
  unfold headInput at hs
  rw [reindexQuaternionPolynomial_mul] at hs
  exact RatPolyCoeffEqv.add (RatPolyCoeffEqv.mul (.refl _) hs)
    (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul (inserted_pin w K extent link hl p)
      (inserted_pin w K extent link hl p)))

include hl in
private theorem count_pin : blocks extent = (blocks extent-1)+1 := by
  have h := List.idxOf_lt_length_of_mem hl
  dsimp only [blocks]
  omega

private theorem headWeight_supported :
    SupportedQuaternionBlocks ((blocks extent-1)+1) (headWeight w K extent link hl) := by
  rw [← count_pin extent link hl]
  exact reindex_supported _ _

private theorem headInput_supported (p : RatPoly) :
    SupportedQuaternionBlocks ((blocks extent-1)+1) (headInput extent link hl p) := by
  rw [← count_pin extent link hl]
  exact reindex_supported _ _

/-- Actual two-copy identity, with no positivity or small-nome hypothesis. -/
theorem varianceNumerator_replica (p : RatPoly) :
    HaarCarrierEqv (blocks extent-1)
      (partialHaarHead (partialHaarHead
        (replicaEnergy (headWeight w K extent link hl) (headInput extent link hl p))))
      (polyAdd (varianceNumerator w K extent link hl p) (varianceNumerator w K extent link hl p)) :=
  (replica_identity (blocks extent-1) _ _ (headWeight_supported w K extent link hl)
    (headInput_supported extent link hl p)).trans
    (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.add
      (varianceNumerator_pin w K extent link hl p).symm
      (varianceNumerator_pin w K extent link hl p).symm))

private theorem partial_independent (p : RatPoly) (hp : HeadQuaternionIndependent p) :
    RatPolyCoeffEqv (partialHaarHead p) (dropHeadPolynomial p) := by
  have ht : RatPolyTermwiseEqv (partialHaarHead p) (dropHeadPolynomial p) := by
    induction p with
    | nil => exact True.intro
    | cons t ts ih =>
        have hz := hp t List.mem_cons_self
        unfold headQuaternionDegree at hz
        have h0 : exponentAt t.1 0 = 0 := by omega
        have h1 : exponentAt t.1 1 = 0 := by omega
        have h2 : exponentAt t.1 2 = 0 := by omega
        have h3 : exponentAt t.1 3 = 0 := by omega
        have hm : headQuaternionMoment t.1 ≈ 1 := by
          unfold headQuaternionMoment
          rw [h0, h1, h2, h3]
          decide +kernel
        exact ⟨rfl, Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hm) (Q'.mul_one_eqv _),
          ih (fun s hs => hp s (List.mem_cons_of_mem t hs))⟩
  exact fun weight => ratWeightedSum_termwise_eqv weight ht

variable {w}
  (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hK : headCutoff w ≤ K)

def headWeight_certificate :
    Certificate ((blocks extent-1)+1) (headWeight w K extent link hl) := by
  rw [← count_pin extent link hl]
  exact reindex_certificate _ (incidentHeat_supported w K extent link)
    (headProduct_certificate hw0 hw1 K extent hK (incidentIds extent link)
      (fun _ hi => incidentIds_physical hi))

/-- All complementary action factors survive as a positive tail certificate. -/
def exterior_certificate : Certificate (blocks extent-1) (exterior w K extent link hl) := by
  let P := reindex_certificate (linkHeadSwap extent link hl)
    (complementHeat_supported w K extent link)
    (headProduct_certificate hw0 hw1 K extent hK (complementIds extent link)
      (fun _ hi => complementIds_physical hi))
  have P' : Certificate ((blocks extent-1)+1)
      (reindexQuaternionPolynomial (linkHeadSwap extent link hl) (complementHeat w K extent link)) := by
    rw [← count_pin extent link hl]
    exact P
  exact .ofCoeff (partial_independent _ (complementHeat_headIndependent w K extent link hl)).symm
    (partialHaarHead_certificate (blocks extent-1) P')

def varianceNumerator_certificate (p : RatPoly) :
    Certificate (blocks extent-1) (varianceNumerator w K extent link hl p) :=
  .ofCoeff (varianceNumerator_pin w K extent link hl p)
    (determinant_certificate (blocks extent-1) _ _
      (headWeight_supported w K extent link hl) (headInput_supported extent link hl p)
      (headWeight_certificate K extent link hl hw0 hw1 hK))

include hw0 hw1 hK in
/-- Retain the literal exterior B, rather than use a product-Haar surrogate. -/
theorem retained_variance_nonnegative (p : RatPoly) :
    (0 : Q') ≤ quaternionHaar (blocks extent-1)
      (polyMul (varianceNumerator w K extent link hl p) (exterior w K extent link hl)) :=
  (Certificate.mul (varianceNumerator_certificate K extent link hl hw0 hw1 hK p)
    (exterior_certificate K extent link hl hw0 hw1 hK)).haar_nonnegative

#print axioms varianceNumerator_pin
#print axioms varianceNumerator_replica
#print axioms headWeight_certificate
#print axioms exterior_certificate
#print axioms varianceNumerator_certificate
#print axioms retained_variance_nonnegative

end YMGap.Continuum.BF4ExactSlabStarVarianceReplica
