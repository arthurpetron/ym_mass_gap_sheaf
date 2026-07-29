/-
# Symmetric endpoint operators versus entrywise-positive BF4 joint laws

A Peter--Weyl matrix of a positive Gaussian/Mehler integral operator is
naturally a symmetric positive-semidefinite matrix.  It is not, merely from
those facts, an entrywise-nonnegative joint probability table: Fourier matrix
coefficients may have either sign, and their row sums are not probability
marginals.

This module records that distinction in the types.

* `CentralSymmetricReferenceOperator` is the common-carrier object naturally
  produced by a Peter--Weyl transform.  It asks for symmetry, positivity of
  every finite quadratic form, and the physical-mean-zero Rayleigh estimate.
  It does NOT ask for entrywise positivity or a row marginal.
* `CentralPhysicalSymmetricReferenceComparison` adds exactly the
  Yang--Mills row-relative estimate needed by the weighted perturbation
  theorem.
* `CentralPhysicalJointLawCertificate` is separate optional data asserting
  entrywise positivity and exact physical marginal matching.  Only with this
  additional certificate can the reference be repackaged as the older
  `CentralPhysicalMehlerComparison` joint-law interface.

The main consumer proves that the symmetric-operator interface already
suffices for the physical weighted quarter bound.  Thus the genuine
Peter--Weyl endpoint construction need not prove the generally false
implication "PSD matrix => entrywise-positive joint law".

Honest scope: no endpoint matrix and no AF-uniform row estimate is
constructed here.  This is the constructive common-carrier interface and its
completed perturbative consumer.

## Axiom gate

Finite `Q'` sums and exact rational order only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4CentralPositivePeterWeylEndpoint
import YMGap.Continuum.BF4WeightedJointPerronPerturbation

namespace YMGap.Continuum.BF4SymmetricReferenceOperatorComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralPositivePeterWeylEndpoint
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

/-- Cancellation-free rational polynomial normalization. -/
local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. The common-carrier symmetric reference operator -/

/-- A symmetric positive-semidefinite reference matrix on the exact
positive-row BF4 carrier, with a located physical-mean-zero Rayleigh rate.

This is the natural target of a real Peter--Weyl matrix-coefficient
calculation.  Neither entrywise nonnegativity nor a probability marginal is
part of the structure. -/
structure CentralSymmetricReferenceOperator
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) : Type where
  /-- Matrix coefficients on the retained physical row labels. -/
  matrix : EdgeLabelling → EdgeLabelling → Q'
  /-- Self-adjointness on the finite retained carrier. -/
  symmetric :
    ∀ left right,
      left ∈ centralPositiveHalfStates w hw K halfExtent →
      right ∈ centralPositiveHalfStates w hw K halfExtent →
        matrix left right ≈ matrix right left
  /-- Positive-semidefiniteness as a quadratic-form statement. -/
  quadratic_nonnegative :
    ∀ observable : EdgeLabelling → Q',
      (0 : Q') ≤
        finiteJointQuadratic
          (centralPositiveHalfStates w hw K halfExtent)
          observable matrix
  /-- Located rational upper bound for the reference mean-zero quadratic. -/
  rate : Q'
  rate_nonnegative : (0 : Q') ≤ rate
  /-- Reference contraction on the exact PHYSICAL mean-zero carrier. -/
  meanZero_quadratic :
    ∀ observable,
      CentralPhysicalMeanZero w hw K halfExtent observable →
        Q'.abs
            (finiteJointQuadratic
              (centralPositiveHalfStates w hw K halfExtent)
              observable matrix) ≤
          rate *
            centralPhysicalWeightedInner
              w hw K halfExtent observable observable

/-- The analytic certificate which upgrades a GENUINE projected
five-holonomy endpoint to the symmetric reference-operator interface.

The endpoint projection itself already pins the matrix entries to the
double-Haar Peter--Weyl transform and to the exact BF4 tangent precision.
The additional fields here are precisely operator positivity and the
located mean-zero rate. -/
structure CentralPositiveGaussianEndpointSpectralCertificate
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {pw :
      CentralPositiveBoundaryPeterWeylTransform
        w hw K halfExtent}
    (endpoint :
      CentralPositiveGaussianEndpointProjection
        w hw K halfExtent pw) : Type where
  quadratic_nonnegative :
    ∀ observable : EdgeLabelling → Q',
      (0 : Q') ≤
        finiteJointQuadratic
          (centralPositiveHalfStates w hw K halfExtent)
          observable endpoint.projectedJoint
  rate : Q'
  rate_nonnegative : (0 : Q') ≤ rate
  meanZero_quadratic :
    ∀ observable,
      CentralPhysicalMeanZero w hw K halfExtent observable →
        Q'.abs
            (finiteJointQuadratic
              (centralPositiveHalfStates w hw K halfExtent)
              observable endpoint.projectedJoint) ≤
          rate *
            centralPhysicalWeightedInner
              w hw K halfExtent observable observable

namespace CentralPositiveGaussianEndpointSpectralCertificate

/-- A genuine double-Haar endpoint projection with its spectral certificate
is a symmetric PSD common-carrier reference operator. -/
def toSymmetricReferenceOperator
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {pw :
      CentralPositiveBoundaryPeterWeylTransform
        w hw K halfExtent}
    {endpoint :
      CentralPositiveGaussianEndpointProjection
        w hw K halfExtent pw}
    (certificate :
      CentralPositiveGaussianEndpointSpectralCertificate endpoint) :
    CentralSymmetricReferenceOperator
      w hw K halfExtent where
  matrix := endpoint.projectedJoint
  symmetric := endpoint.projectedJoint_symmetric
  quadratic_nonnegative := certificate.quadratic_nonnegative
  rate := certificate.rate
  rate_nonnegative := certificate.rate_nonnegative
  meanZero_quadratic := certificate.meanZero_quadratic

end CentralPositiveGaussianEndpointSpectralCertificate

/-- The genuine nonlinear-versus-reference comparison.  The error is
relative to the physical row marginal, so no inverse small marginal or
uniform carrier measure is introduced. -/
structure CentralPhysicalSymmetricReferenceComparison
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) : Type where
  reference :
    CentralSymmetricReferenceOperator w hw K halfExtent
  epsilon : Q'
  epsilon_nonnegative : (0 : Q') ≤ epsilon
  row_relative_error :
    ∀ source,
      source ∈ centralPositiveHalfStates w hw K halfExtent →
        finiteJointDifferenceAbsRowMass
            (centralPositiveHalfStates w hw K halfExtent)
            (centralNormalizedPhysicalReflectedKernel
              w hw K halfExtent)
            reference.matrix
            source ≤
          epsilon *
            centralPhysicalRowMarginal
              w hw K halfExtent source

/-! ## 2. Optional entrywise joint-law data -/

/-- Extra facts needed to regard a symmetric PSD reference operator as an
entrywise-positive joint law with the exact physical marginal.

These fields are deliberately separate: neither follows from symmetry and
positive-semidefiniteness of the operator matrix. -/
structure CentralPhysicalJointLawCertificate
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (reference :
      CentralSymmetricReferenceOperator
        w hw K halfExtent) : Type where
  entry_nonnegative :
    ∀ left, left ∈ centralPositiveHalfStates w hw K halfExtent →
      ∀ right, right ∈ centralPositiveHalfStates w hw K halfExtent →
        (0 : Q') ≤ reference.matrix left right
  physical_rowMarginal :
    ∀ source,
      source ∈ centralPositiveHalfStates w hw K halfExtent →
        listQSum
            (reference.matrix source)
            (centralPositiveHalfStates w hw K halfExtent) ≈
          centralPhysicalRowMarginal
            w hw K halfExtent source

namespace CentralPhysicalSymmetricReferenceComparison

/-- With a separate entrywise/marginal certificate, the corrected
symmetric-operator comparison recovers the older joint-law interface. -/
def toPhysicalMehlerComparison
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (comparison :
      CentralPhysicalSymmetricReferenceComparison
        w hw K halfExtent)
    (jointLaw :
      CentralPhysicalJointLawCertificate
        comparison.reference) :
    CentralPhysicalMehlerComparison
      w hw K halfExtent where
  mehlerJoint := comparison.reference.matrix
  mehlerJoint_nonnegative := jointLaw.entry_nonnegative
  mehlerJoint_symmetric := comparison.reference.symmetric
  mehlerJoint_rowMarginal := jointLaw.physical_rowMarginal
  rate := comparison.reference.rate
  rate_nonnegative := comparison.reference.rate_nonnegative
  epsilon := comparison.epsilon
  epsilon_nonnegative := comparison.epsilon_nonnegative
  row_relative_error := comparison.row_relative_error
  mehler_meanZero_quadratic :=
    comparison.reference.meanZero_quadratic

/-! ## 3. Direct weighted consumer — no joint-law upgrade required -/

/-- The physical joint quadratic is close to a symmetric reference
quadratic.  Entrywise positivity and reference marginal normalization are
not used. -/
theorem physical_joint_close
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (comparison :
      CentralPhysicalSymmetricReferenceComparison
        w hw K halfExtent)
    (observable : EdgeLabelling → Q') :
    Q'.abs
        (centralPhysicalJointQuadratic
            w hw K halfExtent observable +
          (-finiteJointQuadratic
            (centralPositiveHalfStates w hw K halfExtent)
            observable comparison.reference.matrix)) ≤
      comparison.epsilon *
        centralPhysicalWeightedInner
          w hw K halfExtent observable observable := by
  refine Q'.le_trans' _ _ _
    (finiteJointQuadratic_abs_sub_le_weightedSquare
      (centralPositiveHalfStates w hw K halfExtent)
      observable
      (centralPhysicalRowMarginal w hw K halfExtent)
      (centralNormalizedPhysicalReflectedKernel
        w hw K halfExtent)
      comparison.reference.matrix
      comparison.epsilon
      (fun left right hleft hright =>
        centralNormalizedPhysicalReflectedKernel_symm
          ((mem_centralPositiveHalfStates_iff).1 hleft).1
          ((mem_centralPositiveHalfStates_iff).1 hright).1)
      comparison.reference.symmetric
      comparison.row_relative_error) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.le_of_eqv
      (finiteWeightedSquare_physical_eqv_inner
        w hw K halfExtent observable))
    comparison.epsilon_nonnegative

/-- A symmetric PSD endpoint comparison transfers its Rayleigh bound to the
exact physical BF4 Markov quadratic, with additive loss
`reference.rate + epsilon`. -/
theorem physical_markov_quadratic_abs_le
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (comparison :
      CentralPhysicalSymmetricReferenceComparison
        w hw K halfExtent)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        w hw K halfExtent observable) :
    Q'.abs
        (centralPhysicalWeightedInner w hw K halfExtent
          observable
          (centralPhysicalMarkovApply
            w hw K halfExtent observable)) ≤
      (comparison.reference.rate + comparison.epsilon) *
        centralPhysicalWeightedInner
          w hw K halfExtent observable observable := by
  let physicalQuadratic :=
    centralPhysicalJointQuadratic
      w hw K halfExtent observable
  let referenceQuadratic :=
    finiteJointQuadratic
      (centralPositiveHalfStates w hw K halfExtent)
      observable comparison.reference.matrix
  have hphysical :
      centralPhysicalWeightedInner w hw K halfExtent
          observable
          (centralPhysicalMarkovApply
            w hw K halfExtent observable) ≈
        physicalQuadratic :=
    centralPhysicalWeightedMarkovQuadratic_eq_joint
      w hw K halfExtent observable
  have hsplit :
      physicalQuadratic ≈
        (physicalQuadratic + (-referenceQuadratic)) +
          referenceQuadratic := by
    exact Q'.eqv_symm
      (Q'.eqv_trans _
        (physicalQuadratic +
          ((-referenceQuadratic) + referenceQuadratic)) _
        (Q'.add_assoc_eqv
          physicalQuadratic (-referenceQuadratic) referenceQuadratic)
        (Q'.eqv_trans _
          (physicalQuadratic + 0) _
          (Q'.add_eqv_congr_left physicalQuadratic _ _
            (Q'.neg_add_self_eqv referenceQuadratic))
          (Q'.eqv_of_eq
            (Q'.add_zero' physicalQuadratic))))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hphysical)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hsplit)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.abs_add_le'
      (physicalQuadratic + (-referenceQuadratic))
      referenceQuadratic) ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add
      (physical_joint_close comparison observable)
      (comparison.reference.meanZero_quadratic
        observable hmean)) ?_
  exact Q'.le_of_eqv (by q_ring)

/-- Quarter-bound consumer for the corrected symmetric reference interface.
No entrywise-positive reference joint law or exact reference marginal is
needed. -/
theorem physical_markov_quadratic_abs_le_quarter
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (comparison :
      CentralPhysicalSymmetricReferenceComparison
        w hw K halfExtent)
    (hquarter :
      comparison.reference.rate + comparison.epsilon ≤
        Q'.mkPos 1 4 (by decide))
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        w hw K halfExtent observable) :
    Q'.abs
        (centralPhysicalWeightedInner w hw K halfExtent
          observable
          (centralPhysicalMarkovApply
            w hw K halfExtent observable)) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          w hw K halfExtent observable observable := by
  exact Q'.le_trans' _ _ _
    (physical_markov_quadratic_abs_le
      comparison observable hmean)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      hquarter
      (centralPhysicalWeightedSquare_nonnegative
        w hw K halfExtent observable))

end CentralPhysicalSymmetricReferenceComparison

end YMGap.Continuum.BF4SymmetricReferenceOperatorComparison

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4SymmetricReferenceOperatorComparison.CentralPhysicalSymmetricReferenceComparison.toPhysicalMehlerComparison
#print axioms YMGap.Continuum.BF4SymmetricReferenceOperatorComparison.CentralPositiveGaussianEndpointSpectralCertificate.toSymmetricReferenceOperator
#print axioms YMGap.Continuum.BF4SymmetricReferenceOperatorComparison.CentralPhysicalSymmetricReferenceComparison.physical_joint_close
#print axioms YMGap.Continuum.BF4SymmetricReferenceOperatorComparison.CentralPhysicalSymmetricReferenceComparison.physical_markov_quadratic_abs_le
#print axioms YMGap.Continuum.BF4SymmetricReferenceOperatorComparison.CentralPhysicalSymmetricReferenceComparison.physical_markov_quadratic_abs_le_quarter
