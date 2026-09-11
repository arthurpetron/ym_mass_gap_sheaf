/-
# Symmetric-reference perturbations give the completed physical BF4 gap

The finite weighted perturbation theorem already compares the exact physical
BF4 joint law with a symmetric positive reference operator at the additive
rate

  reference.rate + epsilon.

The old direct finite-to-completion wrapper was specialized to `1/16`.  This
module removes that inessential specialization.  An arbitrary finite
mean-zero rate passes through exact stationary centering and constructive GNS
completion.  Consequently, a strict symmetric-reference comparison gives a
gap for the concrete completed physical transfer without an exact RG endpoint
intertwiner, entrywise positivity of the reference matrix, or a reference
probability marginal.

No symmetric reference comparison is constructed here.  The model-specific
SU(2) row-relative estimate remains the analytic producer leaf.  This is a
finite-cutoff theorem and makes no thermodynamic, continuum, or Clay claim.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
import YMGap.Continuum.BF4SymmetricReferenceOperatorComparison

namespace YMGap.Continuum.BF4PhysicalSymmetricReferenceCompletedGap

set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SymmetricReferenceOperatorComparison
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. Arbitrary-rate finite-to-completed contraction -/

/-- The exact finite quadratic input needed at a named rational rate. -/
def CentralPhysicalFiniteQuadraticGapAtRate
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) (rate : Q') : Prop :=
  ∀ observable : EdgeLabelling → Q',
    CentralPhysicalMeanZero w hw K half observable →
      Q'.abs
          (centralPhysicalJointQuadratic w hw K half observable) ≤
        rate *
          centralPhysicalWeightedInner
            w hw K half observable observable

/-- A finite mean-zero bound at `rate` controls every exactly centered Cauchy
stage at that same rate. -/
theorem centralPhysical_cauchyCenteredFormSeq_le_of_finite_gap_at_rate
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (finiteGap :
      CentralPhysicalFiniteQuadraticGapAtRate w hw K half rate)
    (X : CauchyGNS (centralPhysicalSmulGNS w hw K half).toGNSData)
    (stage : Nat) :
    CReal.leEv
      (centralPhysicalCauchyCenteredMarkovFormSeq w hw K half X stage)
      (CReal.mul (CReal.ofQ' rate)
        (centralPhysicalCauchyCenteredNormSeq w hw K half X stage)) := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  let E := (centralPhysicalMarkovFormGNS w hw K half).toGNSData
  let mean := centralPhysicalStationaryMean w hw K half (X.seq stage)
  let normCorrection := D.B (X.seq stage) (X.seq stage) + -(mean * mean)
  let formCorrection := E.B (X.seq stage) (X.seq stage) + -(mean * mean)
  have hfinite : formCorrection ≤ rate * normCorrection :=
    centralPhysical_centeredCorrection_form_le_of_abs_gap
      w hw K half rate finiteGap (X.seq stage)
  refine CReal.leEv_trans
    (CReal.leEv_of_le (CReal.ofQ'_le_ofQ' hfinite)) ?_
  exact CReal.leEv_of_equiv (CRealAlg.ofQ'_mul rate normCorrection)

/-- Representative-level passage of an arbitrary finite rate through the
constructive GNS completion. -/
theorem centralPhysical_cinnerRep_form_gap_of_finite_gap_at_rate
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (finiteGap :
      CentralPhysicalFiniteQuadraticGapAtRate w hw K half rate)
    (X : CauchyGNS (centralPhysicalSmulGNS w hw K half).toGNSData)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal w hw K half
      (Quotient.mk
        (cauchySetoid (centralPhysicalSmulGNS w hw K half).toGNSData) X)) :
    CReal.leEv
      ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerRep
        ((centralPhysicalMarkovSymbol w hw K half).cDiagCauchy X) X)
      (CReal.mul (CReal.ofQ' rate)
        ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerRep X X)) := by
  apply CReal.leEv_of_convergesTo_le
    (centralPhysicalCauchyCenteredMarkovFormSeq_converges_form
      w hw K half X horthogonal)
    (CReal.convergesTo_constMul rate
      (centralPhysicalCauchyCenteredNormSeq_converges_self
        w hw K half X horthogonal))
  exact centralPhysical_cauchyCenteredFormSeq_le_of_finite_gap_at_rate
    hw K half finiteGap X

/-- Any finite physical mean-zero bound passes, at the identical rational
rate, to the whole completed vacuum complement. -/
theorem centralPhysical_completed_vacuum_form_gap_of_finite_gap_at_rate
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (finiteGap :
      CentralPhysicalFiniteQuadraticGapAtRate w hw K half rate)
    (vector : CentralPhysicalGNSCompletion w hw K half)
    (horthogonal :
      CentralPhysicalCompletedVacuumOrthogonal w hw K half vector) :
    CReal.RCle
      ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        (centralPhysicalCompletedMarkovTransfer w hw K half vector) vector)
      (CReal.RCscale rate
        ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
          vector vector)) := by
  revert horthogonal
  refine Quotient.inductionOn vector ?_
  intro X horthogonal
  exact centralPhysical_cinnerRep_form_gap_of_finite_gap_at_rate
    hw K half finiteGap X horthogonal

/-- Bundle a strict finite rate as the existing completed form-gap contract. -/
def centralPhysicalCompletedVacuumFormGapData_of_finiteGapAtRate
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (hrate0 : (0 : Q') ≤ rate) (hrate1 : rate < (1 : Q'))
    (finiteGap :
      CentralPhysicalFiniteQuadraticGapAtRate w hw K half rate) :
    CentralPhysicalCompletedVacuumFormGap w hw K half rate :=
  ⟨hrate0, hrate1,
    centralPhysical_completed_vacuum_form_gap_of_finite_gap_at_rate
      hw K half finiteGap⟩

/-! ## 2. The symmetric-reference perturbative route -/

/-- A symmetric-reference comparison is precisely a finite physical
quadratic gap at its additive rate.  The equality used here identifies the
weighted Markov quadratic with the literal symmetric physical joint form. -/
theorem symmetricReference_finite_quadratic_gap_at_combined_rate
    {w : Q'} {hw : (0 : Q') ≤ w} {K half : Nat}
    (comparison :
      CentralPhysicalSymmetricReferenceComparison w hw K half) :
    CentralPhysicalFiniteQuadraticGapAtRate w hw K half
      (comparison.reference.rate + comparison.epsilon) := by
  intro observable hmean
  have hphysical :=
    CentralPhysicalSymmetricReferenceComparison.physical_markov_quadratic_abs_le
      comparison observable hmean
  exact le_of_eqv_le
    (Q'.eqv_symm
      (Q'.abs_eqv_congr
        (centralPhysicalWeightedMarkovQuadratic_eq_joint
          w hw K half observable)))
    hphysical

/-- A strict symmetric-reference comparison gives the completed form gap for
the concrete physical transfer.  No exact endpoint intertwiner or reference
joint-law normalization is required. -/
def symmetricReference_completed_vacuum_form_gap_data
    {w : Q'} {hw : (0 : Q') ≤ w} {K half : Nat}
    (comparison :
      CentralPhysicalSymmetricReferenceComparison w hw K half)
    (hstrict :
      comparison.reference.rate + comparison.epsilon < (1 : Q')) :
    CentralPhysicalCompletedVacuumFormGap w hw K half
      (comparison.reference.rate + comparison.epsilon) :=
  centralPhysicalCompletedVacuumFormGapData_of_finiteGapAtRate
    hw K half
    (Q'.zero_le_add
      comparison.reference.rate comparison.epsilon
      comparison.reference.rate_nonnegative
      comparison.epsilon_nonnegative)
    hstrict
    (symmetricReference_finite_quadratic_gap_at_combined_rate comparison)

/-- The strict comparison yields the genuine completed operator estimate at
squared rate `(reference.rate + epsilon)^2`. -/
theorem symmetricReference_completed_vacuum_operator_norm_gap
    {w : Q'} {hw : (0 : Q') ≤ w} {K half : Nat}
    (comparison :
      CentralPhysicalSymmetricReferenceComparison w hw K half)
    (hstrict :
      comparison.reference.rate + comparison.epsilon < (1 : Q'))
    (vector : CentralPhysicalGNSCompletion w hw K half)
    (horthogonal :
      CentralPhysicalCompletedVacuumOrthogonal w hw K half vector) :
    let rate := comparison.reference.rate + comparison.epsilon
    let D := (centralPhysicalSmulGNS w hw K half).toGNSData
    let transferred := centralPhysicalCompletedMarkovTransfer w hw K half vector
    CReal.RCle
      (D.cinnerCompl transferred transferred)
      (CReal.RCscale (rate * rate) (D.cinnerCompl vector vector)) := by
  dsimp only
  exact centralPhysicalCompletedMarkovTransfer_norm_gap_of_form_gap
    hw K half
    (symmetricReference_completed_vacuum_form_gap_data comparison hstrict)
    vector horthogonal

/-- Every completed matrix coefficient of a propagated vacuum-orthogonal
vector decays geometrically at the same perturbative rate. -/
theorem symmetricReference_completed_power_matrixCoefficientSq_decay
    {w : Q'} {hw : (0 : Q') ≤ w} {K half : Nat}
    (comparison :
      CentralPhysicalSymmetricReferenceComparison w hw K half)
    (hstrict :
      comparison.reference.rate + comparison.epsilon < (1 : Q'))
    (n : Nat)
    (vector test : CentralPhysicalGNSCompletion w hw K half)
    (horthogonal :
      CentralPhysicalCompletedVacuumOrthogonal w hw K half vector) :
    let rate := comparison.reference.rate + comparison.epsilon
    let D := (centralPhysicalSmulGNS w hw K half).toGNSData
    let propagated :=
      centralPhysicalCompletedMarkovPower w hw K half n vector
    CReal.RCle
      (CReal.RCmul
        (D.cinnerCompl propagated test)
        (D.cinnerCompl propagated test))
      (CReal.RCmul
        (CReal.RCscale ((rate * rate) ^ n)
          (D.cinnerCompl vector vector))
        (D.cinnerCompl test test)) := by
  dsimp only
  exact centralPhysicalCompletedMarkovPower_matrixCoefficientSq_decay_of_form_gap
    hw K half
    (symmetricReference_completed_vacuum_form_gap_data comparison hstrict)
    n vector test horthogonal

/-! ## Axiom audit -/

#print axioms centralPhysical_completed_vacuum_form_gap_of_finite_gap_at_rate
#print axioms symmetricReference_finite_quadratic_gap_at_combined_rate
#print axioms symmetricReference_completed_vacuum_form_gap_data
#print axioms symmetricReference_completed_vacuum_operator_norm_gap
#print axioms symmetricReference_completed_power_matrixCoefficientSq_decay

end YMGap.Continuum.BF4PhysicalSymmetricReferenceCompletedGap
