/-
# Completed physical BF4 operator-norm gap

The preceding centered-limit module gives a strict `1/16` form gap for every
completed vacuum-orthogonal vector selected by a physical BF4 producer.  The
positive Markov form also satisfies completed Cauchy--Schwarz.  Combining
those facts constructively gives the square-form estimate and then the actual
squared-norm contraction

  ||T v||^2 <= (1/16)^2 ||v||^2.

The proof uses no spectral theorem and no division by a possibly zero norm.
It remains a finite-cutoff theorem parametrized by the named physical producer;
no thermodynamic or continuum limit is asserted.
-/

import YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap

namespace YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap

/-! ## 1. The reusable completed physical form-gap contract -/

/-- A nonnegative strict form rate on the completed physical vacuum
complement. -/
def CentralPhysicalCompletedVacuumFormGap
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) (rate : Q') : Prop :=
  (0 : Q') ≤ rate ∧ rate < 1 ∧
    ∀ vector : CentralPhysicalGNSCompletion w hw K half,
      CentralPhysicalCompletedVacuumOrthogonal w hw K half vector →
        CReal.RCle
          ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
            (centralPhysicalCompletedMarkovTransfer w hw K half vector) vector)
          (CReal.RCscale rate
            ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
              vector vector))

/-- The centered-limit theorem packages the producer's rate as a completed
physical form-gap contract at each matched scale. -/
def producer_completed_vacuum_form_gap_data
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat) :
    CentralPhysicalCompletedVacuumFormGap
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0
      (Q'.mkPos 1 16 (by decide)) :=
  ⟨by decide, by decide,
    producer_completed_vacuum_form_gap_sixteenth producer scale⟩

/-! ## 2. Constructive square-form and operator-norm contraction -/

/-- Move a rational scale between the two factors of a completed-real
product. -/
private theorem RCmul_scale_right_eq_scale_left
    (scalar : Q') (left right : CReal.RC) :
    CReal.RCmul left (CReal.RCscale scalar right) =
      CReal.RCmul (CReal.RCscale scalar left) right := by
  refine Quotient.inductionOn₂ left right ?_
  intro L R
  exact Quotient.sound
    (YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
      (fun n => by
        change (L.approx n * (scalar * R.approx n)).eqv
          ((scalar * L.approx n) * R.approx n)
        ring_qeqv))

/-- A positive completed physical form gap controls the squared norm by the
same rate times the first Markov form. -/
theorem centralPhysicalCompletedMarkovTransfer_square_form_gap_of_form_gap
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (gap : CentralPhysicalCompletedVacuumFormGap w hw K half rate)
    (vector : CentralPhysicalGNSCompletion w hw K half)
    (horthogonal :
      CentralPhysicalCompletedVacuumOrthogonal w hw K half vector) :
    CReal.RCle
      ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        (centralPhysicalCompletedMarkovTransfer w hw K half vector)
        (centralPhysicalCompletedMarkovTransfer w hw K half vector))
      (CReal.RCscale rate
        ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
          (centralPhysicalCompletedMarkovTransfer w hw K half vector)
          vector)) := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  let Tvector := centralPhysicalCompletedMarkovTransfer w hw K half vector
  let normT := D.cinnerCompl Tvector Tvector
  let form := D.cinnerCompl Tvector vector
  let nextForm := D.cinnerCompl
    (centralPhysicalCompletedMarkovTransfer w hw K half Tvector) Tvector
  have hTorthogonal : CentralPhysicalCompletedVacuumOrthogonal w hw K half
      Tvector :=
    centralPhysicalCompletedVacuumOrthogonal_preserved
      w hw K half horthogonal
  have hcs : CReal.RCle
      (CReal.RCmul normT normT)
      (CReal.RCmul form nextForm) := by
    exact centralPhysicalCompletedMarkovForm_cauchy_schwarz
      w hw K half vector Tvector
  have hnext : CReal.RCle nextForm (CReal.RCscale rate normT) :=
    gap.2.2 Tvector hTorthogonal
  have hformNonnegative : CReal.RCnonneg form :=
    centralPhysicalCompletedMarkovTransfer_positive
      w hw K half vector
  have hproductScaled : CReal.RCle
      (CReal.RCmul form nextForm)
      (CReal.RCmul form (CReal.RCscale rate normT)) :=
    CReal.RCmul_mono_nonnegative_left_local hformNonnegative hnext
  rw [RCmul_scale_right_eq_scale_left] at hproductScaled
  have hnormNonnegative : CReal.RCnonneg normT :=
    D.cinner_self_nonneg Tvector
  have hscaledFormNonnegative :
      CReal.RCnonneg (CReal.RCscale rate form) := by
    have hscaled := CReal.RCscale_mono gap.1 hformNonnegative
    rwa [CReal.RCscale_RCzero] at hscaled
  exact CReal.RCle_of_mul_self_le_mul_right_nonnegative
    hnormNonnegative hscaledFormNonnegative
      (CReal.RCle_trans hcs hproductScaled)

/-- A completed physical form gap of rate `q` upgrades to the genuine
operator estimate `||T v||^2 <= q^2 ||v||^2` on the same complement. -/
theorem centralPhysicalCompletedMarkovTransfer_norm_gap_of_form_gap
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (gap : CentralPhysicalCompletedVacuumFormGap w hw K half rate)
    (vector : CentralPhysicalGNSCompletion w hw K half)
    (horthogonal :
      CentralPhysicalCompletedVacuumOrthogonal w hw K half vector) :
    CReal.RCle
      ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        (centralPhysicalCompletedMarkovTransfer w hw K half vector)
        (centralPhysicalCompletedMarkovTransfer w hw K half vector))
      (CReal.RCscale (rate * rate)
        ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
          vector vector)) := by
  refine CReal.RCle_trans
    (centralPhysicalCompletedMarkovTransfer_square_form_gap_of_form_gap
      hw K half gap vector horthogonal) ?_
  have hform := gap.2.2 vector horthogonal
  have hscaled := CReal.RCscale_mono gap.1 hform
  refine CReal.RCle_trans hscaled ?_
  rw [CReal.RCscale_RCscale]
  exact CReal.RCle_refl _

/-- At every matched scale selected by a physical BF4 producer, the completed
physical macro transfer has operator norm at most `1/16` on the completed
vacuum complement. -/
theorem producer_completed_vacuum_operator_norm_gap_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat)
    (vector : CentralPhysicalGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 vector) :
    CReal.RCle
      ((centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
        (centralPhysicalCompletedMarkovTransfer
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 vector)
        (centralPhysicalCompletedMarkovTransfer
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 vector))
      (CReal.RCscale
        (Q'.mkPos 1 16 (by decide) * Q'.mkPos 1 16 (by decide))
        ((centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
          vector vector)) :=
  centralPhysicalCompletedMarkovTransfer_norm_gap_of_form_gap
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (producer_completed_vacuum_form_gap_data producer scale)
    vector horthogonal

/-! ## 3. Iterated geometric decay on the completed physical complement -/

/-- Powers of the concrete completed physical macro transfer. -/
def centralPhysicalCompletedMarkovPower
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    Nat → CentralPhysicalGNSCompletion w hw K half →
      CentralPhysicalGNSCompletion w hw K half
  | 0, vector => vector
  | n + 1, vector =>
      centralPhysicalCompletedMarkovTransfer w hw K half
        (centralPhysicalCompletedMarkovPower w hw K half n vector)

theorem centralPhysicalCompletedMarkovPower_zero
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (vector : CentralPhysicalGNSCompletion w hw K half) :
    centralPhysicalCompletedMarkovPower w hw K half 0 vector = vector :=
  rfl

theorem centralPhysicalCompletedMarkovPower_succ
    (w : Q') (hw : (0 : Q') ≤ w) (K half n : Nat)
    (vector : CentralPhysicalGNSCompletion w hw K half) :
    centralPhysicalCompletedMarkovPower w hw K half (n + 1) vector =
      centralPhysicalCompletedMarkovTransfer w hw K half
        (centralPhysicalCompletedMarkovPower w hw K half n vector) :=
  rfl

theorem centralPhysicalCompletedMarkovPower_preserves_vacuumOrthogonal
    (w : Q') (hw : (0 : Q') ≤ w) (K half n : Nat)
    (vector : CentralPhysicalGNSCompletion w hw K half)
    (horthogonal :
      CentralPhysicalCompletedVacuumOrthogonal w hw K half vector) :
    CentralPhysicalCompletedVacuumOrthogonal w hw K half
      (centralPhysicalCompletedMarkovPower w hw K half n vector) := by
  induction n with
  | zero => exact horthogonal
  | succ k ih =>
      exact centralPhysicalCompletedVacuumOrthogonal_preserved
        w hw K half ih

/-- The completed physical operator-norm estimate iterates geometrically. -/
theorem centralPhysicalCompletedMarkovPower_norm_gap_of_form_gap
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (gap : CentralPhysicalCompletedVacuumFormGap w hw K half rate)
    (n : Nat)
    (vector : CentralPhysicalGNSCompletion w hw K half)
    (horthogonal :
      CentralPhysicalCompletedVacuumOrthogonal w hw K half vector) :
    CReal.RCle
      ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        (centralPhysicalCompletedMarkovPower w hw K half n vector)
        (centralPhysicalCompletedMarkovPower w hw K half n vector))
      (CReal.RCscale ((rate * rate) ^ n)
        ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
          vector vector)) := by
  induction n with
  | zero =>
      rw [centralPhysicalCompletedMarkovPower_zero,
        Q'.pow_zero, CReal.RCscale_one]
      exact CReal.RCle_refl _
  | succ k ih =>
      rw [centralPhysicalCompletedMarkovPower_succ]
      have hpowerOrthogonal :=
        centralPhysicalCompletedMarkovPower_preserves_vacuumOrthogonal
          w hw K half k vector horthogonal
      have hstep :=
        centralPhysicalCompletedMarkovTransfer_norm_gap_of_form_gap
          hw K half gap
            (centralPhysicalCompletedMarkovPower w hw K half k vector)
            hpowerOrthogonal
      refine CReal.RCle_trans hstep ?_
      have hrateSqNonnegative : (0 : Q') ≤ rate * rate :=
        Q'.mul_nonneg rate rate gap.1 gap.1
      have hscaled := CReal.RCscale_mono hrateSqNonnegative ih
      refine CReal.RCle_trans hscaled ?_
      rw [CReal.RCscale_RCscale]
      exact CReal.RCle_refl _

/-- Every squared matrix coefficient of a propagated vacuum-orthogonal
vector inherits the completed geometric norm decay.  The test vector is an
arbitrary element of the same completed physical carrier. -/
theorem centralPhysicalCompletedMarkovPower_matrixCoefficientSq_decay_of_form_gap
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (gap : CentralPhysicalCompletedVacuumFormGap w hw K half rate)
    (n : Nat)
    (vector test : CentralPhysicalGNSCompletion w hw K half)
    (horthogonal :
      CentralPhysicalCompletedVacuumOrthogonal w hw K half vector) :
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
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  let propagated :=
    centralPhysicalCompletedMarkovPower w hw K half n vector
  have hcs := D.RC_cauchy_schwarz propagated test
  have hnorm := centralPhysicalCompletedMarkovPower_norm_gap_of_form_gap
    hw K half gap n vector horthogonal
  change CReal.RCle
    (D.cinnerCompl propagated propagated)
    (CReal.RCscale ((rate * rate) ^ n)
      (D.cinnerCompl vector vector)) at hnorm
  have htestNonnegative := D.cinner_self_nonneg test
  have hmul := CReal.RCmul_mono_nonnegative_left_local
    htestNonnegative hnorm
  rw [CReal.RCmul_comm (D.cinnerCompl test test),
      CReal.RCmul_comm (D.cinnerCompl test test)] at hmul
  exact CReal.RCle_trans hcs hmul

/-- Powers of the producer-selected physical BF4 macro transfer decay with
squared-norm rate `((1/16)^2)^n` on the completed vacuum complement. -/
theorem producer_completed_power_norm_decay_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale n : Nat)
    (vector : CentralPhysicalGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 vector) :
    CReal.RCle
      ((centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
        (centralPhysicalCompletedMarkovPower
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 n vector)
        (centralPhysicalCompletedMarkovPower
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 n vector))
      (CReal.RCscale
        ((Q'.mkPos 1 16 (by decide) * Q'.mkPos 1 16 (by decide)) ^ n)
        ((centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
          vector vector)) :=
  centralPhysicalCompletedMarkovPower_norm_gap_of_form_gap
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (producer_completed_vacuum_form_gap_data producer scale)
    n vector horthogonal

end YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap

#print axioms YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap.producer_completed_vacuum_form_gap_data
#print axioms YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap.centralPhysicalCompletedMarkovTransfer_square_form_gap_of_form_gap
#print axioms YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap.centralPhysicalCompletedMarkovTransfer_norm_gap_of_form_gap
#print axioms YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap.producer_completed_vacuum_operator_norm_gap_sixteenth
#print axioms YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap.centralPhysicalCompletedMarkovPower_norm_gap_of_form_gap
#print axioms YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap.centralPhysicalCompletedMarkovPower_matrixCoefficientSq_decay_of_form_gap
#print axioms YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap.producer_completed_power_norm_decay_sixteenth
