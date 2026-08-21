/-
# The direct physical BF4 gap on the Type-modulated completion

The physical macro transfer and full inner product on the Type-modulated GNS
completion map exactly to their legacy counterparts.  The direct completed
physical form and operator gaps therefore transport back to the modulated
carrier without choosing a modulus from a Prop-level null proof.

This remains a finite-cutoff theorem parametrized by the named physical BF4
producer.  It supplies no thermodynamic or continuum limit.
-/

import YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
import YMGap.Continuum.BF4PhysicalMarkovModulusCompletion

namespace YMGap.Continuum.BF4PhysicalModulatedOperatorNormGap

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalMarkovModulusCompletion
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. Vacuum complement and one-step gap transport -/

/-- Modulated vacuum orthogonality is exactly legacy vacuum orthogonality
after forgetting the explicit null modulus. -/
theorem centralPhysicalModulatedVacuumOrthogonal_toLegacy
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (vector : CentralPhysicalModulatedGNSCompletion w hw K half)
    (horthogonal :
      CentralPhysicalModulatedVacuumOrthogonal w hw K half vector) :
    CentralPhysicalCompletedVacuumOrthogonal w hw K half
      (toLegacyCompletion
        (centralPhysicalSmulGNS w hw K half).toGNSData vector) := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  unfold CentralPhysicalModulatedVacuumOrthogonal at horthogonal
  unfold CentralPhysicalCompletedVacuumOrthogonal
  change D.cinnerCompl (toLegacyCompletion D vector)
      (toLegacyCompletion D
        (centralPhysicalModulatedVacuum w hw K half)) = CReal.RCzero
  rw [centralPhysicalModulatedInner_toLegacy]
  exact horthogonal

/-- The producer's completed `1/16` form gap holds directly on the
Type-modulated physical vacuum complement. -/
theorem producer_modulated_vacuum_form_gap_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat)
    (vector : CentralPhysicalModulatedGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)
    (horthogonal : CentralPhysicalModulatedVacuumOrthogonal
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 vector) :
    CReal.RCle
      (modulatedCinnerCompl
        (centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData
        (centralPhysicalModulatedMarkovTransfer
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 vector)
        vector)
      (CReal.RCscale (Q'.mkPos 1 16 (by decide))
        (modulatedCinnerCompl
          (centralPhysicalSmulGNS
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0).toGNSData
          vector vector)) := by
  let w := matchedAllSpinWeight family coupling scale
  let hw := matchedAllSpinWeight_nonnegative family coupling scale
  let K := matchedAllSpinCutoff family coupling scale
  let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
  have hlegacy := producer_completed_vacuum_form_gap_sixteenth
    producer scale (toLegacyCompletion D vector)
      (centralPhysicalModulatedVacuumOrthogonal_toLegacy
        w hw K 0 vector horthogonal)
  rw [← centralPhysicalModulatedMarkovTransfer_toLegacy] at hlegacy
  rw [centralPhysicalModulatedInner_toLegacy] at hlegacy
  rw [centralPhysicalModulatedInner_toLegacy] at hlegacy
  exact hlegacy

/-- The Type-modulated physical macro transfer has the same operator norm
bound `1/16` on its completed vacuum complement. -/
theorem producer_modulated_vacuum_operator_norm_gap_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat)
    (vector : CentralPhysicalModulatedGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)
    (horthogonal : CentralPhysicalModulatedVacuumOrthogonal
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 vector) :
    CReal.RCle
      (modulatedCinnerCompl
        (centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData
        (centralPhysicalModulatedMarkovTransfer
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 vector)
        (centralPhysicalModulatedMarkovTransfer
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 vector))
      (CReal.RCscale
        (Q'.mkPos 1 16 (by decide) * Q'.mkPos 1 16 (by decide))
        (modulatedCinnerCompl
          (centralPhysicalSmulGNS
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0).toGNSData
          vector vector)) := by
  let w := matchedAllSpinWeight family coupling scale
  let hw := matchedAllSpinWeight_nonnegative family coupling scale
  let K := matchedAllSpinCutoff family coupling scale
  let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
  have hlegacy := producer_completed_vacuum_operator_norm_gap_sixteenth
    producer scale (toLegacyCompletion D vector)
      (centralPhysicalModulatedVacuumOrthogonal_toLegacy
        w hw K 0 vector horthogonal)
  rw [← centralPhysicalModulatedMarkovTransfer_toLegacy] at hlegacy
  rw [centralPhysicalModulatedInner_toLegacy] at hlegacy
  rw [centralPhysicalModulatedInner_toLegacy] at hlegacy
  exact hlegacy

/-! ## 2. Iterated geometric decay on the modulated carrier -/

/-- Powers of the Type-modulated physical macro transfer. -/
def centralPhysicalModulatedMarkovPower
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    Nat → CentralPhysicalModulatedGNSCompletion w hw K half →
      CentralPhysicalModulatedGNSCompletion w hw K half
  | 0, vector => vector
  | n + 1, vector =>
      centralPhysicalModulatedMarkovTransfer w hw K half
        (centralPhysicalModulatedMarkovPower w hw K half n vector)

/-- Forgetting explicit null moduli commutes with every macro-transfer power. -/
theorem centralPhysicalModulatedMarkovPower_toLegacy
    (w : Q') (hw : (0 : Q') ≤ w) (K half n : Nat)
    (vector : CentralPhysicalModulatedGNSCompletion w hw K half) :
    toLegacyCompletion
        (centralPhysicalSmulGNS w hw K half).toGNSData
        (centralPhysicalModulatedMarkovPower w hw K half n vector) =
      centralPhysicalCompletedMarkovPower w hw K half n
        (toLegacyCompletion
          (centralPhysicalSmulGNS w hw K half).toGNSData vector) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      change toLegacyCompletion _
        (centralPhysicalModulatedMarkovTransfer w hw K half
          (centralPhysicalModulatedMarkovPower w hw K half k vector)) = _
      rw [centralPhysicalModulatedMarkovTransfer_toLegacy, ih,
        centralPhysicalCompletedMarkovPower_succ]

/-- The producer-selected Type-modulated transfer powers have the same
geometric squared-norm decay `((1/16)^2)^n`. -/
theorem producer_modulated_power_norm_decay_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale n : Nat)
    (vector : CentralPhysicalModulatedGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)
    (horthogonal : CentralPhysicalModulatedVacuumOrthogonal
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 vector) :
    CReal.RCle
      (modulatedCinnerCompl
        (centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData
        (centralPhysicalModulatedMarkovPower
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 n vector)
        (centralPhysicalModulatedMarkovPower
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 n vector))
      (CReal.RCscale
        ((Q'.mkPos 1 16 (by decide) * Q'.mkPos 1 16 (by decide)) ^ n)
        (modulatedCinnerCompl
          (centralPhysicalSmulGNS
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0).toGNSData
          vector vector)) := by
  let w := matchedAllSpinWeight family coupling scale
  let hw := matchedAllSpinWeight_nonnegative family coupling scale
  let K := matchedAllSpinCutoff family coupling scale
  let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
  have hlegacy := producer_completed_power_norm_decay_sixteenth
    producer scale n (toLegacyCompletion D vector)
      (centralPhysicalModulatedVacuumOrthogonal_toLegacy
        w hw K 0 vector horthogonal)
  rw [← centralPhysicalModulatedMarkovPower_toLegacy] at hlegacy
  rw [centralPhysicalModulatedInner_toLegacy] at hlegacy
  rw [centralPhysicalModulatedInner_toLegacy] at hlegacy
  exact hlegacy

end YMGap.Continuum.BF4PhysicalModulatedOperatorNormGap

#print axioms YMGap.Continuum.BF4PhysicalModulatedOperatorNormGap.centralPhysicalModulatedVacuumOrthogonal_toLegacy
#print axioms YMGap.Continuum.BF4PhysicalModulatedOperatorNormGap.producer_modulated_vacuum_form_gap_sixteenth
#print axioms YMGap.Continuum.BF4PhysicalModulatedOperatorNormGap.producer_modulated_vacuum_operator_norm_gap_sixteenth
#print axioms YMGap.Continuum.BF4PhysicalModulatedOperatorNormGap.centralPhysicalModulatedMarkovPower_toLegacy
#print axioms YMGap.Continuum.BF4PhysicalModulatedOperatorNormGap.producer_modulated_power_norm_decay_sixteenth
