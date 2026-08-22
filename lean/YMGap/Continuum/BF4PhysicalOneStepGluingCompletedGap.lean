/-
# One-step BF4 gluing rows give the completed physical gap

The existing matched one-step gluing rows are stronger than the direct
physical local-gluing certificate: they also carry endpoint/Faraut estimates.
The forgetful adapter removes those unused fields.  This file records the
resulting end-to-end contraction from the genuine shared one-step kernel to
the completed physical vacuum form gap and its same-vector power-correlation
decay.

No inhabitant of the matched one-step row family is asserted.  Exact density
gluing and the uniform local quarter bound remain the analytic producer leaf.
No volume, lattice-spacing, thermodynamic, or continuum limit is claimed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalLocalGluingAFAdapter
import YMGap.Continuum.BF4PhysicalLocalGluingCompletedOperatorNormGap

namespace YMGap.Continuum.BF4PhysicalOneStepGluingCompletedGap

open YMGap.Constructive
open YMGap.Continuum.BF4GroupedCommonKernelPerronAction
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalLocalGluingAFAdapter
open YMGap.Continuum.BF4PhysicalLocalGluingCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. Direct completed form-gap package -/

/-- Genuine matched one-step gluing rows, stripped of their unused endpoint
fields, give the completed `1/16` vacuum form gap at every AF scale. -/
def oneStepGluing_completed_vacuum_form_gap_data
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bits depth : Nat → Nat}
    {localRate : Nat → Q'}
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (localRate_le_quarter :
      ∀ scale,
        localRate scale ≤
          YMGap.Continuum.FiveHolonomyPerronCutoff.quarter)
    (oneStep :
      ∀ (_scale : Nat), EdgeLabelling → EdgeLabelling → Q')
    (rows : MatchedBF4OneStepGluingRows
      family coupling (fun _ => 0) bits depth localRate oneStep)
    (scale : Nat) :
    CentralPhysicalCompletedVacuumFormGap
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0
      (Q'.mkPos 1 16 (by decide)) :=
  localGluing_completed_vacuum_form_gap_data (spacing := spacing)
    (ofOneStepGluingRows (spacing := spacing)
      coupling_pos coupling_le_window localRate_le_quarter
      oneStep rows)
    scale

/-! ## 2. Strongest immediate same-object consequence -/

/-- The same one-step gluing rows imply geometric decay of the squared
same-vector completed matrix coefficient after every number of macro steps. -/
theorem oneStepGluing_completed_power_autocorrelationSq_decay_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bits depth : Nat → Nat}
    {localRate : Nat → Q'}
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (localRate_le_quarter :
      ∀ scale,
        localRate scale ≤
          YMGap.Continuum.FiveHolonomyPerronCutoff.quarter)
    (oneStep :
      ∀ (_scale : Nat), EdgeLabelling → EdgeLabelling → Q')
    (rows : MatchedBF4OneStepGluingRows
      family coupling (fun _ => 0) bits depth localRate oneStep)
    (scale n : Nat)
    (vector : CentralPhysicalGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 vector) :
    let w := matchedAllSpinWeight family coupling scale
    let hw := matchedAllSpinWeight_nonnegative family coupling scale
    let K := matchedAllSpinCutoff family coupling scale
    let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
    let propagated :=
      centralPhysicalCompletedMarkovPower w hw K 0 n vector
    CReal.RCle
      (CReal.RCmul
        (D.cinnerCompl propagated vector)
        (D.cinnerCompl propagated vector))
      (CReal.RCmul
        (CReal.RCscale
          ((Q'.mkPos 1 16 (by decide) * Q'.mkPos 1 16 (by decide)) ^ n)
          (D.cinnerCompl vector vector))
        (D.cinnerCompl vector vector)) := by
  exact localGluing_completed_power_autocorrelationSq_decay_sixteenth
    (spacing := spacing)
    (ofOneStepGluingRows (spacing := spacing)
      coupling_pos coupling_le_window localRate_le_quarter
      oneStep rows)
    scale n vector horthogonal

/-! ## Axiom audit -/

#print axioms oneStepGluing_completed_vacuum_form_gap_data
#print axioms oneStepGluing_completed_power_autocorrelationSq_decay_sixteenth

end YMGap.Continuum.BF4PhysicalOneStepGluingCompletedGap
