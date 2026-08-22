/-
# Centered physical AF rows give the completed BF4 gap

Exact local-slice power gluing is sufficient for the completed physical gap,
but it is not necessary.  The downstream quadratic argument consumes only a
rowwise `1/16` estimate for the literal centered physical joint.

This file records that minimal matched-AF certificate, forgets the unrelated
cross-zero Harnack field from the existing row package, and contracts the row
estimate through the finite quadratic form, constructive completion, concrete
operator norm, and same-vector power matrix coefficient.

No inhabitant of the row certificate is asserted.  No volume,
lattice-spacing, thermodynamic, or continuum limit is claimed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4BufferedPerronRowConvergence
import YMGap.Continuum.BF4PhysicalLocalGluingCompletedOperatorNormGap

namespace YMGap.Continuum.BF4PhysicalCenteredRowCompletedGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4BufferedPerronRowConvergence
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate
open YMGap.Continuum.BF4PhysicalLocalGluingCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. Minimal matched-AF centered-row certificate -/

/-- The exact rowwise finite input needed by the completed `1/16` gap along a
matched AF trajectory.  No Harnack, local-root, gluing, or endpoint field is
retained. -/
structure PhysicalCenteredRowSixteenthAFCertificate
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q') : Type where
  coupling_pos : ∀ scale, (0 : Q') < coupling scale
  coupling_le_window : ∀ scale, coupling scale ≤ law.g₁
  physical_centered_row_sixteenth :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0 →
        physicalCenteredPhysicalRowMass
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0 source ≤
          Q'.mkPos 1 16 (by decide) *
            centralPhysicalRowMarginal
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinWeight_nonnegative family coupling scale)
              (matchedAllSpinCutoff family coupling scale) 0 source

namespace PhysicalCenteredRowSixteenthAFCertificate

/-- The pre-existing cross-zero row package contains the minimal centered-row
certificate when specialized to the physical half-extent zero.  Its Harnack
and diagonal-order data are discarded. -/
def ofCrossZeroRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {diagonalOrder : Nat → Nat}
    (rows : MatchedCrossZeroPhysicalSixteenthRows
      family law spacing coupling (fun _ => 0) diagonalOrder) :
    PhysicalCenteredRowSixteenthAFCertificate
      family law spacing coupling where
  coupling_pos := rows.coupling_pos
  coupling_le_window := rows.coupling_le_window
  physical_centered_row_sixteenth :=
    rows.physical_centered_row_sixteenth

/-! ## 2. Row estimate to finite and completed form gaps -/

/-- The centered-row certificate contracts the literal finite physical joint
quadratic at every matched AF scale. -/
theorem physical_joint_quadratic_abs_le_sixteenth_at
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate : PhysicalCenteredRowSixteenthAFCertificate
      family law spacing coupling)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean : CentralPhysicalMeanZero
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 observable) :
    Q'.abs
        (centralPhysicalJointQuadratic
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 observable) ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          observable observable :=
  physical_joint_quadratic_abs_le_sixteenth_of_centered_rows
    (certificate.physical_centered_row_sixteenth scale)
    observable hmean

/-- The finite row estimate extends to the whole completed vacuum complement. -/
theorem completed_vacuum_form_gap_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate : PhysicalCenteredRowSixteenthAFCertificate
      family law spacing coupling)
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
        vector)
      (CReal.RCscale (Q'.mkPos 1 16 (by decide))
        ((centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
          vector vector)) :=
  centralPhysical_completed_vacuum_form_gap_sixteenth_of_finite_gap
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (certificate.physical_joint_quadratic_abs_le_sixteenth_at scale)
    vector horthogonal

/-- Package the row-derived completed form gap for the generic operator
theorems. -/
def completed_vacuum_form_gap_data
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate : PhysicalCenteredRowSixteenthAFCertificate
      family law spacing coupling)
    (scale : Nat) :
    CentralPhysicalCompletedVacuumFormGap
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0
      (Q'.mkPos 1 16 (by decide)) :=
  ⟨by decide, by decide,
    certificate.completed_vacuum_form_gap_sixteenth scale⟩

/-! ## 3. Concrete operator and same-object power decay -/

/-- The row certificate gives the concrete completed transfer estimate
`||T v||^2 <= (1/16)^2 ||v||^2` on the vacuum complement. -/
theorem completed_vacuum_operator_norm_gap_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate : PhysicalCenteredRowSixteenthAFCertificate
      family law spacing coupling)
    (scale : Nat)
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
    let transferred := centralPhysicalCompletedMarkovTransfer w hw K 0 vector
    CReal.RCle
      (D.cinnerCompl transferred transferred)
      (CReal.RCscale
        (Q'.mkPos 1 16 (by decide) * Q'.mkPos 1 16 (by decide))
        (D.cinnerCompl vector vector)) := by
  dsimp only
  exact centralPhysicalCompletedMarkovTransfer_norm_gap_of_form_gap
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (certificate.completed_vacuum_form_gap_data scale)
    vector horthogonal

/-- The same row certificate gives geometric squared same-vector matrix-
coefficient decay after every completed physical macro step. -/
theorem completed_power_autocorrelationSq_decay_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate : PhysicalCenteredRowSixteenthAFCertificate
      family law spacing coupling)
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
  exact centralPhysicalCompletedMarkovPower_matrixCoefficientSq_decay_of_form_gap
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (certificate.completed_vacuum_form_gap_data scale)
    n vector vector horthogonal

end PhysicalCenteredRowSixteenthAFCertificate

/-! ## Axiom audit -/

#print axioms PhysicalCenteredRowSixteenthAFCertificate.ofCrossZeroRows
#print axioms PhysicalCenteredRowSixteenthAFCertificate.physical_joint_quadratic_abs_le_sixteenth_at
#print axioms PhysicalCenteredRowSixteenthAFCertificate.completed_vacuum_form_gap_sixteenth
#print axioms PhysicalCenteredRowSixteenthAFCertificate.completed_vacuum_form_gap_data
#print axioms PhysicalCenteredRowSixteenthAFCertificate.completed_vacuum_operator_norm_gap_sixteenth
#print axioms PhysicalCenteredRowSixteenthAFCertificate.completed_power_autocorrelationSq_decay_sixteenth

end YMGap.Continuum.BF4PhysicalCenteredRowCompletedGap
