/-
# Support-safe physical core/tail data give the completed BF4 gap

The literal centered-row route does not consume the calibrated profile
Harnack field carried by the older matched core/tail package.  This file
factors the actual support-safe analytic leaf at physical half-extent zero:

* a retained core on which the weighted density error is at most `1/32`;
* stationary mass of the discarded tail at most `1/64`; and
* conditional row mass of the discarded tail at most `1/64`.

These source-dependent finite windows permit fusion zeros.  They contract to
the literal physical centered-row estimate `1/16`, then to the already
constructed completed vacuum form gap, concrete operator gap, and geometric
same-vector power decay.

Adapters are supplied from both the pre-existing matched core/tail rows and
the deeper buffered-Faraut rows.  No inhabitant of any matched certificate is
asserted.  No volume, lattice-spacing, thermodynamic, or continuum limit is
claimed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCenteredRowCompletedGap
import YMGap.Continuum.BF4PhysicalDensityThresholdCoreAF

namespace YMGap.Continuum.BF4PhysicalCoreTailCompletedGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedBufferedPerronEighthClosure
open YMGap.Continuum.BF4PhysicalCenteredRowCompletedGap
open YMGap.Continuum.BF4PhysicalConditionalDensityContraction
open YMGap.Continuum.BF4PhysicalDensityThresholdCoreAF
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. Minimal support-safe matched-AF certificate -/

/-- The exact support-safe density data needed to prove the completed gap at
physical half-extent zero.  The core may depend on the scale and source, so
fusion-zero targets can be discarded into the two explicitly controlled
tails.  No Harnack or diagonal-order field is retained. -/
structure PhysicalConditionalDensityCoreTailAFCertificate
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q') : Type where
  coupling_pos : ∀ scale, (0 : Q') < coupling scale
  coupling_le_window : ∀ scale, coupling scale ≤ law.g₁
  inCore : Nat → EdgeLabelling → EdgeLabelling → Bool
  coreTail_exists :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0 →
        Nonempty
          (PhysicalConditionalDensityCoreTailWindow
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0 source
            (inCore scale source))

namespace PhysicalConditionalDensityCoreTailAFCertificate

/-- Forget the unused calibrated-Harnack and diagonal-order data from the
older matched support-safe package, specialized to physical half-extent
zero. -/
def ofMatchedCoreTailRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {diagonalOrder : Nat → Nat}
    (rows : MatchedPhysicalConditionalDensityCoreTailRows
      family law spacing coupling (fun _ => 0) diagonalOrder) :
    PhysicalConditionalDensityCoreTailAFCertificate
      family law spacing coupling where
  coupling_pos := rows.coupling_pos
  coupling_le_window := rows.coupling_le_window
  inCore := rows.inCore
  coreTail_exists := rows.coreTail_exists

/-- Deeper matched buffered-Faraut rows provide the minimal support-safe
certificate whenever their depth pays the explicit core/tail budget. -/
def ofFarautBufferedRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {diagonalOrder : Nat → Nat}
    (rows : MatchedPhysicalBF4FarautBufferedRows
      family law spacing coupling (fun _ => 0) diagonalOrder)
    (core_depth_available :
      ∀ scale,
        farautCoreTailRequiredDepth (rows.bits scale) ≤
          rows.depth scale) :
    PhysicalConditionalDensityCoreTailAFCertificate
      family law spacing coupling :=
  ofMatchedCoreTailRows
    (matchedThirtySecondCoreTailRows_of_buffered
      rows core_depth_available)

/-! ## 2. Core/tail windows to literal centered rows -/

/-- The three support-safe budgets sum to the literal physical centered-row
rate `1/16` at every matched AF scale and physical source. -/
theorem physical_centered_row_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate : PhysicalConditionalDensityCoreTailAFCertificate
      family law spacing coupling)
    (scale : Nat) (source : EdgeLabelling)
    (source_mem :
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0) :
    physicalCenteredPhysicalRowMass
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 source := by
  obtain ⟨window⟩ :=
    certificate.coreTail_exists scale source source_mem
  exact window.physical_centered_row_sixteenth

/-- Forget the explicit core/tail decomposition after it has discharged the
literal centered-row estimate. -/
def toCenteredRowCertificate
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate : PhysicalConditionalDensityCoreTailAFCertificate
      family law spacing coupling) :
    PhysicalCenteredRowSixteenthAFCertificate
      family law spacing coupling where
  coupling_pos := certificate.coupling_pos
  coupling_le_window := certificate.coupling_le_window
  physical_centered_row_sixteenth :=
    certificate.physical_centered_row_sixteenth

/-! ## 3. Completed operator and same-object consequences -/

/-- The support-safe core/tail windows give the completed physical vacuum
form gap at rate `1/16`. -/
def completed_vacuum_form_gap_data
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate : PhysicalConditionalDensityCoreTailAFCertificate
      family law spacing coupling)
    (scale : Nat) :=
  certificate.toCenteredRowCertificate
    |>.completed_vacuum_form_gap_data scale

/-- The support-safe core/tail windows give the concrete completed transfer
estimate `||T v||^2 <= (1/16)^2 ||v||^2` on the vacuum complement. -/
def completed_vacuum_operator_norm_gap_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate : PhysicalConditionalDensityCoreTailAFCertificate
      family law spacing coupling)
    (scale : Nat)
    (vector : CentralPhysicalGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 vector) :=
  certificate.toCenteredRowCertificate
    |>.completed_vacuum_operator_norm_gap_sixteenth
      scale vector horthogonal

/-- The same support-safe windows give geometric squared same-vector
completed matrix-coefficient decay at rate `((1/16)^2)^n`. -/
def completed_power_autocorrelationSq_decay_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate : PhysicalConditionalDensityCoreTailAFCertificate
      family law spacing coupling)
    (scale n : Nat)
    (vector : CentralPhysicalGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 vector) :=
  certificate.toCenteredRowCertificate
    |>.completed_power_autocorrelationSq_decay_sixteenth
      scale n vector horthogonal

end PhysicalConditionalDensityCoreTailAFCertificate

/-! ## Axiom audit -/

#print axioms PhysicalConditionalDensityCoreTailAFCertificate.ofMatchedCoreTailRows
#print axioms PhysicalConditionalDensityCoreTailAFCertificate.ofFarautBufferedRows
#print axioms PhysicalConditionalDensityCoreTailAFCertificate.physical_centered_row_sixteenth
#print axioms PhysicalConditionalDensityCoreTailAFCertificate.toCenteredRowCertificate
#print axioms PhysicalConditionalDensityCoreTailAFCertificate.completed_vacuum_form_gap_data
#print axioms PhysicalConditionalDensityCoreTailAFCertificate.completed_vacuum_operator_norm_gap_sixteenth
#print axioms PhysicalConditionalDensityCoreTailAFCertificate.completed_power_autocorrelationSq_decay_sixteenth

end YMGap.Continuum.BF4PhysicalCoreTailCompletedGap
