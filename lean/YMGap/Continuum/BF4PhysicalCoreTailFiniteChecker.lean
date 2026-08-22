/-
# Executable finite checker for the support-safe physical core/tail frontier

The completed BF4 gap now reduces to three rational core/tail inequalities on
the literal finite physical carrier.  This file makes that remaining leaf
executable.  One Boolean row check verifies all nonnegativity, normalization,
core, and tail clauses of `FiniteWeightedDensityCoreTailWindow`.  A second
Boolean check scans every physical source at one cutoff.  Soundness theorems
turn `check = true` into the exact proof structures consumed downstream.

Along a matched AF trajectory, one true all-source check per scale therefore
constructs the minimal support-safe certificate and the completed same-object
decay theorem.  No check is claimed to evaluate to true here.  In particular,
the file provides a verified decision procedure and compiler, not the still
missing uniform analytic/numerical certificate.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCoreTailCompletedGap

namespace YMGap.Continuum.BF4PhysicalCoreTailFiniteChecker

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalConditionalDensity
open YMGap.Continuum.BF4PhysicalConditionalDensityContraction
open YMGap.Continuum.BF4PhysicalCoreTailCompletedGap
open YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate
open YMGap.Continuum.BF4PhysicalLocalGluingCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic finite row checker -/

/-- Executably verify every field of a finite weighted density core/tail
window.  All arithmetic is exact `Q'` arithmetic; no floating-point or
external oracle is involved. -/
def finiteWeightedDensityCoreTailCheck
    {State : Type}
    (states : List State) (weight : State → Q')
    (kernel : State → State → Q')
    (source : State) (inCore : State → Bool)
    (coreTolerance tailTolerance : Q') : Bool :=
  states.all (fun state =>
      decide ((0 : Q') ≤ weight state)) &&
    (states.all (fun target =>
      decide ((0 : Q') ≤ kernel source target)) &&
    (decide (listQSum weight states ≈ 1) &&
    (decide ((0 : Q') ≤ coreTolerance) &&
    (states.all (fun target =>
      if inCore target = true then
        decide
          (Q'.abs (kernel source target + (-1)) ≤
            coreTolerance)
      else true) &&
    (decide
      (listQSum
          (fun target =>
            if inCore target = true then 0
            else weight target)
          states ≤
        tailTolerance) &&
      decide
        (listQSum
            (fun target =>
              if inCore target = true then 0
              else weight target * kernel source target)
            states ≤
          tailTolerance))))))

/-- Soundness of the executable generic row check. -/
def finiteWeightedDensityCoreTailWindow_of_check
    {State : Type}
    {states : List State} {weight : State → Q'}
    {kernel : State → State → Q'}
    {source : State} {inCore : State → Bool}
    {coreTolerance tailTolerance : Q'}
    (checked :
      finiteWeightedDensityCoreTailCheck
        states weight kernel source inCore
        coreTolerance tailTolerance = true) :
    FiniteWeightedDensityCoreTailWindow
      states weight kernel source inCore
      coreTolerance tailTolerance := by
  unfold finiteWeightedDensityCoreTailCheck at checked
  simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
  rcases checked with
    ⟨hweight, hkernel, htotal, hcoreNonnegative,
      hcore, htailWeight, htailKernel⟩
  refine
    { weight_nonnegative := ?_
      kernel_nonnegative := ?_
      weight_total := ?_
      coreTolerance_nonnegative := ?_
      core_pointwise := ?_
      tail_weight := ?_
      tail_kernel := ?_ }
  · intro state hstate
    have hchecked :=
      List.all_eq_true.mp hweight state hstate
    simpa only [decide_eq_true_eq] using hchecked
  · intro target htarget
    have hchecked :=
      List.all_eq_true.mp hkernel target htarget
    simpa only [decide_eq_true_eq] using hchecked
  · simpa only [decide_eq_true_eq] using htotal
  · simpa only [decide_eq_true_eq] using hcoreNonnegative
  · intro target htarget htargetCore
    have hchecked :=
      List.all_eq_true.mp hcore target htarget
    rw [if_pos htargetCore] at hchecked
    simpa only [decide_eq_true_eq] using hchecked
  · simpa only [decide_eq_true_eq] using htailWeight
  · simpa only [decide_eq_true_eq] using htailKernel

/-! ## 2. Canonical physical row and all-source checkers -/

/-- The generic exact checker specialized to one canonical physical BF4
conditional-density row and the `1/32 + 1/64 + 1/64` budgets. -/
def physicalConditionalDensityCoreTailRowCheck
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (source : EdgeLabelling)
    (inCore : EdgeLabelling → Bool) : Bool :=
  finiteWeightedDensityCoreTailCheck
    (centralPositiveHalfStates w hw K half)
    (centralPhysicalRowMarginal w hw K half)
    (centralPhysicalConditionalDensity w hw K half)
    source inCore
    (Q'.mkPos 1 32 (by decide))
    (Q'.mkPos 1 64 (by decide))

/-- A true canonical row check constructs the exact support-safe physical
window, assuming only that the checked source belongs to the carrier. -/
def physicalConditionalDensityCoreTailWindow_of_rowCheck
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    {inCore : EdgeLabelling → Bool}
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half)
    (checked :
      physicalConditionalDensityCoreTailRowCheck
        w hw K half source inCore = true) :
    PhysicalConditionalDensityCoreTailWindow
      w hw K half source inCore where
  source_mem := source_mem
  window := ⟨finiteWeightedDensityCoreTailWindow_of_check checked⟩

/-- Scan the exact finite physical carrier and verify the core/tail window for
every source in one Boolean computation. -/
def physicalConditionalDensityCoreTailAllRowsCheck
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (inCore : EdgeLabelling → EdgeLabelling → Bool) : Bool :=
  (centralPositiveHalfStates w hw K half).all
    (fun source =>
      physicalConditionalDensityCoreTailRowCheck
        w hw K half source (inCore source))

/-- Soundness of the all-source physical scan. -/
theorem physicalConditionalDensityCoreTailWindow_of_allRowsCheck
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    {inCore : EdgeLabelling → EdgeLabelling → Bool}
    (checked :
      physicalConditionalDensityCoreTailAllRowsCheck
        w hw K half inCore = true)
    (source : EdgeLabelling)
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half) :
    Nonempty
      (PhysicalConditionalDensityCoreTailWindow
        w hw K half source (inCore source)) := by
  have hrow :=
    List.all_eq_true.mp checked source source_mem
  exact ⟨
    physicalConditionalDensityCoreTailWindow_of_rowCheck
      source_mem hrow⟩

/-! ## 3. Checked matched-AF family to completed decay -/

/-- A fully executable formulation of the remaining matched support-safe
frontier: at every scale, one finite all-source Boolean scan returns true.
The scale quantifier remains an analytic/uniformity obligation; each value it
asserts is nevertheless a concrete exact computation. -/
structure PhysicalConditionalDensityCoreTailAFCheckedCertificate
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q') : Type where
  coupling_pos : ∀ scale, (0 : Q') < coupling scale
  coupling_le_window : ∀ scale, coupling scale ≤ law.g₁
  inCore : Nat → EdgeLabelling → EdgeLabelling → Bool
  allRows_checked :
    ∀ scale,
      physicalConditionalDensityCoreTailAllRowsCheck
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
        (inCore scale) = true

namespace PhysicalConditionalDensityCoreTailAFCheckedCertificate

/-- Compile the executable all-source checks into the minimal support-safe
matched-AF certificate. -/
def toCoreTailCertificate
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (checked : PhysicalConditionalDensityCoreTailAFCheckedCertificate
      family law spacing coupling) :
    PhysicalConditionalDensityCoreTailAFCertificate
      family law spacing coupling where
  coupling_pos := checked.coupling_pos
  coupling_le_window := checked.coupling_le_window
  inCore := checked.inCore
  coreTail_exists := by
    intro scale source source_mem
    exact physicalConditionalDensityCoreTailWindow_of_allRowsCheck
      (checked.allRows_checked scale) source source_mem

/-- The checked family gives the completed vacuum form gap data. -/
def completed_vacuum_form_gap_data
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (checked : PhysicalConditionalDensityCoreTailAFCheckedCertificate
      family law spacing coupling)
    (scale : Nat) :=
  checked.toCoreTailCertificate
    |>.completed_vacuum_form_gap_data scale

/-- A true finite all-source scan at every matched scale gives geometric
squared same-vector completed matrix-coefficient decay. -/
def completed_power_autocorrelationSq_decay_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (checked : PhysicalConditionalDensityCoreTailAFCheckedCertificate
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
  checked.toCoreTailCertificate
    |>.completed_power_autocorrelationSq_decay_sixteenth
      scale n vector horthogonal

end PhysicalConditionalDensityCoreTailAFCheckedCertificate

/-! ## 4. Concrete checker smoke test -/

/-- The closed nonnegativity proof used by the concrete cutoff-zero check. -/
theorem cutoffZeroCoupling_nonnegative :
    (0 : Q') ≤ (1 : Q') := by
  decide

/-- At the zero representation cutoff the exact canonical physical carrier
passes the all-source support-safe check with the full carrier retained.  This
is a kernel-evaluated base case for the checker, not an AF-uniform estimate. -/
theorem cutoffZero_allRows_check_true :
    physicalConditionalDensityCoreTailAllRowsCheck
      (1 : Q') cutoffZeroCoupling_nonnegative
      0 0 (fun _ _ => true) = true := by
  decide

/-- The evaluated cutoff-zero check proves the literal centered physical row
bound for every retained source. -/
theorem cutoffZero_physical_centered_row_sixteenth
    (source : EdgeLabelling)
    (source_mem :
      source ∈ centralPositiveHalfStates
        (1 : Q') cutoffZeroCoupling_nonnegative 0 0) :
    physicalCenteredPhysicalRowMass
        (1 : Q') cutoffZeroCoupling_nonnegative 0 0 source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          (1 : Q') cutoffZeroCoupling_nonnegative 0 0 source := by
  obtain ⟨window⟩ :=
    physicalConditionalDensityCoreTailWindow_of_allRowsCheck
      cutoffZero_allRows_check_true source source_mem
  exact window.physical_centered_row_sixteenth

/-- Hence the concrete cutoff-zero physical joint has the finite mean-zero
quadratic gap at rate `1/16`. -/
def cutoffZero_finite_quadratic_gap :
    CentralPhysicalFiniteQuadraticGapSixteenth
      (1 : Q') cutoffZeroCoupling_nonnegative 0 0 :=
  physical_joint_quadratic_abs_le_sixteenth_of_centered_rows
    cutoffZero_physical_centered_row_sixteenth

/-- Package the concrete cutoff-zero completed vacuum form gap. -/
def cutoffZero_completed_vacuum_form_gap_data :
    CentralPhysicalCompletedVacuumFormGap
      (1 : Q') cutoffZeroCoupling_nonnegative 0 0
      (Q'.mkPos 1 16 (by decide)) :=
  ⟨by decide, by decide,
    centralPhysical_completed_vacuum_form_gap_sixteenth_of_finite_gap
      cutoffZeroCoupling_nonnegative 0 0
      cutoffZero_finite_quadratic_gap⟩

/-- The kernel-evaluated cutoff-zero physical model has geometric squared
same-vector completed matrix-coefficient decay.  This is an inhabited finite
base case, not uniformity in representation cutoff or physical scale. -/
def cutoffZero_completed_power_autocorrelationSq_decay_sixteenth
    (n : Nat)
    (vector : CentralPhysicalGNSCompletion
      (1 : Q') cutoffZeroCoupling_nonnegative 0 0)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      (1 : Q') cutoffZeroCoupling_nonnegative 0 0 vector) :=
  centralPhysicalCompletedMarkovPower_matrixCoefficientSq_decay_of_form_gap
    cutoffZeroCoupling_nonnegative 0 0
    cutoffZero_completed_vacuum_form_gap_data
    n vector vector horthogonal

/-! ## Axiom audit -/

#print axioms finiteWeightedDensityCoreTailWindow_of_check
#print axioms physicalConditionalDensityCoreTailWindow_of_rowCheck
#print axioms physicalConditionalDensityCoreTailWindow_of_allRowsCheck
#print axioms PhysicalConditionalDensityCoreTailAFCheckedCertificate.toCoreTailCertificate
#print axioms PhysicalConditionalDensityCoreTailAFCheckedCertificate.completed_vacuum_form_gap_data
#print axioms PhysicalConditionalDensityCoreTailAFCheckedCertificate.completed_power_autocorrelationSq_decay_sixteenth
#print axioms cutoffZeroCoupling_nonnegative
#print axioms cutoffZero_allRows_check_true
#print axioms cutoffZero_physical_centered_row_sixteenth
#print axioms cutoffZero_finite_quadratic_gap
#print axioms cutoffZero_completed_vacuum_form_gap_data
#print axioms cutoffZero_completed_power_autocorrelationSq_decay_sixteenth

end YMGap.Continuum.BF4PhysicalCoreTailFiniteChecker
