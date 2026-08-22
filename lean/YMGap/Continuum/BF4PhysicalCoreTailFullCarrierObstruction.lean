/-
# The cutoff-two obstruction to full-carrier BF4 core/tail certificates

The support-safe core/tail estimate is mathematically sufficient for a strict
gap on the carrier on which it is imposed.  The literal positive BF4 carrier,
however, is already reducible at cutoff two: an exact centered sector
indicator is fixed by the physical Markov operator and has positive norm.

This module closes the resulting logical loop.  It proves that no choice of
core predicate can supply the `1/32 + 1/64 + 1/64` window for every retained
cutoff-two source.  Consequently the executable all-row checker cannot return
`true` at that cutoff.  This is a routing theorem: any uniform physical gap
campaign must first select the canonical vacuum communicating component.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCoreTailFiniteChecker
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorReducibilityObstruction

namespace YMGap.Continuum.BF4PhysicalCoreTailFullCarrierObstruction

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorReducibilityObstruction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalConditionalDensityContraction
open YMGap.Continuum.BF4PhysicalCoreTailFiniteChecker
open YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. The analytic all-row leaf is impossible on the full carrier -/

/-- No source-dependent core can provide the support-safe window for every
source of the literal cutoff-two positive carrier.  Such windows would imply
the strict full-carrier form gap ruled out by the exact reducibility mode. -/
theorem no_cutoffTwo_fullCarrier_coreTail_allRows
    (inCore : EdgeLabelling → EdgeLabelling → Bool) :
    ¬ (∀ source,
      source ∈ centralPositiveHalfStates cutoffTwoHalfCoupling
          (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0 →
        Nonempty
          (PhysicalConditionalDensityCoreTailWindow
            cutoffTwoHalfCoupling
            (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
            2 0 source (inCore source))) := by
  intro windows
  apply no_cutoffTwo_fullCarrier_strict_abs_gap
    (Q'.mkPos 1 16 (by decide)) (by decide)
  intro observable hmean
  apply physical_joint_quadratic_abs_le_sixteenth_of_centered_rows
    (observable := observable) (hmean := hmean)
  intro source hsource
  obtain ⟨window⟩ := windows source hsource
  exact window.physical_centered_row_sixteenth

/-! ## 2. The exact finite checker cannot certify the false target -/

/-- The canonical exact Boolean scan is provably unable to return `true` at
cutoff two, independently of the proposed source-dependent core.  This is not
a timeout or a performance diagnosis; it is a kernel-checked mathematical
impossibility result for the full-carrier target. -/
theorem cutoffTwo_fullCarrier_allRowsCheck_ne_true
    (inCore : EdgeLabelling → EdgeLabelling → Bool) :
    physicalConditionalDensityCoreTailAllRowsCheck
        cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 0 inCore ≠ true := by
  intro checked
  apply no_cutoffTwo_fullCarrier_coreTail_allRows inCore
  intro source hsource
  exact physicalConditionalDensityCoreTailWindow_of_allRowsCheck
    checked source hsource

end YMGap.Continuum.BF4PhysicalCoreTailFullCarrierObstruction

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCoreTailFullCarrierObstruction.no_cutoffTwo_fullCarrier_coreTail_allRows
#print axioms
  YMGap.Continuum.BF4PhysicalCoreTailFullCarrierObstruction.cutoffTwo_fullCarrier_allRowsCheck_ne_true
