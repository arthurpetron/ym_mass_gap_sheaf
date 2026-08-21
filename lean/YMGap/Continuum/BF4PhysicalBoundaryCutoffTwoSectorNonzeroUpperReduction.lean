/-
# Reduce the physical-table certificate to unordered nonzero entries

The literal cutoff-two table contains many exact zeros.  Those entries are
already known to vanish in the production physical kernel by local support.
Physical symmetry then reduces the remaining comparison to the upper
triangle, provided the literal raw table is itself certified symmetric.

This module packages exactly that smaller residual and compiles it back to the
row-check certificate consumed by the physical table bridge.  It does not
inhabit the residual certificate.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassificationCompact
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorNonzeroUpperReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComputedKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassificationCompact
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

local infix:50 " ≈ " => Q'.eqv

/-- The remaining expensive comparison after locally forced zeros and
physical symmetry have been removed.  Raw-table symmetry is kept as a
separate, cheap finite field so the physical field only covers unordered
nonzero pairs. -/
structure CutoffTwoSectorPhysicalNonzeroUpperCertificate : Type where
  rawSymmetry : ∀ {row column : Nat}, row < 65 → column < 65 →
    cutoffTwoSectorRawKernel row column ≈
      cutoffTwoSectorRawKernel column row
  upperNonzeroChecked : ∀ {row column : Nat},
    row < 65 → column < 65 → row ≤ column →
    ¬ cutoffTwoSectorRawKernel row column ≈ 0 →
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt row)
        (cutoffTwoSectorStateAt column) ≈
      cutoffTwoSectorRawKernel row column

/-- Local-zero classification handles zero entries; physical and raw
symmetry reflect a checked upper entry into the lower triangle. -/
theorem centralPhysicalReflectedKernel_cutoffTwo_sectorStateAt_eqv_raw_of_nonzeroUpper
    (certificate : CutoffTwoSectorPhysicalNonzeroUpperCertificate)
    {row column : Nat} (hrow : row < 65) (hcolumn : column < 65) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt row)
        (cutoffTwoSectorStateAt column) ≈
      cutoffTwoSectorRawKernel row column := by
  by_cases hzero : cutoffTwoSectorRawKernel row column ≈ 0
  · have hphysicalZero :
        centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
            (cutoffTwoSectorStateAt row)
            (cutoffTwoSectorStateAt column) ≈ 0 := by
      simpa only [cutoffTwoSectorStateAt,
        cutoffTwoSectorLocalZeroStateAt] using
        (centralPhysicalReflectedKernel_cutoffTwo_sector_index_eqv_zero_of_raw_compact
          hrow hcolumn hzero)
    exact Q'.eqv_trans _ _ _ hphysicalZero (Q'.eqv_symm hzero)
  · by_cases hupper : row ≤ column
    · exact certificate.upperNonzeroChecked hrow hcolumn hupper hzero
    · have hlower : column ≤ row := by omega
      have hswappedNonzero :
          ¬ cutoffTwoSectorRawKernel column row ≈ 0 := by
        intro hswappedZero
        exact hzero (Q'.eqv_trans _ _ _
          (certificate.rawSymmetry hrow hcolumn) hswappedZero)
      have hswapped := certificate.upperNonzeroChecked
        hcolumn hrow hlower hswappedNonzero
      have hphysicalSymmetry :=
        centralPhysicalReflectedKernel_symm cutoffTwoHalfCoupling
          (cutoffTwoCubeSectorState_mem_halfStates
            (cutoffTwoSectorStateAt_mem hrow))
          (cutoffTwoCubeSectorState_mem_halfStates
            (cutoffTwoSectorStateAt_mem hcolumn))
      exact Q'.eqv_trans _ _ _ hphysicalSymmetry
        (Q'.eqv_trans _ _ _ hswapped
          (Q'.eqv_symm (certificate.rawSymmetry hrow hcolumn)))

/-- The smaller unordered-nonzero certificate constructs the original
65-row recurrence certificate without evaluating the giant recurrence in a
Boolean normalizer. -/
def CutoffTwoSectorPhysicalNonzeroUpperCertificate.toPhysicalTableCertificate
    (certificate : CutoffTwoSectorPhysicalNonzeroUpperCertificate) :
    CutoffTwoSectorPhysicalTableCertificate where
  rowsChecked := by
    intro row hrow
    unfold cutoffTwoSectorRawKernelRowCheck
    apply List.all_eq_true.mpr
    intro column hcolumn
    apply decide_eq_true
    have hphysical :=
      centralPhysicalReflectedKernel_cutoffTwo_sectorStateAt_eqv_raw_of_nonzeroUpper
        certificate hrow (List.mem_range.mp hcolumn)
    have hcomputed :
        centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
            (cutoffTwoSectorStateAt row)
            (cutoffTwoSectorStateAt column) ≈
          cutoffTwoSectorComputedRawKernel row column := by
      simpa only [cutoffTwoSectorComputedRawKernel] using
        (centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_computed
          (cutoffTwoSectorStateAt row)
          (cutoffTwoSectorStateAt column)
          (cutoffTwoSectorStateAt_mem hrow)
          (cutoffTwoSectorStateAt_mem (List.mem_range.mp hcolumn)))
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hcomputed) hphysical

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorNonzeroUpperReduction

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorNonzeroUpperReduction.centralPhysicalReflectedKernel_cutoffTwo_sectorStateAt_eqv_raw_of_nonzeroUpper
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorNonzeroUpperReduction.CutoffTwoSectorPhysicalNonzeroUpperCertificate.toPhysicalTableCertificate
