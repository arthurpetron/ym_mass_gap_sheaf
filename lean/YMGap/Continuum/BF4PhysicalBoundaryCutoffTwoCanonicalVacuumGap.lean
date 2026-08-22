/-
# Canonical cutoff-two vacuum-sector gap

This module contracts the two independently checked cutoff-two facts into one
honest theorem: the certified 65-state block is exactly the support component
of the vacuum in the genuine positive-row physical Markov carrier, and the
production reflected kernel on that same block obeys the absolute centered
`49/50` form bound.

The coefficient coordinates below use the certified 65-state enumeration;
the support equality proves that this is an enumeration of the canonical
vacuum sector.  No cross-cutoff compatibility, Hilbert completion,
thermodynamic limit, continuum theory, or Clay conclusion is asserted.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalUpperGap

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumGap

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalUpperGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-- The exact canonical-vacuum support identification and its strict absolute
production-kernel contraction, exposed as one finite-cutoff theorem. -/
theorem cutoffTwoCanonicalVacuumSector_exact_and_strict_abs_gap :
    (∀ state : EdgeLabelling,
      state ∈ centralPhysicalFiniteVacuumSectorStates
          cutoffTwoHalfCoupling (by decide) 2 0 ↔
        state ∈ cutoffTwoCubeSectorStates) ∧
      cutoffTwoSectorRate49Over50 < (1 : Q') ∧
      ∀ coefficient : Nat → Q',
        finiteWeightedMean 65
            cutoffTwoSectorPhysicalRowSum coefficient ≈ 0 →
          Q'.abs
              (finiteMatrixQuadratic 65
                cutoffTwoSectorPhysicalKernel coefficient) ≤
            cutoffTwoSectorRate49Over50 *
              finiteDiagonalQuadratic 65
                cutoffTwoSectorPhysicalRowSum coefficient := by
  exact ⟨centralPhysicalFiniteVacuumSectorStates_cutoffTwo_iff,
    cutoffTwoSectorPhysicalStrictAbsGapAt49Over50⟩

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumGap
