/-
# Production Gram positivity on the cutoff-two sector

The indexed production kernel on the exact 65-state sector is a finite
weighted Gram kernel.  Consequently its quadratic form is nonnegative for
every rational coefficient family.

This is finite-volume and cutoff-two only.  No completed-space, uniform,
thermodynamic, continuum, or Clay conclusion is asserted.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalFormTransport
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalUpperGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- Every entry of the restricted production kernel retains the same weighted
Gram factorization as the full finite physical kernel.  The state type here is
the literal table index, so no choice of inverse enumeration is required. -/
theorem cutoffTwoSectorPhysicalKernel_eqv_weightedGram
    {row column : Nat} (hrow : row < 65) (hcolumn : column < 65) :
    cutoffTwoSectorPhysicalKernel row column ≈
      weightedGram (centralBoundaryChannels 2 0)
        (centralBoundaryWeight cutoffTwoHalfCoupling 2 0)
        (fun index boundary =>
          centralHalfAmplitude cutoffTwoHalfCoupling 2 0
            (cutoffTwoSectorStateAt index) boundary)
        row column := by
  change centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (cutoffTwoSectorStateAt row) (cutoffTwoSectorStateAt column) ≈
    weightedGram (centralBoundaryChannels 2 0)
      (centralBoundaryWeight cutoffTwoHalfCoupling 2 0)
      (fun index boundary =>
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          (cutoffTwoSectorStateAt index) boundary)
      row column
  exact centralPhysicalReflectedKernel_eq_weightedGram
    cutoffTwoHalfCoupling
    (cutoffTwoCubeSectorState_mem_halfStates
      (cutoffTwoSectorStateAt_mem hrow))
    (cutoffTwoCubeSectorState_mem_halfStates
      (cutoffTwoSectorStateAt_mem hcolumn))

/-- The indexed production quadratic is exactly a manifest finite weighted
Gram quadratic on the same 65 literal states. -/
theorem cutoffTwoSectorPhysicalMatrixQuadratic_eqv_weightedGram
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic 65 cutoffTwoSectorPhysicalKernel coefficient ≈
      weightedGramQuadratic (List.range 65)
        (centralBoundaryChannels 2 0)
        (centralBoundaryWeight cutoffTwoHalfCoupling 2 0)
        (fun index boundary =>
          centralHalfAmplitude cutoffTwoHalfCoupling 2 0
            (cutoffTwoSectorStateAt index) boundary)
        coefficient := by
  unfold finiteMatrixQuadratic weightedGramQuadratic
  apply listQSum_congr_on
  intro row hrow
  apply listQSum_congr_on
  intro column hcolumn
  exact Q'.mul_eqv_congr_left
    (coefficient row * coefficient column) _ _
    (cutoffTwoSectorPhysicalKernel_eqv_weightedGram
      (List.mem_range.mp hrow) (List.mem_range.mp hcolumn))

/-- Reflection positivity survives restriction to the exact 65-state
production sector: its quadratic form is nonnegative for every coefficient. -/
theorem cutoffTwoSectorPhysicalMatrixQuadratic_nonnegative
    (coefficient : Nat → Q') :
    (0 : Q') ≤
      finiteMatrixQuadratic 65 cutoffTwoSectorPhysicalKernel coefficient := by
  have hgram : (0 : Q') ≤
      weightedGramQuadratic (List.range 65)
        (centralBoundaryChannels 2 0)
        (centralBoundaryWeight cutoffTwoHalfCoupling 2 0)
        (fun index boundary =>
          centralHalfAmplitude cutoffTwoHalfCoupling 2 0
            (cutoffTwoSectorStateAt index) boundary)
        coefficient :=
    weightedGramQuadratic_nonnegative _ _ _ _ _
      (centralBoundaryWeight_nonnegative_on
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling))
  exact Q'.le_trans' _ _ _ hgram
    (Q'.ge_of_eqv
      (cutoffTwoSectorPhysicalMatrixQuadratic_eqv_weightedGram coefficient))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalUpperGap
