/-
# Raw SU(2) ratio for the physical BF4 new-tail self-return trace

The centered-tail compiler reduces its analytic input to a sum of physical
self-return probabilities.  This module cancels the common slab-partition
normalization from every such probability.  On a genuine vacuum-sector state,
the return is exactly

    raw reflected diagonal(state)
    ---------------------------------- .
    raw positive-carrier row mass(state)

Summing this identity over the new block presents the remaining tail estimate
entirely in terms of unnormalized finite SU(2) state sums.  This is the right
boundary for either an analytic high-spin envelope or exact certificate data:
external code may generate data, but Lean checks the displayed rational ratios
and their sum.

No cutoff-uniform bound, thermodynamic limit, continuum theory, or Clay result
is asserted.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredTailTrace

namespace YMGap.Continuum.BF4PhysicalVacuumSectorNewTailSelfReturnRawRatio

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredTailTrace
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- The unnormalized diagonal/row ratio, totalized by zero away from the
canonical vacuum component. -/
def centralPhysicalFiniteVacuumSectorRawSelfReturnRatio
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half index : Nat) : Q' :=
  if hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half then
    let state := centralPhysicalFiniteStateAt w hw cutoff half index
    let hpositive := centralPhysicalFiniteStateAt_mem_positive
      w hw cutoff half
      (centralPhysicalFiniteVacuumSectorIndex_lt
        w hw cutoff half hindex)
    Q'.divPos
      (centralPhysicalReflectedKernel w cutoff half state state)
      (centralPhysicalPositiveRawRowMass w hw cutoff half state)
      (centralPhysicalPositiveRawRowMass_pos hpositive)
  else 0

/-- Exact cancellation of the common partition reciprocal identifies every
physical self-return probability with its raw diagonal/row ratio. -/
theorem centralPhysicalFiniteVacuumSectorSelfReturnProbability_eqv_rawRatio
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half index : Nat}
    (hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorSelfReturnProbability
        w hw cutoff half index ≈
      centralPhysicalFiniteVacuumSectorRawSelfReturnRatio
        w hw cutoff half index := by
  let state := centralPhysicalFiniteStateAt w hw cutoff half index
  let hpositive := centralPhysicalFiniteStateAt_mem_positive
    w hw cutoff half
    (centralPhysicalFiniteVacuumSectorIndex_lt
      w hw cutoff half hindex)
  unfold centralPhysicalFiniteVacuumSectorSelfReturnProbability
    centralPhysicalFiniteVacuumSectorRawSelfReturnRatio
  rw [dif_pos hindex, dif_pos hindex]
  simpa only [centralPhysicalFiniteKernel, centralPhysicalFiniteWeight]
    using
      (centralNormalizedPhysicalReturn_eqv_rawRatio
        hpositive state)

/-- Sum of unnormalized physical diagonal/row ratios over the genuinely new
vacuum-sector block. -/
def centralPhysicalFiniteVacuumSectorExactNewTailRawSelfReturnTrace
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Q' :=
  listQSum
    (centralPhysicalFiniteVacuumSectorRawSelfReturnRatio
      w hw later half)
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      w hw base later half)

/-- The normalized physical self-return trace is exactly the finite sum of
unnormalized SU(2) diagonal/row ratios. -/
theorem centralPhysicalFiniteVacuumSectorExactNewTailSelfReturnTrace_eqv_rawRatioTrace
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    centralPhysicalFiniteVacuumSectorExactNewTailSelfReturnTrace
        w hw base later half ≈
      centralPhysicalFiniteVacuumSectorExactNewTailRawSelfReturnTrace
        w hw base later half := by
  unfold centralPhysicalFiniteVacuumSectorExactNewTailSelfReturnTrace
    centralPhysicalFiniteVacuumSectorExactNewTailRawSelfReturnTrace
  apply listQSum_congr_on
  intro index hindex
  exact centralPhysicalFiniteVacuumSectorSelfReturnProbability_eqv_rawRatio
    (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp hindex).1

/-- A bound on the raw SU(2) diagonal/row trace is already the tail input
required by the same-object strict-gap compiler. -/
theorem centralPhysicalFiniteVacuumSectorExactNewTailSelfReturnTrace_le_of_rawRatioTrace
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (tau : Q')
    (hraw :
      centralPhysicalFiniteVacuumSectorExactNewTailRawSelfReturnTrace
        w hw base later half ≤ tau) :
    centralPhysicalFiniteVacuumSectorExactNewTailSelfReturnTrace
        w hw base later half ≤ tau :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (centralPhysicalFiniteVacuumSectorExactNewTailSelfReturnTrace_eqv_rawRatioTrace
        w hw base later half))
    hraw

end YMGap.Continuum.BF4PhysicalVacuumSectorNewTailSelfReturnRawRatio

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorNewTailSelfReturnRawRatio.centralPhysicalFiniteVacuumSectorSelfReturnProbability_eqv_rawRatio
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorNewTailSelfReturnRawRatio.centralPhysicalFiniteVacuumSectorExactNewTailSelfReturnTrace_eqv_rawRatioTrace
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorNewTailSelfReturnRawRatio.centralPhysicalFiniteVacuumSectorExactNewTailSelfReturnTrace_le_of_rawRatioTrace
