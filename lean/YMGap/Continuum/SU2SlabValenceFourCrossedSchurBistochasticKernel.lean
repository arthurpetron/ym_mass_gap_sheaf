/-
# Bistochastic degree-four crossed slab recoupling

The production degree-four switch supplies one distinguished source row in
each replica.  The physical associator actually gives a matrix on every
canonical left source at those same external labels.  Taking the exact
Cartesian tensor product exposes the full crossed bistochastic kernel and
recovers the pre-existing production row by specialization.

This remains a recoupling kernel, not a Gibbs conditional law or OS transfer
operator.

Constructive contract: exact finite carriers and `Q'` algebra only; no
choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.FiniteBistochasticQKernelComposition
import YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
import YMGap.Continuum.SU2SlabValenceFourCrossedSchurCompiler

namespace YMGap.Continuum.SU2SlabValenceFourCrossedSchurBistochasticKernel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
open YMGap.Continuum.SU2SlabValenceFourCrossedSchurCompiler
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-- Canonical left-channel source type for the first crossed replica. -/
abbrev CrossedLeftSchurSource {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :=
  FixedLeftCGChannel
    ((slabLinkExternalSpins extent (crossedLeftPhysical D) D.link) 0)
    ((slabLinkExternalSpins extent (crossedLeftPhysical D) D.link) 1)
    ((slabLinkExternalSpins extent (crossedLeftPhysical D) D.link) 2)
    ((slabLinkExternalSpins extent (crossedLeftPhysical D) D.link) 3)

/-- Canonical left-channel source type for the second crossed replica. -/
abbrev CrossedRightSchurSource {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :=
  FixedLeftCGChannel
    ((slabLinkExternalSpins extent (crossedRightPhysical D) D.link) 0)
    ((slabLinkExternalSpins extent (crossedRightPhysical D) D.link) 1)
    ((slabLinkExternalSpins extent (crossedRightPhysical D) D.link) 2)
    ((slabLinkExternalSpins extent (crossedRightPhysical D) D.link) 3)

abbrev CrossedSchurSource {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :=
  CrossedLeftSchurSource D × CrossedRightSchurSource D

/-- Full two-replica physical associator matrix at the actual crossed
external labels of a production degree-four link. -/
def crossedSchurBistochasticKernel {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :
    FiniteBistochasticQKernel (CrossedSchurSource D) (CrossedSchurTarget D) :=
  tensor
    (physicalSchurBistochasticKernel
      ((slabLinkExternalSpins extent (crossedLeftPhysical D) D.link) 0)
      ((slabLinkExternalSpins extent (crossedLeftPhysical D) D.link) 1)
      ((slabLinkExternalSpins extent (crossedLeftPhysical D) D.link) 2)
      ((slabLinkExternalSpins extent (crossedLeftPhysical D) D.link) 3))
    (physicalSchurBistochasticKernel
      ((slabLinkExternalSpins extent (crossedRightPhysical D) D.link) 0)
      ((slabLinkExternalSpins extent (crossedRightPhysical D) D.link) 1)
      ((slabLinkExternalSpins extent (crossedRightPhysical D) D.link) 2)
      ((slabLinkExternalSpins extent (crossedRightPhysical D) D.link) 3))

/-- The target carrier of the full matrix is definitionally the target list
used by the existing production-row compiler. -/
theorem crossedSchurBistochasticKernel_targets {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent) :
    (crossedSchurBistochasticKernel D).targets = crossedSchurTargets D := by
  simp only [crossedSchurBistochasticKernel, tensor,
    physicalSchurBistochasticKernel, crossedSchurTargets,
    YMGap.Continuum.SU2PhysicalSchurHeterogeneousTwoReplicaTransport.heterogeneousSchurTargets,
    YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport.physicalSchurRightTargets]

/-- The distinguished production row is exactly the row previously exposed
by `crossedSchurKernelAt`. -/
theorem crossedSchurBistochasticKernel_production_row {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent)
    (target : CrossedSchurTarget D) :
    (crossedSchurBistochasticKernel D).weight
        (crossedLeftChannel D, crossedRightChannel D) target ≈
      crossedSchurKernelAt D target := by
  exact Q'.eqv_refl _

/-- **Every target column of the actual degree-four crossed recoupling
matrix has exact mass one over the explicit pair of canonical sources.** -/
theorem crossedSchurBistochasticKernel_column_normalized
    {K extent : Nat} (D : ValenceFourCrossReplicaSwitchData K extent)
    (target : CrossedSchurTarget D) :
    listQSum
      (fun source => (crossedSchurBistochasticKernel D).weight source target)
      (crossedSchurBistochasticKernel D).sources ≈ 1 :=
  (crossedSchurBistochasticKernel D).column_normalized target

end YMGap.Continuum.SU2SlabValenceFourCrossedSchurBistochasticKernel

#print axioms YMGap.Continuum.SU2SlabValenceFourCrossedSchurBistochasticKernel.crossedSchurBistochasticKernel
#print axioms YMGap.Continuum.SU2SlabValenceFourCrossedSchurBistochasticKernel.crossedSchurBistochasticKernel_targets
#print axioms YMGap.Continuum.SU2SlabValenceFourCrossedSchurBistochasticKernel.crossedSchurBistochasticKernel_production_row
#print axioms YMGap.Continuum.SU2SlabValenceFourCrossedSchurBistochasticKernel.crossedSchurBistochasticKernel_column_normalized
