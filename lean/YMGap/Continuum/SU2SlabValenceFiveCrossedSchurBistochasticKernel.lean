/-
# Bistochastic degree-five crossed slab recoupling

At an actual degree-five slab link, each crossed replica has a complete
all-source/all-final-target valence-five associator matrix.  Their Cartesian
tensor is therefore a complete crossed bistochastic kernel.  The existing
production chain supplies one distinguished source, while every old
dependent path maps to a canonical common-middle point and final target.

The old path weight is one factorized matrix-product atom, not the already
summed final matrix entry.  This distinction is kept explicit.

Constructive contract: exact finite carriers and `Q'` algebra only; no
choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2SlabHigherValenceCrossedSchurCompiler
import YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock

namespace YMGap.Continuum.SU2SlabValenceFiveCrossedSchurBistochasticKernel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2SlabHigherValenceCrossedSchurCompiler
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.SU2ValenceFiveIteratedSchurTransport
open YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Actual crossed source and final-target carriers -/

abbrev CrossedValenceFiveLeftMatrixSource {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 5) :=
  ValenceFiveLeftCarrier
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 0)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 1)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 2)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 3)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 4)

abbrev CrossedValenceFiveRightMatrixSource {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 5) :=
  ValenceFiveLeftCarrier
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 0)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 1)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 2)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 3)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 4)

abbrev CrossedValenceFiveMatrixSource {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 5) :=
  CrossedValenceFiveLeftMatrixSource D ×
    CrossedValenceFiveRightMatrixSource D

abbrev CrossedValenceFiveLeftMatrixTarget {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 5) :=
  ValenceFiveRightCarrier
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 0)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 1)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 2)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 3)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 4)

abbrev CrossedValenceFiveRightMatrixTarget {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 5) :=
  ValenceFiveRightCarrier
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 0)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 1)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 2)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 3)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 4)

abbrev CrossedValenceFiveMatrixTarget {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 5) :=
  CrossedValenceFiveLeftMatrixTarget D ×
    CrossedValenceFiveRightMatrixTarget D

/-! ## 2. The full crossed matrix and its production source -/

def crossedValenceFiveBistochasticKernel {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 5) :
    FiniteBistochasticQKernel
      (CrossedValenceFiveMatrixSource D)
      (CrossedValenceFiveMatrixTarget D) :=
  tensor
    (valenceFiveBistochasticKernel
      ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 0)
      ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 1)
      ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 2)
      ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 3)
      ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 4))
    (valenceFiveBistochasticKernel
      ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 0)
      ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 1)
      ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 2)
      ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 3)
      ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 4))

def crossedValenceFiveProductionSource {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 5) :
    CrossedValenceFiveMatrixSource D :=
  (valenceFiveLeftCarrierOfChain (crossedValenceFiveLeftChain D),
    valenceFiveLeftCarrierOfChain (crossedValenceFiveRightChain D))

theorem crossedValenceFiveBistochasticKernel_column_normalized
    {K extent : Nat} (D : CrossedSlabSwitchData K extent 5)
    (target : CrossedValenceFiveMatrixTarget D) :
    listQSum
      (fun source =>
        (crossedValenceFiveBistochasticKernel D).weight source target)
      (crossedValenceFiveBistochasticKernel D).sources ≈ 1 :=
  (crossedValenceFiveBistochasticKernel D).column_normalized target

theorem crossedValenceFiveProductionSource_row_normalized
    {K extent : Nat} (D : CrossedSlabSwitchData K extent 5) :
    listQSum
      ((crossedValenceFiveBistochasticKernel D).weight
        (crossedValenceFiveProductionSource D))
      (crossedValenceFiveBistochasticKernel D).targets ≈ 1 :=
  (crossedValenceFiveBistochasticKernel D).row_normalized
    (crossedValenceFiveProductionSource D)

/-! ## 3. Exact map from the old dependent path carrier -/

def crossedValenceFiveFinalTargetOfPath {K extent : Nat}
    {D : CrossedSlabSwitchData K extent 5}
    (target : CrossedValenceFiveTarget D) :
    CrossedValenceFiveMatrixTarget D :=
  (valenceFiveRightCarrierOfPath target.1,
    valenceFiveRightCarrierOfPath target.2)

/-- Each old crossed path weight is exactly the product of the two local
matrix-product atoms through its canonical common middle points. -/
theorem crossedValenceFiveKernelAt_common_paths {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 5)
    (target : CrossedValenceFiveTarget D) :
    (valenceFiveFirstBlockKernelAt
        (valenceFiveLeftCarrierOfChain (crossedValenceFiveLeftChain D))
        (valenceFiveMiddleCarrierOfPath
          (crossedValenceFiveLeftChain D) target.1) rfl *
      valenceFiveSecondBlockKernelAt
        (valenceFiveMiddleCarrierOfPath
          (crossedValenceFiveLeftChain D) target.1)
        (valenceFiveRightCarrierOfPath target.1) rfl) *
    (valenceFiveFirstBlockKernelAt
        (valenceFiveLeftCarrierOfChain (crossedValenceFiveRightChain D))
        (valenceFiveMiddleCarrierOfPath
          (crossedValenceFiveRightChain D) target.2) rfl *
      valenceFiveSecondBlockKernelAt
        (valenceFiveMiddleCarrierOfPath
          (crossedValenceFiveRightChain D) target.2)
        (valenceFiveRightCarrierOfPath target.2) rfl) ≈
      crossedValenceFiveKernelAt D target := by
  refine Q'.eqv_trans _
    (valenceFiveIteratedSchurKernelAt
        (crossedValenceFiveLeftChain D) target.1 *
      (valenceFiveFirstBlockKernelAt
          (valenceFiveLeftCarrierOfChain (crossedValenceFiveRightChain D))
          (valenceFiveMiddleCarrierOfPath
            (crossedValenceFiveRightChain D) target.2) rfl *
        valenceFiveSecondBlockKernelAt
          (valenceFiveMiddleCarrierOfPath
            (crossedValenceFiveRightChain D) target.2)
          (valenceFiveRightCarrierOfPath target.2) rfl)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (valenceFiveIteratedSchurKernelAt_common_path
        (crossedValenceFiveLeftChain D) target.1)
  · exact Q'.mul_eqv_congr_left _ _ _
      (valenceFiveIteratedSchurKernelAt_common_path
        (crossedValenceFiveRightChain D) target.2)

end YMGap.Continuum.SU2SlabValenceFiveCrossedSchurBistochasticKernel

#print axioms YMGap.Continuum.SU2SlabValenceFiveCrossedSchurBistochasticKernel.crossedValenceFiveBistochasticKernel
#print axioms YMGap.Continuum.SU2SlabValenceFiveCrossedSchurBistochasticKernel.crossedValenceFiveProductionSource
#print axioms YMGap.Continuum.SU2SlabValenceFiveCrossedSchurBistochasticKernel.crossedValenceFiveBistochasticKernel_column_normalized
#print axioms YMGap.Continuum.SU2SlabValenceFiveCrossedSchurBistochasticKernel.crossedValenceFiveProductionSource_row_normalized
#print axioms YMGap.Continuum.SU2SlabValenceFiveCrossedSchurBistochasticKernel.crossedValenceFiveFinalTargetOfPath
#print axioms YMGap.Continuum.SU2SlabValenceFiveCrossedSchurBistochasticKernel.crossedValenceFiveKernelAt_common_paths
