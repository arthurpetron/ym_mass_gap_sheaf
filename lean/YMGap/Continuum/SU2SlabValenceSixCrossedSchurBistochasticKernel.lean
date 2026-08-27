/-
# Bistochastic degree-six crossed slab recoupling

At an actual degree-six slab link, each crossed replica has the complete
all-source/all-final-target valence-six associator matrix.  Their Cartesian
tensor is therefore a complete crossed bistochastic kernel.  The production
fusion chains select one distinguished source, and every old dependent
three-step path maps to its canonical middle and final carriers.

The old path weight is one factorized three-block atom, not the finite sum
over common middle states defining the composed matrix entry.

Constructive contract: exact finite carriers and `Q'` algebra only; no
choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2SlabHigherValenceCrossedSchurCompiler
import YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock

namespace YMGap.Continuum.SU2SlabValenceSixCrossedSchurBistochasticKernel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2PhysicalSchurRecouplingKernel
open YMGap.Continuum.SU2SlabHigherValenceCrossedSchurCompiler
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.SU2ValenceFiveIteratedSchurTransport
open YMGap.Continuum.SU2ValenceSixIteratedSchurTransport
open YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock
open YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Actual crossed source and final-target carriers -/

abbrev CrossedValenceSixLeftMatrixSource {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 6) :=
  ValenceSixLeftCarrier
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 0)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 1)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 2)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 3)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 4)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 5)

abbrev CrossedValenceSixRightMatrixSource {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 6) :=
  ValenceSixLeftCarrier
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 0)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 1)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 2)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 3)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 4)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 5)

abbrev CrossedValenceSixMatrixSource {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 6) :=
  CrossedValenceSixLeftMatrixSource D ×
    CrossedValenceSixRightMatrixSource D

abbrev CrossedValenceSixLeftMatrixTarget {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 6) :=
  ValenceSixRightCarrier
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 0)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 1)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 2)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 3)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 4)
    ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 5)

abbrev CrossedValenceSixRightMatrixTarget {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 6) :=
  ValenceSixRightCarrier
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 0)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 1)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 2)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 3)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 4)
    ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 5)

abbrev CrossedValenceSixMatrixTarget {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 6) :=
  CrossedValenceSixLeftMatrixTarget D ×
    CrossedValenceSixRightMatrixTarget D

/-! ## 2. The full crossed matrix and its production source -/

def crossedValenceSixBistochasticKernel {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 6) :
    FiniteBistochasticQKernel
      (CrossedValenceSixMatrixSource D)
      (CrossedValenceSixMatrixTarget D) :=
  tensor
    (valenceSixBistochasticKernel
      ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 0)
      ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 1)
      ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 2)
      ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 3)
      ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 4)
      ((slabLinkExternalSpins extent (higherCrossedLeftPhysical D) D.link) 5))
    (valenceSixBistochasticKernel
      ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 0)
      ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 1)
      ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 2)
      ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 3)
      ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 4)
      ((slabLinkExternalSpins extent (higherCrossedRightPhysical D) D.link) 5))

def crossedValenceSixProductionSource {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 6) :
    CrossedValenceSixMatrixSource D :=
  (valenceSixLeftCarrierOfChain (crossedValenceSixLeftChain D),
    valenceSixLeftCarrierOfChain (crossedValenceSixRightChain D))

theorem crossedValenceSixBistochasticKernel_column_normalized
    {K extent : Nat} (D : CrossedSlabSwitchData K extent 6)
    (target : CrossedValenceSixMatrixTarget D) :
    listQSum
      (fun source =>
        (crossedValenceSixBistochasticKernel D).weight source target)
      (crossedValenceSixBistochasticKernel D).sources ≈ 1 :=
  (crossedValenceSixBistochasticKernel D).column_normalized target

theorem crossedValenceSixProductionSource_row_normalized
    {K extent : Nat} (D : CrossedSlabSwitchData K extent 6) :
    listQSum
      ((crossedValenceSixBistochasticKernel D).weight
        (crossedValenceSixProductionSource D))
      (crossedValenceSixBistochasticKernel D).targets ≈ 1 :=
  (crossedValenceSixBistochasticKernel D).row_normalized
    (crossedValenceSixProductionSource D)

/-! ## 3. Exact map from the old dependent path carrier -/

def crossedValenceSixFinalTargetOfPath {K extent : Nat}
    {D : CrossedSlabSwitchData K extent 6}
    (target : CrossedValenceSixTarget D) :
    CrossedValenceSixMatrixTarget D :=
  (valenceSixRightCarrierOfPath target.1,
    valenceSixRightCarrierOfPath target.2)

private abbrev valenceFivePrefixOf {a b c d e f : Nat}
    (chain : FixedLeftCGValenceSix a b c d e f) :=
  YMGap.Continuum.SU2ValenceSixIteratedSchurTransport.FixedLeftCGValenceSix.valenceFivePrefix
    chain

private theorem valenceSixThreeBlockAtom_path {a b c d e f : Nat}
    (chain : FixedLeftCGValenceSix a b c d e f)
    (target : ValenceSixRightTreeTarget chain) :
    (valenceFiveFirstBlockKernelAt
        (valenceFiveLeftCarrierOfChain (valenceFivePrefixOf chain))
        (valenceFiveMiddleCarrierOfPath (valenceFivePrefixOf chain) target.prior)
        rfl *
      valenceFiveSecondBlockKernelAt
        (valenceFiveMiddleCarrierOfPath (valenceFivePrefixOf chain) target.prior)
        (valenceFiveRightCarrierOfPath target.prior) rfl) *
      valenceSixThirdKernelAt
        (valenceSixCommonMiddleOfPath chain target)
        (valenceSixRightCarrierOfPath target) ≈
      valenceSixIteratedSchurKernelAt chain target := by
  refine Q'.eqv_trans _
    (valenceFiveIteratedSchurKernelAt (valenceFivePrefixOf chain) target.prior *
      valenceSixThirdKernelAt
        (valenceSixCommonMiddleOfPath chain target)
        (valenceSixRightCarrierOfPath target)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (valenceFiveIteratedSchurKernelAt_common_path
        (valenceFivePrefixOf chain) target.prior)
  · exact Q'.eqv_trans _
      (valenceFiveIteratedSchurKernelAt (valenceFivePrefixOf chain) target.prior *
        physicalSchurRecouplingKernelAt
          (valenceSixThirdLeftChannel chain target.prior) target.third) _
      (Q'.mul_eqv_congr_left _ _ _
        (valenceSixThirdKernelAt_path chain target))
      (Q'.eqv_refl _)

/-- Each old crossed degree-six path weight is exactly the product of the six
local block atoms through its two canonical three-step paths. -/
theorem crossedValenceSixKernelAt_common_paths {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 6)
    (target : CrossedValenceSixTarget D) :
    (((valenceFiveFirstBlockKernelAt
          (valenceFiveLeftCarrierOfChain
            (valenceFivePrefixOf (crossedValenceSixLeftChain D)))
          (valenceFiveMiddleCarrierOfPath
            (valenceFivePrefixOf (crossedValenceSixLeftChain D))
            target.1.prior) rfl *
        valenceFiveSecondBlockKernelAt
          (valenceFiveMiddleCarrierOfPath
            (valenceFivePrefixOf (crossedValenceSixLeftChain D))
            target.1.prior)
          (valenceFiveRightCarrierOfPath target.1.prior) rfl) *
        valenceSixThirdKernelAt
          (valenceSixCommonMiddleOfPath
            (crossedValenceSixLeftChain D) target.1)
          (valenceSixRightCarrierOfPath target.1)) *
      ((valenceFiveFirstBlockKernelAt
          (valenceFiveLeftCarrierOfChain
            (valenceFivePrefixOf (crossedValenceSixRightChain D)))
          (valenceFiveMiddleCarrierOfPath
            (valenceFivePrefixOf (crossedValenceSixRightChain D))
            target.2.prior) rfl *
        valenceFiveSecondBlockKernelAt
          (valenceFiveMiddleCarrierOfPath
            (valenceFivePrefixOf (crossedValenceSixRightChain D))
            target.2.prior)
          (valenceFiveRightCarrierOfPath target.2.prior) rfl) *
        valenceSixThirdKernelAt
          (valenceSixCommonMiddleOfPath
            (crossedValenceSixRightChain D) target.2)
          (valenceSixRightCarrierOfPath target.2))) ≈
      crossedValenceSixKernelAt D target := by
  refine Q'.eqv_trans _
    (valenceSixIteratedSchurKernelAt
        (crossedValenceSixLeftChain D) target.1 *
      ((valenceFiveFirstBlockKernelAt
          (valenceFiveLeftCarrierOfChain
            (valenceFivePrefixOf (crossedValenceSixRightChain D)))
          (valenceFiveMiddleCarrierOfPath
            (valenceFivePrefixOf (crossedValenceSixRightChain D))
            target.2.prior) rfl *
        valenceFiveSecondBlockKernelAt
          (valenceFiveMiddleCarrierOfPath
            (valenceFivePrefixOf (crossedValenceSixRightChain D))
            target.2.prior)
          (valenceFiveRightCarrierOfPath target.2.prior) rfl) *
        valenceSixThirdKernelAt
          (valenceSixCommonMiddleOfPath
            (crossedValenceSixRightChain D) target.2)
          (valenceSixRightCarrierOfPath target.2))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (valenceSixThreeBlockAtom_path
        (crossedValenceSixLeftChain D) target.1)
  · exact Q'.mul_eqv_congr_left _ _ _
      (valenceSixThreeBlockAtom_path
        (crossedValenceSixRightChain D) target.2)

end YMGap.Continuum.SU2SlabValenceSixCrossedSchurBistochasticKernel

#print axioms YMGap.Continuum.SU2SlabValenceSixCrossedSchurBistochasticKernel.crossedValenceSixBistochasticKernel
#print axioms YMGap.Continuum.SU2SlabValenceSixCrossedSchurBistochasticKernel.crossedValenceSixProductionSource
#print axioms YMGap.Continuum.SU2SlabValenceSixCrossedSchurBistochasticKernel.crossedValenceSixBistochasticKernel_column_normalized
#print axioms YMGap.Continuum.SU2SlabValenceSixCrossedSchurBistochasticKernel.crossedValenceSixProductionSource_row_normalized
#print axioms YMGap.Continuum.SU2SlabValenceSixCrossedSchurBistochasticKernel.crossedValenceSixFinalTargetOfPath
#print axioms YMGap.Continuum.SU2SlabValenceSixCrossedSchurBistochasticKernel.crossedValenceSixKernelAt_common_paths
