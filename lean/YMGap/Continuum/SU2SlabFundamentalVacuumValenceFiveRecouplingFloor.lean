/-
# The fundamental-vacuum floor at a production valence-five slab link

The concrete seven-cube switching pivot has external word `(1,1,1,1,0)`
in one physical replica and the vacuum word in the other.  The first
one-replica valence-five kernel has the sharp `1/4` floor, while the vacuum
kernel is deterministic.  Their exact tensor-product production coordinate
therefore retains the same `1/4` floor.

This closes the local representation-theoretic weight at the actual ambient
valence of the selected pivot.  It does not choose a target column or prove
that the chosen recoupling disconnects the global strand component.

Constructive contract: dependent-label specialization of proved finite SU(2)
kernels and exact rational order only; no choice principle, unchecked
existence claim, or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2FundamentalVacuumValenceFiveKernelFloor
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel

namespace YMGap.Continuum.SU2SlabFundamentalVacuumValenceFiveRecouplingFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2FundamentalVacuumValenceFiveKernelFloor
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Tensor the nontrivial and deterministic blocks -/

theorem fundamentalVacuum_twoReplicaValenceFiveKernel_floor
    (source : ValenceFiveLeftCarrier 1 1 1 1 0 ×
      ValenceFiveLeftCarrier 0 0 0 0 0)
    (target : ValenceFiveRightCarrier 1 1 1 1 0 ×
      ValenceFiveRightCarrier 0 0 0 0 0) :
    oneQuarter ≤
      tensorWeight
        (valenceFiveBistochasticKernel 1 1 1 1 0)
        (valenceFiveBistochasticKernel 0 0 0 0 0)
        source target := by
  have hfundamental := fundamentalVacuumValenceFiveKernel_oneQuarter_le
    source.1 target.1
  have hvacuum := zeroValenceFiveKernel_eqv_one source.2 target.2
  have hproduct :
      (valenceFiveBistochasticKernel 1 1 1 1 0).weight
          source.1 target.1 *
          (valenceFiveBistochasticKernel 0 0 0 0 0).weight
            source.2 target.2 ≈
        (valenceFiveBistochasticKernel 1 1 1 1 0).weight
          source.1 target.1 :=
    Q'.eqv_trans _
      ((valenceFiveBistochasticKernel 1 1 1 1 0).weight
        source.1 target.1 * 1) _
      (Q'.mul_eqv_congr_left
        ((valenceFiveBistochasticKernel 1 1 1 1 0).weight
          source.1 target.1)
        ((valenceFiveBistochasticKernel 0 0 0 0 0).weight
          source.2 target.2) 1 hvacuum)
      (Q'.mul_one_eqv _)
  exact Q'.le_trans' _ _ _ hfundamental (Q'.ge_of_eqv hproduct)

/-! ## 2. Dependent-label specialization -/

theorem twoReplicaValenceFiveKernel_floor_of_left_fundamental_vacuum
    (left0 left1 left2 left3 left4
      right0 right1 right2 right3 right4 : Nat)
    (hleft0 : left0 = 1) (hleft1 : left1 = 1)
    (hleft2 : left2 = 1) (hleft3 : left3 = 1)
    (hleft4 : left4 = 0)
    (hright0 : right0 = 0) (hright1 : right1 = 0)
    (hright2 : right2 = 0) (hright3 : right3 = 0)
    (hright4 : right4 = 0)
    (source : ValenceFiveLeftCarrier left0 left1 left2 left3 left4 ×
      ValenceFiveLeftCarrier right0 right1 right2 right3 right4)
    (target : ValenceFiveRightCarrier left0 left1 left2 left3 left4 ×
      ValenceFiveRightCarrier right0 right1 right2 right3 right4) :
    oneQuarter ≤
      tensorWeight
        (valenceFiveBistochasticKernel left0 left1 left2 left3 left4)
        (valenceFiveBistochasticKernel right0 right1 right2 right3 right4)
        source target := by
  subst left0
  subst left1
  subst left2
  subst left3
  subst left4
  subst right0
  subst right1
  subst right2
  subst right3
  subst right4
  exact fundamentalVacuum_twoReplicaValenceFiveKernel_floor source target

/-! ## 3. The production slab-link package -/

theorem slabPhysicalPairRecouplingKernelPackageFive_fundamentalVacuum_floor
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 5)
    (hleft0 : (slabLinkExternalSpins extent D.leftPhysical D.link) 0 = 1)
    (hleft1 : (slabLinkExternalSpins extent D.leftPhysical D.link) 1 = 1)
    (hleft2 : (slabLinkExternalSpins extent D.leftPhysical D.link) 2 = 1)
    (hleft3 : (slabLinkExternalSpins extent D.leftPhysical D.link) 3 = 1)
    (hleft4 : (slabLinkExternalSpins extent D.leftPhysical D.link) 4 = 0)
    (hright0 : (slabLinkExternalSpins extent D.rightPhysical D.link) 0 = 0)
    (hright1 : (slabLinkExternalSpins extent D.rightPhysical D.link) 1 = 0)
    (hright2 : (slabLinkExternalSpins extent D.rightPhysical D.link) 2 = 0)
    (hright3 : (slabLinkExternalSpins extent D.rightPhysical D.link) 3 = 0)
    (hright4 : (slabLinkExternalSpins extent D.rightPhysical D.link) 4 = 0)
    (source : (slabPhysicalPairRecouplingKernelPackageFive D).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFive D).Target) :
    oneQuarter ≤
      (slabPhysicalPairRecouplingKernelPackageFive D).kernel.weight
        source target := by
  change
    tensorWeight
      (valenceFiveBistochasticKernel
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 3)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 4))
      (valenceFiveBistochasticKernel
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 4))
      source target ≥ oneQuarter
  exact twoReplicaValenceFiveKernel_floor_of_left_fundamental_vacuum
    ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
    ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
    ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
    ((slabLinkExternalSpins extent D.leftPhysical D.link) 3)
    ((slabLinkExternalSpins extent D.leftPhysical D.link) 4)
    ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
    ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
    ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
    ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)
    ((slabLinkExternalSpins extent D.rightPhysical D.link) 4)
    hleft0 hleft1 hleft2 hleft3 hleft4
    hright0 hright1 hright2 hright3 hright4 source target

theorem slabPhysicalPairRecouplingKernelPackageFive_fundamentalVacuum_pos
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 5)
    (hleft0 : (slabLinkExternalSpins extent D.leftPhysical D.link) 0 = 1)
    (hleft1 : (slabLinkExternalSpins extent D.leftPhysical D.link) 1 = 1)
    (hleft2 : (slabLinkExternalSpins extent D.leftPhysical D.link) 2 = 1)
    (hleft3 : (slabLinkExternalSpins extent D.leftPhysical D.link) 3 = 1)
    (hleft4 : (slabLinkExternalSpins extent D.leftPhysical D.link) 4 = 0)
    (hright0 : (slabLinkExternalSpins extent D.rightPhysical D.link) 0 = 0)
    (hright1 : (slabLinkExternalSpins extent D.rightPhysical D.link) 1 = 0)
    (hright2 : (slabLinkExternalSpins extent D.rightPhysical D.link) 2 = 0)
    (hright3 : (slabLinkExternalSpins extent D.rightPhysical D.link) 3 = 0)
    (hright4 : (slabLinkExternalSpins extent D.rightPhysical D.link) 4 = 0)
    (source : (slabPhysicalPairRecouplingKernelPackageFive D).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFive D).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingKernelPackageFive D).kernel.weight
        source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < oneQuarter)
    (slabPhysicalPairRecouplingKernelPackageFive_fundamentalVacuum_floor D
      hleft0 hleft1 hleft2 hleft3 hleft4
      hright0 hright1 hright2 hright3 hright4 source target)

end YMGap.Continuum.SU2SlabFundamentalVacuumValenceFiveRecouplingFloor

#print axioms YMGap.Continuum.SU2SlabFundamentalVacuumValenceFiveRecouplingFloor.fundamentalVacuum_twoReplicaValenceFiveKernel_floor
#print axioms YMGap.Continuum.SU2SlabFundamentalVacuumValenceFiveRecouplingFloor.twoReplicaValenceFiveKernel_floor_of_left_fundamental_vacuum
#print axioms YMGap.Continuum.SU2SlabFundamentalVacuumValenceFiveRecouplingFloor.slabPhysicalPairRecouplingKernelPackageFive_fundamentalVacuum_floor
#print axioms YMGap.Continuum.SU2SlabFundamentalVacuumValenceFiveRecouplingFloor.slabPhysicalPairRecouplingKernelPackageFive_fundamentalVacuum_pos
