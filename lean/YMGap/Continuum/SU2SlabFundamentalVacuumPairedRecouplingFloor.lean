/-
# The fundamental-vacuum floor inside an actual slab-link package

At a genuine valence-four corrected-slab link, suppose one physical replica
has four fundamental external doubled-spin labels and the other has four
vacuum labels.  The exact production package is then the tensor product of
the nontrivial fundamental Schur block and the deterministic vacuum block.
Every local source-target coordinate is therefore at least `1/4` and is
strictly positive.  The same result holds after interchanging the replicas.

This closes the local representation-theoretic coordinate expected at the
pivot of a one-replica switching surface.  It does not construct that surface
or prove global strand disconnection.

Constructive contract: definitional specialization of the production slab
kernel and the proved fundamental-vacuum floor only; no `Classical`, choice,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.SU2FundamentalVacuumPhysicalSchurKernelFloor
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel

namespace YMGap.Continuum.SU2SlabFundamentalVacuumPairedRecouplingFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FundamentalVacuumPhysicalSchurKernelFloor
open YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates

/-! ## 1. Dependent-label specialization -/

theorem twoReplicaSchurKernel_floor_of_left_one_right_zero
    (left0 left1 left2 left3 right0 right1 right2 right3 : Nat)
    (hleft0 : left0 = 1) (hleft1 : left1 = 1)
    (hleft2 : left2 = 1) (hleft3 : left3 = 1)
    (hright0 : right0 = 0) (hright1 : right1 = 0)
    (hright2 : right2 = 0) (hright3 : right3 = 0)
    (source : FixedLeftCGChannel left0 left1 left2 left3 ×
      FixedLeftCGChannel right0 right1 right2 right3)
    (target : FixedRightCGChannel left0 left1 left2 left3 ×
      FixedRightCGChannel right0 right1 right2 right3) :
    oneQuarter ≤
      tensorWeight
        (physicalSchurBistochasticKernel left0 left1 left2 left3)
        (physicalSchurBistochasticKernel right0 right1 right2 right3)
        source target := by
  subst left0
  subst left1
  subst left2
  subst left3
  subst right0
  subst right1
  subst right2
  subst right3
  exact fundamental_vacuum_twoReplicaSchurKernel_floor source target

theorem twoReplicaSchurKernel_floor_of_left_zero_right_one
    (left0 left1 left2 left3 right0 right1 right2 right3 : Nat)
    (hleft0 : left0 = 0) (hleft1 : left1 = 0)
    (hleft2 : left2 = 0) (hleft3 : left3 = 0)
    (hright0 : right0 = 1) (hright1 : right1 = 1)
    (hright2 : right2 = 1) (hright3 : right3 = 1)
    (source : FixedLeftCGChannel left0 left1 left2 left3 ×
      FixedLeftCGChannel right0 right1 right2 right3)
    (target : FixedRightCGChannel left0 left1 left2 left3 ×
      FixedRightCGChannel right0 right1 right2 right3) :
    oneQuarter ≤
      tensorWeight
        (physicalSchurBistochasticKernel left0 left1 left2 left3)
        (physicalSchurBistochasticKernel right0 right1 right2 right3)
        source target := by
  subst left0
  subst left1
  subst left2
  subst left3
  subst right0
  subst right1
  subst right2
  subst right3
  exact vacuum_fundamental_twoReplicaSchurKernel_floor source target

/-! ## 2. The production valence-four package -/

theorem slabPhysicalPairRecouplingKernelPackageFour_fundamental_vacuum_floor
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 4)
    (hleft0 : (slabLinkExternalSpins extent D.leftPhysical D.link) 0 = 1)
    (hleft1 : (slabLinkExternalSpins extent D.leftPhysical D.link) 1 = 1)
    (hleft2 : (slabLinkExternalSpins extent D.leftPhysical D.link) 2 = 1)
    (hleft3 : (slabLinkExternalSpins extent D.leftPhysical D.link) 3 = 1)
    (hright0 : (slabLinkExternalSpins extent D.rightPhysical D.link) 0 = 0)
    (hright1 : (slabLinkExternalSpins extent D.rightPhysical D.link) 1 = 0)
    (hright2 : (slabLinkExternalSpins extent D.rightPhysical D.link) 2 = 0)
    (hright3 : (slabLinkExternalSpins extent D.rightPhysical D.link) 3 = 0)
    (source : (slabPhysicalPairRecouplingKernelPackageFour D).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFour D).Target) :
    oneQuarter ≤
      (slabPhysicalPairRecouplingKernelPackageFour D).kernel.weight
        source target := by
  change
    (FixedLeftCGChannel
          ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
          ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
          ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
          ((slabLinkExternalSpins extent D.leftPhysical D.link) 3) ×
        FixedLeftCGChannel
          ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
          ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
          ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
          ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)) at source
  change
    (FixedRightCGChannel
          ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
          ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
          ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
          ((slabLinkExternalSpins extent D.leftPhysical D.link) 3) ×
        FixedRightCGChannel
          ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
          ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
          ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
          ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)) at target
  change oneQuarter ≤
    tensorWeight
      (physicalSchurBistochasticKernel
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 3))
      (physicalSchurBistochasticKernel
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 3))
      source target
  exact twoReplicaSchurKernel_floor_of_left_one_right_zero
    ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
    ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
    ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
    ((slabLinkExternalSpins extent D.leftPhysical D.link) 3)
    ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
    ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
    ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
    ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)
    hleft0 hleft1 hleft2 hleft3
    hright0 hright1 hright2 hright3 source target

theorem slabPhysicalPairRecouplingKernelPackageFour_fundamental_vacuum_pos
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 4)
    (hleft0 : (slabLinkExternalSpins extent D.leftPhysical D.link) 0 = 1)
    (hleft1 : (slabLinkExternalSpins extent D.leftPhysical D.link) 1 = 1)
    (hleft2 : (slabLinkExternalSpins extent D.leftPhysical D.link) 2 = 1)
    (hleft3 : (slabLinkExternalSpins extent D.leftPhysical D.link) 3 = 1)
    (hright0 : (slabLinkExternalSpins extent D.rightPhysical D.link) 0 = 0)
    (hright1 : (slabLinkExternalSpins extent D.rightPhysical D.link) 1 = 0)
    (hright2 : (slabLinkExternalSpins extent D.rightPhysical D.link) 2 = 0)
    (hright3 : (slabLinkExternalSpins extent D.rightPhysical D.link) 3 = 0)
    (source : (slabPhysicalPairRecouplingKernelPackageFour D).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFour D).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingKernelPackageFour D).kernel.weight
        source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < oneQuarter)
    (slabPhysicalPairRecouplingKernelPackageFour_fundamental_vacuum_floor D
      hleft0 hleft1 hleft2 hleft3
      hright0 hright1 hright2 hright3 source target)

theorem slabPhysicalPairRecouplingKernelPackageFour_vacuum_fundamental_floor
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 4)
    (hleft0 : (slabLinkExternalSpins extent D.leftPhysical D.link) 0 = 0)
    (hleft1 : (slabLinkExternalSpins extent D.leftPhysical D.link) 1 = 0)
    (hleft2 : (slabLinkExternalSpins extent D.leftPhysical D.link) 2 = 0)
    (hleft3 : (slabLinkExternalSpins extent D.leftPhysical D.link) 3 = 0)
    (hright0 : (slabLinkExternalSpins extent D.rightPhysical D.link) 0 = 1)
    (hright1 : (slabLinkExternalSpins extent D.rightPhysical D.link) 1 = 1)
    (hright2 : (slabLinkExternalSpins extent D.rightPhysical D.link) 2 = 1)
    (hright3 : (slabLinkExternalSpins extent D.rightPhysical D.link) 3 = 1)
    (source : (slabPhysicalPairRecouplingKernelPackageFour D).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFour D).Target) :
    oneQuarter ≤
      (slabPhysicalPairRecouplingKernelPackageFour D).kernel.weight
        source target := by
  change
    (FixedLeftCGChannel
          ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
          ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
          ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
          ((slabLinkExternalSpins extent D.leftPhysical D.link) 3) ×
        FixedLeftCGChannel
          ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
          ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
          ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
          ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)) at source
  change
    (FixedRightCGChannel
          ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
          ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
          ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
          ((slabLinkExternalSpins extent D.leftPhysical D.link) 3) ×
        FixedRightCGChannel
          ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
          ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
          ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
          ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)) at target
  change oneQuarter ≤
    tensorWeight
      (physicalSchurBistochasticKernel
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 3))
      (physicalSchurBistochasticKernel
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 3))
      source target
  exact twoReplicaSchurKernel_floor_of_left_zero_right_one
    ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
    ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
    ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
    ((slabLinkExternalSpins extent D.leftPhysical D.link) 3)
    ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
    ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
    ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
    ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)
    hleft0 hleft1 hleft2 hleft3
    hright0 hright1 hright2 hright3 source target

theorem slabPhysicalPairRecouplingKernelPackageFour_vacuum_fundamental_pos
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 4)
    (hleft0 : (slabLinkExternalSpins extent D.leftPhysical D.link) 0 = 0)
    (hleft1 : (slabLinkExternalSpins extent D.leftPhysical D.link) 1 = 0)
    (hleft2 : (slabLinkExternalSpins extent D.leftPhysical D.link) 2 = 0)
    (hleft3 : (slabLinkExternalSpins extent D.leftPhysical D.link) 3 = 0)
    (hright0 : (slabLinkExternalSpins extent D.rightPhysical D.link) 0 = 1)
    (hright1 : (slabLinkExternalSpins extent D.rightPhysical D.link) 1 = 1)
    (hright2 : (slabLinkExternalSpins extent D.rightPhysical D.link) 2 = 1)
    (hright3 : (slabLinkExternalSpins extent D.rightPhysical D.link) 3 = 1)
    (source : (slabPhysicalPairRecouplingKernelPackageFour D).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFour D).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingKernelPackageFour D).kernel.weight
        source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < oneQuarter)
    (slabPhysicalPairRecouplingKernelPackageFour_vacuum_fundamental_floor D
      hleft0 hleft1 hleft2 hleft3
      hright0 hright1 hright2 hright3 source target)

end YMGap.Continuum.SU2SlabFundamentalVacuumPairedRecouplingFloor

#print axioms YMGap.Continuum.SU2SlabFundamentalVacuumPairedRecouplingFloor.twoReplicaSchurKernel_floor_of_left_one_right_zero
#print axioms YMGap.Continuum.SU2SlabFundamentalVacuumPairedRecouplingFloor.twoReplicaSchurKernel_floor_of_left_zero_right_one
#print axioms YMGap.Continuum.SU2SlabFundamentalVacuumPairedRecouplingFloor.slabPhysicalPairRecouplingKernelPackageFour_fundamental_vacuum_floor
#print axioms YMGap.Continuum.SU2SlabFundamentalVacuumPairedRecouplingFloor.slabPhysicalPairRecouplingKernelPackageFour_fundamental_vacuum_pos
#print axioms YMGap.Continuum.SU2SlabFundamentalVacuumPairedRecouplingFloor.slabPhysicalPairRecouplingKernelPackageFour_vacuum_fundamental_floor
#print axioms YMGap.Continuum.SU2SlabFundamentalVacuumPairedRecouplingFloor.slabPhysicalPairRecouplingKernelPackageFour_vacuum_fundamental_pos
