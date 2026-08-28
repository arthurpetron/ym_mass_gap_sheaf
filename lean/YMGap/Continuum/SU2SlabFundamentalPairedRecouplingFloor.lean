/-
# The fundamental paired floor inside an actual slab-link package

The sharp `1/16` two-replica floor is stated first on the canonical
four-valent Schur carrier.  This module identifies that carrier inside the
production `SlabPhysicalPairRecouplingData` package at a genuine geometric
valence-four corrected-slab link.

If all four incident doubled-spin labels equal one in both physical
replicas, every source-to-target entry of the exact local slab package is at
least `1/16`.  Thus no target-side rewiring at such a link can be erased by a
zero SU(2) coefficient.

The theorem is local.  It does not construct physical fields containing a
pivotal fundamental link, prove global strand disconnection after choosing a
target, or multiply the estimate over the whole slab.

Constructive contract: definitional specialization of the exact production
kernel and the proved fundamental Schur floor only; no `Classical`, choice,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.SU2FundamentalPhysicalSchurKernelFloor
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel

namespace YMGap.Continuum.SU2SlabFundamentalPairedRecouplingFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FundamentalPhysicalSchurKernelFloor
open YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates

/-! ## 1. A dependent-label specialization lemma -/

theorem twoReplicaSchurKernel_floor_of_labels_eq_one
    (left0 left1 left2 left3 right0 right1 right2 right3 : Nat)
    (hleft0 : left0 = 1) (hleft1 : left1 = 1)
    (hleft2 : left2 = 1) (hleft3 : left3 = 1)
    (hright0 : right0 = 1) (hright1 : right1 = 1)
    (hright2 : right2 = 1) (hright3 : right3 = 1)
    (source : FixedLeftCGChannel left0 left1 left2 left3 ×
      FixedLeftCGChannel right0 right1 right2 right3)
    (target : FixedRightCGChannel left0 left1 left2 left3 ×
      FixedRightCGChannel right0 right1 right2 right3) :
    fundamentalPairedFloor ≤
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
  exact fundamental_twoReplicaSchurKernel_floor source target

/-! ## 2. The production valence-four package -/

theorem slabPhysicalPairRecouplingKernelPackageFour_floor
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 4)
    (hleft0 : (slabLinkExternalSpins extent D.leftPhysical D.link) 0 = 1)
    (hleft1 : (slabLinkExternalSpins extent D.leftPhysical D.link) 1 = 1)
    (hleft2 : (slabLinkExternalSpins extent D.leftPhysical D.link) 2 = 1)
    (hleft3 : (slabLinkExternalSpins extent D.leftPhysical D.link) 3 = 1)
    (hright0 : (slabLinkExternalSpins extent D.rightPhysical D.link) 0 = 1)
    (hright1 : (slabLinkExternalSpins extent D.rightPhysical D.link) 1 = 1)
    (hright2 : (slabLinkExternalSpins extent D.rightPhysical D.link) 2 = 1)
    (hright3 : (slabLinkExternalSpins extent D.rightPhysical D.link) 3 = 1)
    (source : (slabPhysicalPairRecouplingKernelPackageFour D).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFour D).Target) :
    fundamentalPairedFloor ≤
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
  change fundamentalPairedFloor ≤
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
  exact twoReplicaSchurKernel_floor_of_labels_eq_one
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

theorem slabPhysicalPairRecouplingKernelPackageFour_pos
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 4)
    (hleft0 : (slabLinkExternalSpins extent D.leftPhysical D.link) 0 = 1)
    (hleft1 : (slabLinkExternalSpins extent D.leftPhysical D.link) 1 = 1)
    (hleft2 : (slabLinkExternalSpins extent D.leftPhysical D.link) 2 = 1)
    (hleft3 : (slabLinkExternalSpins extent D.leftPhysical D.link) 3 = 1)
    (hright0 : (slabLinkExternalSpins extent D.rightPhysical D.link) 0 = 1)
    (hright1 : (slabLinkExternalSpins extent D.rightPhysical D.link) 1 = 1)
    (hright2 : (slabLinkExternalSpins extent D.rightPhysical D.link) 2 = 1)
    (hright3 : (slabLinkExternalSpins extent D.rightPhysical D.link) 3 = 1)
    (source : (slabPhysicalPairRecouplingKernelPackageFour D).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFour D).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingKernelPackageFour D).kernel.weight
        source target :=
  Q'.pos_of_lt_of_le fundamentalPairedFloor_pos
    (slabPhysicalPairRecouplingKernelPackageFour_floor D
      hleft0 hleft1 hleft2 hleft3
      hright0 hright1 hright2 hright3 source target)

end YMGap.Continuum.SU2SlabFundamentalPairedRecouplingFloor

#print axioms YMGap.Continuum.SU2SlabFundamentalPairedRecouplingFloor.twoReplicaSchurKernel_floor_of_labels_eq_one
#print axioms YMGap.Continuum.SU2SlabFundamentalPairedRecouplingFloor.slabPhysicalPairRecouplingKernelPackageFour_floor
#print axioms YMGap.Continuum.SU2SlabFundamentalPairedRecouplingFloor.slabPhysicalPairRecouplingKernelPackageFour_pos
