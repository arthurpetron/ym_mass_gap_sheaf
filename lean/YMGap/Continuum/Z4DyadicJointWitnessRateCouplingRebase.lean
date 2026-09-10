/-
# Rebase all four entries of a joint witness to one explicit rate

A literal joint unit witness contains an accepted fine-source pair and an
accepted coarse-target pair, with lowering words attached to the latter.
This module changes the coupling of all four accepted entries to the same
named nonnegative rate.  The lowering words remain structural data and carry
unit weight.

The resulting four-state weight is exactly the unit joint witness weight
multiplied by the rate to the sum of all four physical face-Casimir
exponents.  This is the precise rate-coupled object to which the two
arbitrary-coupling component-peeling telescopes will be applied.

Constructive contract: typed coupling transport and exact rational algebra
only; no classical choice, proof hole, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase
import YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeeling

namespace YMGap.Continuum.Z4DyadicJointWitnessRateCouplingRebase

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.RGTransport
open YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase
open YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeeling
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr_local
    {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

private theorem mul_four_regroup_local (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-! ## 1. Identify the unit coarse pair hidden beside the lowering words -/

theorem finePacketOrientedUnitTargetExpandedWitnessPairWeight_eqv_accepted
    (S : SlabScalePair)
    (witness : FinePacketOrientedUnitTargetExpandedWitnessPair S) :
    finePacketOrientedUnitTargetExpandedWitnessPairWeight S witness ≈
      slabAcceptedTwoReplicaStateWeight
        (coarseUnitCouplingSlabPhysicalData S)
        (witness.1.2, witness.2.2) := by
  unfold finePacketOrientedUnitTargetExpandedWitnessPairWeight
    finePacketLocalizedUnitTargetExpandedWitnessWeight
    slabAcceptedTwoReplicaStateWeight
  exact qmul_congr_local
    (Q'.one_mul_eqv _) (Q'.one_mul_eqv _)

theorem finePacketOrientedJointUnitExpandedWitnessWeight_eqv_fourState
    (S : SlabScalePair)
    (witness : FinePacketOrientedJointUnitExpandedWitness S) :
    finePacketOrientedJointUnitExpandedWitnessWeight S witness ≈
      slabAcceptedTwoReplicaStateWeight
          (finePacketFineUnitCouplingSlabPhysicalData S) witness.1 *
        slabAcceptedTwoReplicaStateWeight
          (coarseUnitCouplingSlabPhysicalData S)
          (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
            S witness) := by
  unfold finePacketOrientedJointUnitExpandedWitnessWeight
    finePacketFineUnitSourceExpandedStateWeight
    finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
  exact Q'.mul_eqv_congr_left _ _ _
    (finePacketOrientedUnitTargetExpandedWitnessPairWeight_eqv_accepted
      S witness.2)

/-! ## 2. Four rate-coupled accepted entries and their exact weight -/

/-- The total face-Casimir exponent of both fine and both coarse accepted
entries in a literal joint witness. -/
def finePacketOrientedJointUnitExpandedWitnessCasimirExponent
    (S : SlabScalePair)
    (witness : FinePacketOrientedJointUnitExpandedWitness S) : Nat :=
  slabAcceptedTwoReplicaStateCasimirExponent
      (finePacketFineUnitCouplingSlabPhysicalData S) witness.1 +
    slabAcceptedTwoReplicaStateCasimirExponent
      (coarseUnitCouplingSlabPhysicalData S)
      (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
        S witness)

/-- Product weight of the fine and coarse accepted pairs after all four
entries have been rebased to the same explicit rate. -/
def finePacketOrientedJointExpandedWitnessAtCouplingWeight
    (S : SlabScalePair) (coupling : Q')
    (hcoupling : (0 : Q') ≤ coupling)
    (witness : FinePacketOrientedJointUnitExpandedWitness S) : Q' :=
  slabAcceptedTwoReplicaStateWeight
      (slabPhysicalDataAtCoupling
        (finePacketFineUnitCouplingSlabPhysicalData S)
        coupling hcoupling)
      (slabAcceptedTwoReplicaStateAtCoupling
        (finePacketFineUnitCouplingSlabPhysicalData S)
        coupling hcoupling witness.1) *
    slabAcceptedTwoReplicaStateWeight
      (slabPhysicalDataAtCoupling
        (coarseUnitCouplingSlabPhysicalData S)
        coupling hcoupling)
      (slabAcceptedTwoReplicaStateAtCoupling
        (coarseUnitCouplingSlabPhysicalData S)
        coupling hcoupling
        (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
          S witness))

/-- Exact four-entry change-of-coupling identity.  The rate and every
Casimir exponent remain visible in the statement. -/
theorem finePacketOrientedJointExpandedWitnessAtCouplingWeight_eqv
    (S : SlabScalePair) (coupling : Q')
    (hcoupling : (0 : Q') ≤ coupling)
    (witness : FinePacketOrientedJointUnitExpandedWitness S) :
    finePacketOrientedJointExpandedWitnessAtCouplingWeight
        S coupling hcoupling witness ≈
      qpow coupling
          (finePacketOrientedJointUnitExpandedWitnessCasimirExponent
            S witness) *
        finePacketOrientedJointUnitExpandedWitnessWeight S witness := by
  let fineD := finePacketFineUnitCouplingSlabPhysicalData S
  let coarseD := coarseUnitCouplingSlabPhysicalData S
  let coarseState :=
    finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState S witness
  let fineExponent :=
    slabAcceptedTwoReplicaStateCasimirExponent fineD witness.1
  let coarseExponent :=
    slabAcceptedTwoReplicaStateCasimirExponent coarseD coarseState
  let fineWeight := slabAcceptedTwoReplicaStateWeight fineD witness.1
  let coarseWeight := slabAcceptedTwoReplicaStateWeight coarseD coarseState
  have hfine := slabAcceptedTwoReplicaStateAtCoupling_weight_eqv
    fineD rfl coupling hcoupling witness.1
  have hcoarse := slabAcceptedTwoReplicaStateAtCoupling_weight_eqv
    coarseD rfl coupling hcoupling coarseState
  have hjoint :=
    finePacketOrientedJointUnitExpandedWitnessWeight_eqv_fourState S witness
  unfold finePacketOrientedJointExpandedWitnessAtCouplingWeight
  refine Q'.eqv_trans _
    ((qpow coupling fineExponent * fineWeight) *
      (qpow coupling coarseExponent * coarseWeight)) _
    (qmul_congr_local hfine hcoarse) ?_
  refine Q'.eqv_trans _
    ((qpow coupling fineExponent * qpow coupling coarseExponent) *
      (fineWeight * coarseWeight)) _
    (mul_four_regroup_local _ _ _ _) ?_
  refine Q'.eqv_trans _
    (qpow coupling (fineExponent + coarseExponent) *
      (fineWeight * coarseWeight)) _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm
        (YMGap.Continuum.HeatKernelRGStep.qpow_add coupling
          fineExponent coarseExponent))) ?_
  have hfinal := Q'.mul_eqv_congr_left
    (qpow coupling (fineExponent + coarseExponent)) _ _
    (Q'.eqv_symm hjoint)
  simpa only [finePacketOrientedJointUnitExpandedWitnessCasimirExponent,
    fineD, coarseD, coarseState, fineExponent, coarseExponent,
    fineWeight, coarseWeight] using hfinal

#print axioms finePacketOrientedUnitTargetExpandedWitnessPairWeight_eqv_accepted
#print axioms finePacketOrientedJointUnitExpandedWitnessWeight_eqv_fourState
#print axioms finePacketOrientedJointUnitExpandedWitnessCasimirExponent
#print axioms finePacketOrientedJointExpandedWitnessAtCouplingWeight
#print axioms finePacketOrientedJointExpandedWitnessAtCouplingWeight_eqv

end YMGap.Continuum.Z4DyadicJointWitnessRateCouplingRebase
