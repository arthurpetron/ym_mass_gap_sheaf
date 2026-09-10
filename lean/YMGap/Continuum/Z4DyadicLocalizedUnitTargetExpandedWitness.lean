/-
# Expand one coupling-one localized target into literal witnesses

A localized coarse target weight at coupling one contains two kinds of
finite multiplicity: the spin-four lowering-path product and the accepted
coarse fusion-assignment count inside the corrected-slab physical term.
Both must be explicit before a canonical component erasure can be inverted.

This file pairs the separated lowering words of the preceding recoupling
carrier with an attached accepted expanded coarse entry above the fixed
target labelling.  The resulting carrier is duplicate-free, every expanded
entry has the requested physical target, and its exact total weight is the
original localized coupling-one target weight.

Constructive contract: literal finite lists and exact rational Fubini only;
no classical choice, proof hole, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRecouplingWitnessExpansion
import YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
import YMGap.Continuum.Z4DyadicPhysicalTermExpandedWitnessFiber

namespace YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRecouplingWitnessExpansion
open YMGap.Continuum.Z4DyadicPhysicalTermExpandedWitnessFiber
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The unit-coupling coarse slab -/

/-- The coarse corrected slab with unchanged cutoff and geometry and with
heat nome set to one. -/
def coarseUnitCouplingSlabPhysicalData
    (S : SlabScalePair) : SlabPhysicalData where
  coupling := 1
  coupling_nonnegative := by decide
  cutoff := S.coarse.cutoff
  half := S.coarse.half

theorem coarseUnitCouplingSlabPhysicalData_extent
    (S : SlabScalePair) :
    (coarseUnitCouplingSlabPhysicalData S).extent =
      S.coarse.extent := rfl

theorem coarseUnitCouplingSlabPhysicalData_physicalTerm
    (S : SlabScalePair) (targetState : EdgeLabelling) :
    (coarseUnitCouplingSlabPhysicalData S).physicalTerm targetState =
      slabParametricKPhysicalTerm
        1 S.coarse.cutoff S.coarse.extent targetState := rfl

/-- A coarse physical target remains in the physical carrier after only its
coupling is changed to one. -/
theorem coarsePhysical_mem_unitCoupling
    (S : SlabScalePair) (targetState : EdgeLabelling)
    (htarget : targetState ∈ S.coarse.physicalLabellings) :
    targetState ∈
      (coarseUnitCouplingSlabPhysicalData S).physicalLabellings := by
  simpa only [coarseUnitCouplingSlabPhysicalData,
    SlabPhysicalData.physicalLabellings,
    SlabPhysicalData.faceEdges] using htarget

/-! ## 2. Lowering words paired with an accepted coarse entry -/

/-- One separated pair of lowering words and one accepted expanded entry
above the fixed coarse target. -/
abbrev FinePacketLocalizedUnitTargetExpandedWitness
    (S : SlabScalePair) :=
  FinePacketLoweringWitnessPair ×
    SlabExpandedFineSourceEntry (coarseUnitCouplingSlabPhysicalData S)

/-- The full witness carrier of one localized unit-coupling target term. -/
def finePacketLocalizedUnitTargetExpandedWitnessCarrier
    (S : SlabScalePair) (source first second targetState : EdgeLabelling)
    (htarget : targetState ∈ S.coarse.physicalLabellings) :
    List (FinePacketLocalizedUnitTargetExpandedWitness S) :=
  cartesian
    (finePacketLocalizedLoweringWitnessPairCarrier
      S source first second targetState)
    (slabPhysicalExpandedEntryBlock
      (coarseUnitCouplingSlabPhysicalData S) targetState
      (coarsePhysical_mem_unitCoupling S targetState htarget))

/-- The witness weight is the literal accepted coarse-entry weight; the
lowering word contributes one copy. -/
def finePacketLocalizedUnitTargetExpandedWitnessWeight
    (S : SlabScalePair)
    (witness : FinePacketLocalizedUnitTargetExpandedWitness S) : Q' :=
  (1 : Q') * slabExpandedFineEntryWeight
    (coarseUnitCouplingSlabPhysicalData S) witness.2

/-- The expanded witness carrier contains no duplicate. -/
theorem finePacketLocalizedUnitTargetExpandedWitnessCarrier_nodup
    (S : SlabScalePair) (source first second targetState : EdgeLabelling)
    (htarget : targetState ∈ S.coarse.physicalLabellings) :
    (finePacketLocalizedUnitTargetExpandedWitnessCarrier
      S source first second targetState htarget).Nodup := by
  unfold finePacketLocalizedUnitTargetExpandedWitnessCarrier
  exact cartesian_nodup _ _
    (finePacketLocalizedLoweringWitnessPairCarrier_nodup
      S source first second targetState)
    (slabPhysicalExpandedEntryBlock_nodup
      (coarseUnitCouplingSlabPhysicalData S) targetState
      (coarsePhysical_mem_unitCoupling S targetState htarget))

/-- Every expanded coarse entry in this carrier has literally the selected
target labelling. -/
theorem finePacketLocalizedUnitTargetExpandedWitness_physical_eq
    (S : SlabScalePair) (source first second targetState : EdgeLabelling)
    (htarget : targetState ∈ S.coarse.physicalLabellings)
    (witness : FinePacketLocalizedUnitTargetExpandedWitness S)
    (hwitness : witness ∈
      finePacketLocalizedUnitTargetExpandedWitnessCarrier
        S source first second targetState htarget) :
    witness.2.1.1 = targetState := by
  have hparts := (mem_cartesian_iff _ _ witness).mp hwitness
  exact slabPhysicalExpandedEntryBlock_physical_eq
    (coarseUnitCouplingSlabPhysicalData S) targetState
    (coarsePhysical_mem_unitCoupling S targetState htarget)
    witness.2 hparts.2

/-! ## 3. Exact total weight -/

private theorem listQSum_const_local {A : Type} (constant : Q') :
    ∀ items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _head :: tail => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat tail.length * constant) _ ?_ ?_
      · exact Q'.add_eqv_congr_left constant _ _
          (listQSum_const_local constant tail)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv _ constant)

/-- Summing literal lowering and accepted-assignment witnesses reconstructs
the localized coupling-one target weight exactly. -/
theorem finePacketLocalizedUnitTargetExpandedWitnessWeight_total
    (S : SlabScalePair) (source first second targetState : EdgeLabelling)
    (htarget : targetState ∈ S.coarse.physicalLabellings) :
    listQSum
        (finePacketLocalizedUnitTargetExpandedWitnessWeight S)
        (finePacketLocalizedUnitTargetExpandedWitnessCarrier
          S source first second targetState htarget) ≈
      finePacketLocalizedUnitCouplingTargetRawWeight
        S source first second targetState := by
  let lowering := finePacketLocalizedLoweringWitnessPairCarrier
    S source first second targetState
  let targetBlock := slabPhysicalExpandedEntryBlock
    (coarseUnitCouplingSlabPhysicalData S) targetState
    (coarsePhysical_mem_unitCoupling S targetState htarget)
  have hcart := listQSum_cartesian_product
    (fun _word : FinePacketLoweringWitnessPair => (1 : Q'))
    (slabExpandedFineEntryWeight
      (coarseUnitCouplingSlabPhysicalData S))
    lowering targetBlock
  have hlowering := listQSum_const_local (1 : Q') lowering
  have htargetWeight := slabPhysicalExpandedEntryBlock_weight_total
    (coarseUnitCouplingSlabPhysicalData S) targetState
    (coarsePhysical_mem_unitCoupling S targetState htarget)
  have hlength :=
    finePacketLocalizedLoweringWitnessPairCarrier_length
      S source first second targetState
  refine Q'.eqv_trans _
    (listQSum (fun _word : FinePacketLoweringWitnessPair => (1 : Q'))
        lowering *
      listQSum
    (slabExpandedFineEntryWeight
          (coarseUnitCouplingSlabPhysicalData S)) targetBlock) _ ?_ ?_
  · change
      listQSum
          (fun pair : FinePacketLoweringWitnessPair ×
              SlabExpandedFineSourceEntry
                (coarseUnitCouplingSlabPhysicalData S) =>
            (1 : Q') * slabExpandedFineEntryWeight
              (coarseUnitCouplingSlabPhysicalData S) pair.2)
          (cartesian lowering targetBlock) ≈ _
    exact hcart
  refine Q'.eqv_trans _
    ((Q'.ofNat lowering.length * (1 : Q')) *
      listQSum
        (slabExpandedFineEntryWeight
          (coarseUnitCouplingSlabPhysicalData S)) targetBlock) _
    (Q'.mul_eqv_congr_right _ _ _ hlowering) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat lowering.length *
      listQSum
        (slabExpandedFineEntryWeight
          (coarseUnitCouplingSlabPhysicalData S)) targetBlock) _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_one_eqv (Q'.ofNat lowering.length))) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat lowering.length *
      (coarseUnitCouplingSlabPhysicalData S).physicalTerm targetState) _
    (Q'.mul_eqv_congr_left _ _ _ htargetWeight) ?_
  rw [hlength]
  unfold finePacketLocalizedUnitCouplingTargetRawWeight
    coarseUnitCouplingSlabPhysicalData
    SlabPhysicalData.physicalTerm
  refine Q'.eqv_trans _
    (Q'.ofNat
        (finePacketCommonExteriorMultiplicityProduct
          S first second targetState) *
      Q'.ofNat
        (finePacketDisagreementMultiplicityProduct
          S source first second targetState) *
      slabParametricKPhysicalTerm
        1 S.coarse.cutoff S.coarse.extent targetState) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (ofNat_mul_eqv
        (finePacketCommonExteriorMultiplicityProduct
          S first second targetState)
        (finePacketDisagreementMultiplicityProduct
          S source first second targetState))
  · exact Q'.mul_assoc_eqv _ _ _

#print axioms coarseUnitCouplingSlabPhysicalData
#print axioms coarseUnitCouplingSlabPhysicalData_extent
#print axioms coarseUnitCouplingSlabPhysicalData_physicalTerm
#print axioms coarsePhysical_mem_unitCoupling
#print axioms finePacketLocalizedUnitTargetExpandedWitnessCarrier
#print axioms finePacketLocalizedUnitTargetExpandedWitnessCarrier_nodup
#print axioms finePacketLocalizedUnitTargetExpandedWitness_physical_eq
#print axioms finePacketLocalizedUnitTargetExpandedWitnessWeight_total

end YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness
