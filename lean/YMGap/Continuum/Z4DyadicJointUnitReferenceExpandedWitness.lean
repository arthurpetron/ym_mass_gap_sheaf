/-
# Explicit four-entry carrier for the joint coupling-one reference

The heat-free numerator left by the connected-row factorization is the
product of a coupling-one fine-source pair weight and an oriented
coupling-one coarse-target pair weight.  The preceding modules separately
expose physical fusion assignments and coarse lowering paths.

This file combines them without collapsing the scale boundary.  One joint
witness consists of two accepted fine entries and two accepted coarse
entries, with the coarse entries additionally carrying their separated
agreement/disagreement lowering words.  The carrier is duplicate-free and
its total weight is exactly the full joint coupling-one reference numerator.

Constructive contract: finite Cartesian products and exact rational Fubini
only; no classical choice, proof hole, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness

namespace YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness
open YMGap.Continuum.Z4DyadicPhysicalTermExpandedWitnessFiber
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr_local
    {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

/-! ## 1. The oriented coarse-target pair -/

/-- Two expanded localized target witnesses in their oriented row order. -/
abbrev FinePacketOrientedUnitTargetExpandedWitnessPair
    (S : SlabScalePair) :=
  FinePacketLocalizedUnitTargetExpandedWitness S ×
    FinePacketLocalizedUnitTargetExpandedWitness S

/-- The two localized target witness carriers, ordered according to the
forward or reverse determinant orientation. -/
def finePacketOrientedUnitTargetExpandedWitnessPairCarrier
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling)
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings) :
    List (FinePacketOrientedUnitTargetExpandedWitnessPair S) :=
  match orientation with
  | .forward =>
      cartesian
        (finePacketLocalizedUnitTargetExpandedWitnessCarrier
          S first first second pair.1 hleft)
        (finePacketLocalizedUnitTargetExpandedWitnessCarrier
          S second first second pair.2 hright)
  | .reverse =>
      cartesian
        (finePacketLocalizedUnitTargetExpandedWitnessCarrier
          S second first second pair.1 hleft)
        (finePacketLocalizedUnitTargetExpandedWitnessCarrier
          S first first second pair.2 hright)

/-- Product of the two literal coarse witness weights. -/
def finePacketOrientedUnitTargetExpandedWitnessPairWeight
    (S : SlabScalePair)
    (witness : FinePacketOrientedUnitTargetExpandedWitnessPair S) : Q' :=
  finePacketLocalizedUnitTargetExpandedWitnessWeight S witness.1 *
    finePacketLocalizedUnitTargetExpandedWitnessWeight S witness.2

/-- The oriented coarse-target witness carrier is duplicate-free. -/
theorem finePacketOrientedUnitTargetExpandedWitnessPairCarrier_nodup
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling)
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings) :
    (finePacketOrientedUnitTargetExpandedWitnessPairCarrier
      S orientation first second pair hleft hright).Nodup := by
  cases orientation with
  | forward =>
      exact cartesian_nodup _ _
        (finePacketLocalizedUnitTargetExpandedWitnessCarrier_nodup
          S first first second pair.1 hleft)
        (finePacketLocalizedUnitTargetExpandedWitnessCarrier_nodup
          S second first second pair.2 hright)
  | reverse =>
      exact cartesian_nodup _ _
        (finePacketLocalizedUnitTargetExpandedWitnessCarrier_nodup
          S second first second pair.1 hleft)
        (finePacketLocalizedUnitTargetExpandedWitnessCarrier_nodup
          S first first second pair.2 hright)

/-- The explicit oriented pair sums exactly to the existing coupling-one
target-pair weight. -/
theorem finePacketOrientedUnitTargetExpandedWitnessPairWeight_total
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling)
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings) :
    listQSum
        (finePacketOrientedUnitTargetExpandedWitnessPairWeight S)
        (finePacketOrientedUnitTargetExpandedWitnessPairCarrier
          S orientation first second pair hleft hright) ≈
      finePacketOrientedUnitCouplingTargetRawPairWeight
        S orientation first second pair := by
  cases orientation with
  | forward =>
      have hcart := listQSum_cartesian_product
        (finePacketLocalizedUnitTargetExpandedWitnessWeight S)
        (finePacketLocalizedUnitTargetExpandedWitnessWeight S)
        (finePacketLocalizedUnitTargetExpandedWitnessCarrier
          S first first second pair.1 hleft)
        (finePacketLocalizedUnitTargetExpandedWitnessCarrier
          S second first second pair.2 hright)
      refine Q'.eqv_trans _ _ _ hcart ?_
      exact qmul_congr_local
        (finePacketLocalizedUnitTargetExpandedWitnessWeight_total
          S first first second pair.1 hleft)
        (finePacketLocalizedUnitTargetExpandedWitnessWeight_total
          S second first second pair.2 hright)
  | reverse =>
      have hcart := listQSum_cartesian_product
        (finePacketLocalizedUnitTargetExpandedWitnessWeight S)
        (finePacketLocalizedUnitTargetExpandedWitnessWeight S)
        (finePacketLocalizedUnitTargetExpandedWitnessCarrier
          S second first second pair.1 hleft)
        (finePacketLocalizedUnitTargetExpandedWitnessCarrier
          S first first second pair.2 hright)
      refine Q'.eqv_trans _ _ _ hcart ?_
      exact qmul_congr_local
        (finePacketLocalizedUnitTargetExpandedWitnessWeight_total
          S second first second pair.1 hleft)
        (finePacketLocalizedUnitTargetExpandedWitnessWeight_total
          S first first second pair.2 hright)

/-! ## 2. The accepted fine-source pair at coupling one -/

/-- The fine slab with unchanged cutoff and geometry and unit heat nome,
introduced here upstream of the response-specific expansion. -/
def finePacketFineUnitCouplingSlabPhysicalData
    (S : SlabScalePair) : SlabPhysicalData where
  coupling := 1
  coupling_nonnegative := by decide
  cutoff := S.fine.cutoff
  half := S.fine.half

theorem finePacketFineUnitCouplingSlabPhysicalData_physicalTerm
    (S : SlabScalePair) (source : EdgeLabelling) :
    (finePacketFineUnitCouplingSlabPhysicalData S).physicalTerm source =
      fineUnitCouplingPhysicalTerm S source := rfl

theorem finePhysical_mem_unitCoupling
    (S : SlabScalePair) (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings) :
    source ∈
      (finePacketFineUnitCouplingSlabPhysicalData S).physicalLabellings := by
  simpa only [finePacketFineUnitCouplingSlabPhysicalData,
    SlabPhysicalData.physicalLabellings,
    SlabPhysicalData.faceEdges] using hsource

/-- All accepted fine fusion assignments above the fixed positive source
pair. -/
def finePacketFineUnitSourceExpandedStateCarrier
    (S : SlabScalePair) (first second : PositivePhysicalSource S) :
    List (SlabAcceptedTwoReplicaState
      (finePacketFineUnitCouplingSlabPhysicalData S)) :=
  slabPhysicalPairExpandedStateCarrier
    (finePacketFineUnitCouplingSlabPhysicalData S)
    first.1 (finePhysical_mem_unitCoupling S first.1 first.2.1)
    second.1 (finePhysical_mem_unitCoupling S second.1 second.2.1)

def finePacketFineUnitSourceExpandedStateWeight
    (S : SlabScalePair)
    (state : SlabAcceptedTwoReplicaState
      (finePacketFineUnitCouplingSlabPhysicalData S)) : Q' :=
  slabAcceptedTwoReplicaStateWeight
    (finePacketFineUnitCouplingSlabPhysicalData S) state

theorem finePacketFineUnitSourceExpandedStateCarrier_nodup
    (S : SlabScalePair) (first second : PositivePhysicalSource S) :
    (finePacketFineUnitSourceExpandedStateCarrier
      S first second).Nodup :=
  slabPhysicalPairExpandedStateCarrier_nodup
    (finePacketFineUnitCouplingSlabPhysicalData S)
    first.1 (finePhysical_mem_unitCoupling S first.1 first.2.1)
    second.1 (finePhysical_mem_unitCoupling S second.1 second.2.1)

theorem finePacketFineUnitSourceExpandedStateWeight_total
    (S : SlabScalePair) (first second : PositivePhysicalSource S) :
    listQSum
        (finePacketFineUnitSourceExpandedStateWeight S)
        (finePacketFineUnitSourceExpandedStateCarrier S first second) ≈
      finePacketFineSourceUnitCouplingPairWeight
        S first.1 second.1 := by
  simpa only [finePacketFineUnitSourceExpandedStateCarrier,
    finePacketFineUnitSourceExpandedStateWeight,
    finePacketFineUnitCouplingSlabPhysicalData_physicalTerm,
    finePacketFineSourceUnitCouplingPairWeight] using
    (slabPhysicalPairExpandedStateCarrier_weight_total
      (finePacketFineUnitCouplingSlabPhysicalData S)
      first.1 (finePhysical_mem_unitCoupling S first.1 first.2.1)
      second.1 (finePhysical_mem_unitCoupling S second.1 second.2.1))

/-! ## 3. The complete fine/coarse joint witness -/

/-- Two accepted fine entries paired with two accepted coarse entries and
their four lowering words. -/
abbrev FinePacketOrientedJointUnitExpandedWitness
    (S : SlabScalePair) :=
  SlabAcceptedTwoReplicaState
      (finePacketFineUnitCouplingSlabPhysicalData S) ×
    FinePacketOrientedUnitTargetExpandedWitnessPair S

def finePacketOrientedJointUnitExpandedWitnessCarrier
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings) :
    List (FinePacketOrientedJointUnitExpandedWitness S) :=
  cartesian
    (finePacketFineUnitSourceExpandedStateCarrier S first second)
    (finePacketOrientedUnitTargetExpandedWitnessPairCarrier
      S orientation first.1 second.1 pair hleft hright)

def finePacketOrientedJointUnitExpandedWitnessWeight
    (S : SlabScalePair)
    (witness : FinePacketOrientedJointUnitExpandedWitness S) : Q' :=
  finePacketFineUnitSourceExpandedStateWeight S witness.1 *
    finePacketOrientedUnitTargetExpandedWitnessPairWeight S witness.2

/-- The full four-entry joint witness carrier is duplicate-free. -/
theorem finePacketOrientedJointUnitExpandedWitnessCarrier_nodup
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings) :
    (finePacketOrientedJointUnitExpandedWitnessCarrier
      S orientation first second pair hleft hright).Nodup := by
  unfold finePacketOrientedJointUnitExpandedWitnessCarrier
  exact cartesian_nodup _ _
    (finePacketFineUnitSourceExpandedStateCarrier_nodup S first second)
    (finePacketOrientedUnitTargetExpandedWitnessPairCarrier_nodup
      S orientation first.1 second.1 pair hleft hright)

/-- The explicit reference numerator named independently of its later
positive ground-target denominator. -/
def finePacketOrientedJointUnitReferenceNumerator
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  finePacketFineSourceUnitCouplingPairWeight S first second *
    finePacketOrientedUnitCouplingTargetRawPairWeight
      S orientation first second pair

/-- Exact expansion of the complete heat-free joint numerator into literal
fine and coarse SU(2) witnesses. -/
theorem finePacketOrientedJointUnitExpandedWitnessWeight_total
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings) :
    listQSum
        (finePacketOrientedJointUnitExpandedWitnessWeight S)
        (finePacketOrientedJointUnitExpandedWitnessCarrier
          S orientation first second pair hleft hright) ≈
      finePacketOrientedJointUnitReferenceNumerator
        S orientation first.1 second.1 pair := by
  refine Q'.eqv_trans _
    (listQSum (finePacketFineUnitSourceExpandedStateWeight S)
        (finePacketFineUnitSourceExpandedStateCarrier S first second) *
      listQSum
        (finePacketOrientedUnitTargetExpandedWitnessPairWeight S)
        (finePacketOrientedUnitTargetExpandedWitnessPairCarrier
          S orientation first.1 second.1 pair hleft hright)) _ ?_ ?_
  · exact listQSum_cartesian_product _ _ _ _
  · unfold finePacketOrientedJointUnitReferenceNumerator
    exact qmul_congr_local
      (finePacketFineUnitSourceExpandedStateWeight_total S first second)
      (finePacketOrientedUnitTargetExpandedWitnessPairWeight_total
        S orientation first.1 second.1 pair hleft hright)

#print axioms finePacketOrientedUnitTargetExpandedWitnessPairCarrier
#print axioms finePacketOrientedUnitTargetExpandedWitnessPairCarrier_nodup
#print axioms finePacketOrientedUnitTargetExpandedWitnessPairWeight_total
#print axioms finePacketFineUnitCouplingSlabPhysicalData
#print axioms finePacketFineUnitCouplingSlabPhysicalData_physicalTerm
#print axioms finePhysical_mem_unitCoupling
#print axioms finePacketFineUnitSourceExpandedStateCarrier
#print axioms finePacketFineUnitSourceExpandedStateWeight_total
#print axioms finePacketOrientedJointUnitExpandedWitnessCarrier
#print axioms finePacketOrientedJointUnitExpandedWitnessCarrier_nodup
#print axioms finePacketOrientedJointUnitReferenceNumerator
#print axioms finePacketOrientedJointUnitExpandedWitnessWeight_total

end YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
