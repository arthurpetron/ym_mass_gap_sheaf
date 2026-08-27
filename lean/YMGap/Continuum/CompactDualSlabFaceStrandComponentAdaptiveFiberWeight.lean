/-
# Weighted summation on a fixed adaptive component-removal fiber

The inverse-fiber theorem bounds the number of source configurations by
`10240000^n`.  The accepted component peel bounds each source weight by
`anchorFaceCoefficient^n` times the common target weight.  This module combines
those two statements constructively, producing the exact fixed-fiber estimate

  sourceWeightSum <= (8/25)^n * targetWeight.

The family remains an explicit input: connecting this fixed-fiber estimate to
the actual bounded slab-state enumeration and summing over roots and component
sizes is the next theorem, not an implicit assumption here.

Constructive contract: finite rational sums, explicit nonnegativity, and exact
power algebra only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveInverseFiber
import YMGap.Continuum.PartitionUpperBound

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveInverseFiber
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.PartitionUpperBound
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic finite cardinality-to-weight compiler -/

/-- A pointwise nonnegative rational bound sums to length times that bound. -/
theorem listQSum_le_length_mul
    {A : Type} (value : A -> Q')
    {bound : Q'} (hboundNonnegative : (0 : Q') <= bound) :
    forall items : List A,
      (forall item, item ∈ items -> value item <= bound) ->
      listQSum value items <= Q'.ofNat items.length * bound
  | [], _ =>
      Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound => by
      have hhead := hbound head List.mem_cons_self
      have htail := listQSum_le_length_mul value hboundNonnegative tail
        (fun item hitem =>
          hbound item (List.mem_cons_of_mem head hitem))
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add hhead htail) ?_
      refine Q'.le_of_eqv (Q'.eqv_symm ?_)
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * bound) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ bound
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + (1 : Q') * bound) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 bound) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + bound) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv bound))
        (Q'.add_comm_eqv (Q'.ofNat tail.length * bound) bound)

/-- A cardinality bound `base^n` and a pointwise factor `factor^n` combine
into the product-rate bound `(base*factor)^n`. -/
theorem fixedCardinalityWeightedSum_le
    {A : Type} (items : List A) (weight : A -> Q')
    (base exponent : Nat) (factor targetWeight : Q')
    (hcardinality : items.length <= base ^ exponent)
    (hfactorNonnegative : (0 : Q') <= factor)
    (htargetNonnegative : (0 : Q') <= targetWeight)
    (hpointwise : forall item, item ∈ items ->
      weight item <= factor ^ exponent * targetWeight) :
    listQSum weight items <=
      (Q'.ofNat base * factor) ^ exponent * targetWeight := by
  have hfactorPowerNonnegative : (0 : Q') <= factor ^ exponent :=
    Q'.pow_nonneg factor hfactorNonnegative exponent
  have hboundNonnegative :
      (0 : Q') <= factor ^ exponent * targetWeight :=
    Q'.mul_nonneg _ _ hfactorPowerNonnegative htargetNonnegative
  have hsum := listQSum_le_length_mul weight hboundNonnegative
    items hpointwise
  have hcardinalityQ :
      Q'.ofNat items.length <= Q'.ofNat (base ^ exponent) :=
    Q'.ofNat_le_ofNat hcardinality
  have hscale :
      Q'.ofNat items.length * (factor ^ exponent * targetWeight) <=
        Q'.ofNat (base ^ exponent) *
          (factor ^ exponent * targetWeight) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcardinalityQ hboundNonnegative
  refine Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ hscale ?_)
  refine Q'.le_of_eqv (Q'.eqv_trans _
    ((Q'.ofNat (base ^ exponent) * factor ^ exponent) * targetWeight) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv
      (Q'.ofNat (base ^ exponent)) (factor ^ exponent) targetWeight)) ?_)
  exact Q'.mul_eqv_congr_right _ _ targetWeight
    (ofNat_pow_mul base factor exponent)

/-! ## 2. Nonnegativity of the actual target fiber weight -/

private theorem anchorPacketCoefficient_nonnegativeLocal
    (cutoff spin : Nat) :
    (0 : Q') <= coeffAt (heatKernelPacket cutoff anchorCoupling) spin := by
  by_cases hspin : spin < cutoff + 1
  · rw [coeffAt_heatKernelPacket hspin]
    exact coeffW_nonneg (by decide) spin
  · have hlarge : cutoff < spin := by omega
    rw [coeffAt_of_gt (heatKernelPacket cutoff anchorCoupling) hlarge]
    exact Q'.le_refl' 0

private theorem eliminateLinks_anchor_nonnegativeLocal
    (cutoff : Nat) (physical : EdgeLabelling) : forall ids : List Nat,
    (0 : Q') <= eliminateLinks
      (fun id => coeffAt (heatKernelPacket cutoff anchorCoupling)
        (physical id)) ids
  | [] => Q'.zero_le_one
  | _ :: ids =>
      Q'.mul_nonneg _ _
        (anchorPacketCoefficient_nonnegativeLocal cutoff _)
        (eliminateLinks_anchor_nonnegativeLocal cutoff physical ids)

/-- Every literal expanded-fiber entry at the production anchor is
nonnegative. -/
theorem retainedFineIntertwinerPhysicalFiberWeight_anchor_nonnegative
    (cutoff half : Nat) (physical : SlabLabelling)
    (assignment : SlabFusionWitnessAssignment) :
    let D : SlabPhysicalData :=
      { coupling := anchorCoupling
        coupling_nonnegative := by decide
        cutoff := cutoff
        half := half }
    (0 : Q') <=
      retainedFineIntertwinerPhysicalFiberWeight D physical assignment := by
  dsimp only
  unfold retainedFineIntertwinerPhysicalFiberWeight
    retainedFineIntertwinerRawWeight
    slabParametricKPhysicalFaceFactor
  exact Q'.mul_nonneg _ _
    (eliminateLinks_anchor_nonnegativeLocal cutoff physical
      (slabPhysicalFaceEdges (centralExtent half)))
    Q'.zero_le_one

/-! ## 3. Fixed-target component-fiber heat sum -/

/-- **Strict weighted fixed-fiber estimate.**  An explicit duplicate-free
family of sources which all remove one rooted component of size `peelSize` to
the same target has total source weight at most `(8/25)^peelSize` times the
target weight. -/
theorem componentAdaptiveRemovalSources_weight_sum_le
    (cutoff half rootFaceId peelSize : Nat)
    (targetPhysical : SlabLabelling)
    (targetAssignment : SlabFusionWitnessAssignment)
    (sources : List (SlabLabelling × SlabFusionWitnessAssignment))
    (hsources : sources.Nodup)
    (witness : forall source, source ∈ sources ->
      ComponentAdaptiveRemovalWitness cutoff (centralExtent half)
        rootFaceId peelSize targetPhysical targetAssignment source)
    (hbounded : forall source, source ∈ sources ->
      SlabFaceLabellingBounded cutoff (centralExtent half) source.1) :
    let D : SlabPhysicalData :=
      { coupling := anchorCoupling
        coupling_nonnegative := by decide
        cutoff := cutoff
        half := half }
    listQSum
        (fun source => retainedFineIntertwinerPhysicalFiberWeight
          D source.1 source.2) sources <=
      componentAdaptiveEntropyAnchorRatio ^ peelSize *
        retainedFineIntertwinerPhysicalFiberWeight
          D targetPhysical targetAssignment := by
  dsimp only
  unfold componentAdaptiveEntropyAnchorRatio
  apply fixedCardinalityWeightedSum_le
  · exact componentAdaptiveRemovalSources_length_le
      cutoff (centralExtent half) rootFaceId peelSize
      targetPhysical targetAssignment sources hsources witness
  · decide
  · exact retainedFineIntertwinerPhysicalFiberWeight_anchor_nonnegative
      cutoff half targetPhysical targetAssignment
  · intro source hsource
    have hweight :=
      SlabFusionWitnessFaceStrandSeed.expandedFiberWeight_le
        cutoff half (witness source hsource).seed
          (hbounded source hsource)
    dsimp only at hweight
    rw [(witness source hsource).peelSize_eq,
      (witness source hsource).lowerPhysical_eq,
      (witness source hsource).lowerAssignment_eq] at hweight
    exact hweight

#print axioms listQSum_le_length_mul
#print axioms fixedCardinalityWeightedSum_le
#print axioms retainedFineIntertwinerPhysicalFiberWeight_anchor_nonnegative
#print axioms componentAdaptiveRemovalSources_weight_sum_le

end YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
