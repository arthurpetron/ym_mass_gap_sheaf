/-
# Aggregate first-edge load of the all-source inward-mate OS flow

The pointwise source-demand bound does not by itself control congestion:
several full-slab sources can forget to the same lower/right OS edge.  This
module performs the missing aggregation without a cardinality estimate.

For one fixed first OS edge, every source in its exact finite key fiber maps
to its literal `(boundary, fine-intertwiner witness)` summand.  Equality of
those summands, together with the fixed lower/right restrictions, reconstructs
the source production atom.  Global source-compiler injectivity therefore
makes the map collision-free.  Exact fine-intertwiner disintegration then
identifies the complete target sum with the raw reflected kernel entry.

After partition normalization, the total traffic of every first-edge fiber
is at most the actual symmetric OS joint capacity of that edge.  This closes
the first-edge congestion, not the second-edge aggregation, an all-pairs
demand identity, a Poincare inequality, spectral gap, continuum limit, or
Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSNormalizedFlow
import YMGap.Continuum.FiniteKeyRepresentativePartition
import YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSFirstEdgeLoad

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSEdgeCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSNormalizedFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionTransport
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionPair
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionSourceMarginal
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem pair_eq_of_fields_eq_local
    {A B : Type} {leftFirst rightFirst : A} {leftSecond rightSecond : B}
    (hfirst : leftFirst = rightFirst)
    (hsecond : leftSecond = rightSecond) :
    (leftFirst, leftSecond) = (rightFirst, rightSecond) := by
  cases hfirst
  cases hsecond
  rfl

/-! ## 1. A decidable key for the first physical OS edge -/

abbrev GlobalInwardMateOSEdgeKey := List Nat × List Nat

def globalInwardMateFirstOSEdgeKey
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    GlobalInwardMateOSEdgeKey :=
  (finiteEdgeLabellingWord (centralLowerFaceIds 0) (sourceLower source),
    finiteEdgeLabellingWord (centralLowerFaceIds 0) (commonRight source))

def globalInwardMateFirstOSEdgeFiber
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    List (GlobalCubeInwardMateCertifiedTargetFullSource K hK) :=
  representativeFiber
    (globalCubeInwardMateCertifiedTargetFullSources K hK)
    globalInwardMateFirstOSEdgeKey representative

theorem globalInwardMateFirstOSEdgeFiber_mem_source
    {K : Nat} {hK : 1 <= K}
    {representative source :
      GlobalCubeInwardMateCertifiedTargetFullSource K hK}
    (hsource : source ∈ globalInwardMateFirstOSEdgeFiber representative) :
    source ∈ globalCubeInwardMateCertifiedTargetFullSources K hK := by
  exact (List.mem_filter.mp hsource).1

private theorem supportedHalf_eq_of_word_eq
    {K : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ centralHalfStates K 0)
    (hright : right ∈ centralHalfStates K 0)
    (hword : finiteEdgeLabellingWord (centralLowerFaceIds 0) left =
      finiteEdgeLabellingWord (centralLowerFaceIds 0) right) :
    left = right := by
  exact edgeLabelling_eq_of_word_eq_of_supported
    (centralLowerFaceIds 0) left right
    (boundedEdgeLabellings_sound K (centralLowerFaceIds 0) left hleft).2
    (boundedEdgeLabellings_sound K (centralLowerFaceIds 0) right hright).2
    hword

theorem globalInwardMateFirstOSEdgeFiber_states_eq
    {K : Nat} {hK : 1 <= K}
    {representative source :
      GlobalCubeInwardMateCertifiedTargetFullSource K hK}
    (hsource : source ∈ globalInwardMateFirstOSEdgeFiber representative) :
    sourceLower representative = sourceLower source ∧
      commonRight representative = commonRight source := by
  have hkey : globalInwardMateFirstOSEdgeKey representative =
      globalInwardMateFirstOSEdgeKey source :=
    of_decide_eq_true (List.mem_filter.mp hsource).2
  constructor
  · apply supportedHalf_eq_of_word_eq
      (sourceLower_mem representative) (sourceLower_mem source)
    exact congrArg Prod.fst hkey
  · apply supportedHalf_eq_of_word_eq
      (commonRight_mem representative) (commonRight_mem source)
    exact congrArg Prod.snd hkey

/-! ## 2. The complete boundary--intertwiner carrier over one OS edge -/

abbrev GlobalInwardMateOSEdgeWitness :=
  EdgeLabelling × SlabFusionWitnessAssignment

def globalInwardMateOSEdgeWitnessBlock
    (K : Nat) (left right boundary : EdgeLabelling) :
    List GlobalInwardMateOSEdgeWitness :=
  (slabFineFusionWitnesses (globalInwardMateAnchorSlabData K)
    (assembleReflectedSlabLabelling 0 left boundary right)).map
      (fun witness => (boundary, witness))

def globalInwardMateOSEdgeWitnesses
    (K : Nat) (left right : EdgeLabelling) :
    List GlobalInwardMateOSEdgeWitness :=
  (centralBoundaryChannels K 0).flatMap
    (globalInwardMateOSEdgeWitnessBlock K left right)

def globalInwardMateOSEdgeWitnessWeight
    (K : Nat) (left right : EdgeLabelling)
    (entry : GlobalInwardMateOSEdgeWitness) : Q' :=
  retainedFineIntertwinerPhysicalFiberWeight
    (globalInwardMateAnchorSlabData K)
    (assembleReflectedSlabLabelling 0 left entry.1 right) entry.2

private theorem nodup_flatMap_of_disjoint_blocks_local {A B : Type}
    (block : A -> List B) : forall (items : List A),
    items.Nodup ->
    (forall item, item ∈ items -> (block item).Nodup) ->
    (forall left, left ∈ items -> forall right, right ∈ items -> left ≠ right ->
      forall value, value ∈ block left -> value ∉ block right) ->
    (items.flatMap block).Nodup
  | [], _, _, _ => List.nodup_nil
  | head :: tail, hitems, hblocks, hdisjoint => by
      have hparts := List.nodup_cons.mp hitems
      simp only [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨hblocks head List.mem_cons_self,
        nodup_flatMap_of_disjoint_blocks_local block tail hparts.2
          (fun item hitem => hblocks item (List.mem_cons_of_mem head hitem))
          (fun left hleft right hright hne =>
            hdisjoint left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright) hne), ?_⟩
      intro value hhead other htail heq
      have hvalueTail : value ∈ tail.flatMap block := heq ▸ htail
      obtain ⟨item, hitem, hvalueItem⟩ := List.mem_flatMap.mp hvalueTail
      have hne : head ≠ item := by
        intro hsame
        subst item
        exact hparts.1 hitem
      exact (hdisjoint head List.mem_cons_self item
        (List.mem_cons_of_mem head hitem) hne value hhead) hvalueItem

theorem globalInwardMateOSEdgeWitnesses_nodup
    (K : Nat) (left right : EdgeLabelling) :
    (globalInwardMateOSEdgeWitnesses K left right).Nodup := by
  unfold globalInwardMateOSEdgeWitnesses
  apply nodup_flatMap_of_disjoint_blocks_local
  · exact centralBoundaryChannels_nodup K 0
  · intro boundary _
    unfold globalInwardMateOSEdgeWitnessBlock
    apply nodup_map_of_injOn
    · exact slabFineFusionWitnesses_nodup
        (globalInwardMateAnchorSlabData K)
        (assembleReflectedSlabLabelling 0 left boundary right)
    · intro first _ second _ heq
      exact congrArg Prod.snd heq
  · intro first _ second _ hne entry hfirst hsecond
    obtain ⟨firstWitness, _, hfirstEq⟩ := List.mem_map.mp hfirst
    obtain ⟨secondWitness, _, hsecondEq⟩ := List.mem_map.mp hsecond
    have hpairs : (first, firstWitness) = (second, secondWitness) :=
      hfirstEq.trans hsecondEq.symm
    exact hne (congrArg Prod.fst hpairs)

theorem globalInwardMateOSEdgeWitnesses_weight_eqv_rawKernel
    (K : Nat) (left right : EdgeLabelling) :
    listQSum (globalInwardMateOSEdgeWitnessWeight K left right)
        (globalInwardMateOSEdgeWitnesses K left right) ≈
      centralPhysicalReflectedKernel anchorCoupling K 0 left right := by
  refine Q'.eqv_trans _
    (listQSum
      (fun boundary =>
        listQSum (globalInwardMateOSEdgeWitnessWeight K left right)
          (globalInwardMateOSEdgeWitnessBlock K left right boundary))
      (centralBoundaryChannels K 0)) _ ?_ ?_
  · unfold globalInwardMateOSEdgeWitnesses
    exact listQSum_flatMap
      (globalInwardMateOSEdgeWitnessWeight K left right)
      (globalInwardMateOSEdgeWitnessBlock K left right)
      (centralBoundaryChannels K 0)
  · unfold centralPhysicalReflectedKernel
    apply listQSum_congr
    intro boundary
    unfold globalInwardMateOSEdgeWitnessBlock
    rw [listQSum_map]
    exact retainedFineIntertwinerPhysicalFiberWeight_total
      (globalInwardMateAnchorSlabData K)
      (assembleReflectedSlabLabelling 0 left boundary right)

/-! ## 3. Inject every source-edge fiber into the complete OS summands -/

def globalInwardMateFirstOSEdgeWitnessEncode
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    GlobalInwardMateOSEdgeWitness :=
  (commonBoundary source,
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw source)

theorem globalInwardMateFirstOSEdgeWitnessEncode_mem
    {K : Nat} {hK : 1 <= K}
    (representative source :
      GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈ globalInwardMateFirstOSEdgeFiber representative) :
    globalInwardMateFirstOSEdgeWitnessEncode source ∈
      globalInwardMateOSEdgeWitnesses K
        (sourceLower representative) (commonRight representative) := by
  have hstates := globalInwardMateFirstOSEdgeFiber_states_eq hsource
  have hphysical :
      assembleReflectedSlabLabelling 0 (sourceLower representative)
          (commonBoundary source) (commonRight representative) =
        source.physical := by
    rw [hstates.1, hstates.2]
    exact assemble_source_path source
  unfold globalInwardMateOSEdgeWitnesses
  apply List.mem_flatMap.mpr
  refine ⟨commonBoundary source, commonBoundary_mem source, ?_⟩
  unfold globalInwardMateOSEdgeWitnessBlock
  apply List.mem_map.mpr
  refine ⟨GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw
    source, ?_, rfl⟩
  rw [hphysical]
  exact
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw_mem_allSources
      source (globalInwardMateFirstOSEdgeFiber_mem_source hsource)

theorem globalInwardMateFirstOSEdgeWitnessEncode_injective
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (left : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hleft : left ∈ globalInwardMateFirstOSEdgeFiber representative)
    (right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hright : right ∈ globalInwardMateFirstOSEdgeFiber representative)
    (heq : globalInwardMateFirstOSEdgeWitnessEncode left =
      globalInwardMateFirstOSEdgeWitnessEncode right) :
    left = right := by
  have hleftStates := globalInwardMateFirstOSEdgeFiber_states_eq hleft
  have hrightStates := globalInwardMateFirstOSEdgeFiber_states_eq hright
  have hboundary : commonBoundary left = commonBoundary right :=
    congrArg Prod.fst heq
  have hraw :
      GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw left =
        GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionRaw right := by
    have hprojection := congrArg Prod.snd heq
    simpa only [globalInwardMateFirstOSEdgeWitnessEncode] using hprojection
  have hphysical : left.physical = right.physical := by
    calc
      left.physical =
          assembleReflectedSlabLabelling 0 (sourceLower left)
            (commonBoundary left) (commonRight left) :=
        (assemble_source_path left).symm
      _ = assembleReflectedSlabLabelling 0 (sourceLower right)
            (commonBoundary right) (commonRight right) := by
        rw [← hleftStates.1, ← hrightStates.1,
          ← hleftStates.2, ← hrightStates.2, hboundary]
      _ = right.physical := assemble_source_path right
  apply globalInwardMateAllSourceProductionAtom_injective
    left (globalInwardMateFirstOSEdgeFiber_mem_source hleft)
    right (globalInwardMateFirstOSEdgeFiber_mem_source hright)
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom
  exact pair_eq_of_fields_eq_local hphysical hraw

theorem globalInwardMateFirstOSEdgeFiber_productionWeight_le_rawKernel
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
        (globalInwardMateFirstOSEdgeFiber representative) <=
      centralPhysicalReflectedKernel anchorCoupling K 0
        (sourceLower representative) (commonRight representative) := by
  have hinjection := listQSum_le_of_injective_nodup
    (globalInwardMateFirstOSEdgeFiber representative)
    (globalInwardMateOSEdgeWitnesses K
      (sourceLower representative) (commonRight representative))
    GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
    (globalInwardMateOSEdgeWitnessWeight K
      (sourceLower representative) (commonRight representative))
    globalInwardMateFirstOSEdgeWitnessEncode
    (List.filter_sublist.nodup
      (globalCubeInwardMateCertifiedTargetFullSources_nodup K hK))
    (globalInwardMateOSEdgeWitnesses_nodup K
      (sourceLower representative) (commonRight representative))
    (fun source hsource =>
      globalInwardMateFirstOSEdgeWitnessEncode_mem
        representative source hsource)
    (fun left hleft right hright heq =>
      globalInwardMateFirstOSEdgeWitnessEncode_injective
        representative left hleft right hright heq)
    (fun source hsource => by
      have hstates := globalInwardMateFirstOSEdgeFiber_states_eq hsource
      have hphysical :
          assembleReflectedSlabLabelling 0 (sourceLower representative)
              (commonBoundary source) (commonRight representative) =
            source.physical := by
        rw [hstates.1, hstates.2]
        exact assemble_source_path source
      exact Q'.le_of_eqv (Q'.eqv_of_eq (by
        unfold GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
          slabExpandedFineSourceWeight
          GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom
          globalInwardMateFirstOSEdgeWitnessEncode
          globalInwardMateOSEdgeWitnessWeight
        rw [hphysical])))
    (fun entry _ =>
      retainedFineIntertwinerPhysicalFiberWeight_nonnegative
        (by decide) K 0
        (assembleReflectedSlabLabelling 0
          (sourceLower representative) entry.1 (commonRight representative))
        entry.2)
  exact Q'.le_trans' _ _ _ hinjection
    (Q'.le_of_eqv
      (globalInwardMateOSEdgeWitnesses_weight_eqv_rawKernel K
        (sourceLower representative) (commonRight representative)))

/-! ## 4. The aggregate normalized first-edge capacity -/

theorem globalInwardMateFirstOSEdgeFiber_traffic_le_normalizedKernel
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    listQSum globalInwardMateSourceTraffic
        (globalInwardMateFirstOSEdgeFiber representative) <=
      centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0
          (sourceLower representative) (commonRight representative) := by
  let partition := slabParametricKPhysicalPartition anchorCoupling K 1
  let reciprocal := Q'.recipPos partition
    (slabParametricKPhysicalPartition_pos (by decide) K 1)
  have hsum :
      listQSum globalInwardMateSourceTraffic
          (globalInwardMateFirstOSEdgeFiber representative) ≈
        listQSum
            GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
            (globalInwardMateFirstOSEdgeFiber representative) * reciprocal := by
    unfold globalInwardMateSourceTraffic Q'.divPos reciprocal partition
    exact listQSum_mul_right
      GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
      (Q'.recipPos
        (slabParametricKPhysicalPartition anchorCoupling K 1)
        (slabParametricKPhysicalPartition_pos (by decide) K 1))
      (globalInwardMateFirstOSEdgeFiber representative)
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ reciprocal
    (globalInwardMateFirstOSEdgeFiber_productionWeight_le_rawKernel
      representative)
    (Q'.le_of_lt
      (Q'.recipPos_pos partition
        (slabParametricKPhysicalPartition_pos (by decide) K 1)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (by
      unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
      simpa [partition, reciprocal, centralExtent] using Q'.eqv_refl
        (centralPhysicalReflectedKernel anchorCoupling K 0
          (sourceLower representative) (commonRight representative) *
          Q'.recipPos
            (slabParametricKPhysicalPartition anchorCoupling K 1)
            (slabParametricKPhysicalPartition_pos (by decide) K 1)))))

#print axioms globalInwardMateFirstOSEdgeKey
#print axioms globalInwardMateFirstOSEdgeFiber_states_eq
#print axioms globalInwardMateOSEdgeWitnesses_nodup
#print axioms globalInwardMateOSEdgeWitnesses_weight_eqv_rawKernel
#print axioms globalInwardMateFirstOSEdgeWitnessEncode_mem
#print axioms globalInwardMateFirstOSEdgeWitnessEncode_injective
#print axioms globalInwardMateFirstOSEdgeFiber_productionWeight_le_rawKernel
#print axioms globalInwardMateFirstOSEdgeFiber_traffic_le_normalizedKernel

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSFirstEdgeLoad
