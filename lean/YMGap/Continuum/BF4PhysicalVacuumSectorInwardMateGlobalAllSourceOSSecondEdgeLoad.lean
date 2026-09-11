/-
# Aggregate second-edge load of the all-source inward-mate OS flow

The normalized-flow theorem controls all sources that compile to one exact
production target.  Several distinct production targets can nevertheless
forget to the same second physical OS edge.  This module performs that second
aggregation without a cardinality loss.

First, exact production-target representatives are partitioned by their
literal `(targetLower, commonRight)` OS edge.  Distinct representatives over
one such edge inject into distinct `(boundary, fine-intertwiner witness)`
summands of the raw kernel.  Their normalized target units therefore sum to
at most the actual symmetric OS joint capacity.  Summing the already proved
target-class congestion estimate then bounds the complete second-edge load by
`globalInwardMateTransportCost` times that capacity.

Two exact representative-partition identities prove that these edge loads
count every selected source traffic term exactly once.  This closes both edge
loads of the selected flow.  It does not identify that selected demand with
the full pairwise variance, prove a Poincare inequality, spectral gap,
beta/lattice-spacing uniformity, continuum limit, or Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSFirstEdgeLoad
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFubini

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSSecondEdgeLoad

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSEdgeCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSFirstEdgeLoad
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSNormalizedFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionCongestion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionTransport
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFraction
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
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

private theorem nodup_of_map_nodup_local
    {A B : Type} (map : A -> B) : forall {items : List A},
    (items.map map).Nodup -> items.Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_of_map_nodup_local map hparts.2⟩
      intro hmem
      exact hparts.1 (List.mem_map.mpr ⟨head, hmem, rfl⟩)

private theorem listQSum_congr_mem_local
    {A : Type} {left right : A -> Q'} : forall items : List A,
    (forall item, item ∈ items -> left item ≈ right item) ->
      listQSum left items ≈ listQSum right items
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hagree =>
      Q'.add_eqv_congr'
        (hagree head List.mem_cons_self)
        (listQSum_congr_mem_local tail
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A -> Q') : forall items : List A,
    (forall item, item ∈ items -> left item <= right item) ->
      listQSum left items <= listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hpoint =>
      Q'.add_le_add
        (hpoint head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem =>
            hpoint item (List.mem_cons_of_mem head hitem)))

/-! ## 1. Exact target representatives over one second OS edge -/

def globalInwardMateSecondOSEdgeKey
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    GlobalInwardMateOSEdgeKey :=
  (finiteEdgeLabellingWord (centralLowerFaceIds 0) (targetLower source),
    finiteEdgeLabellingWord (centralLowerFaceIds 0) (commonRight source))

def globalInwardMateSecondOSEdgeTargetFiber
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    List (GlobalCubeInwardMateCertifiedTargetFullSource K hK) :=
  representativeFiber (globalInwardMateTargetRepresentatives K hK)
    globalInwardMateSecondOSEdgeKey representative

def globalInwardMateSecondOSEdgeRepresentatives
    (K : Nat) (hK : 1 <= K) :
    List (GlobalCubeInwardMateCertifiedTargetFullSource K hK) :=
  keyRepresentatives globalInwardMateSecondOSEdgeKey
    (globalInwardMateTargetRepresentatives K hK)

theorem globalInwardMateSecondOSEdgeTargetFiber_mem_targetRepresentative
    {K : Nat} {hK : 1 <= K}
    {representative source :
      GlobalCubeInwardMateCertifiedTargetFullSource K hK}
    (hsource : source ∈
      globalInwardMateSecondOSEdgeTargetFiber representative) :
    source ∈ globalInwardMateTargetRepresentatives K hK := by
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

theorem globalInwardMateSecondOSEdgeTargetFiber_states_eq
    {K : Nat} {hK : 1 <= K}
    {representative source :
      GlobalCubeInwardMateCertifiedTargetFullSource K hK}
    (hsource : source ∈
      globalInwardMateSecondOSEdgeTargetFiber representative) :
    targetLower representative = targetLower source /\
      commonRight representative = commonRight source := by
  have hkey : globalInwardMateSecondOSEdgeKey representative =
      globalInwardMateSecondOSEdgeKey source :=
    of_decide_eq_true (List.mem_filter.mp hsource).2
  constructor
  · apply supportedHalf_eq_of_word_eq
      (targetLower_mem representative) (targetLower_mem source)
    exact congrArg Prod.fst hkey
  · apply supportedHalf_eq_of_word_eq
      (commonRight_mem representative) (commonRight_mem source)
    exact congrArg Prod.snd hkey

theorem globalInwardMateTargetRepresentatives_nodup
    (K : Nat) (hK : 1 <= K) :
    (globalInwardMateTargetRepresentatives K hK).Nodup := by
  unfold globalInwardMateTargetRepresentatives
  apply nodup_of_map_nodup_local globalInwardMateTargetKey
  exact keyRepresentatives_keys_nodup globalInwardMateTargetKey
    (globalCubeInwardMateCertifiedTargetFullSources K hK)

/-! ## 2. Inject the distinct target atoms into complete OS summands -/

def globalInwardMateSecondOSEdgeWitnessEncode
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    GlobalInwardMateOSEdgeWitness :=
  (commonBoundary source,
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw source)

theorem globalInwardMateSecondOSEdgeWitnessEncode_mem
    {K : Nat} {hK : 1 <= K}
    (representative source :
      GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈
      globalInwardMateSecondOSEdgeTargetFiber representative) :
    globalInwardMateSecondOSEdgeWitnessEncode source ∈
      globalInwardMateOSEdgeWitnesses K
        (targetLower representative) (commonRight representative) := by
  have hstates := globalInwardMateSecondOSEdgeTargetFiber_states_eq hsource
  have hphysical :
      assembleReflectedSlabLabelling 0 (targetLower representative)
          (commonBoundary source) (commonRight representative) =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source := by
    rw [hstates.1, hstates.2]
    exact assemble_target_path source
  have hrepresentative :=
    globalInwardMateSecondOSEdgeTargetFiber_mem_targetRepresentative hsource
  unfold globalInwardMateOSEdgeWitnesses
  apply List.mem_flatMap.mpr
  refine ⟨commonBoundary source, commonBoundary_mem source, ?_⟩
  unfold globalInwardMateOSEdgeWitnessBlock
  apply List.mem_map.mpr
  refine ⟨GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw
    source, ?_, rfl⟩
  rw [hphysical]
  exact
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw_mem
      source hrepresentative

theorem globalInwardMateSecondOSEdgeWitnessEncode_injective
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (left : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hleft : left ∈
      globalInwardMateSecondOSEdgeTargetFiber representative)
    (right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hright : right ∈
      globalInwardMateSecondOSEdgeTargetFiber representative)
    (heq : globalInwardMateSecondOSEdgeWitnessEncode left =
      globalInwardMateSecondOSEdgeWitnessEncode right) :
    left = right := by
  have hleftStates := globalInwardMateSecondOSEdgeTargetFiber_states_eq hleft
  have hrightStates := globalInwardMateSecondOSEdgeTargetFiber_states_eq hright
  have hboundary : commonBoundary left = commonBoundary right :=
    congrArg Prod.fst heq
  have hraw :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionRaw right := by
    have hprojection := congrArg Prod.snd heq
    simpa only [globalInwardMateSecondOSEdgeWitnessEncode] using hprojection
  have hphysical :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right := by
    calc
      GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left =
          assembleReflectedSlabLabelling 0 (targetLower left)
            (commonBoundary left) (commonRight left) :=
        (assemble_target_path left).symm
      _ = assembleReflectedSlabLabelling 0 (targetLower right)
            (commonBoundary right) (commonRight right) := by
        rw [← hleftStates.1, ← hrightStates.1,
          ← hleftStates.2, ← hrightStates.2, hboundary]
      _ = GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right :=
        assemble_target_path right
  apply globalInwardMateTargetProductionAtom_injective
    left (globalInwardMateSecondOSEdgeTargetFiber_mem_targetRepresentative hleft)
    right (globalInwardMateSecondOSEdgeTargetFiber_mem_targetRepresentative hright)
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom
  exact pair_eq_of_fields_eq_local hphysical hraw

theorem globalInwardMateSecondOSEdgeTargetFiber_targetWeight_le_rawKernel
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
        (globalInwardMateSecondOSEdgeTargetFiber representative) <=
      centralPhysicalReflectedKernel anchorCoupling K 0
        (targetLower representative) (commonRight representative) := by
  have hinjection := listQSum_le_of_injective_nodup
    (globalInwardMateSecondOSEdgeTargetFiber representative)
    (globalInwardMateOSEdgeWitnesses K
      (targetLower representative) (commonRight representative))
    GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
    (globalInwardMateOSEdgeWitnessWeight K
      (targetLower representative) (commonRight representative))
    globalInwardMateSecondOSEdgeWitnessEncode
    (List.filter_sublist.nodup
      (globalInwardMateTargetRepresentatives_nodup K hK))
    (globalInwardMateOSEdgeWitnesses_nodup K
      (targetLower representative) (commonRight representative))
    (fun source hsource =>
      globalInwardMateSecondOSEdgeWitnessEncode_mem
        representative source hsource)
    (fun left hleft right hright heq =>
      globalInwardMateSecondOSEdgeWitnessEncode_injective
        representative left hleft right hright heq)
    (fun source hsource => by
      have hstates := globalInwardMateSecondOSEdgeTargetFiber_states_eq hsource
      have hphysical :
          assembleReflectedSlabLabelling 0 (targetLower representative)
              (commonBoundary source) (commonRight representative) =
            GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source := by
        rw [hstates.1, hstates.2]
        exact assemble_target_path source
      exact Q'.le_of_eqv (Q'.eqv_of_eq (by
        unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
          slabExpandedFineSourceWeight
          GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionAtom
          globalInwardMateSecondOSEdgeWitnessEncode
          globalInwardMateOSEdgeWitnessWeight
        rw [hphysical])))
    (fun entry _ =>
      retainedFineIntertwinerPhysicalFiberWeight_nonnegative
        (by decide) K 0
        (assembleReflectedSlabLabelling 0
          (targetLower representative) entry.1 (commonRight representative))
        entry.2)
  exact Q'.le_trans' _ _ _ hinjection
    (Q'.le_of_eqv
      (globalInwardMateOSEdgeWitnesses_weight_eqv_rawKernel K
        (targetLower representative) (commonRight representative)))

theorem globalInwardMateSecondOSEdgeTargetFiber_units_le_normalizedKernel
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    listQSum globalInwardMateTargetEdgeUnit
        (globalInwardMateSecondOSEdgeTargetFiber representative) <=
      centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0
          (targetLower representative) (commonRight representative) := by
  let partition := slabParametricKPhysicalPartition anchorCoupling K 1
  let reciprocal := Q'.recipPos partition
    (slabParametricKPhysicalPartition_pos (by decide) K 1)
  have hsum :
      listQSum globalInwardMateTargetEdgeUnit
          (globalInwardMateSecondOSEdgeTargetFiber representative) ≈
        listQSum
            GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
            (globalInwardMateSecondOSEdgeTargetFiber representative) * reciprocal := by
    unfold globalInwardMateTargetEdgeUnit Q'.divPos reciprocal partition
    exact listQSum_mul_right
      GlobalCubeInwardMateCertifiedTargetFullSource.targetProductionWeight
      (Q'.recipPos
        (slabParametricKPhysicalPartition anchorCoupling K 1)
        (slabParametricKPhysicalPartition_pos (by decide) K 1))
      (globalInwardMateSecondOSEdgeTargetFiber representative)
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ reciprocal
    (globalInwardMateSecondOSEdgeTargetFiber_targetWeight_le_rawKernel
      representative)
    (Q'.le_of_lt
      (Q'.recipPos_pos partition
        (slabParametricKPhysicalPartition_pos (by decide) K 1)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (by
      unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
      simpa [partition, reciprocal, centralExtent] using Q'.eqv_refl
        (centralPhysicalReflectedKernel anchorCoupling K 0
          (targetLower representative) (commonRight representative) *
          Q'.recipPos
            (slabParametricKPhysicalPartition anchorCoupling K 1)
            (slabParametricKPhysicalPartition_pos (by decide) K 1)))))

/-! ## 3. Exact two-level partition and aggregate second-edge load -/

def globalInwardMateTargetClassTraffic
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Q' :=
  listQSum globalInwardMateSourceTraffic
    (globalInwardMateProductionTargetFiber representative)

def globalInwardMateSecondOSEdgeLoad
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Q' :=
  listQSum globalInwardMateTargetClassTraffic
    (globalInwardMateSecondOSEdgeTargetFiber representative)

theorem globalInwardMateTargetClassTraffic_total
    (K : Nat) (hK : 1 <= K) :
    listQSum globalInwardMateTargetClassTraffic
        (globalInwardMateTargetRepresentatives K hK) ≈
      listQSum globalInwardMateSourceTraffic
        (globalCubeInwardMateCertifiedTargetFullSources K hK) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun representative =>
        listQSum globalInwardMateSourceTraffic
          (representativeFiber
            (globalCubeInwardMateCertifiedTargetFullSources K hK)
            globalInwardMateTargetKey representative))
      (globalInwardMateTargetRepresentatives K hK)) _ ?_ ?_
  · apply listQSum_congr
    intro representative
    unfold globalInwardMateTargetClassTraffic
    rw [globalInwardMateProductionTargetFiber_eq_targetFiber,
      ← globalInwardMateRepresentativeFiber_eq_targetFiber]
    exact Q'.eqv_refl _
  · unfold globalInwardMateTargetRepresentatives
    exact keyRepresentativeFibers_weight_total
      (globalCubeInwardMateCertifiedTargetFullSources K hK)
      globalInwardMateSourceTraffic globalInwardMateTargetKey

theorem globalInwardMateSecondOSEdgeLoads_total
    (K : Nat) (hK : 1 <= K) :
    listQSum globalInwardMateSecondOSEdgeLoad
        (globalInwardMateSecondOSEdgeRepresentatives K hK) ≈
      listQSum globalInwardMateSourceTraffic
        (globalCubeInwardMateCertifiedTargetFullSources K hK) := by
  refine Q'.eqv_trans _
    (listQSum globalInwardMateTargetClassTraffic
      (globalInwardMateTargetRepresentatives K hK)) _ ?_ ?_
  · unfold globalInwardMateSecondOSEdgeLoad
      globalInwardMateSecondOSEdgeTargetFiber
      globalInwardMateSecondOSEdgeRepresentatives
    exact keyRepresentativeFibers_weight_total
      (globalInwardMateTargetRepresentatives K hK)
      globalInwardMateTargetClassTraffic globalInwardMateSecondOSEdgeKey
  · exact globalInwardMateTargetClassTraffic_total K hK

theorem globalInwardMateSecondOSEdgeLoad_le_capacity
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    globalInwardMateSecondOSEdgeLoad representative <=
      globalInwardMateTransportCost *
        centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0
            (targetLower representative) (commonRight representative) := by
  have hclasses :
      globalInwardMateSecondOSEdgeLoad representative <=
        listQSum
          (fun targetRepresentative =>
            globalInwardMateTransportCost *
              globalInwardMateTargetEdgeUnit targetRepresentative)
          (globalInwardMateSecondOSEdgeTargetFiber representative) := by
    unfold globalInwardMateSecondOSEdgeLoad
      globalInwardMateTargetClassTraffic
    apply listQSum_le_termwise_local
    intro targetRepresentative _
    exact globalInwardMateProductionTargetFiber_sourceTraffic_le
      targetRepresentative
  have hfactor :
      listQSum
          (fun targetRepresentative =>
            globalInwardMateTransportCost *
              globalInwardMateTargetEdgeUnit targetRepresentative)
          (globalInwardMateSecondOSEdgeTargetFiber representative) ≈
        globalInwardMateTransportCost *
          listQSum globalInwardMateTargetEdgeUnit
            (globalInwardMateSecondOSEdgeTargetFiber representative) :=
    listQSum_mul_left globalInwardMateTransportCost
      globalInwardMateTargetEdgeUnit
      (globalInwardMateSecondOSEdgeTargetFiber representative)
  have hcapacity := Q'.mul_le_mul_of_nonneg_left _ _
    globalInwardMateTransportCost
    (globalInwardMateSecondOSEdgeTargetFiber_units_le_normalizedKernel
      representative)
    (Q'.le_of_lt globalInwardMateTransportCost_positive)
  exact Q'.le_trans' _ _ _ hclasses
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) hcapacity)

/-! ## 4. Witness-bearing complete selected-flow load certificate -/

structure GlobalInwardMateAllSourceOSTwoEdgeLoadCertificate
    (K : Nat) (hK : 1 <= K) : Type where
  sources : List (GlobalCubeInwardMateCertifiedTargetFullSource K hK)
  edgeRepresentatives :
    List (GlobalCubeInwardMateCertifiedTargetFullSource K hK)
  traffic : GlobalCubeInwardMateCertifiedTargetFullSource K hK -> Q'
  edgeLoad : GlobalCubeInwardMateCertifiedTargetFullSource K hK -> Q'
  sources_eq : sources = globalCubeInwardMateCertifiedTargetFullSources K hK
  edgeRepresentatives_eq : edgeRepresentatives =
    globalInwardMateSecondOSEdgeRepresentatives K hK
  traffic_eq : forall source, traffic source ≈ globalInwardMateSourceTraffic source
  edgeLoad_eq : forall representative,
    edgeLoad representative ≈ globalInwardMateSecondOSEdgeLoad representative
  total_lower : Q'.mkPos 41 425 (by decide) <= listQSum traffic sources
  edgeLoads_total : listQSum edgeLoad edgeRepresentatives ≈
    listQSum traffic sources
  first_capacity : forall representative,
    listQSum traffic (globalInwardMateFirstOSEdgeFiber representative) <=
      centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0
          (sourceLower representative) (commonRight representative)
  second_capacity : forall representative,
    edgeLoad representative <=
      globalInwardMateTransportCost *
        centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0
            (targetLower representative) (commonRight representative)

def globalInwardMateAllSourceOSTwoEdgeLoadCertificate
    (K : Nat) (hK : 1 <= K) :
    GlobalInwardMateAllSourceOSTwoEdgeLoadCertificate K hK :=
  { sources := globalCubeInwardMateCertifiedTargetFullSources K hK
    edgeRepresentatives := globalInwardMateSecondOSEdgeRepresentatives K hK
    traffic := globalInwardMateSourceTraffic
    edgeLoad := globalInwardMateSecondOSEdgeLoad
    sources_eq := rfl
    edgeRepresentatives_eq := rfl
    traffic_eq := fun _ => Q'.eqv_refl _
    edgeLoad_eq := fun _ => Q'.eqv_refl _
    total_lower := globalInwardMateSuccessRate_le_allSourceTraffic K hK
    edgeLoads_total := globalInwardMateSecondOSEdgeLoads_total K hK
    first_capacity := globalInwardMateFirstOSEdgeFiber_traffic_le_normalizedKernel
    second_capacity := globalInwardMateSecondOSEdgeLoad_le_capacity }

#print axioms globalInwardMateSecondOSEdgeKey
#print axioms globalInwardMateSecondOSEdgeTargetFiber_states_eq
#print axioms globalInwardMateTargetRepresentatives_nodup
#print axioms globalInwardMateSecondOSEdgeWitnessEncode_mem
#print axioms globalInwardMateSecondOSEdgeWitnessEncode_injective
#print axioms globalInwardMateSecondOSEdgeTargetFiber_targetWeight_le_rawKernel
#print axioms globalInwardMateSecondOSEdgeTargetFiber_units_le_normalizedKernel
#print axioms globalInwardMateTargetClassTraffic_total
#print axioms globalInwardMateSecondOSEdgeLoads_total
#print axioms globalInwardMateSecondOSEdgeLoad_le_capacity
#print axioms globalInwardMateAllSourceOSTwoEdgeLoadCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSSecondEdgeLoad
