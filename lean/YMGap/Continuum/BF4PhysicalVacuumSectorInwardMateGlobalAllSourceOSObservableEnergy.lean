/-
# Arbitrary-observable energy carried by the inward-mate OS flow

The preceding parity argument used an exact Boolean identity to obtain a
particularly sharp one-vector bound.  This module records the part of the
flow argument that is valid for every rational observable.

For any coefficient `f`, the selected source-to-target squared oscillation is
at most twice the sum of the two path-edge squared oscillations.  The already
proved aggregate first- and second-edge congestion estimates then embed those
two energies in the actual normalized physical OS Dirichlet form.  Thus

  selectedEndpointEnergy(f) <= 2 * (1 + transportCost) * Dirichlet(f).

The final structure names the exact remaining mathematical input: a positive,
cutoff-independent comparison from the full centered physical norm to this
selected endpoint energy.  No inhabitant of that all-vector coverage
structure is asserted here.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFormGap
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy
import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorCongestion

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSObservableEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSEdgeCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSFirstEdgeLoad
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSNormalizedFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFirstEdgeEnergy
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFormGap
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParitySecondEdgeEnergy
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSSecondEdgeLoad
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionCongestion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFraction
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionPair
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionSourceMarginal
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorCongestion
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

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
          (fun item hitem => hagree item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A -> Q') : forall items : List A,
    (forall item, item ∈ items -> left item <= right item) ->
      listQSum left items <= listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hpoint =>
      Q'.add_le_add
        (hpoint head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hpoint item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_cartesian_eq_nested_local
    {A B : Type} (value : A × B -> Q')
    (left : List A) (right : List B) :
    listQSum value (cartesian left right) ≈
      listQSum (fun a => listQSum (fun b => value (a, b)) right) left := by
  unfold cartesian
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap value (fun a => right.map (fun b => (a, b))) left) ?_
  apply listQSum_congr
  intro a
  rw [listQSum_map]
  exact Q'.eqv_refl _

private theorem square_eqv_congr_local {left right : Q'}
    (heq : left ≈ right) : left * left ≈ right * right := by
  exact Q'.eqv_trans _ (right * left) _
    (Q'.mul_eqv_congr_right left right left heq)
    (Q'.mul_eqv_congr_left right left right heq)

/-! ## 1. Arbitrary observable gradients -/

def observableSquaredDifference
    (coefficient : EdgeLabelling -> Q')
    (left right : EdgeLabelling) : Q' :=
  (coefficient left + -coefficient right) *
    (coefficient left + -coefficient right)

theorem observableSquaredDifference_nonnegative
    (coefficient : EdgeLabelling -> Q')
    (left right : EdgeLabelling) :
    (0 : Q') <= observableSquaredDifference coefficient left right := by
  unfold observableSquaredDifference
  exact YMGap.Constructive.SumOfSquares.q_mul_self_nonneg _

theorem observableSquaredDifference_symm
    (coefficient : EdgeLabelling -> Q')
    (left right : EdgeLabelling) :
    observableSquaredDifference coefficient left right ≈
      observableSquaredDifference coefficient right left := by
  unfold observableSquaredDifference
  q_ring

theorem globalInwardMateSourceTraffic_nonnegative
    {K : Nat} {hK : 1 <= K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    (0 : Q') <= globalInwardMateSourceTraffic source := by
  unfold globalInwardMateSourceTraffic Q'.divPos
  exact Q'.mul_nonneg _ _
    (slabExpandedFineSourceWeight_nonnegative
      (globalInwardMateAnchorSlabData K)
      (GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionAtom
        source))
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (slabParametricKPhysicalPartition_pos (by decide) K 1)))

/-! ## 2. First-edge energy for every observable -/

def globalInwardMateSelectedFirstObservableEnergyTerm
    {K : Nat} {hK : 1 <= K}
    (coefficient : EdgeLabelling -> Q')
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Q' :=
  globalInwardMateSourceTraffic source *
    observableSquaredDifference coefficient
      (sourceLower source) (commonRight source)

def globalInwardMateSelectedFirstObservableEnergy
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') : Q' :=
  listQSum (globalInwardMateSelectedFirstObservableEnergyTerm coefficient)
    (globalCubeInwardMateCertifiedTargetFullSources K hK)

def globalInwardMateUsedFirstObservableEnergy
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') : Q' :=
  listQSum
    (fun representative =>
      globalInwardMateFirstOSEdgeLoad representative *
        observableSquaredDifference coefficient
          (sourceLower representative) (commonRight representative))
    (globalInwardMateFirstOSEdgeRepresentatives K hK)

def globalInwardMateUsedFirstObservableCapacityEnergy
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') : Q' :=
  listQSum
    (fun representative =>
      centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0
          (sourceLower representative) (commonRight representative) *
        observableSquaredDifference coefficient
          (sourceLower representative) (commonRight representative))
    (globalInwardMateFirstOSEdgeRepresentatives K hK)

theorem globalInwardMateFirstOSEdgeFiber_observableEnergy_eqv
    {K : Nat} {hK : 1 <= K}
    (coefficient : EdgeLabelling -> Q')
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    listQSum (globalInwardMateSelectedFirstObservableEnergyTerm coefficient)
        (globalInwardMateFirstOSEdgeFiber representative) ≈
      globalInwardMateFirstOSEdgeLoad representative *
        observableSquaredDifference coefficient
          (sourceLower representative) (commonRight representative) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        globalInwardMateSourceTraffic source *
          observableSquaredDifference coefficient
            (sourceLower representative) (commonRight representative))
      (globalInwardMateFirstOSEdgeFiber representative)) _ ?_ ?_
  · apply listQSum_congr_mem_local
    intro source hsource
    have hstates := globalInwardMateFirstOSEdgeFiber_states_eq hsource
    unfold globalInwardMateSelectedFirstObservableEnergyTerm
    apply Q'.mul_eqv_congr_left
    rw [← hstates.1, ← hstates.2]
    exact Q'.eqv_refl _
  · unfold globalInwardMateFirstOSEdgeLoad
    exact listQSum_mul_right globalInwardMateSourceTraffic
      (observableSquaredDifference coefficient
        (sourceLower representative) (commonRight representative))
      (globalInwardMateFirstOSEdgeFiber representative)

theorem globalInwardMateUsedFirstObservableEnergy_eqv_selected
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') :
    globalInwardMateUsedFirstObservableEnergy K hK coefficient ≈
      globalInwardMateSelectedFirstObservableEnergy K hK coefficient := by
  refine Q'.eqv_trans _
    (listQSum
      (fun representative =>
        listQSum (globalInwardMateSelectedFirstObservableEnergyTerm coefficient)
          (globalInwardMateFirstOSEdgeFiber representative))
      (globalInwardMateFirstOSEdgeRepresentatives K hK)) _ ?_ ?_
  · apply listQSum_congr
    intro representative
    exact Q'.eqv_symm
      (globalInwardMateFirstOSEdgeFiber_observableEnergy_eqv
        coefficient representative)
  · unfold globalInwardMateFirstOSEdgeRepresentatives
      globalInwardMateFirstOSEdgeFiber
      globalInwardMateSelectedFirstObservableEnergy
    exact keyRepresentativeFibers_weight_total
      (globalCubeInwardMateCertifiedTargetFullSources K hK)
      (globalInwardMateSelectedFirstObservableEnergyTerm coefficient)
      globalInwardMateFirstOSEdgeKey

theorem globalInwardMateUsedFirstObservableEnergy_le_capacity
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') :
    globalInwardMateUsedFirstObservableEnergy K hK coefficient <=
      globalInwardMateUsedFirstObservableCapacityEnergy K hK coefficient := by
  unfold globalInwardMateUsedFirstObservableEnergy
    globalInwardMateUsedFirstObservableCapacityEnergy
  apply listQSum_le_termwise_local
  intro representative _
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (globalInwardMateFirstOSEdgeFiber_traffic_le_normalizedKernel
      representative)
    (observableSquaredDifference_nonnegative coefficient _ _)

theorem globalInwardMateUsedFirstObservableCapacityEnergy_le_Dirichlet
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') :
    globalInwardMateUsedFirstObservableCapacityEnergy K hK coefficient <=
      finiteJointDirichletEnergy (centralHalfStates K 0) coefficient
        (centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0) := by
  let states := centralHalfStates K 0
  let representatives := globalInwardMateFirstOSEdgeRepresentatives K hK
  let edgeTerm : EdgeLabelling × EdgeLabelling -> Q' := fun edge =>
    centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0 edge.1 edge.2 *
      observableSquaredDifference coefficient edge.1 edge.2
  have hrepresentatives : representatives.Nodup := by
    unfold representatives globalInwardMateFirstOSEdgeRepresentatives
    apply nodup_of_map_nodup_local globalInwardMateFirstOSEdgeKey
    exact keyRepresentatives_keys_nodup globalInwardMateFirstOSEdgeKey
      (globalCubeInwardMateCertifiedTargetFullSources K hK)
  have hinjection := listQSum_le_of_injective_nodup
    representatives (cartesian states states)
    (fun representative => edgeTerm
      (globalInwardMateFirstOSEdgePair representative))
    edgeTerm globalInwardMateFirstOSEdgePair
    hrepresentatives
    (cartesian_nodup states states
      (by unfold states; exact centralHalfStates_nodup K 0)
      (by unfold states; exact centralHalfStates_nodup K 0))
    (fun representative _ => by
      apply (mem_cartesian_iff states states _).mpr
      exact ⟨sourceLower_mem representative, commonRight_mem representative⟩)
    (fun left hleft right hright heq =>
      globalInwardMateFirstOSEdgePair_injective
        left hleft right hright heq)
    (fun _ _ => Q'.le_refl' _)
    (fun edge _ =>
      Q'.mul_nonneg _ _
        (centralNormalizedPhysicalReflectedKernel_nonnegative
          (by decide) K 0 edge.1 edge.2)
        (observableSquaredDifference_nonnegative coefficient edge.1 edge.2))
  have htarget : listQSum edgeTerm (cartesian states states) ≈
      finiteJointDirichletEnergy states coefficient
        (centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0) := by
    refine Q'.eqv_trans _
      (listQSum (fun left => listQSum (fun right => edgeTerm (left, right)) states)
        states) _ (listQSum_cartesian_eq_nested_local edgeTerm states states) ?_
    unfold finiteJointDirichletEnergy edgeTerm observableSquaredDifference
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ hinjection (Q'.le_of_eqv htarget)

theorem globalInwardMateSelectedFirstObservableEnergy_le_Dirichlet
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') :
    globalInwardMateSelectedFirstObservableEnergy K hK coefficient <=
      finiteJointDirichletEnergy (centralHalfStates K 0) coefficient
        (centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (globalInwardMateUsedFirstObservableEnergy_eqv_selected
          K hK coefficient)))
    (Q'.le_trans' _ _ _
      (globalInwardMateUsedFirstObservableEnergy_le_capacity
        K hK coefficient)
      (globalInwardMateUsedFirstObservableCapacityEnergy_le_Dirichlet
        K hK coefficient))

/-! ## 3. Second-edge energy for every observable -/

def globalInwardMateSelectedSecondObservableEnergyTerm
    {K : Nat} {hK : 1 <= K}
    (coefficient : EdgeLabelling -> Q')
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Q' :=
  globalInwardMateSourceTraffic source *
    observableSquaredDifference coefficient
      (commonRight source) (targetLower source)

def globalInwardMateSelectedSecondObservableEnergy
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') : Q' :=
  listQSum (globalInwardMateSelectedSecondObservableEnergyTerm coefficient)
    (globalCubeInwardMateCertifiedTargetFullSources K hK)

def globalInwardMateTargetClassSecondObservableEnergy
    {K : Nat} {hK : 1 <= K}
    (coefficient : EdgeLabelling -> Q')
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Q' :=
  globalInwardMateTargetClassTraffic representative *
    observableSquaredDifference coefficient
      (targetLower representative) (commonRight representative)

def globalInwardMateTargetRepresentativeSecondObservableEnergy
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') : Q' :=
  listQSum (globalInwardMateTargetClassSecondObservableEnergy coefficient)
    (globalInwardMateTargetRepresentatives K hK)

def globalInwardMateUsedSecondObservableEnergy
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') : Q' :=
  listQSum
    (fun representative =>
      globalInwardMateSecondOSEdgeLoad representative *
        observableSquaredDifference coefficient
          (targetLower representative) (commonRight representative))
    (globalInwardMateSecondOSEdgeRepresentatives K hK)

def globalInwardMateUsedSecondObservableCapacityEnergy
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') : Q' :=
  listQSum
    (fun representative =>
      centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0
          (targetLower representative) (commonRight representative) *
        observableSquaredDifference coefficient
          (targetLower representative) (commonRight representative))
    (globalInwardMateSecondOSEdgeRepresentatives K hK)

theorem globalInwardMateProductionTargetFiber_secondObservableEnergy_eqv
    {K : Nat} {hK : 1 <= K}
    (coefficient : EdgeLabelling -> Q')
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    listQSum (globalInwardMateSelectedSecondObservableEnergyTerm coefficient)
        (globalInwardMateProductionTargetFiber representative) ≈
      globalInwardMateTargetClassSecondObservableEnergy
        coefficient representative := by
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        globalInwardMateSourceTraffic source *
          observableSquaredDifference coefficient
            (targetLower representative) (commonRight representative))
      (globalInwardMateProductionTargetFiber representative)) _ ?_ ?_
  · apply listQSum_congr_mem_local
    intro source hsource
    have hstates := globalInwardMateProductionTargetFiber_states_eq hsource
    unfold globalInwardMateSelectedSecondObservableEnergyTerm
    apply Q'.mul_eqv_congr_left
    rw [← hstates.1, ← hstates.2]
    exact observableSquaredDifference_symm coefficient _ _
  · unfold globalInwardMateTargetClassSecondObservableEnergy
      globalInwardMateTargetClassTraffic
    exact listQSum_mul_right globalInwardMateSourceTraffic
      (observableSquaredDifference coefficient
        (targetLower representative) (commonRight representative))
      (globalInwardMateProductionTargetFiber representative)

theorem globalInwardMateTargetRepresentativeSecondObservableEnergy_eqv_selected
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') :
    globalInwardMateTargetRepresentativeSecondObservableEnergy
        K hK coefficient ≈
      globalInwardMateSelectedSecondObservableEnergy K hK coefficient := by
  refine Q'.eqv_trans _
    (listQSum
      (fun representative =>
        listQSum (globalInwardMateSelectedSecondObservableEnergyTerm coefficient)
          (globalInwardMateProductionTargetFiber representative))
      (globalInwardMateTargetRepresentatives K hK)) _ ?_ ?_
  · apply listQSum_congr
    intro representative
    exact Q'.eqv_symm
      (globalInwardMateProductionTargetFiber_secondObservableEnergy_eqv
        coefficient representative)
  refine Q'.eqv_trans _
    (listQSum
      (fun representative =>
        listQSum (globalInwardMateSelectedSecondObservableEnergyTerm coefficient)
          (representativeFiber
            (globalCubeInwardMateCertifiedTargetFullSources K hK)
            globalInwardMateTargetKey representative))
      (globalInwardMateTargetRepresentatives K hK)) _ ?_ ?_
  · apply listQSum_congr
    intro representative
    rw [globalInwardMateProductionTargetFiber_eq_targetFiber,
      ← globalInwardMateRepresentativeFiber_eq_targetFiber]
    exact Q'.eqv_refl _
  · unfold globalInwardMateSelectedSecondObservableEnergy
      globalInwardMateTargetRepresentatives
    exact keyRepresentativeFibers_weight_total
      (globalCubeInwardMateCertifiedTargetFullSources K hK)
      (globalInwardMateSelectedSecondObservableEnergyTerm coefficient)
      globalInwardMateTargetKey

theorem globalInwardMateSecondOSEdgeTargetFiber_observableEnergy_eqv
    {K : Nat} {hK : 1 <= K}
    (coefficient : EdgeLabelling -> Q')
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    listQSum (globalInwardMateTargetClassSecondObservableEnergy coefficient)
        (globalInwardMateSecondOSEdgeTargetFiber representative) ≈
      globalInwardMateSecondOSEdgeLoad representative *
        observableSquaredDifference coefficient
          (targetLower representative) (commonRight representative) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun targetRepresentative =>
        globalInwardMateTargetClassTraffic targetRepresentative *
          observableSquaredDifference coefficient
            (targetLower representative) (commonRight representative))
      (globalInwardMateSecondOSEdgeTargetFiber representative)) _ ?_ ?_
  · apply listQSum_congr_mem_local
    intro targetRepresentative htarget
    have hstates := globalInwardMateSecondOSEdgeTargetFiber_states_eq htarget
    unfold globalInwardMateTargetClassSecondObservableEnergy
    apply Q'.mul_eqv_congr_left
    rw [← hstates.1, ← hstates.2]
    exact Q'.eqv_refl _
  · unfold globalInwardMateSecondOSEdgeLoad
    exact listQSum_mul_right globalInwardMateTargetClassTraffic
      (observableSquaredDifference coefficient
        (targetLower representative) (commonRight representative))
      (globalInwardMateSecondOSEdgeTargetFiber representative)

theorem globalInwardMateUsedSecondObservableEnergy_eqv_selected
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') :
    globalInwardMateUsedSecondObservableEnergy K hK coefficient ≈
      globalInwardMateSelectedSecondObservableEnergy K hK coefficient := by
  refine Q'.eqv_trans _
    (globalInwardMateTargetRepresentativeSecondObservableEnergy
      K hK coefficient) _ ?_ ?_
  · refine Q'.eqv_trans _
      (listQSum
        (fun representative =>
          listQSum (globalInwardMateTargetClassSecondObservableEnergy coefficient)
            (globalInwardMateSecondOSEdgeTargetFiber representative))
        (globalInwardMateSecondOSEdgeRepresentatives K hK)) _ ?_ ?_
    · apply listQSum_congr
      intro representative
      exact Q'.eqv_symm
        (globalInwardMateSecondOSEdgeTargetFiber_observableEnergy_eqv
          coefficient representative)
    · unfold globalInwardMateSecondOSEdgeRepresentatives
        globalInwardMateSecondOSEdgeTargetFiber
        globalInwardMateTargetRepresentativeSecondObservableEnergy
      exact keyRepresentativeFibers_weight_total
        (globalInwardMateTargetRepresentatives K hK)
        (globalInwardMateTargetClassSecondObservableEnergy coefficient)
        globalInwardMateSecondOSEdgeKey
  · exact globalInwardMateTargetRepresentativeSecondObservableEnergy_eqv_selected
      K hK coefficient

theorem globalInwardMateUsedSecondObservableEnergy_le_cost_mul_capacity
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') :
    globalInwardMateUsedSecondObservableEnergy K hK coefficient <=
      globalInwardMateTransportCost *
        globalInwardMateUsedSecondObservableCapacityEnergy
          K hK coefficient := by
  have htermwise : globalInwardMateUsedSecondObservableEnergy K hK coefficient <=
      listQSum
        (fun representative =>
          globalInwardMateTransportCost *
            (centralNormalizedPhysicalReflectedKernel
                anchorCoupling (by decide) K 0
                (targetLower representative) (commonRight representative) *
              observableSquaredDifference coefficient
                (targetLower representative) (commonRight representative)))
        (globalInwardMateSecondOSEdgeRepresentatives K hK) := by
    unfold globalInwardMateUsedSecondObservableEnergy
    apply listQSum_le_termwise_local
    intro representative _
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
      (observableSquaredDifference coefficient
        (targetLower representative) (commonRight representative))
      (globalInwardMateSecondOSEdgeLoad_le_capacity representative)
      (observableSquaredDifference_nonnegative coefficient _ _)
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.mul_assoc_eqv
        globalInwardMateTransportCost
        (centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0
          (targetLower representative) (commonRight representative))
        (observableSquaredDifference coefficient
          (targetLower representative) (commonRight representative))))
  exact Q'.le_trans' _ _ _ htermwise
    (Q'.le_of_eqv
      (listQSum_mul_left globalInwardMateTransportCost _
        (globalInwardMateSecondOSEdgeRepresentatives K hK)))

theorem globalInwardMateUsedSecondObservableCapacityEnergy_le_Dirichlet
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') :
    globalInwardMateUsedSecondObservableCapacityEnergy K hK coefficient <=
      finiteJointDirichletEnergy (centralHalfStates K 0) coefficient
        (centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0) := by
  let states := centralHalfStates K 0
  let representatives := globalInwardMateSecondOSEdgeRepresentatives K hK
  let edgeTerm : EdgeLabelling × EdgeLabelling -> Q' := fun edge =>
    centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0 edge.1 edge.2 *
      observableSquaredDifference coefficient edge.1 edge.2
  have hrepresentatives : representatives.Nodup := by
    unfold representatives globalInwardMateSecondOSEdgeRepresentatives
    apply nodup_of_map_nodup_local globalInwardMateSecondOSEdgeKey
    exact keyRepresentatives_keys_nodup globalInwardMateSecondOSEdgeKey
      (globalInwardMateTargetRepresentatives K hK)
  have hinjection := listQSum_le_of_injective_nodup
    representatives (cartesian states states)
    (fun representative => edgeTerm
      (globalInwardMateSecondOSEdgePair representative))
    edgeTerm globalInwardMateSecondOSEdgePair
    hrepresentatives
    (cartesian_nodup states states
      (by unfold states; exact centralHalfStates_nodup K 0)
      (by unfold states; exact centralHalfStates_nodup K 0))
    (fun representative _ => by
      apply (mem_cartesian_iff states states _).mpr
      exact ⟨targetLower_mem representative, commonRight_mem representative⟩)
    (fun left hleft right hright heq =>
      globalInwardMateSecondOSEdgePair_injective
        left hleft right hright heq)
    (fun _ _ => Q'.le_refl' _)
    (fun edge _ =>
      Q'.mul_nonneg _ _
        (centralNormalizedPhysicalReflectedKernel_nonnegative
          (by decide) K 0 edge.1 edge.2)
        (observableSquaredDifference_nonnegative coefficient edge.1 edge.2))
  have htarget : listQSum edgeTerm (cartesian states states) ≈
      finiteJointDirichletEnergy states coefficient
        (centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0) := by
    refine Q'.eqv_trans _
      (listQSum (fun left => listQSum (fun right => edgeTerm (left, right)) states)
        states) _ (listQSum_cartesian_eq_nested_local edgeTerm states states) ?_
    unfold finiteJointDirichletEnergy edgeTerm observableSquaredDifference
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ hinjection (Q'.le_of_eqv htarget)

theorem globalInwardMateSelectedSecondObservableEnergy_le_cost_mul_Dirichlet
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') :
    globalInwardMateSelectedSecondObservableEnergy K hK coefficient <=
      globalInwardMateTransportCost *
        finiteJointDirichletEnergy (centralHalfStates K 0) coefficient
          (centralNormalizedPhysicalReflectedKernel
            anchorCoupling (by decide) K 0) := by
  have hcapacity := Q'.mul_le_mul_of_nonneg_left _ _
    globalInwardMateTransportCost
    (globalInwardMateUsedSecondObservableCapacityEnergy_le_Dirichlet
      K hK coefficient)
    (Q'.le_of_lt globalInwardMateTransportCost_positive)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (globalInwardMateUsedSecondObservableEnergy_eqv_selected
          K hK coefficient)))
    (Q'.le_trans' _ _ _
      (globalInwardMateUsedSecondObservableEnergy_le_cost_mul_capacity
        K hK coefficient)
      hcapacity)

/-! ## 4. Endpoint oscillation and the exact coverage frontier -/

def globalInwardMateSelectedEndpointObservableEnergyTerm
    {K : Nat} {hK : 1 <= K}
    (coefficient : EdgeLabelling -> Q')
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Q' :=
  globalInwardMateSourceTraffic source *
    observableSquaredDifference coefficient
      (sourceLower source) (targetLower source)

def globalInwardMateSelectedEndpointObservableEnergy
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') : Q' :=
  listQSum (globalInwardMateSelectedEndpointObservableEnergyTerm coefficient)
    (globalCubeInwardMateCertifiedTargetFullSources K hK)

def globalInwardMateTwiceEdgeObservableEnergyTerm
    {K : Nat} {hK : 1 <= K}
    (coefficient : EdgeLabelling -> Q')
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Q' :=
  (globalInwardMateSelectedFirstObservableEnergyTerm coefficient source +
      globalInwardMateSelectedSecondObservableEnergyTerm coefficient source) +
    (globalInwardMateSelectedFirstObservableEnergyTerm coefficient source +
      globalInwardMateSelectedSecondObservableEnergyTerm coefficient source)

def globalInwardMateObservablePathScale : Q' :=
  (1 + globalInwardMateTransportCost) +
    (1 + globalInwardMateTransportCost)

theorem globalInwardMateObservablePathScale_positive :
    (0 : Q') < globalInwardMateObservablePathScale := by
  unfold globalInwardMateObservablePathScale
  exact Q'.pos_add_nonneg
    (Q'.pos_add_nonneg (by decide)
      (Q'.le_of_lt globalInwardMateTransportCost_positive))
    (Q'.zero_le_add _ _ (by decide)
      (Q'.le_of_lt globalInwardMateTransportCost_positive))

private theorem endpointSquaredDifference_le_twice_edges
    (coefficient : EdgeLabelling -> Q')
    (source middle target : EdgeLabelling) :
    observableSquaredDifference coefficient source target <=
      (observableSquaredDifference coefficient source middle +
          observableSquaredDifference coefficient middle target) +
        (observableSquaredDifference coefficient source middle +
          observableSquaredDifference coefficient middle target) := by
  let left := coefficient source + -coefficient middle
  let right := coefficient middle + -coefficient target
  have htel : coefficient source + -coefficient target ≈ left + right := by
    unfold left right
    apply Q'.eqv_symm
    refine Q'.eqv_trans _
      (coefficient source +
        ((-coefficient middle) +
          (coefficient middle + -coefficient target))) _
      (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      (coefficient source +
        (((-coefficient middle) + coefficient middle) +
          -coefficient target)) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
    refine Q'.eqv_trans _
      (coefficient source + (0 + -coefficient target)) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.neg_add_self_eqv (coefficient middle)))
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_of_eq (Q'.zero_add' (-coefficient target)))
  have hsquare : observableSquaredDifference coefficient source target ≈
      (left + right) * (left + right) := by
    unfold observableSquaredDifference
    exact square_eqv_congr_local htel
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsquare)
    (square_add_le_double_square_sum left right)

private theorem endpointObservableEnergyTerm_le_twiceEdgeTerm
    {K : Nat} {hK : 1 <= K}
    (coefficient : EdgeLabelling -> Q')
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    globalInwardMateSelectedEndpointObservableEnergyTerm coefficient source <=
      globalInwardMateTwiceEdgeObservableEnergyTerm coefficient source := by
  let traffic := globalInwardMateSourceTraffic source
  let firstSquare := observableSquaredDifference coefficient
    (sourceLower source) (commonRight source)
  let secondSquare := observableSquaredDifference coefficient
    (commonRight source) (targetLower source)
  have hscaled :
      traffic * observableSquaredDifference coefficient
          (sourceLower source) (targetLower source) <=
        traffic *
          ((firstSquare + secondSquare) + (firstSquare + secondSquare)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ traffic
      (endpointSquaredDifference_le_twice_edges coefficient
        (sourceLower source) (commonRight source) (targetLower source))
      (globalInwardMateSourceTraffic_nonnegative source)
  have hcollect :
      traffic * ((firstSquare + secondSquare) +
          (firstSquare + secondSquare)) ≈
        (traffic * firstSquare + traffic * secondSquare) +
          (traffic * firstSquare + traffic * secondSquare) := by
    exact Q'.eqv_trans _
      (traffic * (firstSquare + secondSquare) +
        traffic * (firstSquare + secondSquare)) _
      (Q'.mul_add_eqv traffic _ _)
      (Q'.add_eqv_congr'
        (Q'.mul_add_eqv traffic firstSquare secondSquare)
        (Q'.mul_add_eqv traffic firstSquare secondSquare))
  unfold globalInwardMateSelectedEndpointObservableEnergyTerm
    globalInwardMateTwiceEdgeObservableEnergyTerm
    globalInwardMateSelectedFirstObservableEnergyTerm
    globalInwardMateSelectedSecondObservableEnergyTerm
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcollect)

theorem globalInwardMateSelectedEndpointObservableEnergy_le_twice_edges
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') :
    globalInwardMateSelectedEndpointObservableEnergy K hK coefficient <=
      (globalInwardMateSelectedFirstObservableEnergy K hK coefficient +
          globalInwardMateSelectedSecondObservableEnergy K hK coefficient) +
        (globalInwardMateSelectedFirstObservableEnergy K hK coefficient +
          globalInwardMateSelectedSecondObservableEnergy K hK coefficient) := by
  let sources := globalCubeInwardMateCertifiedTargetFullSources K hK
  let first : GlobalCubeInwardMateCertifiedTargetFullSource K hK -> Q' :=
    globalInwardMateSelectedFirstObservableEnergyTerm
      (K := K) (hK := hK) coefficient
  let second : GlobalCubeInwardMateCertifiedTargetFullSource K hK -> Q' :=
    globalInwardMateSelectedSecondObservableEnergyTerm
      (K := K) (hK := hK) coefficient
  let pair := fun source : GlobalCubeInwardMateCertifiedTargetFullSource K hK =>
    first source + second source
  let upper := globalInwardMateTwiceEdgeObservableEnergyTerm
    (K := K) (hK := hK) coefficient
  have htermwise :
      listQSum (globalInwardMateSelectedEndpointObservableEnergyTerm coefficient)
          sources <= listQSum upper sources := by
    apply listQSum_le_termwise_local
    intro source _
    exact endpointObservableEnergyTerm_le_twiceEdgeTerm coefficient source
  have hsum : listQSum upper sources ≈
      (globalInwardMateSelectedFirstObservableEnergy K hK coefficient +
          globalInwardMateSelectedSecondObservableEnergy K hK coefficient) +
        (globalInwardMateSelectedFirstObservableEnergy K hK coefficient +
          globalInwardMateSelectedSecondObservableEnergy K hK coefficient) := by
    refine Q'.eqv_trans _
      (listQSum pair sources + listQSum pair sources) _ ?_ ?_
    · unfold upper pair first second
      exact listQSum_add _ _ sources
    refine Q'.eqv_trans _
      ((listQSum first sources + listQSum second sources) +
        (listQSum first sources + listQSum second sources)) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (listQSum_add first second sources)
        (listQSum_add first second sources)
    · unfold first second globalInwardMateSelectedFirstObservableEnergy
        globalInwardMateSelectedSecondObservableEnergy
      exact Q'.eqv_refl _
  unfold globalInwardMateSelectedEndpointObservableEnergy
  exact Q'.le_trans' _ _ _ htermwise (Q'.le_of_eqv hsum)

theorem globalInwardMateSelectedEndpointObservableEnergy_le_scale_mul_Dirichlet
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q') :
    globalInwardMateSelectedEndpointObservableEnergy K hK coefficient <=
      globalInwardMateObservablePathScale *
        finiteJointDirichletEnergy (centralHalfStates K 0) coefficient
          (centralNormalizedPhysicalReflectedKernel
            anchorCoupling (by decide) K 0) := by
  let energy := finiteJointDirichletEnergy (centralHalfStates K 0) coefficient
    (centralNormalizedPhysicalReflectedKernel
      anchorCoupling (by decide) K 0)
  let first := globalInwardMateSelectedFirstObservableEnergy K hK coefficient
  let second := globalInwardMateSelectedSecondObservableEnergy K hK coefficient
  have hfirst : first <= energy :=
    globalInwardMateSelectedFirstObservableEnergy_le_Dirichlet
      K hK coefficient
  have hsecond : second <= globalInwardMateTransportCost * energy :=
    globalInwardMateSelectedSecondObservableEnergy_le_cost_mul_Dirichlet
      K hK coefficient
  have hpair : first + second <=
      energy + globalInwardMateTransportCost * energy :=
    Q'.add_le_add hfirst hsecond
  have htwice : (first + second) + (first + second) <=
      (energy + globalInwardMateTransportCost * energy) +
        (energy + globalInwardMateTransportCost * energy) :=
    Q'.add_le_add hpair hpair
  have hcollect :
      (energy + globalInwardMateTransportCost * energy) +
          (energy + globalInwardMateTransportCost * energy) ≈
        globalInwardMateObservablePathScale * energy := by
    unfold globalInwardMateObservablePathScale
    q_ring
  exact Q'.le_trans' _ _ _
    (globalInwardMateSelectedEndpointObservableEnergy_le_twice_edges
      K hK coefficient)
    (Q'.le_trans' _ _ _ htwice (Q'.le_of_eqv hcollect))

/-- The exact still-open all-vector input for this route.  An inhabitant must
provide one positive rational floor, independent of `K`, comparing every
centered physical norm with the selected inward-mate endpoint oscillation. -/
structure GlobalInwardMateUniformEndpointCoverage : Type where
  floor : Q'
  floor_positive : (0 : Q') < floor
  floor_mul_norm_le_endpoint : forall (K : Nat) (hK : 1 <= K)
      (coefficient : EdgeLabelling -> Q'),
    CentralPhysicalMeanZero anchorCoupling (by decide) K 0 coefficient ->
      floor *
          centralPhysicalWeightedInner anchorCoupling (by decide) K 0
            coefficient coefficient <=
        globalInwardMateSelectedEndpointObservableEnergy
          K hK coefficient

namespace GlobalInwardMateUniformEndpointCoverage

theorem floor_mul_norm_le_scale_mul_Dirichlet
    (coverage : GlobalInwardMateUniformEndpointCoverage)
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q')
    (hcenter : CentralPhysicalMeanZero
      anchorCoupling (by decide) K 0 coefficient) :
    coverage.floor *
        centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          coefficient coefficient <=
      globalInwardMateObservablePathScale *
        finiteJointDirichletEnergy (centralHalfStates K 0) coefficient
          (centralNormalizedPhysicalReflectedKernel
            anchorCoupling (by decide) K 0) := by
  exact Q'.le_trans' _ _ _
    (coverage.floor_mul_norm_le_endpoint K hK coefficient hcenter)
    (globalInwardMateSelectedEndpointObservableEnergy_le_scale_mul_Dirichlet
      K hK coefficient)

end GlobalInwardMateUniformEndpointCoverage

#print axioms observableSquaredDifference_nonnegative
#print axioms globalInwardMateSourceTraffic_nonnegative
#print axioms globalInwardMateSelectedFirstObservableEnergy_le_Dirichlet
#print axioms globalInwardMateSelectedSecondObservableEnergy_le_cost_mul_Dirichlet
#print axioms globalInwardMateSelectedEndpointObservableEnergy_le_twice_edges
#print axioms globalInwardMateSelectedEndpointObservableEnergy_le_scale_mul_Dirichlet
#print axioms GlobalInwardMateUniformEndpointCoverage.floor_mul_norm_le_scale_mul_Dirichlet

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSObservableEnergy
