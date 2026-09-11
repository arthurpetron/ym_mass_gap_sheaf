/-
# Embed selected inward-mate second-edge parity energy in the full OS form

The second half of the selected parity demand passes through two exact finite
partitions.  Successful sources first partition by their compiled production
target, and those target representatives then partition by their literal
second physical OS edge.  The target endpoint and the common middle state are
constant on both fibers, so the parity gradient factors through both sums.

The proved second-edge congestion estimate bounds every grouped load by
`globalInwardMateTransportCost` times the actual normalized OS joint capacity.
Distinct realized second edges inject into the Cartesian half-state square,
so positivity embeds their capacity energy in the full directed physical OS
Dirichlet energy.

Together with the first-edge module this prepares one concrete observable
coercivity bound.  It is not an all-vector Poincare inequality, spectral gap,
beta/lattice-spacing uniformity statement, continuum limit, or Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFirstEdgeEnergy

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParitySecondEdgeEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSEdgeCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSNormalizedFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityDemand
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSSecondEdgeLoad
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionCongestion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFraction
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

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

private theorem eq_of_key_eq_of_map_nodup_local
    {A Key : Type} (key : A -> Key) : forall
    {items : List A}, (items.map key).Nodup ->
    forall {left right : A}, left ∈ items -> right ∈ items ->
      key left = key right -> left = right
  | [], _, _, _, hleft, _, _ => False.elim (List.not_mem_nil hleft)
  | head :: tail, hnodup, left, right, hleft, hright, hkey => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hleft with rfl | hleftTail
      · rcases List.mem_cons.mp hright with rfl | hrightTail
        · rfl
        · exact False.elim (hparts.1
            (List.mem_map.mpr ⟨right, hrightTail, hkey.symm⟩))
      · rcases List.mem_cons.mp hright with rfl | hrightTail
        · exact False.elim (hparts.1
            (List.mem_map.mpr ⟨left, hleftTail, hkey⟩))
        · exact eq_of_key_eq_of_map_nodup_local key hparts.2
            hleftTail hrightTail hkey

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

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

theorem paritySquaredDifference_symm
    (left right : EdgeLabelling) :
    paritySquaredDifference left right ≈
      paritySquaredDifference right left := by
  unfold paritySquaredDifference
  q_ring

private theorem paritySquaredDifference_nonnegative
    (left right : EdgeLabelling) :
    (0 : Q') <= paritySquaredDifference left right := by
  unfold paritySquaredDifference
  exact YMGap.Constructive.SumOfSquares.q_mul_self_nonneg _

/-! ## 1. The second-edge gradient factors through target classes -/

theorem globalInwardMateProductionTargetFiber_states_eq
    {K : Nat} {hK : 1 <= K}
    {representative source :
      GlobalCubeInwardMateCertifiedTargetFullSource K hK}
    (hsource : source ∈ globalInwardMateProductionTargetFiber representative) :
    targetLower representative = targetLower source ∧
      commonRight representative = commonRight source := by
  have hproduction : globalInwardMateProductionTargetKey source =
      globalInwardMateProductionTargetKey representative :=
    of_decide_eq_true (List.mem_filter.mp hsource).2
  have hkey : globalInwardMateTargetKey representative =
      globalInwardMateTargetKey source :=
    (globalInwardMateProductionTargetKey_eq_iff_targetKey_eq
      representative source).mp hproduction.symm
  have hatom := globalInwardMateTargetProductionAtom_eq_of_targetKey_eq
    representative source hkey
  have hphysical : targetPhysical representative = targetPhysical source :=
    congrArg Prod.fst hatom
  constructor
  · unfold targetLower
    rw [hphysical]
  · calc
      commonRight representative =
          centralReflectedUpperRestriction 0 (targetPhysical representative) :=
        (targetRight_eq_common representative).symm
      _ = centralReflectedUpperRestriction 0 (targetPhysical source) :=
        congrArg (centralReflectedUpperRestriction 0) hphysical
      _ = commonRight source := targetRight_eq_common source

def globalInwardMateTargetClassSecondParityEnergy
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Q' :=
  globalInwardMateTargetClassTraffic representative *
    paritySquaredDifference
      (targetLower representative) (commonRight representative)

theorem globalInwardMateProductionTargetFiber_secondParityEnergy_eqv
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    listQSum globalInwardMateSelectedSecondParityEnergyTerm
        (globalInwardMateProductionTargetFiber representative) ≈
      globalInwardMateTargetClassSecondParityEnergy representative := by
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        globalInwardMateSourceTraffic source *
          paritySquaredDifference
            (targetLower representative) (commonRight representative))
      (globalInwardMateProductionTargetFiber representative)) _ ?_ ?_
  · apply listQSum_congr_mem_local
    intro source hsource
    have hstates := globalInwardMateProductionTargetFiber_states_eq hsource
    unfold globalInwardMateSelectedSecondParityEnergyTerm
    apply Q'.mul_eqv_congr_left
    rw [← hstates.1, ← hstates.2]
    exact paritySquaredDifference_symm _ _
  · unfold globalInwardMateTargetClassSecondParityEnergy
      globalInwardMateTargetClassTraffic
    exact listQSum_mul_right globalInwardMateSourceTraffic
      (paritySquaredDifference
        (targetLower representative) (commonRight representative))
      (globalInwardMateProductionTargetFiber representative)

def globalInwardMateTargetRepresentativeSecondParityEnergy
    (K : Nat) (hK : 1 <= K) : Q' :=
  listQSum globalInwardMateTargetClassSecondParityEnergy
    (globalInwardMateTargetRepresentatives K hK)

theorem globalInwardMateTargetRepresentativeSecondParityEnergy_eqv_selected
    (K : Nat) (hK : 1 <= K) :
    globalInwardMateTargetRepresentativeSecondParityEnergy K hK ≈
      globalInwardMateSelectedSecondParityEnergy K hK := by
  refine Q'.eqv_trans _
    (listQSum
      (fun representative =>
        listQSum globalInwardMateSelectedSecondParityEnergyTerm
          (globalInwardMateProductionTargetFiber representative))
      (globalInwardMateTargetRepresentatives K hK)) _ ?_ ?_
  · apply listQSum_congr
    intro representative
    exact Q'.eqv_symm
      (globalInwardMateProductionTargetFiber_secondParityEnergy_eqv
        representative)
  refine Q'.eqv_trans _
    (listQSum
      (fun representative =>
        listQSum globalInwardMateSelectedSecondParityEnergyTerm
          (representativeFiber
            (globalCubeInwardMateCertifiedTargetFullSources K hK)
            globalInwardMateTargetKey representative))
      (globalInwardMateTargetRepresentatives K hK)) _ ?_ ?_
  · apply listQSum_congr
    intro representative
    rw [globalInwardMateProductionTargetFiber_eq_targetFiber,
      ← globalInwardMateRepresentativeFiber_eq_targetFiber]
    exact Q'.eqv_refl _
  · unfold globalInwardMateSelectedSecondParityEnergy
      globalInwardMateTargetRepresentatives
    exact keyRepresentativeFibers_weight_total
      (globalCubeInwardMateCertifiedTargetFullSources K hK)
      globalInwardMateSelectedSecondParityEnergyTerm
      globalInwardMateTargetKey

/-! ## 2. Target classes repartition exactly by the second OS edge -/

def globalInwardMateUsedSecondParityEnergy
    (K : Nat) (hK : 1 <= K) : Q' :=
  listQSum
    (fun representative =>
      globalInwardMateSecondOSEdgeLoad representative *
        paritySquaredDifference
          (targetLower representative) (commonRight representative))
    (globalInwardMateSecondOSEdgeRepresentatives K hK)

theorem globalInwardMateSecondOSEdgeTargetFiber_parityEnergy_eqv
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    listQSum globalInwardMateTargetClassSecondParityEnergy
        (globalInwardMateSecondOSEdgeTargetFiber representative) ≈
      globalInwardMateSecondOSEdgeLoad representative *
        paritySquaredDifference
          (targetLower representative) (commonRight representative) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun targetRepresentative =>
        globalInwardMateTargetClassTraffic targetRepresentative *
          paritySquaredDifference
            (targetLower representative) (commonRight representative))
      (globalInwardMateSecondOSEdgeTargetFiber representative)) _ ?_ ?_
  · apply listQSum_congr_mem_local
    intro targetRepresentative htarget
    have hstates := globalInwardMateSecondOSEdgeTargetFiber_states_eq htarget
    unfold globalInwardMateTargetClassSecondParityEnergy
    apply Q'.mul_eqv_congr_left
    rw [← hstates.1, ← hstates.2]
    exact Q'.eqv_refl _
  · unfold globalInwardMateSecondOSEdgeLoad
    exact listQSum_mul_right globalInwardMateTargetClassTraffic
      (paritySquaredDifference
        (targetLower representative) (commonRight representative))
      (globalInwardMateSecondOSEdgeTargetFiber representative)

theorem globalInwardMateUsedSecondParityEnergy_eqv_targetRepresentatives
    (K : Nat) (hK : 1 <= K) :
    globalInwardMateUsedSecondParityEnergy K hK ≈
      globalInwardMateTargetRepresentativeSecondParityEnergy K hK := by
  refine Q'.eqv_trans _
    (listQSum
      (fun representative =>
        listQSum globalInwardMateTargetClassSecondParityEnergy
          (globalInwardMateSecondOSEdgeTargetFiber representative))
      (globalInwardMateSecondOSEdgeRepresentatives K hK)) _ ?_ ?_
  · apply listQSum_congr
    intro representative
    exact Q'.eqv_symm
      (globalInwardMateSecondOSEdgeTargetFiber_parityEnergy_eqv
        representative)
  · unfold globalInwardMateSecondOSEdgeRepresentatives
      globalInwardMateSecondOSEdgeTargetFiber
      globalInwardMateTargetRepresentativeSecondParityEnergy
    exact keyRepresentativeFibers_weight_total
      (globalInwardMateTargetRepresentatives K hK)
      globalInwardMateTargetClassSecondParityEnergy
      globalInwardMateSecondOSEdgeKey

theorem globalInwardMateUsedSecondParityEnergy_eqv_selected
    (K : Nat) (hK : 1 <= K) :
    globalInwardMateUsedSecondParityEnergy K hK ≈
      globalInwardMateSelectedSecondParityEnergy K hK :=
  Q'.eqv_trans _ _ _
    (globalInwardMateUsedSecondParityEnergy_eqv_targetRepresentatives K hK)
    (globalInwardMateTargetRepresentativeSecondParityEnergy_eqv_selected K hK)

/-! ## 3. Congestion and injection into the full OS Dirichlet form -/

def globalInwardMateUsedSecondParityCapacityEnergy
    (K : Nat) (hK : 1 <= K) : Q' :=
  listQSum
    (fun representative =>
      centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0
          (targetLower representative) (commonRight representative) *
        paritySquaredDifference
          (targetLower representative) (commonRight representative))
    (globalInwardMateSecondOSEdgeRepresentatives K hK)

theorem globalInwardMateUsedSecondParityEnergy_le_cost_mul_capacity
    (K : Nat) (hK : 1 <= K) :
    globalInwardMateUsedSecondParityEnergy K hK <=
      globalInwardMateTransportCost *
        globalInwardMateUsedSecondParityCapacityEnergy K hK := by
  have htermwise : globalInwardMateUsedSecondParityEnergy K hK <=
      listQSum
        (fun representative =>
          globalInwardMateTransportCost *
            (centralNormalizedPhysicalReflectedKernel
                anchorCoupling (by decide) K 0
                (targetLower representative) (commonRight representative) *
              paritySquaredDifference
                (targetLower representative) (commonRight representative)))
        (globalInwardMateSecondOSEdgeRepresentatives K hK) := by
    unfold globalInwardMateUsedSecondParityEnergy
    apply listQSum_le_termwise_local
    intro representative _
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
      (paritySquaredDifference
        (targetLower representative) (commonRight representative))
      (globalInwardMateSecondOSEdgeLoad_le_capacity representative)
      (paritySquaredDifference_nonnegative _ _)
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.mul_assoc_eqv
        globalInwardMateTransportCost
        (centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0
          (targetLower representative) (commonRight representative))
        (paritySquaredDifference
          (targetLower representative) (commonRight representative))))
  have hfactor :
      listQSum
        (fun representative =>
          globalInwardMateTransportCost *
            (centralNormalizedPhysicalReflectedKernel
                anchorCoupling (by decide) K 0
                (targetLower representative) (commonRight representative) *
              paritySquaredDifference
                (targetLower representative) (commonRight representative)))
        (globalInwardMateSecondOSEdgeRepresentatives K hK) ≈
      globalInwardMateTransportCost *
        globalInwardMateUsedSecondParityCapacityEnergy K hK := by
    unfold globalInwardMateUsedSecondParityCapacityEnergy
    exact listQSum_mul_left globalInwardMateTransportCost _
      (globalInwardMateSecondOSEdgeRepresentatives K hK)
  exact Q'.le_trans' _ _ _ htermwise (Q'.le_of_eqv hfactor)

def globalInwardMateSecondOSEdgePair
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    EdgeLabelling × EdgeLabelling :=
  (targetLower representative, commonRight representative)

theorem globalInwardMateSecondOSEdgePair_injective
    {K : Nat} {hK : 1 <= K}
    (left : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hleft : left ∈ globalInwardMateSecondOSEdgeRepresentatives K hK)
    (right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hright : right ∈ globalInwardMateSecondOSEdgeRepresentatives K hK)
    (heq : globalInwardMateSecondOSEdgePair left =
      globalInwardMateSecondOSEdgePair right) :
    left = right := by
  have hkey : globalInwardMateSecondOSEdgeKey left =
      globalInwardMateSecondOSEdgeKey right := by
    unfold globalInwardMateSecondOSEdgeKey
    have hp := congrArg
      (fun pair : EdgeLabelling × EdgeLabelling =>
        (finiteEdgeLabellingWord (centralLowerFaceIds 0) pair.1,
          finiteEdgeLabellingWord (centralLowerFaceIds 0) pair.2)) heq
    simpa only [globalInwardMateSecondOSEdgePair] using hp
  apply eq_of_key_eq_of_map_nodup_local globalInwardMateSecondOSEdgeKey
    (keyRepresentatives_keys_nodup globalInwardMateSecondOSEdgeKey
      (globalInwardMateTargetRepresentatives K hK))
    hleft hright hkey

theorem globalInwardMateUsedSecondParityCapacityEnergy_le_Dirichlet
    (K : Nat) (hK : 1 <= K) :
    globalInwardMateUsedSecondParityCapacityEnergy K hK <=
      finiteJointDirichletEnergy (centralHalfStates K 0)
        centralFaceZeroParityCoefficient
        (centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0) := by
  let states := centralHalfStates K 0
  let representatives := globalInwardMateSecondOSEdgeRepresentatives K hK
  let edgeTerm : EdgeLabelling × EdgeLabelling -> Q' := fun edge =>
    centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0 edge.1 edge.2 *
      paritySquaredDifference edge.1 edge.2
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
        (paritySquaredDifference_nonnegative edge.1 edge.2))
  have hsource : globalInwardMateUsedSecondParityCapacityEnergy K hK ≈
      listQSum
        (fun representative => edgeTerm
          (globalInwardMateSecondOSEdgePair representative))
        representatives := Q'.eqv_refl _
  have htarget : listQSum edgeTerm (cartesian states states) ≈
      finiteJointDirichletEnergy states centralFaceZeroParityCoefficient
        (centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0) := by
    refine Q'.eqv_trans _
      (listQSum (fun left => listQSum (fun right => edgeTerm (left, right)) states)
        states) _ (listQSum_cartesian_eq_nested_local edgeTerm states states) ?_
    unfold finiteJointDirichletEnergy edgeTerm paritySquaredDifference
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsource)
    (Q'.le_trans' _ _ _ hinjection (Q'.le_of_eqv htarget))

/-- The complete second-edge part of the selected parity demand is bounded by
`globalInwardMateTransportCost` times the actual full physical OS Dirichlet
energy. -/
theorem globalInwardMateSelectedSecondParityEnergy_le_cost_mul_Dirichlet
    (K : Nat) (hK : 1 <= K) :
    globalInwardMateSelectedSecondParityEnergy K hK <=
      globalInwardMateTransportCost *
        finiteJointDirichletEnergy (centralHalfStates K 0)
          centralFaceZeroParityCoefficient
          (centralNormalizedPhysicalReflectedKernel
            anchorCoupling (by decide) K 0) := by
  have hcapacity := Q'.mul_le_mul_of_nonneg_left _ _
    globalInwardMateTransportCost
    (globalInwardMateUsedSecondParityCapacityEnergy_le_Dirichlet K hK)
    (Q'.le_of_lt globalInwardMateTransportCost_positive)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (globalInwardMateUsedSecondParityEnergy_eqv_selected K hK)))
    (Q'.le_trans' _ _ _
      (globalInwardMateUsedSecondParityEnergy_le_cost_mul_capacity K hK)
      hcapacity)

structure GlobalInwardMateSecondParityEnergyCertificate
    (K : Nat) (hK : 1 <= K) : Type where
  selectedEnergy : Q'
  usedCapacityEnergy : Q'
  selectedEnergy_eq : selectedEnergy ≈
    globalInwardMateSelectedSecondParityEnergy K hK
  usedCapacityEnergy_eq : usedCapacityEnergy ≈
    globalInwardMateUsedSecondParityCapacityEnergy K hK
  selected_le_cost_mul_capacity : selectedEnergy <=
    globalInwardMateTransportCost * usedCapacityEnergy
  usedCapacity_le_Dirichlet : usedCapacityEnergy <=
    finiteJointDirichletEnergy (centralHalfStates K 0)
      centralFaceZeroParityCoefficient
      (centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0)
  selected_le_cost_mul_Dirichlet : selectedEnergy <=
    globalInwardMateTransportCost *
      finiteJointDirichletEnergy (centralHalfStates K 0)
        centralFaceZeroParityCoefficient
        (centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0)

def globalInwardMateSecondParityEnergyCertificate
    (K : Nat) (hK : 1 <= K) :
    GlobalInwardMateSecondParityEnergyCertificate K hK :=
  { selectedEnergy := globalInwardMateSelectedSecondParityEnergy K hK
    usedCapacityEnergy :=
      globalInwardMateUsedSecondParityCapacityEnergy K hK
    selectedEnergy_eq := Q'.eqv_refl _
    usedCapacityEnergy_eq := Q'.eqv_refl _
    selected_le_cost_mul_capacity := Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (globalInwardMateUsedSecondParityEnergy_eqv_selected K hK)))
      (globalInwardMateUsedSecondParityEnergy_le_cost_mul_capacity K hK)
    usedCapacity_le_Dirichlet :=
      globalInwardMateUsedSecondParityCapacityEnergy_le_Dirichlet K hK
    selected_le_cost_mul_Dirichlet :=
      globalInwardMateSelectedSecondParityEnergy_le_cost_mul_Dirichlet K hK }

#print axioms paritySquaredDifference_symm
#print axioms globalInwardMateProductionTargetFiber_states_eq
#print axioms globalInwardMateProductionTargetFiber_secondParityEnergy_eqv
#print axioms globalInwardMateTargetRepresentativeSecondParityEnergy_eqv_selected
#print axioms globalInwardMateSecondOSEdgeTargetFiber_parityEnergy_eqv
#print axioms globalInwardMateUsedSecondParityEnergy_eqv_selected
#print axioms globalInwardMateUsedSecondParityEnergy_le_cost_mul_capacity
#print axioms globalInwardMateSecondOSEdgePair_injective
#print axioms globalInwardMateUsedSecondParityCapacityEnergy_le_Dirichlet
#print axioms globalInwardMateSelectedSecondParityEnergy_le_cost_mul_Dirichlet
#print axioms globalInwardMateSecondParityEnergyCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParitySecondEdgeEnergy
