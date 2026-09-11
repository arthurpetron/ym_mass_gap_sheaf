/-
# Embed selected inward-mate first-edge parity energy in the full OS form

The selected parity demand is initially a sum over complete successful slab
sources.  This module partitions that sum by the literal first physical OS
edge.  On each exact edge fiber the parity gradient is constant, so the fiber
sum is its aggregate traffic times that gradient square.  The proved
first-edge load estimate replaces the traffic by the actual normalized OS
joint capacity.

Distinct realized edge representatives map injectively into the Cartesian
half-state square.  Positivity therefore embeds the used-edge sum in the full
directed physical OS Dirichlet energy.  No minimum edge, carrier cardinality,
volume factor, or cutoff factor is introduced.

This controls the first half of one concrete parity demand.  The second-edge
energy, all-vector Poincare inequality, spectral gap, beta/lattice-spacing
uniformity, continuum limit, and Clay theorem remain separate.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityDemand
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFirstEdgeEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSEdgeCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSFirstEdgeLoad
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityDemand
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
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

private theorem paritySquaredDifference_nonnegative
    (left right : EdgeLabelling) :
    (0 : Q') <= paritySquaredDifference left right := by
  unfold paritySquaredDifference
  exact YMGap.Constructive.SumOfSquares.q_mul_self_nonneg _

/-! ## 1. Realized first edges and their aggregate parity energy -/

def globalInwardMateFirstOSEdgeRepresentatives
    (K : Nat) (hK : 1 <= K) :
    List (GlobalCubeInwardMateCertifiedTargetFullSource K hK) :=
  keyRepresentatives globalInwardMateFirstOSEdgeKey
    (globalCubeInwardMateCertifiedTargetFullSources K hK)

def globalInwardMateFirstOSEdgeLoad
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Q' :=
  listQSum globalInwardMateSourceTraffic
    (globalInwardMateFirstOSEdgeFiber representative)

def globalInwardMateFirstOSEdgePair
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    EdgeLabelling × EdgeLabelling :=
  (sourceLower representative, commonRight representative)

def globalInwardMateUsedFirstParityEnergy
    (K : Nat) (hK : 1 <= K) : Q' :=
  listQSum
    (fun representative =>
      globalInwardMateFirstOSEdgeLoad representative *
        paritySquaredDifference
          (sourceLower representative) (commonRight representative))
    (globalInwardMateFirstOSEdgeRepresentatives K hK)

theorem globalInwardMateFirstOSEdgeFiber_parityEnergy_eqv
    {K : Nat} {hK : 1 <= K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    listQSum globalInwardMateSelectedFirstParityEnergyTerm
        (globalInwardMateFirstOSEdgeFiber representative) ≈
      globalInwardMateFirstOSEdgeLoad representative *
        paritySquaredDifference
          (sourceLower representative) (commonRight representative) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        globalInwardMateSourceTraffic source *
          paritySquaredDifference
            (sourceLower representative) (commonRight representative))
      (globalInwardMateFirstOSEdgeFiber representative)) _ ?_ ?_
  · apply listQSum_congr_mem_local
    intro source hsource
    have hstates := globalInwardMateFirstOSEdgeFiber_states_eq hsource
    unfold globalInwardMateSelectedFirstParityEnergyTerm
    apply Q'.mul_eqv_congr_left
    rw [← hstates.1, ← hstates.2]
    exact Q'.eqv_refl _
  · unfold globalInwardMateFirstOSEdgeLoad
    exact listQSum_mul_right globalInwardMateSourceTraffic
      (paritySquaredDifference
        (sourceLower representative) (commonRight representative))
      (globalInwardMateFirstOSEdgeFiber representative)

theorem globalInwardMateUsedFirstParityEnergy_eqv_selected
    (K : Nat) (hK : 1 <= K) :
    globalInwardMateUsedFirstParityEnergy K hK ≈
      globalInwardMateSelectedFirstParityEnergy K hK := by
  refine Q'.eqv_trans _
    (listQSum
      (fun representative =>
        listQSum globalInwardMateSelectedFirstParityEnergyTerm
          (globalInwardMateFirstOSEdgeFiber representative))
      (globalInwardMateFirstOSEdgeRepresentatives K hK)) _ ?_ ?_
  · apply listQSum_congr
    intro representative
    exact Q'.eqv_symm
      (globalInwardMateFirstOSEdgeFiber_parityEnergy_eqv representative)
  · unfold globalInwardMateFirstOSEdgeRepresentatives
      globalInwardMateFirstOSEdgeFiber
      globalInwardMateSelectedFirstParityEnergy
    exact keyRepresentativeFibers_weight_total
      (globalCubeInwardMateCertifiedTargetFullSources K hK)
      globalInwardMateSelectedFirstParityEnergyTerm
      globalInwardMateFirstOSEdgeKey

/-! ## 2. Used first-edge capacity embeds in the full OS Dirichlet sum -/

def globalInwardMateUsedFirstParityCapacityEnergy
    (K : Nat) (hK : 1 <= K) : Q' :=
  listQSum
    (fun representative =>
      centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0
          (sourceLower representative) (commonRight representative) *
        paritySquaredDifference
          (sourceLower representative) (commonRight representative))
    (globalInwardMateFirstOSEdgeRepresentatives K hK)

theorem globalInwardMateUsedFirstParityEnergy_le_capacity
    (K : Nat) (hK : 1 <= K) :
    globalInwardMateUsedFirstParityEnergy K hK <=
      globalInwardMateUsedFirstParityCapacityEnergy K hK := by
  unfold globalInwardMateUsedFirstParityEnergy
    globalInwardMateUsedFirstParityCapacityEnergy
  apply listQSum_le_termwise_local
  intro representative _
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (globalInwardMateFirstOSEdgeFiber_traffic_le_normalizedKernel
      representative)
    (paritySquaredDifference_nonnegative _ _)

theorem globalInwardMateFirstOSEdgePair_injective
    {K : Nat} {hK : 1 <= K}
    (left : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hleft : left ∈ globalInwardMateFirstOSEdgeRepresentatives K hK)
    (right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hright : right ∈ globalInwardMateFirstOSEdgeRepresentatives K hK)
    (heq : globalInwardMateFirstOSEdgePair left =
      globalInwardMateFirstOSEdgePair right) :
    left = right := by
  have hkey : globalInwardMateFirstOSEdgeKey left =
      globalInwardMateFirstOSEdgeKey right := by
    unfold globalInwardMateFirstOSEdgeKey
    have hp := congrArg
      (fun pair : EdgeLabelling × EdgeLabelling =>
        (finiteEdgeLabellingWord (centralLowerFaceIds 0) pair.1,
          finiteEdgeLabellingWord (centralLowerFaceIds 0) pair.2)) heq
    simpa only [globalInwardMateFirstOSEdgePair] using hp
  apply eq_of_key_eq_of_map_nodup_local globalInwardMateFirstOSEdgeKey
    (keyRepresentatives_keys_nodup globalInwardMateFirstOSEdgeKey
      (globalCubeInwardMateCertifiedTargetFullSources K hK))
    hleft hright hkey

theorem globalInwardMateUsedFirstParityCapacityEnergy_le_Dirichlet
    (K : Nat) (hK : 1 <= K) :
    globalInwardMateUsedFirstParityCapacityEnergy K hK <=
      finiteJointDirichletEnergy (centralHalfStates K 0)
        centralFaceZeroParityCoefficient
        (centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0) := by
  let states := centralHalfStates K 0
  let representatives := globalInwardMateFirstOSEdgeRepresentatives K hK
  let edgeTerm : EdgeLabelling × EdgeLabelling -> Q' := fun edge =>
    centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0 edge.1 edge.2 *
      paritySquaredDifference edge.1 edge.2
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
        (paritySquaredDifference_nonnegative edge.1 edge.2))
  have hsource : globalInwardMateUsedFirstParityCapacityEnergy K hK ≈
      listQSum
        (fun representative => edgeTerm
          (globalInwardMateFirstOSEdgePair representative))
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

/-- The complete first-edge part of the selected parity demand is bounded by
the actual full physical OS Dirichlet energy. -/
theorem globalInwardMateSelectedFirstParityEnergy_le_Dirichlet
    (K : Nat) (hK : 1 <= K) :
    globalInwardMateSelectedFirstParityEnergy K hK <=
      finiteJointDirichletEnergy (centralHalfStates K 0)
        centralFaceZeroParityCoefficient
        (centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (globalInwardMateUsedFirstParityEnergy_eqv_selected K hK)))
    (Q'.le_trans' _ _ _
      (globalInwardMateUsedFirstParityEnergy_le_capacity K hK)
      (globalInwardMateUsedFirstParityCapacityEnergy_le_Dirichlet K hK))

#print axioms globalInwardMateFirstOSEdgeRepresentatives
#print axioms globalInwardMateFirstOSEdgeFiber_parityEnergy_eqv
#print axioms globalInwardMateUsedFirstParityEnergy_eqv_selected
#print axioms globalInwardMateUsedFirstParityEnergy_le_capacity
#print axioms globalInwardMateFirstOSEdgePair_injective
#print axioms globalInwardMateUsedFirstParityCapacityEnergy_le_Dirichlet
#print axioms globalInwardMateSelectedFirstParityEnergy_le_Dirichlet

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFirstEdgeEnergy
