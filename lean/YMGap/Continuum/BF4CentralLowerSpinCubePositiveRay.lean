/-
# An all-spin positive support ray of closed lower cubes

For every label `spin` admitted by the production cutoff, put that label on
the six faces of the literal central lower cube and zero elsewhere.  Every
touched link sees the equal pair `spin, spin`; the singlet-channel injection
therefore bounds its multiplicity below by the vacuum multiplicity one.
Together with strict positivity of every heat-kernel coefficient, this gives
a strictly positive physical term and a strictly positive raw reflected
kernel edge between the state and the vacuum.

Thus every cutoff-admitted spin cube is a genuine member of the positive
physical carrier.  The present file constructs the states and their support
edges; the subsequent finite-graph step must still compile their pairwise
distinctness into a vacuum-sector cardinality lower bound.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CentralLowerCubeRowDomination
import YMGap.Continuum.Z4FusionEqualPairSingletInjection

namespace YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CentralLowerCubeRowDomination
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FusionEqualPairSingletInjection
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. The spin-labelled closed cube -/

/-- Label the six faces of the central lower cube by `spin` and every other
face by zero. -/
def centralLowerSpinCubeState (spin : Nat) : EdgeLabelling := fun id =>
  if id ∈ centralLowerCubeFaceIds then spin else 0

/-- The complete corrected-slab labelling selected by the spin cube and
vacuum fixed/target data. -/
def centralLowerSpinCubePhysical (spin : Nat) : EdgeLabelling :=
  assembleReflectedSlabLabelling 0 (centralLowerSpinCubeState spin)
    zeroEdgeLabelling zeroEdgeLabelling

theorem centralLowerSpinCubeState_eq_spin_on_cube
    (spin : Nat) {id : Nat} (hid : id ∈ centralLowerCubeFaceIds) :
    centralLowerSpinCubeState spin id = spin := by
  simp [centralLowerSpinCubeState, hid]

theorem centralLowerSpinCubeState_eq_zero_off_cube
    (spin : Nat) {id : Nat} (hid : id ∉ centralLowerCubeFaceIds) :
    centralLowerSpinCubeState spin id = 0 := by
  simp [centralLowerSpinCubeState, hid]

theorem centralLowerSpinCubeState_le
    (spin id : Nat) : centralLowerSpinCubeState spin id <= spin := by
  unfold centralLowerSpinCubeState
  by_cases hcube : id ∈ centralLowerCubeFaceIds <;> simp [hcube]

theorem centralLowerSpinCubePhysical_eq_state (spin : Nat) :
    centralLowerSpinCubePhysical spin =
      centralLowerSpinCubeState spin := by
  funext id
  unfold centralLowerSpinCubePhysical assembleReflectedSlabLabelling
  by_cases hid : id ∈ slabPhysicalFaceEdges (centralExtent 0)
  · rw [if_pos hid]
    cases hside :
        plaquetteHalfSide 0
          (slabPlaquetteAt (centralExtent 0) id)
    · rfl
    · change 0 = centralLowerSpinCubeState spin id
      symm
      apply centralLowerSpinCubeState_eq_zero_off_cube
      intro hcube
      have hlower :=
        (mem_centralLowerFaceIds.mp
          (centralLowerCubeFaceIds_subset_lower id hcube)).2
      rw [hside] at hlower
      contradiction
    · change 0 = centralLowerSpinCubeState spin id
      symm
      apply centralLowerSpinCubeState_eq_zero_off_cube
      intro hcube
      have hlower :=
        (mem_centralLowerFaceIds.mp
          (centralLowerCubeFaceIds_subset_lower id hcube)).2
      rw [hside] at hlower
      contradiction
  · rw [if_neg hid]
    change 0 = centralLowerSpinCubeState spin id
    symm
    apply centralLowerSpinCubeState_eq_zero_off_cube
    intro hcube
    exact hid
      (mem_centralLowerFaceIds.mp
        (centralLowerCubeFaceIds_subset_lower id hcube)).1

theorem centralLowerSpinCubePhysical_le
    (spin id : Nat) : centralLowerSpinCubePhysical spin id <= spin := by
  rw [centralLowerSpinCubePhysical_eq_state]
  exact centralLowerSpinCubeState_le spin id

theorem centralLowerSpinCubeState_mem_centralHalfStates
    {K spin : Nat} (hspin : spin <= K) :
    centralLowerSpinCubeState spin ∈ centralHalfStates K 0 := by
  unfold centralHalfStates
  apply boundedEdgeLabellings_complete
  · intro id _
    exact Nat.lt_succ_of_le
      (Nat.le_trans (centralLowerSpinCubeState_le spin id) hspin)
  · intro id hid
    apply centralLowerSpinCubeState_eq_zero_off_cube
    intro hcube
    exact hid (centralLowerCubeFaceIds_subset_lower id hcube)

/-- Evaluation on face zero makes the spin parameter recoverable. -/
theorem centralLowerSpinCubeState_injective :
    Function.Injective centralLowerSpinCubeState := by
  intro left right heq
  have hvalue := congrFun heq 0
  simpa [centralLowerSpinCubeState, centralLowerCubeFaceIds] using hvalue

/-! ## 2. Canonical incident-spin permutations -/

private theorem map_eq_replicate_of_constant
    {A B : Type} (value : A → B) (constant : B) :
    ∀ items : List A,
      (∀ item, item ∈ items → value item = constant) →
        items.map value = List.replicate items.length constant
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [List.map_cons, List.length_cons, List.replicate_succ]
      rw [hagree head List.mem_cons_self,
        map_eq_replicate_of_constant value constant tail
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem head hitem))]

theorem selected_map_spinCube_eq_replicate
    (spin : Nat)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    (centralLowerCubeSelectedIncidentIds link).map
        (centralLowerSpinCubePhysical spin) =
      List.replicate
        (centralLowerCubeSelectedIncidentIds link).length spin := by
  apply map_eq_replicate_of_constant
  intro id hid
  rw [centralLowerSpinCubePhysical_eq_state]
  apply centralLowerSpinCubeState_eq_spin_on_cube
  exact of_decide_eq_true (List.mem_filter.mp hid).2

theorem unselected_map_spinCube_eq_zero
    (spin : Nat)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    (centralLowerCubeUnselectedIncidentIds link).map
        (centralLowerSpinCubePhysical spin) =
      (centralLowerCubeUnselectedIncidentIds link).map
        zeroEdgeLabelling := by
  apply List.map_congr_left
  intro id hid
  rw [centralLowerSpinCubePhysical_eq_state]
  apply centralLowerSpinCubeState_eq_zero_off_cube
  have hfalse : decide (id ∈ centralLowerCubeFaceIds) = false := by
    simpa using (List.mem_filter.mp hid).2
  exact of_decide_eq_false hfalse

theorem zero_incident_spins_perm_selected_remainder
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    ((slabIncidentPlaqIds 1 link).map zeroEdgeLabelling).Perm
      (List.replicate
          (centralLowerCubeSelectedIncidentIds link).length 0 ++
        (centralLowerCubeUnselectedIncidentIds link).map
          zeroEdgeLabelling) := by
  have hperm :=
    (centralLowerCube_incident_partition_perm link).symm.map
      zeroEdgeLabelling
  rw [List.map_append] at hperm
  have hselected :
      (centralLowerCubeSelectedIncidentIds link).map
          zeroEdgeLabelling =
        List.replicate
          (centralLowerCubeSelectedIncidentIds link).length 0 := by
    apply map_eq_replicate_of_constant
    intro _ _
    rfl
  rw [hselected] at hperm
  exact hperm

theorem spinCube_incident_spins_perm_selected_remainder
    (spin : Nat)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    ((slabIncidentPlaqIds 1 link).map
        (centralLowerSpinCubePhysical spin)).Perm
      (List.replicate
          (centralLowerCubeSelectedIncidentIds link).length spin ++
        (centralLowerCubeUnselectedIncidentIds link).map
          zeroEdgeLabelling) := by
  have hperm :=
    (centralLowerCube_incident_partition_perm link).symm.map
      (centralLowerSpinCubePhysical spin)
  rw [List.map_append, selected_map_spinCube_eq_replicate,
    unselected_map_spinCube_eq_zero] at hperm
  exact hperm

/-! ## 3. Every corrected-slab link retains a singlet channel -/

private theorem zeroPhysical_bounded (K : Nat) :
    SlabFaceLabellingBounded K 1 zeroEdgeLabelling := by
  intro _ _
  exact Nat.zero_le K

private theorem spinCubePhysical_bounded
    {K spin : Nat} (hspin : spin <= K) :
    SlabFaceLabellingBounded K 1
      (centralLowerSpinCubePhysical spin) := by
  intro id _
  exact Nat.le_trans (centralLowerSpinCubePhysical_le spin id) hspin

/-- Linkwise, an admitted spin cube has at least the vacuum multiplicity. -/
theorem vacuum_linkMultiplicity_le_spinCube
    {K spin : Nat} (hspin : spin <= K)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link)
    (hlink : link ∈ boundaryCompleteSlabLinks 1) :
    slabExplicitLinkMultiplicity K 1 zeroEdgeLabelling link <=
      slabExplicitLinkMultiplicity K 1
        (centralLowerSpinCubePhysical spin) link := by
  let oldSpins :=
    (slabIncidentPlaqIds 1 link).map zeroEdgeLabelling
  let newSpins :=
    (slabIncidentPlaqIds 1 link).map
      (centralLowerSpinCubePhysical spin)
  let rest :=
    (centralLowerCubeUnselectedIncidentIds link).map
      zeroEdgeLabelling
  have holdBounded : SpinsBounded K oldSpins := by
    exact slabIncidentSpins_bounded (zeroPhysical_bounded K) link
  have hnewBounded : SpinsBounded K newSpins := by
    exact slabIncidentSpins_bounded
      (spinCubePhysical_bounded hspin) link
  have hlength : oldSpins.length <= 6 := by
    unfold oldSpins
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six 1 link
  have holdPerm :
      oldSpins.Perm
        (List.replicate
            (centralLowerCubeSelectedIncidentIds link).length 0 ++
          rest) := by
    exact zero_incident_spins_perm_selected_remainder link
  have hnewPerm :
      newSpins.Perm
        (List.replicate
            (centralLowerCubeSelectedIncidentIds link).length spin ++
          rest) := by
    exact spinCube_incident_spins_perm_selected_remainder spin link
  rcases centralLowerCube_selected_length_zero_or_two link hlink
      with hzero | htwo
  · rw [hzero] at holdPerm hnewPerm
    simp only [List.replicate_zero, List.nil_append] at holdPerm hnewPerm
    unfold slabExplicitLinkMultiplicity
    exact Nat.le_of_eq
      (explicitValenceMultiplicity_physical_perm
        (holdPerm.trans hnewPerm.symm) hlength holdBounded)
  · rw [htwo] at holdPerm hnewPerm
    simp only [List.replicate_succ, List.replicate_zero,
      List.cons_append, List.nil_append] at holdPerm hnewPerm
    unfold slabExplicitLinkMultiplicity
    exact explicitValenceMultiplicity_physical_equal_pair_replacement_le
      holdPerm hnewPerm hlength holdBounded hnewBounded

theorem centralLowerSpinCube_linkMultiplicity_pos
    {K spin : Nat} (hspin : spin <= K)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link)
    (hlink : link ∈ boundaryCompleteSlabLinks 1) :
    0 < slabExplicitLinkMultiplicity K 1
      (centralLowerSpinCubePhysical spin) link := by
  have hle := vacuum_linkMultiplicity_le_spinCube hspin link hlink
  rw [slabExplicitLinkMultiplicity_zero_eq_one] at hle
  omega

private theorem natListProduct_pos_of_pointwise
    {A : Type} (value : A → Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items → 0 < value item) →
        0 < natListProduct value items
  | [], _ => by
      change 0 < 1
      omega
  | head :: tail, hvalue => by
      rw [natListProduct]
      exact Nat.mul_pos
        (hvalue head List.mem_cons_self)
        (natListProduct_pos_of_pointwise value tail
          (fun item hitem =>
            hvalue item (List.mem_cons_of_mem head hitem)))

theorem centralLowerSpinCube_linkProduct_pos
    {K spin : Nat} (hspin : spin <= K) :
    0 < slabExplicitLinkMultiplicityProduct K 1
      (centralLowerSpinCubePhysical spin) := by
  unfold slabExplicitLinkMultiplicityProduct
  exact natListProduct_pos_of_pointwise
    (slabExplicitLinkMultiplicity K 1
      (centralLowerSpinCubePhysical spin))
    (boundaryCompleteSlabLinks 1)
    (fun link hlink =>
      centralLowerSpinCube_linkMultiplicity_pos hspin link hlink)

/-! ## 4. Strict physical activity and positive-row membership -/

private theorem eliminateLinks_pos
    (value : Nat → Q') (hvalue : ∀ id, (0 : Q') < value id) :
    ∀ ids : List Nat, (0 : Q') < eliminateLinks value ids
  | [] => by
      change (0 : Q') < 1
      decide
  | head :: tail =>
      Q'.mul_pos (hvalue head) (eliminateLinks_pos value hvalue tail)

private theorem ofNat_pos_of_pos
    (value : Nat) (hvalue : 0 < value) :
    (0 : Q') < Q'.ofNat value := by
  cases value with
  | zero => contradiction
  | succ predecessor => exact Q'.ofNat_succ_pos predecessor

theorem centralLowerSpinCubePhysicalTerm_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin <= K) :
    (0 : Q') < slabParametricKPhysicalTerm w K 1
      (centralLowerSpinCubePhysical spin) := by
  have hface :
      (0 : Q') < slabParametricKPhysicalFaceFactor w K 1
        (centralLowerSpinCubePhysical spin) := by
    unfold slabParametricKPhysicalFaceFactor
    apply eliminateLinks_pos
    intro id
    have hid : centralLowerSpinCubePhysical spin id < K + 1 := by
      exact Nat.lt_succ_of_le
        (Nat.le_trans
          (centralLowerSpinCubePhysical_le spin id) hspin)
    rw [coeffAt_heatKernelPacket hid]
    exact coeffW_pos hw _
  unfold slabParametricKPhysicalTerm
  exact Q'.mul_pos hface
    (ofNat_pos_of_pos
      _ (centralLowerSpinCube_linkProduct_pos hspin))

private theorem zero_mem_bounded (K : Nat) :
    ∀ ids : List Nat,
      zeroEdgeLabelling ∈ boundedEdgeLabellings K ids := by
  intro ids
  apply boundedEdgeLabellings_complete
  · intro _ _
    change 0 < K + 1
    omega
  · intro _ _
    rfl

private theorem listQSum_nonnegative
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') <= value item) :
    ∀ items : List A, (0 : Q') <= listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hvalue head)
        (listQSum_nonnegative value hvalue tail)

private theorem listQSum_member_le
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') <= value item) :
    ∀ (items : List A) {item : A}, item ∈ items →
      value item <= listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative value hvalue tail)
      · have ih := listQSum_member_le value hvalue tail htail
        have hmono :
            listQSum value tail <= value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih hmono

theorem centralLowerSpinCubePhysicalReflectedKernel_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin <= K) :
    (0 : Q') < centralPhysicalReflectedKernel w K 0
      (centralLowerSpinCubeState spin) zeroEdgeLabelling := by
  let value := fun boundary =>
    slabParametricKPhysicalTerm w K 1
      (assembleReflectedSlabLabelling 0
        (centralLowerSpinCubeState spin) boundary zeroEdgeLabelling)
  have hmember :
      value zeroEdgeLabelling <=
        listQSum value (centralBoundaryChannels K 0) :=
    listQSum_member_le value
      (fun boundary =>
        slabParametricKPhysicalTerm_nonnegative
          (Q'.le_of_lt hw) K 1
          (assembleReflectedSlabLabelling 0
            (centralLowerSpinCubeState spin) boundary zeroEdgeLabelling))
      (centralBoundaryChannels K 0)
      (zero_mem_bounded K (centralFixedFaceIds 0))
  have hchosen : (0 : Q') < value zeroEdgeLabelling :=
    centralLowerSpinCubePhysicalTerm_pos hw hspin
  unfold centralPhysicalReflectedKernel
  exact Q'.pos_of_lt_of_le hchosen hmember

theorem centralPhysicalReflectedKernel_vacuum_spinCube_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin <= K) :
    (0 : Q') < centralPhysicalReflectedKernel w K 0
      zeroEdgeLabelling (centralLowerSpinCubeState spin) := by
  have hforward :=
    centralLowerSpinCubePhysicalReflectedKernel_pos hw hspin
  have hzeroHalf : zeroEdgeLabelling ∈ centralHalfStates K 0 :=
    zero_mem_bounded K (centralLowerFaceIds 0)
  have hspinHalf := centralLowerSpinCubeState_mem_centralHalfStates hspin
  exact Q'.pos_of_lt_of_le hforward
    (Q'.ge_of_eqv
      (centralPhysicalReflectedKernel_symm w hzeroHalf hspinHalf))

theorem centralLowerSpinCubeNormalizedJoint_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin <= K) :
    (0 : Q') < centralNormalizedPhysicalReflectedKernel
      w (Q'.le_of_lt hw) K 0
      (centralLowerSpinCubeState spin) zeroEdgeLabelling := by
  unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
  exact Q'.mul_pos
    (centralLowerSpinCubePhysicalReflectedKernel_pos hw hspin)
    (Q'.recipPos_pos _ _)

theorem centralLowerSpinCubeRowMarginal_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin <= K) :
    (0 : Q') < centralPhysicalRowMarginal
      w (Q'.le_of_lt hw) K 0
      (centralLowerSpinCubeState spin) := by
  unfold centralPhysicalRowMarginal
  have hmember := listQSum_member_le
    (centralNormalizedPhysicalReflectedKernel
      w (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState spin))
    (fun target =>
      centralNormalizedPhysicalReflectedKernel_nonnegative
        (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState spin) target)
    (centralHalfStates K 0)
    (zero_mem_bounded K (centralLowerFaceIds 0))
  exact Q'.pos_of_lt_of_le
    (centralLowerSpinCubeNormalizedJoint_pos hw hspin) hmember

/-- Every cutoff-admitted spin cube is a genuine positive physical state. -/
theorem centralLowerSpinCubeState_mem_centralPositiveHalfStates
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin <= K) :
    centralLowerSpinCubeState spin ∈
      centralPositiveHalfStates w (Q'.le_of_lt hw) K 0 := by
  exact mem_centralPositiveHalfStates_iff.mpr
    ⟨centralLowerSpinCubeState_mem_centralHalfStates hspin,
      centralLowerSpinCubeRowMarginal_pos hw hspin⟩

end YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay.centralLowerSpinCubePhysical_eq_state
#print axioms YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay.centralLowerSpinCubeState_mem_centralHalfStates
#print axioms YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay.centralLowerSpinCubeState_injective
#print axioms YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay.vacuum_linkMultiplicity_le_spinCube
#print axioms YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay.centralLowerSpinCube_linkProduct_pos
#print axioms YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay.centralLowerSpinCubePhysicalTerm_pos
#print axioms YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay.centralLowerSpinCubePhysicalReflectedKernel_pos
#print axioms YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay.centralPhysicalReflectedKernel_vacuum_spinCube_pos
#print axioms YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay.centralLowerSpinCubeState_mem_centralPositiveHalfStates
