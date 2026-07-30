/-
# Termwise domination of the BF4 vacuum row by the lower-cube row

The six fundamental faces of the central lower cube meet every lattice link
in either zero or two faces.  At a touched link the two added twice-spin-one
labels can be fused through their singlet channel.  This file combines that
finite geometric certificate with the constructive local injection from
`Z4FusionPairSingletInjection`.

The resulting comparison is termwise in the fixed-interface and target
labels.  It is therefore suitable for summation and normalization without a
minimum-row or carrier-cardinality loss.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CentralLowerCubePositiveRow
import YMGap.Continuum.Z4FusionPairSingletInjection

namespace YMGap.Continuum.BF4CentralLowerCubeRowDomination

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPairSingletInjection
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Vacuum-source and cube-source physical labellings -/

def centralVacuumSourcePhysical
    (boundary target : EdgeLabelling) : EdgeLabelling :=
  assembleReflectedSlabLabelling 0
    zeroEdgeLabelling boundary target

def centralCubeSourcePhysical
    (boundary target : EdgeLabelling) : EdgeLabelling :=
  assembleReflectedSlabLabelling 0
    centralLowerCubeState boundary target

theorem centralVacuumSourcePhysical_eq_zero_on_cube
    (boundary target : EdgeLabelling)
    {id : Nat} (hid : id ∈ centralLowerCubeFaceIds) :
    centralVacuumSourcePhysical boundary target id = 0 := by
  unfold centralVacuumSourcePhysical
  have hlower :=
    mem_centralLowerFaceIds.mp
      (centralLowerCubeFaceIds_subset_lower id hid)
  exact assembleReflectedSlabLabelling_lower hlower.1 hlower.2

theorem centralCubeSourcePhysical_eq_one_on_cube
    (boundary target : EdgeLabelling)
    {id : Nat} (hid : id ∈ centralLowerCubeFaceIds) :
    centralCubeSourcePhysical boundary target id = 1 := by
  unfold centralCubeSourcePhysical
  have hlower :=
    mem_centralLowerFaceIds.mp
      (centralLowerCubeFaceIds_subset_lower id hid)
  rw [assembleReflectedSlabLabelling_lower hlower.1 hlower.2]
  exact componentLabel_eq_one_iff.mpr hid

theorem centralCubeSourcePhysical_eq_vacuum_off_cube
    (boundary target : EdgeLabelling)
    {id : Nat} (hid : id ∉ centralLowerCubeFaceIds) :
    centralCubeSourcePhysical boundary target id =
      centralVacuumSourcePhysical boundary target id := by
  unfold centralCubeSourcePhysical centralVacuumSourcePhysical
    assembleReflectedSlabLabelling
  have hsource :
      centralLowerCubeState id = zeroEdgeLabelling id := by
    unfold centralLowerCubeState zeroEdgeLabelling
    exact componentLabel_eq_zero_of_not_mem hid
  by_cases hphysical :
      id ∈ slabPhysicalFaceEdges (centralExtent 0)
  · simp only [hphysical, if_pos]
    cases hside :
        plaquetteHalfSide 0
          (slabPlaquetteAt (centralExtent 0) id)
    · exact hsource
    · rfl
    · rfl
  · simp [hphysical]

/-! ## 2. The exact zero-or-two incidence certificate -/

def centralLowerCubeSelectedIncidentIds
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link) : List Nat :=
  (slabIncidentPlaqIds 1 link).filter
    (fun id => decide (id ∈ centralLowerCubeFaceIds))

def centralLowerCubeUnselectedIncidentIds
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link) : List Nat :=
  (slabIncidentPlaqIds 1 link).filter
    (fun id => !decide (id ∈ centralLowerCubeFaceIds))

/-- A closed cube has even local incidence: every corrected-slab link meets
its boundary in exactly zero or two faces. -/
theorem centralLowerCube_selected_length_zero_or_two
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link)
    (hlink : link ∈ boundaryCompleteSlabLinks 1) :
    (centralLowerCubeSelectedIncidentIds link).length = 0 ∨
      (centralLowerCubeSelectedIncidentIds link).length = 2 := by
  have hcheck :
      (boundaryCompleteSlabLinks 1).all
        (fun candidate =>
          decide
            ((centralLowerCubeSelectedIncidentIds candidate).length = 0 ∨
              (centralLowerCubeSelectedIncidentIds candidate).length = 2)) =
        true := by
    rfl
  exact of_decide_eq_true
    (List.all_eq_true.mp hcheck link hlink)

theorem centralLowerCube_incident_partition_perm
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    (centralLowerCubeSelectedIncidentIds link ++
        centralLowerCubeUnselectedIncidentIds link).Perm
      (slabIncidentPlaqIds 1 link) := by
  exact List.filter_append_perm
    (fun id => decide (id ∈ centralLowerCubeFaceIds))
    (slabIncidentPlaqIds 1 link)

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

theorem selected_map_vacuum_eq_replicate
    (boundary target : EdgeLabelling)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    (centralLowerCubeSelectedIncidentIds link).map
        (centralVacuumSourcePhysical boundary target) =
      List.replicate
        (centralLowerCubeSelectedIncidentIds link).length 0 := by
  apply map_eq_replicate_of_constant
  intro id hid
  apply centralVacuumSourcePhysical_eq_zero_on_cube
  exact of_decide_eq_true (List.mem_filter.mp hid).2

theorem selected_map_cube_eq_replicate
    (boundary target : EdgeLabelling)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    (centralLowerCubeSelectedIncidentIds link).map
        (centralCubeSourcePhysical boundary target) =
      List.replicate
        (centralLowerCubeSelectedIncidentIds link).length 1 := by
  apply map_eq_replicate_of_constant
  intro id hid
  apply centralCubeSourcePhysical_eq_one_on_cube
  exact of_decide_eq_true (List.mem_filter.mp hid).2

theorem unselected_map_cube_eq_vacuum
    (boundary target : EdgeLabelling)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    (centralLowerCubeUnselectedIncidentIds link).map
        (centralCubeSourcePhysical boundary target) =
      (centralLowerCubeUnselectedIncidentIds link).map
        (centralVacuumSourcePhysical boundary target) := by
  apply List.map_congr_left
  intro id hid
  apply centralCubeSourcePhysical_eq_vacuum_off_cube
  have hfalse : decide (id ∈ centralLowerCubeFaceIds) = false := by
    simpa using (List.mem_filter.mp hid).2
  exact of_decide_eq_false hfalse

/-! ## 3. Canonical incident-spin permutations -/

theorem vacuum_incident_spins_perm_selected_remainder
    (boundary target : EdgeLabelling)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    ((slabIncidentPlaqIds 1 link).map
        (centralVacuumSourcePhysical boundary target)).Perm
      (List.replicate
          (centralLowerCubeSelectedIncidentIds link).length 0 ++
        (centralLowerCubeUnselectedIncidentIds link).map
          (centralVacuumSourcePhysical boundary target)) := by
  have hperm :=
    (centralLowerCube_incident_partition_perm link).symm.map
      (centralVacuumSourcePhysical boundary target)
  rw [List.map_append,
    selected_map_vacuum_eq_replicate] at hperm
  exact hperm

theorem cube_incident_spins_perm_selected_remainder
    (boundary target : EdgeLabelling)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    ((slabIncidentPlaqIds 1 link).map
        (centralCubeSourcePhysical boundary target)).Perm
      (List.replicate
          (centralLowerCubeSelectedIncidentIds link).length 1 ++
        (centralLowerCubeUnselectedIncidentIds link).map
          (centralVacuumSourcePhysical boundary target)) := by
  have hperm :=
    (centralLowerCube_incident_partition_perm link).symm.map
      (centralCubeSourcePhysical boundary target)
  rw [List.map_append, selected_map_cube_eq_replicate,
    unselected_map_cube_eq_vacuum] at hperm
  exact hperm

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

/-! ## 4. Linkwise singlet-channel domination -/

/-- For every interface and target labelling, inserting the closed lower
cube cannot decrease any corrected-slab link multiplicity. -/
theorem centralVacuum_linkMultiplicity_le_cube
    {K : Nat} (hK : 1 ≤ K)
    (boundary target : EdgeLabelling)
    (hboundary : boundary ∈ centralBoundaryChannels K 0)
    (htarget : target ∈ centralHalfStates K 0)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link)
    (hlink : link ∈ boundaryCompleteSlabLinks 1) :
    slabExplicitLinkMultiplicity K 1
        (centralVacuumSourcePhysical boundary target) link ≤
      slabExplicitLinkMultiplicity K 1
        (centralCubeSourcePhysical boundary target) link := by
  let oldSpins :=
    (slabIncidentPlaqIds 1 link).map
      (centralVacuumSourcePhysical boundary target)
  let newSpins :=
    (slabIncidentPlaqIds 1 link).map
      (centralCubeSourcePhysical boundary target)
  let rest :=
    (centralLowerCubeUnselectedIncidentIds link).map
      (centralVacuumSourcePhysical boundary target)
  have hzeroSource :
      zeroEdgeLabelling ∈ centralHalfStates K 0 := by
    exact zero_mem_bounded K (centralLowerFaceIds 0)
  have hcubeSource :
      centralLowerCubeState ∈ centralHalfStates K 0 :=
    centralLowerCubeState_mem_centralHalfStates hK
  have holdPhysical :
      SlabFaceLabellingBounded K 1
        (centralVacuumSourcePhysical boundary target) := by
    unfold centralVacuumSourcePhysical
    exact assembleReflectedSlabLabelling_bounded
      hzeroSource hboundary htarget
  have hnewPhysical :
      SlabFaceLabellingBounded K 1
        (centralCubeSourcePhysical boundary target) := by
    unfold centralCubeSourcePhysical
    exact assembleReflectedSlabLabelling_bounded
      hcubeSource hboundary htarget
  have holdBounded : SpinsBounded K oldSpins := by
    exact slabIncidentSpins_bounded holdPhysical link
  have hnewBounded : SpinsBounded K newSpins := by
    exact slabIncidentSpins_bounded hnewPhysical link
  have hlength : oldSpins.length ≤ 6 := by
    unfold oldSpins
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six 1 link
  have holdPerm :
      oldSpins.Perm
        (List.replicate
            (centralLowerCubeSelectedIncidentIds link).length 0 ++
          rest) := by
    exact vacuum_incident_spins_perm_selected_remainder
      boundary target link
  have hnewPerm :
      newSpins.Perm
        (List.replicate
            (centralLowerCubeSelectedIncidentIds link).length 1 ++
          rest) := by
    exact cube_incident_spins_perm_selected_remainder
      boundary target link
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
    exact explicitValenceMultiplicity_physical_pair_replacement_le
      holdPerm hnewPerm hlength holdBounded hnewBounded

/-! ## 5. Product and face-factor domination -/

private theorem natListProduct_mono_on
    {A : Type} (left right : A → Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
        natListProduct left items ≤ natListProduct right items
  | [], _ => Nat.le_refl 1
  | head :: tail, hle => by
      simp only [natListProduct]
      exact Nat.mul_le_mul
        (hle head List.mem_cons_self)
        (natListProduct_mono_on left right tail
          (fun item hitem =>
            hle item (List.mem_cons_of_mem head hitem)))

theorem centralVacuum_linkMultiplicityProduct_le_cube
    {K : Nat} (hK : 1 ≤ K)
    (boundary target : EdgeLabelling)
    (hboundary : boundary ∈ centralBoundaryChannels K 0)
    (htarget : target ∈ centralHalfStates K 0) :
    slabExplicitLinkMultiplicityProduct K 1
        (centralVacuumSourcePhysical boundary target) ≤
      slabExplicitLinkMultiplicityProduct K 1
        (centralCubeSourcePhysical boundary target) := by
  unfold slabExplicitLinkMultiplicityProduct
  exact natListProduct_mono_on _ _
    (boundaryCompleteSlabLinks 1)
    (fun link hlink =>
      centralVacuum_linkMultiplicity_le_cube
        hK boundary target hboundary htarget link hlink)

private theorem qmul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem eliminateLinks_congr_on
    (left right : Nat → Q') :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → left id ≈ right id) →
        eliminateLinks left ids ≈ eliminateLinks right ids
  | [], _ => Q'.eqv_refl _
  | id :: rest, hagree =>
      qmul_congr
        (hagree id List.mem_cons_self)
        (eliminateLinks_congr_on left right rest
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem id hitem)))

private theorem rearrange_pointwise_products
    (a b c d : Q') :
    (a * b) * (c * d) ≈
      (a * c) * (b * d) := by
  show ((a * b) * (c * d)).num *
      (((a * c) * (b * d)).den : Int) =
    ((a * c) * (b * d)).num *
      (((a * b) * (c * d)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem eliminateLinks_pointwise_mul
    (left right : Nat → Q') :
    ∀ ids : List Nat,
      eliminateLinks
          (fun id => left id * right id) ids ≈
        eliminateLinks left ids *
          eliminateLinks right ids
  | [] => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | id :: rest => by
      unfold eliminateLinks
      refine Q'.eqv_trans _
        ((left id * right id) *
          (eliminateLinks left rest *
            eliminateLinks right rest)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (eliminateLinks_pointwise_mul left right rest)
      · exact rearrange_pointwise_products
          (left id) (right id)
          (eliminateLinks left rest)
          (eliminateLinks right rest)

private theorem eliminateLinks_indicator_pow
    (selected : List Nat) (coefficient : Q') :
    ∀ ids : List Nat,
      eliminateLinks
          (fun id =>
            if id ∈ selected then coefficient else 1)
          ids ≈
        coefficient ^
          (ids.filter
            (fun id => decide (id ∈ selected))).length
  | [] => Q'.eqv_refl _
  | id :: rest => by
      by_cases hselected : id ∈ selected
      · simp only [eliminateLinks, hselected, if_pos,
          List.filter_cons, decide_true, List.length_cons,
          Q'.pow_succ]
        exact qmul_congr (Q'.eqv_refl _)
          (eliminateLinks_indicator_pow selected coefficient rest)
      · simp only [eliminateLinks, hselected,
          List.filter_cons, decide_false]
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left 1 _ _
            (eliminateLinks_indicator_pow
              selected coefficient rest))
          (Q'.one_mul_eqv _)

/-- At each face, the cube source coefficient is the vacuum-source
coefficient multiplied by the fundamental activity precisely on the six
cube faces. -/
theorem centralCube_faceCoefficient_factor
    (w : Q') {K : Nat} (hK : 1 ≤ K)
    (boundary target : EdgeLabelling) (id : Nat) :
    coeffAt (heatKernelPacket K w)
        (centralCubeSourcePhysical boundary target id) ≈
      (if id ∈ centralLowerCubeFaceIds then coeffW w 1 else 1) *
        coeffAt (heatKernelPacket K w)
          (centralVacuumSourcePhysical boundary target id) := by
  by_cases hcube : id ∈ centralLowerCubeFaceIds
  · rw [centralCubeSourcePhysical_eq_one_on_cube
        boundary target hcube,
      centralVacuumSourcePhysical_eq_zero_on_cube
        boundary target hcube,
      coeffAt_heatKernelPacket (by omega),
      coeffAt_heatKernelPacket (by omega),
      coeffW_zero, if_pos hcube]
    exact Q'.eqv_symm (Q'.mul_one_eqv _)
  · rw [centralCubeSourcePhysical_eq_vacuum_off_cube
        boundary target hcube, if_neg hcube]
    exact Q'.eqv_symm (Q'.one_mul_eqv _)

/-- Exact face-factor ratio: the only change is one fundamental coefficient
on each of the six lower-cube faces. -/
theorem centralCubePhysicalFaceFactor_eqv_activity_mul_vacuum
    (w : Q') {K : Nat} (hK : 1 ≤ K)
    (boundary target : EdgeLabelling) :
    slabParametricKPhysicalFaceFactor w K 1
        (centralCubeSourcePhysical boundary target) ≈
      (coeffW w 1) ^ 6 *
        slabParametricKPhysicalFaceFactor w K 1
          (centralVacuumSourcePhysical boundary target) := by
  unfold slabParametricKPhysicalFaceFactor
  have hpointwise :
      eliminateLinks
          (fun id =>
            coeffAt (heatKernelPacket K w)
              (centralCubeSourcePhysical boundary target id))
          (slabPhysicalFaceEdges 1) ≈
        eliminateLinks
          (fun id =>
            (if id ∈ centralLowerCubeFaceIds
              then coeffW w 1 else 1) *
            coeffAt (heatKernelPacket K w)
              (centralVacuumSourcePhysical boundary target id))
          (slabPhysicalFaceEdges 1) := by
    apply eliminateLinks_congr_on
    intro id _
    exact centralCube_faceCoefficient_factor
      w hK boundary target id
  have hsplit :=
    eliminateLinks_pointwise_mul
      (fun id =>
        if id ∈ centralLowerCubeFaceIds
        then coeffW w 1 else 1)
      (fun id =>
        coeffAt (heatKernelPacket K w)
          (centralVacuumSourcePhysical boundary target id))
      (slabPhysicalFaceEdges 1)
  have hpower :=
    eliminateLinks_indicator_pow
      centralLowerCubeFaceIds (coeffW w 1)
      (slabPhysicalFaceEdges 1)
  have hcount :
      ((slabPhysicalFaceEdges 1).filter
        (fun id =>
          decide (id ∈ centralLowerCubeFaceIds))).length = 6 := by
    decide
  rw [hcount] at hpower
  exact Q'.eqv_trans _ _ _ hpointwise
    (Q'.eqv_trans _ _ _ hsplit
      (Q'.mul_eqv_congr_right _ _ _
        hpower))

private theorem slabParametricCoefficient_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (K spin : Nat) :
    (0 : Q') ≤ coeffAt (heatKernelPacket K w) spin := by
  by_cases hspin : spin < K + 1
  · rw [coeffAt_heatKernelPacket hspin]
    exact coeffW_nonneg hw spin
  · have hlarge : K < spin := by omega
    rw [coeffAt_of_gt (heatKernelPacket K w) hlarge]
    exact Q'.le_refl' 0

private theorem eliminateLinks_nonnegative
    (value : Nat → Q') (hvalue : ∀ id, (0 : Q') ≤ value id) :
    ∀ ids : List Nat, (0 : Q') ≤ eliminateLinks value ids
  | [] => Q'.zero_le_one
  | head :: tail =>
      Q'.mul_nonneg _ _ (hvalue head)
        (eliminateLinks_nonnegative value hvalue tail)

theorem centralCubePhysicalFaceFactor_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K : Nat) (boundary target : EdgeLabelling) :
    (0 : Q') ≤
      slabParametricKPhysicalFaceFactor w K 1
        (centralCubeSourcePhysical boundary target) := by
  unfold slabParametricKPhysicalFaceFactor
  exact eliminateLinks_nonnegative _
    (fun id =>
      slabParametricCoefficient_nonnegative hw K
        (centralCubeSourcePhysical boundary target id)) _

private theorem qOfNat_mono {left right : Nat}
    (hle : left ≤ right) :
    Q'.ofNat left ≤ Q'.ofNat right := by
  show (Int.ofNat left) * (1 : Int) ≤
    (Int.ofNat right) * (1 : Int)
  rw [Int.mul_one, Int.mul_one]
  exact Int.ofNat_le.mpr hle

/-- **Termwise physical domination.**  For every fixed interface and target,
the cube summand dominates the corresponding vacuum summand multiplied by
the exact six-face activity. -/
theorem centralCubePhysicalTerm_dominates_activity_mul_vacuum
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K : Nat} (hK : 1 ≤ K)
    (boundary target : EdgeLabelling)
    (hboundary : boundary ∈ centralBoundaryChannels K 0)
    (htarget : target ∈ centralHalfStates K 0) :
    (coeffW w 1) ^ 6 *
        slabParametricKPhysicalTerm w K 1
          (centralVacuumSourcePhysical boundary target) ≤
      slabParametricKPhysicalTerm w K 1
        (centralCubeSourcePhysical boundary target) := by
  let oldFace :=
    slabParametricKPhysicalFaceFactor w K 1
      (centralVacuumSourcePhysical boundary target)
  let newFace :=
    slabParametricKPhysicalFaceFactor w K 1
      (centralCubeSourcePhysical boundary target)
  let oldLinks :=
    slabExplicitLinkMultiplicityProduct K 1
      (centralVacuumSourcePhysical boundary target)
  let newLinks :=
    slabExplicitLinkMultiplicityProduct K 1
      (centralCubeSourcePhysical boundary target)
  have hface :
      newFace ≈ (coeffW w 1) ^ 6 * oldFace :=
    centralCubePhysicalFaceFactor_eqv_activity_mul_vacuum
      w hK boundary target
  have hlinks : oldLinks ≤ newLinks :=
    centralVacuum_linkMultiplicityProduct_le_cube
      hK boundary target hboundary htarget
  have hqLinks : Q'.ofNat oldLinks ≤ Q'.ofNat newLinks :=
    qOfNat_mono hlinks
  have hnewFaceNonnegative : (0 : Q') ≤ newFace :=
    centralCubePhysicalFaceFactor_nonnegative
      hw K boundary target
  unfold slabParametricKPhysicalTerm
  change
    (coeffW w 1) ^ 6 *
        (oldFace * Q'.ofNat oldLinks) ≤
      newFace * Q'.ofNat newLinks
  have hregroup :
      (coeffW w 1) ^ 6 *
          (oldFace * Q'.ofNat oldLinks) ≈
        newFace * Q'.ofNat oldLinks := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          ((coeffW w 1) ^ 6) oldFace
          (Q'.ofNat oldLinks)))
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm hface))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hregroup)
    (Q'.mul_le_mul_of_nonneg_left
      (Q'.ofNat oldLinks) (Q'.ofNat newLinks)
      newFace hqLinks hnewFaceNonnegative)

private theorem listQSum_scaled_termwise_le
    {A : Type} (scale : Q') (oldValue newValue : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items →
        scale * oldValue item ≤ newValue item) →
      (∀ item, item ∈ items → (0 : Q') ≤ newValue item) →
        scale * listQSum oldValue items ≤
          listQSum newValue items
  | [], _, _ => by
      change scale * 0 ≤ 0
      exact Q'.le_of_eqv (Q'.mul_zero_eqv scale)
  | head :: tail, hterm, hnew => by
      have hhead :=
        hterm head List.mem_cons_self
      have htail :=
        listQSum_scaled_termwise_le
          scale oldValue newValue tail
          (fun item hitem =>
            hterm item (List.mem_cons_of_mem head hitem))
          (fun item hitem =>
            hnew item (List.mem_cons_of_mem head hitem))
      have hsplit :
          scale *
              (oldValue head + listQSum oldValue tail) ≈
            scale * oldValue head +
              scale * listQSum oldValue tail :=
        Q'.mul_add_eqv scale
          (oldValue head) (listQSum oldValue tail)
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv hsplit)
        (Q'.add_le_add hhead htail)

/-- The raw reflected cube kernel dominates the raw vacuum kernel at every
target, with the same six-face activity and no summation loss. -/
theorem centralCubeReflectedKernel_dominates_activity_mul_vacuum
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K : Nat} (hK : 1 ≤ K)
    (target : EdgeLabelling)
    (htarget : target ∈ centralHalfStates K 0) :
    (coeffW w 1) ^ 6 *
        centralPhysicalReflectedKernel
          w K 0 zeroEdgeLabelling target ≤
      centralPhysicalReflectedKernel
        w K 0 centralLowerCubeState target := by
  unfold centralPhysicalReflectedKernel
  exact listQSum_scaled_termwise_le
    ((coeffW w 1) ^ 6)
    (fun boundary =>
      slabParametricKPhysicalTerm w K 1
        (centralVacuumSourcePhysical boundary target))
    (fun boundary =>
      slabParametricKPhysicalTerm w K 1
        (centralCubeSourcePhysical boundary target))
    (centralBoundaryChannels K 0)
    (fun boundary hboundary =>
      centralCubePhysicalTerm_dominates_activity_mul_vacuum
        hw hK boundary target hboundary htarget)
    (fun boundary _ =>
      slabParametricKPhysicalTerm_nonnegative
        hw K 1
        (centralCubeSourcePhysical boundary target))

/-! ## 6. Normalized row domination -/

theorem centralCubeNormalizedKernel_dominates_activity_mul_vacuum
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K : Nat} (hK : 1 ≤ K)
    (target : EdgeLabelling)
    (htarget : target ∈ centralHalfStates K 0) :
    (coeffW w 1) ^ 6 *
        centralNormalizedPhysicalReflectedKernel
          w hw K 0 zeroEdgeLabelling target ≤
      centralNormalizedPhysicalReflectedKernel
        w hw K 0 centralLowerCubeState target := by
  let partition :=
    slabParametricKPhysicalPartition w K 1
  let hpartition :=
    slabParametricKPhysicalPartition_pos hw K 1
  let reciprocal := Q'.recipPos partition hpartition
  have hraw :=
    centralCubeReflectedKernel_dominates_activity_mul_vacuum
      hw hK target htarget
  have hreciprocal : (0 : Q') ≤ reciprocal :=
    Q'.le_of_lt (Q'.recipPos_pos partition hpartition)
  unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
  change
    (coeffW w 1) ^ 6 *
        (centralPhysicalReflectedKernel
            w K 0 zeroEdgeLabelling target *
          reciprocal) ≤
      centralPhysicalReflectedKernel
          w K 0 centralLowerCubeState target *
        reciprocal
  have hregroup :
      (coeffW w 1) ^ 6 *
          (centralPhysicalReflectedKernel
              w K 0 zeroEdgeLabelling target *
            reciprocal) ≈
        ((coeffW w 1) ^ 6 *
            centralPhysicalReflectedKernel
              w K 0 zeroEdgeLabelling target) *
          reciprocal :=
    Q'.eqv_symm
      (Q'.mul_assoc_eqv
        ((coeffW w 1) ^ 6)
        (centralPhysicalReflectedKernel
          w K 0 zeroEdgeLabelling target)
        reciprocal)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hregroup)
    (Q'.mul_le_mul_of_nonneg_right
      _ _ reciprocal hraw hreciprocal)

/-- The complete normalized cube-row marginal dominates the vacuum-row
marginal by the exact six-face activity.  This is the quantitative result
for which mere strict positivity of the cube row was insufficient. -/
theorem centralCubeRowMarginal_dominates_activity_mul_vacuum
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K : Nat} (hK : 1 ≤ K) :
    (coeffW w 1) ^ 6 *
        centralPhysicalRowMarginal
          w hw K 0 zeroEdgeLabelling ≤
      centralPhysicalRowMarginal
        w hw K 0 centralLowerCubeState := by
  unfold centralPhysicalRowMarginal
  exact listQSum_scaled_termwise_le
    ((coeffW w 1) ^ 6)
    (centralNormalizedPhysicalReflectedKernel
      w hw K 0 zeroEdgeLabelling)
    (centralNormalizedPhysicalReflectedKernel
      w hw K 0 centralLowerCubeState)
    (centralHalfStates K 0)
    (fun target htarget =>
      centralCubeNormalizedKernel_dominates_activity_mul_vacuum
        hw hK target htarget)
    (fun target _ =>
      centralNormalizedPhysicalReflectedKernel_nonnegative
        hw K 0 centralLowerCubeState target)

/-! ## 7. From cube activity to the `5/6` vacuum calibration -/

private theorem listQSum_nonnegative
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A, (0 : Q') ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _
        (hvalue head)
        (listQSum_nonnegative value hvalue tail)

private theorem listQSum_member_le_nonnegative
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A}, item ∈ items →
      value item ≤ listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative value hvalue tail)
      · have ih :=
          listQSum_member_le_nonnegative
            value hvalue tail htail
        have hmono :
            listQSum value tail ≤
              value head + listQSum value tail :=
          by
            have h :=
              Q'.add_le_add_right
                (0 : Q') (value head)
                (listQSum value tail)
                (hvalue head)
            rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih hmono

private theorem two_members_le_listQSum
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {left right : A},
      items.Nodup →
      left ∈ items →
      right ∈ items →
      left ≠ right →
        value left + value right ≤ listQSum value items
  | [], _, _, _, hleft, _, _ => absurd hleft List.not_mem_nil
  | head :: tail, left, right, hnodup, hleft, hright, hne => by
      have htailNodup := (List.nodup_cons.mp hnodup).2
      rcases List.mem_cons.mp hleft with rfl | hleftTail
      · have hrightTail : right ∈ tail := by
          rcases List.mem_cons.mp hright with hrightHead | hrightTail
          · exact False.elim (hne hrightHead.symm)
          · exact hrightTail
        exact Q'.add_le_add_left
          (value left) (value right)
          (listQSum value tail)
          (listQSum_member_le_nonnegative
            value hvalue tail hrightTail)
      · rcases List.mem_cons.mp hright with rfl | hrightTail
        · have hmember :=
            listQSum_member_le_nonnegative
              value hvalue tail hleftTail
          have hadd :=
            Q'.add_le_add_right
              (value left) (listQSum value tail)
              (value right) hmember
          exact Q'.le_trans' _ _ _ hadd
            (Q'.le_of_eqv
              (Q'.add_comm_eqv
                (listQSum value tail) (value right)))
        · have ih :=
            two_members_le_listQSum value hvalue tail
              htailNodup hleftTail hrightTail hne
          have htailLe :
              listQSum value tail ≤
                value head + listQSum value tail :=
            by
              have h :=
                Q'.add_le_add_right
                  (0 : Q') (value head)
                  (listQSum value tail)
                  (hvalue head)
              rwa [Q'.zero_add'] at h
          exact Q'.le_trans' _ _ _ ih htailLe

theorem centralVacuum_add_cube_marginal_le_one
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K : Nat} (hK : 1 ≤ K) :
    centralPhysicalRowMarginal
          w hw K 0 zeroEdgeLabelling +
        centralPhysicalRowMarginal
          w hw K 0 centralLowerCubeState ≤
      1 := by
  have hsum :=
    two_members_le_listQSum
      (centralPhysicalRowMarginal w hw K 0)
      (fun state =>
        centralPhysicalRowMarginal_nonnegative
          hw K 0 state)
      (centralHalfStates K 0)
      (centralHalfStates_nodup K 0)
      (zero_mem_bounded K (centralLowerFaceIds 0))
      (centralLowerCubeState_mem_centralHalfStates hK)
      (fun heq =>
        centralLowerCubeState_ne_zero heq.symm)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (centralPhysicalRowMarginal_total_one
        w hw K 0))

def cubeActivityOneFifth : Q' :=
  Q'.mkPos 1 5 (by decide)

private def cubeActivitySixFifths : Q' :=
  Q'.mkPos 6 5 (by decide)

/-- An exact `1/5` lower bound on the six-face activity supplies the required
physical stationary-vacuum calibration `pi(0) ≤ 5/6`. -/
theorem centralVacuumRowMarginal_le_fiveSixths_of_cubeActivity
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K : Nat} (hK : 1 ≤ K)
    (hactivity :
      cubeActivityOneFifth ≤ (coeffW w 1) ^ 6) :
    centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling ≤
      Q'.mkPos 5 6 (by decide) := by
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K 0 zeroEdgeLabelling
  let picube :=
    centralPhysicalRowMarginal
      w hw K 0 centralLowerCubeState
  have hpi0nonnegative : (0 : Q') ≤ pi0 :=
    centralPhysicalRowMarginal_nonnegative
      hw K 0 zeroEdgeLabelling
  have hactivityScaled :
      cubeActivityOneFifth * pi0 ≤
        (coeffW w 1) ^ 6 * pi0 :=
    Q'.mul_le_mul_of_nonneg_right
      cubeActivityOneFifth ((coeffW w 1) ^ 6)
      pi0 hactivity hpi0nonnegative
  have hcube :
      (coeffW w 1) ^ 6 * pi0 ≤ picube :=
    centralCubeRowMarginal_dominates_activity_mul_vacuum
      hw hK
  have hpair : pi0 + picube ≤ 1 :=
    centralVacuum_add_cube_marginal_le_one hw hK
  have hsum :
      pi0 + cubeActivityOneFifth * pi0 ≤ 1 :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_left pi0
        (cubeActivityOneFifth * pi0) picube
        (Q'.le_trans' _ _ _
          hactivityScaled hcube))
      hpair
  have hsixFifths :
      pi0 + cubeActivityOneFifth * pi0 ≈
        cubeActivitySixFifths * pi0 := by
    calc
      pi0 + cubeActivityOneFifth * pi0 ≈
          pi0 * 1 + cubeActivityOneFifth * pi0 :=
        Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_symm (Q'.mul_one_eqv pi0))
      _ ≈ pi0 * 1 + pi0 * cubeActivityOneFifth :=
        Q'.add_eqv_congr_left _ _ _
          (Q'.mul_comm_eqv cubeActivityOneFifth pi0)
      _ ≈ pi0 * (1 + cubeActivityOneFifth) :=
        Q'.eqv_symm
          (Q'.mul_add_eqv pi0 1 cubeActivityOneFifth)
      _ ≈ pi0 * cubeActivitySixFifths :=
        Q'.mul_eqv_congr_left pi0 _ _
          (by
            unfold cubeActivityOneFifth cubeActivitySixFifths
            decide)
      _ ≈ cubeActivitySixFifths * pi0 :=
        Q'.mul_comm_eqv pi0 cubeActivitySixFifths
  have hsixBound :
      cubeActivitySixFifths * pi0 ≤ 1 :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hsixFifths) hsum
  have hscaled :=
    Q'.mul_le_mul_of_nonneg_left
      (cubeActivitySixFifths * pi0) 1
      (Q'.mkPos 5 6 (by decide))
      hsixBound (by decide)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (by
      change
        Q'.mkPos 5 6 (by decide) *
            (cubeActivitySixFifths * pi0) ≈ pi0
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (Q'.mkPos 5 6 (by decide))
            cubeActivitySixFifths pi0))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ pi0
            (by decide))
          (Q'.one_mul_eqv pi0))))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv
        (Q'.mul_one_eqv
          (Q'.mkPos 5 6 (by decide)))))

def cubeActivityWeightFloor : Q' :=
  Q'.mkPos 3 4 (by decide)

/-- The transparent AF-window criterion: `w ≥ 3/4` already makes the exact
six-face fundamental activity at least `1/5`. -/
theorem cubeActivity_oneFifth_le_of_threeQuarters_le
    {w : Q'} (hw : cubeActivityWeightFloor ≤ w) :
    cubeActivityOneFifth ≤ (coeffW w 1) ^ 6 := by
  have hcoefficient :
      coeffW cubeActivityWeightFloor 1 ≤ coeffW w 1 :=
    coeffW_mono_w
      (by
        unfold cubeActivityWeightFloor
        decide)
      hw 1
  have hpower :
      (coeffW cubeActivityWeightFloor 1) ^ 6 ≤
        (coeffW w 1) ^ 6 :=
    pow_le_pow_of_le
      (coeffW_nonneg
        (by
          unfold cubeActivityWeightFloor
          decide) 1)
      hcoefficient 6
  exact Q'.le_trans' _ _ _
    (by
      unfold cubeActivityOneFifth cubeActivityWeightFloor
      decide)
    hpower

theorem centralVacuumRowMarginal_le_fiveSixths_of_threeQuarters_le
    {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : cubeActivityWeightFloor ≤ w)
    {K : Nat} (hK : 1 ≤ K) :
    centralPhysicalRowMarginal
        w hw0 K 0 zeroEdgeLabelling ≤
      Q'.mkPos 5 6 (by decide) :=
  centralVacuumRowMarginal_le_fiveSixths_of_cubeActivity
    hw0 hK
    (cubeActivity_oneFifth_le_of_threeQuarters_le hw)

end YMGap.Continuum.BF4CentralLowerCubeRowDomination

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.centralLowerCube_selected_length_zero_or_two
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.centralLowerCube_incident_partition_perm
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.selected_map_vacuum_eq_replicate
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.selected_map_cube_eq_replicate
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.unselected_map_cube_eq_vacuum
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.vacuum_incident_spins_perm_selected_remainder
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.cube_incident_spins_perm_selected_remainder
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.centralVacuum_linkMultiplicity_le_cube
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.centralVacuum_linkMultiplicityProduct_le_cube
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.centralCube_faceCoefficient_factor
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.centralCubePhysicalFaceFactor_eqv_activity_mul_vacuum
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.centralCubePhysicalTerm_dominates_activity_mul_vacuum
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.centralCubeReflectedKernel_dominates_activity_mul_vacuum
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.centralCubeNormalizedKernel_dominates_activity_mul_vacuum
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.centralCubeRowMarginal_dominates_activity_mul_vacuum
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.centralVacuum_add_cube_marginal_le_one
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.centralVacuumRowMarginal_le_fiveSixths_of_cubeActivity
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.cubeActivity_oneFifth_le_of_threeQuarters_le
#print axioms YMGap.Continuum.BF4CentralLowerCubeRowDomination.centralVacuumRowMarginal_le_fiveSixths_of_threeQuarters_le
