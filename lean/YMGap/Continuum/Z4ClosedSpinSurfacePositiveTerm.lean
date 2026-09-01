/-
# Positive physical terms from closed equal-spin surfaces

A finite corrected-slab support is called closed here when every physical
link meets it in either zero or two faces.  Labelling every selected face by
the same admitted SU(2) twice-spin then retains a singlet channel at every
touched link.  This file packages that geometric condition as constructive
data and proves strict positivity of the resulting production term for every
positive coupling.

The compiler is finite-slab and cutoff-local.  It supplies no probability,
cutoff-uniform estimate, continuum limit, or Clay mass-gap conclusion.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.Z4FusionEqualPairSingletInjection
import YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

namespace YMGap.Continuum.Z4ClosedSpinSurfacePositiveTerm

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FusionEqualPairSingletInjection
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

/-! ## 1. Geometric input and its equal-spin labelling -/

/-- A literal corrected-slab face support with zero-or-two incidence at every
physical link.  The support inclusion is retained as data so later geometric
consumers cannot hide faces outside the production slab. -/
structure ClosedSpinSurface (extent : Nat) : Type where
  faceIds : List Nat
  faceIds_subset_physical : ∀ id, id ∈ faceIds →
    id ∈ slabPhysicalFaceEdges extent
  selected_length_zero_or_two : ∀ link,
    link ∈ boundaryCompleteSlabLinks extent →
      ((slabIncidentPlaqIds extent link).filter
        (fun id => decide (id ∈ faceIds))).length = 0 ∨
      ((slabIncidentPlaqIds extent link).filter
        (fun id => decide (id ∈ faceIds))).length = 2

namespace ClosedSpinSurface

/-- Put one common twice-spin label on the selected closed surface. -/
def spinLabelling {extent : Nat}
    (surface : ClosedSpinSurface extent) (spin : Nat) : EdgeLabelling :=
  fun id => if id ∈ surface.faceIds then spin else 0

theorem spinLabelling_eq_spin_on
    {extent spin id : Nat} (surface : ClosedSpinSurface extent)
    (hid : id ∈ surface.faceIds) :
    surface.spinLabelling spin id = spin := by
  simp [spinLabelling, hid]

theorem spinLabelling_eq_zero_off
    {extent spin id : Nat} (surface : ClosedSpinSurface extent)
    (hid : id ∉ surface.faceIds) :
    surface.spinLabelling spin id = 0 := by
  simp [spinLabelling, hid]

theorem spinLabelling_le
    {extent : Nat} (surface : ClosedSpinSurface extent)
    (spin id : Nat) : surface.spinLabelling spin id ≤ spin := by
  unfold spinLabelling
  by_cases hid : id ∈ surface.faceIds <;> simp [hid]

def selectedIncidentIds
    {extent : Nat} (surface : ClosedSpinSurface extent)
    (link : Z4Link) : List Nat :=
  (slabIncidentPlaqIds extent link).filter
    (fun id => decide (id ∈ surface.faceIds))

def unselectedIncidentIds
    {extent : Nat} (surface : ClosedSpinSurface extent)
    (link : Z4Link) : List Nat :=
  (slabIncidentPlaqIds extent link).filter
    (fun id => !decide (id ∈ surface.faceIds))

theorem selectedIncidentIds_length_zero_or_two
    {extent : Nat} (surface : ClosedSpinSurface extent)
    (link : Z4Link) (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    (surface.selectedIncidentIds link).length = 0 ∨
      (surface.selectedIncidentIds link).length = 2 :=
  surface.selected_length_zero_or_two link hlink

theorem incident_partition_perm
    {extent : Nat} (surface : ClosedSpinSurface extent)
    (link : Z4Link) :
    (surface.selectedIncidentIds link ++
        surface.unselectedIncidentIds link).Perm
      (slabIncidentPlaqIds extent link) := by
  exact List.filter_append_perm
    (fun id => decide (id ∈ surface.faceIds))
    (slabIncidentPlaqIds extent link)

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

theorem selected_map_spin_eq_replicate
    {extent : Nat} (surface : ClosedSpinSurface extent)
    (spin : Nat) (link : Z4Link) :
    (surface.selectedIncidentIds link).map
        (surface.spinLabelling spin) =
      List.replicate (surface.selectedIncidentIds link).length spin := by
  apply map_eq_replicate_of_constant
  intro id hid
  apply surface.spinLabelling_eq_spin_on
  exact of_decide_eq_true (List.mem_filter.mp hid).2

theorem unselected_map_spin_eq_zero
    {extent : Nat} (surface : ClosedSpinSurface extent)
    (spin : Nat) (link : Z4Link) :
    (surface.unselectedIncidentIds link).map
        (surface.spinLabelling spin) =
      (surface.unselectedIncidentIds link).map zeroEdgeLabelling := by
  apply List.map_congr_left
  intro id hid
  apply surface.spinLabelling_eq_zero_off
  have hfalse : decide (id ∈ surface.faceIds) = false := by
    simpa using (List.mem_filter.mp hid).2
  exact of_decide_eq_false hfalse

theorem zero_incident_spins_perm_selected_remainder
    {extent : Nat} (surface : ClosedSpinSurface extent)
    (link : Z4Link) :
    ((slabIncidentPlaqIds extent link).map zeroEdgeLabelling).Perm
      (List.replicate (surface.selectedIncidentIds link).length 0 ++
        (surface.unselectedIncidentIds link).map zeroEdgeLabelling) := by
  have hperm := (surface.incident_partition_perm link).symm.map
    zeroEdgeLabelling
  rw [List.map_append] at hperm
  have hselected :
      (surface.selectedIncidentIds link).map zeroEdgeLabelling =
        List.replicate (surface.selectedIncidentIds link).length 0 := by
    apply map_eq_replicate_of_constant
    intro _ _
    rfl
  rw [hselected] at hperm
  exact hperm

theorem spin_incident_spins_perm_selected_remainder
    {extent : Nat} (surface : ClosedSpinSurface extent)
    (spin : Nat) (link : Z4Link) :
    ((slabIncidentPlaqIds extent link).map
        (surface.spinLabelling spin)).Perm
      (List.replicate (surface.selectedIncidentIds link).length spin ++
        (surface.unselectedIncidentIds link).map zeroEdgeLabelling) := by
  have hperm := (surface.incident_partition_perm link).symm.map
    (surface.spinLabelling spin)
  rw [List.map_append, surface.selected_map_spin_eq_replicate,
    surface.unselected_map_spin_eq_zero] at hperm
  exact hperm

/-! ## 3. Link and product positivity -/

private theorem zeroPhysical_bounded (K extent : Nat) :
    SlabFaceLabellingBounded K extent zeroEdgeLabelling := by
  intro _ _
  exact Nat.zero_le K

private theorem spinPhysical_bounded
    {extent K spin : Nat} (surface : ClosedSpinSurface extent)
    (hspin : spin ≤ K) :
    SlabFaceLabellingBounded K extent (surface.spinLabelling spin) := by
  intro id _
  exact Nat.le_trans (surface.spinLabelling_le spin id) hspin

theorem vacuum_linkMultiplicity_le_spin
    {extent K spin : Nat} (surface : ClosedSpinSurface extent)
    (hspin : spin ≤ K) (link : Z4Link)
    (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    slabExplicitLinkMultiplicity K extent zeroEdgeLabelling link ≤
      slabExplicitLinkMultiplicity K extent
        (surface.spinLabelling spin) link := by
  let oldSpins :=
    (slabIncidentPlaqIds extent link).map zeroEdgeLabelling
  let newSpins :=
    (slabIncidentPlaqIds extent link).map (surface.spinLabelling spin)
  let rest :=
    (surface.unselectedIncidentIds link).map zeroEdgeLabelling
  have holdBounded : SpinsBounded K oldSpins := by
    exact slabIncidentSpins_bounded (zeroPhysical_bounded K extent) link
  have hnewBounded : SpinsBounded K newSpins := by
    exact slabIncidentSpins_bounded
      (surface.spinPhysical_bounded hspin) link
  have hlength : oldSpins.length ≤ 6 := by
    unfold oldSpins
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six extent link
  have holdPerm :
      oldSpins.Perm
        (List.replicate (surface.selectedIncidentIds link).length 0 ++
          rest) := by
    exact surface.zero_incident_spins_perm_selected_remainder link
  have hnewPerm :
      newSpins.Perm
        (List.replicate (surface.selectedIncidentIds link).length spin ++
          rest) := by
    exact surface.spin_incident_spins_perm_selected_remainder spin link
  rcases surface.selectedIncidentIds_length_zero_or_two link hlink with
      hzero | htwo
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

theorem linkMultiplicity_pos
    {extent K spin : Nat} (surface : ClosedSpinSurface extent)
    (hspin : spin ≤ K) (link : Z4Link)
    (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    0 < slabExplicitLinkMultiplicity K extent
      (surface.spinLabelling spin) link := by
  have hle := surface.vacuum_linkMultiplicity_le_spin hspin link hlink
  rw [slabExplicitLinkMultiplicity_zero_eq_one K extent link] at hle
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

theorem linkProduct_pos
    {extent K spin : Nat} (surface : ClosedSpinSurface extent)
    (hspin : spin ≤ K) :
    0 < slabExplicitLinkMultiplicityProduct K extent
      (surface.spinLabelling spin) := by
  unfold slabExplicitLinkMultiplicityProduct
  exact natListProduct_pos_of_pointwise
    (slabExplicitLinkMultiplicity K extent (surface.spinLabelling spin))
    (boundaryCompleteSlabLinks extent)
    (fun link hlink => surface.linkMultiplicity_pos hspin link hlink)

/-! ## 4. Strict physical-term positivity -/

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

/-- Every admitted common spin on a closed support gives a strictly positive
production summand. -/
theorem physicalTerm_pos
    {extent : Nat} (surface : ClosedSpinSurface extent)
    {w : Q'} (hw : (0 : Q') < w)
    {K spin : Nat} (hspin : spin ≤ K) :
    (0 : Q') < slabParametricKPhysicalTerm w K extent
      (surface.spinLabelling spin) := by
  have hface :
      (0 : Q') < slabParametricKPhysicalFaceFactor w K extent
        (surface.spinLabelling spin) := by
    unfold slabParametricKPhysicalFaceFactor
    apply eliminateLinks_pos
    intro id
    have hid : surface.spinLabelling spin id < K + 1 := by
      exact Nat.lt_succ_of_le
        (Nat.le_trans (surface.spinLabelling_le spin id) hspin)
    rw [coeffAt_heatKernelPacket hid]
    exact coeffW_pos hw _
  unfold slabParametricKPhysicalTerm
  exact Q'.mul_pos hface
    (ofNat_pos_of_pos _ (surface.linkProduct_pos hspin))

end ClosedSpinSurface

end YMGap.Continuum.Z4ClosedSpinSurfacePositiveTerm

#print axioms
  YMGap.Continuum.Z4ClosedSpinSurfacePositiveTerm.ClosedSpinSurface.vacuum_linkMultiplicity_le_spin
#print axioms
  YMGap.Continuum.Z4ClosedSpinSurfacePositiveTerm.ClosedSpinSurface.linkProduct_pos
#print axioms
  YMGap.Continuum.Z4ClosedSpinSurfacePositiveTerm.ClosedSpinSurface.physicalTerm_pos
