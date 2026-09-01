/-
# Positive terms from two independently labelled closed surfaces

Two disjoint closed corrected-slab supports may carry independent admitted
twice-spin labels.  At every link, the second support either contributes no
face or replaces a pair of vacuum labels by one equal-spin pair while leaving
the first support unchanged.  Applying the explicit singlet injection twice
therefore preserves a positive local fusion channel and makes the combined
physical term strictly positive.

This is a finite-slab positivity compiler.  It supplies no cutoff-uniform
probability floor, continuum limit, or Clay mass-gap statement.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.Z4ClosedSpinSurfacePositiveTerm

namespace YMGap.Continuum.Z4DisjointClosedSpinSurfacesPositiveTerm

set_option maxRecDepth 250000
set_option maxHeartbeats 6000000
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
open YMGap.Continuum.Z4ClosedSpinSurfacePositiveTerm
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

/-! ## 1. Disjoint surface pair and its two-spin labelling -/

structure DisjointClosedSpinSurfaces (extent : Nat) : Type where
  first : ClosedSpinSurface extent
  second : ClosedSpinSurface extent
  supports_disjoint : ∀ id, id ∈ first.faceIds →
    id ∈ second.faceIds → False

namespace DisjointClosedSpinSurfaces

def spinLabelling {extent : Nat}
    (surfaces : DisjointClosedSpinSurfaces extent)
    (firstSpin secondSpin : Nat) : EdgeLabelling := fun id =>
  if id ∈ surfaces.first.faceIds then firstSpin
  else if id ∈ surfaces.second.faceIds then secondSpin
  else 0

theorem spinLabelling_eq_firstSpin
    {extent firstSpin secondSpin id : Nat}
    (surfaces : DisjointClosedSpinSurfaces extent)
    (hid : id ∈ surfaces.first.faceIds) :
    surfaces.spinLabelling firstSpin secondSpin id = firstSpin := by
  simp [spinLabelling, hid]

theorem spinLabelling_eq_secondSpin
    {extent firstSpin secondSpin id : Nat}
    (surfaces : DisjointClosedSpinSurfaces extent)
    (hid : id ∈ surfaces.second.faceIds) :
    surfaces.spinLabelling firstSpin secondSpin id = secondSpin := by
  have hnotFirst : id ∉ surfaces.first.faceIds := by
    intro hfirst
    exact surfaces.supports_disjoint id hfirst hid
  simp [spinLabelling, hnotFirst, hid]

theorem spinLabelling_eq_first_off_second
    {extent firstSpin secondSpin id : Nat}
    (surfaces : DisjointClosedSpinSurfaces extent)
    (hid : id ∉ surfaces.second.faceIds) :
    surfaces.spinLabelling firstSpin secondSpin id =
      surfaces.first.spinLabelling firstSpin id := by
  unfold spinLabelling ClosedSpinSurface.spinLabelling
  by_cases hfirst : id ∈ surfaces.first.faceIds <;> simp [hfirst, hid]

theorem spinLabelling_le
    {extent : Nat} (surfaces : DisjointClosedSpinSurfaces extent)
    (firstSpin secondSpin bound coordinate : Nat)
    (hfirstSpin : firstSpin ≤ bound)
    (hsecondSpin : secondSpin ≤ bound) :
    surfaces.spinLabelling firstSpin secondSpin coordinate ≤ bound := by
  unfold spinLabelling
  by_cases hfirst : coordinate ∈ surfaces.first.faceIds
  · simp [hfirst, hfirstSpin]
  · by_cases hsecond : coordinate ∈ surfaces.second.faceIds
    · simp [hfirst, hsecond, hsecondSpin]
    · simp [hfirst, hsecond]

/-- The two-spin surface labelling is a literal member of the finite physical
state space whenever both spins are admitted by the cutoff. -/
theorem spinLabelling_mem_bounded
    {extent K firstSpin secondSpin : Nat}
    (surfaces : DisjointClosedSpinSurfaces extent)
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    surfaces.spinLabelling firstSpin secondSpin ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges extent) := by
  apply boundedEdgeLabellings_complete
  · intro id _
    exact Nat.lt_succ_of_le
      (surfaces.spinLabelling_le firstSpin secondSpin K id
        hfirstSpin hsecondSpin)
  · intro id hphysical
    have hnotFirst : id ∉ surfaces.first.faceIds := by
      intro hfirst
      exact hphysical (surfaces.first.faceIds_subset_physical id hfirst)
    have hnotSecond : id ∉ surfaces.second.faceIds := by
      intro hsecond
      exact hphysical (surfaces.second.faceIds_subset_physical id hsecond)
    simp [spinLabelling, hnotFirst, hnotSecond]

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

theorem selectedSecond_map_first_eq_zero
    {extent : Nat} (surfaces : DisjointClosedSpinSurfaces extent)
    (firstSpin : Nat) (link : Z4Link) :
    (surfaces.second.selectedIncidentIds link).map
        (surfaces.first.spinLabelling firstSpin) =
      List.replicate
        (surfaces.second.selectedIncidentIds link).length 0 := by
  apply map_eq_replicate_of_constant
  intro id hid
  apply surfaces.first.spinLabelling_eq_zero_off
  intro hfirst
  have hsecond : id ∈ surfaces.second.faceIds :=
    of_decide_eq_true (List.mem_filter.mp hid).2
  exact surfaces.supports_disjoint id hfirst hsecond

theorem selectedSecond_map_pair_eq_replicate
    {extent : Nat} (surfaces : DisjointClosedSpinSurfaces extent)
    (firstSpin secondSpin : Nat) (link : Z4Link) :
    (surfaces.second.selectedIncidentIds link).map
        (surfaces.spinLabelling firstSpin secondSpin) =
      List.replicate
        (surfaces.second.selectedIncidentIds link).length secondSpin := by
  apply map_eq_replicate_of_constant
  intro id hid
  apply surfaces.spinLabelling_eq_secondSpin
  exact of_decide_eq_true (List.mem_filter.mp hid).2

theorem unselectedSecond_map_pair_eq_first
    {extent : Nat} (surfaces : DisjointClosedSpinSurfaces extent)
    (firstSpin secondSpin : Nat) (link : Z4Link) :
    (surfaces.second.unselectedIncidentIds link).map
        (surfaces.spinLabelling firstSpin secondSpin) =
      (surfaces.second.unselectedIncidentIds link).map
        (surfaces.first.spinLabelling firstSpin) := by
  apply List.map_congr_left
  intro id hid
  apply surfaces.spinLabelling_eq_first_off_second
  have hfalse : decide (id ∈ surfaces.second.faceIds) = false := by
    simpa using (List.mem_filter.mp hid).2
  exact of_decide_eq_false hfalse

/-! ## 2. The second singlet injection at every link -/

private theorem firstPhysical_bounded
    {extent K firstSpin : Nat}
    (surfaces : DisjointClosedSpinSurfaces extent)
    (hfirstSpin : firstSpin ≤ K) :
    SlabFaceLabellingBounded K extent
      (surfaces.first.spinLabelling firstSpin) := by
  intro id _
  exact Nat.le_trans
    (surfaces.first.spinLabelling_le firstSpin id) hfirstSpin

private theorem pairPhysical_bounded
    {extent K firstSpin secondSpin : Nat}
    (surfaces : DisjointClosedSpinSurfaces extent)
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    SlabFaceLabellingBounded K extent
      (surfaces.spinLabelling firstSpin secondSpin) := by
  intro id _
  exact surfaces.spinLabelling_le firstSpin secondSpin K id
    hfirstSpin hsecondSpin

theorem first_linkMultiplicity_le_pair
    {extent K firstSpin secondSpin : Nat}
    (surfaces : DisjointClosedSpinSurfaces extent)
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K)
    (link : Z4Link) (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    slabExplicitLinkMultiplicity K extent
        (surfaces.first.spinLabelling firstSpin) link ≤
      slabExplicitLinkMultiplicity K extent
        (surfaces.spinLabelling firstSpin secondSpin) link := by
  let oldSpins := (slabIncidentPlaqIds extent link).map
    (surfaces.first.spinLabelling firstSpin)
  let newSpins := (slabIncidentPlaqIds extent link).map
    (surfaces.spinLabelling firstSpin secondSpin)
  let rest := (surfaces.second.unselectedIncidentIds link).map
    (surfaces.first.spinLabelling firstSpin)
  have holdBounded : SpinsBounded K oldSpins := by
    exact slabIncidentSpins_bounded
      (firstPhysical_bounded surfaces hfirstSpin) link
  have hnewBounded : SpinsBounded K newSpins := by
    exact slabIncidentSpins_bounded
      (pairPhysical_bounded surfaces hfirstSpin hsecondSpin) link
  have hlength : oldSpins.length ≤ 6 := by
    unfold oldSpins
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six extent link
  have holdPerm :
      oldSpins.Perm
        (List.replicate
            (surfaces.second.selectedIncidentIds link).length 0 ++ rest) := by
    have hperm := (surfaces.second.incident_partition_perm link).symm.map
      (surfaces.first.spinLabelling firstSpin)
    rw [List.map_append,
      surfaces.selectedSecond_map_first_eq_zero] at hperm
    exact hperm
  have hnewPerm :
      newSpins.Perm
        (List.replicate
            (surfaces.second.selectedIncidentIds link).length secondSpin ++
          rest) := by
    have hperm := (surfaces.second.incident_partition_perm link).symm.map
      (surfaces.spinLabelling firstSpin secondSpin)
    rw [List.map_append,
      surfaces.selectedSecond_map_pair_eq_replicate,
      surfaces.unselectedSecond_map_pair_eq_first] at hperm
    exact hperm
  rcases surfaces.second.selectedIncidentIds_length_zero_or_two
      link hlink with hzero | htwo
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

theorem vacuum_linkMultiplicity_le_pair
    {extent K firstSpin secondSpin : Nat}
    (surfaces : DisjointClosedSpinSurfaces extent)
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K)
    (link : Z4Link) (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    slabExplicitLinkMultiplicity K extent zeroEdgeLabelling link ≤
      slabExplicitLinkMultiplicity K extent
        (surfaces.spinLabelling firstSpin secondSpin) link := by
  exact Nat.le_trans
    (surfaces.first.vacuum_linkMultiplicity_le_spin
      hfirstSpin link hlink)
    (surfaces.first_linkMultiplicity_le_pair
      hfirstSpin hsecondSpin link hlink)

theorem linkMultiplicity_pos
    {extent K firstSpin secondSpin : Nat}
    (surfaces : DisjointClosedSpinSurfaces extent)
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K)
    (link : Z4Link) (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    0 < slabExplicitLinkMultiplicity K extent
      (surfaces.spinLabelling firstSpin secondSpin) link := by
  have hle := surfaces.vacuum_linkMultiplicity_le_pair
    hfirstSpin hsecondSpin link hlink
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
    {extent K firstSpin secondSpin : Nat}
    (surfaces : DisjointClosedSpinSurfaces extent)
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    0 < slabExplicitLinkMultiplicityProduct K extent
      (surfaces.spinLabelling firstSpin secondSpin) := by
  unfold slabExplicitLinkMultiplicityProduct
  exact natListProduct_pos_of_pointwise
    (slabExplicitLinkMultiplicity K extent
      (surfaces.spinLabelling firstSpin secondSpin))
    (boundaryCompleteSlabLinks extent)
    (fun link hlink => surfaces.linkMultiplicity_pos
      hfirstSpin hsecondSpin link hlink)

/-! ## 3. Strict two-spin physical-term positivity -/

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

theorem physicalTerm_pos
    {extent : Nat} (surfaces : DisjointClosedSpinSurfaces extent)
    {w : Q'} (hw : (0 : Q') < w)
    {K firstSpin secondSpin : Nat}
    (hfirstSpin : firstSpin ≤ K) (hsecondSpin : secondSpin ≤ K) :
    (0 : Q') < slabParametricKPhysicalTerm w K extent
      (surfaces.spinLabelling firstSpin secondSpin) := by
  have hface :
      (0 : Q') < slabParametricKPhysicalFaceFactor w K extent
        (surfaces.spinLabelling firstSpin secondSpin) := by
    unfold slabParametricKPhysicalFaceFactor
    apply eliminateLinks_pos
    intro id
    have hid : surfaces.spinLabelling firstSpin secondSpin id < K + 1 := by
      exact Nat.lt_succ_of_le
        (surfaces.spinLabelling_le firstSpin secondSpin K id
          hfirstSpin hsecondSpin)
    rw [coeffAt_heatKernelPacket hid]
    exact coeffW_pos hw _
  unfold slabParametricKPhysicalTerm
  exact Q'.mul_pos hface
    (ofNat_pos_of_pos _
      (surfaces.linkProduct_pos hfirstSpin hsecondSpin))

end DisjointClosedSpinSurfaces

end YMGap.Continuum.Z4DisjointClosedSpinSurfacesPositiveTerm

#print axioms
  YMGap.Continuum.Z4DisjointClosedSpinSurfacesPositiveTerm.DisjointClosedSpinSurfaces.first_linkMultiplicity_le_pair
#print axioms
  YMGap.Continuum.Z4DisjointClosedSpinSurfacesPositiveTerm.DisjointClosedSpinSurfaces.spinLabelling_mem_bounded
#print axioms
  YMGap.Continuum.Z4DisjointClosedSpinSurfacesPositiveTerm.DisjointClosedSpinSurfaces.linkProduct_pos
#print axioms
  YMGap.Continuum.Z4DisjointClosedSpinSurfacesPositiveTerm.DisjointClosedSpinSurfaces.physicalTerm_pos
