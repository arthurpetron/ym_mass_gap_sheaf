/-
# Source-spin-free link bound for the central BF4 spin cube

For an arbitrary boundary channel and target half-state, every corrected-slab
link meets the six source-cube faces in zero or two positions.  In the zero
case the actual incident list is just the residual list.  In the two case it
is a permutation of `spin, spin` followed by that same residual list.

Combining the generic residual-list theorem with the equal-pair theorem gives
one linkwise bound, and hence one complete link-product bound, containing no
source spin.  This is the local-to-global fusion step required before the
remaining non-source heat activities can be summed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4CentralLowerCubeRowDomination
import YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
import YMGap.Continuum.Z4ResidualListMultiplicityBound

namespace YMGap.Continuum.BF4CentralSpinCubeResidualLinkBound

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option autoImplicit false

open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CentralLowerCubeRowDomination
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4EqualPairResidualValenceBound
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
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
open YMGap.Continuum.Z4ResidualListMultiplicityBound
open YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Arbitrary-spin source labelling and incidence permutation -/

def centralSpinCubeSourcePhysical
    (spin : Nat) (boundary target : EdgeLabelling) : EdgeLabelling :=
  assembleReflectedSlabLabelling 0
    (centralLowerSpinCubeState spin) boundary target

theorem centralSpinCubeSourcePhysical_eq_spin_on_cube
    (spin : Nat) (boundary target : EdgeLabelling)
    {id : Nat} (hid : id ∈ centralLowerCubeFaceIds) :
    centralSpinCubeSourcePhysical spin boundary target id = spin := by
  unfold centralSpinCubeSourcePhysical
  have hlower := mem_centralLowerFaceIds.mp
    (centralLowerCubeFaceIds_subset_lower id hid)
  rw [assembleReflectedSlabLabelling_lower hlower.1 hlower.2]
  exact centralLowerSpinCubeState_eq_spin_on_cube spin hid

theorem centralSpinCubeSourcePhysical_eq_vacuum_off_cube
    (spin : Nat) (boundary target : EdgeLabelling)
    {id : Nat} (hid : id ∉ centralLowerCubeFaceIds) :
    centralSpinCubeSourcePhysical spin boundary target id =
      centralVacuumSourcePhysical boundary target id := by
  unfold centralSpinCubeSourcePhysical centralVacuumSourcePhysical
    assembleReflectedSlabLabelling
  have hsource : centralLowerSpinCubeState spin id =
      zeroEdgeLabelling id := by
    unfold zeroEdgeLabelling
    exact centralLowerSpinCubeState_eq_zero_off_cube spin hid
  by_cases hphysical : id ∈ slabPhysicalFaceEdges (centralExtent 0)
  · simp only [hphysical, if_pos]
    cases hside : plaquetteHalfSide 0
        (slabPlaquetteAt (centralExtent 0) id)
    · exact hsource
    · rfl
    · rfl
  · simp [hphysical]

private theorem map_eq_replicate_of_constant
    {A B : Type} (value : A -> B) (constant : B) :
    forall items : List A,
      (forall item, item ∈ items -> value item = constant) ->
        items.map value = List.replicate items.length constant
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [List.map_cons, List.length_cons, List.replicate_succ]
      rw [hagree head List.mem_cons_self,
        map_eq_replicate_of_constant value constant tail
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem head hitem))]

theorem selected_map_spinSource_eq_replicate
    (spin : Nat) (boundary target : EdgeLabelling) (link : Z4Link) :
    (centralLowerCubeSelectedIncidentIds link).map
        (centralSpinCubeSourcePhysical spin boundary target) =
      List.replicate
        (centralLowerCubeSelectedIncidentIds link).length spin := by
  apply map_eq_replicate_of_constant
  intro id hid
  apply centralSpinCubeSourcePhysical_eq_spin_on_cube
  exact of_decide_eq_true (List.mem_filter.mp hid).2

theorem unselected_map_spinSource_eq_vacuum
    (spin : Nat) (boundary target : EdgeLabelling) (link : Z4Link) :
    (centralLowerCubeUnselectedIncidentIds link).map
        (centralSpinCubeSourcePhysical spin boundary target) =
      (centralLowerCubeUnselectedIncidentIds link).map
        (centralVacuumSourcePhysical boundary target) := by
  apply List.map_congr_left
  intro id hid
  apply centralSpinCubeSourcePhysical_eq_vacuum_off_cube
  have hfalse : decide (id ∈ centralLowerCubeFaceIds) = false := by
    simpa using (List.mem_filter.mp hid).2
  exact of_decide_eq_false hfalse

/-- The actual arbitrary-spin source list is a permutation of the selected
equal source labels followed by the source-free residual list. -/
theorem spinSource_incident_spins_perm_selected_residual
    (spin : Nat) (boundary target : EdgeLabelling) (link : Z4Link) :
    ((slabIncidentPlaqIds 1 link).map
        (centralSpinCubeSourcePhysical spin boundary target)).Perm
      (List.replicate
          (centralLowerCubeSelectedIncidentIds link).length spin ++
        (centralLowerCubeUnselectedIncidentIds link).map
          (centralVacuumSourcePhysical boundary target)) := by
  have hperm :=
    (centralLowerCube_incident_partition_perm link).symm.map
      (centralSpinCubeSourcePhysical spin boundary target)
  rw [List.map_append, selected_map_spinSource_eq_replicate,
    unselected_map_spinSource_eq_vacuum] at hperm
  exact hperm

/-! ## 2. Linkwise and product residual bounds -/

def centralSpinCubeResidualIncidentSpins
    (boundary target : EdgeLabelling) (link : Z4Link) : List Nat :=
  (centralLowerCubeUnselectedIncidentIds link).map
    (centralVacuumSourcePhysical boundary target)

def centralSpinCubeResidualLinkBound
    (boundary target : EdgeLabelling) (link : Z4Link) : Nat :=
  spinSumCube
    (natListSum (centralSpinCubeResidualIncidentSpins boundary target link))

/-- Every actual cube-source link multiplicity is bounded by a quantity
depending only on the boundary/target residual labels. -/
theorem centralSpinCube_linkMultiplicity_le_residual
    {K spin : Nat} (hspin : spin <= K)
    (boundary target : EdgeLabelling)
    (hboundary : boundary ∈ centralBoundaryChannels K 0)
    (htarget : target ∈ centralHalfStates K 0)
    (link : Z4Link) (hlink : link ∈ boundaryCompleteSlabLinks 1) :
    slabExplicitLinkMultiplicity K 1
        (centralSpinCubeSourcePhysical spin boundary target) link <=
      centralSpinCubeResidualLinkBound boundary target link := by
  let actual := (slabIncidentPlaqIds 1 link).map
    (centralSpinCubeSourcePhysical spin boundary target)
  let residual := centralSpinCubeResidualIncidentSpins boundary target link
  have hsource : centralLowerSpinCubeState spin ∈ centralHalfStates K 0 :=
    centralLowerSpinCubeState_mem_centralHalfStates hspin
  have hphysical : SlabFaceLabellingBounded K 1
      (centralSpinCubeSourcePhysical spin boundary target) := by
    unfold centralSpinCubeSourcePhysical
    exact assembleReflectedSlabLabelling_bounded
      hsource hboundary htarget
  have hbounded : SpinsBounded K actual :=
    slabIncidentSpins_bounded hphysical link
  have hlength : actual.length <= 6 := by
    unfold actual
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six 1 link
  have hperm := spinSource_incident_spins_perm_selected_residual
    spin boundary target link
  change actual.Perm
    (List.replicate
      (centralLowerCubeSelectedIncidentIds link).length spin ++ residual)
    at hperm
  rcases centralLowerCube_selected_length_zero_or_two link hlink
      with hzero | htwo
  · rw [hzero] at hperm
    simp only [List.replicate_zero, List.nil_append] at hperm
    unfold slabExplicitLinkMultiplicity centralSpinCubeResidualLinkBound
    exact explicitValenceMultiplicity_physical_perm_le_spinSumCube
      hperm hlength hbounded
  · rw [htwo] at hperm
    simp only [List.replicate_succ, List.replicate_zero,
      List.cons_append, List.nil_append] at hperm
    unfold slabExplicitLinkMultiplicity centralSpinCubeResidualLinkBound
    exact
      explicitValenceMultiplicity_physical_equalPair_le_residualSpinSumCube
        hperm hlength hbounded

def centralSpinCubeResidualMultiplicityProduct
    (boundary target : EdgeLabelling) : Nat :=
  natListProduct
    (centralSpinCubeResidualLinkBound boundary target)
    (boundaryCompleteSlabLinks 1)

private theorem natListProduct_mono_on
    {A : Type} (left right : A -> Nat) :
    forall items : List A,
      (forall item, item ∈ items -> left item <= right item) ->
        natListProduct left items <= natListProduct right items
  | [], _ => Nat.le_refl 1
  | head :: tail, hle => by
      simp only [natListProduct]
      exact Nat.mul_le_mul
        (hle head List.mem_cons_self)
        (natListProduct_mono_on left right tail
          (fun item hitem =>
            hle item (List.mem_cons_of_mem head hitem)))

/-- The complete production link product has a source-spin-free residual
majorant. -/
theorem centralSpinCube_linkProduct_le_residual
    {K spin : Nat} (hspin : spin <= K)
    (boundary target : EdgeLabelling)
    (hboundary : boundary ∈ centralBoundaryChannels K 0)
    (htarget : target ∈ centralHalfStates K 0) :
    slabExplicitLinkMultiplicityProduct K 1
        (centralSpinCubeSourcePhysical spin boundary target) <=
      centralSpinCubeResidualMultiplicityProduct boundary target := by
  unfold slabExplicitLinkMultiplicityProduct
    centralSpinCubeResidualMultiplicityProduct
  exact natListProduct_mono_on _ _ (boundaryCompleteSlabLinks 1)
    (fun link hlink => centralSpinCube_linkMultiplicity_le_residual
      hspin boundary target hboundary htarget link hlink)

end YMGap.Continuum.BF4CentralSpinCubeResidualLinkBound

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4CentralSpinCubeResidualLinkBound.spinSource_incident_spins_perm_selected_residual
#print axioms YMGap.Continuum.BF4CentralSpinCubeResidualLinkBound.centralSpinCube_linkMultiplicity_le_residual
#print axioms YMGap.Continuum.BF4CentralSpinCubeResidualLinkBound.centralSpinCube_linkProduct_le_residual
