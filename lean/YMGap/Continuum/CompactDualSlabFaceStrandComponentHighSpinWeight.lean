/-
# Executable exterior/core classification of rooted strand components

The arbitrary-coupling Casimir payment applies to a component peel only when
the complete selected multiplicity on every touched face leaves the face at
or above a declared finite-core threshold.  Numeric strand slots are not a
global invariant: local trivalent mating shifts slots between unequal legs.
The correct condition is therefore the component-level reserve

    selectedCount(face) = 0
      or selectedCount(face) + threshold <= physical(face).

This module makes that condition executable on the finite corrected-slab
face carrier.  Every rooted component is constructively classified as either
`exterior`, carrying a successful reserve check, or `coreBlocked`, carrying
its failed check.  In the exterior branch, the existing serialized component
drop constructs a `SlabHighSpinFacePeelPath`, hence an accepted lowered BF4
fiber with the arbitrary-coupling Casimir payment.  At the explicit moving
threshold, the exact anchor entropy coefficient pays the whole component.

The `coreBlocked` branch is intentionally retained.  This module does not
claim that every component is exterior, nor does it yet decode a failed check
to a low-spin anchor copy or sum the core-attached exterior decorations.

Constructive contract: finite Boolean scans, `Nat` recursion, and existing
typed component data only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
import YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinWeight

set_option autoImplicit false

open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. A reserve-aware multiplicity-list peel -/

/-- A supported face list whose complete multiplicity leaves `threshold`
copies on every touched face constructs a high-spin peel path.  Each recursive
step consumes one unit of the displayed reserve inequality. -/
def slabHighSpinFacePeelPath_of_count_reserve
    (threshold cutoff extent : Nat) (physical : SlabLabelling) :
    forall faces : List Nat,
      (forall faceId, faceId ∈ faces ->
        faces.count faceId + threshold <= physical faceId) ->
      (forall faceId, faceId ∈ faces ->
        faceId ∈ slabPhysicalFaceEdges extent) ->
      SlabFaceLabellingBounded cutoff extent physical ->
      SlabHighSpinFacePeelPath threshold cutoff extent physical faces
        (lowerSlabFacesByList physical faces)
  | [], _, _, _ => by
      simpa [lowerSlabFacesByList] using
        (SlabHighSpinFacePeelPath.nil
          (threshold := threshold) (cutoff := cutoff)
          (extent := extent) physical)
  | faceId :: rest, hreserve, hsupport, hbounded => by
      have hface : faceId ∈ slabPhysicalFaceEdges extent :=
        hsupport faceId List.mem_cons_self
      have hheadReserve :
          (faceId :: rest).count faceId + threshold <= physical faceId :=
        hreserve faceId List.mem_cons_self
      have hexterior : threshold < physical faceId := by
        rw [List.count_cons, if_pos (beq_iff_eq.mpr rfl)] at hheadReserve
        omega
      have hfaceBounded : physical faceId <= cutoff :=
        hbounded faceId hface
      have htailReserve : forall id, id ∈ rest ->
          rest.count id + threshold <=
            lowerSlabFace physical faceId id := by
        intro id hid
        have hfull := hreserve id (List.mem_cons_of_mem faceId hid)
        by_cases heq : id = faceId
        · subst id
          rw [lowerSlabFace_selected]
          rw [List.count_cons, if_pos (beq_iff_eq.mpr rfl)] at hfull
          omega
        · rw [lowerSlabFace_other physical heq]
          rw [List.count_cons,
            if_neg (fun h => heq (beq_iff_eq.mp h).symm)] at hfull
          exact hfull
      have htailSupport : forall id, id ∈ rest ->
          id ∈ slabPhysicalFaceEdges extent := by
        intro id hid
        exact hsupport id (List.mem_cons_of_mem faceId hid)
      have htailBounded : SlabFaceLabellingBounded cutoff extent
          (lowerSlabFace physical faceId) := by
        intro id hid
        by_cases heq : id = faceId
        · subst id
          rw [lowerSlabFace_selected]
          exact Nat.le_trans (Nat.sub_le _ _) hfaceBounded
        · rw [lowerSlabFace_other physical heq]
          exact hbounded id hid
      have tailPath := slabHighSpinFacePeelPath_of_count_reserve
        threshold cutoff extent (lowerSlabFace physical faceId) rest
        htailReserve htailSupport htailBounded
      have path := SlabHighSpinFacePeelPath.cons
        faceId hface hexterior hfaceBounded tailPath
      rw [lowerSlabFacesByList_cons]
      exact path

/-! ## 2. Finite executable reserve check for one rooted component -/

/-- Semantic reserve condition for a rooted component.  Untouched faces are
allowed at any label; every touched face must retain the declared core. -/
def SlabFusionWitnessFaceStrandSeed.HighSpinReserve
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat) : Prop :=
  forall faceId,
    slabFaceStrandSelectionCount seed.selected faceId = 0 ∨
      slabFaceStrandSelectionCount seed.selected faceId + threshold <=
        physical faceId

/-- Executable finite scan of the component reserve condition. -/
def SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat) : Bool :=
  (slabPhysicalFaceEdges extent).all fun faceId =>
    decide
      (slabFaceStrandSelectionCount seed.selected faceId = 0 ∨
        slabFaceStrandSelectionCount seed.selected faceId + threshold <=
          physical faceId)

/-- The finite scan is sound because component selection counts vanish
outside the displayed physical face carrier. -/
theorem SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck_sound
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat)
    (hcheck :
      SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck seed threshold =
        true) :
    SlabFusionWitnessFaceStrandSeed.HighSpinReserve seed threshold := by
  intro faceId
  by_cases hface : faceId ∈ slabPhysicalFaceEdges extent
  · unfold SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck at hcheck
    exact of_decide_eq_true
      (List.all_eq_true.mp hcheck faceId hface)
  · exact Or.inl
      (SlabFusionWitnessFaceStrandSeed.selectionCount_eq_zero_of_not_physical
        seed faceId hface)

/-- The finite scan is complete for the semantic reserve condition. -/
theorem SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck_complete
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat)
    (hreserve :
      SlabFusionWitnessFaceStrandSeed.HighSpinReserve seed threshold) :
    SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck seed threshold =
      true := by
  unfold SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck
  apply List.all_eq_true.mpr
  intro faceId _
  apply decide_eq_true
  exact hreserve faceId

theorem SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck_eq_true_iff
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat) :
    SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck seed threshold =
        true ↔
      SlabFusionWitnessFaceStrandSeed.HighSpinReserve seed threshold :=
  ⟨SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck_sound seed threshold,
    SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck_complete seed
      threshold⟩

/-! ## 3. Every rooted component has an executable exterior/core class -/

/-- The exact two-way component classification at a finite-core threshold.
The blocked branch is data, not a discarded negation. -/
inductive SlabComponentHighSpinClass
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat) : Type
  | exterior
      (reserve_paid :
        SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck seed threshold =
          true)
  | coreBlocked
      (reserve_failed :
        SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck seed threshold =
          false)

/-- Finite evaluation classifies every component without excluded middle on
an infinite carrier. -/
def SlabFusionWitnessFaceStrandSeed.highSpinClass
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat) :
    SlabComponentHighSpinClass seed threshold :=
  match hcheck :
      SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck seed threshold with
  | true => .exterior hcheck
  | false => .coreBlocked hcheck

/-! ## 4. Construct the accepted exterior component peel -/

/-- A successful component reserve scan constructs the actual high-spin peel
path ending at the already accepted component target. -/
def SlabFusionWitnessFaceStrandSeed.highSpinPeelPath
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat)
    (hcheck :
      SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck seed threshold =
        true)
    (hbounded : SlabFaceLabellingBounded K extent physical) :
    SlabHighSpinFacePeelPath threshold K extent physical
      (SlabFusionWitnessFaceStrandSeed.peelFaces seed)
      (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) := by
  have hsemantic :=
    SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck_sound
      seed threshold hcheck
  have hreserve : forall faceId,
      faceId ∈ SlabFusionWitnessFaceStrandSeed.peelFaces seed ->
      (SlabFusionWitnessFaceStrandSeed.peelFaces seed).count faceId +
          threshold <= physical faceId := by
    intro faceId hmem
    have hcountNe :
        (SlabFusionWitnessFaceStrandSeed.peelFaces seed).count faceId ≠ 0 := by
      intro hzero
      exact (List.count_eq_zero.mp hzero) hmem
    have hcountPos :
        0 < (SlabFusionWitnessFaceStrandSeed.peelFaces seed).count faceId := by
      omega
    have hcount := SlabFusionWitnessFaceStrandSeed.peelFaces_count seed faceId
    rcases hsemantic faceId with hzero | hpaid
    · rw [hcount] at hcountPos
      exact False.elim (Nat.not_lt_zero _ (hzero ▸ hcountPos))
    · rwa [hcount]
  have path := slabHighSpinFacePeelPath_of_count_reserve
    threshold K extent physical
    (SlabFusionWitnessFaceStrandSeed.peelFaces seed)
    hreserve
    (fun faceId hmem => mem_slabFaceDropList hmem)
    hbounded
  rw [SlabFusionWitnessFaceStrandSeed.lowerSlabFacesByList_peelFaces seed]
    at path
  exact path

/-- Arbitrary-coupling accepted component payment in the exterior branch. -/
theorem SlabFusionWitnessFaceStrandSeed.expandedFiberWeight_highSpin_le_of_rate
    {w rate : YMGap.Constructive.Q'}
    (hw0 : (0 : YMGap.Constructive.Q') ≤ w)
    (hw1 : w ≤ (1 : YMGap.Constructive.Q'))
    (hrate : (0 : YMGap.Constructive.Q') ≤ rate)
    (cutoff half threshold : Nat) {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff (centralExtent half) physical
        (boundaryCompleteSlabLinks (centralExtent half))}
    (seed : SlabFusionWitnessFaceStrandSeed
      cutoff (centralExtent half) physical
        (boundaryCompleteSlabLinks (centralExtent half))
        assignment hassignment)
    (hcheck :
      SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck seed threshold =
        true)
    (hbounded : SlabFaceLabellingBounded
      cutoff (centralExtent half) physical)
    (hpay : exteriorFaceCoefficient w threshold ≤ rate) :
    let D : SlabPhysicalData :=
      { coupling := w
        coupling_nonnegative := hw0
        cutoff := cutoff
        half := half }
    retainedFineIntertwinerPhysicalFiberWeight D physical assignment <=
      rate ^ (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length *
        retainedFineIntertwinerPhysicalFiberWeight D
          (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed)
          (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed) := by
  exact retainedFineIntertwinerPhysicalFiberWeight_exterior_peelPath_le_of_rate
    hw0 hw1 hrate cutoff half threshold assignment
    (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed)
    (SlabFusionWitnessFaceStrandSeed.highSpinPeelPath
      seed threshold hcheck hbounded) hpay

/-- At the executable moving threshold, every exterior-classified accepted
component pays the exact anchor entropy coefficient at arbitrary fixed
`0 < w < 1`. -/
theorem SlabFusionWitnessFaceStrandSeed.expandedFiberWeight_anchorPaidExterior_le
    {w : YMGap.Constructive.Q'}
    (hw0 : (0 : YMGap.Constructive.Q') < w)
    (hw1 : w < (1 : YMGap.Constructive.Q'))
    (cutoff half : Nat) {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff (centralExtent half) physical
        (boundaryCompleteSlabLinks (centralExtent half))}
    (seed : SlabFusionWitnessFaceStrandSeed
      cutoff (centralExtent half) physical
        (boundaryCompleteSlabLinks (centralExtent half))
        assignment hassignment)
    (hcheck :
      SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck seed
        (anchorPaidExteriorThreshold w) = true)
    (hbounded : SlabFaceLabellingBounded
      cutoff (centralExtent half) physical) :
    let D : SlabPhysicalData :=
      { coupling := w
        coupling_nonnegative := YMGap.Constructive.Q'.le_of_lt hw0
        cutoff := cutoff
        half := half }
    retainedFineIntertwinerPhysicalFiberWeight D physical assignment <=
      anchorFaceCoefficient ^
          (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length *
        retainedFineIntertwinerPhysicalFiberWeight D
          (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed)
          (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed) := by
  exact retainedFineIntertwinerPhysicalFiberWeight_exterior_anchorPaid_le
    hw0 hw1 cutoff half assignment
    (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed)
    (SlabFusionWitnessFaceStrandSeed.highSpinPeelPath seed
      (anchorPaidExteriorThreshold w) hcheck hbounded)

#print axioms slabHighSpinFacePeelPath_of_count_reserve
#print axioms SlabFusionWitnessFaceStrandSeed.HighSpinReserve
#print axioms SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck
#print axioms SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck_sound
#print axioms SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck_complete
#print axioms SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck_eq_true_iff
#print axioms SlabComponentHighSpinClass
#print axioms SlabFusionWitnessFaceStrandSeed.highSpinClass
#print axioms SlabFusionWitnessFaceStrandSeed.highSpinPeelPath
#print axioms SlabFusionWitnessFaceStrandSeed.expandedFiberWeight_highSpin_le_of_rate
#print axioms SlabFusionWitnessFaceStrandSeed.expandedFiberWeight_anchorPaidExterior_le

end YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinWeight
