/-
# Split every component drop into a paid exterior and finite core remainder

A core-blocked strand component is connected and therefore cannot be split
into independently mate-closed subcomponents.  Its *physical multiplicity
profile*, however, admits an exact arithmetic split at any threshold `S`.
For source label `p` and component drop `d <= p`, define

```text
exterior = min d (p - S),
core     = d - exterior.
```

The exterior decrement leaves the current label at least `S`, so its
canonical serialized word constructs a `SlabHighSpinFacePeelPath`.  The core
remainder is at most `S` on every physical face, and exterior followed by core
is exactly the complete component decrement.

The retained fine-intertwiner fiber has unit counting weight, so the exterior
path comparison allows an arbitrary target witness.  Consequently this split
produces the same anchor-rate Casimir payment at every fixed `0 < w < 1`, even
for a component whose complete removal is blocked at the core.

This module isolates the one-component exterior/core split and its global
`faces * S` residual-word bound.  It does not yet sum these residuals over the
canonical component family or construct an accepted intermediate assignment
over the partially lowered physical field.

Constructive contract: exact `Nat` subtraction/minimum arithmetic, finite
drop serialization, and the existing high-spin path compiler only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinWeight

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreSplitWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Exact pointwise exterior/core arithmetic -/

/-- The largest part of a declared drop which leaves `threshold` copies on
the source face. -/
def exteriorDropCount
    (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat) (faceId : Nat) : Nat :=
  min (drop faceId) (physical faceId - threshold)

/-- The finite-core part of the drop after removing the paid exterior. -/
def coreResidualDropCount
    (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat) (faceId : Nat) : Nat :=
  drop faceId - exteriorDropCount physical threshold drop faceId

theorem exteriorDropCount_le_drop
    (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat) (faceId : Nat) :
    exteriorDropCount physical threshold drop faceId <= drop faceId :=
  Nat.min_le_left _ _

theorem exteriorDropCount_le_available
    (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat) (faceId : Nat) :
    exteriorDropCount physical threshold drop faceId <=
      physical faceId - threshold :=
  Nat.min_le_right _ _

/-- The two pieces reconstruct the original declared drop exactly. -/
theorem exteriorDropCount_add_coreResidualDropCount
    (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat) (faceId : Nat) :
    exteriorDropCount physical threshold drop faceId +
        coreResidualDropCount physical threshold drop faceId =
      drop faceId := by
  unfold coreResidualDropCount
  exact Nat.add_sub_of_le
    (exteriorDropCount_le_drop physical threshold drop faceId)

/-- A positive exterior decrement really leaves the threshold below the
source label. -/
theorem exteriorDropCount_add_threshold_le
    (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat) (faceId : Nat)
    (hpositive : 0 < exteriorDropCount physical threshold drop faceId) :
    exteriorDropCount physical threshold drop faceId + threshold <=
      physical faceId := by
  have havailable :=
    exteriorDropCount_le_available physical threshold drop faceId
  by_cases hthreshold : threshold <= physical faceId
  · omega
  · have hzero : physical faceId - threshold = 0 := by omega
    rw [hzero] at havailable
    omega

/-- If the complete drop fits in the source label, its unpaid remainder is
bounded by the core threshold. -/
theorem coreResidualDropCount_le_threshold
    (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat) (faceId : Nat)
    (hdrop : drop faceId <= physical faceId) :
    coreResidualDropCount physical threshold drop faceId <= threshold := by
  unfold coreResidualDropCount exteriorDropCount
  by_cases hthreshold : threshold <= physical faceId
  · by_cases hsmall : drop faceId <= physical faceId - threshold
    · rw [Nat.min_eq_left hsmall]
      omega
    · have hlarge : physical faceId - threshold <= drop faceId := by
        omega
      rw [Nat.min_eq_right hlarge]
      omega
  · have hzero : physical faceId - threshold = 0 := by omega
    rw [hzero]
    rw [Nat.min_eq_right (Nat.zero_le _)]
    simp only [Nat.sub_zero]
    omega

/-! ## 2. Serialize the paid and residual profiles -/

/-- The canonical grouped word of exterior decrements. -/
def highSpinExteriorDropFaces
    (extent : Nat) (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat) : List Nat :=
  slabFaceDropList extent
    (exteriorDropCount physical threshold drop)

/-- The canonical grouped word of finite-core residual decrements. -/
def highSpinCoreResidualFaces
    (extent : Nat) (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat) : List Nat :=
  slabFaceDropList extent
    (coreResidualDropCount physical threshold drop)

/-- The physical field after paying and removing only the high-spin exterior
part of a drop profile. -/
def highSpinCorePhysical
    (extent : Nat) (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat) : SlabLabelling :=
  lowerSlabFacesByList physical
    (highSpinExteriorDropFaces extent physical threshold drop)

/-- The paid exterior word constructs an actual threshold-respecting path. -/
def slabHighSpinCoreSplitPath
    (threshold cutoff extent : Nat) (physical : SlabLabelling)
    (drop : Nat -> Nat)
    (hbounded : SlabFaceLabellingBounded cutoff extent physical) :
    SlabHighSpinFacePeelPath threshold cutoff extent physical
      (highSpinExteriorDropFaces extent physical threshold drop)
      (highSpinCorePhysical extent physical threshold drop) := by
  unfold highSpinExteriorDropFaces highSpinCorePhysical
  apply slabHighSpinFacePeelPath_of_count_reserve
  · intro faceId hmem
    have hface := mem_slabFaceDropList hmem
    rw [slabFaceDropList_count_of_mem extent
      (exteriorDropCount physical threshold drop) hface]
    apply exteriorDropCount_add_threshold_le
    have hcountNe :
        (slabFaceDropList extent
          (exteriorDropCount physical threshold drop)).count faceId ≠ 0 := by
      intro hzero
      exact (List.count_eq_zero.mp hzero) hmem
    rw [slabFaceDropList_count_of_mem extent
      (exteriorDropCount physical threshold drop) hface] at hcountNe
    omega
  · intro faceId hmem
    exact mem_slabFaceDropList hmem
  · exact hbounded

private theorem length_flatMap_le
    {A B : Type} (block : A -> List B) (bound : Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items -> (block item).length <= bound) ->
      (items.flatMap block).length <= items.length * bound
  | [], _ => by simp
  | head :: tail, hbound => by
      have hhead := hbound head List.mem_cons_self
      have htail := length_flatMap_le block bound tail
        (fun item hitem => hbound item (List.mem_cons_of_mem head hitem))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [Nat.succ_mul]
      omega

/-- The complete residual word has at most `threshold` entries per displayed
physical face. -/
theorem highSpinCoreResidualFaces_length_le
    (extent : Nat) (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat)
    (hdrop : ∀ faceId, faceId ∈ slabPhysicalFaceEdges extent ->
      drop faceId <= physical faceId) :
    (highSpinCoreResidualFaces extent physical threshold drop).length <=
      (slabPhysicalFaceEdges extent).length * threshold := by
  unfold highSpinCoreResidualFaces slabFaceDropList
  apply length_flatMap_le
  intro faceId hface
  rw [List.length_replicate]
  exact coreResidualDropCount_le_threshold
    physical threshold drop faceId (hdrop faceId hface)

/-- Exterior removal followed by the residual core removal is exactly the
complete original drop on every coordinate. -/
theorem lower_exterior_then_core_eq_full
    (extent : Nat) (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat)
    (hdrop : ∀ faceId, faceId ∈ slabPhysicalFaceEdges extent ->
      drop faceId <= physical faceId) :
    lowerSlabFacesByList
        (highSpinCorePhysical extent physical threshold drop)
        (highSpinCoreResidualFaces extent physical threshold drop) =
      lowerSlabFacesByList physical (slabFaceDropList extent drop) := by
  funext faceId
  unfold highSpinCorePhysical highSpinExteriorDropFaces
    highSpinCoreResidualFaces lowerSlabFacesByList
  by_cases hface : faceId ∈ slabPhysicalFaceEdges extent
  · rw [slabFaceDropList_count_of_mem extent
        (exteriorDropCount physical threshold drop) hface,
      slabFaceDropList_count_of_mem extent
        (coreResidualDropCount physical threshold drop) hface,
      slabFaceDropList_count_of_mem extent drop hface]
    have hsplit := exteriorDropCount_add_coreResidualDropCount
      physical threshold drop faceId
    have hcapacity := hdrop faceId hface
    omega
  · rw [slabFaceDropList_count_of_not_mem extent
        (exteriorDropCount physical threshold drop) hface,
      slabFaceDropList_count_of_not_mem extent
        (coreResidualDropCount physical threshold drop) hface,
      slabFaceDropList_count_of_not_mem extent drop hface]
    omega

/-! ## 3. Specialize the split to an actual rooted strand component -/

def SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat) : List Nat :=
  highSpinExteriorDropFaces extent physical threshold
    (slabFaceStrandSelectionCount seed.selected)

def SlabFusionWitnessFaceStrandSeed.coreResidualFaces
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat) : List Nat :=
  highSpinCoreResidualFaces extent physical threshold
    (slabFaceStrandSelectionCount seed.selected)

def SlabFusionWitnessFaceStrandSeed.corePhysical
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat) : SlabLabelling :=
  highSpinCorePhysical extent physical threshold
    (slabFaceStrandSelectionCount seed.selected)

/-- Every component, whether exterior or blocked, has a canonical paid
high-spin path down to its finite-core remainder. -/
def SlabFusionWitnessFaceStrandSeed.highSpinCoreSplitPath
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat)
    (hbounded : SlabFaceLabellingBounded K extent physical) :
    SlabHighSpinFacePeelPath threshold K extent physical
      (SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces seed threshold)
      (SlabFusionWitnessFaceStrandSeed.corePhysical seed threshold) :=
  slabHighSpinCoreSplitPath threshold K extent physical
    (slabFaceStrandSelectionCount seed.selected) hbounded

/-- The residual component word is uniformly finite at fixed threshold. -/
theorem SlabFusionWitnessFaceStrandSeed.coreResidualFaces_length_le
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat) :
    (SlabFusionWitnessFaceStrandSeed.coreResidualFaces seed threshold).length <=
      (slabPhysicalFaceEdges extent).length * threshold := by
  exact highSpinCoreResidualFaces_length_le extent physical threshold
    (slabFaceStrandSelectionCount seed.selected)
    (fun faceId _ => slabFaceStrandSelectionCount_le seed.selected faceId)

/-- Removing the paid exterior and then the finite core remainder reaches the
same physical target as complete accepted component removal. -/
theorem SlabFusionWitnessFaceStrandSeed.lower_corePhysical_residual_eq_lowerPhysical
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat) :
    lowerSlabFacesByList
        (SlabFusionWitnessFaceStrandSeed.corePhysical seed threshold)
        (SlabFusionWitnessFaceStrandSeed.coreResidualFaces seed threshold) =
      SlabFusionWitnessFaceStrandSeed.lowerPhysical seed := by
  change lowerSlabFacesByList
      (highSpinCorePhysical extent physical threshold
        (slabFaceStrandSelectionCount seed.selected))
      (highSpinCoreResidualFaces extent physical threshold
        (slabFaceStrandSelectionCount seed.selected)) =
    SlabFusionWitnessFaceStrandSeed.lowerPhysical seed
  calc
    lowerSlabFacesByList
        (highSpinCorePhysical extent physical threshold
          (slabFaceStrandSelectionCount seed.selected))
        (highSpinCoreResidualFaces extent physical threshold
          (slabFaceStrandSelectionCount seed.selected)) =
      lowerSlabFacesByList physical
        (slabFaceDropList extent
          (slabFaceStrandSelectionCount seed.selected)) :=
        lower_exterior_then_core_eq_full extent physical threshold
          (slabFaceStrandSelectionCount seed.selected)
          (fun faceId _ =>
            slabFaceStrandSelectionCount_le seed.selected faceId)
    _ = SlabFusionWitnessFaceStrandSeed.lowerPhysical seed :=
      SlabFusionWitnessFaceStrandSeed.lowerSlabFacesByList_peelFaces seed

/-! ## 4. Arbitrary-coupling payment down to the core remainder -/

/-- At the executable moving threshold, the paid exterior of every rooted
component receives the anchor entropy rate, including core-blocked
components.  The target witness is arbitrary because retained fibers have
unit counting weight. -/
theorem SlabFusionWitnessFaceStrandSeed.expandedFiberWeight_coreSplit_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff (centralExtent half) physical
        (boundaryCompleteSlabLinks (centralExtent half))}
    (seed : SlabFusionWitnessFaceStrandSeed
      cutoff (centralExtent half) physical
        (boundaryCompleteSlabLinks (centralExtent half))
        assignment hassignment)
    (targetWitness : SlabFusionWitnessAssignment)
    (hbounded : SlabFaceLabellingBounded
      cutoff (centralExtent half) physical) :
    let D : SlabPhysicalData :=
      { coupling := w
        coupling_nonnegative := Q'.le_of_lt hw0
        cutoff := cutoff
        half := half }
    retainedFineIntertwinerPhysicalFiberWeight D physical assignment <=
      anchorFaceCoefficient ^
          (SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces seed
            (anchorPaidExteriorThreshold w)).length *
        retainedFineIntertwinerPhysicalFiberWeight D
          (SlabFusionWitnessFaceStrandSeed.corePhysical seed
            (anchorPaidExteriorThreshold w))
          targetWitness := by
  exact retainedFineIntertwinerPhysicalFiberWeight_exterior_anchorPaid_le
    hw0 hw1 cutoff half assignment targetWitness
    (SlabFusionWitnessFaceStrandSeed.highSpinCoreSplitPath
      seed (anchorPaidExteriorThreshold w) hbounded)

#print axioms exteriorDropCount
#print axioms coreResidualDropCount
#print axioms exteriorDropCount_add_coreResidualDropCount
#print axioms exteriorDropCount_add_threshold_le
#print axioms coreResidualDropCount_le_threshold
#print axioms highSpinExteriorDropFaces
#print axioms highSpinCoreResidualFaces
#print axioms highSpinCorePhysical
#print axioms slabHighSpinCoreSplitPath
#print axioms highSpinCoreResidualFaces_length_le
#print axioms lower_exterior_then_core_eq_full
#print axioms SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces
#print axioms SlabFusionWitnessFaceStrandSeed.coreResidualFaces
#print axioms SlabFusionWitnessFaceStrandSeed.corePhysical
#print axioms SlabFusionWitnessFaceStrandSeed.highSpinCoreSplitPath
#print axioms SlabFusionWitnessFaceStrandSeed.coreResidualFaces_length_le
#print axioms SlabFusionWitnessFaceStrandSeed.lower_corePhysical_residual_eq_lowerPhysical
#print axioms SlabFusionWitnessFaceStrandSeed.expandedFiberWeight_coreSplit_le

end YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreSplitWeight
