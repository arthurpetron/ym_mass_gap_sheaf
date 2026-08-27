/-
# Canonical whole-slab realization of a physical-pair target column

The common physical-pair product matrix is fixed before any accepted
auxiliary assignment is chosen.  This module realizes one of its target
columns by recursing directly over that physical-only package list.  Accepted
auxiliary assignments enter only as local membership anchors.

Local anchor independence therefore lifts by the same recursion to the whole
slab.  Local target faithfulness likewise lifts to an injective global target
realization, without transporting a target through an anchor-indexed package
structure.

Constructive contract: structural dependent products and literal finite-list
membership only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetProduct
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetAnchorIndependence

namespace YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetAnchorIndependence
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetInjectivity
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Direct realization over the common physical package list -/

structure SlabPhysicalPairCanonicalAssignmentsResult
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks extent}) where
  leftAssignment : SlabFusionWitnessAssignment
  rightAssignment : SlabFusionWitnessAssignment
  left_mem : leftAssignment ∈
    slabFusionWitnessAssignmentsOn K extent leftPhysical
      (linkedList.map Subtype.val)
  right_mem : rightAssignment ∈
    slabFusionWitnessAssignmentsOn K extent rightPhysical
      (linkedList.map Subtype.val)

def slabPhysicalPairCanonicalTargetAssignmentsFrom
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (left_mem : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent))
    (leftBounded : SlabFaceLabellingBounded K extent leftPhysical)
    (rightBounded : SlabFaceLabellingBounded K extent rightPhysical) :
    (linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks extent}) →
    FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink
          extent leftPhysical rightPhysical linked) →
    SlabPhysicalPairCanonicalAssignmentsResult
      K extent leftPhysical rightPhysical linkedList
  | [], _ => ⟨[], [], List.mem_cons_self, List.mem_cons_self⟩
  | linked :: rest, target => by
      let localData := slabPhysicalPairRecouplingDataAtLink
        extent leftPhysical rightPhysical linked
      let anchor := slabPhysicalPairRecouplingWitnessDataAtLink
        K extent leftPhysical rightPhysical leftAssignment rightAssignment
        left_mem right_mem linked
      let localResult := slabPhysicalPairTargetProductionWitnessPair
        localData anchor leftBounded rightBounded target.1
      let tail := slabPhysicalPairCanonicalTargetAssignmentsFrom
        K extent leftPhysical rightPhysical leftAssignment rightAssignment
        left_mem right_mem leftBounded rightBounded rest target.2
      exact
        { leftAssignment := (linked.1, localResult.leftAuxiliary) ::
            tail.leftAssignment
          rightAssignment := (linked.1, localResult.rightAuxiliary) ::
            tail.rightAssignment
          left_mem := by
            simp only [List.map_cons, slabFusionWitnessAssignmentsOn]
            apply List.mem_flatMap.mpr
            refine ⟨localResult.leftAuxiliary, localResult.left_mem, ?_⟩
            exact List.mem_map.mpr
              ⟨tail.leftAssignment, tail.left_mem, rfl⟩
          right_mem := by
            simp only [List.map_cons, slabFusionWitnessAssignmentsOn]
            apply List.mem_flatMap.mpr
            refine ⟨localResult.rightAuxiliary, localResult.right_mem, ?_⟩
            exact List.mem_map.mpr
              ⟨tail.rightAssignment, tail.right_mem, rfl⟩ }

/-! ## 2. The global realization is independent of its accepted anchor -/

theorem slabPhysicalPairCanonicalTargetAssignmentsFrom_anchor_independent
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment₁ rightAssignment₁
      leftAssignment₂ rightAssignment₂ : SlabFusionWitnessAssignment)
    (left_mem₁ : leftAssignment₁ ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem₁ : rightAssignment₁ ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent))
    (left_mem₂ : leftAssignment₂ ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem₂ : rightAssignment₂ ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent))
    (leftBounded : SlabFaceLabellingBounded K extent leftPhysical)
    (rightBounded : SlabFaceLabellingBounded K extent rightPhysical) :
    ∀ (linkedList :
        List {link // link ∈ boundaryCompleteSlabLinks extent})
      (target : FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink
            extent leftPhysical rightPhysical linked)),
      let first := slabPhysicalPairCanonicalTargetAssignmentsFrom
        K extent leftPhysical rightPhysical
        leftAssignment₁ rightAssignment₁ left_mem₁ right_mem₁
        leftBounded rightBounded linkedList target
      let second := slabPhysicalPairCanonicalTargetAssignmentsFrom
        K extent leftPhysical rightPhysical
        leftAssignment₂ rightAssignment₂ left_mem₂ right_mem₂
        leftBounded rightBounded linkedList target
      first.leftAssignment = second.leftAssignment ∧
        first.rightAssignment = second.rightAssignment
  | [], _ => ⟨rfl, rfl⟩
  | linked :: rest, target => by
      let localData := slabPhysicalPairRecouplingDataAtLink
        extent leftPhysical rightPhysical linked
      let firstAnchor := slabPhysicalPairRecouplingWitnessDataAtLink
        K extent leftPhysical rightPhysical
        leftAssignment₁ rightAssignment₁ left_mem₁ right_mem₁ linked
      let secondAnchor := slabPhysicalPairRecouplingWitnessDataAtLink
        K extent leftPhysical rightPhysical
        leftAssignment₂ rightAssignment₂ left_mem₂ right_mem₂ linked
      have hlocal :=
        slabPhysicalPairTargetProductionWitnessPair_anchor_independent
          localData firstAnchor secondAnchor leftBounded rightBounded target.1
      have htail :=
        slabPhysicalPairCanonicalTargetAssignmentsFrom_anchor_independent
          K extent leftPhysical rightPhysical
          leftAssignment₁ rightAssignment₁
          leftAssignment₂ rightAssignment₂
          left_mem₁ right_mem₁ left_mem₂ right_mem₂
          leftBounded rightBounded rest target.2
      change
        (linked.1,
            (slabPhysicalPairTargetProductionWitnessPair
              localData firstAnchor leftBounded rightBounded target.1).leftAuxiliary) ::
              (slabPhysicalPairCanonicalTargetAssignmentsFrom
                K extent leftPhysical rightPhysical
                leftAssignment₁ rightAssignment₁ left_mem₁ right_mem₁
                leftBounded rightBounded rest target.2).leftAssignment =
          (linked.1,
            (slabPhysicalPairTargetProductionWitnessPair
              localData secondAnchor leftBounded rightBounded target.1).leftAuxiliary) ::
              (slabPhysicalPairCanonicalTargetAssignmentsFrom
                K extent leftPhysical rightPhysical
                leftAssignment₂ rightAssignment₂ left_mem₂ right_mem₂
                leftBounded rightBounded rest target.2).leftAssignment ∧
        (linked.1,
            (slabPhysicalPairTargetProductionWitnessPair
              localData firstAnchor leftBounded rightBounded target.1).rightAuxiliary) ::
              (slabPhysicalPairCanonicalTargetAssignmentsFrom
                K extent leftPhysical rightPhysical
                leftAssignment₁ rightAssignment₁ left_mem₁ right_mem₁
                leftBounded rightBounded rest target.2).rightAssignment =
          (linked.1,
            (slabPhysicalPairTargetProductionWitnessPair
              localData secondAnchor leftBounded rightBounded target.1).rightAuxiliary) ::
              (slabPhysicalPairCanonicalTargetAssignmentsFrom
                K extent leftPhysical rightPhysical
                leftAssignment₂ rightAssignment₂ left_mem₂ right_mem₂
                leftBounded rightBounded rest target.2).rightAssignment
      constructor
      · rw [hlocal.1, htail.1]
      · rw [hlocal.2, htail.2]

/-! ## 3. The two realized assignments retain the common target column -/

theorem slabPhysicalPairCanonicalTargetAssignmentsFrom_injective
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (left_mem : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent))
    (leftBounded : SlabFaceLabellingBounded K extent leftPhysical)
    (rightBounded : SlabFaceLabellingBounded K extent rightPhysical) :
    ∀ (linkedList :
        List {link // link ∈ boundaryCompleteSlabLinks extent})
      {first second : FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink
            extent leftPhysical rightPhysical linked)},
      (slabPhysicalPairCanonicalTargetAssignmentsFrom
        K extent leftPhysical rightPhysical leftAssignment rightAssignment
        left_mem right_mem leftBounded rightBounded
        linkedList first).leftAssignment =
      (slabPhysicalPairCanonicalTargetAssignmentsFrom
        K extent leftPhysical rightPhysical leftAssignment rightAssignment
        left_mem right_mem leftBounded rightBounded
        linkedList second).leftAssignment →
      (slabPhysicalPairCanonicalTargetAssignmentsFrom
        K extent leftPhysical rightPhysical leftAssignment rightAssignment
        left_mem right_mem leftBounded rightBounded
        linkedList first).rightAssignment =
      (slabPhysicalPairCanonicalTargetAssignmentsFrom
        K extent leftPhysical rightPhysical leftAssignment rightAssignment
        left_mem right_mem leftBounded rightBounded
        linkedList second).rightAssignment →
      first = second
  | [], first, second, _, _ => by
      cases first
      cases second
      rfl
  | linked :: rest, first, second, hleft, hright => by
      let localData := slabPhysicalPairRecouplingDataAtLink
        extent leftPhysical rightPhysical linked
      let anchor := slabPhysicalPairRecouplingWitnessDataAtLink
        K extent leftPhysical rightPhysical leftAssignment rightAssignment
        left_mem right_mem linked
      change
        (linked.1,
            (slabPhysicalPairTargetProductionWitnessPair
              localData anchor leftBounded rightBounded first.1).leftAuxiliary) ::
              (slabPhysicalPairCanonicalTargetAssignmentsFrom
                K extent leftPhysical rightPhysical
                leftAssignment rightAssignment left_mem right_mem
                leftBounded rightBounded rest first.2).leftAssignment =
          (linked.1,
            (slabPhysicalPairTargetProductionWitnessPair
              localData anchor leftBounded rightBounded second.1).leftAuxiliary) ::
              (slabPhysicalPairCanonicalTargetAssignmentsFrom
                K extent leftPhysical rightPhysical
                leftAssignment rightAssignment left_mem right_mem
                leftBounded rightBounded rest second.2).leftAssignment
        at hleft
      change
        (linked.1,
            (slabPhysicalPairTargetProductionWitnessPair
              localData anchor leftBounded rightBounded first.1).rightAuxiliary) ::
              (slabPhysicalPairCanonicalTargetAssignmentsFrom
                K extent leftPhysical rightPhysical
                leftAssignment rightAssignment left_mem right_mem
                leftBounded rightBounded rest first.2).rightAssignment =
          (linked.1,
            (slabPhysicalPairTargetProductionWitnessPair
              localData anchor leftBounded rightBounded second.1).rightAuxiliary) ::
              (slabPhysicalPairCanonicalTargetAssignmentsFrom
                K extent leftPhysical rightPhysical
                leftAssignment rightAssignment left_mem right_mem
                leftBounded rightBounded rest second.2).rightAssignment
        at hright
      apply Prod.ext
      · apply slabPhysicalPairTargetProductionWitnessPair_injective
          localData anchor leftBounded rightBounded
        · exact congrArg Prod.snd (List.cons.inj hleft).1
        · exact congrArg Prod.snd (List.cons.inj hright).1
      · exact slabPhysicalPairCanonicalTargetAssignmentsFrom_injective
          K extent leftPhysical rightPhysical leftAssignment rightAssignment
          left_mem right_mem leftBounded rightBounded rest
          (List.cons.inj hleft).2 (List.cons.inj hright).2

/-! ## 4. The canonical full-slab compiler -/

def slabPhysicalPairCanonicalTargetAssignmentsResult
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (left_mem : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent))
    (leftBounded : SlabFaceLabellingBounded K extent leftPhysical)
    (rightBounded : SlabFaceLabellingBounded K extent rightPhysical)
    (target : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical rightPhysical) :
    SlabPhysicalPairCanonicalAssignmentsResult
      K extent leftPhysical rightPhysical
      (boundaryCompleteSlabLinks extent).attach :=
  slabPhysicalPairCanonicalTargetAssignmentsFrom
    K extent leftPhysical rightPhysical leftAssignment rightAssignment
    left_mem right_mem leftBounded rightBounded
    (boundaryCompleteSlabLinks extent).attach target

theorem slabPhysicalPairCanonicalTargetAssignmentsResult_anchor_independent
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment₁ rightAssignment₁
      leftAssignment₂ rightAssignment₂ : SlabFusionWitnessAssignment)
    (left_mem₁ : leftAssignment₁ ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem₁ : rightAssignment₁ ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent))
    (left_mem₂ : leftAssignment₂ ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem₂ : rightAssignment₂ ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent))
    (leftBounded : SlabFaceLabellingBounded K extent leftPhysical)
    (rightBounded : SlabFaceLabellingBounded K extent rightPhysical)
    (target : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical rightPhysical) :
    let first := slabPhysicalPairCanonicalTargetAssignmentsResult
      K extent leftPhysical rightPhysical
      leftAssignment₁ rightAssignment₁ left_mem₁ right_mem₁
      leftBounded rightBounded target
    let second := slabPhysicalPairCanonicalTargetAssignmentsResult
      K extent leftPhysical rightPhysical
      leftAssignment₂ rightAssignment₂ left_mem₂ right_mem₂
      leftBounded rightBounded target
    first.leftAssignment = second.leftAssignment ∧
      first.rightAssignment = second.rightAssignment :=
  slabPhysicalPairCanonicalTargetAssignmentsFrom_anchor_independent
    K extent leftPhysical rightPhysical
    leftAssignment₁ rightAssignment₁ leftAssignment₂ rightAssignment₂
    left_mem₁ right_mem₁ left_mem₂ right_mem₂
    leftBounded rightBounded (boundaryCompleteSlabLinks extent).attach target

theorem slabPhysicalPairCanonicalTargetAssignmentsResult_injective
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (left_mem : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent))
    (leftBounded : SlabFaceLabellingBounded K extent leftPhysical)
    (rightBounded : SlabFaceLabellingBounded K extent rightPhysical)
    {first second : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical rightPhysical}
    (hleft :
      (slabPhysicalPairCanonicalTargetAssignmentsResult K extent
        leftPhysical rightPhysical leftAssignment rightAssignment
        left_mem right_mem leftBounded rightBounded first).leftAssignment =
      (slabPhysicalPairCanonicalTargetAssignmentsResult K extent
        leftPhysical rightPhysical leftAssignment rightAssignment
        left_mem right_mem leftBounded rightBounded second).leftAssignment)
    (hright :
      (slabPhysicalPairCanonicalTargetAssignmentsResult K extent
        leftPhysical rightPhysical leftAssignment rightAssignment
        left_mem right_mem leftBounded rightBounded first).rightAssignment =
      (slabPhysicalPairCanonicalTargetAssignmentsResult K extent
        leftPhysical rightPhysical leftAssignment rightAssignment
        left_mem right_mem leftBounded rightBounded second).rightAssignment) :
    first = second :=
  slabPhysicalPairCanonicalTargetAssignmentsFrom_injective
    K extent leftPhysical rightPhysical leftAssignment rightAssignment
    left_mem right_mem leftBounded rightBounded
    (boundaryCompleteSlabLinks extent).attach hleft hright

theorem slabPhysicalPairCanonicalTargetLeftAssignment_mem
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (left_mem : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent))
    (leftBounded : SlabFaceLabellingBounded K extent leftPhysical)
    (rightBounded : SlabFaceLabellingBounded K extent rightPhysical)
    (target : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical rightPhysical) :
    (slabPhysicalPairCanonicalTargetAssignmentsResult K extent
      leftPhysical rightPhysical leftAssignment rightAssignment
      left_mem right_mem leftBounded rightBounded target).leftAssignment ∈
        slabFusionWitnessAssignmentsOn K extent leftPhysical
          (boundaryCompleteSlabLinks extent) := by
  simpa only [List.attach_map_subtype_val] using
    (slabPhysicalPairCanonicalTargetAssignmentsResult K extent
      leftPhysical rightPhysical leftAssignment rightAssignment
      left_mem right_mem leftBounded rightBounded target).left_mem

theorem slabPhysicalPairCanonicalTargetRightAssignment_mem
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (left_mem : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent))
    (leftBounded : SlabFaceLabellingBounded K extent leftPhysical)
    (rightBounded : SlabFaceLabellingBounded K extent rightPhysical)
    (target : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical rightPhysical) :
    (slabPhysicalPairCanonicalTargetAssignmentsResult K extent
      leftPhysical rightPhysical leftAssignment rightAssignment
      left_mem right_mem leftBounded rightBounded target).rightAssignment ∈
        slabFusionWitnessAssignmentsOn K extent rightPhysical
          (boundaryCompleteSlabLinks extent) := by
  simpa only [List.attach_map_subtype_val] using
    (slabPhysicalPairCanonicalTargetAssignmentsResult K extent
      leftPhysical rightPhysical leftAssignment rightAssignment
      left_mem right_mem leftBounded rightBounded target).right_mem

/-! ## 5. Transport and packaged anchored target points -/

def transportSlabPhysicalPairRecouplingTargetAssignment
    {extent : Nat}
    {leftPhysical₁ rightPhysical₁
      leftPhysical₂ rightPhysical₂ : SlabLabelling}
    (hleft : leftPhysical₁ = leftPhysical₂)
    (hright : rightPhysical₁ = rightPhysical₂)
    (target : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical₁ rightPhysical₁) :
    SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical₂ rightPhysical₂ := by
  subst leftPhysical₂
  subst rightPhysical₂
  exact target

theorem transportSlabPhysicalPairRecouplingTargetAssignment_rfl
    {extent : Nat} {leftPhysical rightPhysical : SlabLabelling}
    (target : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical rightPhysical) :
    transportSlabPhysicalPairRecouplingTargetAssignment
      (Eq.refl leftPhysical) (Eq.refl rightPhysical) target = target := rfl

/-- Equality of the two realized assignment pairs identifies target columns
even when the two accepted anchors were initially indexed by propositionally
equal physical fields. -/
theorem slabPhysicalPairCanonicalTargetAssignmentsResult_injective_across_physical_eq
    (K extent : Nat)
    {leftPhysical₁ rightPhysical₁
      leftPhysical₂ rightPhysical₂ : SlabLabelling}
    (hleftPhysical : leftPhysical₁ = leftPhysical₂)
    (hrightPhysical : rightPhysical₁ = rightPhysical₂)
    (leftAssignment₁ rightAssignment₁
      leftAssignment₂ rightAssignment₂ : SlabFusionWitnessAssignment)
    (left_mem₁ : leftAssignment₁ ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical₁
        (boundaryCompleteSlabLinks extent))
    (right_mem₁ : rightAssignment₁ ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical₁
        (boundaryCompleteSlabLinks extent))
    (left_mem₂ : leftAssignment₂ ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical₂
        (boundaryCompleteSlabLinks extent))
    (right_mem₂ : rightAssignment₂ ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical₂
        (boundaryCompleteSlabLinks extent))
    (leftBounded₁ : SlabFaceLabellingBounded K extent leftPhysical₁)
    (rightBounded₁ : SlabFaceLabellingBounded K extent rightPhysical₁)
    (leftBounded₂ : SlabFaceLabellingBounded K extent leftPhysical₂)
    (rightBounded₂ : SlabFaceLabellingBounded K extent rightPhysical₂)
    (firstTarget : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical₁ rightPhysical₁)
    (secondTarget : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical₂ rightPhysical₂)
    (hleftAssignment :
      (slabPhysicalPairCanonicalTargetAssignmentsResult K extent
        leftPhysical₁ rightPhysical₁
        leftAssignment₁ rightAssignment₁ left_mem₁ right_mem₁
        leftBounded₁ rightBounded₁ firstTarget).leftAssignment =
      (slabPhysicalPairCanonicalTargetAssignmentsResult K extent
        leftPhysical₂ rightPhysical₂
        leftAssignment₂ rightAssignment₂ left_mem₂ right_mem₂
        leftBounded₂ rightBounded₂ secondTarget).leftAssignment)
    (hrightAssignment :
      (slabPhysicalPairCanonicalTargetAssignmentsResult K extent
        leftPhysical₁ rightPhysical₁
        leftAssignment₁ rightAssignment₁ left_mem₁ right_mem₁
        leftBounded₁ rightBounded₁ firstTarget).rightAssignment =
      (slabPhysicalPairCanonicalTargetAssignmentsResult K extent
        leftPhysical₂ rightPhysical₂
        leftAssignment₂ rightAssignment₂ left_mem₂ right_mem₂
        leftBounded₂ rightBounded₂ secondTarget).rightAssignment) :
    transportSlabPhysicalPairRecouplingTargetAssignment
        hleftPhysical hrightPhysical firstTarget = secondTarget := by
  cases hleftPhysical
  cases hrightPhysical
  rw [transportSlabPhysicalPairRecouplingTargetAssignment_rfl]
  have hanchor :=
    slabPhysicalPairCanonicalTargetAssignmentsResult_anchor_independent
      K extent leftPhysical₁ rightPhysical₁
      leftAssignment₁ rightAssignment₁
      leftAssignment₂ rightAssignment₂
      left_mem₁ right_mem₁ left_mem₂ right_mem₂
      leftBounded₁ rightBounded₁ secondTarget
  apply slabPhysicalPairCanonicalTargetAssignmentsResult_injective
    K extent leftPhysical₁ rightPhysical₁
    leftAssignment₁ rightAssignment₁ left_mem₁ right_mem₁
    leftBounded₁ rightBounded₁
  · exact hleftAssignment.trans hanchor.1.symm
  · exact hrightAssignment.trans hanchor.2.symm

/-- Accepted source data over one fixed physical pair, separated from the
target column subsequently realized above it. -/
structure SlabPhysicalPairCanonicalAnchor
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling) where
  leftAssignment : SlabFusionWitnessAssignment
  rightAssignment : SlabFusionWitnessAssignment
  left_mem : leftAssignment ∈
    slabFusionWitnessAssignmentsOn K extent leftPhysical
      (boundaryCompleteSlabLinks extent)
  right_mem : rightAssignment ∈
    slabFusionWitnessAssignmentsOn K extent rightPhysical
      (boundaryCompleteSlabLinks extent)
  leftBounded : SlabFaceLabellingBounded K extent leftPhysical
  rightBounded : SlabFaceLabellingBounded K extent rightPhysical

def SlabPhysicalPairCanonicalAnchor.realize
    {K extent : Nat} {leftPhysical rightPhysical : SlabLabelling}
    (anchor : SlabPhysicalPairCanonicalAnchor
      K extent leftPhysical rightPhysical)
    (target : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical rightPhysical) :=
  slabPhysicalPairCanonicalTargetAssignmentsResult K extent
    leftPhysical rightPhysical
    anchor.leftAssignment anchor.rightAssignment
    anchor.left_mem anchor.right_mem anchor.leftBounded anchor.rightBounded target

theorem SlabPhysicalPairCanonicalAnchor.realize_left_mem
    {K extent : Nat} {leftPhysical rightPhysical : SlabLabelling}
    (anchor : SlabPhysicalPairCanonicalAnchor
      K extent leftPhysical rightPhysical)
    (target : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical rightPhysical) :
    (anchor.realize target).leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent) :=
  slabPhysicalPairCanonicalTargetLeftAssignment_mem K extent
    leftPhysical rightPhysical
    anchor.leftAssignment anchor.rightAssignment
    anchor.left_mem anchor.right_mem anchor.leftBounded anchor.rightBounded target

theorem SlabPhysicalPairCanonicalAnchor.realize_right_mem
    {K extent : Nat} {leftPhysical rightPhysical : SlabLabelling}
    (anchor : SlabPhysicalPairCanonicalAnchor
      K extent leftPhysical rightPhysical)
    (target : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical rightPhysical) :
    (anchor.realize target).rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent) :=
  slabPhysicalPairCanonicalTargetRightAssignment_mem K extent
    leftPhysical rightPhysical
    anchor.leftAssignment anchor.rightAssignment
    anchor.left_mem anchor.right_mem anchor.leftBounded anchor.rightBounded target

theorem SlabPhysicalPairCanonicalAnchor.target_eq_of_realizations_eq
    {K extent : Nat}
    {leftPhysical₁ rightPhysical₁
      leftPhysical₂ rightPhysical₂ : SlabLabelling}
    (first : SlabPhysicalPairCanonicalAnchor
      K extent leftPhysical₁ rightPhysical₁)
    (second : SlabPhysicalPairCanonicalAnchor
      K extent leftPhysical₂ rightPhysical₂)
    (hleftPhysical : leftPhysical₁ = leftPhysical₂)
    (hrightPhysical : rightPhysical₁ = rightPhysical₂)
    (firstTarget : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical₁ rightPhysical₁)
    (secondTarget : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical₂ rightPhysical₂)
    (hleftAssignment : (first.realize firstTarget).leftAssignment =
      (second.realize secondTarget).leftAssignment)
    (hrightAssignment : (first.realize firstTarget).rightAssignment =
      (second.realize secondTarget).rightAssignment) :
    transportSlabPhysicalPairRecouplingTargetAssignment
        hleftPhysical hrightPhysical firstTarget = secondTarget :=
  slabPhysicalPairCanonicalTargetAssignmentsResult_injective_across_physical_eq
    K extent hleftPhysical hrightPhysical
    first.leftAssignment first.rightAssignment
    second.leftAssignment second.rightAssignment
    first.left_mem first.right_mem second.left_mem second.right_mem
    first.leftBounded first.rightBounded
    second.leftBounded second.rightBounded
    firstTarget secondTarget hleftAssignment hrightAssignment

end YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct

#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct.slabPhysicalPairCanonicalTargetAssignmentsFrom
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct.slabPhysicalPairCanonicalTargetAssignmentsFrom_anchor_independent
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct.slabPhysicalPairCanonicalTargetAssignmentsFrom_injective
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct.slabPhysicalPairCanonicalTargetAssignmentsResult
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct.slabPhysicalPairCanonicalTargetAssignmentsResult_anchor_independent
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct.slabPhysicalPairCanonicalTargetAssignmentsResult_injective
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct.slabPhysicalPairCanonicalTargetLeftAssignment_mem
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct.slabPhysicalPairCanonicalTargetRightAssignment_mem
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct.transportSlabPhysicalPairRecouplingTargetAssignment
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct.slabPhysicalPairCanonicalTargetAssignmentsResult_injective_across_physical_eq
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct.SlabPhysicalPairCanonicalAnchor.realize_left_mem
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct.SlabPhysicalPairCanonicalAnchor.realize_right_mem
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct.SlabPhysicalPairCanonicalAnchor.target_eq_of_realizations_eq
