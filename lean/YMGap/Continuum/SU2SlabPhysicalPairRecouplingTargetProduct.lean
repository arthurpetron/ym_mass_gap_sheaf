/-
# Whole-slab witness realization of a physical-pair target column

The local physical-pair target compiler is mapped over the literal
boundary-complete slab-link list.  A structural fold then turns every target
column of the common whole-slab product matrix into two complete accepted
auxiliary assignments over its fixed physical fields.

Constructive contract: structural dependent products and literal finite-list
membership only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization

namespace YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetProduct

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Small locally realized packages -/

structure SlabPhysicalPairRealizedPackage
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling) where
  linked : {link // link ∈ boundaryCompleteSlabLinks extent}
  package : FiniteBistochasticQKernelPackage
  Target : Type
  decodeTarget : package.Target → Target
  leftAuxiliary : Target → SlabLabelling
  rightAuxiliary : Target → SlabLabelling
  left_mem : ∀ target, leftAuxiliary target ∈
    slabLinkFusionWitnesses K extent leftPhysical linked.1
  right_mem : ∀ target, rightAuxiliary target ∈
    slabLinkFusionWitnesses K extent rightPhysical linked.1

def slabPhysicalPairRealizedPackageAtLink
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
    (linked : {link // link ∈ boundaryCompleteSlabLinks extent}) :
    SlabPhysicalPairRealizedPackage
      K extent leftPhysical rightPhysical :=
  let localData := slabPhysicalPairRecouplingDataAtLink
    extent leftPhysical rightPhysical linked
  let witnessData := slabPhysicalPairRecouplingWitnessDataAtLink
    K extent leftPhysical rightPhysical leftAssignment rightAssignment
    left_mem right_mem linked
  { linked := linked
    package := slabPhysicalPairRecouplingPackageAtLink
      extent leftPhysical rightPhysical linked
    Target :=
      (slabPhysicalPairRecouplingKernelPackage
        (slabIncidentPlaqIds extent linked.1).length localData).Target
    decodeTarget := fun target => target
    leftAuxiliary := fun target =>
      (slabPhysicalPairTargetProductionWitnessPair
        localData witnessData leftBounded rightBounded target).leftAuxiliary
    rightAuxiliary := fun target =>
      (slabPhysicalPairTargetProductionWitnessPair
        localData witnessData leftBounded rightBounded target).rightAuxiliary
    left_mem := fun target =>
      (slabPhysicalPairTargetProductionWitnessPair
        localData witnessData leftBounded rightBounded target).left_mem
    right_mem := fun target =>
      (slabPhysicalPairTargetProductionWitnessPair
        localData witnessData leftBounded rightBounded target).right_mem }

def slabPhysicalPairRealizedPackages
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
    List (SlabPhysicalPairRealizedPackage
      K extent leftPhysical rightPhysical) :=
  (boundaryCompleteSlabLinks extent).attach.map fun linked =>
    slabPhysicalPairRealizedPackageAtLink K extent
      leftPhysical rightPhysical leftAssignment rightAssignment
      left_mem right_mem leftBounded rightBounded linked

def packagesOfPhysicalPairRealized
    {K extent : Nat} {leftPhysical rightPhysical : SlabLabelling} :
    List (SlabPhysicalPairRealizedPackage
      K extent leftPhysical rightPhysical) →
      List FiniteBistochasticQKernelPackage
  | [] => []
  | package :: packages =>
      package.package :: packagesOfPhysicalPairRealized packages

theorem slabPhysicalPairRealized_packages
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
    packagesOfPhysicalPairRealized
        (slabPhysicalPairRealizedPackages K extent
          leftPhysical rightPhysical leftAssignment rightAssignment
          left_mem right_mem leftBounded rightBounded) =
      slabPhysicalPairRecouplingPackages
        extent leftPhysical rightPhysical := by
  unfold slabPhysicalPairRealizedPackages
    slabPhysicalPairRecouplingPackages
  induction (boundaryCompleteSlabLinks extent).attach with
  | nil => rfl
  | cons linked rest ih =>
      simp only [List.map_cons, packagesOfPhysicalPairRealized,
        slabPhysicalPairRealizedPackageAtLink]
      exact congrArg
        (List.cons (slabPhysicalPairRecouplingPackageAtLink
          extent leftPhysical rightPhysical linked)) ih

theorem slabPhysicalPairRealized_links
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
    (slabPhysicalPairRealizedPackages K extent
        leftPhysical rightPhysical leftAssignment rightAssignment
        left_mem right_mem leftBounded rightBounded).map
        (fun package => package.linked.1) =
      boundaryCompleteSlabLinks extent := by
  unfold slabPhysicalPairRealizedPackages
  rw [List.map_map]
  change (boundaryCompleteSlabLinks extent).attach.map Subtype.val = _
  exact List.attach_map_subtype_val _

/-! ## 2. Structural assembly of every local target witness -/

structure SlabPhysicalPairRealizedAssignmentsResult
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (packages : List (SlabPhysicalPairRealizedPackage
      K extent leftPhysical rightPhysical)) where
  leftAssignment : SlabFusionWitnessAssignment
  rightAssignment : SlabFusionWitnessAssignment
  left_mem : leftAssignment ∈
    slabFusionWitnessAssignmentsOn K extent leftPhysical
      (packages.map fun package => package.linked.1)
  right_mem : rightAssignment ∈
    slabFusionWitnessAssignmentsOn K extent rightPhysical
      (packages.map fun package => package.linked.1)

def slabPhysicalPairRealizeTargetAssignments
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling) :
    (packages : List (SlabPhysicalPairRealizedPackage
      K extent leftPhysical rightPhysical)) →
    FiniteBistochasticTargetAssignment
      (packagesOfPhysicalPairRealized packages) →
    SlabPhysicalPairRealizedAssignmentsResult
      K extent leftPhysical rightPhysical packages
  | [], _ => ⟨[], [], List.mem_cons_self, List.mem_cons_self⟩
  | package :: packages, target => by
      let tail := slabPhysicalPairRealizeTargetAssignments
        K extent leftPhysical rightPhysical packages target.2
      exact
        { leftAssignment :=
            (package.linked.1,
              package.leftAuxiliary (package.decodeTarget target.1)) ::
              tail.leftAssignment
          rightAssignment :=
            (package.linked.1,
              package.rightAuxiliary (package.decodeTarget target.1)) ::
              tail.rightAssignment
          left_mem := by
            simp only [List.map_cons, slabFusionWitnessAssignmentsOn]
            apply List.mem_flatMap.mpr
            refine ⟨package.leftAuxiliary (package.decodeTarget target.1),
              package.left_mem (package.decodeTarget target.1), ?_⟩
            exact List.mem_map.mpr
              ⟨tail.leftAssignment, tail.left_mem, rfl⟩
          right_mem := by
            simp only [List.map_cons, slabFusionWitnessAssignmentsOn]
            apply List.mem_flatMap.mpr
            refine ⟨package.rightAuxiliary (package.decodeTarget target.1),
              package.right_mem (package.decodeTarget target.1), ?_⟩
            exact List.mem_map.mpr
              ⟨tail.rightAssignment, tail.right_mem, rfl⟩ }

def transportPhysicalPairTargetAssignment
    {left right : List FiniteBistochasticQKernelPackage}
    (hpackages : left = right)
    (target : FiniteBistochasticTargetAssignment right) :
    FiniteBistochasticTargetAssignment left := by
  rw [hpackages]
  exact target

def slabPhysicalPairTargetAssignmentsResult
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
    SlabPhysicalPairRealizedAssignmentsResult
      K extent leftPhysical rightPhysical
      (slabPhysicalPairRealizedPackages K extent
        leftPhysical rightPhysical leftAssignment rightAssignment
        left_mem right_mem leftBounded rightBounded) :=
  let packages := slabPhysicalPairRealizedPackages K extent
    leftPhysical rightPhysical leftAssignment rightAssignment
    left_mem right_mem leftBounded rightBounded
  let hpackages := slabPhysicalPairRealized_packages K extent
    leftPhysical rightPhysical leftAssignment rightAssignment
    left_mem right_mem leftBounded rightBounded
  slabPhysicalPairRealizeTargetAssignments
    K extent leftPhysical rightPhysical packages
    (transportPhysicalPairTargetAssignment hpackages target)

theorem slabPhysicalPairTargetLeftAssignment_mem
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
    (slabPhysicalPairTargetAssignmentsResult K extent
      leftPhysical rightPhysical leftAssignment rightAssignment
      left_mem right_mem leftBounded rightBounded target).leftAssignment ∈
        slabFusionWitnessAssignmentsOn K extent leftPhysical
          (boundaryCompleteSlabLinks extent) := by
  let result := slabPhysicalPairTargetAssignmentsResult K extent
    leftPhysical rightPhysical leftAssignment rightAssignment
    left_mem right_mem leftBounded rightBounded target
  have hlinks := slabPhysicalPairRealized_links K extent
    leftPhysical rightPhysical leftAssignment rightAssignment
    left_mem right_mem leftBounded rightBounded
  change result.leftAssignment ∈
    slabFusionWitnessAssignmentsOn K extent leftPhysical
      (boundaryCompleteSlabLinks extent)
  rw [← hlinks]
  exact result.left_mem

theorem slabPhysicalPairTargetRightAssignment_mem
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
    (slabPhysicalPairTargetAssignmentsResult K extent
      leftPhysical rightPhysical leftAssignment rightAssignment
      left_mem right_mem leftBounded rightBounded target).rightAssignment ∈
        slabFusionWitnessAssignmentsOn K extent rightPhysical
          (boundaryCompleteSlabLinks extent) := by
  let result := slabPhysicalPairTargetAssignmentsResult K extent
    leftPhysical rightPhysical leftAssignment rightAssignment
    left_mem right_mem leftBounded rightBounded target
  have hlinks := slabPhysicalPairRealized_links K extent
    leftPhysical rightPhysical leftAssignment rightAssignment
    left_mem right_mem leftBounded rightBounded
  change result.rightAssignment ∈
    slabFusionWitnessAssignmentsOn K extent rightPhysical
      (boundaryCompleteSlabLinks extent)
  rw [← hlinks]
  exact result.right_mem

end YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetProduct

#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetProduct.slabPhysicalPairRealized_packages
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetProduct.slabPhysicalPairRealizeTargetAssignments
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetProduct.slabPhysicalPairTargetLeftAssignment_mem
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetProduct.slabPhysicalPairTargetRightAssignment_mem
