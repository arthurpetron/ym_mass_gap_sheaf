/-
# Whole-slab recoupling matrix above one fixed physical pair

The local physical-pair compiler is mapped over the literal
boundary-complete slab-link list.  The resulting dependent product matrix is
determined only by the two physical labellings.  Two accepted global
auxiliary assignments merely select one row in this common matrix.

This dependency separation is the finite Fubini object needed for a genuine
target-column argument: sources with the same switched physical output now
live in definitionally the same product kernel.

Constructive contract: literal link enumeration, structural dependent
products, exact `Q'`, no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
import YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction

namespace YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A physical-only package list -/

def slabPhysicalPairRecouplingDataAtLink
    (extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (linked : {link // link ∈ boundaryCompleteSlabLinks extent}) :
    SlabPhysicalPairRecouplingData extent
      (slabIncidentPlaqIds extent linked.1).length where
  leftPhysical := leftPhysical
  rightPhysical := rightPhysical
  link := linked.1
  degree_eq := rfl

def slabPhysicalPairRecouplingPackageAtLink
    (extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (linked : {link // link ∈ boundaryCompleteSlabLinks extent}) :
    FiniteBistochasticQKernelPackage :=
  slabPhysicalPairRecouplingKernelPackage
    (slabIncidentPlaqIds extent linked.1).length
    (slabPhysicalPairRecouplingDataAtLink
      extent leftPhysical rightPhysical linked)

/-- The complete whole-slab package list depends on no auxiliary witness. -/
def slabPhysicalPairRecouplingPackages
    (extent : Nat) (leftPhysical rightPhysical : SlabLabelling) :
    List FiniteBistochasticQKernelPackage :=
  (boundaryCompleteSlabLinks extent).attach.map fun linked =>
    slabPhysicalPairRecouplingPackageAtLink
      extent leftPhysical rightPhysical linked

abbrev SlabPhysicalPairRecouplingSourceAssignment
    (extent : Nat) (leftPhysical rightPhysical : SlabLabelling) :=
  FiniteBistochasticSourceAssignment
    (slabPhysicalPairRecouplingPackages extent leftPhysical rightPhysical)

abbrev SlabPhysicalPairRecouplingTargetAssignment
    (extent : Nat) (leftPhysical rightPhysical : SlabLabelling) :=
  FiniteBistochasticTargetAssignment
    (slabPhysicalPairRecouplingPackages extent leftPhysical rightPhysical)

def slabPhysicalPairRecouplingKernel
    (extent : Nat) (leftPhysical rightPhysical : SlabLabelling) :
    FiniteBistochasticQKernel
      (SlabPhysicalPairRecouplingSourceAssignment
        extent leftPhysical rightPhysical)
      (SlabPhysicalPairRecouplingTargetAssignment
        extent leftPhysical rightPhysical) :=
  finiteBistochasticKernelProduct
    (slabPhysicalPairRecouplingPackages extent leftPhysical rightPhysical)

/-! ## 2. Accepted global assignments point at one row -/

def slabPhysicalPairRecouplingWitnessDataAtLink
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (left_mem : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent))
    (linked : {link // link ∈ boundaryCompleteSlabLinks extent}) :
    SlabPhysicalPairRecouplingWitnessData K
      (slabPhysicalPairRecouplingDataAtLink
        extent leftPhysical rightPhysical linked) where
  leftAuxiliary := slabFusionWitnessAssignmentAt linked.1 leftAssignment
  rightAuxiliary := slabFusionWitnessAssignmentAt linked.1 rightAssignment
  left_mem := slabFusionWitnessAssignmentAt_mem_local
    K extent leftPhysical (boundaryCompleteSlabLinks extent)
    leftAssignment left_mem linked.1 linked.2
  right_mem := slabFusionWitnessAssignmentAt_mem_local
    K extent rightPhysical (boundaryCompleteSlabLinks extent)
    rightAssignment right_mem linked.1 linked.2

def slabPhysicalPairPointedRecouplingPackages
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (left_mem : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent)) :
    List PointedFiniteBistochasticQKernelPackage :=
  (boundaryCompleteSlabLinks extent).attach.map fun linked =>
    slabPhysicalPairPointedRecouplingKernelPackage
      (slabPhysicalPairRecouplingDataAtLink
        extent leftPhysical rightPhysical linked)
      (slabPhysicalPairRecouplingWitnessDataAtLink
        K extent leftPhysical rightPhysical leftAssignment rightAssignment
        left_mem right_mem linked)

theorem slabPhysicalPairPointedRecouplingPackages_forget
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (left_mem : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent)) :
    finiteBistochasticPackagesOfPointed
        (slabPhysicalPairPointedRecouplingPackages K extent
          leftPhysical rightPhysical leftAssignment rightAssignment
          left_mem right_mem) =
      slabPhysicalPairRecouplingPackages
        extent leftPhysical rightPhysical := by
  unfold slabPhysicalPairPointedRecouplingPackages
    slabPhysicalPairRecouplingPackages
  induction (boundaryCompleteSlabLinks extent).attach with
  | nil => rfl
  | cons linked rest ih =>
      simp only [List.map_cons, finiteBistochasticPackagesOfPointed,
        slabPhysicalPairPointedRecouplingKernelPackage,
        slabPhysicalPairRecouplingPackageAtLink]
      exact congrArg
        (List.cons
          (slabPhysicalPairRecouplingKernelPackage
            (slabIncidentPlaqIds extent linked.1).length
            (slabPhysicalPairRecouplingDataAtLink
              extent leftPhysical rightPhysical linked))) ih

def transportFiniteBistochasticSourceAssignment
    {left right : List FiniteBistochasticQKernelPackage}
    (heq : left = right)
    (source : FiniteBistochasticSourceAssignment left) :
    FiniteBistochasticSourceAssignment right := by
  rw [← heq]
  exact source

/-- Structural source assembly over an arbitrary sublist of attached actual
links.  Keeping this recursion explicit makes the later decoder a direct
induction rather than an equality-transport argument. -/
def slabPhysicalPairRecouplingProductionSourceFrom
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (left_mem : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent)) :
    (linkedList :
      List {link // link ∈ boundaryCompleteSlabLinks extent}) →
      FiniteBistochasticSourceAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink
            extent leftPhysical rightPhysical linked)
  | [] => ()
  | linked :: rest =>
      (slabPhysicalPairRecouplingProductionSource
          (slabIncidentPlaqIds extent linked.1).length
          (slabPhysicalPairRecouplingDataAtLink
            extent leftPhysical rightPhysical linked)
          (slabPhysicalPairRecouplingWitnessDataAtLink
            K extent leftPhysical rightPhysical
            leftAssignment rightAssignment left_mem right_mem linked),
        slabPhysicalPairRecouplingProductionSourceFrom
          K extent leftPhysical rightPhysical
          leftAssignment rightAssignment left_mem right_mem rest)

/-- The literal production row selected by two accepted global auxiliary
assignments in the common physical-only product matrix. -/
def slabPhysicalPairRecouplingProductionSource
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (left_mem : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent)) :
    SlabPhysicalPairRecouplingSourceAssignment
      extent leftPhysical rightPhysical :=
  slabPhysicalPairRecouplingProductionSourceFrom
    K extent leftPhysical rightPhysical leftAssignment rightAssignment
    left_mem right_mem (boundaryCompleteSlabLinks extent).attach

theorem slabPhysicalPairRecouplingProductionSourceFrom_lookup_injective
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
        (boundaryCompleteSlabLinks extent)) :
    ∀ linkedList,
      slabPhysicalPairRecouplingProductionSourceFrom
          K extent leftPhysical rightPhysical
          leftAssignment₁ rightAssignment₁ left_mem₁ right_mem₁
          linkedList =
        slabPhysicalPairRecouplingProductionSourceFrom
          K extent leftPhysical rightPhysical
          leftAssignment₂ rightAssignment₂ left_mem₂ right_mem₂
          linkedList →
      ∀ linked, linked ∈ linkedList →
        slabFusionWitnessAssignmentAt linked.1 leftAssignment₁ =
            slabFusionWitnessAssignmentAt linked.1 leftAssignment₂ ∧
          slabFusionWitnessAssignmentAt linked.1 rightAssignment₁ =
            slabFusionWitnessAssignmentAt linked.1 rightAssignment₂
  | [], _, linked, hlinked => False.elim (List.not_mem_nil hlinked)
  | head :: rest, heq, linked, hlinked => by
      have hheadSource := congrArg Prod.fst heq
      have htailSource := congrArg Prod.snd heq
      simp only [slabPhysicalPairRecouplingProductionSourceFrom]
        at hheadSource htailSource
      have hhead :=
        slabPhysicalPairRecouplingProductionSource_auxiliaries_injective
          (slabPhysicalPairRecouplingDataAtLink
            extent leftPhysical rightPhysical head)
          (slabPhysicalPairRecouplingWitnessDataAtLink
            K extent leftPhysical rightPhysical
            leftAssignment₁ rightAssignment₁ left_mem₁ right_mem₁ head)
          (slabPhysicalPairRecouplingWitnessDataAtLink
            K extent leftPhysical rightPhysical
            leftAssignment₂ rightAssignment₂ left_mem₂ right_mem₂ head)
          hheadSource
      rcases List.mem_cons.mp hlinked with hlinkedHead | hlinkedTail
      · subst linked
        simpa only [slabPhysicalPairRecouplingWitnessDataAtLink] using hhead
      · exact slabPhysicalPairRecouplingProductionSourceFrom_lookup_injective
          K extent leftPhysical rightPhysical
          leftAssignment₁ rightAssignment₁
          leftAssignment₂ rightAssignment₂
          left_mem₁ right_mem₁ left_mem₂ right_mem₂
          rest htailSource linked hlinkedTail

/-- **The common whole-slab row is an injective code for the two accepted
global auxiliary assignments.** -/
theorem slabPhysicalPairRecouplingProductionSource_assignments_injective
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
    (heq : slabPhysicalPairRecouplingProductionSource K extent
        leftPhysical rightPhysical leftAssignment₁ rightAssignment₁
        left_mem₁ right_mem₁ =
      slabPhysicalPairRecouplingProductionSource K extent
        leftPhysical rightPhysical leftAssignment₂ rightAssignment₂
        left_mem₂ right_mem₂) :
    leftAssignment₁ = leftAssignment₂ ∧
      rightAssignment₁ = rightAssignment₂ := by
  have hlookups :=
    slabPhysicalPairRecouplingProductionSourceFrom_lookup_injective
      K extent leftPhysical rightPhysical
      leftAssignment₁ rightAssignment₁
      leftAssignment₂ rightAssignment₂
      left_mem₁ right_mem₁ left_mem₂ right_mem₂
      (boundaryCompleteSlabLinks extent).attach heq
  have left_reconstruct₁ := slabFusionWitnessAssignmentFrom_at_eq
    K extent leftPhysical (boundaryCompleteSlabLinks extent)
    leftAssignment₁ (boundaryCompleteSlabLinks_nodup extent) left_mem₁
  have left_reconstruct₂ := slabFusionWitnessAssignmentFrom_at_eq
    K extent leftPhysical (boundaryCompleteSlabLinks extent)
    leftAssignment₂ (boundaryCompleteSlabLinks_nodup extent) left_mem₂
  have right_reconstruct₁ := slabFusionWitnessAssignmentFrom_at_eq
    K extent rightPhysical (boundaryCompleteSlabLinks extent)
    rightAssignment₁ (boundaryCompleteSlabLinks_nodup extent) right_mem₁
  have right_reconstruct₂ := slabFusionWitnessAssignmentFrom_at_eq
    K extent rightPhysical (boundaryCompleteSlabLinks extent)
    rightAssignment₂ (boundaryCompleteSlabLinks_nodup extent) right_mem₂
  constructor
  · rw [← left_reconstruct₁, ← left_reconstruct₂]
    unfold slabFusionWitnessAssignmentFrom
    apply List.map_congr_left
    intro link hlink
    congr 1
    exact (hlookups ⟨link, hlink⟩
      (List.mem_attach _ ⟨link, hlink⟩)).1
  · rw [← right_reconstruct₁, ← right_reconstruct₂]
    unfold slabFusionWitnessAssignmentFrom
    apply List.map_congr_left
    intro link hlink
    congr 1
    exact (hlookups ⟨link, hlink⟩
      (List.mem_attach _ ⟨link, hlink⟩)).2

theorem slabPhysicalPairRecouplingProductionSource_row_normalized
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (left_mem : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent)) :
    listQSum
        ((slabPhysicalPairRecouplingKernel
          extent leftPhysical rightPhysical).weight
          (slabPhysicalPairRecouplingProductionSource K extent
            leftPhysical rightPhysical leftAssignment rightAssignment
            left_mem right_mem))
        (slabPhysicalPairRecouplingKernel
          extent leftPhysical rightPhysical).targets ≈ 1 :=
  (slabPhysicalPairRecouplingKernel
    extent leftPhysical rightPhysical).row_normalized _

theorem slabPhysicalPairRecouplingKernel_column_normalized
    (extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (target : SlabPhysicalPairRecouplingTargetAssignment
      extent leftPhysical rightPhysical) :
    listQSum
        (fun source =>
          (slabPhysicalPairRecouplingKernel
            extent leftPhysical rightPhysical).weight source target)
        (slabPhysicalPairRecouplingKernel
          extent leftPhysical rightPhysical).sources ≈ 1 :=
  (slabPhysicalPairRecouplingKernel
    extent leftPhysical rightPhysical).column_normalized target

end YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct

#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct.slabPhysicalPairRecouplingPackages
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct.slabPhysicalPairRecouplingKernel
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct.slabPhysicalPairPointedRecouplingPackages_forget
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct.slabPhysicalPairRecouplingProductionSource
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct.slabPhysicalPairRecouplingProductionSourceFrom_lookup_injective
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct.slabPhysicalPairRecouplingProductionSource_assignments_injective
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct.slabPhysicalPairRecouplingProductionSource_row_normalized
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct.slabPhysicalPairRecouplingKernel_column_normalized
