/-
# Fixed-order Cartesian carrier for complete-source lowered targets

Every lowered target now has a source-independent order at every complete
slab link.  This file enumerates the resulting heterogeneous Cartesian fiber,
proves that its cardinality is exactly the genuine SU(2) production
multiplicity, and places every deterministic lowered target inside it.

The carrier is a bookkeeping compiler.  It does not yet sum over physical
target labellings or prove the final target-congestion bound.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrder

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetCarrier

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceEnumeration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrder
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Constructing a dependent tuple from pointwise choices -/

/-- Assemble a structural heterogeneous tuple from one choice in every
fiber. -/
def dependentFiniteAssignmentOfFunction
    {A : Type} {fiber : A → Type} :
    (items : List A) → ((item : A) → fiber item) →
      DependentFiniteAssignment fiber items
  | [], _ => ()
  | head :: tail, choice =>
      (choice head, dependentFiniteAssignmentOfFunction tail choice)

/-- Structural assembly is a right inverse to coordinate lookup. -/
theorem dependentFiniteAssignmentOfFunction_get
    {A : Type} [DecidableEq A] {fiber : A → Type} :
    ∀ (items : List A) (choice : (item : A) → fiber item)
      (item : A) (hitem : item ∈ items),
      (dependentFiniteAssignmentOfFunction items choice).get item hitem =
        choice item
  | [], _, _, hitem => False.elim (List.not_mem_nil hitem)
  | head :: tail, choice, item, hitem => by
      unfold dependentFiniteAssignmentOfFunction
        DependentFiniteAssignment.get
      split
      · rename_i heq
        subst item
        rfl
      · rename_i hne
        exact dependentFiniteAssignmentOfFunction_get tail choice item (by
          rcases List.mem_cons.mp hitem with hhead | htail
          · exact False.elim (hne hhead)
          · exact htail)

/-- Pointwise membership places the assembled tuple in the explicit
heterogeneous Cartesian enumeration. -/
theorem dependentFiniteAssignmentOfFunction_mem
    {A : Type} {fiber : A → Type}
    (entries : (item : A) → List (fiber item)) :
    ∀ (items : List A) (choice : (item : A) → fiber item),
      (∀ item, choice item ∈ entries item) →
      dependentFiniteAssignmentOfFunction items choice ∈
        dependentFiniteAssignments entries items
  | [], _, _ => List.mem_cons_self
  | head :: tail, choice, hchoice => by
      unfold dependentFiniteAssignmentOfFunction
        dependentFiniteAssignments
      apply List.mem_flatMap.mpr
      refine ⟨choice head, hchoice head, ?_⟩
      apply List.mem_map.mpr
      exact ⟨dependentFiniteAssignmentOfFunction tail choice,
        dependentFiniteAssignmentOfFunction_mem entries tail choice hchoice,
        rfl⟩

/-- Type-level realization of one pointwise choice inside an enumerated
heterogeneous product. -/
structure DependentFiniteAssignmentRealization
    {A : Type} [DecidableEq A] {fiber : A → Type}
    (entries : (item : A) → List (fiber item))
    (items : List A) (choice : (item : A) → fiber item) : Type where
  tuple : DependentFiniteAssignment fiber items
  tuple_mem : tuple ∈ dependentFiniteAssignments entries items
  get_eq : ∀ item (hitem : item ∈ items),
    tuple.get item hitem = choice item

/-- Package an enumerated dependent tuple together with exact recovery of all
pointwise choices.  The record boundary prevents consumers from normalizing a
large concrete heterogeneous product. -/
def dependentFiniteAssignmentsRealize
    {A : Type} [DecidableEq A] {fiber : A → Type}
    (entries : (item : A) → List (fiber item))
    (items : List A) (choice : (item : A) → fiber item)
    (hchoice : ∀ item, choice item ∈ entries item) :
    DependentFiniteAssignmentRealization entries items choice where
  tuple := dependentFiniteAssignmentOfFunction items choice
  tuple_mem :=
    dependentFiniteAssignmentOfFunction_mem entries items choice hchoice
  get_eq := dependentFiniteAssignmentOfFunction_get items choice

/-! ## 2. The fixed-order local and global target fibers -/

/-- One accepted auxiliary field in the common order at one displayed link. -/
abbrev CubeInwardMateFixedOrderTargetWitness
    (K : Nat) (target : EdgeLabelling)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1}) :=
  { auxiliary : EdgeLabelling //
    auxiliary ∈ orderedSlabLinkFusionWitnesses K target
      (cubeInwardMateCompleteSourceFaceOrder linked) }

/-- The literal accepted local fiber, with membership retained in its type. -/
def cubeInwardMateFixedOrderTargetWitnesses
    (K : Nat) (target : EdgeLabelling)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1}) :
    List (CubeInwardMateFixedOrderTargetWitness K target linked) :=
  (orderedSlabLinkFusionWitnesses K target
    (cubeInwardMateCompleteSourceFaceOrder linked)).attach

/-- Reordering a bounded target spin word does not change its production
SU(2) fusion multiplicity. -/
theorem cubeInwardMateFixedOrderTargetWitnesses_length
    (K : Nat) (target : EdgeLabelling)
    (hbounded : SlabFaceLabellingBounded K 1 target)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1}) :
    (cubeInwardMateFixedOrderTargetWitnesses K target linked).length =
      slabExplicitLinkMultiplicity K 1 target linked.1 := by
  unfold cubeInwardMateFixedOrderTargetWitnesses
  rw [List.length_attach]
  unfold orderedSlabLinkFusionWitnesses
  rw [fusionWitnessesForSpins_length_eq_explicit _ _
    (by
      simpa only [List.length_map] using
        (cubeInwardMateCompleteSourceFaceOrder linked).length_le_six)]
  unfold slabExplicitLinkMultiplicity
  exact (explicitValenceMultiplicity_physical_perm
    ((cubeInwardMateCompleteSourceFaceOrder linked).production_perm.map target)
    (by
      simpa only [List.length_map] using
        slabIncidentPlaqIds_length_le_six 1 linked.1)
    (slabIncidentSpins_bounded hbounded linked.1)).symm

/-- Every local fixed-order target fiber is duplicate-free. -/
theorem cubeInwardMateFixedOrderTargetWitnesses_nodup
    (K : Nat) (target : EdgeLabelling)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1}) :
    (cubeInwardMateFixedOrderTargetWitnesses K target linked).Nodup := by
  unfold cubeInwardMateFixedOrderTargetWitnesses
  apply attach_nodup_of_nodup
  unfold orderedSlabLinkFusionWitnesses fusionWitnessesForSpins
  apply List.filter_sublist.nodup
  apply boundedEdgeLabellings_nodup
  exact canonicalUsedAuxiliaryCoordinates_nodup (by
    simpa only [List.length_map] using
      (cubeInwardMateCompleteSourceFaceOrder linked).length_le_six)

/-- One accepted fixed-order choice at every complete extent-one slab link. -/
abbrev CubeInwardMateFixedOrderTargetTuple
    (K : Nat) (target : EdgeLabelling) :=
  DependentFiniteAssignment
    (fun linked : {link // link ∈ boundaryCompleteSlabLinks 1} =>
      CubeInwardMateFixedOrderTargetWitness K target linked)
    (boundaryCompleteSlabLinks 1).attach

/-- The complete heterogeneous Cartesian target fiber. -/
def cubeInwardMateFixedOrderTargetTuples
    (K : Nat) (target : EdgeLabelling) :
    List (CubeInwardMateFixedOrderTargetTuple K target) :=
  dependentFiniteAssignments
    (cubeInwardMateFixedOrderTargetWitnesses K target)
    (boundaryCompleteSlabLinks 1).attach

/-- The fixed-order Cartesian target fiber has exactly the genuine global
production multiplicity. -/
theorem cubeInwardMateFixedOrderTargetTuples_length
    (K : Nat) (target : EdgeLabelling)
    (hbounded : SlabFaceLabellingBounded K 1 target) :
    (cubeInwardMateFixedOrderTargetTuples K target).length =
      slabExplicitLinkMultiplicityProduct K 1 target := by
  unfold cubeInwardMateFixedOrderTargetTuples
  rw [dependentFiniteAssignments_length]
  unfold slabExplicitLinkMultiplicityProduct
  calc
    natListProduct
        (fun linked =>
          (cubeInwardMateFixedOrderTargetWitnesses
            K target linked).length)
        (boundaryCompleteSlabLinks 1).attach =
        natListProduct
          (fun linked =>
            slabExplicitLinkMultiplicity K 1 target linked.1)
          (boundaryCompleteSlabLinks 1).attach :=
      natListProduct_congr _ _ _ (fun linked _ =>
        cubeInwardMateFixedOrderTargetWitnesses_length
          K target hbounded linked)
    _ = natListProduct (slabExplicitLinkMultiplicity K 1 target)
          ((boundaryCompleteSlabLinks 1).attach.map Subtype.val) :=
      (natListProduct_map
        (slabExplicitLinkMultiplicity K 1 target) Subtype.val
        (boundaryCompleteSlabLinks 1).attach).symm
    _ = natListProduct (slabExplicitLinkMultiplicity K 1 target)
          (boundaryCompleteSlabLinks 1) := by
      rw [List.attach_map_subtype_val]

/-- The complete fixed-order target tuple enumeration is duplicate-free. -/
theorem cubeInwardMateFixedOrderTargetTuples_nodup
    (K : Nat) (target : EdgeLabelling) :
    (cubeInwardMateFixedOrderTargetTuples K target).Nodup := by
  unfold cubeInwardMateFixedOrderTargetTuples
  exact dependentFiniteAssignments_nodup
    (cubeInwardMateFixedOrderTargetWitnesses K target)
    (cubeInwardMateFixedOrderTargetWitnesses_nodup K target)
    (boundaryCompleteSlabLinks 1).attach

/-! ## 3. Every fixed-order presented target belongs to the carrier -/

/-- Recode one fixed-order presented coordinate in the local target subtype. -/
def cubeInwardMateFixedOrderTargetChoiceOfPresented
    {K : Nat} {target : EdgeLabelling}
    (assignment : PresentedSlabFusionWitnessAssignment
      K 1 target (boundaryCompleteSlabLinks 1))
    (horder : ∀ linked,
      (assignment linked).order = cubeInwardMateCompleteSourceFaceOrder linked)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1}) :
    CubeInwardMateFixedOrderTargetWitness K target linked :=
  ⟨(assignment linked).auxiliary, by
    rw [← horder linked]
    exact (assignment linked).auxiliary_mem⟩

/-- Realize a fixed-order presentation as an enumerated target tuple while
retaining exact recovery of every local coordinate. -/
def cubeInwardMateFixedOrderTargetPresentedRealization
    {K : Nat} {target : EdgeLabelling}
    (assignment : PresentedSlabFusionWitnessAssignment
      K 1 target (boundaryCompleteSlabLinks 1))
    (horder : ∀ linked,
      (assignment linked).order = cubeInwardMateCompleteSourceFaceOrder linked) :
    DependentFiniteAssignmentRealization
      (cubeInwardMateFixedOrderTargetWitnesses K target)
      (boundaryCompleteSlabLinks 1).attach
      (cubeInwardMateFixedOrderTargetChoiceOfPresented assignment horder) := by
  exact dependentFiniteAssignmentsRealize
    (cubeInwardMateFixedOrderTargetWitnesses K target)
    (boundaryCompleteSlabLinks 1).attach
    (cubeInwardMateFixedOrderTargetChoiceOfPresented assignment horder)
    (fun linked => List.mem_attach
      (orderedSlabLinkFusionWitnesses K target
        (cubeInwardMateCompleteSourceFaceOrder linked))
      (cubeInwardMateFixedOrderTargetChoiceOfPresented
        assignment horder linked))

/-! ## 4. The deterministic peel specializes the generic carrier compiler -/

/-- Every realized lowered assignment is witnessed inside its exact
fixed-order Cartesian target fiber. -/
def enumeratedCubeInwardMateFullSourceLowerTargetFixedOrderRealization
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource K physical hK hbounded) :
    DependentFiniteAssignmentRealization
      (cubeInwardMateFixedOrderTargetWitnesses
        K entry.adaptiveInverseData.lowerPhysical)
      (boundaryCompleteSlabLinks 1).attach
      (cubeInwardMateFixedOrderTargetChoiceOfPresented
        entry.adaptiveInverseData.lowerAssignment
        (YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrder.EnumeratedCubeInwardMateFullSource.adaptiveInverseData_lowerAssignment_order
          entry)) := by
  let horder :=
    YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrder.EnumeratedCubeInwardMateFullSource.adaptiveInverseData_lowerAssignment_order
      entry
  exact cubeInwardMateFixedOrderTargetPresentedRealization
    entry.adaptiveInverseData.lowerAssignment horder

#print axioms dependentFiniteAssignmentOfFunction_get
#print axioms dependentFiniteAssignmentOfFunction_mem
#print axioms dependentFiniteAssignmentsRealize
#print axioms cubeInwardMateFixedOrderTargetWitnesses_length
#print axioms cubeInwardMateFixedOrderTargetWitnesses_nodup
#print axioms cubeInwardMateFixedOrderTargetTuples_length
#print axioms cubeInwardMateFixedOrderTargetTuples_nodup
#print axioms cubeInwardMateFixedOrderTargetChoiceOfPresented
#print axioms cubeInwardMateFixedOrderTargetPresentedRealization
#print axioms enumeratedCubeInwardMateFullSourceLowerTargetFixedOrderRealization

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetCarrier
