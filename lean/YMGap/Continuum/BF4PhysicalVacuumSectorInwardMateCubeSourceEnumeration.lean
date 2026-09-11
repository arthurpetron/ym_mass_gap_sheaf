/-
# Enumerate the complete root-first cube source product

The certified inward-mate classifier consumes one accepted witness in the
literal root-first face order at each of the twelve cube incidences.  This
file constructs that dependent finite product explicitly.

The root-first local list is not identified elementwise with the production
list.  Instead, the already-proved SU(2) fusion-path permutation theorem
shows that the two lists have the same length at the physical `6*K` channel
cutoff.  Thus the dependent product has exactly the cube-boundary production
multiplicity while retaining the presentation required by the classifier.

A structural lookup turns each dependent tuple into the function-valued
source assignment used downstream.  Duplicate-free local fibers and
duplicate-free cube incidences make this conversion injective, so the final
function-valued enumeration remains duplicate-free.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
import YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
import YMGap.Continuum.Z4FusionMultiplicityPermutationLift

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceEnumeration

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. A reusable heterogeneous finite product -/

/-- One correctly typed choice from the fiber over every item in a written
list. -/
def DependentFiniteAssignment {A : Type} (fiber : A -> Type) :
    List A -> Type
  | [] => Unit
  | head :: tail => fiber head × DependentFiniteAssignment fiber tail

/-- Enumerate the complete heterogeneous product of explicit local fibers. -/
def dependentFiniteAssignments {A : Type} {fiber : A -> Type}
    (entries : (item : A) -> List (fiber item)) :
    (items : List A) -> List (DependentFiniteAssignment fiber items)
  | [] => [()]
  | head :: tail =>
      (entries head).flatMap fun entry =>
        (dependentFiniteAssignments entries tail).map fun rest =>
          (entry, rest)

private theorem flatMap_pair_length {A B : Type}
    (heads : List A) (tails : List B) :
    (heads.flatMap fun head => tails.map fun tail => (head, tail)).length =
      heads.length * tails.length := by
  induction heads with
  | nil => simp
  | cons head rest ih =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_map, List.length_cons]
      rw [ih, Nat.succ_mul, Nat.add_comm]

/-- The heterogeneous enumeration has the expected product cardinality. -/
theorem dependentFiniteAssignments_length {A : Type} {fiber : A -> Type}
    (entries : (item : A) -> List (fiber item)) : forall items : List A,
    (dependentFiniteAssignments entries items).length =
      natListProduct (fun item => (entries item).length) items
  | [] => rfl
  | head :: tail => by
      simpa only [dependentFiniteAssignments, natListProduct,
        dependentFiniteAssignments_length entries tail] using
        flatMap_pair_length (entries head)
          (dependentFiniteAssignments entries tail)

/-- Read the coordinate at a listed item.  The membership proof certifies
that the structurally unreachable empty branch is never used. -/
def DependentFiniteAssignment.get {A : Type} [DecidableEq A]
    {fiber : A -> Type} :
    {items : List A} -> DependentFiniteAssignment fiber items ->
      (item : A) -> item ∈ items -> fiber item
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, assignment, item, hmem =>
      if heq : item = head then
        heq ▸ assignment.1
      else
        DependentFiniteAssignment.get assignment.2 item (by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact False.elim (heq hhead)
          · exact htail)

/-- On a duplicate-free item list, equality of every structural lookup
reconstructs equality of the complete dependent tuple. -/
theorem DependentFiniteAssignment.eq_of_get_eq
    {A : Type} [DecidableEq A] {fiber : A -> Type} :
    forall {items : List A}, items.Nodup ->
      forall (left right : DependentFiniteAssignment fiber items),
      (forall item (hmem : item ∈ items),
        left.get item hmem = right.get item hmem) -> left = right
  | [], _, left, right, _ => by
      cases left
      cases right
      rfl
  | head :: tail, hnodup, left, right, heq => by
      have hparts := List.nodup_cons.mp hnodup
      have hhead : left.1 = right.1 := by
        simpa [DependentFiniteAssignment.get] using
          heq head List.mem_cons_self
      have htail : left.2 = right.2 := by
        apply DependentFiniteAssignment.eq_of_get_eq hparts.2
        intro item hitem
        have hne : item ≠ head := by
          intro hsame
          subst item
          exact hparts.1 hitem
        simpa [DependentFiniteAssignment.get, hne] using
          heq item (List.mem_cons_of_mem head hitem)
      cases left
      cases right
      simp only at hhead htail
      rw [hhead, htail]

private theorem nodup_flatMap_pairs {A B : Type}
    (heads : List A) (tails : List B)
    (hheads : heads.Nodup) (htails : tails.Nodup) :
    (heads.flatMap fun head => tails.map fun tail => (head, tail)).Nodup := by
  induction heads with
  | nil => exact List.nodup_nil
  | cons head rest ih =>
      have hparts := List.nodup_cons.mp hheads
      rw [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨?_, ih hparts.2, ?_⟩
      · apply CayleyPruferInjection.nodup_map_of_injOn
          (fun tail => (head, tail)) tails htails
        intro left _ right _ heq
        exact congrArg Prod.snd heq
      · intro left hleft right hright heq
        obtain ⟨leftTail, _, hleftEq⟩ := List.mem_map.mp hleft
        obtain ⟨rightHead, hrightHead, hrightBlock⟩ :=
          List.mem_flatMap.mp hright
        obtain ⟨rightTail, _, hrightEq⟩ := List.mem_map.mp hrightBlock
        have hpairs : (head, leftTail) = (rightHead, rightTail) := by
          exact hleftEq.trans (heq.trans hrightEq.symm)
        have hheadEq := congrArg (fun pair : A × B => pair.1) hpairs
        change head = rightHead at hheadEq
        exact hparts.1 (hheadEq.symm ▸ hrightHead)

/-- Duplicate-free local fibers give a duplicate-free heterogeneous product. -/
theorem dependentFiniteAssignments_nodup {A : Type} {fiber : A -> Type}
    (entries : (item : A) -> List (fiber item))
    (hnodup : forall item, (entries item).Nodup) : forall items : List A,
    (dependentFiniteAssignments entries items).Nodup
  | [] => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | head :: tail => by
      unfold dependentFiniteAssignments
      exact nodup_flatMap_pairs (entries head)
        (dependentFiniteAssignments entries tail)
        (hnodup head) (dependentFiniteAssignments_nodup entries hnodup tail)

/-! ## 2. The physical root-first local fibers have production size -/

/-- The actual accepted root-first witnesses, with membership retained as
Type-level data. -/
def cubeInwardMateOrderedSourceWitnesses
    (K : Nat) (physical : EdgeLabelling)
    (linked : CubeProductionIncidenceMember) :
    List (CubeInwardMateOrderedSourceWitness K physical linked) :=
  (orderedSlabLinkFusionWitnesses K physical
    (cubeInwardMateSourceFaceOrder linked)).attach

/-- Reordering the external spin word changes the basis presentation but not
the completed SU(2) fusion multiplicity. -/
theorem cubeInwardMateOrderedSourceWitnesses_length
    (K : Nat) (physical : EdgeLabelling)
    (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) :
    (cubeInwardMateOrderedSourceWitnesses K physical linked).length =
      cubeInwardMateSourceLinkMultiplicity K physical linked := by
  unfold cubeInwardMateOrderedSourceWitnesses
  rw [List.length_attach]
  unfold orderedSlabLinkFusionWitnesses
  rw [fusionWitnessesForSpins_length_eq_explicit _ _
    (by
      simpa only [List.length_map] using
        (cubeInwardMateSourceFaceOrder linked).length_le_six)]
  unfold cubeInwardMateSourceLinkMultiplicity slabExplicitLinkMultiplicity
  exact (explicitValenceMultiplicity_physical_perm
    ((cubeInwardMateSourceFaceOrder linked).production_perm.map physical)
    (by
      simpa only [List.length_map] using
        slabIncidentPlaqIds_length_le_six 1 linked.1.link)
    (slabIncidentSpins_bounded hbounded linked.1.link)).symm

/-- Every local root-first witness fiber is duplicate-free. -/
theorem cubeInwardMateOrderedSourceWitnesses_nodup
    (K : Nat) (physical : EdgeLabelling)
    (linked : CubeProductionIncidenceMember) :
    (cubeInwardMateOrderedSourceWitnesses K physical linked).Nodup := by
  unfold cubeInwardMateOrderedSourceWitnesses
  apply attach_nodup_of_nodup
  unfold orderedSlabLinkFusionWitnesses fusionWitnessesForSpins
  apply List.filter_sublist.nodup
  apply boundedEdgeLabellings_nodup
  exact canonicalUsedAuxiliaryCoordinates_nodup (by
    simpa only [List.length_map] using
      (cubeInwardMateSourceFaceOrder linked).length_le_six)

/-! ## 3. Exact twelve-link source enumeration -/

abbrev CubeInwardMateOrderedSourceTuple
    (K : Nat) (physical : EdgeLabelling) :=
  DependentFiniteAssignment
    (fun linked : CubeProductionIncidenceMember =>
      CubeInwardMateOrderedSourceWitness K physical linked)
    cubeProductionIncidences.attach

/-- The literal finite product of the twelve dependent root-first fibers. -/
def cubeInwardMateOrderedSourceTuples
    (K : Nat) (physical : EdgeLabelling) :
    List (CubeInwardMateOrderedSourceTuple K physical) :=
  dependentFiniteAssignments
    (cubeInwardMateOrderedSourceWitnesses K physical)
    cubeProductionIncidences.attach

/-- Read a dependent tuple as the function-valued source assignment consumed
by the certified classifier. -/
def CubeInwardMateOrderedSourceTuple.toAssignment
    {K : Nat} {physical : EdgeLabelling}
    (tuple : CubeInwardMateOrderedSourceTuple K physical) :
    CubeInwardMateOrderedSourceWitnessAssignment K physical :=
  fun linked => tuple.get linked
    (List.mem_attach cubeProductionIncidences linked)

/-- The structural tuple-to-function conversion loses no coordinate. -/
theorem CubeInwardMateOrderedSourceTuple.toAssignment_injective
    (K : Nat) (physical : EdgeLabelling) :
    Function.Injective
      (@CubeInwardMateOrderedSourceTuple.toAssignment K physical) := by
  intro left right heq
  apply DependentFiniteAssignment.eq_of_get_eq
    (attach_nodup_of_nodup cubeProductionIncidences
      cubeProductionIncidences_nodup)
  intro linked hlinked
  have hcoordinate := congrFun heq linked
  simpa [CubeInwardMateOrderedSourceTuple.toAssignment] using hcoordinate

/-- The final function-valued finite source family. -/
def cubeInwardMateOrderedSourceAssignments
    (K : Nat) (physical : EdgeLabelling) :
    List (CubeInwardMateOrderedSourceWitnessAssignment K physical) :=
  (cubeInwardMateOrderedSourceTuples K physical).map
    CubeInwardMateOrderedSourceTuple.toAssignment

/-- The explicit source family is duplicate-free. -/
theorem cubeInwardMateOrderedSourceAssignments_nodup
    (K : Nat) (physical : EdgeLabelling) :
    (cubeInwardMateOrderedSourceAssignments K physical).Nodup := by
  unfold cubeInwardMateOrderedSourceAssignments
  apply CayleyPruferInjection.nodup_map_of_injOn
    CubeInwardMateOrderedSourceTuple.toAssignment
    (cubeInwardMateOrderedSourceTuples K physical)
  · unfold cubeInwardMateOrderedSourceTuples
    exact dependentFiniteAssignments_nodup
      (cubeInwardMateOrderedSourceWitnesses K physical)
      (cubeInwardMateOrderedSourceWitnesses_nodup K physical)
      cubeProductionIncidences.attach
  · intro left _ right _ heq
    exact CubeInwardMateOrderedSourceTuple.toAssignment_injective
      K physical heq

/-- **Exact cube-source enumeration.**  The function-valued root-first
source family has exactly the production cube-boundary multiplicity. -/
theorem cubeInwardMateOrderedSourceAssignments_length
    (K : Nat) (physical : EdgeLabelling)
    (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateOrderedSourceAssignments K physical).length =
      cubeInwardMateSourceBoundaryProduct K physical := by
  unfold cubeInwardMateOrderedSourceAssignments
  rw [List.length_map]
  unfold cubeInwardMateOrderedSourceTuples
  rw [dependentFiniteAssignments_length]
  unfold cubeInwardMateSourceBoundaryProduct
  exact natListProduct_congr _ _ cubeProductionIncidences.attach
    (fun linked _ =>
      cubeInwardMateOrderedSourceWitnesses_length
        K physical hbounded linked)

/-! ## 4. Enumerate the certified target-or-first-stretched outcomes -/

/-- Apply the certified injective dichotomy to the complete finite source
family. -/
def cubeInwardMateCertifiedSourceOutcomes
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 <= K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    List
      (Sum
        (CubeInwardMateOrderedTargetWitnessAssignment K physical)
        (CubeInwardMateCertifiedFirstStretchedSource
          K physical hK hbounded)) :=
  (cubeInwardMateOrderedSourceAssignments K physical).map
    (cubeInwardMateCertifiedSourceTargetOrFirstStretched
      K physical hK hbounded)

/-- Classification preserves every source multiplicity exactly. -/
theorem cubeInwardMateCertifiedSourceOutcomes_length
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 <= K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateCertifiedSourceOutcomes
      K physical hK hbounded).length =
      cubeInwardMateSourceBoundaryProduct K physical := by
  unfold cubeInwardMateCertifiedSourceOutcomes
  rw [List.length_map,
    cubeInwardMateOrderedSourceAssignments_length K physical hbounded]

/-- The classified finite family remains duplicate-free. -/
theorem cubeInwardMateCertifiedSourceOutcomes_nodup
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 <= K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateCertifiedSourceOutcomes
      K physical hK hbounded).Nodup := by
  unfold cubeInwardMateCertifiedSourceOutcomes
  apply CayleyPruferInjection.nodup_map_of_injOn
    (cubeInwardMateCertifiedSourceTargetOrFirstStretched
      K physical hK hbounded)
    (cubeInwardMateOrderedSourceAssignments K physical)
  · exact cubeInwardMateOrderedSourceAssignments_nodup K physical
  · intro left _ right _ heq
    exact cubeInwardMateCertifiedSourceTargetOrFirstStretched_injective
      K physical hK hbounded heq

/-! ## 5. Extract the two classified branches without losing witnesses -/

/-- Retain the left payloads of a finite sum-valued family. -/
def sumInlValues {A B : Type} : List (Sum A B) -> List A
  | [] => []
  | Sum.inl left :: rest => left :: sumInlValues rest
  | Sum.inr _ :: rest => sumInlValues rest

/-- Retain the right payloads of a finite sum-valued family. -/
def sumInrValues {A B : Type} : List (Sum A B) -> List B
  | [] => []
  | Sum.inl _ :: rest => sumInrValues rest
  | Sum.inr right :: rest => right :: sumInrValues rest

theorem mem_sumInlValues_iff {A B : Type} {left : A} :
    forall items : List (Sum A B),
    left ∈ sumInlValues items <-> Sum.inl left ∈ items
  | [] => by simp [sumInlValues]
  | Sum.inl head :: rest => by
      simp only [sumInlValues, List.mem_cons, Sum.inl.injEq]
      rw [mem_sumInlValues_iff rest]
  | Sum.inr head :: rest => by
      simp only [sumInlValues, List.mem_cons,
        Sum.inl_ne_inr, false_or]
      exact mem_sumInlValues_iff rest

theorem mem_sumInrValues_iff {A B : Type} {right : B} :
    forall items : List (Sum A B),
    right ∈ sumInrValues items <-> Sum.inr right ∈ items
  | [] => by simp [sumInrValues]
  | Sum.inl head :: rest => by
      simp only [sumInrValues, List.mem_cons, Sum.inr_ne_inl, false_or]
      exact mem_sumInrValues_iff rest
  | Sum.inr head :: rest => by
      simp only [sumInrValues, List.mem_cons, Sum.inr.injEq]
      rw [mem_sumInrValues_iff rest]

/-- Projecting either disjoint constructor branch preserves
duplicate-freeness. -/
theorem sumInlValues_nodup {A B : Type} :
    forall {items : List (Sum A B)}, items.Nodup ->
      (sumInlValues items).Nodup
  | [], _ => List.nodup_nil
  | Sum.inl head :: rest, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, sumInlValues_nodup hparts.2⟩
      intro hhead
      exact hparts.1 ((mem_sumInlValues_iff rest).mp hhead)
  | Sum.inr _ :: rest, hnodup =>
      sumInlValues_nodup (items := rest) (List.nodup_cons.mp hnodup).2

theorem sumInrValues_nodup {A B : Type} :
    forall {items : List (Sum A B)}, items.Nodup ->
      (sumInrValues items).Nodup
  | [], _ => List.nodup_nil
  | Sum.inl _ :: rest, hnodup =>
      sumInrValues_nodup (items := rest) (List.nodup_cons.mp hnodup).2
  | Sum.inr head :: rest, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, sumInrValues_nodup hparts.2⟩
      intro hhead
      exact hparts.1 ((mem_sumInrValues_iff rest).mp hhead)

/-- The two extracted branch lengths partition the original finite family. -/
theorem sumInlValues_length_add_sumInrValues_length {A B : Type} :
    forall items : List (Sum A B),
    (sumInlValues items).length + (sumInrValues items).length = items.length
  | [] => rfl
  | Sum.inl _ :: rest => by
      have ih := sumInlValues_length_add_sumInrValues_length rest
      simp only [sumInlValues, sumInrValues, List.length_cons]
      omega
  | Sum.inr _ :: rest => by
      have ih := sumInlValues_length_add_sumInrValues_length rest
      simp only [sumInlValues, sumInrValues, List.length_cons]
      omega

/-- Every certified all-target assignment in the exact outcome family. -/
def cubeInwardMateCertifiedTargetAssignments
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 <= K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    List (CubeInwardMateOrderedTargetWitnessAssignment K physical) :=
  sumInlValues
    (cubeInwardMateCertifiedSourceOutcomes K physical hK hbounded)

/-- Every certified first-stretched source in the exact outcome family. -/
def cubeInwardMateCertifiedFirstStretchedSources
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 <= K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    List (CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded) :=
  sumInrValues
    (cubeInwardMateCertifiedSourceOutcomes K physical hK hbounded)

theorem cubeInwardMateCertifiedTargetAssignments_nodup
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 <= K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateCertifiedTargetAssignments
      K physical hK hbounded).Nodup :=
  sumInlValues_nodup
    (cubeInwardMateCertifiedSourceOutcomes_nodup
      K physical hK hbounded)

theorem cubeInwardMateCertifiedFirstStretchedSources_nodup
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 <= K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateCertifiedFirstStretchedSources
      K physical hK hbounded).Nodup :=
  sumInrValues_nodup
    (cubeInwardMateCertifiedSourceOutcomes_nodup
      K physical hK hbounded)

/-- The target and first-stretched lists are an exact cardinality partition
of the production cube-boundary source multiplicity. -/
theorem cubeInwardMateCertifiedBranches_length
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 <= K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateCertifiedTargetAssignments
        K physical hK hbounded).length +
      (cubeInwardMateCertifiedFirstStretchedSources
        K physical hK hbounded).length =
      cubeInwardMateSourceBoundaryProduct K physical := by
  exact (sumInlValues_length_add_sumInrValues_length
    (cubeInwardMateCertifiedSourceOutcomes
      K physical hK hbounded)).trans
    (cubeInwardMateCertifiedSourceOutcomes_length
      K physical hK hbounded)

#print axioms dependentFiniteAssignments_length
#print axioms DependentFiniteAssignment.eq_of_get_eq
#print axioms dependentFiniteAssignments_nodup
#print axioms cubeInwardMateOrderedSourceWitnesses_length
#print axioms cubeInwardMateOrderedSourceAssignments_nodup
#print axioms cubeInwardMateOrderedSourceAssignments_length
#print axioms cubeInwardMateCertifiedSourceOutcomes_length
#print axioms cubeInwardMateCertifiedSourceOutcomes_nodup
#print axioms mem_sumInrValues_iff
#print axioms sumInrValues_nodup
#print axioms sumInlValues_length_add_sumInrValues_length
#print axioms cubeInwardMateCertifiedFirstStretchedSources_nodup
#print axioms cubeInwardMateCertifiedBranches_length

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceEnumeration
