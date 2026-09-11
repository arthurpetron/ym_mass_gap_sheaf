/-
# Split a classified cube source at its first stretched link

The dependent twelve-link classifier has exactly two global outcomes.  If no
coordinate is stretched, every coordinate supplies an accepted mated witness.
Otherwise a structural scan of the attached incidence list returns the first
stretched incidence together with its actual dependent debt witness.

This file implements that dichotomy as data and proves it lossless.  Forgetting
the global branch reconstructs the entire pointwise classified assignment;
composing this identity with the already proved pointwise decoders makes the
source-to-global-branch compiler injective.

The first-stretched branch has the positive two-face root and collapsed
accepted witness needed by the component peel.  Converting its remaining
coordinates into the existing mixed carrier, completing the presented source
away from the cube, and paying the peel history remain downstream steps.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Structural first-stretched scan -/

/-- A literal incidence paired with a debt witness in its own dependent local
fiber. -/
abbrev CubeInwardMateStretchedRoot
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :=
  Σ' linked : CubeProductionIncidenceMember,
    CubeInwardMateStretchedWitnessDebt K physical hK hbounded linked

/-- Scan an incidence list from the left and return the first classified debt
coordinate, including its actual collapsed witness and positivity data. -/
def firstCubeInwardMateStretched?
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (classified : CubeInwardMateClassifiedWitnessAssignment
      K physical hK hbounded) :
    List CubeProductionIncidenceMember →
      Option (CubeInwardMateStretchedRoot K physical hK hbounded)
  | [] => none
  | linked :: rest =>
      match classified linked with
      | Sum.inl _ => firstCubeInwardMateStretched?
          K physical hK hbounded classified rest
      | Sum.inr debt => some ⟨linked, debt⟩

/-- A successful scan result is an actual member of the scanned list and its
stored debt is exactly the classified value at that coordinate. -/
theorem firstCubeInwardMateStretched_eq_some_parts
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (classified : CubeInwardMateClassifiedWitnessAssignment
      K physical hK hbounded) :
    ∀ (items : List CubeProductionIncidenceMember)
      (root : CubeInwardMateStretchedRoot K physical hK hbounded),
      firstCubeInwardMateStretched?
          K physical hK hbounded classified items = some root →
        root.1 ∈ items ∧ classified root.1 = Sum.inr root.2
  | [], _, hroot => by
      simp [firstCubeInwardMateStretched?] at hroot
  | head :: tail, root, hroot => by
      cases hhead : classified head with
      | inl target =>
          have hparts := firstCubeInwardMateStretched_eq_some_parts
            K physical hK hbounded classified tail root (by
              simpa [firstCubeInwardMateStretched?, hhead] using hroot)
          exact ⟨List.mem_cons_of_mem head hparts.1, hparts.2⟩
      | inr debt =>
          have heq :
              (⟨head, debt⟩ : CubeInwardMateStretchedRoot
                K physical hK hbounded) = root := by
            exact Option.some.inj (by
              simpa [firstCubeInwardMateStretched?, hhead] using hroot)
          subst root
          exact ⟨List.mem_cons_self, hhead⟩

theorem firstCubeInwardMateStretched_ne_none_of_mem_inr
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (classified : CubeInwardMateClassifiedWitnessAssignment
      K physical hK hbounded) :
    ∀ (items : List CubeProductionIncidenceMember)
      (linked : CubeProductionIncidenceMember),
      linked ∈ items →
      ∀ debt : CubeInwardMateStretchedWitnessDebt
        K physical hK hbounded linked,
        classified linked = Sum.inr debt →
        firstCubeInwardMateStretched?
          K physical hK hbounded classified items ≠ none
  | [], linked, hmem, _, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, linked, hmem, debt, hclassified => by
      have hparts := List.mem_cons.mp hmem
      rcases hparts with heq | htail
      · subst linked
        simp [firstCubeInwardMateStretched?, hclassified]
      · cases hhead : classified head with
        | inl target =>
            simpa [firstCubeInwardMateStretched?, hhead] using
              firstCubeInwardMateStretched_ne_none_of_mem_inr
                K physical hK hbounded classified tail linked htail
                  debt hclassified
        | inr headDebt =>
            simp [firstCubeInwardMateStretched?, hhead]

/-! ## 2. The no-debt branch is a complete target assignment -/

abbrev CubeInwardMateOrderedTargetWitnessAssignment
    (K : Nat) (physical : EdgeLabelling) :=
  (linked : CubeProductionIncidenceMember) →
    CubeInwardMateOrderedTargetWitness K physical linked

/-- Constructively project the left value of a sum once every possible right
constructor has been ruled out. -/
def sumLeftOfNotRight {A B : Type}
    (value : Sum A B) (hnot : ∀ right, value ≠ Sum.inr right) : A :=
  match value with
  | Sum.inl left => left
  | Sum.inr right => False.elim (hnot right rfl)

theorem sumInl_leftOfNotRight {A B : Type}
    (value : Sum A B) (hnot : ∀ right, value ≠ Sum.inr right) :
    Sum.inl (sumLeftOfNotRight value hnot) = value := by
  cases value with
  | inl left => rfl
  | inr right => exact False.elim (hnot right rfl)

/-- If the complete scan finds no stretched coordinate, each classified
coordinate can constructively be projected to its target witness. -/
def cubeInwardMateTargetAssignmentOfFirstStretchedEqNone
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (classified : CubeInwardMateClassifiedWitnessAssignment
      K physical hK hbounded)
    (hnone : firstCubeInwardMateStretched?
      K physical hK hbounded classified
        cubeProductionIncidences.attach = none) :
    CubeInwardMateOrderedTargetWitnessAssignment K physical :=
  fun linked =>
    sumLeftOfNotRight (classified linked) (fun debt hclassified =>
      (firstCubeInwardMateStretched_ne_none_of_mem_inr
          K physical hK hbounded classified
          cubeProductionIncidences.attach linked
          (List.mem_attach cubeProductionIncidences linked)
          debt hclassified) hnone)

/-- Embed an all-target family back into the complete classified product. -/
def cubeInwardMateClassifiedAssignmentOfTarget
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (target : CubeInwardMateOrderedTargetWitnessAssignment K physical) :
    CubeInwardMateClassifiedWitnessAssignment
      K physical hK hbounded :=
  fun linked => Sum.inl (target linked)

theorem classifiedAssignmentOfTarget_of_firstStretchedEqNone
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (classified : CubeInwardMateClassifiedWitnessAssignment
      K physical hK hbounded)
    (hnone : firstCubeInwardMateStretched?
      K physical hK hbounded classified
        cubeProductionIncidences.attach = none) :
    cubeInwardMateClassifiedAssignmentOfTarget
        K physical hK hbounded
        (cubeInwardMateTargetAssignmentOfFirstStretchedEqNone
          K physical hK hbounded classified hnone) =
      classified := by
  funext linked
  exact sumInl_leftOfNotRight (classified linked) (fun debt hclassified =>
    (firstCubeInwardMateStretched_ne_none_of_mem_inr
      K physical hK hbounded classified
      cubeProductionIncidences.attach linked
      (List.mem_attach cubeProductionIncidences linked)
      debt hclassified) hnone)

/-! ## 3. Lossless global dichotomy and source injectivity -/

/-- A nonempty classified output retaining both the complete classification
and its structurally first stretched coordinate. -/
structure CubeInwardMateFirstStretchedClassifiedAssignment
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) where
  classified : CubeInwardMateClassifiedWitnessAssignment
    K physical hK hbounded
  root : CubeInwardMateStretchedRoot K physical hK hbounded
  root_eq : firstCubeInwardMateStretched?
    K physical hK hbounded classified
      cubeProductionIncidences.attach = some root

/-- Split the complete dependent classification into all-target data or a
first-stretched rooted output. -/
def splitCubeInwardMateClassifiedAssignment
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (classified : CubeInwardMateClassifiedWitnessAssignment
      K physical hK hbounded) :
    Sum
      (CubeInwardMateOrderedTargetWitnessAssignment K physical)
      (CubeInwardMateFirstStretchedClassifiedAssignment
        K physical hK hbounded) :=
  match hfirst : firstCubeInwardMateStretched?
      K physical hK hbounded classified
        cubeProductionIncidences.attach with
  | none => Sum.inl
      (cubeInwardMateTargetAssignmentOfFirstStretchedEqNone
        K physical hK hbounded classified hfirst)
  | some root => Sum.inr
      { classified := classified
        root := root
        root_eq := hfirst }

/-- Forget the global branch and reconstruct its entire pointwise classified
assignment. -/
def unsplitCubeInwardMateClassifiedAssignment
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    Sum
      (CubeInwardMateOrderedTargetWitnessAssignment K physical)
      (CubeInwardMateFirstStretchedClassifiedAssignment
        K physical hK hbounded) →
    CubeInwardMateClassifiedWitnessAssignment
      K physical hK hbounded
  | Sum.inl target =>
      cubeInwardMateClassifiedAssignmentOfTarget
        K physical hK hbounded target
  | Sum.inr stretched => stretched.classified

theorem unsplit_splitCubeInwardMateClassifiedAssignment
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (classified : CubeInwardMateClassifiedWitnessAssignment
      K physical hK hbounded) :
    unsplitCubeInwardMateClassifiedAssignment
        K physical hK hbounded
        (splitCubeInwardMateClassifiedAssignment
          K physical hK hbounded classified) =
      classified := by
  unfold splitCubeInwardMateClassifiedAssignment
  split
  · exact classifiedAssignmentOfTarget_of_firstStretchedEqNone
      K physical hK hbounded classified ‹_›
  · rfl

/-- Classify a complete source and immediately expose its global all-target or
first-stretched outcome. -/
def cubeInwardMateSourceAssignmentTargetOrFirstStretched
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    CubeInwardMateOrderedSourceWitnessAssignment K physical →
    Sum
      (CubeInwardMateOrderedTargetWitnessAssignment K physical)
      (CubeInwardMateFirstStretchedClassifiedAssignment
        K physical hK hbounded) :=
  fun source => splitCubeInwardMateClassifiedAssignment
    K physical hK hbounded
    (cubeInwardMateSourceAssignmentPartition
      K physical hK hbounded source)

/-- **Lossless global source split.**  The all-target/first-stretched compiler
is injective on the complete dependent source assignment. -/
theorem cubeInwardMateSourceAssignmentTargetOrFirstStretched_injective
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    Function.Injective
      (cubeInwardMateSourceAssignmentTargetOrFirstStretched
        K physical hK hbounded) := by
  intro source₁ source₂ heq
  apply cubeInwardMateSourceAssignmentPartition_injective
    K physical hK hbounded
  calc
    cubeInwardMateSourceAssignmentPartition
        K physical hK hbounded source₁ =
      unsplitCubeInwardMateClassifiedAssignment
        K physical hK hbounded
        (cubeInwardMateSourceAssignmentTargetOrFirstStretched
          K physical hK hbounded source₁) :=
      (unsplit_splitCubeInwardMateClassifiedAssignment
        K physical hK hbounded
        (cubeInwardMateSourceAssignmentPartition
          K physical hK hbounded source₁)).symm
    _ = unsplitCubeInwardMateClassifiedAssignment
        K physical hK hbounded
        (cubeInwardMateSourceAssignmentTargetOrFirstStretched
          K physical hK hbounded source₂) :=
      congrArg
        (unsplitCubeInwardMateClassifiedAssignment
          K physical hK hbounded) heq
    _ = cubeInwardMateSourceAssignmentPartition
        K physical hK hbounded source₂ :=
      unsplit_splitCubeInwardMateClassifiedAssignment
        K physical hK hbounded
        (cubeInwardMateSourceAssignmentPartition
          K physical hK hbounded source₂)

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched.firstCubeInwardMateStretched?
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched.cubeInwardMateTargetAssignmentOfFirstStretchedEqNone
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched.classifiedAssignmentOfTarget_of_firstStretchedEqNone
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched.splitCubeInwardMateClassifiedAssignment
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched.unsplit_splitCubeInwardMateClassifiedAssignment
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched.cubeInwardMateSourceAssignmentTargetOrFirstStretched_injective
