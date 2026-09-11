/-
# Retain source acceptance through the cube classification

The raw target-or-debt output determines the source auxiliary by the exact
local decoder, but an arbitrary value of that sum need not lie in the image of
the source classifier.  For component peeling we must retain the missing image
invariant: the decoded auxiliary is accepted on the literal root-first source
word.

This file packages that invariant at one link and over the dependent twelve-
link product.  The actual classifier inhabits the package, its certified
decoder is a left inverse, and every certified classified assignment produces
a common accepted presented source family on the cube.  A source-level global
dichotomy then retains this certified family precisely on the first-stretched
branch while preserving the earlier injectivity proof.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. One classified link retaining its source-image certificate -/

structure CubeInwardMateCertifiedClassifiedWitness
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) : Type where
  classified : Sum
    (CubeInwardMateOrderedTargetWitness K physical linked)
    (CubeInwardMateStretchedWitnessDebt
      K physical hK hbounded linked)
  recovered_mem :
    recoverCubeInwardMateSourceWitnessPartitionAt
        K physical hK hbounded linked classified ∈
      orderedSlabLinkFusionWitnesses K physical
        (cubeInwardMateSourceFaceOrder linked)

/-- The actual local source classifier lands in the certified image. -/
def cubeInwardMateCertifiedClassifiedWitness
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember)
    (source : CubeInwardMateOrderedSourceWitness K physical linked) :
    CubeInwardMateCertifiedClassifiedWitness
      K physical hK hbounded linked where
  classified := cubeInwardMateSourceWitnessPartition
    K physical hK hbounded linked source
  recovered_mem := by
    rw [recoverCubeInwardMateSourceWitnessPartitionAt_apply]
    exact source.2

/-- Decode a certified classified output back into the accepted ordered source
fiber. -/
def recoverCubeInwardMateCertifiedClassifiedWitness
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember)
    (certified : CubeInwardMateCertifiedClassifiedWitness
      K physical hK hbounded linked) :
    CubeInwardMateOrderedSourceWitness K physical linked :=
  ⟨recoverCubeInwardMateSourceWitnessPartitionAt
      K physical hK hbounded linked certified.classified,
    certified.recovered_mem⟩

theorem recoverCubeInwardMateCertifiedClassifiedWitness_apply
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember)
    (source : CubeInwardMateOrderedSourceWitness K physical linked) :
    recoverCubeInwardMateCertifiedClassifiedWitness
        K physical hK hbounded linked
        (cubeInwardMateCertifiedClassifiedWitness
          K physical hK hbounded linked source) = source := by
  apply Subtype.ext
  exact recoverCubeInwardMateSourceWitnessPartitionAt_apply
    K physical hK hbounded linked source

theorem cubeInwardMateCertifiedClassifiedWitness_injective
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) :
    Function.Injective
      (cubeInwardMateCertifiedClassifiedWitness
        K physical hK hbounded linked) := by
  intro source₁ source₂ heq
  calc
    source₁ = recoverCubeInwardMateCertifiedClassifiedWitness
        K physical hK hbounded linked
        (cubeInwardMateCertifiedClassifiedWitness
          K physical hK hbounded linked source₁) :=
      (recoverCubeInwardMateCertifiedClassifiedWitness_apply
        K physical hK hbounded linked source₁).symm
    _ = recoverCubeInwardMateCertifiedClassifiedWitness
        K physical hK hbounded linked
        (cubeInwardMateCertifiedClassifiedWitness
          K physical hK hbounded linked source₂) :=
      congrArg
        (recoverCubeInwardMateCertifiedClassifiedWitness
          K physical hK hbounded linked) heq
    _ = source₂ :=
      recoverCubeInwardMateCertifiedClassifiedWitness_apply
        K physical hK hbounded linked source₂

/-! ## 2. Dependent certified product and presented source family -/

abbrev CubeInwardMateCertifiedClassifiedAssignment
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :=
  (linked : CubeProductionIncidenceMember) →
    CubeInwardMateCertifiedClassifiedWitness
      K physical hK hbounded linked

def cubeInwardMateCertifiedClassifiedAssignment
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (source : CubeInwardMateOrderedSourceWitnessAssignment K physical) :
    CubeInwardMateCertifiedClassifiedAssignment
      K physical hK hbounded :=
  fun linked => cubeInwardMateCertifiedClassifiedWitness
    K physical hK hbounded linked (source linked)

def recoverCubeInwardMateCertifiedClassifiedAssignment
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (certified : CubeInwardMateCertifiedClassifiedAssignment
      K physical hK hbounded) :
    CubeInwardMateOrderedSourceWitnessAssignment K physical :=
  fun linked => recoverCubeInwardMateCertifiedClassifiedWitness
    K physical hK hbounded linked (certified linked)

theorem recoverCubeInwardMateCertifiedClassifiedAssignment_apply
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (source : CubeInwardMateOrderedSourceWitnessAssignment K physical) :
    recoverCubeInwardMateCertifiedClassifiedAssignment
        K physical hK hbounded
        (cubeInwardMateCertifiedClassifiedAssignment
          K physical hK hbounded source) = source := by
  funext linked
  exact recoverCubeInwardMateCertifiedClassifiedWitness_apply
    K physical hK hbounded linked (source linked)

/-- Forget only the source-image certificates. -/
def forgetCubeInwardMateCertifiedClassifiedAssignment
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (certified : CubeInwardMateCertifiedClassifiedAssignment
      K physical hK hbounded) :
    CubeInwardMateClassifiedWitnessAssignment
      K physical hK hbounded :=
  fun linked => (certified linked).classified

theorem forget_certifiedClassifiedAssignment_eq_partition
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (source : CubeInwardMateOrderedSourceWitnessAssignment K physical) :
    forgetCubeInwardMateCertifiedClassifiedAssignment
        K physical hK hbounded
        (cubeInwardMateCertifiedClassifiedAssignment
          K physical hK hbounded source) =
      cubeInwardMateSourceAssignmentPartition
        K physical hK hbounded source := by
  rfl

/-- Every certified classified product determines the accepted source
presentation from which it came, on all twelve cube incidences. -/
def cubeInwardMatePresentedSourceAssignmentOfCertified
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (certified : CubeInwardMateCertifiedClassifiedAssignment
      K physical hK hbounded) :
    CubeInwardMatePresentedSourceAssignment K physical :=
  cubeInwardMatePresentedSourceAssignment K physical
    (recoverCubeInwardMateCertifiedClassifiedAssignment
      K physical hK hbounded certified)

/-! ## 3. A source dichotomy whose stretched branch retains certification -/

structure CubeInwardMateCertifiedFirstStretchedSource
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) : Type where
  certified : CubeInwardMateCertifiedClassifiedAssignment
    K physical hK hbounded
  root : CubeInwardMateStretchedRoot K physical hK hbounded
  root_eq : firstCubeInwardMateStretched?
    K physical hK hbounded
    (forgetCubeInwardMateCertifiedClassifiedAssignment
      K physical hK hbounded certified)
    cubeProductionIncidences.attach = some root

/-- The root is a literal member of the attached twelve-incidence list and its
debt is exactly the forgotten classified output at that coordinate. -/
theorem CubeInwardMateCertifiedFirstStretchedSource.root_parts
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded) :
    stretched.root.1 ∈ cubeProductionIncidences.attach ∧
      forgetCubeInwardMateCertifiedClassifiedAssignment
          K physical hK hbounded stretched.certified stretched.root.1 =
        Sum.inr stretched.root.2 :=
  firstCubeInwardMateStretched_eq_some_parts
    K physical hK hbounded
    (forgetCubeInwardMateCertifiedClassifiedAssignment
      K physical hK hbounded stretched.certified)
    cubeProductionIncidences.attach stretched.root stretched.root_eq

def cubeInwardMateCertifiedSourceTargetOrFirstStretched
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    CubeInwardMateOrderedSourceWitnessAssignment K physical →
    Sum
      (CubeInwardMateOrderedTargetWitnessAssignment K physical)
      (CubeInwardMateCertifiedFirstStretchedSource
        K physical hK hbounded) :=
  fun source =>
    let certified := cubeInwardMateCertifiedClassifiedAssignment
      K physical hK hbounded source
    let classified := forgetCubeInwardMateCertifiedClassifiedAssignment
      K physical hK hbounded certified
    match hfirst : firstCubeInwardMateStretched?
        K physical hK hbounded classified
          cubeProductionIncidences.attach with
    | none => Sum.inl
        (cubeInwardMateTargetAssignmentOfFirstStretchedEqNone
          K physical hK hbounded classified hfirst)
    | some root => Sum.inr
        { certified := certified
          root := root
          root_eq := hfirst }

/-- Forget the strengthened branch back to the complete raw classified
assignment. -/
def unsplitCubeInwardMateCertifiedSource
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    Sum
      (CubeInwardMateOrderedTargetWitnessAssignment K physical)
      (CubeInwardMateCertifiedFirstStretchedSource
        K physical hK hbounded) →
    CubeInwardMateClassifiedWitnessAssignment
      K physical hK hbounded
  | Sum.inl target => cubeInwardMateClassifiedAssignmentOfTarget
      K physical hK hbounded target
  | Sum.inr stretched =>
      forgetCubeInwardMateCertifiedClassifiedAssignment
        K physical hK hbounded stretched.certified

theorem unsplit_certifiedSourceTargetOrFirstStretched
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (source : CubeInwardMateOrderedSourceWitnessAssignment K physical) :
    unsplitCubeInwardMateCertifiedSource
        K physical hK hbounded
        (cubeInwardMateCertifiedSourceTargetOrFirstStretched
          K physical hK hbounded source) =
      cubeInwardMateSourceAssignmentPartition
        K physical hK hbounded source := by
  unfold cubeInwardMateCertifiedSourceTargetOrFirstStretched
  dsimp only
  split
  · change cubeInwardMateClassifiedAssignmentOfTarget
        K physical hK hbounded
        (cubeInwardMateTargetAssignmentOfFirstStretchedEqNone
          K physical hK hbounded
          (forgetCubeInwardMateCertifiedClassifiedAssignment
            K physical hK hbounded
            (cubeInwardMateCertifiedClassifiedAssignment
              K physical hK hbounded source)) ‹_›) = _
    rw [classifiedAssignmentOfTarget_of_firstStretchedEqNone]
    exact forget_certifiedClassifiedAssignment_eq_partition
      K physical hK hbounded source
  · rfl

theorem cubeInwardMateCertifiedSourceTargetOrFirstStretched_injective
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    Function.Injective
      (cubeInwardMateCertifiedSourceTargetOrFirstStretched
        K physical hK hbounded) := by
  intro source₁ source₂ heq
  apply cubeInwardMateSourceAssignmentPartition_injective
    K physical hK hbounded
  calc
    cubeInwardMateSourceAssignmentPartition
        K physical hK hbounded source₁ =
      unsplitCubeInwardMateCertifiedSource
        K physical hK hbounded
        (cubeInwardMateCertifiedSourceTargetOrFirstStretched
          K physical hK hbounded source₁) :=
      (unsplit_certifiedSourceTargetOrFirstStretched
        K physical hK hbounded source₁).symm
    _ = unsplitCubeInwardMateCertifiedSource
        K physical hK hbounded
        (cubeInwardMateCertifiedSourceTargetOrFirstStretched
          K physical hK hbounded source₂) :=
      congrArg
        (unsplitCubeInwardMateCertifiedSource
          K physical hK hbounded) heq
    _ = cubeInwardMateSourceAssignmentPartition
        K physical hK hbounded source₂ :=
      unsplit_certifiedSourceTargetOrFirstStretched
        K physical hK hbounded source₂

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification.cubeInwardMateCertifiedClassifiedWitness
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification.recoverCubeInwardMateCertifiedClassifiedWitness_apply
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification.recoverCubeInwardMateCertifiedClassifiedAssignment_apply
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification.cubeInwardMatePresentedSourceAssignmentOfCertified
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification.CubeInwardMateCertifiedFirstStretchedSource.root_parts
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification.unsplit_certifiedSourceTargetOrFirstStretched
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification.cubeInwardMateCertifiedSourceTargetOrFirstStretched_injective
