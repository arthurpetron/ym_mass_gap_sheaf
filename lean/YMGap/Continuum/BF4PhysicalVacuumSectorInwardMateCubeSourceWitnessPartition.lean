/-
# Specialize the inward-mate witness partition to a literal cube link

The abstract SU(2) partition acts on an ordered word
`left :: right :: rest`.  A corrected-slab cube-boundary link instead begins
with a production incidence list of literal plaquette identifiers.  This file
joins those two descriptions without identifying witnesses across a bare
permutation of external spins.

For every one of the twelve recorded cube incidences, the two incident cube
faces are moved to the first two literal positions.  The same face order maps
the source labelling to `left :: right :: rest` and the global six-face mate
to `mate left :: mate right :: rest`.  The abstract injective partition can
therefore be applied to the actual ordered link fiber.  Its surviving branch
is packaged as a presented mated-link witness; its stretched branch retains
the accepted collapsed witness and both positivity certificates.

This is one local compiler.  The dependent product over all twelve links and
the common presented source assignment remain separate obligations.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder
import YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
import YMGap.Continuum.SU2InwardMateFusionWitnessPartition

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateIncidentOrder
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2InwardMateFusionWitnessPartition
open YMGap.Continuum.SU2StretchedFusionWitnessLift
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. One literal root-first face order at every cube link -/

/-- The root-first literal face order attached to any of the twelve recorded
cube-boundary incidences. -/
def cubeInwardMateSourceFaceOrder
    (linked : CubeProductionIncidenceMember) :
    SlabLinkFaceOrder 1 linked.1.link where
  faceIds :=
    centralLowerCubeFaceId linked.1.left ::
      centralLowerCubeFaceId linked.1.right ::
        cubeInwardMateLinkRestFaceIds linked
  production_perm := (cubeInwardMateLinkFaceOrderCertificate linked).2

@[simp] theorem cubeInwardMateSourceFaceOrder_faceIds
    (linked : CubeProductionIncidenceMember) :
    (cubeInwardMateSourceFaceOrder linked).faceIds =
      centralLowerCubeFaceId linked.1.left ::
        centralLowerCubeFaceId linked.1.right ::
          cubeInwardMateLinkRestFaceIds linked :=
  rfl

/-- The residual literal faces contain none of the other four selected cube
faces, so the global mate is pointwise the identity on that residual list. -/
theorem cubeInwardMateLinkRestFaceIds_map_mate_eq_source
    (physical : EdgeLabelling)
    (linked : CubeProductionIncidenceMember) :
    (cubeInwardMateLinkRestFaceIds linked).map
        (centralLowerCubeEvenInwardMatePhysical physical) =
      (cubeInwardMateLinkRestFaceIds linked).map physical := by
  have hgeometry := cubeProductionIncidence_numeric_exact linked.2
  have hids := (cubeInwardMateLinkFaceOrderCertificate linked).2
  have hexcludes := two_head_perm_rest_excludes
    (slabIncidentPlaqIds_nodup 1 linked.1.link) hids
  apply List.map_congr_left
  intro faceId hface
  apply centralLowerCubeEvenInwardMatePhysical_off_cube
  intro hselected
  have hpair := hgeometry.2.2.2 faceId
    (hids.mem_iff.mpr (by
      simp only [List.mem_cons]
      exact Or.inr (Or.inr hface))) hselected
  rcases hpair with hleft | hright
  · exact hexcludes.1 (hleft ▸ hface)
  · exact hexcludes.2 (hright ▸ hface)

theorem cubeInwardMateSourceFaceOrder_map_source
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) :
    (cubeInwardMateSourceFaceOrder linked).faceIds.map physical =
      physical (centralLowerCubeFaceId linked.1.left) ::
        physical (centralLowerCubeFaceId linked.1.right) ::
          cubeInwardMateLinkRest K physical hK hbounded linked := by
  simp [cubeInwardMateSourceFaceOrder,
    cubeInwardMateLinkRest_eq_map_restFaceIds]

theorem cubeInwardMateSourceFaceOrder_map_mate
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) :
    (cubeInwardMateSourceFaceOrder linked).faceIds.map
        (centralLowerCubeEvenInwardMatePhysical physical) =
      evenInwardMateLabel
          (physical (centralLowerCubeFaceId linked.1.left)) ::
        evenInwardMateLabel
            (physical (centralLowerCubeFaceId linked.1.right)) ::
          cubeInwardMateLinkRest K physical hK hbounded linked := by
  simp [cubeInwardMateSourceFaceOrder,
    centralLowerCubeEvenInwardMatePhysical_on_cube,
    centralLowerCubeFaceId_mem,
    cubeInwardMateLinkRest_eq_map_restFaceIds,
    cubeInwardMateLinkRestFaceIds_map_mate_eq_source]

/-- Every root-first cube-link word lies inside the proved valence-six range
of the abstract witness partition. -/
theorem cubeInwardMateOrderedSourceSpins_length_le_six
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) :
    (physical (centralLowerCubeFaceId linked.1.left) ::
      physical (centralLowerCubeFaceId linked.1.right) ::
        cubeInwardMateLinkRest K physical hK hbounded linked).length ≤ 6 := by
  rw [← cubeInwardMateSourceFaceOrder_map_source
    K physical hK hbounded linked, List.length_map]
  exact (cubeInwardMateSourceFaceOrder linked).length_le_six

/-! ## 2. The physical-link source partition -/

abbrev CubeInwardMateOrderedSourceWitness
    (K : Nat) (physical : EdgeLabelling)
    (linked : CubeProductionIncidenceMember) :=
  { auxiliary : EdgeLabelling //
    auxiliary ∈ orderedSlabLinkFusionWitnesses K physical
      (cubeInwardMateSourceFaceOrder linked) }

abbrev CubeInwardMateOrderedTargetWitness
    (K : Nat) (physical : EdgeLabelling)
    (linked : CubeProductionIncidenceMember) :=
  { auxiliary : EdgeLabelling //
    auxiliary ∈ orderedSlabLinkFusionWitnesses K
      (centralLowerCubeEvenInwardMatePhysical physical)
      (cubeInwardMateSourceFaceOrder linked) }

abbrev CubeInwardMateStretchedWitnessDebt
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) :=
  InwardMateStretchedFusionWitnessDebt
    (linkAuxiliaryCutoff K)
    (physical (centralLowerCubeFaceId linked.1.left))
    (physical (centralLowerCubeFaceId linked.1.right))
    (cubeInwardMateLinkRest K physical hK hbounded linked)

/-- Reinterpret an ordered physical source witness in the exact root-first
spin word consumed by the abstract SU(2) partition. -/
def exactCubeInwardMateSourceWitness
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember)
    (source : CubeInwardMateOrderedSourceWitness K physical linked) :
    { auxiliary : EdgeLabelling //
      auxiliary ∈ fusionWitnessesForSpins (linkAuxiliaryCutoff K)
        (physical (centralLowerCubeFaceId linked.1.left) ::
          physical (centralLowerCubeFaceId linked.1.right) ::
            cubeInwardMateLinkRest K physical hK hbounded linked) } :=
  ⟨source.1, by
    simpa [orderedSlabLinkFusionWitnesses,
      cubeInwardMateSourceFaceOrder_map_source] using source.2⟩

/-- Repackage the abstract classified output in the literal ordered target
fiber.  No auxiliary coordinate is changed by this operation. -/
def packageCubeInwardMateClassifiedWitness
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) :
    Sum
      { auxiliary : EdgeLabelling //
        auxiliary ∈ fusionWitnessesForSpins (linkAuxiliaryCutoff K)
          (evenInwardMateLabel
              (physical (centralLowerCubeFaceId linked.1.left)) ::
            evenInwardMateLabel
                (physical (centralLowerCubeFaceId linked.1.right)) ::
              cubeInwardMateLinkRest K physical hK hbounded linked) }
      (CubeInwardMateStretchedWitnessDebt
        K physical hK hbounded linked) →
    Sum
      (CubeInwardMateOrderedTargetWitness K physical linked)
      (CubeInwardMateStretchedWitnessDebt
        K physical hK hbounded linked)
  | Sum.inl target => Sum.inl ⟨target.1, by
      change target.1 ∈ fusionWitnessesForSpins (linkAuxiliaryCutoff K)
        ((cubeInwardMateSourceFaceOrder linked).faceIds.map
          (centralLowerCubeEvenInwardMatePhysical physical))
      rw [cubeInwardMateSourceFaceOrder_map_mate
        K physical hK hbounded linked]
      exact target.2⟩
  | Sum.inr debt => Sum.inr debt

/-- **Literal-link witness partition.**  Classify an accepted witness in the
actual root-first presentation of one cube-boundary link. -/
def cubeInwardMateSourceWitnessPartition
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember)
    (source : CubeInwardMateOrderedSourceWitness K physical linked) :
    Sum
      (CubeInwardMateOrderedTargetWitness K physical linked)
      (CubeInwardMateStretchedWitnessDebt
        K physical hK hbounded linked) :=
  packageCubeInwardMateClassifiedWitness
    K physical hK hbounded linked
    (inwardMateFusionWitnessPartition
      (linkAuxiliaryCutoff K)
      (physical (centralLowerCubeFaceId linked.1.left))
      (physical (centralLowerCubeFaceId linked.1.right))
      (cubeInwardMateLinkRest K physical hK hbounded linked)
    (cubeInwardMateOrderedSourceSpins_length_le_six
      K physical hK hbounded linked)
      (exactCubeInwardMateSourceWitness
        K physical hK hbounded linked source))

/-- Forget the fixed target order only after membership has been established;
the resulting witness is accepted in a literal presented mated-link fiber. -/
def presentedMatedLinkWitnessOfCubeInwardMateTarget
    (K : Nat) (physical : EdgeLabelling)
    (linked : CubeProductionIncidenceMember)
    (target : CubeInwardMateOrderedTargetWitness K physical linked) :
    PresentedSlabLinkFusionWitness K 1
      (centralLowerCubeEvenInwardMatePhysical physical) linked.1.link where
  order := cubeInwardMateSourceFaceOrder linked
  auxiliary := target.1
  auxiliary_mem := target.2

/-! ## 3. Exact recovery and injectivity -/

def recoverCubeInwardMateSourceWitnessPartitionAt
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) :
    Sum
      (CubeInwardMateOrderedTargetWitness K physical linked)
      (CubeInwardMateStretchedWitnessDebt
        K physical hK hbounded linked) → EdgeLabelling
  | Sum.inl target => target.1
  | Sum.inr debt =>
      stretchedFusionWitnessLift
        (physical (centralLowerCubeFaceId linked.1.left))
        (physical (centralLowerCubeFaceId linked.1.right))
        (cubeInwardMateLinkRest K physical hK hbounded linked)
        debt.collapsed

theorem recoverCubeInwardMatePackage_eq_recoverAbstract
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember)
    (classified :
      Sum
        { auxiliary : EdgeLabelling //
          auxiliary ∈ fusionWitnessesForSpins (linkAuxiliaryCutoff K)
            (evenInwardMateLabel
                (physical (centralLowerCubeFaceId linked.1.left)) ::
              evenInwardMateLabel
                  (physical (centralLowerCubeFaceId linked.1.right)) ::
                cubeInwardMateLinkRest K physical hK hbounded linked) }
        (CubeInwardMateStretchedWitnessDebt
          K physical hK hbounded linked)) :
    recoverCubeInwardMateSourceWitnessPartitionAt
        K physical hK hbounded linked
        (packageCubeInwardMateClassifiedWitness
          K physical hK hbounded linked classified) =
      recoverInwardMateFusionWitnessPartitionAt
        (linkAuxiliaryCutoff K)
        (physical (centralLowerCubeFaceId linked.1.left))
        (physical (centralLowerCubeFaceId linked.1.right))
        (cubeInwardMateLinkRest K physical hK hbounded linked)
        classified := by
  cases classified <;> rfl

theorem recoverCubeInwardMateSourceWitnessPartitionAt_apply
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember)
    (source : CubeInwardMateOrderedSourceWitness K physical linked) :
    recoverCubeInwardMateSourceWitnessPartitionAt
        K physical hK hbounded linked
        (cubeInwardMateSourceWitnessPartition
          K physical hK hbounded linked source) = source.1 := by
  rw [cubeInwardMateSourceWitnessPartition,
    recoverCubeInwardMatePackage_eq_recoverAbstract]
  exact recoverInwardMateFusionWitnessPartitionAt_apply
    (linkAuxiliaryCutoff K)
    (physical (centralLowerCubeFaceId linked.1.left))
    (physical (centralLowerCubeFaceId linked.1.right))
    (cubeInwardMateLinkRest K physical hK hbounded linked)
    (cubeInwardMateOrderedSourceSpins_length_le_six
      K physical hK hbounded linked)
    (exactCubeInwardMateSourceWitness
      K physical hK hbounded linked source)

/-- **Multiplicity-faithful physical-link compiler.**  The literal
cube-incidence specialization remains injective. -/
theorem cubeInwardMateSourceWitnessPartition_injective
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (linked : CubeProductionIncidenceMember) :
    Function.Injective
      (cubeInwardMateSourceWitnessPartition
        K physical hK hbounded linked) := by
  intro source₁ source₂ heq
  apply Subtype.ext
  calc
    source₁.1 = recoverCubeInwardMateSourceWitnessPartitionAt
        K physical hK hbounded linked
        (cubeInwardMateSourceWitnessPartition
          K physical hK hbounded linked source₁) :=
      (recoverCubeInwardMateSourceWitnessPartitionAt_apply
        K physical hK hbounded linked source₁).symm
    _ = recoverCubeInwardMateSourceWitnessPartitionAt
        K physical hK hbounded linked
        (cubeInwardMateSourceWitnessPartition
          K physical hK hbounded linked source₂) :=
      congrArg
        (recoverCubeInwardMateSourceWitnessPartitionAt
          K physical hK hbounded linked) heq
    _ = source₂.1 :=
      recoverCubeInwardMateSourceWitnessPartitionAt_apply
        K physical hK hbounded linked source₂

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition.cubeInwardMateSourceFaceOrder
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition.cubeInwardMateLinkRestFaceIds_map_mate_eq_source
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition.cubeInwardMateSourceFaceOrder_map_mate
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition.cubeInwardMateSourceWitnessPartition
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition.recoverCubeInwardMateSourceWitnessPartitionAt_apply
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition.cubeInwardMateSourceWitnessPartition_injective
