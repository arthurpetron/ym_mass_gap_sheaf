/-
# Recover a global inward-mate source from target atom and six-bit code

The six-bit physical ambiguity code is useful only if the remaining source
data can be read back from the realized target atom.  This module proves that
recovery directly.  On each of the twelve cube links the target presentation
stores the classified target auxiliary itself; on the off-cube complement it
stores the original Cartesian auxiliary.  The standard reconstruction from
all duplicate-free link lookups then recovers the complete off-cube list.

Consequently the realized target atom together with the six-bit code is
injective on all global successful sources.  This is not yet the cardinality
bound on a filtered target fiber, summed weight transport, posterior variance,
OS form bound, spectral gap, or continuum estimate.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPreimageCode
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeight
import YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPreimageInjectivity

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceOffCubeCompletion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPreimageCode
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchCardinality
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Raw equality exposes every target auxiliary -/

private theorem listMap_functions_eq_on_mem
    {A B : Type} (items : List A) (left right : A → B)
    (hmap : items.map left = items.map right) :
    ∀ item, item ∈ items → left item = right item := by
  induction items with
  | nil =>
      intro item hitem
      exact False.elim (List.not_mem_nil hitem)
  | cons head tail ih =>
      simp only [List.map_cons] at hmap
      have hhead : left head = right head := by
        injection hmap
      have htail : tail.map left = tail.map right := by
        injection hmap
      intro item hitem
      rcases List.mem_cons.mp hitem with heq | htailMem
      · exact heq ▸ hhead
      · exact ih htail item htailMem

/-- Equality of complete raw targets implies equality of their presented
auxiliary at every displayed slab link. -/
theorem globalTargetRaw_auxiliary_eq_of_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hraw :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw right)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1}) :
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
        left linked).auxiliary =
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
        right linked).auxiliary := by
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw at hraw
  have hentry := listMap_functions_eq_on_mem
    (boundaryCompleteSlabLinks 1).attach
    (fun item =>
      (item.1,
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
          left item).auxiliary))
    (fun item =>
      (item.1,
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
          right item).auxiliary))
    hraw linked (List.mem_attach (boundaryCompleteSlabLinks 1) linked)
  exact congrArg Prod.snd hentry

/-! ## 2. Fixed-physical target raw data recovers the complete entry -/

/-- Once the source physical field is fixed, equality of complete target raw
assignments recovers both the twelve cube target witnesses and every off-cube
production auxiliary. -/
theorem targetEntry_eq_of_targetRaw_eq
    (K : Nat) (hK : 1 ≤ K)
    (physicalSource : CubeInwardMatePhysicalSource K)
    (left right : CubeInwardMateCertifiedTargetFullSource
      K physicalSource.1)
    (hraw :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw
          ({ physicalSource := physicalSource
             entry := left } :
            GlobalCubeInwardMateCertifiedTargetFullSource K hK) =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw
          ({ physicalSource := physicalSource
             entry := right } :
            GlobalCubeInwardMateCertifiedTargetFullSource K hK)) :
    left = right := by
  let leftSource : GlobalCubeInwardMateCertifiedTargetFullSource K hK :=
    { physicalSource := physicalSource
      entry := left }
  let rightSource : GlobalCubeInwardMateCertifiedTargetFullSource K hK :=
    { physicalSource := physicalSource
      entry := right }
  have hraw' :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw leftSource =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw rightSource :=
    hraw
  have hcube : left.1 = right.1 := by
    funext linked
    apply Subtype.ext
    have haux :=
      globalTargetRaw_auxiliary_eq_of_eq
        leftSource rightSource hraw'
        (cubeProductionIncidenceSlabLink linked)
    calc
      (left.1 linked).1 =
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
            leftSource
            (cubeProductionIncidenceSlabLink linked)).auxiliary := by
        rw [GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented_at_cube]
        rfl
      _ = (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
            rightSource
            (cubeProductionIncidenceSlabLink linked)).auxiliary := haux
      _ = (right.1 linked).1 := by
        rw [GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented_at_cube]
        rfl
  have hoffLookup : ∀ link,
      link ∈ cubeInwardMateOffCubeSlabLinks →
      slabFusionWitnessAssignmentAt link left.2.1 =
        slabFusionWitnessAssignmentAt link right.2.1 := by
    intro link hlink
    let linked : {link // link ∈ cubeInwardMateOffCubeSlabLinks} :=
      ⟨link, hlink⟩
    let complete := cubeInwardMateOffCubeSlabLinkToComplete linked
    have hnot : link ∉ coarseCubeBoundaryLinks :=
      (mem_cubeInwardMateOffCubeSlabLinks_iff link).mp hlink |>.2
    have haux :=
      globalTargetRaw_auxiliary_eq_of_eq
        leftSource rightSource hraw' complete
    calc
      slabFusionWitnessAssignmentAt link left.2.1 =
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
            leftSource complete).auxiliary :=
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented_at_not_cube
          leftSource complete hnot).symm
      _ = (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
            rightSource complete).auxiliary := haux
      _ = slabFusionWitnessAssignmentAt link right.2.1 :=
        GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented_at_not_cube
          rightSource complete hnot
  have hoffAssignment : left.2.1 = right.2.1 := by
    calc
      left.2.1 = slabFusionWitnessAssignmentFrom
          cubeInwardMateOffCubeSlabLinks
          (fun link => slabFusionWitnessAssignmentAt link left.2.1) :=
        (slabFusionWitnessAssignmentFrom_at_eq
          K 1 physicalSource.1 cubeInwardMateOffCubeSlabLinks left.2.1
          ((boundaryCompleteSlabLinks_nodup 1).filter _)
          left.2.2).symm
      _ = slabFusionWitnessAssignmentFrom
          cubeInwardMateOffCubeSlabLinks
          (fun link => slabFusionWitnessAssignmentAt link right.2.1) := by
        unfold slabFusionWitnessAssignmentFrom
        apply List.map_congr_left
        intro link hlink
        exact congrArg (fun auxiliary => (link, auxiliary))
          (hoffLookup link hlink)
      _ = right.2.1 :=
        slabFusionWitnessAssignmentFrom_at_eq
          K 1 physicalSource.1 cubeInwardMateOffCubeSlabLinks right.2.1
          ((boundaryCompleteSlabLinks_nodup 1).filter _)
          right.2.2
  apply Prod.ext
  · exact hcube
  · exact Subtype.ext hoffAssignment

/-! ## 3. Target atom and six-bit code recover the global source -/

private theorem prod_fst_eq_of_eq
    {A B : Type} {leftA rightA : A} {leftB rightB : B}
    (hpair : (leftA, leftB) = (rightA, rightB)) :
    leftA = rightA := by
  injection hpair

private theorem prod_snd_eq_of_eq
    {A B : Type} {leftA rightA : A} {leftB rightB : B}
    (hpair : (leftA, leftB) = (rightA, rightB)) :
    leftB = rightB := by
  injection hpair

theorem globalTargetAtom_eq
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom source =
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source,
        GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw source) := by
  rfl

/-- Equality of source physical fields and target raw assignments recovers the
dependent global source. -/
theorem globalTargetSource_eq_of_physical_eq_of_targetRaw_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hphysical : left.physical = right.physical)
    (hraw :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw right) :
    left = right := by
  have hphysicalSource : left.physicalSource = right.physicalSource :=
    Subtype.ext hphysical
  cases left with
  | mk leftPhysicalSource leftEntry =>
      cases right with
      | mk rightPhysicalSource rightEntry =>
          dsimp only at hphysicalSource
          cases hphysicalSource
          have hentry : leftEntry = rightEntry :=
            targetEntry_eq_of_targetRaw_eq
              K hK leftPhysicalSource leftEntry rightEntry hraw
          cases hentry
          rfl

/-- **Full preimage injectivity.**  A realized target atom and its six-bit
zero/nonzero code uniquely determine the complete successful global source. -/
theorem globalTargetSource_eq_of_targetAtom_eq_of_targetPreimageCode_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hatom :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom right)
    (hcode :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode right) :
    left = right := by
  have hpair :
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left,
          GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw left) =
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right,
          GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw right) := by
    calc
      _ = GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom left :=
        (globalTargetAtom_eq left).symm
      _ = GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom right :=
        hatom
      _ = _ := globalTargetAtom_eq right
  have htargetPhysical :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right := by
    exact prod_fst_eq_of_eq hpair
  have hphysical :=
    GlobalCubeInwardMateCertifiedTargetFullSource.physical_eq_of_targetPhysical_eq_of_targetPreimageCode_eq
      left right htargetPhysical hcode
  have htargetRaw :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw right := by
    exact prod_snd_eq_of_eq hpair
  exact
    globalTargetSource_eq_of_physical_eq_of_targetRaw_eq
      left right hphysical htargetRaw

#print axioms globalTargetRaw_auxiliary_eq_of_eq
#print axioms targetEntry_eq_of_targetRaw_eq
#print axioms globalTargetAtom_eq
#print axioms globalTargetSource_eq_of_physical_eq_of_targetRaw_eq
#print axioms globalTargetSource_eq_of_targetAtom_eq_of_targetPreimageCode_eq

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPreimageInjectivity
