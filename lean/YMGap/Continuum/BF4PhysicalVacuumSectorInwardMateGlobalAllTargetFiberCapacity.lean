/-
# Uniform capacity sixty-four for global inward-mate target fibers

The realized target atom contains function-valued physical and auxiliary
labellings, so it has no direct decidable equality.  We serialize exactly the
finite physical and auxiliary supports into a decidable key and prove that two
successful sources have equal keys exactly when they have equal target atoms.
The complete global successful-source carrier is duplicate-free.  Therefore
each exact target-atom fiber maps injectively to the exhaustive six-bit code
space and has cardinality at most `64`.

This closes target-column congestion for the global all-target event.  It does
not yet sum the pointwise source-to-target weight comparison, derive a
posterior-variance fraction, identify the OS transfer form, or assert a
spectral-gap or continuum estimate.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPreimageInjectivity
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey
import YMGap.Continuum.CayleyPruferInjection

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberCapacity

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPreimageCode
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPreimageInjectivity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchCardinality
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff

/-! ## 1. A finite decidable key exactly equivalent to target-atom equality -/

/-- The complete finite support of a realized global inward-mate target. -/
structure GlobalInwardMateTargetKey : Type where
  physicalWord : List Nat
  auxiliaryWords : List (List Nat)
  deriving DecidableEq

/-- An opaque coordinate package keeps dependent target presentations behind a
small projection boundary while exposing exact finite-word equations. -/
structure GlobalInwardMateTargetCoordinates
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Type where
  physicalWord : List Nat
  auxiliaryWords : List (List Nat)
  physicalWord_eq : physicalWord = finiteEdgeLabellingWord
    (slabPhysicalFaceEdges 1)
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source)
  auxiliaryWords_eq : auxiliaryWords =
    presentedSlabFusionWitnessAssignmentAuxiliaryWords
      (boundaryCompleteSlabLinks 1)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented source)

opaque globalInwardMateTargetCoordinates
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    GlobalInwardMateTargetCoordinates source :=
  { physicalWord := finiteEdgeLabellingWord
      (slabPhysicalFaceEdges 1)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source)
    auxiliaryWords := presentedSlabFusionWitnessAssignmentAuxiliaryWords
      (boundaryCompleteSlabLinks 1)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented source)
    physicalWord_eq := rfl
    auxiliaryWords_eq := rfl }

/-- The finite physical coordinate of the exact target key. -/
def globalInwardMateTargetPhysicalWord
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    List Nat :=
  (globalInwardMateTargetCoordinates source).physicalWord

/-- The finite auxiliary coordinate of the exact target key. -/
def globalInwardMateTargetAuxiliaryWords
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    List (List Nat) :=
  (globalInwardMateTargetCoordinates source).auxiliaryWords

theorem globalInwardMateTargetPhysicalWord_eq
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    globalInwardMateTargetPhysicalWord source = finiteEdgeLabellingWord
      (slabPhysicalFaceEdges 1)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source) :=
  (globalInwardMateTargetCoordinates source).physicalWord_eq

theorem globalInwardMateTargetAuxiliaryWords_eq
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    globalInwardMateTargetAuxiliaryWords source =
      presentedSlabFusionWitnessAssignmentAuxiliaryWords
        (boundaryCompleteSlabLinks 1)
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented source) :=
  (globalInwardMateTargetCoordinates source).auxiliaryWords_eq

/-- Serialize the realized target physical field and every displayed target
auxiliary on its canonical finite support. -/
def globalInwardMateTargetKey
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    GlobalInwardMateTargetKey where
  physicalWord := globalInwardMateTargetPhysicalWord source
  auxiliaryWords := globalInwardMateTargetAuxiliaryWords source

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

private theorem prod_eq_of_fields_eq
    {A B : Type} {leftA rightA : A} {leftB rightB : B}
    (hleft : leftA = rightA) (hright : leftB = rightB) :
    (leftA, leftB) = (rightA, rightB) := by
  cases hleft
  cases hright
  rfl

private theorem targetKey_eq_of_fields_eq
    (left right : GlobalInwardMateTargetKey)
    (hphysical : left.physicalWord = right.physicalWord)
    (hauxiliary : left.auxiliaryWords = right.auxiliaryWords) :
    left = right := by
  cases left with
  | mk leftPhysical leftAuxiliary =>
      cases right with
      | mk rightPhysical rightAuxiliary =>
          dsimp only at hphysical hauxiliary
          cases hphysical
          cases hauxiliary
          rfl

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

/-- Equality of every finite target-auxiliary word reconstructs equality of
the complete raw target lists. -/
theorem globalTargetRaw_eq_of_auxiliaryWords_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hwords :
      presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented left) =
        presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented right)) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw left =
      GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw right := by
  have hauxiliary : ∀ linked :
      {link // link ∈ boundaryCompleteSlabLinks 1},
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
          left linked).auxiliary =
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
          right linked).auxiliary := by
    intro linked
    let edges := canonicalUsedAuxiliaryCoordinates
      (slabIncidentPlaqIds 1 linked.1).length
    have hword : finiteEdgeLabellingWord edges
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
          left linked).auxiliary =
      finiteEdgeLabellingWord edges
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
          right linked).auxiliary := by
      unfold presentedSlabFusionWitnessAssignmentAuxiliaryWords at hwords
      exact listMap_functions_eq_on_mem
        (boundaryCompleteSlabLinks 1).attach
        (fun item => finiteEdgeLabellingWord
          (canonicalUsedAuxiliaryCoordinates
            (slabIncidentPlaqIds 1 item.1).length)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
            left item).auxiliary)
        (fun item => finiteEdgeLabellingWord
          (canonicalUsedAuxiliaryCoordinates
            (slabIncidentPlaqIds 1 item.1).length)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
            right item).auxiliary)
        hwords linked (List.mem_attach (boundaryCompleteSlabLinks 1) linked)
    have hleftMem :=
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
        left linked).auxiliary_mem
    have hrightMem :=
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
        right linked).auxiliary_mem
    unfold orderedSlabLinkFusionWitnesses fusionWitnessesForSpins at hleftMem hrightMem
    simp only [List.length_map] at hleftMem hrightMem
    have hleftBounded := (List.mem_filter.mp hleftMem).1
    have hrightBounded := (List.mem_filter.mp hrightMem).1
    rw [(GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
      left linked).order.length_eq] at hleftBounded
    rw [(GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
      right linked).order.length_eq] at hrightBounded
    exact edgeLabelling_eq_of_word_eq_of_supported edges
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
        left linked).auxiliary
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
        right linked).auxiliary
      (boundedEdgeLabellings_sound
        (linkAuxiliaryCutoff K) edges _ hleftBounded).2
      (boundedEdgeLabellings_sound
        (linkAuxiliaryCutoff K) edges _ hrightBounded).2
      hword
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw
  apply List.map_congr_left
  intro linked _
  exact Prod.ext rfl (hauxiliary linked)

/-- Every target physical field is zero away from the displayed slab faces. -/
theorem globalTargetPhysical_eq_zero_of_not_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (faceId : Nat) (hface : faceId ∉ slabPhysicalFaceEdges 1) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
      source faceId = 0 :=
  (boundedEdgeLabellings_sound K (slabPhysicalFaceEdges 1)
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source)
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_mem
      source)).2 faceId hface

/-- Equality of finite target keys reconstructs equality of the literal target
atoms. -/
theorem globalTargetAtom_eq_of_targetKey_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hkey : globalInwardMateTargetKey left =
      globalInwardMateTargetKey right) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom left =
      GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom right := by
  have hphysicalWord :
      globalInwardMateTargetPhysicalWord left =
        globalInwardMateTargetPhysicalWord right :=
    congrArg GlobalInwardMateTargetKey.physicalWord hkey
  have hauxiliaryWords :
      globalInwardMateTargetAuxiliaryWords left =
        globalInwardMateTargetAuxiliaryWords right :=
    congrArg GlobalInwardMateTargetKey.auxiliaryWords hkey
  have hphysicalFiniteWord :
      finiteEdgeLabellingWord (slabPhysicalFaceEdges 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left) =
        finiteEdgeLabellingWord (slabPhysicalFaceEdges 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right) := by
    calc
      _ = globalInwardMateTargetPhysicalWord left :=
        (globalInwardMateTargetPhysicalWord_eq left).symm
      _ = globalInwardMateTargetPhysicalWord right := hphysicalWord
      _ = _ := globalInwardMateTargetPhysicalWord_eq right
  have hauxiliaryFiniteWords :
      presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented left) =
        presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented right) := by
    calc
      _ = globalInwardMateTargetAuxiliaryWords left :=
        (globalInwardMateTargetAuxiliaryWords_eq left).symm
      _ = globalInwardMateTargetAuxiliaryWords right := hauxiliaryWords
      _ = _ := globalInwardMateTargetAuxiliaryWords_eq right
  have hphysical :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right :=
    edgeLabelling_eq_of_word_eq_of_supported
      (slabPhysicalFaceEdges 1)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right)
      (globalTargetPhysical_eq_zero_of_not_mem left)
      (globalTargetPhysical_eq_zero_of_not_mem right)
      hphysicalFiniteWord
  have hraw :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw right :=
    globalTargetRaw_eq_of_auxiliaryWords_eq left right hauxiliaryFiniteWords
  have hpair :
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left,
          GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw left) =
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right,
          GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw right) :=
    prod_eq_of_fields_eq hphysical hraw
  calc
    GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom left =
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left,
          GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw left) :=
      globalTargetAtom_eq left
    _ = _ := hpair
    _ = GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom right :=
      (globalTargetAtom_eq right).symm

/-- Conversely, equal target atoms have equal finite keys. -/
theorem globalTargetKey_eq_of_targetAtom_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hatom :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom right) :
    globalInwardMateTargetKey left = globalInwardMateTargetKey right := by
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
  have hphysical := prod_fst_eq_of_eq hpair
  have hraw := prod_snd_eq_of_eq hpair
  have hphysicalWord :
      finiteEdgeLabellingWord (slabPhysicalFaceEdges 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left) =
        finiteEdgeLabellingWord (slabPhysicalFaceEdges 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right) :=
    congrArg (finiteEdgeLabellingWord (slabPhysicalFaceEdges 1)) hphysical
  have hauxiliaryWords :
      presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented left) =
        presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented right) := by
    unfold presentedSlabFusionWitnessAssignmentAuxiliaryWords
    apply List.map_congr_left
    intro linked _
    have haux := globalTargetRaw_auxiliary_eq_of_eq
      left right hraw linked
    exact congrArg
      (finiteEdgeLabellingWord
        (canonicalUsedAuxiliaryCoordinates
          (slabIncidentPlaqIds 1 linked.1).length)) haux
  have hphysicalKeyWord :
      globalInwardMateTargetPhysicalWord left =
        globalInwardMateTargetPhysicalWord right := by
    calc
      _ = finiteEdgeLabellingWord (slabPhysicalFaceEdges 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left) :=
        globalInwardMateTargetPhysicalWord_eq left
      _ = _ := hphysicalWord
      _ = globalInwardMateTargetPhysicalWord right :=
        (globalInwardMateTargetPhysicalWord_eq right).symm
  have hauxiliaryKeyWords :
      globalInwardMateTargetAuxiliaryWords left =
        globalInwardMateTargetAuxiliaryWords right := by
    calc
      _ = presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented left) :=
        globalInwardMateTargetAuxiliaryWords_eq left
      _ = _ := hauxiliaryWords
      _ = globalInwardMateTargetAuxiliaryWords right :=
        (globalInwardMateTargetAuxiliaryWords_eq right).symm
  change
    ({ physicalWord := globalInwardMateTargetPhysicalWord left
       auxiliaryWords := globalInwardMateTargetAuxiliaryWords left } :
      GlobalInwardMateTargetKey) =
    ({ physicalWord := globalInwardMateTargetPhysicalWord right
       auxiliaryWords := globalInwardMateTargetAuxiliaryWords right } :
      GlobalInwardMateTargetKey)
  exact targetKey_eq_of_fields_eq
    { physicalWord := globalInwardMateTargetPhysicalWord left
      auxiliaryWords := globalInwardMateTargetAuxiliaryWords left }
    { physicalWord := globalInwardMateTargetPhysicalWord right
      auxiliaryWords := globalInwardMateTargetAuxiliaryWords right }
    hphysicalKeyWord hauxiliaryKeyWords

theorem globalTargetKey_eq_iff_targetAtom_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    globalInwardMateTargetKey left = globalInwardMateTargetKey right ↔
      GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom right :=
  ⟨globalTargetAtom_eq_of_targetKey_eq left right,
    globalTargetKey_eq_of_targetAtom_eq left right⟩

/-- Equal exact target keys and equal six-bit codes recover the complete
successful source. -/
theorem globalTargetSource_eq_of_targetKey_eq_of_code_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hkey : globalInwardMateTargetKey left =
      globalInwardMateTargetKey right)
    (hcode :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode right) :
    left = right :=
  globalTargetSource_eq_of_targetAtom_eq_of_targetPreimageCode_eq
    left right (globalTargetAtom_eq_of_targetKey_eq left right hkey) hcode

/-! ## 2. The global successful-source carrier is duplicate-free -/

private theorem nodup_flatMap_of_disjoint_blocks
    {A B : Type} (block : A → List B) :
    ∀ source : List A, source.Nodup →
      (∀ item, item ∈ source → (block item).Nodup) →
      (∀ left, left ∈ source → ∀ right, right ∈ source →
        left ≠ right → ∀ value, value ∈ block left →
          value ∉ block right) →
      (source.flatMap block).Nodup
  | [], _, _, _ => List.nodup_nil
  | head :: tail, hsource, hblocks, hdisjoint => by
      have hparts := List.nodup_cons.mp hsource
      rw [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨hblocks head List.mem_cons_self,
        nodup_flatMap_of_disjoint_blocks block tail hparts.2
          (fun item hitem =>
            hblocks item (List.mem_cons_of_mem head hitem))
          (fun left hleft right hright hne =>
            hdisjoint left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright) hne), ?_⟩
      intro value hhead other htail heq
      have hvalueTail : value ∈ tail.flatMap block := by
        rw [heq]
        exact htail
      obtain ⟨item, hitem, hvalueItem⟩ := List.mem_flatMap.mp hvalueTail
      have hne : head ≠ item := by
        intro hsame
        subst item
        exact hparts.1 hitem
      exact (hdisjoint head List.mem_cons_self item
        (List.mem_cons_of_mem head hitem) hne value hhead) hvalueItem

private theorem globalTargetBlock_nodup
    (K : Nat) (hK : 1 ≤ K) (physicalSource : CubeInwardMatePhysicalSource K) :
    (globalCubeInwardMateCertifiedTargetFullSourceBlock
      K hK physicalSource).Nodup := by
  unfold globalCubeInwardMateCertifiedTargetFullSourceBlock
  apply nodup_map_of_injOn
  · exact cubeInwardMateCertifiedTargetFullSources_nodup
      K physicalSource.1 hK
        (cubeInwardMatePhysicalBoundedOfMem
          K physicalSource.1 physicalSource.2)
  · intro left _ right _ heq
    injection heq

private theorem range_nodup_local :
    ∀ count : Nat, (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      exact List.nodup_append.mpr
        ⟨range_nodup_local count,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
          fun item hitem member hmember => by
            have hmemberEq : member = count := List.mem_singleton.mp hmember
            subst member
            exact Nat.ne_of_lt (List.mem_range.mp hitem)⟩

/-- No successful all-target global source is enumerated twice. -/
theorem globalCubeInwardMateCertifiedTargetFullSources_nodup
    (K : Nat) (hK : 1 ≤ K) :
    (globalCubeInwardMateCertifiedTargetFullSources K hK).Nodup := by
  unfold globalCubeInwardMateCertifiedTargetFullSources
  apply nodup_flatMap_of_disjoint_blocks
    (globalCubeInwardMateCertifiedTargetFullSourceBlock K hK)
  · exact attach_nodup_of_nodup _
      (YMGap.Continuum.Z4BoundedEdgeLabellingNodup.boundedEdgeLabellings_nodup
        K (slabPhysicalFaceEdges 1)
          (by
            unfold slabPhysicalFaceEdges
            exact range_nodup_local _))
  · intro physicalSource _
    exact globalTargetBlock_nodup K hK physicalSource
  · intro left _ right _ hne value hleft
    intro hright
    have hleftPhysical : value.physicalSource = left := by
      obtain ⟨entry, _, hentry⟩ := List.mem_map.mp hleft
      exact congrArg
        GlobalCubeInwardMateCertifiedTargetFullSource.physicalSource
        hentry.symm
    have hrightPhysical : value.physicalSource = right := by
      obtain ⟨entry, _, hentry⟩ := List.mem_map.mp hright
      exact congrArg
        GlobalCubeInwardMateCertifiedTargetFullSource.physicalSource
        hentry.symm
    exact hne (hleftPhysical.symm.trans hrightPhysical)

/-! ## 3. Exact target fibers have capacity at most sixty-four -/

/-- The literal successful-source fiber over the exact target atom represented
by `representative`. -/
def globalInwardMateTargetFiber
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    List (GlobalCubeInwardMateCertifiedTargetFullSource K hK) :=
  (globalCubeInwardMateCertifiedTargetFullSources K hK).filter
    (fun source => decide
      (globalInwardMateTargetKey source =
        globalInwardMateTargetKey representative))

theorem globalInwardMateTargetFiber_nodup
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    (globalInwardMateTargetFiber representative).Nodup := by
  unfold globalInwardMateTargetFiber
  exact List.filter_sublist.nodup
    (globalCubeInwardMateCertifiedTargetFullSources_nodup K hK)

theorem globalInwardMateTargetFiber_key_eq
    {K : Nat} {hK : 1 ≤ K}
    (representative source :
      GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hsource : source ∈ globalInwardMateTargetFiber representative) :
    globalInwardMateTargetKey source =
      globalInwardMateTargetKey representative := by
  exact of_decide_eq_true (List.mem_filter.mp hsource).2

/-- **Exact target-column capacity.**  Every realized target atom has at most
the `2^6 = 64` successful source preimages. -/
theorem globalInwardMateTargetFiber_length_le_sixtyFour
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    (globalInwardMateTargetFiber representative).length ≤ 64 := by
  let fiber := globalInwardMateTargetFiber representative
  let encode : {source // source ∈ fiber} → List Bool :=
    fun source =>
      GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode source.1
  have hfiberNodup : fiber.Nodup :=
    globalInwardMateTargetFiber_nodup representative
  have hattachedNodup : fiber.attach.Nodup :=
    attach_nodup_of_nodup fiber hfiberNodup
  have hencodedNodup : (fiber.attach.map encode).Nodup := by
    apply nodup_map_of_injOn encode fiber.attach hattachedNodup
    intro left _ right _ hcode
    apply Subtype.ext
    apply globalTargetSource_eq_of_targetKey_eq_of_code_eq left.1 right.1
    · exact (globalInwardMateTargetFiber_key_eq
          representative left.1 left.2).trans
        (globalInwardMateTargetFiber_key_eq
          representative right.1 right.2).symm
    · exact hcode
  have hsubset : ∀ code, code ∈ fiber.attach.map encode →
      code ∈ globalInwardMateTargetPreimageCodeSpace := by
    intro code hcode
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp hcode
    exact
      GlobalCubeInwardMateCertifiedTargetFullSource.targetPreimageCode_mem
        source.1
  have hbound := nodup_subset_length_le
    (fiber.attach.map encode)
    globalInwardMateTargetPreimageCodeSpace
    hencodedNodup hsubset
  have hattachLength : fiber.attach.length = fiber.length := by
    rw [← List.length_map Subtype.val, List.attach_map_subtype_val]
  calc
    (globalInwardMateTargetFiber representative).length = fiber.length := rfl
    _ = fiber.attach.length := hattachLength.symm
    _ = (fiber.attach.map encode).length := (List.length_map _).symm
    _ ≤ globalInwardMateTargetPreimageCodeSpace.length := hbound
    _ = 64 := globalInwardMateTargetPreimageCodeSpace_length

#print axioms globalTargetRaw_eq_of_auxiliaryWords_eq
#print axioms globalTargetPhysical_eq_zero_of_not_mem
#print axioms globalTargetAtom_eq_of_targetKey_eq
#print axioms globalTargetKey_eq_of_targetAtom_eq
#print axioms globalTargetKey_eq_iff_targetAtom_eq
#print axioms globalTargetSource_eq_of_targetKey_eq_of_code_eq
#print axioms globalCubeInwardMateCertifiedTargetFullSources_nodup
#print axioms globalInwardMateTargetFiber_nodup
#print axioms globalInwardMateTargetFiber_key_eq
#print axioms globalInwardMateTargetFiber_length_le_sixtyFour

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberCapacity
