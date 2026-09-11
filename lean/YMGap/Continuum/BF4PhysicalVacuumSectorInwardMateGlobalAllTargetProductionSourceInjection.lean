/-
# Multiplicity-faithful production source compiler

The production-pair layer serializes every complete classified source
outcome into two finite natural-word blocks: the twelve decoded cube rows and
the off-cube production assignment.  This module proves that serialization
is injective on the exact complete carrier.

The proof is an explicit inverse argument.  Equal cube words reconstruct the
accepted root-first source witnesses on every incidence; injectivity of the
certified classifier then reconstructs the classified branch.  Equal
off-cube words reconstruct the literal finite assignment on the complementary
links.  Hence the complete source-code list is duplicate-free, and the
equal-rank compiler into the production fiber is injective.

This establishes multiplicity-faithful source recoding at each fixed physical
field.  It still does not identify the constructed pairs with the actual BF4
conditional/OS joint, and no posterior variance, OS form bound, spectral gap,
beta/lattice-spacing uniformity, or continuum theorem is asserted.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionPair

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionSourceInjection

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceEnumeration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceOffCubeCompletion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionPair
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.FiniteBistochasticRankReindex
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff

private theorem map_functions_eq_on_mem_local
    {A B : Type} [DecidableEq A] (items : List A)
    (left right : A → B) (hmap : items.map left = items.map right) :
    ∀ item, item ∈ items → left item = right item := by
  induction items with
  | nil =>
      intro item hitem
      exact False.elim (List.not_mem_nil hitem)
  | cons head tail ih =>
      simp only [List.map_cons] at hmap
      have hhead : left head = right head := by injection hmap
      have htail : tail.map left = tail.map right := by injection hmap
      intro item hitem
      rcases List.mem_cons.mp hitem with heq | htailMem
      · subst item
        exact hhead
      · exact ih htail item htailMem

/-! ## 1. The cube word reconstructs a classified outcome -/

/-- The twelve decoded root-first source rows of one classified cube
outcome. -/
def cubeInwardMateCertifiedOutcomeSourceWords
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (outcome :
      Sum
        (CubeInwardMateOrderedTargetWitnessAssignment K physical)
        (CubeInwardMateCertifiedFirstStretchedSource
          K physical hK hbounded)) : List (List Nat) :=
  List.map (fun linked =>
    finiteEdgeLabellingWord
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds 1 linked.1.link).length)
      (recoverCubeInwardMateSourceWitnessPartitionAt
        K physical hK hbounded linked
        (unsplitCubeInwardMateCertifiedSource
          K physical hK hbounded outcome linked)))
    cubeProductionIncidences.attach

private theorem classifiedOutcome_eq_of_sourceWords_eq
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (left right :
      Sum
        (CubeInwardMateOrderedTargetWitnessAssignment K physical)
        (CubeInwardMateCertifiedFirstStretchedSource
          K physical hK hbounded))
    (hleft : left ∈ cubeInwardMateCertifiedSourceOutcomes
      K physical hK hbounded)
    (hright : right ∈ cubeInwardMateCertifiedSourceOutcomes
      K physical hK hbounded)
    (hwords : cubeInwardMateCertifiedOutcomeSourceWords
        K physical hK hbounded left =
      cubeInwardMateCertifiedOutcomeSourceWords
        K physical hK hbounded right) :
    left = right := by
  unfold cubeInwardMateCertifiedSourceOutcomes at hleft hright
  obtain ⟨leftSource, hleftSource, hleftEq⟩ := List.mem_map.mp hleft
  obtain ⟨rightSource, hrightSource, hrightEq⟩ := List.mem_map.mp hright
  have hsources : leftSource = rightSource := by
    funext linked
    apply Subtype.ext
    let edges := canonicalUsedAuxiliaryCoordinates
      (slabIncidentPlaqIds 1 linked.1.link).length
    apply edgeLabelling_eq_of_word_eq_of_supported edges
    · have hboundedLeft := (List.mem_filter.mp (leftSource linked).2).1
      have hlength :
          (List.map physical
            (cubeInwardMateSourceFaceOrder linked).faceIds).length =
            (slabIncidentPlaqIds 1 linked.1.link).length := by
        rw [List.length_map]
        exact (cubeInwardMateSourceFaceOrder linked).length_eq
      rw [hlength] at hboundedLeft
      exact (boundedEdgeLabellings_sound
        (linkAuxiliaryCutoff K) edges (leftSource linked).1
        (by simpa [edges] using hboundedLeft)).2
    · have hboundedRight := (List.mem_filter.mp (rightSource linked).2).1
      have hlength :
          (List.map physical
            (cubeInwardMateSourceFaceOrder linked).faceIds).length =
            (slabIncidentPlaqIds 1 linked.1.link).length := by
        rw [List.length_map]
        exact (cubeInwardMateSourceFaceOrder linked).length_eq
      rw [hlength] at hboundedRight
      exact (boundedEdgeLabellings_sound
        (linkAuxiliaryCutoff K) edges (rightSource linked).1
        (by simpa [edges] using hboundedRight)).2
    · have hrow := map_functions_eq_on_mem_local
        cubeProductionIncidences.attach
        (fun candidate =>
          finiteEdgeLabellingWord
            (canonicalUsedAuxiliaryCoordinates
              (slabIncidentPlaqIds 1 candidate.1.link).length)
            (recoverCubeInwardMateSourceWitnessPartitionAt
              K physical hK hbounded candidate
              (unsplitCubeInwardMateCertifiedSource
                K physical hK hbounded left candidate)))
        (fun candidate =>
          finiteEdgeLabellingWord
            (canonicalUsedAuxiliaryCoordinates
              (slabIncidentPlaqIds 1 candidate.1.link).length)
            (recoverCubeInwardMateSourceWitnessPartitionAt
              K physical hK hbounded candidate
              (unsplitCubeInwardMateCertifiedSource
                K physical hK hbounded right candidate)))
        hwords linked (List.mem_attach cubeProductionIncidences linked)
      have hleftDecoded :
          recoverCubeInwardMateSourceWitnessPartitionAt
              K physical hK hbounded linked
              (unsplitCubeInwardMateCertifiedSource
                K physical hK hbounded left linked) =
            (leftSource linked).1 := by
        rw [← hleftEq,
          unsplit_certifiedSourceTargetOrFirstStretched]
        unfold cubeInwardMateSourceAssignmentPartition
        exact recoverCubeInwardMateSourceWitnessPartitionAt_apply
          K physical hK hbounded linked (leftSource linked)
      have hrightDecoded :
          recoverCubeInwardMateSourceWitnessPartitionAt
              K physical hK hbounded linked
              (unsplitCubeInwardMateCertifiedSource
                K physical hK hbounded right linked) =
            (rightSource linked).1 := by
        rw [← hrightEq,
          unsplit_certifiedSourceTargetOrFirstStretched]
        unfold cubeInwardMateSourceAssignmentPartition
        exact recoverCubeInwardMateSourceWitnessPartitionAt_apply
          K physical hK hbounded linked (rightSource linked)
      simpa [cubeInwardMateCertifiedOutcomeSourceWords,
        edges, hleftDecoded, hrightDecoded] using hrow
  calc
    left = cubeInwardMateCertifiedSourceTargetOrFirstStretched
        K physical hK hbounded leftSource := hleftEq.symm
    _ = cubeInwardMateCertifiedSourceTargetOrFirstStretched
        K physical hK hbounded rightSource := congrArg _ hsources
    _ = right := hrightEq

/-! ## 2. The off-cube word reconstructs the production assignment -/

private theorem offCubeAssignment_eq_of_words_eq
    (K : Nat) (physical : EdgeLabelling)
    (left right : SlabFusionWitnessAssignment)
    (hleft : left ∈
      cubeInwardMateOffCubeFusionWitnessAssignments K physical)
    (hright : right ∈
      cubeInwardMateOffCubeFusionWitnessAssignments K physical)
    (hwords : slabFusionWitnessAssignmentWords 1 left =
      slabFusionWitnessAssignmentWords 1 right) :
    left = right := by
  let links := cubeInwardMateOffCubeSlabLinks
  have hleftOn : left ∈ slabFusionWitnessAssignmentsOn K 1 physical links := by
    simpa [links, cubeInwardMateOffCubeFusionWitnessAssignments] using hleft
  have hrightOn : right ∈ slabFusionWitnessAssignmentsOn K 1 physical links := by
    simpa [links, cubeInwardMateOffCubeFusionWitnessAssignments] using hright
  have hlinksNodup : links.Nodup := by
    unfold links cubeInwardMateOffCubeSlabLinks
    exact List.filter_sublist.nodup (boundaryCompleteSlabLinks_nodup 1)
  have hlookup : ∀ link, link ∈ links →
      slabFusionWitnessAssignmentAt link left =
        slabFusionWitnessAssignmentAt link right := by
    intro link hlink
    let edges := canonicalUsedAuxiliaryCoordinates
      (slabIncidentPlaqIds 1 link).length
    have hcomplete : link ∈ boundaryCompleteSlabLinks 1 :=
      (mem_cubeInwardMateOffCubeSlabLinks_iff link).mp hlink |>.1
    have hword : finiteEdgeLabellingWord edges
          (slabFusionWitnessAssignmentAt link left) =
        finiteEdgeLabellingWord edges
          (slabFusionWitnessAssignmentAt link right) := by
      exact map_functions_eq_on_mem_local
        (boundaryCompleteSlabLinks 1)
        (fun candidate =>
          finiteEdgeLabellingWord
            (canonicalUsedAuxiliaryCoordinates
              (slabIncidentPlaqIds 1 candidate).length)
            (slabFusionWitnessAssignmentAt candidate left))
        (fun candidate =>
          finiteEdgeLabellingWord
            (canonicalUsedAuxiliaryCoordinates
              (slabIncidentPlaqIds 1 candidate).length)
            (slabFusionWitnessAssignmentAt candidate right))
        hwords link hcomplete
    have hleftLocal := slabFusionWitnessAssignmentAt_mem_local
      K 1 physical links left hleftOn link hlink
    have hrightLocal := slabFusionWitnessAssignmentAt_mem_local
      K 1 physical links right hrightOn link hlink
    have hleftBounded := (List.mem_filter.mp hleftLocal).1
    have hrightBounded := (List.mem_filter.mp hrightLocal).1
    apply edgeLabelling_eq_of_word_eq_of_supported edges
    · exact (boundedEdgeLabellings_sound
        (linkAuxiliaryCutoff K) edges
        (slabFusionWitnessAssignmentAt link left) hleftBounded).2
    · exact (boundedEdgeLabellings_sound
        (linkAuxiliaryCutoff K) edges
        (slabFusionWitnessAssignmentAt link right) hrightBounded).2
    · exact hword
  calc
    left = slabFusionWitnessAssignmentFrom links
        (fun link => slabFusionWitnessAssignmentAt link left) :=
      (slabFusionWitnessAssignmentFrom_at_eq K 1 physical
        links left hlinksNodup hleftOn).symm
    _ = slabFusionWitnessAssignmentFrom links
        (fun link => slabFusionWitnessAssignmentAt link right) := by
      unfold slabFusionWitnessAssignmentFrom
      apply List.map_congr_left
      intro link hlink
      exact congrArg (fun auxiliary => (link, auxiliary))
        (hlookup link hlink)
    _ = right := slabFusionWitnessAssignmentFrom_at_eq K 1 physical
      links right hlinksNodup hrightOn

/-! ## 3. The complete source code is injective -/

/-- Equal finite source codes recover equal complete classified outcomes. -/
theorem cubeInwardMateCertifiedOutcomeFullSourceCode_injective
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (left : CubeInwardMateCertifiedOutcomeFullSource
      K physical hK hbounded)
    (hleft : left ∈ cubeInwardMateCertifiedOutcomeFullSources
      K physical hK hbounded)
    (right : CubeInwardMateCertifiedOutcomeFullSource
      K physical hK hbounded)
    (hright : right ∈ cubeInwardMateCertifiedOutcomeFullSources
      K physical hK hbounded)
    (hcode : cubeInwardMateCertifiedOutcomeFullSourceCode
        K physical hK hbounded left =
      cubeInwardMateCertifiedOutcomeFullSourceCode
        K physical hK hbounded right) :
    left = right := by
  have hleftParts := (mem_cartesian_iff _ _ left).mp hleft
  have hrightParts := (mem_cartesian_iff _ _ right).mp hright
  have hcubeCode := congrArg Prod.fst hcode
  have hoffCode := congrArg Prod.snd hcode
  have hcube : left.1 = right.1 := by
    apply classifiedOutcome_eq_of_sourceWords_eq
      K physical hK hbounded left.1 right.1 hleftParts.1 hrightParts.1
    simpa [cubeInwardMateCertifiedOutcomeFullSourceCode,
      cubeInwardMateCertifiedOutcomeSourceWords] using hcubeCode
  have hoff : left.2.1 = right.2.1 := by
    apply offCubeAssignment_eq_of_words_eq K physical
    · exact left.2.2
    · exact right.2.2
    · simpa [cubeInwardMateCertifiedOutcomeFullSourceCode] using hoffCode
  apply Prod.ext
  · exact hcube
  · exact Subtype.ext hoff

/-- The complete written source-code family has no collisions. -/
theorem cubeInwardMateCertifiedOutcomeFullSourceCodes_nodup
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateCertifiedOutcomeFullSourceCodes
      K physical hK hbounded).Nodup := by
  unfold cubeInwardMateCertifiedOutcomeFullSourceCodes
  apply nodup_map_of_injOn
  · exact cubeInwardMateCertifiedOutcomeFullSources_nodup
      K physical hK hbounded
  · intro left hleft right hright hcode
    exact cubeInwardMateCertifiedOutcomeFullSourceCode_injective
      K physical hK hbounded left hleft right hright hcode

/-! ## 4. Equal-rank production recoding preserves multiplicity -/

private theorem listAtRank_injective_local
    {A : Type} (fallback : A) :
    ∀ {items : List A}, items.Nodup →
      ∀ {left right : Nat},
        left < items.length → right < items.length →
        listAtRank fallback items left = listAtRank fallback items right →
        left = right
  | [], _, left, _, hleft, _, _ =>
      False.elim (Nat.not_lt_zero left hleft)
  | head :: tail, hnodup, left, right, hleft, hright, heq => by
      have hparts := List.nodup_cons.mp hnodup
      cases left with
      | zero =>
          cases right with
          | zero => rfl
          | succ rightTail =>
              have hrightTail : rightTail < tail.length :=
                Nat.lt_of_succ_lt_succ hright
              have hmem := listAtRank_mem_of_lt
                fallback tail rightTail hrightTail
              change head = listAtRank fallback tail rightTail at heq
              rw [← heq] at hmem
              exact False.elim (hparts.1 hmem)
      | succ leftTail =>
          cases right with
          | zero =>
              have hleftTail : leftTail < tail.length :=
                Nat.lt_of_succ_lt_succ hleft
              have hmem := listAtRank_mem_of_lt
                fallback tail leftTail hleftTail
              change listAtRank fallback tail leftTail = head at heq
              rw [heq] at hmem
              exact False.elim (hparts.1 hmem)
          | succ rightTail =>
              have hleftTail : leftTail < tail.length :=
                Nat.lt_of_succ_lt_succ hleft
              have hrightTail : rightTail < tail.length :=
                Nat.lt_of_succ_lt_succ hright
              change listAtRank fallback tail leftTail =
                listAtRank fallback tail rightTail at heq
              exact congrArg Nat.succ
                (listAtRank_injective_local fallback hparts.2
                  hleftTail hrightTail heq)

/-- On the complete fixed-physical source-code carrier, equal production
assignments recover equal source codes. -/
theorem globalInwardMateSourceProductionRawAt_injective
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    {left right : List (List Nat) × List (List Nat)}
    (hleft : left ∈ cubeInwardMateCertifiedOutcomeFullSourceCodes
      K physical hK hbounded)
    (hright : right ∈ cubeInwardMateCertifiedOutcomeFullSourceCodes
      K physical hK hbounded)
    (heq : globalInwardMateSourceProductionRawAt
        K physical hK hbounded left =
      globalInwardMateSourceProductionRawAt
        K physical hK hbounded right) :
    left = right := by
  let codes := cubeInwardMateCertifiedOutcomeFullSourceCodes
    K physical hK hbounded
  let production := slabFineFusionWitnesses
    (globalInwardMateAnchorSlabData K) physical
  have hlength : production.length = codes.length :=
    globalInwardMateProductionFiber_length_eq_sourceOutcomes
      K physical hK hbounded
  have hleftRank : listRank left codes < production.length := by
    rw [hlength]
    exact listRank_lt_length_of_mem left hleft
  have hrightRank : listRank right codes < production.length := by
    rw [hlength]
    exact listRank_lt_length_of_mem right hright
  have hranks : listRank left codes = listRank right codes := by
    apply listAtRank_injective_local []
      (slabFineFusionWitnesses_nodup
        (globalInwardMateAnchorSlabData K) physical)
      hleftRank hrightRank
    simpa only [globalInwardMateSourceProductionRawAt,
      equalRankReindex, production, codes] using heq
  calc
    left = listAtRank left codes (listRank left codes) :=
      (listAtRank_listRank_eq_of_mem left left hleft).symm
    _ = listAtRank left codes (listRank right codes) := by rw [hranks]
    _ = right := listAtRank_listRank_eq_of_mem left right hright

#print axioms cubeInwardMateCertifiedOutcomeSourceWords
#print axioms cubeInwardMateCertifiedOutcomeFullSourceCode_injective
#print axioms cubeInwardMateCertifiedOutcomeFullSourceCodes_nodup
#print axioms globalInwardMateSourceProductionRawAt_injective

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionSourceInjection
