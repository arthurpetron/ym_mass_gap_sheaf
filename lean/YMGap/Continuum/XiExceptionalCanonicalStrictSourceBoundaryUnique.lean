/-
# Exact first-b2 source boundary when the bad occurrence is unique

This module discharges the complete canonical source-fibre round trip for the
natural source class in which `b2` occurs at only one in-range occurrence of
`Gamma`.  The proof is structural: the simple exceptional walk reaches that
unique occurrence only at its endpoint, and all later normalization edges are
outer attachments.
-/

import YMGap.Continuum.XiExceptionalCanonicalStrictSourceBoundary

namespace YMGap.Continuum.XiExceptionalCanonicalStrictSourceBoundaryUnique

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier
open YMGap.Continuum.XiExceptionalOccurrenceTreeCodes
open YMGap.Continuum.XiExceptionalOccurrenceTreeWeight
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalSourceTreeCarrier
open YMGap.Continuum.XiExceptionalSourceTreeFiber
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier
open YMGap.Continuum.XiExceptionalCanonicalStrictSourceFiber
open YMGap.Continuum.XiExceptionalCanonicalStrictSourceBoundary

variable {L : Lattice} [DecidableEq L.Plaquette]

def B2OccurrenceUnique (Gamma : List (Polymer L))
    (b2 : Polymer L → Bool) : Prop :=
  ∀ i j, i < Gamma.length → j < Gamma.length →
    b2 (polyAt Gamma i) = true → b2 (polyAt Gamma j) = true → i = j

theorem CWalk.end_mem_vertices
    {α : Type} {edge : α → α → Bool} :
    ∀ {x y : α} (walk : CWalk edge x y), y ∈ walk.vertices
  | _, _, .single _ => List.mem_cons_self
  | _, _, .cons _ rest =>
      List.mem_cons_of_mem _ (CWalk.end_mem_vertices rest)

theorem prependUntilB2_ofWalk_append
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    {edge : Nat → Nat → Bool} :
    ∀ {x y : Nat} (walk : CWalk edge x y),
      walk.vertices.Nodup →
      b2 (polyAt Gamma y) = true →
      (∀ i, i ∈ walk.vertices →
        b2 (polyAt Gamma i) = true → i = y) →
      x ≠ y →
      ∀ suffix : List (Nat × Nat),
        prependUntilB2 Gamma b2 x
            (oTreeOrderedAttachments (OTree.ofWalk walk) ++ suffix) =
          OTree.toCode (N := Gamma.length) (OTree.ofWalk walk)
  | _, _, .single _, _, _, _, hxy, _ => absurd rfl hxy
  | x, y, @CWalk.cons _ _ _ next _ hedge rest,
      hnodup, hterminal, honly, hxy, suffix => by
      cases rest with
      | single _ =>
          change (if b2 (polyAt Gamma y) then
              OccTreeCode.prepend x (OccTreeCode.single y)
            else OccTreeCode.prepend x
              (prependUntilB2 Gamma b2 y suffix)) = _
          rw [hterminal]
          rfl
      | cons hedge2 tail =>
          have hrestNodup :
              (CWalk.cons hedge2 tail).vertices.Nodup :=
            (List.nodup_cons.mp hnodup).2
          have hnextNe : next ≠ y := by
            intro hnext
            subst next
            have hyTail : y ∈ tail.vertices :=
              CWalk.end_mem_vertices tail
            exact (List.nodup_cons.mp hrestNodup).1 hyTail
          have hnextFalse : b2 (polyAt Gamma next) = false := by
            cases hbad : b2 (polyAt Gamma next) with
            | false => rfl
            | true =>
                have hnextEq : next = y := honly next
                  (List.mem_cons_of_mem x List.mem_cons_self) hbad
                exact absurd hnextEq hnextNe
          have honlyRest : ∀ i,
              i ∈ (CWalk.cons hedge2 tail).vertices →
              b2 (polyAt Gamma i) = true → i = y := by
            intro i hi hb
            exact honly i (List.mem_cons_of_mem x hi) hb
          have ih := prependUntilB2_ofWalk_append Gamma b2
            (CWalk.cons hedge2 tail) hrestNodup hterminal
            honlyRest hnextNe suffix
          change (if b2 (polyAt Gamma next) then
              OccTreeCode.prepend x (OccTreeCode.single next)
            else OccTreeCode.prepend x
              (prependUntilB2 Gamma b2 next
                (oTreeOrderedAttachments
                  (OTree.ofWalk (CWalk.cons hedge2 tail)) ++ suffix))) =
            OccTreeCode.prepend x
              (OTree.toCode (N := Gamma.length)
                (OTree.ofWalk (CWalk.cons hedge2 tail)))
          rw [hnextFalse]
          exact congrArg (OccTreeCode.prepend x) ih

theorem treeCodeRoot_core {N : Nat} : ∀ code : OccTreeCode N,
    treeCodeRoot (OccTreeCode.core code) = treeCodeRoot code
  | .single _ => rfl
  | .prepend _ _ => rfl
  | .attach tree _ _ => treeCodeRoot_core tree

theorem entry_path_prependUntilB2_of_unique
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hunique : B2OccurrenceUnique Gamma b2) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let walk := conflictWalkOfDisagreement Gamma
      (bitMask pair.1) (bitMask pair.2) path.indexWalk
    ∀ suffix : List (Nat × Nat),
      prependUntilB2 Gamma b2 path.indexWalk.start
          (oTreeOrderedAttachments (OTree.ofWalk walk) ++ suffix) =
        OTree.toCode (N := Gamma.length) (OTree.ofWalk walk) := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let walk := conflictWalkOfDisagreement Gamma
    (bitMask pair.1) (bitMask pair.2) path.indexWalk
  have hseedB2 : b2 (polyAt Gamma path.seed) = true :=
    (forwardSeed_parts Gamma.length (bitMask pair.1) (bitMask pair.2)
      (predAt Gamma b2) path.seed_true).2.2.2
  have hseedLt : path.seed < Gamma.length :=
    (forwardSeed_parts Gamma.length (bitMask pair.1) (bitMask pair.2)
      (predAt Gamma b2) path.seed_true).1
  have hvertices : walk.vertices = path.indexWalk.vertices :=
    conflictWalkOfDisagreement_vertices Gamma
      (bitMask pair.1) (bitMask pair.2) path.indexWalk
  have hbound : ∀ i, i ∈ walk.vertices → i < Gamma.length := by
    intro i hi
    rw [hvertices] at hi
    exact walk_vertices_lt_of_seed Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) path.indexWalk hseedLt i hi
  have honly : ∀ i, i ∈ walk.vertices →
      b2 (polyAt Gamma i) = true → i = path.seed := by
    intro i hi hb
    exact hunique i path.seed (hbound i hi) hseedLt hb hseedB2
  have hmarkedB2 : b2 (polyAt Gamma
      (exceptionalMarkedIndex Gamma b1 b2 pair)) = false :=
    facts.right_good _ facts.marked_right_true
  have hstartNe : path.indexWalk.start ≠ path.seed := by
    intro heq
    have hstart : path.indexWalk.start =
        exceptionalMarkedIndex Gamma b1 b2 pair := CWalk.start_eq _
    have : b2 (polyAt Gamma
        (exceptionalMarkedIndex Gamma b1 b2 pair)) = true := by
      rw [← hstart, heq]
      exact hseedB2
    rw [hmarkedB2] at this
    cases this
  have hnodup : walk.vertices.Nodup := by
    rw [hvertices]
    exact path.index_nodup
  intro suffix
  exact prependUntilB2_ofWalk_append Gamma b2 walk hnodup
    hseedB2 honly hstartNe suffix

theorem entry_core_cut_of_b2OccurrenceUnique
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hunique : B2OccurrenceUnique Gamma b2) :
    prependUntilB2 Gamma b2
        (entryRootAttachmentCarrierCode Gamma qP b1 b2 entry).tree.root
        (entryRootAttachmentCarrierCode Gamma qP b1 b2 entry).tree.attachments =
      OccTreeCode.core
        (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry).tree := by
  let old := (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry).tree
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let walk := conflictWalkOfDisagreement Gamma
    (bitMask pair.1) (bitMask pair.2) path.indexWalk
  have hcanonical :
      (entryRootAttachmentCarrierCode Gamma qP b1 b2 entry).tree =
        occTreeCodeToRootAttachment old := by
    change oTreeToRootAttachmentCode
        (N := Gamma.length)
        (entryTreeExhaust Gamma qP b1 b2 entry).tree =
      occTreeCodeToRootAttachment
        (OTree.toCode (N := Gamma.length)
          (entryTreeExhaust Gamma qP b1 b2 entry).tree)
    exact (occTreeCodeToRootAttachment_toCode
      (N := Gamma.length)
      (entryTreeExhaust Gamma qP b1 b2 entry).tree).symm
  rw [hcanonical]
  unfold occTreeCodeToRootAttachment
  dsimp only
  rw [orderedAttachments_eq_core_append_attachments]
  have hcore := entryTreeCore_eq_initial Gamma qP b1 b2 entry
  change OccTreeCode.core old = OTree.toCode
      (N := Gamma.length) (OTree.ofWalk walk) at hcore
  have hroot := congrArg treeCodeRoot hcore
  rw [treeCodeRoot_core old, oTree_toCode_root] at hroot
  rw [hcore, oTree_toCode_orderedAttachments, hroot]
  simpa only [CWalk.start_eq] using
    (entry_path_prependUntilB2_of_unique
      Gamma qP b1 b2 entry hunique (OccTreeCode.attachments old))

theorem firstB2SourceBoundary_of_b2OccurrenceUnique
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hunique : B2OccurrenceUnique Gamma b2) :
    FirstB2SourceBoundary Gamma qP b1 b2 entry :=
  firstB2SourceBoundary_of_core_cut Gamma qP b1 b2 entry
    (entry_core_cut_of_b2OccurrenceUnique
      Gamma qP b1 b2 entry hunique)

#print axioms prependUntilB2_ofWalk_append
#print axioms entry_path_prependUntilB2_of_unique
#print axioms entry_core_cut_of_b2OccurrenceUnique
#print axioms firstB2SourceBoundary_of_b2OccurrenceUnique

end YMGap.Continuum.XiExceptionalCanonicalStrictSourceBoundaryUnique
