/-
# Exact first-b2 source boundary for every exceptional source

The canonical Warshall witness reaches no forward seed before its endpoint.
Along an exceptional source path, every `b2` occurrence is left-only (the
right family is pointwise `!b2`), hence is a forward seed.  Therefore the
first-`b2` decoder cuts exactly at the old walk core for every source entry,
with no uniqueness assumption on occurrences of `b2` in `Gamma`.
-/

import YMGap.Continuum.XiExceptionalWarshallSeedEndpoint
import YMGap.Continuum.XiExceptionalCanonicalStrictSourceBoundaryUnique

namespace YMGap.Continuum.XiExceptionalCanonicalStrictSourceBoundaryAll

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier
open YMGap.Continuum.XiExceptionalOccurrenceTreeCodes
open YMGap.Continuum.XiExceptionalOccurrenceTreeWeight
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalSourceTreeCarrier
open YMGap.Continuum.XiExceptionalSourceTreeFiber
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentEnumeration
open YMGap.Continuum.XiExceptionalCanonicalStrictCarrier
open YMGap.Continuum.XiExceptionalCanonicalStrictAnalytic
open YMGap.Continuum.XiExceptionalCanonicalStrictSourceFiber
open YMGap.Continuum.XiExceptionalCanonicalStrictSourceBoundary
open YMGap.Continuum.XiExceptionalCanonicalStrictSourceBoundaryUnique
open YMGap.Continuum.XiExceptionalWarshallSeedEndpoint

variable {L : Lattice} [DecidableEq L.Plaquette]

theorem sourceExceptionalPath_forwardSeed_unique
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (facts : ExceptionalSourceFacts Gamma qP b1 b2 pair) :
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    ∀ i, i ∈ path.indexWalk.vertices →
      forwardSeed Gamma.length (bitMask pair.1) (bitMask pair.2)
        (predAt Gamma b2) i = true → i = path.seed := by
  dsimp only [sourceExceptionalPath]
  apply reverseOccurrencePath_seed_unique

theorem sourceExceptionalPath_b2_only_seed
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (facts : ExceptionalSourceFacts Gamma qP b1 b2 pair) :
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    ∀ i, i ∈ path.indexWalk.vertices →
      b2 (polyAt Gamma i) = true → i = path.seed := by
  dsimp only
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  intro i hi hb2
  have hseedLt := (forwardSeed_parts Gamma.length
    (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
    path.seed_true).1
  have hiLt := walk_vertices_lt_of_seed Gamma.length
    (incAtDistinct Gamma) (bitMask pair.1) (bitMask pair.2)
    path.indexWalk hseedLt i hi
  have hdiff := walk_vertices_different_of_seed Gamma.length
    (incAtDistinct Gamma) (bitMask pair.1) (bitMask pair.2)
    (predAt Gamma b2) path.indexWalk path.seed_true i hi
  have hforward : forwardSeed Gamma.length
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i = true := by
    cases hl : bitMask pair.1 i <;> cases hr : bitMask pair.2 i
    · simp [differentBits, hl, hr] at hdiff
    · have hgood := facts.right_good i hr
      change predAt Gamma b2 i = true at hb2
      rw [hgood] at hb2
      cases hb2
    · unfold forwardSeed leftOnly
      rw [decide_eq_true hiLt, hl, hr]
      exact hb2
    · simp [differentBits, hl, hr] at hdiff
  exact sourceExceptionalPath_forwardSeed_unique
    Gamma qP b1 b2 pair facts i hi hforward

theorem entry_path_prependUntilB2
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
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
  have hvertices : walk.vertices = path.indexWalk.vertices :=
    conflictWalkOfDisagreement_vertices Gamma
      (bitMask pair.1) (bitMask pair.2) path.indexWalk
  have honly : ∀ i, i ∈ walk.vertices →
      b2 (polyAt Gamma i) = true → i = path.seed := by
    intro i hi hb
    rw [hvertices] at hi
    exact sourceExceptionalPath_b2_only_seed
      Gamma qP b1 b2 pair facts i hi hb
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

theorem entry_core_cut
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
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
    (entry_path_prependUntilB2
      Gamma qP b1 b2 entry (OccTreeCode.attachments old))

theorem firstB2SourceBoundary_all
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    FirstB2SourceBoundary Gamma qP b1 b2 entry :=
  firstB2SourceBoundary_of_core_cut Gamma qP b1 b2 entry
    (entry_core_cut Gamma qP b1 b2 entry)

theorem canonicalSourceRecoverable_all
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    CanonicalSourceRecoverable Gamma qP b1 b2 entry :=
  canonicalSourceRecoverable_of_firstB2Boundary Gamma qP b1 b2 entry
    (firstB2SourceBoundary_all Gamma qP b1 b2 entry)

theorem entryRootAttachmentCarrierCode_injective_all
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry1 entry2 : ExceptionalSourceEntry Gamma qP b1 b2)
    (hcode : entryRootAttachmentCarrierCode Gamma qP b1 b2 entry1 =
      entryRootAttachmentCarrierCode Gamma qP b1 b2 entry2) :
    entry1 = entry2 :=
  entryRootAttachmentCarrierCode_injective_of_recoverable
    Gamma qP b1 b2 entry1 entry2
    (canonicalSourceRecoverable_all Gamma qP b1 b2 entry1)
    (canonicalSourceRecoverable_all Gamma qP b1 b2 entry2) hcode

theorem fullExceptionalSource_sum_le_strictCarrier
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum
        (fun entry => occurrencePairWeight
          w qP b1 b2 Gamma label entry.1)
        (fullExceptionalSource Gamma qP b1 b2) ≤
      qListSum
        (strictRootAttachmentCarrierCodeWeight w Gamma qP b1 b2 label)
        (rootAttachmentCarrierCodes Gamma.length Gamma.length) := by
  apply qListSum_le_of_injective
    (fullExceptionalSource Gamma qP b1 b2)
    (rootAttachmentCarrierCodes Gamma.length Gamma.length)
    (fun entry => occurrencePairWeight
      w qP b1 b2 Gamma label entry.1)
    (strictRootAttachmentCarrierCodeWeight w Gamma qP b1 b2 label)
    (entryRootAttachmentCarrierCode Gamma qP b1 b2)
    (fullExceptionalSource_nodup Gamma qP b1 b2)
  · intro entry _
    exact entryRootAttachmentCarrierCode_mem Gamma qP b1 b2 entry
  · intro entry1 _ entry2 _ hcode
    exact entryRootAttachmentCarrierCode_injective_all
      Gamma qP b1 b2 entry1 entry2 hcode
  · intro entry _
    exact Q'.ge_of_eqv
      (entryRootAttachmentCarrierCode_strict_weight_eqv_source
        w Gamma qP b1 b2 label entry)
  · intro code _
    exact strictRootAttachmentCarrierCodeWeight_nonnegative hw
      Gamma qP b1 b2 label code

theorem exceptionalSourceCodes_sum_le_strictCarrier
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
        (exceptionalSourceCodes Gamma qP b1 b2) ≤
      qListSum
        (strictRootAttachmentCarrierCodeWeight w Gamma qP b1 b2 label)
        (rootAttachmentCarrierCodes Gamma.length Gamma.length) := by
  rw [← fullExceptionalSource_weight_eq]
  exact fullExceptionalSource_sum_le_strictCarrier
    hw Gamma qP b1 b2 label

theorem exceptionalSourceCodes_sum_le_strictRelaxed
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
        (exceptionalSourceCodes Gamma qP b1 b2) ≤
      strictRelaxedRootAttachmentCarrierMajorant
        w Gamma qP b1 b2 label :=
  Q'.le_trans' _ _ _
    (exceptionalSourceCodes_sum_le_strictCarrier
      hw Gamma qP b1 b2 label)
    (strictRootAttachmentCarrierMajorant_le_relaxed
      hw Gamma qP b1 b2 label)

theorem exceptionalSourceCodes_sum_le_strictTree_mul_XiR_sq
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
        (exceptionalSourceCodes Gamma qP b1 b2) ≤
      (strictCanonicalRootAttachmentTreeMajorant
          w Gamma qP b1 b2 label * XiR w qP Gamma label) *
        XiR w qP Gamma label :=
  Q'.le_trans' _ _ _
    (exceptionalSourceCodes_sum_le_strictRelaxed
      hw Gamma qP b1 b2 label)
    (Q'.le_of_eqv (strictRelaxedRootAttachmentCarrierMajorant_eqv
      w Gamma qP b1 b2 label))

#print axioms sourceExceptionalPath_forwardSeed_unique
#print axioms sourceExceptionalPath_b2_only_seed
#print axioms entry_path_prependUntilB2
#print axioms entry_core_cut
#print axioms firstB2SourceBoundary_all
#print axioms canonicalSourceRecoverable_all
#print axioms entryRootAttachmentCarrierCode_injective_all
#print axioms fullExceptionalSource_sum_le_strictCarrier
#print axioms exceptionalSourceCodes_sum_le_strictCarrier
#print axioms exceptionalSourceCodes_sum_le_strictRelaxed
#print axioms exceptionalSourceCodes_sum_le_strictTree_mul_XiR_sq

end YMGap.Continuum.XiExceptionalCanonicalStrictSourceBoundaryAll
