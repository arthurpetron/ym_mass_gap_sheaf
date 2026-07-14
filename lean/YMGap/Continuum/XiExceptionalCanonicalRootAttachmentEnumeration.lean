/-
# Duplicate-free finite enumeration of canonical root-attachment carriers

Attachment lists are enumerated at exact length and then concatenated across
disjoint length layers.  Pairing them with one root and two occurrence masks
gives a source-independent, duplicate-free finite carrier.  Every terminal
canonical source code belongs to the height-`|Gamma|` enumeration.
-/

import YMGap.Continuum.XiExceptionalCanonicalRootAttachmentImage
import YMGap.Continuum.XiExceptionalTargetNodup

namespace YMGap.Continuum.XiExceptionalCanonicalRootAttachmentEnumeration

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier
open YMGap.Continuum.XiExceptionalOccurrenceTreeMajorant
open YMGap.Continuum.XiExceptionalSourceTreeCarrier
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentImage
open YMGap.Continuum.XiExceptionalTargetNodup

variable {L : Lattice} [DecidableEq L.Plaquette]

/-! ## Exact attachment-list layers -/

def occurrenceIndexPairs (N : Nat) : List (Nat × Nat) :=
  (occurrenceIndices N).flatMap (fun parent =>
    (occurrenceIndices N).map (fun child => (parent, child)))

theorem occurrenceIndexPairs_complete {N parent child : Nat}
    (hparent : parent < N) (hchild : child < N) :
    (parent, child) ∈ occurrenceIndexPairs N := by
  unfold occurrenceIndexPairs
  apply List.mem_flatMap.mpr
  exact ⟨parent, occurrenceIndices_complete hparent,
    List.mem_map.mpr
      ⟨child, occurrenceIndices_complete hchild, rfl⟩⟩

theorem occurrenceIndexPairs_nodup (N : Nat) :
    (occurrenceIndexPairs N).Nodup := by
  unfold occurrenceIndexPairs
  exact nodup_cartesian (occurrenceIndices N) (occurrenceIndices N)
    (occurrenceIndices_nodup N) (occurrenceIndices_nodup N)

def attachmentListsExact (N : Nat) : Nat → List (List (Nat × Nat))
  | 0 => [[]]
  | fuel + 1 =>
      (occurrenceIndexPairs N).flatMap (fun edge =>
        (attachmentListsExact N fuel).map (fun rest => edge :: rest))

def attachmentListsUpTo (N : Nat) : Nat → List (List (Nat × Nat))
  | 0 => attachmentListsExact N 0
  | fuel + 1 =>
      attachmentListsUpTo N fuel ++ attachmentListsExact N (fuel + 1)

theorem mem_attachmentListsExact_length {N fuel : Nat} :
    ∀ {edges : List (Nat × Nat)},
      edges ∈ attachmentListsExact N fuel → edges.length = fuel := by
  induction fuel with
  | zero =>
      intro edges hmem
      simp [attachmentListsExact] at hmem
      subst edges
      rfl
  | succ fuel ih =>
      intro edges hmem
      unfold attachmentListsExact at hmem
      obtain ⟨edge, _, hblock⟩ := List.mem_flatMap.mp hmem
      obtain ⟨rest, hrest, rfl⟩ := List.mem_map.mp hblock
      simp only [List.length_cons]
      rw [ih hrest]

theorem attachmentListsExact_complete (N : Nat) :
    ∀ edges : List (Nat × Nat),
      (∀ edge, edge ∈ edges → edge.1 < N ∧ edge.2 < N) →
      edges ∈ attachmentListsExact N edges.length
  | [], _ => by simp [attachmentListsExact]
  | edge :: rest, hbound => by
      unfold attachmentListsExact
      apply List.mem_flatMap.mpr
      refine ⟨edge,
        occurrenceIndexPairs_complete
          (hbound edge List.mem_cons_self).1
          (hbound edge List.mem_cons_self).2, ?_⟩
      apply List.mem_map.mpr
      refine ⟨rest, attachmentListsExact_complete N rest ?_, rfl⟩
      intro e he
      exact hbound e (List.mem_cons_of_mem edge he)

theorem attachmentListsExact_nodup (N : Nat) :
    ∀ fuel, (attachmentListsExact N fuel).Nodup
  | 0 => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | fuel + 1 => by
      unfold attachmentListsExact
      apply nodup_flatMap_map₂ (fun edge rest => edge :: rest)
        (occurrenceIndexPairs N) (attachmentListsExact N fuel)
        (occurrenceIndexPairs_nodup N)
        (attachmentListsExact_nodup N fuel)
      intro edge _ rest _ edge' _ rest' _ h
      injection h with hedge hrest
      exact ⟨hedge, hrest⟩

theorem mem_attachmentListsUpTo_length_le {N fuel : Nat} :
    ∀ {edges : List (Nat × Nat)},
      edges ∈ attachmentListsUpTo N fuel → edges.length ≤ fuel := by
  induction fuel with
  | zero =>
      intro edges hmem
      have hlen := mem_attachmentListsExact_length hmem
      omega
  | succ fuel ih =>
      intro edges hmem
      unfold attachmentListsUpTo at hmem
      rcases List.mem_append.mp hmem with hprev | hlast
      · exact Nat.le_trans (ih hprev) (Nat.le_succ fuel)
      · have hlen := mem_attachmentListsExact_length hlast
        omega

theorem attachmentListsUpTo_nodup (N : Nat) :
    ∀ fuel, (attachmentListsUpTo N fuel).Nodup
  | 0 => attachmentListsExact_nodup N 0
  | fuel + 1 => by
      unfold attachmentListsUpTo
      apply List.nodup_append.mpr
      refine ⟨attachmentListsUpTo_nodup N fuel,
        attachmentListsExact_nodup N (fuel + 1), ?_⟩
      intro a ha b hb hab
      have haLen := mem_attachmentListsUpTo_length_le ha
      have hbLen := mem_attachmentListsExact_length hb
      rw [hab, hbLen] at haLen
      omega

theorem mem_attachmentListsUpTo_of_le {N fuel : Nat}
    {edges : List (Nat × Nat)} (hbound :
      ∀ edge, edge ∈ edges → edge.1 < N ∧ edge.2 < N)
    (hlen : edges.length ≤ fuel) :
    edges ∈ attachmentListsUpTo N fuel := by
  induction fuel with
  | zero =>
      have hzero : edges.length = 0 := Nat.eq_zero_of_le_zero hlen
      have hedgeNil : edges = [] := List.length_eq_zero_iff.mp hzero
      subst edges
      simp [attachmentListsUpTo, attachmentListsExact]
  | succ fuel ih =>
      unfold attachmentListsUpTo
      by_cases heq : edges.length = fuel + 1
      · exact List.mem_append_right _
          (heq ▸ attachmentListsExact_complete N edges hbound)
      · exact List.mem_append_left _ (ih (by omega))

/-! ## Trees and the two-mask carrier -/

def rootAttachmentTreeCodes (N fuel : Nat) :
    List (RootAttachmentTreeCode N) :=
  (occurrenceIndices N).flatMap (fun root =>
    (attachmentListsUpTo N fuel).map (fun attachments =>
      RootAttachmentTreeCode.mk root attachments))

theorem rootAttachmentTreeCodes_nodup (N fuel : Nat) :
    (rootAttachmentTreeCodes N fuel).Nodup := by
  unfold rootAttachmentTreeCodes
  apply nodup_flatMap_map₂ RootAttachmentTreeCode.mk
    (occurrenceIndices N) (attachmentListsUpTo N fuel)
    (occurrenceIndices_nodup N) (attachmentListsUpTo_nodup N fuel)
  intro root _ attachments _ root' _ attachments' _ h
  injection h with hroot hatt
  exact ⟨hroot, hatt⟩

theorem RootAttachmentTreeCode.mem_rootAttachmentTreeCodes
    {N fuel : Nat} (code : RootAttachmentTreeCode N)
    (hroot : code.root < N)
    (hbound : ∀ edge, edge ∈ code.attachments →
      edge.1 < N ∧ edge.2 < N)
    (hlen : code.attachments.length ≤ fuel) :
    code ∈ rootAttachmentTreeCodes N fuel := by
  unfold rootAttachmentTreeCodes
  apply List.mem_flatMap.mpr
  refine ⟨code.root, occurrenceIndices_complete hroot, ?_⟩
  exact List.mem_map.mpr
    ⟨code.attachments,
      mem_attachmentListsUpTo_of_le hbound hlen, by cases code; rfl⟩

def rootAttachmentCarrierCodes (N fuel : Nat) :
    List (RootAttachmentCarrierCode N) :=
  (rootAttachmentTreeCodes N fuel).flatMap (fun tree =>
    (maskPairs N).map (fun masks =>
      RootAttachmentCarrierCode.mk tree masks.1 masks.2))

theorem rootAttachmentCarrierCodes_nodup (N fuel : Nat) :
    (rootAttachmentCarrierCodes N fuel).Nodup := by
  unfold rootAttachmentCarrierCodes
  apply nodup_flatMap_map₂
    (fun tree masks =>
      RootAttachmentCarrierCode.mk tree masks.1 masks.2)
    (rootAttachmentTreeCodes N fuel) (maskPairs N)
    (rootAttachmentTreeCodes_nodup N fuel) (maskPairs_nodup N)
  intro tree _ masks _ tree' _ masks' _ h
  have htree := congrArg RootAttachmentCarrierCode.tree h
  have hbackground := congrArg RootAttachmentCarrierCode.background h
  have hexternal := congrArg RootAttachmentCarrierCode.external h
  cases masks
  cases masks'
  exact ⟨htree, Prod.ext hbackground hexternal⟩

theorem RootAttachmentCarrierCode.mem_rootAttachmentCarrierCodes
    {N fuel : Nat} (code : RootAttachmentCarrierCode N)
    (htree : code.tree ∈ rootAttachmentTreeCodes N fuel) :
    code ∈ rootAttachmentCarrierCodes N fuel := by
  unfold rootAttachmentCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨code.tree, htree, ?_⟩
  exact List.mem_map.mpr
    ⟨(code.background, code.external), maskPairs_complete _,
      by cases code; rfl⟩

/-! ## Every normalized source code is in the finite enumeration -/

theorem oTreeOrderedAttachments_length_add_one
    {edge : Nat → Nat → Bool} {root : Nat} :
    ∀ tree : OTree edge root,
      (oTreeOrderedAttachments tree).length + 1 = tree.vertices.length
  | .single _ => rfl
  | .prepend _ tree => by
      simp only [oTreeOrderedAttachments, List.length_cons, OTree.vertices]
      rw [oTreeOrderedAttachments_length_add_one tree]
  | .attach tree _ _ _ => by
      simp only [oTreeOrderedAttachments, List.length_append,
        List.length_cons, List.length_nil, Nat.add_zero, OTree.vertices]
      rw [oTreeOrderedAttachments_length_add_one tree]

theorem entryRootAttachmentCarrierCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    entryRootAttachmentCarrierCode Gamma qP b1 b2 entry ∈
      rootAttachmentCarrierCodes Gamma.length Gamma.length := by
  let final := entryTreeExhaust Gamma qP b1 b2 entry
  apply RootAttachmentCarrierCode.mem_rootAttachmentCarrierCodes
  apply RootAttachmentTreeCode.mem_rootAttachmentTreeCodes
  · exact final.vertices_bound _ (OTree.root_mem final.tree)
  · intro edge hedge
    rcases edge with ⟨parent, child⟩
    have hp := oTreeOrderedAttachments_valid final.tree final.valid
      parent child hedge
    exact ⟨final.vertices_bound parent hp.1,
      final.vertices_bound child hp.2.1⟩
  · have hvertices := OTree.vertices_length_le_ambient
      Gamma final.tree final.nodup final.vertices_bound
    have hlen := oTreeOrderedAttachments_length_add_one final.tree
    change (oTreeOrderedAttachments final.tree).length ≤ Gamma.length
    omega

#print axioms occurrenceIndexPairs_nodup
#print axioms attachmentListsExact_complete
#print axioms attachmentListsExact_nodup
#print axioms attachmentListsUpTo_nodup
#print axioms rootAttachmentTreeCodes_nodup
#print axioms rootAttachmentCarrierCodes_nodup
#print axioms oTreeOrderedAttachments_length_add_one
#print axioms entryRootAttachmentCarrierCode_mem

end YMGap.Continuum.XiExceptionalCanonicalRootAttachmentEnumeration
