/-
# Structural reconstruction of the exceptional source trunk boundary

This module separates the purely structural half of the first-`b2` source
decoder.  Both terminating normalizers add only outer `attach` constructors,
so every terminal source tree is its original walk core followed by one
ordered attachment suffix.  Therefore a first-`b2` cut that recovers the
core automatically round-trips the complete old occurrence-tree code.
-/

import YMGap.Continuum.XiExceptionalCanonicalStrictSourceFiber

namespace YMGap.Continuum.XiExceptionalCanonicalStrictSourceBoundary

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier
open YMGap.Continuum.XiExceptionalOccurrenceTreeCodes
open YMGap.Continuum.XiExceptionalOccurrenceTreeWeight
open YMGap.Continuum.XiExceptionalCrossPairTreeNormalization
open YMGap.Continuum.XiExceptionalTreeBackgroundNormalization
open YMGap.Continuum.XiExceptionalSourceTreeCarrier
open YMGap.Continuum.XiExceptionalSourceTreeFiber
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier
open YMGap.Continuum.XiExceptionalCanonicalStrictSourceFiber

variable {L : Lattice} [DecidableEq L.Plaquette]

/-! ## Old codes in outer-attachment normal form -/

def OuterAttachNormal {N : Nat} (code : OccTreeCode N) : Prop :=
  attachAll (OccTreeCode.core code) (OccTreeCode.attachments code) = code

theorem attachAll_append {N : Nat} (tree : OccTreeCode N) :
    ∀ first second,
      attachAll tree (first ++ second) =
        attachAll (attachAll tree first) second
  | [], second => rfl
  | edge :: rest, second => by
      rcases edge with ⟨parent, child⟩
      change attachAll (.attach tree parent child) (rest ++ second) = _
      exact attachAll_append (.attach tree parent child) rest second

theorem OccTreeCode.outerAttachNormal_attach {N : Nat}
    (code : OccTreeCode N) (parent child : Nat)
    (hnormal : OuterAttachNormal code) :
    OuterAttachNormal (OccTreeCode.attach code parent child) := by
  unfold OuterAttachNormal at hnormal ⊢
  simp only [OccTreeCode.core, OccTreeCode.attachments]
  rw [attachAll_append, hnormal]
  rfl

theorem OTree.toCode_outerAttachNormal_ofWalk
    {N : Nat} {edge : Nat → Nat → Bool} {x y : Nat}
    (walk : CWalk edge x y) :
    OuterAttachNormal (OTree.toCode (N := N) (OTree.ofWalk walk)) := by
  unfold OuterAttachNormal
  rw [OTree.toCode_core_ofWalk, OTree.toCode_attachments_ofWalk]
  rfl

theorem OTree.toCode_outerAttachNormal_attach
    {N : Nat} {edge : Nat → Nat → Bool} {root : Nat}
    (tree : OTree edge root) (parent child : Nat)
    (hedge : edge parent child = true)
    (hnormal : OuterAttachNormal (OTree.toCode (N := N) tree)) :
    OuterAttachNormal (OTree.toCode (N := N)
      (OTree.attach tree parent child hedge)) :=
  OccTreeCode.outerAttachNormal_attach _ parent child hnormal

theorem CrossTreeState.exhaust_outerAttachNormal
    {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root)
    (hnormal : OuterAttachNormal (OTree.toCode (N := Gamma.length)
      state.tree)) :
    OuterAttachNormal (OTree.toCode (N := Gamma.length)
      state.exhaust.tree) := by
  rw [CrossTreeState.exhaust]
  split
  next hcross =>
    apply CrossTreeState.exhaust_outerAttachNormal (state.step hcross)
    let pair := state.selection hcross
    let u := pair.leftIndex
    let v := pair.rightIndex
    let pivot := firstConflictIndex Gamma state.tree.vertices u
    change OuterAttachNormal (OTree.toCode (N := Gamma.length)
      (state.tree.attachTwo pivot u v _ _))
    unfold OTree.attachTwo
    apply OTree.toCode_outerAttachNormal_attach
    apply OTree.toCode_outerAttachNormal_attach
    exact hnormal
  next _ => exact hnormal
termination_by state.potential
decreasing_by apply CrossTreeState.step_potential_lt

theorem TreeBackgroundState.exhaust_outerAttachNormal
    {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root)
    (hnormal : OuterAttachNormal (OTree.toCode (N := Gamma.length)
      state.tree)) :
    OuterAttachNormal (OTree.toCode (N := Gamma.length)
      state.exhaust.tree) := by
  rw [TreeBackgroundState.exhaust]
  split
  next hcheck =>
    apply TreeBackgroundState.exhaust_outerAttachNormal (state.step hcheck)
    let u := state.selected
    let pivot := firstConflictIndex Gamma state.tree.vertices u
    change OuterAttachNormal (OTree.toCode (N := Gamma.length)
      (OTree.attach state.tree pivot u _))
    exact OTree.toCode_outerAttachNormal_attach
      state.tree pivot u _ hnormal
  next _ => exact hnormal
termination_by state.potential
decreasing_by apply TreeBackgroundState.step_potential_lt

theorem entryOccurrenceTreeCode_outerAttachNormal
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OuterAttachNormal
      (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry).tree := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let walk := conflictWalkOfDisagreement Gamma
    (bitMask pair.1) (bitMask pair.2) path.indexWalk
  have hinitial : OuterAttachNormal (OTree.toCode (N := Gamma.length)
      (entryCrossTreeState Gamma qP b1 b2 entry).tree) := by
    change OuterAttachNormal (OTree.toCode (N := Gamma.length)
      (OTree.ofWalk walk))
    exact OTree.toCode_outerAttachNormal_ofWalk walk
  have hcross := CrossTreeState.exhaust_outerAttachNormal
    (entryCrossTreeState Gamma qP b1 b2 entry) hinitial
  have hbackground : OuterAttachNormal (OTree.toCode (N := Gamma.length)
      (entryTreeBackgroundState Gamma qP b1 b2 entry).tree) :=
    hcross
  exact TreeBackgroundState.exhaust_outerAttachNormal
    (entryTreeBackgroundState Gamma qP b1 b2 entry) hbackground

/-! ## Ordered-edge decomposition and decoder round trip -/

theorem orderedAttachments_eq_core_append_attachments {N : Nat} :
    ∀ code : OccTreeCode N,
      occTreeCodeOrderedAttachments code =
        occTreeCodeOrderedAttachments (OccTreeCode.core code) ++
          OccTreeCode.attachments code
  | .single _ => rfl
  | .prepend root tree => by
      simp only [occTreeCodeOrderedAttachments, OccTreeCode.core,
        OccTreeCode.attachments, List.cons_append]
      rw [orderedAttachments_eq_core_append_attachments tree]
      congr 1
      induction tree with
      | single _ => rfl
      | prepend _ _ => rfl
      | attach tree _ _ ih => exact ih
  | .attach tree parent child => by
      simp only [occTreeCodeOrderedAttachments, OccTreeCode.core,
        OccTreeCode.attachments]
      rw [orderedAttachments_eq_core_append_attachments tree,
        List.append_assoc]

theorem core_height_eq_orderedAttachments_length_add_one {N : Nat} :
    ∀ code : OccTreeCode N,
      (OccTreeCode.core code).height =
        (occTreeCodeOrderedAttachments
          (OccTreeCode.core code)).length + 1
  | .single _ => rfl
  | .prepend root tree => by
      simp only [OccTreeCode.core, OccTreeCode.height,
        occTreeCodeOrderedAttachments, List.length_cons]
      rw [core_height_eq_orderedAttachments_length_add_one tree]
  | .attach tree parent child =>
      core_height_eq_orderedAttachments_length_add_one tree

theorem drop_length_append {α : Type} : ∀ (pre suffix : List α),
    (pre ++ suffix).drop pre.length = suffix
  | [], suffix => rfl
  | _ :: pre, suffix => drop_length_append pre suffix

theorem firstB2CanonicalTreeDecoder_eq_of_core_cut
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (code : OccTreeCode Gamma.length)
    (hnormal : OuterAttachNormal code)
    (hcut : prependUntilB2 Gamma b2 (treeCodeRoot code)
        (occTreeCodeOrderedAttachments code) = OccTreeCode.core code) :
    firstB2CanonicalTreeDecoder Gamma b2
        (occTreeCodeToRootAttachment code) = code := by
  unfold firstB2CanonicalTreeDecoder occTreeCodeToRootAttachment
  dsimp only
  rw [hcut]
  have hheight := core_height_eq_orderedAttachments_length_add_one code
  have hordered := orderedAttachments_eq_core_append_attachments code
  rw [hordered]
  have hdrop :
      (occTreeCodeOrderedAttachments (OccTreeCode.core code) ++
        OccTreeCode.attachments code).drop
          ((OccTreeCode.core code).height - 1) =
        OccTreeCode.attachments code := by
    rw [show (OccTreeCode.core code).height - 1 =
        (occTreeCodeOrderedAttachments (OccTreeCode.core code)).length by
      omega]
    exact drop_length_append _ _
  rw [hdrop]
  exact hnormal

theorem oTree_toCode_root
    {N root : Nat} {edge : Nat → Nat → Bool} :
    ∀ tree : OTree edge root,
      treeCodeRoot (OTree.toCode (N := N) tree) = root
  | .single _ => rfl
  | .prepend _ _ => rfl
  | .attach tree _ _ _ => oTree_toCode_root tree

theorem oTree_toCode_orderedAttachments
    {N root : Nat} {edge : Nat → Nat → Bool} :
    ∀ tree : OTree edge root,
      occTreeCodeOrderedAttachments (OTree.toCode (N := N) tree) =
        oTreeOrderedAttachments tree
  | .single _ => rfl
  | .prepend _ tree => by
      simp only [OTree.toCode, occTreeCodeOrderedAttachments,
        oTreeOrderedAttachments]
      rw [oTree_toCode_root tree,
        oTree_toCode_orderedAttachments tree]
  | .attach tree parent child hedge => by
      simp only [OTree.toCode, occTreeCodeOrderedAttachments,
        oTreeOrderedAttachments]
      rw [oTree_toCode_orderedAttachments tree]

theorem occTreeCodeToRootAttachment_toCode
    {N root : Nat} {edge : Nat → Nat → Bool} :
    ∀ tree : OTree edge root,
      occTreeCodeToRootAttachment (OTree.toCode (N := N) tree) =
        oTreeToRootAttachmentCode (N := N) tree
  | .single _ => rfl
  | .prepend _ tree => by
      simp only [OTree.toCode, occTreeCodeToRootAttachment, treeCodeRoot,
        occTreeCodeOrderedAttachments, oTreeToRootAttachmentCode,
        oTreeOrderedAttachments]
      rw [oTree_toCode_root tree,
        oTree_toCode_orderedAttachments tree]
  | .attach tree parent child hedge => by
      simp only [OTree.toCode, occTreeCodeToRootAttachment, treeCodeRoot,
        occTreeCodeOrderedAttachments, oTreeToRootAttachmentCode,
        oTreeOrderedAttachments]
      rw [oTree_toCode_root tree,
        oTree_toCode_orderedAttachments tree]

theorem firstB2SourceBoundary_of_core_cut
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hcut : prependUntilB2 Gamma b2
        (entryRootAttachmentCarrierCode Gamma qP b1 b2 entry).tree.root
        (entryRootAttachmentCarrierCode Gamma qP b1 b2 entry).tree.attachments =
      OccTreeCode.core
        (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry).tree) :
    FirstB2SourceBoundary Gamma qP b1 b2 entry := by
  let old := (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry).tree
  have hnormal := entryOccurrenceTreeCode_outerAttachNormal
    Gamma qP b1 b2 entry
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
  unfold FirstB2SourceBoundary
  rw [hcanonical]
  apply firstB2CanonicalTreeDecoder_eq_of_core_cut
    Gamma b2 old hnormal
  simpa [hcanonical] using hcut

#print axioms attachAll_append
#print axioms CrossTreeState.exhaust_outerAttachNormal
#print axioms TreeBackgroundState.exhaust_outerAttachNormal
#print axioms entryOccurrenceTreeCode_outerAttachNormal
#print axioms orderedAttachments_eq_core_append_attachments
#print axioms firstB2CanonicalTreeDecoder_eq_of_core_cut
#print axioms occTreeCodeToRootAttachment_toCode
#print axioms firstB2SourceBoundary_of_core_cut

end YMGap.Continuum.XiExceptionalCanonicalStrictSourceBoundary
