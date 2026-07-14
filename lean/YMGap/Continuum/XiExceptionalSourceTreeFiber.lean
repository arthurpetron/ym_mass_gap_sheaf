/-
# Decoding and fibres of the exceptional source-tree carrier

The tree normalizer erases residual bits only after recording their
occurrence indices as fresh tree attachments.  This module begins the
constructive inverse: it records the attachment spine of the proof-free tree
code and supplies exact restoration operations for cleared occurrence masks.
-/

import YMGap.Continuum.XiExceptionalSourceTreeCarrier
import YMGap.Continuum.XiExceptionalSourcePartition

namespace YMGap.Continuum.XiExceptionalSourceTreeFiber

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalFiberwiseInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalBranchRouter
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalCustomCarrier
open YMGap.Continuum.XiExceptionalRoutedExactWeight
open YMGap.Continuum.XiExceptionalPathSafeInjection
open YMGap.Continuum.XiExceptionalRoutedExternalSplit
open YMGap.Continuum.XiExceptionalFirstConflictPotential
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalMergedResidualCarrier
open YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier
open YMGap.Continuum.XiExceptionalOccurrenceTreeCodes
open YMGap.Continuum.XiExceptionalOccurrenceTreeMajorant
open YMGap.Continuum.XiExceptionalCrossPairTreeNormalization
open YMGap.Continuum.XiExceptionalTreeBackgroundNormalization
open YMGap.Continuum.XiExceptionalSourceTreeCarrier
open YMGap.Continuum.XiExceptionalSourcePartition

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## Exact restoration of cleared finite masks -/

def restoreAt : {n : Nat} → OccBitVec n → Nat → OccBitVec n
  | 0, .nil, _ => .nil
  | _ + 1, .cons _ tail, 0 => .cons true tail
  | _ + 1, .cons head tail, i + 1 =>
      .cons head (restoreAt tail i)

theorem restoreAt_clearResidualAt :
    ∀ {n : Nat} (bits : OccBitVec n) (i : Nat),
      bits.at i = true → restoreAt (clearResidualAt bits i) i = bits
  | 0, .nil, _, htrue => by cases htrue
  | _ + 1, .cons head tail, 0, htrue => by
      change head = true at htrue
      subst head
      rfl
  | _ + 1, .cons head tail, i + 1, htrue => by
      simp only [clearResidualAt, restoreAt]
      congr 1
      exact restoreAt_clearResidualAt tail i htrue

theorem clearResidualAt_at_of_ne :
    ∀ {n : Nat} (bits : OccBitVec n) (selected k : Nat),
      k ≠ selected →
        (clearResidualAt bits selected).at k = bits.at k
  | 0, .nil, _, _, _ => rfl
  | _ + 1, .cons _ _, 0, 0, hne => False.elim (hne rfl)
  | _ + 1, .cons _ _, 0, _ + 1, _ => rfl
  | _ + 1, .cons _ _, _ + 1, 0, _ => rfl
  | _ + 1, .cons _ tail, selected + 1, k + 1, hne =>
      clearResidualAt_at_of_ne tail selected k
        (fun h => hne (congrArg Nat.succ h))

theorem restoreAt_at_self_true :
    ∀ {n : Nat} (bits : OccBitVec n) (i : Nat), i < n →
      (restoreAt bits i).at i = true
  | 0, .nil, _, hi => by omega
  | _ + 1, .cons _ _, 0, _ => rfl
  | _ + 1, .cons _ tail, i + 1, hi =>
      restoreAt_at_self_true tail i (by omega)

theorem restoreAt_at_of_ne :
    ∀ {n : Nat} (bits : OccBitVec n) (selected k : Nat),
      k ≠ selected → (restoreAt bits selected).at k = bits.at k
  | 0, .nil, _, _, _ => rfl
  | _ + 1, .cons _ _, 0, 0, hne => False.elim (hne rfl)
  | _ + 1, .cons _ _, 0, _ + 1, _ => rfl
  | _ + 1, .cons _ _, _ + 1, 0, _ => rfl
  | _ + 1, .cons _ tail, selected + 1, k + 1, hne =>
      restoreAt_at_of_ne tail selected k
        (fun h => hne (congrArg Nat.succ h))

theorem restore_union_after_cross_clear
    {n : Nat} (left right : OccBitVec n) (u v : Nat)
    (hu : u < n) (hv : v < n)
    (hleft : left.at u = true) (hright : right.at v = true) :
    restoreAt
        (restoreAt
          (unionBits (clearResidualAt left u)
            (clearResidualAt right v)) v) u =
      unionBits left right := by
  apply BitVec.ext
  intro k
  by_cases hk : k < n
  · by_cases hku : k = u
    · subst k
      rw [restoreAt_at_self_true _ u hu]
      rw [unionBits_at, hleft]
      rfl
    · rw [restoreAt_at_of_ne _ u k hku]
      by_cases hkv : k = v
      · subst k
        rw [restoreAt_at_self_true _ v hv]
        rw [unionBits_at, hright, Bool.or_true]
      · rw [restoreAt_at_of_ne _ v k hkv,
          unionBits_at, unionBits_at,
          clearResidualAt_at_of_ne left u k hku,
          clearResidualAt_at_of_ne right v k hkv]
  · have hge : n ≤ k := by omega
    rw [bitVec_at_false_of_ge _ k hge,
      bitVec_at_false_of_ge _ k hge]

def restoreMany {n : Nat} (bits : OccBitVec n) : List Nat → OccBitVec n
  | [] => bits
  | i :: indices => restoreAt (restoreMany bits indices) i

@[simp] theorem restoreMany_nil {n : Nat} (bits : OccBitVec n) :
    restoreMany bits [] = bits := rfl

@[simp] theorem restoreMany_cons {n : Nat} (bits : OccBitVec n)
    (i : Nat) (indices : List Nat) :
    restoreMany bits (i :: indices) =
      restoreAt (restoreMany bits indices) i := rfl

/-! ## The proof-free attachment spine -/

def OccTreeCode.core {N : Nat} : OccTreeCode N → OccTreeCode N
  | .single root => .single root
  | .prepend root tree => .prepend root (OccTreeCode.core tree)
  | .attach tree _ _ => OccTreeCode.core tree

def OccTreeCode.attachments {N : Nat} :
    OccTreeCode N → List (Nat × Nat)
  | .single _ => []
  | .prepend _ tree => OccTreeCode.attachments tree
  | .attach tree parent child =>
      OccTreeCode.attachments tree ++ [(parent, child)]

def OccTreeCode.attachmentChildren {N : Nat} (code : OccTreeCode N) :
    List Nat :=
  (OccTreeCode.attachments code).map Prod.snd

theorem OTree.toCode_core_ofWalk
    {N : Nat} {edge : Nat → Nat → Bool} {x y : Nat}
    (walk : CWalk edge x y) :
    OccTreeCode.core (OTree.toCode (N := N) (OTree.ofWalk walk)) =
      OTree.toCode (N := N) (OTree.ofWalk walk) := by
  induction walk with
  | single _ => rfl
  | cons _ rest ih =>
      simp only [OTree.ofWalk, OTree.toCode, OccTreeCode.core]
      rw [ih]

@[simp] theorem OTree.toCode_attachments_ofWalk
    {N : Nat} {edge : Nat → Nat → Bool} {x y : Nat}
    (walk : CWalk edge x y) :
    OccTreeCode.attachments
      (OTree.toCode (N := N) (OTree.ofWalk walk)) = [] := by
  induction walk with
  | single _ => rfl
  | cons _ rest ih =>
      simpa [OTree.ofWalk, OTree.toCode, OccTreeCode.attachments] using ih

@[simp] theorem OTree.toCode_core_attach
    {N : Nat} {edge : Nat → Nat → Bool} {root : Nat}
    (tree : OTree edge root) (parent child : Nat)
    (hedge : edge parent child = true) :
    OccTreeCode.core
        (OTree.toCode (N := N) (OTree.attach tree parent child hedge)) =
      OccTreeCode.core (OTree.toCode (N := N) tree) := rfl

@[simp] theorem OTree.toCode_attachments_attach
    {N : Nat} {edge : Nat → Nat → Bool} {root : Nat}
    (tree : OTree edge root) (parent child : Nat)
    (hedge : edge parent child = true) :
    OccTreeCode.attachments
        (OTree.toCode (N := N) (OTree.attach tree parent child hedge)) =
      OccTreeCode.attachments (OTree.toCode (N := N) tree) ++
        [(parent, child)] := rfl

@[simp] theorem OTree.toCode_attachmentChildren_attach
    {N : Nat} {edge : Nat → Nat → Bool} {root : Nat}
    (tree : OTree edge root) (parent child : Nat)
    (hedge : edge parent child = true) :
    OccTreeCode.attachmentChildren
        (OTree.toCode (N := N) (OTree.attach tree parent child hedge)) =
      OccTreeCode.attachmentChildren (OTree.toCode (N := N) tree) ++
        [child] := by
  simp [OccTreeCode.attachmentChildren, OccTreeCode.attachments]

/-! ## Selection traces of the two terminating normalizers -/

def CrossTreeState.traceChildren
    {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root) : List Nat :=
  if hcross : state.crossCheckB = false then
    let pair := state.selection hcross
    pair.leftIndex :: pair.rightIndex ::
      CrossTreeState.traceChildren (state.step hcross)
  else []
termination_by state.potential
decreasing_by apply CrossTreeState.step_potential_lt

def TreeBackgroundState.traceChildren
    {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root) : List Nat :=
  if hcheck : state.checkB = false then
    state.selected :: TreeBackgroundState.traceChildren (state.step hcheck)
  else []
termination_by state.potential
decreasing_by apply TreeBackgroundState.step_potential_lt

theorem CrossTreeState.exhaust_core_eq
    {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root) :
    OccTreeCode.core
        (OTree.toCode (N := Gamma.length) state.exhaust.tree) =
      OccTreeCode.core (OTree.toCode (N := Gamma.length) state.tree) := by
  rw [CrossTreeState.exhaust]
  split
  next hcross =>
    exact (CrossTreeState.exhaust_core_eq (state.step hcross)).trans rfl
  next _ => rfl
termination_by state.potential
decreasing_by apply CrossTreeState.step_potential_lt

theorem TreeBackgroundState.exhaust_core_eq
    {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root) :
    OccTreeCode.core
        (OTree.toCode (N := Gamma.length) state.exhaust.tree) =
      OccTreeCode.core (OTree.toCode (N := Gamma.length) state.tree) := by
  rw [TreeBackgroundState.exhaust]
  split
  next hcheck =>
    exact (TreeBackgroundState.exhaust_core_eq (state.step hcheck)).trans rfl
  next _ => rfl
termination_by state.potential
decreasing_by apply TreeBackgroundState.step_potential_lt

theorem CrossTreeState.exhaust_attachmentChildren
    {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root) :
    OccTreeCode.attachmentChildren
        (OTree.toCode (N := Gamma.length) state.exhaust.tree) =
      OccTreeCode.attachmentChildren
          (OTree.toCode (N := Gamma.length) state.tree) ++
        CrossTreeState.traceChildren state := by
  rw [CrossTreeState.exhaust, CrossTreeState.traceChildren]
  split
  next hcross =>
    let pair := state.selection hcross
    have ih := CrossTreeState.exhaust_attachmentChildren
      (state.step hcross)
    rw [ih]
    simp only [CrossTreeState.step, OTree.attachTwo,
      OTree.toCode_attachmentChildren_attach]
    change (_ ++ [pair.leftIndex] ++ [pair.rightIndex]) ++
        CrossTreeState.traceChildren (state.step hcross) =
      _ ++ pair.leftIndex :: pair.rightIndex ::
        CrossTreeState.traceChildren (state.step hcross)
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  next _ => simp
termination_by state.potential
decreasing_by apply CrossTreeState.step_potential_lt

theorem TreeBackgroundState.exhaust_attachmentChildren
    {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root) :
    OccTreeCode.attachmentChildren
        (OTree.toCode (N := Gamma.length) state.exhaust.tree) =
      OccTreeCode.attachmentChildren
          (OTree.toCode (N := Gamma.length) state.tree) ++
        TreeBackgroundState.traceChildren state := by
  rw [TreeBackgroundState.exhaust, TreeBackgroundState.traceChildren]
  split
  next hcheck =>
    have ih := TreeBackgroundState.exhaust_attachmentChildren
      (state.step hcheck)
    rw [ih]
    simp only [TreeBackgroundState.step,
      OTree.toCode_attachmentChildren_attach]
    change (_ ++ [state.selected]) ++
        TreeBackgroundState.traceChildren (state.step hcheck) =
      _ ++ state.selected ::
        TreeBackgroundState.traceChildren (state.step hcheck)
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  next _ => simp
termination_by state.potential
decreasing_by apply TreeBackgroundState.step_potential_lt

/-! ## A phase decoder on the attachment children -/

def splitAttachmentChildren (safe : Nat → Bool) :
    List Nat → List Nat × List Nat
  | [] => ([], [])
  | u :: rest =>
      if safe u then (u :: rest, [])
      else match rest with
        | [] => ([], [u])
        | v :: tail =>
            let decoded := splitAttachmentChildren safe tail
            (decoded.1, u :: v :: decoded.2)

inductive CrossTracePattern (safe : Nat → Bool) : List Nat → Prop
  | nil : CrossTracePattern safe []
  | pair (u v : Nat) (tail : List Nat) (hu : safe u = false)
      (htail : CrossTracePattern safe tail) :
      CrossTracePattern safe (u :: v :: tail)

theorem splitAttachmentChildren_of_patterns
    (safe : Nat → Bool) (cross background : List Nat)
    (hcross : CrossTracePattern safe cross)
    (hbackground : ∀ i, i ∈ background → safe i = true) :
    splitAttachmentChildren safe (cross ++ background) =
      (background, cross) := by
  induction hcross generalizing background with
  | nil =>
      cases background with
      | nil => rfl
      | cons i rest =>
          simp only [List.nil_append]
          rw [splitAttachmentChildren.eq_def]
          simp only [hbackground i List.mem_cons_self, ↓reduceIte]
  | pair u v tail hu htail ih =>
      simp only [List.cons_append, splitAttachmentChildren, hu,
        Bool.false_eq_true, if_false]
      rw [ih background hbackground]

theorem CrossTreeState.traceChildren_pattern
    {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root) (safe : Nat → Bool)
    (hleft : ∀ i, state.left.at i = true → safe i = false) :
    CrossTracePattern safe (CrossTreeState.traceChildren state) := by
  rw [CrossTreeState.traceChildren]
  split
  next hcross =>
    let pair := state.selection hcross
    apply CrossTracePattern.pair pair.leftIndex pair.rightIndex
    · exact hleft pair.leftIndex pair.left_mem
    · apply CrossTreeState.traceChildren_pattern (state.step hcross) safe
      intro i hi
      exact hleft i (clearResidualAt_submask state.left pair.leftIndex i hi)
  next _ => exact CrossTracePattern.nil
termination_by state.potential
decreasing_by apply CrossTreeState.step_potential_lt

theorem TreeBackgroundState.traceChildren_safe
    {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root) (safe : Nat → Bool)
    (hbackground : ∀ i, state.background.at i = true → safe i = true) :
    ∀ i, i ∈ TreeBackgroundState.traceChildren state →
      safe i = true := by
  rw [TreeBackgroundState.traceChildren]
  split
  next hcheck =>
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hbackground state.selected (state.selected_spec hcheck).2.1
    · apply TreeBackgroundState.traceChildren_safe
        (state.step hcheck) safe _ i hi
      intro j hj
      exact hbackground j
        (clearResidualAt_submask state.background state.selected j hj)
  next _ => intro i hi; cases hi
termination_by state.potential
decreasing_by apply TreeBackgroundState.step_potential_lt

/-! ## Exact mask recovery along the traces -/

theorem CrossTreeState.restoreMany_exhaust_union
    {Gamma : List (Polymer L)} {root : Nat}
    (state : CrossTreeState Gamma root) :
    restoreMany (unionBits state.exhaust.left state.exhaust.right)
        (CrossTreeState.traceChildren state) =
      unionBits state.left state.right := by
  rw [CrossTreeState.exhaust, CrossTreeState.traceChildren]
  split
  next hcross =>
    let pair := state.selection hcross
    have ih := CrossTreeState.restoreMany_exhaust_union
      (state.step hcross)
    simp only [restoreMany_cons]
    rw [ih]
    change restoreAt
        (restoreAt
          (unionBits (clearResidualAt state.left pair.leftIndex)
            (clearResidualAt state.right pair.rightIndex))
          pair.rightIndex) pair.leftIndex =
      unionBits state.left state.right
    exact restore_union_after_cross_clear state.left state.right
      pair.leftIndex pair.rightIndex pair.left_lt pair.right_lt
      pair.left_mem pair.right_mem
  next _ => rfl
termination_by state.potential
decreasing_by apply CrossTreeState.step_potential_lt

theorem TreeBackgroundState.restoreMany_exhaust_background
    {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root) :
    restoreMany state.exhaust.background
        (TreeBackgroundState.traceChildren state) = state.background := by
  rw [TreeBackgroundState.exhaust, TreeBackgroundState.traceChildren]
  split
  next hcheck =>
    have ih := TreeBackgroundState.restoreMany_exhaust_background
      (state.step hcheck)
    simp only [restoreMany_cons]
    rw [ih]
    change restoreAt (clearResidualAt state.background state.selected)
        state.selected = state.background
    exact restoreAt_clearResidualAt state.background state.selected
      (state.selected_spec hcheck).2.1
  next _ => rfl
termination_by state.potential
decreasing_by apply TreeBackgroundState.step_potential_lt

private theorem entryUnsafeLeft_safe_false
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    ∀ i, (entryUnsafeLeftBits Gamma qP b1 b2 entry).at i = true →
      exceptionalPathSafe Gamma qP b1 b2 entry i = false := by
  intro i hbit
  by_cases hi : i < Gamma.length
  · rw [entryUnsafeLeftBits,
      unsafeLeftBits_at (exceptionalPathSafe Gamma qP b1 b2 entry)
        (routedLeftResidual Gamma qP b1 b2 entry) i hi] at hbit
    cases hs : exceptionalPathSafe Gamma qP b1 b2 entry i
    · rfl
    · simp only [hs, Bool.not_true, Bool.false_and] at hbit
      cases hbit
  · have hge : Gamma.length ≤ i := by omega
    rw [bitVec_at_false_of_ge
      (entryUnsafeLeftBits Gamma qP b1 b2 entry) i hge] at hbit
    cases hbit

private theorem entryTreeBackground_safe_true
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    ∀ i, (entryTreeBackground Gamma qP b1 b2 entry).at i = true →
      exceptionalPathSafe Gamma qP b1 b2 entry i = true := by
  intro i hbit
  by_cases hi : i < Gamma.length
  · unfold entryTreeBackground at hbit
    rw [routedBackground_at _ _ i hi] at hbit
    exact ((Bool.and_eq_true _ _).mp hbit).1
  · have hge : Gamma.length ≤ i := by omega
    rw [bitVec_at_false_of_ge
      (entryTreeBackground Gamma qP b1 b2 entry) i hge] at hbit
    cases hbit

theorem entryAttachmentChildren_split
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let cross0 := entryCrossTreeState Gamma qP b1 b2 entry
    let bg0 := entryTreeBackgroundState Gamma qP b1 b2 entry
    splitAttachmentChildren (exceptionalPathSafe Gamma qP b1 b2 entry)
        (OccTreeCode.attachmentChildren
          (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry).tree) =
      (TreeBackgroundState.traceChildren bg0,
        CrossTreeState.traceChildren cross0) := by
  dsimp only
  let cross0 := entryCrossTreeState Gamma qP b1 b2 entry
  let bg0 := entryTreeBackgroundState Gamma qP b1 b2 entry
  let safe := exceptionalPathSafe Gamma qP b1 b2 entry
  have hbg := TreeBackgroundState.exhaust_attachmentChildren bg0
  have hcross := CrossTreeState.exhaust_attachmentChildren cross0
  have hinitial : OccTreeCode.attachmentChildren
      (OTree.toCode (N := Gamma.length) cross0.tree) = [] := by
    unfold cross0 entryCrossTreeState
    unfold OccTreeCode.attachmentChildren
    rw [OTree.toCode_attachments_ofWalk]
    rfl
  have hchildren : OccTreeCode.attachmentChildren
      (OTree.toCode (N := Gamma.length) bg0.exhaust.tree) =
      CrossTreeState.traceChildren cross0 ++
        TreeBackgroundState.traceChildren bg0 := by
    rw [hbg]
    change OccTreeCode.attachmentChildren
        (OTree.toCode (N := Gamma.length) cross0.exhaust.tree) ++
          TreeBackgroundState.traceChildren bg0 = _
    rw [hcross, hinitial, List.nil_append]
  change splitAttachmentChildren safe
      (OccTreeCode.attachmentChildren
        (OTree.toCode (N := Gamma.length) bg0.exhaust.tree)) = _
  rw [hchildren]
  apply splitAttachmentChildren_of_patterns
  · apply CrossTreeState.traceChildren_pattern cross0 safe
    exact entryUnsafeLeft_safe_false Gamma qP b1 b2 entry
  · apply TreeBackgroundState.traceChildren_safe bg0 safe
    exact entryTreeBackground_safe_true Gamma qP b1 b2 entry

theorem TreeBackgroundState.exhaust_external_eq
    {Gamma : List (Polymer L)} {root : Nat}
    (state : TreeBackgroundState Gamma root) :
    state.exhaust.external = state.external := by
  rw [TreeBackgroundState.exhaust]
  split
  next hcheck =>
    exact TreeBackgroundState.exhaust_external_eq (state.step hcheck)
  next _ => rfl
termination_by state.potential
decreasing_by apply TreeBackgroundState.step_potential_lt

def decodedBackground (safe : Nat → Bool) {N : Nat}
    (code : OccTreeCarrierCode N) : OccBitVec N :=
  restoreMany code.background
    (splitAttachmentChildren safe
      (OccTreeCode.attachmentChildren code.tree)).1

def decodedExternal (safe : Nat → Bool) {N : Nat}
    (code : OccTreeCarrierCode N) : OccBitVec N :=
  restoreMany code.external
    (splitAttachmentChildren safe
      (OccTreeCode.attachmentChildren code.tree)).2

theorem decodedBackground_entry
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    decodedBackground (exceptionalPathSafe Gamma qP b1 b2 entry)
        (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry) =
      entryTreeBackground Gamma qP b1 b2 entry := by
  let bg0 := entryTreeBackgroundState Gamma qP b1 b2 entry
  unfold decodedBackground
  rw [entryAttachmentChildren_split]
  change restoreMany bg0.exhaust.background
      (TreeBackgroundState.traceChildren bg0) = _
  exact TreeBackgroundState.restoreMany_exhaust_background bg0

theorem decodedExternal_entry
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    decodedExternal (exceptionalPathSafe Gamma qP b1 b2 entry)
        (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry) =
      entryRoutedExternal Gamma qP b1 b2 entry := by
  let cross0 := entryCrossTreeState Gamma qP b1 b2 entry
  let bg0 := entryTreeBackgroundState Gamma qP b1 b2 entry
  unfold decodedExternal
  rw [entryAttachmentChildren_split]
  change restoreMany bg0.exhaust.external
      (CrossTreeState.traceChildren cross0) = _
  rw [TreeBackgroundState.exhaust_external_eq bg0]
  change restoreMany
      (unionBits cross0.exhaust.left cross0.exhaust.right)
        (CrossTreeState.traceChildren cross0) = _
  rw [CrossTreeState.restoreMany_exhaust_union cross0]
  exact (entryRoutedExternal_eq_union Gamma qP b1 b2 entry).symm

theorem entryTreeCore_eq_initial
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccTreeCode.core
        (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry).tree =
      OTree.toCode (N := Gamma.length)
        (entryCrossTreeState Gamma qP b1 b2 entry).tree := by
  let cross0 := entryCrossTreeState Gamma qP b1 b2 entry
  let bg0 := entryTreeBackgroundState Gamma qP b1 b2 entry
  change OccTreeCode.core
      (OTree.toCode (N := Gamma.length) bg0.exhaust.tree) =
    OTree.toCode (N := Gamma.length) cross0.tree
  rw [TreeBackgroundState.exhaust_core_eq bg0]
  change OccTreeCode.core
      (OTree.toCode (N := Gamma.length) cross0.exhaust.tree) = _
  rw [CrossTreeState.exhaust_core_eq cross0]
  unfold cross0 entryCrossTreeState
  exact OTree.toCode_core_ofWalk _

/-! ## Decoding the old injective path-safe carrier -/

def OccTreeCode.decodedRoot {N : Nat} : OccTreeCode N → Nat
  | .single root => root
  | .prepend root _ => root
  | .attach tree _ _ => OccTreeCode.decodedRoot tree

def OccTreeCode.decodedChain {N : Nat} (background : OccBitVec N) :
    OccTreeCode N → OccChainCode N
  | .single _ => .terminal background
  | .prepend _ tree =>
      .step (OccTreeCode.decodedRoot tree)
        (OccTreeCode.decodedChain background tree)
  | .attach tree _ _ => OccTreeCode.decodedChain background tree

theorem OccTreeCode.decodedRoot_core {N : Nat} :
    ∀ code : OccTreeCode N,
      OccTreeCode.decodedRoot (OccTreeCode.core code) =
        OccTreeCode.decodedRoot code
  | .single _ => rfl
  | .prepend _ _ => rfl
  | .attach tree _ _ => OccTreeCode.decodedRoot_core tree

theorem OccTreeCode.decodedChain_core {N : Nat}
    (background : OccBitVec N) : ∀ code : OccTreeCode N,
    OccTreeCode.decodedChain background (OccTreeCode.core code) =
      OccTreeCode.decodedChain background code
  | .single _ => rfl
  | .prepend _ tree => by
      simp only [OccTreeCode.core, OccTreeCode.decodedChain]
      rw [OccTreeCode.decodedRoot_core,
        OccTreeCode.decodedChain_core background tree]
  | .attach tree _ _ => OccTreeCode.decodedChain_core background tree

theorem OTree.toCode_decodedRoot
    {N root : Nat} {edge : Nat → Nat → Bool} :
    ∀ tree : OTree edge root,
      OccTreeCode.decodedRoot (OTree.toCode (N := N) tree) = root
  | .single _ => rfl
  | .prepend _ _ => rfl
  | .attach tree _ _ _ => OTree.toCode_decodedRoot tree

theorem OTree.toCode_decodedChain_ofWalk
    {N : Nat} {edge : Nat → Nat → Bool} {x y : Nat}
    (walk : CWalk edge x y) (background : OccBitVec N) :
    OccTreeCode.decodedChain background
        (OTree.toCode (N := N) (OTree.ofWalk walk)) =
      occurrenceChainCodeOfWalk walk background := by
  induction walk with
  | single _ => rfl
  | cons _ rest ih =>
      simp only [OTree.ofWalk, OTree.toCode, OccTreeCode.decodedChain,
        occurrenceChainCodeOfWalk]
      rw [OTree.toCode_decodedRoot, ih, CWalk.start_eq]

private theorem occurrenceChainCodeOfWalk_map_id
    {N : Nat} {edgeA edgeB : Nat → Nat → Bool}
    (hedge : ∀ i j, edgeA i j = true → edgeB i j = true) :
    ∀ {x y : Nat} (walk : CWalk edgeA x y)
      (background : OccBitVec N),
      occurrenceChainCodeOfWalk
          (mapCWalk (fun i => i) hedge walk) background =
        occurrenceChainCodeOfWalk walk background
  | _, _, .single _, _ => rfl
  | _, _, .cons _ rest, background => by
      simp only [mapCWalk, occurrenceChainCodeOfWalk, CWalk.start_eq]
      rw [occurrenceChainCodeOfWalk_map_id hedge rest background]

def decodedPathSafeCarrierCode
    (Gamma : List (Polymer L)) (safe : Nat → Bool)
    (code : OccTreeCarrierCode Gamma.length) : OccCarrierXiCodeAt Gamma :=
  { carrier :=
      { start := OccTreeCode.decodedRoot code.tree
        chain := OccTreeCode.decodedChain (decodedBackground safe code)
          code.tree }
    external := decodedExternal safe code }

theorem decodedPathSafeCarrierCode_entry
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    decodedPathSafeCarrierCode Gamma
        (exceptionalPathSafe Gamma qP b1 b2 entry)
        (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry) =
      exceptionalPathSafeCarrierCode Gamma qP b1 b2 entry := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let walk := conflictWalkOfDisagreement Gamma
    (bitMask pair.1) (bitMask pair.2) path.indexWalk
  have hcore := entryTreeCore_eq_initial Gamma qP b1 b2 entry
  have hbg := decodedBackground_entry Gamma qP b1 b2 entry
  have hext := decodedExternal_entry Gamma qP b1 b2 entry
  have hroot : OccTreeCode.decodedRoot
      (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry).tree =
      exceptionalMarkedIndex Gamma b1 b2 pair := by
    rw [← OccTreeCode.decodedRoot_core]
    rw [hcore]
    change OccTreeCode.decodedRoot
        (OTree.toCode (N := Gamma.length) (OTree.ofWalk walk)) = _
    exact OTree.toCode_decodedRoot _
  have hchain : OccTreeCode.decodedChain
      (decodedBackground (exceptionalPathSafe Gamma qP b1 b2 entry)
        (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry))
      (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry).tree =
      occurrenceChainCodeOfWalk path.indexWalk
        (entryTreeBackground Gamma qP b1 b2 entry) := by
    rw [hbg, ← OccTreeCode.decodedChain_core]
    rw [hcore]
    change OccTreeCode.decodedChain
        (entryTreeBackground Gamma qP b1 b2 entry)
          (OTree.toCode (N := Gamma.length) (OTree.ofWalk walk)) = _
    rw [OTree.toCode_decodedChain_ofWalk]
    unfold walk conflictWalkOfDisagreement
    exact occurrenceChainCodeOfWalk_map_id _ path.indexWalk _
  have htarget : exceptionalPathSafeCarrierCode Gamma qP b1 b2 entry =
      exceptionalCustomCarrierCode Gamma qP b1 b2 entry
        (entryTreeBackground Gamma qP b1 b2 entry)
        (entryRoutedExternal Gamma qP b1 b2 entry) := by
    rfl
  rw [htarget]
  unfold decodedPathSafeCarrierCode exceptionalCustomCarrierCode
  dsimp only
  rw [hext, hroot, hchain]

theorem entryCrossTreeState_vertices
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
    (entryCrossTreeState Gamma qP b1 b2 entry).tree.vertices =
      path.indexWalk.vertices := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let walk := conflictWalkOfDisagreement Gamma
    (bitMask pair.1) (bitMask pair.2) path.indexWalk
  change (OTree.ofWalk walk).vertices = path.indexWalk.vertices
  rw [OTree.ofWalk_vertices]
  exact conflictWalkOfDisagreement_vertices Gamma
    (bitMask pair.1) (bitMask pair.2) path.indexWalk

theorem entryOccurrenceTreeCarrierCode_injective
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry1 entry2 : ExceptionalSourceEntry Gamma qP b1 b2)
    (hcode : entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry1 =
      entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry2) :
    entry1 = entry2 := by
  let facts1 := exceptionalSourceFactsOfMem Gamma qP b1 b2
    entry1.1 entry1.2
  let facts2 := exceptionalSourceFactsOfMem Gamma qP b1 b2
    entry2.1 entry2.2
  let path1 := sourceExceptionalPath Gamma qP b1 b2 entry1.1 facts1
  let path2 := sourceExceptionalPath Gamma qP b1 b2 entry2.1 facts2
  let safe1 := exceptionalPathSafe Gamma qP b1 b2 entry1
  let safe2 := exceptionalPathSafe Gamma qP b1 b2 entry2
  have htree := congrArg (fun code => code.tree) hcode
  have hcores := congrArg OccTreeCode.core htree
  rw [entryTreeCore_eq_initial Gamma qP b1 b2 entry1,
    entryTreeCore_eq_initial Gamma qP b1 b2 entry2] at hcores
  have hverticesRaw := congrArg OccTreeCode.vertices hcores
  have htreeVertices :
      (entryCrossTreeState Gamma qP b1 b2 entry1).tree.vertices =
        (entryCrossTreeState Gamma qP b1 b2 entry2).tree.vertices := by
    simpa only [OTree.toCode_vertices] using hverticesRaw
  have hpathVertices : path1.indexWalk.vertices =
      path2.indexWalk.vertices := by
    rw [← entryCrossTreeState_vertices Gamma qP b1 b2 entry1,
      ← entryCrossTreeState_vertices Gamma qP b1 b2 entry2]
    exact htreeVertices
  have hsafe : safe1 = safe2 := by
    unfold safe1 safe2 exceptionalPathSafe
    dsimp only
    funext i
    rw [hpathVertices]
  have hdecoded := congrArg
    (decodedPathSafeCarrierCode Gamma safe1) hcode
  have hdecode1 : decodedPathSafeCarrierCode Gamma safe1
      (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry1) =
        exceptionalPathSafeCarrierCode Gamma qP b1 b2 entry1 :=
    decodedPathSafeCarrierCode_entry Gamma qP b1 b2 entry1
  have hdecode2 : decodedPathSafeCarrierCode Gamma safe1
      (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry2) =
        exceptionalPathSafeCarrierCode Gamma qP b1 b2 entry2 := by
    rw [hsafe]
    exact decodedPathSafeCarrierCode_entry Gamma qP b1 b2 entry2
  rw [hdecode1, hdecode2] at hdecoded
  exact exceptionalPathSafeCarrierCode_injective Gamma qP b1 b2
    entry1 entry2 hdecoded

/-! ## Exact finite summation and tree-carrier domination -/

def occurrenceTreeCarrierMajorant (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) : Q' :=
  qListSum (occurrenceTreeCarrierCodeWeight w Gamma qP b1 b2 label)
    (occurrenceTreeCarrierCodes Gamma)

theorem occurrenceTreeCarrierCodeWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : OccTreeCarrierCode Gamma.length) :
    (0 : Q') ≤ occurrenceTreeCarrierCodeWeight w Gamma qP b1 b2 label
      code := by
  unfold occurrenceTreeCarrierCodeWeight
  split
  · exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (occurrenceTreeCodeWeight_nonnegative hw Gamma qP b1 b2 label
          code.tree)
        (familyActivity_nonneg hw
          (selectByBits Gamma code.background) label))
      (admissibleFamilyWeight_nonnegative hw qP label
        (selectByBits Gamma code.external))
  · exact Q'.le_refl' 0

theorem exceptionalSourceTree_mapped_sum_eqv
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep)
    (source : List (ExceptionalSourceEntry Gamma qP b1 b2)) :
    qListSum
        (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
        source ≈
      qListSum (occurrenceTreeCarrierCodeWeight w Gamma qP b1 b2 label)
        (source.map (entryOccurrenceTreeCarrierCode Gamma qP b1 b2)) := by
  refine Q'.eqv_trans _ _ _
    (qListSum_eqv_congr
      (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
      (fun entry => occurrenceTreeCarrierCodeWeight w Gamma qP b1 b2 label
        (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry))
      source ?_) ?_
  · intro entry _
    exact Q'.eqv_symm
      (entryOccurrenceTreeCarrierCode_weight_eqv_source
        w Gamma qP b1 b2 label entry)
  · exact Q'.eqv_of_eq
      (qListSum_map
        (occurrenceTreeCarrierCodeWeight w Gamma qP b1 b2 label)
        (entryOccurrenceTreeCarrierCode Gamma qP b1 b2) source).symm

theorem exceptionalSourceTree_sum_le_carrierMajorant
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (source : List (ExceptionalSourceEntry Gamma qP b1 b2))
    (hsource : source.Nodup) :
    qListSum
        (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
        source ≤
      occurrenceTreeCarrierMajorant w Gamma qP b1 b2 label := by
  apply qListSum_le_of_injective source (occurrenceTreeCarrierCodes Gamma)
    (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
    (occurrenceTreeCarrierCodeWeight w Gamma qP b1 b2 label)
    (entryOccurrenceTreeCarrierCode Gamma qP b1 b2)
    hsource
  · intro entry _
    exact entryOccurrenceTreeCarrierCode_mem Gamma qP b1 b2 entry
  · intro entry1 _ entry2 _ hcode
    exact entryOccurrenceTreeCarrierCode_injective Gamma qP b1 b2
      entry1 entry2 hcode
  · intro entry _
    exact Q'.ge_of_eqv
      (entryOccurrenceTreeCarrierCode_weight_eqv_source
        w Gamma qP b1 b2 label entry)
  · intro code _
    exact occurrenceTreeCarrierCodeWeight_nonnegative hw
      Gamma qP b1 b2 label code

theorem routedExternalIncompatibleSource_treeCarrier_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum
        (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
        (routedExternalIncompatibleSource Gamma qP b1 b2) ≤
      occurrenceTreeCarrierMajorant w Gamma qP b1 b2 label := by
  apply exceptionalSourceTree_sum_le_carrierMajorant hw Gamma qP b1 b2
    label (routedExternalIncompatibleSource Gamma qP b1 b2)
  exact nodup_filter_bool _ _
    (fullExceptionalSource_nodup Gamma qP b1 b2)

#print axioms restoreAt_clearResidualAt
#print axioms OTree.toCode_core_ofWalk
#print axioms OTree.toCode_attachments_ofWalk
#print axioms CrossTreeState.exhaust_attachmentChildren
#print axioms TreeBackgroundState.exhaust_attachmentChildren
#print axioms splitAttachmentChildren_of_patterns
#print axioms CrossTreeState.traceChildren_pattern
#print axioms TreeBackgroundState.traceChildren_safe
#print axioms CrossTreeState.restoreMany_exhaust_union
#print axioms TreeBackgroundState.restoreMany_exhaust_background
#print axioms entryAttachmentChildren_split
#print axioms decodedBackground_entry
#print axioms decodedExternal_entry
#print axioms entryTreeCore_eq_initial
#print axioms OTree.toCode_decodedChain_ofWalk
#print axioms decodedPathSafeCarrierCode_entry
#print axioms entryCrossTreeState_vertices
#print axioms entryOccurrenceTreeCarrierCode_injective
#print axioms occurrenceTreeCarrierCodeWeight_nonnegative
#print axioms exceptionalSourceTree_mapped_sum_eqv
#print axioms exceptionalSourceTree_sum_le_carrierMajorant
#print axioms routedExternalIncompatibleSource_treeCarrier_bound

end YMGap.Continuum.XiExceptionalSourceTreeFiber
