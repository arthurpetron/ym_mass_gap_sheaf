/-
# Canonical root-plus-attachment occurrence-tree carrier

Raw `OccTreeCode` has two presentations of a rooted edge: `prepend` and
`attach`.  This module replaces that syntax by one root followed by one
ordered list of parent/child attachments.  The order is construction order,
so it retains the normalization history without duplicating its tree syntax.

The proof-free code has a constructive decoder into the old all-`attach`
syntax and a left inverse.  More importantly, the terminal tree produced by
the exceptional normalizer has exactly the original source weight in this
canonical carrier.
-/

import YMGap.Continuum.XiExceptionalSourceTreeFiber

namespace YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier
open YMGap.Continuum.XiExceptionalOccurrenceTreeCodes
open YMGap.Continuum.XiExceptionalOccurrenceTreeWeight
open YMGap.Continuum.XiExceptionalOccurrenceTreeMajorant
open YMGap.Continuum.XiExceptionalSourceTreeCarrier

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## The proof-free canonical code and decoder -/

structure RootAttachmentTreeCode (N : Nat) where
  root : Nat
  attachments : List (Nat × Nat)
deriving DecidableEq

def RootAttachmentTreeCode.vertices {N : Nat}
    (code : RootAttachmentTreeCode N) : List Nat :=
  code.root :: code.attachments.map Prod.snd

def attachAll {N : Nat} :
    OccTreeCode N → List (Nat × Nat) → OccTreeCode N
  | tree, [] => tree
  | tree, (parent, child) :: rest =>
      attachAll (.attach tree parent child) rest

def RootAttachmentTreeCode.toOccTreeCode {N : Nat}
    (code : RootAttachmentTreeCode N) : OccTreeCode N :=
  attachAll (.single code.root) code.attachments

def occTreeCodeOrderedAttachments {N : Nat} :
    OccTreeCode N → List (Nat × Nat)
  | .single _ => []
  | .prepend root tree =>
      (root, treeCodeRoot tree) :: occTreeCodeOrderedAttachments tree
  | .attach tree parent child =>
      occTreeCodeOrderedAttachments tree ++ [(parent, child)]

def occTreeCodeToRootAttachment {N : Nat}
    (tree : OccTreeCode N) : RootAttachmentTreeCode N :=
  ⟨treeCodeRoot tree, occTreeCodeOrderedAttachments tree⟩

theorem treeCodeRoot_attachAll {N : Nat} (tree : OccTreeCode N) :
    ∀ attachments,
      treeCodeRoot (attachAll tree attachments) = treeCodeRoot tree
  | [] => rfl
  | (_, _) :: rest => treeCodeRoot_attachAll (.attach tree _ _) rest

theorem orderedAttachments_attachAll {N : Nat} (tree : OccTreeCode N) :
    ∀ attachments,
      occTreeCodeOrderedAttachments (attachAll tree attachments) =
        occTreeCodeOrderedAttachments tree ++ attachments
  | [] => by simp [attachAll]
  | (parent, child) :: rest => by
      change occTreeCodeOrderedAttachments
          (attachAll (.attach tree parent child) rest) = _
      rw [orderedAttachments_attachAll]
      simp [occTreeCodeOrderedAttachments, List.append_assoc]

/-- Constructive decoding is a genuine left inverse: re-reading the root and
ordered attachments of a decoded canonical code returns that code exactly. -/
theorem toRootAttachment_toOccTreeCode {N : Nat}
    (code : RootAttachmentTreeCode N) :
    occTreeCodeToRootAttachment code.toOccTreeCode = code := by
  cases code with
  | mk root attachments =>
      simp only [RootAttachmentTreeCode.toOccTreeCode,
        occTreeCodeToRootAttachment]
      have hroot := treeCodeRoot_attachAll
        (N := N) (OccTreeCode.single root) attachments
      have hatt := orderedAttachments_attachAll
        (N := N) (OccTreeCode.single root) attachments
      simp only [treeCodeRoot, occTreeCodeOrderedAttachments,
        List.nil_append] at hroot hatt
      rw [hroot, hatt]

theorem toOccTreeCode_injective {N : Nat} :
    ∀ a b : RootAttachmentTreeCode N,
      a.toOccTreeCode = b.toOccTreeCode → a = b := by
  intro a b h
  have := congrArg occTreeCodeToRootAttachment h
  simpa [toRootAttachment_toOccTreeCode] using this

/-! ## Canonicalizing certified occurrence trees -/

def oTreeOrderedAttachments {edge : Nat → Nat → Bool} {root : Nat} :
    OTree edge root → List (Nat × Nat)
  | .single _ => []
  | @OTree.prepend _ _ root next _ tree =>
      (root, next) :: oTreeOrderedAttachments tree
  | .attach tree parent child _ =>
      oTreeOrderedAttachments tree ++ [(parent, child)]

def oTreeToRootAttachmentCode {N root : Nat}
    {edge : Nat → Nat → Bool} (tree : OTree edge root) :
    RootAttachmentTreeCode N :=
  ⟨root, oTreeOrderedAttachments tree⟩

theorem oTreeToRootAttachmentCode_vertices {N root : Nat}
    {edge : Nat → Nat → Bool} :
    ∀ (tree : OTree edge root) (i : Nat),
      i ∈ (oTreeToRootAttachmentCode (N := N) tree).vertices ↔
        i ∈ tree.vertices
  | .single _, i => by simp [oTreeToRootAttachmentCode,
      RootAttachmentTreeCode.vertices, oTreeOrderedAttachments,
      OTree.vertices]
  | @OTree.prepend _ _ root next hedge tree, i => by
      simp only [oTreeToRootAttachmentCode,
        RootAttachmentTreeCode.vertices, oTreeOrderedAttachments,
        List.map_cons, Prod.snd, OTree.vertices, List.mem_cons]
      have ih := oTreeToRootAttachmentCode_vertices (N := N) tree i
      have ih' :
          (i = next ∨ i ∈ (oTreeOrderedAttachments tree).map Prod.snd) ↔
            i ∈ tree.vertices := by
        simpa [oTreeToRootAttachmentCode,
          RootAttachmentTreeCode.vertices] using ih
      constructor
      · intro h
        rcases h with hroot | hnext | htail
        · exact Or.inl hroot
        · exact Or.inr (ih'.mp (Or.inl hnext))
        · exact Or.inr (ih'.mp (Or.inr htail))
      · intro h
        rcases h with hroot | htail
        · exact Or.inl hroot
        · rcases ih'.mpr htail with hnext | htail
          · exact Or.inr (Or.inl hnext)
          · exact Or.inr (Or.inr htail)
  | @OTree.attach _ _ root tree parent child hedge, i => by
      simp only [oTreeToRootAttachmentCode,
        RootAttachmentTreeCode.vertices, oTreeOrderedAttachments,
        List.map_append, List.map_cons, List.map_nil, Prod.snd,
        OTree.vertices, List.mem_cons, List.mem_append, List.mem_singleton]
      have ih := oTreeToRootAttachmentCode_vertices (N := N) tree i
      have ih' :
          (i = root ∨ i ∈ (oTreeOrderedAttachments tree).map Prod.snd) ↔
            i ∈ tree.vertices := by
        simpa [oTreeToRootAttachmentCode,
          RootAttachmentTreeCode.vertices] using ih
      constructor
      · intro h
        rcases h with hroot | htail | hchild | hfalse
        · exact Or.inr (ih'.mp (Or.inl hroot))
        · exact Or.inr (ih'.mp (Or.inr htail))
        · exact Or.inl hchild
        · cases hfalse
      · intro h
        rcases h with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · rcases ih'.mpr h with hroot | htail
          · exact Or.inl hroot
          · exact Or.inr (Or.inl htail)

theorem oTreeToRootAttachmentCode_vertices_nodup {N root : Nat}
    {edge : Nat → Nat → Bool} :
    ∀ (tree : OTree edge root), tree.vertices.Nodup →
      (oTreeToRootAttachmentCode (N := N) tree).vertices.Nodup
  | .single _, _ => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | @OTree.prepend _ _ root next hedge tree, hnodup => by
      have hp := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        exact hp.1 ((oTreeToRootAttachmentCode_vertices
          (N := N) tree root).mp hmem)
      · exact oTreeToRootAttachmentCode_vertices_nodup
          (N := N) tree hp.2
  | @OTree.attach _ _ root tree parent child hedge, hnodup => by
      have hp := List.nodup_cons.mp hnodup
      have ih := oTreeToRootAttachmentCode_vertices_nodup
        (N := N) tree hp.2
      have hchild : child ∉
          (oTreeToRootAttachmentCode (N := N) tree).vertices := by
        intro hmem
        exact hp.1 ((oTreeToRootAttachmentCode_vertices
          (N := N) tree child).mp hmem)
      have hcanonical :
          (root :: (oTreeOrderedAttachments tree).map Prod.snd ++ [child]).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨ih,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
        intro x hx y hy hxy
        have hyChild : y = child := List.mem_singleton.mp hy
        exact hchild (hyChild ▸ (hxy ▸ hx))
      simpa [oTreeToRootAttachmentCode,
        RootAttachmentTreeCode.vertices, oTreeOrderedAttachments,
        List.map_append, List.cons_append] using hcanonical

theorem oTreeOrderedAttachments_valid
    {edge : Nat → Nat → Bool} {root : Nat}
    (tree : OTree edge root) (hvalid : tree.Valid) :
    ∀ parent child,
      (parent, child) ∈ oTreeOrderedAttachments tree →
        parent ∈ tree.vertices ∧ child ∈ tree.vertices ∧
          edge parent child = true := by
  induction tree with
  | single _ =>
      intro parent child hmem
      cases hmem
  | @prepend root next hedge tree ih =>
      intro parent child hmem
      rcases List.mem_cons.mp hmem with hp | hp
      · injection hp with hparent hchild
        subst parent
        subst child
        exact ⟨List.mem_cons_self,
          List.mem_cons_of_mem root (OTree.root_mem tree), hedge⟩
      · have h := ih hvalid parent child hp
        exact ⟨List.mem_cons_of_mem root h.1,
          List.mem_cons_of_mem root h.2.1, h.2.2⟩
  | @attach root tree parent0 child0 hedge ih =>
      intro parent child hmem
      rcases List.mem_append.mp hmem with hp | hp
      · have h := ih hvalid.1 parent child hp
        exact ⟨List.mem_cons_of_mem child0 h.1,
          List.mem_cons_of_mem child0 h.2.1, h.2.2⟩
      · have hpEq : (parent, child) = (parent0, child0) :=
          List.mem_singleton.mp hp
        injection hpEq with hparent hchild
        subst parent
        subst child
        exact ⟨List.mem_cons_of_mem child0 hvalid.2,
          List.mem_cons_self, hedge⟩

/-! ## Canonical gates and exact one-use activity -/

def rootAttachmentLocalValidB (Gamma : List (Polymer L))
    (code : RootAttachmentTreeCode Gamma.length) : Bool :=
  decide (code.root < Gamma.length) &&
    code.attachments.all (fun edge =>
      natMemB edge.1 code.vertices &&
        decide (edge.2 < Gamma.length) &&
          incAtDistinct Gamma edge.1 edge.2)

def rootAttachmentAdmissibleB (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool)
    (code : RootAttachmentTreeCode Gamma.length) : Bool :=
  rootAttachmentLocalValidB Gamma code && decide code.vertices.Nodup &&
    b1 (polyAt Gamma code.root) &&
      code.vertices.any (fun i => b2 (polyAt Gamma i)) &&
        code.vertices.all (fun i => qP (polyAt Gamma i))

def rootAttachmentActivity (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep)
    (code : RootAttachmentTreeCode Gamma.length) : Q' :=
  familyActivity w (code.vertices.map (polyAt Gamma)) label

def rootAttachmentTreeWeight (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep)
    (code : RootAttachmentTreeCode Gamma.length) : Q' :=
  if rootAttachmentAdmissibleB Gamma qP b1 b2 code then
    rootAttachmentActivity w Gamma label code
  else 0

private theorem list_any_true_of_mem_true (p : a → Bool) :
    ∀ (xs : List a) (x : a), x ∈ xs → p x = true → xs.any p = true
  | [], _, hx, _ => by cases hx
  | y :: ys, x, hx, hpx => by
      rcases List.mem_cons.mp hx with hxy | htail
      · subst y
        simp [hpx]
      · cases hp : p y with
        | true => simp [List.any_cons, hp]
        | false =>
            simp only [List.any_cons, hp, Bool.false_or]
            exact list_any_true_of_mem_true p ys x htail hpx

theorem oTreeToRootAttachmentCode_localValidB
    (Gamma : List (Polymer L)) {root : Nat}
    (tree : OTree (incAtDistinct Gamma) root)
    (hvalid : tree.Valid)
    (hbound : ∀ k, k ∈ tree.vertices → k < Gamma.length) :
    rootAttachmentLocalValidB Gamma
      (oTreeToRootAttachmentCode (N := Gamma.length) tree) = true := by
  unfold rootAttachmentLocalValidB
  simp only [oTreeToRootAttachmentCode]
  have hroot : root < Gamma.length :=
    hbound root (OTree.root_mem tree)
  refine (Bool.and_eq_true _ _).mpr ⟨decide_eq_true hroot, ?_⟩
  apply List.all_eq_true.mpr
  intro edge hedgeMem
  rcases edge with ⟨parent, child⟩
  have hp := oTreeOrderedAttachments_valid tree hvalid
    parent child hedgeMem
  have hparentCanonical : parent ∈
      (oTreeToRootAttachmentCode (N := Gamma.length) tree).vertices :=
    (oTreeToRootAttachmentCode_vertices
      (N := Gamma.length) tree parent).mpr hp.1
  have hparentB : natMemB parent
      (oTreeToRootAttachmentCode (N := Gamma.length) tree).vertices = true :=
    natMemB_true_of_mem parent _ hparentCanonical
  have hchildBound : child < Gamma.length := hbound child hp.2.1
  change (natMemB parent
      (oTreeToRootAttachmentCode (N := Gamma.length) tree).vertices &&
      decide (child < Gamma.length) &&
        incAtDistinct Gamma parent child) = true
  rw [hparentB, decide_eq_true hchildBound, hp.2.2]
  rfl

theorem oTreeToRootAttachmentCode_admissibleB
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    {root : Nat} (tree : OTree (incAtDistinct Gamma) root)
    (hvalid : tree.Valid)
    (hbound : ∀ k, k ∈ tree.vertices → k < Gamma.length)
    (hnodup : tree.vertices.Nodup)
    (hq : ∀ k, k ∈ tree.vertices → qP (polyAt Gamma k) = true)
    (hb1 : b1 (polyAt Gamma root) = true)
    (b2Index : Nat) (hb2Mem : b2Index ∈ tree.vertices)
    (hb2 : b2 (polyAt Gamma b2Index) = true) :
    rootAttachmentAdmissibleB Gamma qP b1 b2
      (oTreeToRootAttachmentCode (N := Gamma.length) tree) = true := by
  have hlocal := oTreeToRootAttachmentCode_localValidB
    Gamma tree hvalid hbound
  have hcanonNodup := oTreeToRootAttachmentCode_vertices_nodup
    (N := Gamma.length) tree hnodup
  have hb2MemCanon : b2Index ∈
      (oTreeToRootAttachmentCode (N := Gamma.length) tree).vertices :=
    (oTreeToRootAttachmentCode_vertices
      (N := Gamma.length) tree b2Index).mpr hb2Mem
  have hb2Any :
      (oTreeToRootAttachmentCode (N := Gamma.length) tree).vertices.any
        (fun i => b2 (polyAt Gamma i)) = true :=
    list_any_true_of_mem_true _ _ b2Index hb2MemCanon hb2
  have hqAll :
      (oTreeToRootAttachmentCode (N := Gamma.length) tree).vertices.all
        (fun i => qP (polyAt Gamma i)) = true := by
    apply List.all_eq_true.mpr
    intro i hi
    exact hq i ((oTreeToRootAttachmentCode_vertices
      (N := Gamma.length) tree i).mp hi)
  unfold rootAttachmentAdmissibleB
  change (rootAttachmentLocalValidB Gamma
      (oTreeToRootAttachmentCode (N := Gamma.length) tree) &&
      decide (oTreeToRootAttachmentCode
        (N := Gamma.length) tree).vertices.Nodup &&
      b1 (polyAt Gamma root) &&
      (oTreeToRootAttachmentCode
        (N := Gamma.length) tree).vertices.any
          (fun i => b2 (polyAt Gamma i)) &&
      (oTreeToRootAttachmentCode
        (N := Gamma.length) tree).vertices.all
          (fun i => qP (polyAt Gamma i))) = true
  rw [hlocal, decide_eq_true hcanonNodup, hb1, hb2Any, hqAll]
  rfl

theorem oTreeToRootAttachmentCode_activity_eqv
    (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep) {root : Nat} :
    ∀ tree : OTree (incAtDistinct Gamma) root,
      rootAttachmentActivity w Gamma label
          (oTreeToRootAttachmentCode (N := Gamma.length) tree) ≈
        tree.activity (fun i => activity w (polyAt Gamma i) label)
  | .single root => by
      exact Q'.mul_one_eqv (activity w (polyAt Gamma root) label)
  | @OTree.prepend _ _ root next hedge tree => by
      simp only [rootAttachmentActivity, oTreeToRootAttachmentCode,
        RootAttachmentTreeCode.vertices, oTreeOrderedAttachments,
        List.map_cons, Prod.snd, familyActivity_cons, OTree.activity]
      exact Q'.mul_eqv_congr_left _ _ _
        (oTreeToRootAttachmentCode_activity_eqv w Gamma label tree)
  | @OTree.attach _ _ root tree parent child hedge => by
      have hvertices :
          (oTreeToRootAttachmentCode (N := Gamma.length) tree).vertices.map
              (polyAt Gamma) ++ [polyAt Gamma child] =
            (oTreeToRootAttachmentCode (N := Gamma.length)
              (OTree.attach tree parent child hedge)).vertices.map
                (polyAt Gamma) := by
        simp [oTreeToRootAttachmentCode,
          RootAttachmentTreeCode.vertices, oTreeOrderedAttachments,
          List.map_append, List.cons_append]
      unfold rootAttachmentActivity
      rw [← hvertices]
      refine Q'.eqv_trans _ _ _
        (familyActivity_append w label _ [polyAt Gamma child]) ?_
      simp only [familyActivity_cons, familyActivity_nil]
      refine Q'.eqv_trans _
        (rootAttachmentActivity w Gamma label
            (oTreeToRootAttachmentCode (N := Gamma.length) tree) *
          activity w (polyAt Gamma child) label) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_one_eqv (activity w (polyAt Gamma child) label))
      · exact Q'.mul_eqv_congr_right _ _ _
          (oTreeToRootAttachmentCode_activity_eqv w Gamma label tree)

/-! ## Canonical carrier masks and exact source weight -/

structure RootAttachmentCarrierCode (N : Nat) where
  tree : RootAttachmentTreeCode N
  background : OccBitVec N
  external : OccBitVec N
deriving DecidableEq

def rootAttachmentBackgroundValidB (Gamma : List (Polymer L))
    (qP : Polymer L → Bool)
    (tree : RootAttachmentTreeCode Gamma.length)
    (background : OccBitVec Gamma.length) : Bool :=
  let B := selectByBits Gamma background
  B.all qP && familyCompatibleB B &&
    tree.vertices.all (fun i =>
      B.all (fun T => compatibleB (polyAt Gamma i) T))

def rootAttachmentCarrierCodeWeight (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : RootAttachmentCarrierCode Gamma.length) : Q' :=
  if rootAttachmentBackgroundValidB Gamma qP code.tree code.background then
    (rootAttachmentTreeWeight w Gamma qP b1 b2 label code.tree *
      familyActivity w (selectByBits Gamma code.background) label) *
        admissibleFamilyWeight w qP label
          (selectByBits Gamma code.external)
  else 0

theorem rootAttachmentCarrierCodeWeight_of_certified
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep)
    {root : Nat} (tree : OTree (incAtDistinct Gamma) root)
    (hvalid : tree.Valid)
    (hbound : ∀ k, k ∈ tree.vertices → k < Gamma.length)
    (hnodup : tree.vertices.Nodup)
    (htreeQ : ∀ k, k ∈ tree.vertices →
      qP (polyAt Gamma k) = true)
    (hb1 : b1 (polyAt Gamma root) = true)
    (b2Index : Nat) (hb2Mem : b2Index ∈ tree.vertices)
    (hb2 : b2 (polyAt Gamma b2Index) = true)
    (background external : OccBitVec Gamma.length)
    (hbgCompat : familyCompatibleB
      (selectByBits Gamma background) = true)
    (hbgQ : (selectByBits Gamma background).all qP = true)
    (hbgTree : ∀ i, i ∈ tree.vertices → ∀ T,
      T ∈ selectByBits Gamma background →
        compatibleB (polyAt Gamma i) T = true)
    (hextCompat : familyCompatibleB
      (selectByBits Gamma external) = true)
    (hextQ : (selectByBits Gamma external).all qP = true) :
    rootAttachmentCarrierCodeWeight w Gamma qP b1 b2 label
        ⟨oTreeToRootAttachmentCode (N := Gamma.length) tree,
          background, external⟩ ≈
      (tree.activity (fun i => activity w (polyAt Gamma i) label) *
        familyActivity w (selectByBits Gamma background) label) *
          familyActivity w (selectByBits Gamma external) label := by
  have htreeGate := oTreeToRootAttachmentCode_admissibleB
    Gamma qP b1 b2 tree hvalid hbound hnodup htreeQ
      hb1 b2Index hb2Mem hb2
  have hbgTreeCanon : ∀ i,
      i ∈ (oTreeToRootAttachmentCode (N := Gamma.length) tree).vertices →
        ∀ T, T ∈ selectByBits Gamma background →
          compatibleB (polyAt Gamma i) T = true := by
    intro i hi
    exact hbgTree i ((oTreeToRootAttachmentCode_vertices
      (N := Gamma.length) tree i).mp hi)
  have hbgGate : rootAttachmentBackgroundValidB Gamma qP
      (oTreeToRootAttachmentCode (N := Gamma.length) tree) background = true := by
    unfold rootAttachmentBackgroundValidB
    dsimp only
    rw [hbgQ, hbgCompat]
    apply List.all_eq_true.mpr
    intro i hi
    apply List.all_eq_true.mpr
    intro T hT
    exact hbgTreeCanon i hi T hT
  have hextGate :
      ((selectByBits Gamma external).all qP &&
        familyCompatibleB (selectByBits Gamma external)) = true := by
    rw [hextQ, hextCompat]
    rfl
  unfold rootAttachmentCarrierCodeWeight rootAttachmentTreeWeight
  simp only [hbgGate, htreeGate, if_true]
  unfold admissibleFamilyWeight
  rw [hextGate]
  simp only [if_true]
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (oTreeToRootAttachmentCode_activity_eqv w Gamma label tree))

def entryRootAttachmentCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    RootAttachmentCarrierCode Gamma.length :=
  let final := entryTreeExhaust Gamma qP b1 b2 entry
  ⟨oTreeToRootAttachmentCode (N := Gamma.length) final.tree,
    final.background, final.external⟩

theorem entryRootAttachmentCarrierCode_weight_eqv_source
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    rootAttachmentCarrierCodeWeight w Gamma qP b1 b2 label
        (entryRootAttachmentCarrierCode Gamma qP b1 b2 entry) ≈
      occurrencePairWeight w qP b1 b2 Gamma label entry.1 := by
  let final := entryTreeExhaust Gamma qP b1 b2 entry
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  have hb2 : b2 (polyAt Gamma path.seed) = true :=
    (forwardSeed_parts Gamma.length (bitMask pair.1) (bitMask pair.2)
      (predAt Gamma b2) path.seed_true).2.2.2
  have hcanonical := rootAttachmentCarrierCodeWeight_of_certified
    w Gamma qP b1 b2 label final.tree final.valid final.vertices_bound
    final.nodup
    (entryTreeExhaust_all_q Gamma qP b1 b2 entry).tree
    facts.marked_b1 path.seed
    (entryTreeExhaust_seed_mem Gamma qP b1 b2 entry) hb2
    final.background final.external final.background_compatible
    (entryTreeExhaust_background_q Gamma qP b1 b2 entry)
    (entryTreeBackgroundState Gamma qP b1 b2 entry).exhaust_background_tree_compatible
    final.external_compatible
    (entryTreeExhaust_external_q Gamma qP b1 b2 entry)
  have hold := occurrenceTreeCarrierCodeWeight_of_certified
    w Gamma qP b1 b2 label final.tree final.valid final.vertices_bound
    final.nodup
    (entryTreeExhaust_all_q Gamma qP b1 b2 entry).tree
    facts.marked_b1 path.seed
    (entryTreeExhaust_seed_mem Gamma qP b1 b2 entry) hb2
    final.background final.external final.background_compatible
    (entryTreeExhaust_background_q Gamma qP b1 b2 entry)
    (entryTreeBackgroundState Gamma qP b1 b2 entry).exhaust_background_tree_compatible
    final.external_compatible
    (entryTreeExhaust_external_q Gamma qP b1 b2 entry)
  refine Q'.eqv_trans _ _ _ hcanonical ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hold) ?_
  exact entryOccurrenceTreeCarrierCode_weight_eqv_source
    w Gamma qP b1 b2 label entry

#print axioms toRootAttachment_toOccTreeCode
#print axioms toOccTreeCode_injective
#print axioms oTreeToRootAttachmentCode_vertices
#print axioms oTreeToRootAttachmentCode_vertices_nodup
#print axioms oTreeOrderedAttachments_valid
#print axioms oTreeToRootAttachmentCode_admissibleB
#print axioms oTreeToRootAttachmentCode_activity_eqv
#print axioms rootAttachmentCarrierCodeWeight_of_certified
#print axioms entryRootAttachmentCarrierCode_weight_eqv_source

end YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier
