/-
# Construction-valid canonical root-attachment carrier

The first canonical carrier removed duplicate tree syntax but its ambient
local gate only required an attachment parent to occur somewhere in the final
vertex set.  This successor enforces the actual construction order: every
parent must already be present when its child is attached.  Normalized source
trees satisfy the stronger gate and retain exact weight.
-/

import YMGap.Continuum.XiExceptionalCanonicalRootAttachmentAnalytic

namespace YMGap.Continuum.XiExceptionalCanonicalStrictCarrier

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier
open YMGap.Continuum.XiExceptionalOccurrenceTreeWeight
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalSourceTreeCarrier
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier
open YMGap.Continuum.XiExceptionalOccurrenceTreeMajorant

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## Ordered build gate -/

theorem natMemB_eq_true_iff (x : Nat) :
    ∀ xs : List Nat, natMemB x xs = true ↔ x ∈ xs
  | [] => by simp [natMemB]
  | y :: ys => by
      unfold natMemB
      cases hxy : decide (x = y) with
      | true =>
          have heq : x = y := of_decide_eq_true hxy
          subst y
          simp
      | false =>
          have hne : x ≠ y := by
            intro h
            subst y
            simp at hxy
          simp only [hxy, Bool.false_or, List.mem_cons, hne, false_or]
          exact natMemB_eq_true_iff x ys

def seenAfter (seen : List Nat) : List (Nat × Nat) → List Nat
  | [] => seen
  | (_, child) :: rest => seenAfter (child :: seen) rest

def strictAttachmentBuildValidB (Gamma : List (Polymer L)) :
    List Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | seen, (parent, child) :: rest =>
      natMemB parent seen &&
        (decide (child < Gamma.length) &&
          (incAtDistinct Gamma parent child &&
            strictAttachmentBuildValidB Gamma (child :: seen) rest))

theorem seenAfter_mem_of_seen_or_child
    (seen : List Nat) (edges : List (Nat × Nat)) (x : Nat)
    (hmem : x ∈ seen ∨ x ∈ edges.map Prod.snd) :
    x ∈ seenAfter seen edges := by
  induction edges generalizing seen with
  | nil =>
      rcases hmem with h | h
      · exact h
      · cases h
  | cons edge rest ih =>
      rcases edge with ⟨parent, child⟩
      apply ih (child :: seen)
      rcases hmem with hseen | hchildren
      · exact Or.inl (List.mem_cons_of_mem child hseen)
      · rcases List.mem_cons.mp hchildren with hchild | hrest
        · exact Or.inl (List.mem_cons.mpr (Or.inl hchild))
        · exact Or.inr hrest

theorem strictAttachmentBuildValidB_mono
    (Gamma : List (Polymer L)) :
    ∀ edges seen larger,
      strictAttachmentBuildValidB Gamma seen edges = true →
      (∀ x, x ∈ seen → x ∈ larger) →
      strictAttachmentBuildValidB Gamma larger edges = true
  | [], _, _, _, _ => rfl
  | (parent, child) :: rest, seen, larger, hvalid, hsub => by
      have hparts := (Bool.and_eq_true _ _).mp hvalid
      have htail := (Bool.and_eq_true _ _).mp hparts.2
      have hedge := (Bool.and_eq_true _ _).mp htail.2
      have hparent : parent ∈ seen :=
        (natMemB_eq_true_iff parent seen).mp hparts.1
      have hparentLarger : natMemB parent larger = true :=
        (natMemB_eq_true_iff parent larger).mpr (hsub parent hparent)
      have hrest := strictAttachmentBuildValidB_mono Gamma rest
        (child :: seen) (child :: larger) hedge.2 (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem child (hsub x hx))
      exact (Bool.and_eq_true _ _).mpr
        ⟨hparentLarger, (Bool.and_eq_true _ _).mpr
          ⟨htail.1, (Bool.and_eq_true _ _).mpr
            ⟨hedge.1, hrest⟩⟩⟩

theorem strictAttachmentBuildValidB_append
    (Gamma : List (Polymer L)) :
    ∀ (first second : List (Nat × Nat)) (seen : List Nat),
      strictAttachmentBuildValidB Gamma seen first = true →
      strictAttachmentBuildValidB Gamma (seenAfter seen first) second = true →
      strictAttachmentBuildValidB Gamma seen (first ++ second) = true
  | [], second, seen, _, hsecond => hsecond
  | (parent, child) :: rest, second, seen, hfirst, hsecond => by
      have hparts := (Bool.and_eq_true _ _).mp hfirst
      have htail := (Bool.and_eq_true _ _).mp hparts.2
      have hedge := (Bool.and_eq_true _ _).mp htail.2
      have hrec := strictAttachmentBuildValidB_append Gamma rest second
        (child :: seen) hedge.2 hsecond
      exact (Bool.and_eq_true _ _).mpr
        ⟨hparts.1, (Bool.and_eq_true _ _).mpr
          ⟨htail.1, (Bool.and_eq_true _ _).mpr
            ⟨hedge.1, hrec⟩⟩⟩

theorem oTreeOrderedAttachments_strictValidB
    (Gamma : List (Polymer L)) {root : Nat}
    (tree : OTree (incAtDistinct Gamma) root)
    (hvalid : tree.Valid)
    (hbound : ∀ k, k ∈ tree.vertices → k < Gamma.length) :
    strictAttachmentBuildValidB Gamma [root]
      (oTreeOrderedAttachments tree) = true := by
  induction tree with
  | single _ => rfl
  | @prepend root next hedge tree ih =>
      unfold oTreeOrderedAttachments strictAttachmentBuildValidB
      have hnext : next < Gamma.length :=
        hbound next (List.mem_cons_of_mem root (OTree.root_mem tree))
      have htailBound : ∀ k, k ∈ tree.vertices →
          k < Gamma.length := by
        intro k hk
        exact hbound k (List.mem_cons_of_mem root hk)
      have htail := ih hvalid htailBound
      have htailLarger := strictAttachmentBuildValidB_mono Gamma
        (oTreeOrderedAttachments tree) [next] [next, root] htail
        (fun x hx => by
          rcases List.mem_singleton.mp hx with rfl
          exact List.mem_cons_self)
      exact (Bool.and_eq_true _ _).mpr
        ⟨natMemB_true_of_mem root [root] List.mem_cons_self,
          (Bool.and_eq_true _ _).mpr
            ⟨decide_eq_true hnext,
              (Bool.and_eq_true _ _).mpr ⟨hedge, htailLarger⟩⟩⟩
  | @attach root tree parent child hedge ih =>
      have htreeBound : ∀ k, k ∈ tree.vertices →
          k < Gamma.length := by
        intro k hk
        exact hbound k (List.mem_cons_of_mem child hk)
      have hbase := ih hvalid.1 htreeBound
      apply strictAttachmentBuildValidB_append Gamma
        (oTreeOrderedAttachments tree) [(parent, child)] [root] hbase
      have hpCanonical : parent ∈
          (oTreeToRootAttachmentCode
            (N := Gamma.length) tree).vertices :=
        (oTreeToRootAttachmentCode_vertices
          (N := Gamma.length) tree parent).mpr hvalid.2
      have hpSeen : parent ∈
          seenAfter [root] (oTreeOrderedAttachments tree) := by
        apply seenAfter_mem_of_seen_or_child [root]
          (oTreeOrderedAttachments tree) parent
        simpa [oTreeToRootAttachmentCode,
          RootAttachmentTreeCode.vertices] using hpCanonical
      have hchild : child < Gamma.length :=
        hbound child List.mem_cons_self
      unfold strictAttachmentBuildValidB
      exact (Bool.and_eq_true _ _).mpr
        ⟨(natMemB_eq_true_iff parent _).mpr hpSeen,
          (Bool.and_eq_true _ _).mpr
            ⟨decide_eq_true hchild,
              (Bool.and_eq_true _ _).mpr ⟨hedge, rfl⟩⟩⟩

/-! ## Strict tree and carrier weights -/

def strictRootAttachmentLocalValidB (Gamma : List (Polymer L))
    (code : RootAttachmentTreeCode Gamma.length) : Bool :=
  decide (code.root < Gamma.length) &&
    strictAttachmentBuildValidB Gamma [code.root] code.attachments

def strictRootAttachmentAdmissibleB (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool)
    (code : RootAttachmentTreeCode Gamma.length) : Bool :=
  strictRootAttachmentLocalValidB Gamma code && decide code.vertices.Nodup &&
    b1 (polyAt Gamma code.root) &&
      code.vertices.any (fun i => b2 (polyAt Gamma i)) &&
        code.vertices.all (fun i => qP (polyAt Gamma i))

def strictRootAttachmentTreeWeight (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : RootAttachmentTreeCode Gamma.length) : Q' :=
  if strictRootAttachmentAdmissibleB Gamma qP b1 b2 code then
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

theorem oTreeToRootAttachmentCode_strictAdmissibleB
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    {root : Nat} (tree : OTree (incAtDistinct Gamma) root)
    (hvalid : tree.Valid)
    (hbound : ∀ k, k ∈ tree.vertices → k < Gamma.length)
    (hnodup : tree.vertices.Nodup)
    (hq : ∀ k, k ∈ tree.vertices → qP (polyAt Gamma k) = true)
    (hb1 : b1 (polyAt Gamma root) = true)
    (b2Index : Nat) (hb2Mem : b2Index ∈ tree.vertices)
    (hb2 : b2 (polyAt Gamma b2Index) = true) :
    strictRootAttachmentAdmissibleB Gamma qP b1 b2
      (oTreeToRootAttachmentCode (N := Gamma.length) tree) = true := by
  have hroot : root < Gamma.length := hbound root (OTree.root_mem tree)
  have hbuild := oTreeOrderedAttachments_strictValidB
    Gamma tree hvalid hbound
  have hlocal : strictRootAttachmentLocalValidB Gamma
      (oTreeToRootAttachmentCode (N := Gamma.length) tree) = true := by
    unfold strictRootAttachmentLocalValidB
    change (decide (root < Gamma.length) &&
      strictAttachmentBuildValidB Gamma [root]
        (oTreeOrderedAttachments tree)) = true
    exact (Bool.and_eq_true _ _).mpr ⟨decide_eq_true hroot, hbuild⟩
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
  unfold strictRootAttachmentAdmissibleB
  change (strictRootAttachmentLocalValidB Gamma
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

def strictRootAttachmentCarrierCodeWeight (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : RootAttachmentCarrierCode Gamma.length) : Q' :=
  if rootAttachmentBackgroundValidB Gamma qP code.tree code.background then
    (strictRootAttachmentTreeWeight w Gamma qP b1 b2 label code.tree *
      familyActivity w (selectByBits Gamma code.background) label) *
        admissibleFamilyWeight w qP label
          (selectByBits Gamma code.external)
  else 0

theorem strictRootAttachmentCarrierCodeWeight_of_certified
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
    strictRootAttachmentCarrierCodeWeight w Gamma qP b1 b2 label
        ⟨oTreeToRootAttachmentCode (N := Gamma.length) tree,
          background, external⟩ ≈
      (tree.activity (fun i => activity w (polyAt Gamma i) label) *
        familyActivity w (selectByBits Gamma background) label) *
          familyActivity w (selectByBits Gamma external) label := by
  have htreeGate := oTreeToRootAttachmentCode_strictAdmissibleB
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
  unfold strictRootAttachmentCarrierCodeWeight
    strictRootAttachmentTreeWeight
  simp only [hbgGate, htreeGate, if_true]
  unfold admissibleFamilyWeight
  rw [hextGate]
  simp only [if_true]
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (oTreeToRootAttachmentCode_activity_eqv w Gamma label tree))

theorem entryRootAttachmentCarrierCode_strict_weight_eqv_source
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    strictRootAttachmentCarrierCodeWeight w Gamma qP b1 b2 label
        (entryRootAttachmentCarrierCode Gamma qP b1 b2 entry) ≈
      occurrencePairWeight w qP b1 b2 Gamma label entry.1 := by
  let final := entryTreeExhaust Gamma qP b1 b2 entry
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  have hb2 : b2 (polyAt Gamma path.seed) = true :=
    (forwardSeed_parts Gamma.length (bitMask pair.1) (bitMask pair.2)
      (predAt Gamma b2) path.seed_true).2.2.2
  have hstrict := strictRootAttachmentCarrierCodeWeight_of_certified
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
  refine Q'.eqv_trans _ _ _ hstrict ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hold) ?_
  exact entryOccurrenceTreeCarrierCode_weight_eqv_source
    w Gamma qP b1 b2 label entry

#print axioms natMemB_eq_true_iff
#print axioms strictAttachmentBuildValidB_mono
#print axioms strictAttachmentBuildValidB_append
#print axioms oTreeOrderedAttachments_strictValidB
#print axioms oTreeToRootAttachmentCode_strictAdmissibleB
#print axioms strictRootAttachmentCarrierCodeWeight_of_certified
#print axioms entryRootAttachmentCarrierCode_strict_weight_eqv_source

end YMGap.Continuum.XiExceptionalCanonicalStrictCarrier
