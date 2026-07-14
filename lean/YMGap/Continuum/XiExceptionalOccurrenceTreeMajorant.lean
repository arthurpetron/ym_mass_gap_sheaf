/-
# Finite height majorant for occurrence trees

This module sums the zero-gated raw tree weights over a finite height window.
Every certified bounded duplicate-free occurrence tree appears in the ambient
height-`N` list and its exact one-use activity is bounded by that q-list sum.

It then adds the two finite mask slots needed by the exceptional allocation:
a terminal background compatible with every tree vertex and an independent
admissible external family.  The extended code has an exact product-weight
theorem for certified trees and certified masks.
-/

import YMGap.Continuum.XiExceptionalOccurrenceTreeWeight
import YMGap.Continuum.XiExceptionalWeightedInjection

namespace YMGap.Continuum.XiExceptionalOccurrenceTreeMajorant

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier
open YMGap.Continuum.XiExceptionalOccurrenceTreeCodes
open YMGap.Continuum.XiExceptionalOccurrenceTreeWeight

local infix:50 " ≈ " => Q'.eqv

variable {L : Lattice} [DecidableEq L.Plaquette]

/-! ## Height windows -/

def occurrenceTreeCodesUpTo (N : Nat) : Nat -> List (OccTreeCode N)
  | 0 => []
  | fuel + 1 =>
      occurrenceTreeCodesUpTo N fuel ++ occurrenceTreeCodes N (fuel + 1)

private theorem OccTreeCode.height_pos {N : Nat} :
    forall code : OccTreeCode N, 0 < code.height
  | .single _ => Nat.zero_lt_succ 0
  | .prepend _ tree => by
      unfold OccTreeCode.height
      exact Nat.zero_lt_succ _
  | .attach tree _ _ => by
      unfold OccTreeCode.height
      exact Nat.zero_lt_succ _

theorem mem_occurrenceTreeCodesUpTo_of_layer {N h fuel : Nat}
    (code : OccTreeCode N) (hmem : code ∈ occurrenceTreeCodes N h)
    (hle : h ≤ fuel) : code ∈ occurrenceTreeCodesUpTo N fuel := by
  induction fuel with
  | zero =>
      have hzero : h = 0 := by omega
      subst h
      cases hmem
  | succ fuel ih =>
      unfold occurrenceTreeCodesUpTo
      by_cases heq : h = fuel + 1
      · exact List.mem_append_right (occurrenceTreeCodesUpTo N fuel)
          (by simpa [heq] using hmem)
      · exact List.mem_append_left (occurrenceTreeCodes N (fuel + 1))
          (ih (by omega))

theorem OccTreeCode.mem_occurrenceTreeCodesUpTo_of_bound {N fuel : Nat}
    (code : OccTreeCode N) (hbound : code.IndicesBound)
    (hheight : code.height ≤ fuel) :
    code ∈ occurrenceTreeCodesUpTo N fuel :=
  mem_occurrenceTreeCodesUpTo_of_layer code
    (OccTreeCode.mem_occurrenceTreeCodes_of_bound code hbound) hheight

/-! ## Nonnegative finite tree majorant -/

theorem treeCodeActivity_nonnegative {L : Lattice}
    [DecidableEq L.Plaquette] {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (label : L.Plaquette -> Rep) :
    forall code : OccTreeCode Gamma.length,
      (0 : Q') ≤ treeCodeActivity w Gamma label code
  | .single root => activity_nonneg hw (polyAt Gamma root) label
  | .prepend root tree =>
      Q'.mul_nonneg _ _ (activity_nonneg hw (polyAt Gamma root) label)
        (treeCodeActivity_nonnegative hw Gamma label tree)
  | .attach tree _ child =>
      Q'.mul_nonneg _ _
        (treeCodeActivity_nonnegative hw Gamma label tree)
        (activity_nonneg hw (polyAt Gamma child) label)

theorem occurrenceTreeCodeWeight_nonnegative {L : Lattice}
    [DecidableEq L.Plaquette] {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (label : L.Plaquette -> Rep) (code : OccTreeCode Gamma.length) :
    (0 : Q') ≤ occurrenceTreeCodeWeight w Gamma qP b1 b2 label code := by
  unfold occurrenceTreeCodeWeight
  split
  · exact treeCodeActivity_nonnegative hw Gamma label code
  · exact Q'.le_refl' _

def occurrenceTreeMajorant (w : Q') {L : Lattice}
    [DecidableEq L.Plaquette]
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (label : L.Plaquette -> Rep) (fuel : Nat) : Q' :=
  qListSum (occurrenceTreeCodeWeight w Gamma qP b1 b2 label)
    (occurrenceTreeCodesUpTo Gamma.length fuel)

theorem occurrenceTreeMajorant_nonnegative {L : Lattice}
    [DecidableEq L.Plaquette] {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (label : L.Plaquette -> Rep) (fuel : Nat) :
    (0 : Q') ≤ occurrenceTreeMajorant w Gamma qP b1 b2 label fuel := by
  apply qListSum_nonnegative
  intro code _
  exact occurrenceTreeCodeWeight_nonnegative hw Gamma qP b1 b2 label code

private theorem qListSum_term_le_of_mem [DecidableEq a]
    (weight : a -> Q') (xs : List a) (x : a)
    (hmem : x ∈ xs) (hnonneg : forall y, y ∈ xs -> (0 : Q') ≤ weight y) :
    weight x ≤ qListSum weight xs := by
  have hrest : (0 : Q') ≤ qListSum weight (xs.erase x) := by
    apply qListSum_nonnegative
    intro y hy
    exact hnonneg y (List.mem_of_mem_erase hy)
  have hstep : weight x ≤ weight x + qListSum weight (xs.erase x) :=
    Q'.add_le_self_of_nonneg (weight x) _ hrest
  exact Q'.le_trans' _ _ _ hstep
    (Q'.ge_of_eqv (qListSum_erase_decompose weight xs x hmem))

private theorem occurrenceIndices_length (Gamma : List (Polymer L)) :
    (occurrenceIndices Gamma.length).length = Gamma.length := by
  have h := congrArg List.length (map_polyAt_occurrenceIndices Gamma)
  simpa only [List.length_map] using h

theorem OTree.vertices_length_le_ambient {L : Lattice}
    [DecidableEq L.Plaquette]
    (Gamma : List (Polymer L)) {root : Nat}
    (tree : OTree (incAtDistinct Gamma) root)
    (hnodup : tree.vertices.Nodup)
    (hbound : forall k, k ∈ tree.vertices -> k < Gamma.length) :
    tree.vertices.length ≤ Gamma.length := by
  have hsubset : forall k, k ∈ tree.vertices ->
      k ∈ occurrenceIndices Gamma.length := by
    intro k hk
    exact occurrenceIndices_complete (hbound k hk)
  have hle := FiniteListBound.nodup_subset_length_le tree.vertices
    (occurrenceIndices Gamma.length) hnodup hsubset
  rw [occurrenceIndices_length Gamma] at hle
  exact hle

/-- Exact inclusion of every certified ambient tree in the height-`N`
majorant. -/
theorem certified_OTree_activity_le_majorant {L : Lattice}
    [DecidableEq L.Plaquette] {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (label : L.Plaquette -> Rep) {root : Nat}
    (tree : OTree (incAtDistinct Gamma) root)
    (hvalid : tree.Valid)
    (hbound : forall k, k ∈ tree.vertices -> k < Gamma.length)
    (hnodup : tree.vertices.Nodup)
    (hq : forall k, k ∈ tree.vertices -> qP (polyAt Gamma k) = true)
    (hb1 : b1 (polyAt Gamma root) = true)
    (b2Index : Nat) (hb2Mem : b2Index ∈ tree.vertices)
    (hb2 : b2 (polyAt Gamma b2Index) = true) :
    tree.activity (fun i => activity w (polyAt Gamma i) label) ≤
      occurrenceTreeMajorant w Gamma qP b1 b2 label Gamma.length := by
  let code := OTree.toCode (N := Gamma.length) tree
  have hcodeBound := OTree.toCode_indicesBound tree hvalid hbound
  have hheight : code.height ≤ Gamma.length := by
    rw [OTree.toCode_height]
    exact OTree.vertices_length_le_ambient Gamma tree hnodup hbound
  have hmem : code ∈ occurrenceTreeCodesUpTo Gamma.length Gamma.length :=
    OccTreeCode.mem_occurrenceTreeCodesUpTo_of_bound code
      hcodeBound hheight
  have hterm := qListSum_term_le_of_mem
    (occurrenceTreeCodeWeight w Gamma qP b1 b2 label)
    (occurrenceTreeCodesUpTo Gamma.length Gamma.length) code hmem
    (fun c _ => occurrenceTreeCodeWeight_nonnegative hw
      Gamma qP b1 b2 label c)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm
      (occurrenceTreeCodeWeight_toCode_eqv w Gamma qP b1 b2 label
        tree hvalid hbound hnodup hq hb1 b2Index hb2Mem hb2))) hterm

/-! ## Terminal background and independent external masks -/

structure OccTreeCarrierCode (N : Nat) : Type where
  tree : OccTreeCode N
  background : OccBitVec N
  external : OccBitVec N
deriving DecidableEq

def occurrenceTreeCarrierCodes (Gamma : List (Polymer L)) :
    List (OccTreeCarrierCode Gamma.length) :=
  (occurrenceTreeCodesUpTo Gamma.length Gamma.length).flatMap (fun tree =>
    (bitVectors Gamma.length).flatMap (fun background =>
      (bitVectors Gamma.length).map (fun external =>
        ⟨tree, background, external⟩)))

def treeBackgroundValidB (Gamma : List (Polymer L))
    (qP : Polymer L -> Bool) (tree : OccTreeCode Gamma.length)
    (background : OccBitVec Gamma.length) : Bool :=
  let B := selectByBits Gamma background
  B.all qP && familyCompatibleB B &&
    tree.vertices.all (fun i =>
      B.all (fun T => compatibleB (polyAt Gamma i) T))

def occurrenceTreeCarrierCodeWeight (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L -> Bool)
    (label : L.Plaquette -> Rep)
    (code : OccTreeCarrierCode Gamma.length) : Q' :=
  if treeBackgroundValidB Gamma qP code.tree code.background then
    (occurrenceTreeCodeWeight w Gamma qP b1 b2 label code.tree *
      familyActivity w (selectByBits Gamma code.background) label) *
        admissibleFamilyWeight w qP label
          (selectByBits Gamma code.external)
  else 0

omit [DecidableEq L.Plaquette] in
theorem OccTreeCarrierCode.mem_of_parts
    (Gamma : List (Polymer L))
    (tree : OccTreeCode Gamma.length)
    (background external : OccBitVec Gamma.length)
    (htree : tree ∈ occurrenceTreeCodesUpTo Gamma.length Gamma.length) :
    OccTreeCarrierCode.mk tree background external ∈
      occurrenceTreeCarrierCodes Gamma := by
  unfold occurrenceTreeCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨tree, htree, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨background, bitVectors_complete background, ?_⟩
  exact List.mem_map.mpr
    ⟨external, bitVectors_complete external, rfl⟩

theorem treeBackgroundValidB_of_facts
    (Gamma : List (Polymer L)) (qP : Polymer L -> Bool)
    (tree : OccTreeCode Gamma.length)
    (background : OccBitVec Gamma.length)
    (hcompat : familyCompatibleB (selectByBits Gamma background) = true)
    (hq : (selectByBits Gamma background).all qP = true)
    (htree : forall i, i ∈ tree.vertices -> forall T,
      T ∈ selectByBits Gamma background ->
        compatibleB (polyAt Gamma i) T = true) :
    treeBackgroundValidB Gamma qP tree background = true := by
  unfold treeBackgroundValidB
  dsimp only
  rw [hq, hcompat]
  apply List.all_eq_true.mpr
  intro i hi
  apply List.all_eq_true.mpr
  intro T hT
  exact htree i hi T hT

/-- Exact source-shaped product for a certified tree and certified terminal
masks. -/
theorem occurrenceTreeCarrierCodeWeight_of_certified
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L -> Bool) (label : L.Plaquette -> Rep)
    {root : Nat} (tree : OTree (incAtDistinct Gamma) root)
    (hvalid : tree.Valid)
    (hbound : forall k, k ∈ tree.vertices -> k < Gamma.length)
    (hnodup : tree.vertices.Nodup)
    (htreeQ : forall k, k ∈ tree.vertices ->
      qP (polyAt Gamma k) = true)
    (hb1 : b1 (polyAt Gamma root) = true)
    (b2Index : Nat) (hb2Mem : b2Index ∈ tree.vertices)
    (hb2 : b2 (polyAt Gamma b2Index) = true)
    (background external : OccBitVec Gamma.length)
    (hbgCompat : familyCompatibleB
      (selectByBits Gamma background) = true)
    (hbgQ : (selectByBits Gamma background).all qP = true)
    (hbgTree : forall i, i ∈ tree.vertices -> forall T,
      T ∈ selectByBits Gamma background ->
        compatibleB (polyAt Gamma i) T = true)
    (hextCompat : familyCompatibleB
      (selectByBits Gamma external) = true)
    (hextQ : (selectByBits Gamma external).all qP = true) :
    occurrenceTreeCarrierCodeWeight w Gamma qP b1 b2 label
        ⟨OTree.toCode (N := Gamma.length) tree, background, external⟩ ≈
      (tree.activity (fun i => activity w (polyAt Gamma i) label) *
        familyActivity w (selectByBits Gamma background) label) *
          familyActivity w (selectByBits Gamma external) label := by
  have hbg := treeBackgroundValidB_of_facts Gamma qP
    (OTree.toCode (N := Gamma.length) tree) background
    hbgCompat hbgQ (fun i hi => by
      apply hbgTree i
      rw [← OTree.toCode_vertices (N := Gamma.length) tree]
      exact hi)
  unfold occurrenceTreeCarrierCodeWeight
  simp only [hbg, if_true]
  have hcore := occurrenceTreeCodeWeight_toCode_eqv
    w Gamma qP b1 b2 label tree hvalid hbound hnodup htreeQ
      hb1 b2Index hb2Mem hb2
  have hextGate :
      ((selectByBits Gamma external).all qP &&
        familyCompatibleB (selectByBits Gamma external)) = true := by
    rw [hextQ, hextCompat]
    rfl
  unfold admissibleFamilyWeight
  simp only [hextGate, if_true]
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hcore)

#print axioms OccTreeCode.mem_occurrenceTreeCodesUpTo_of_bound
#print axioms treeCodeActivity_nonnegative
#print axioms occurrenceTreeCodeWeight_nonnegative
#print axioms occurrenceTreeMajorant_nonnegative
#print axioms OTree.vertices_length_le_ambient
#print axioms certified_OTree_activity_le_majorant
#print axioms OccTreeCarrierCode.mem_of_parts
#print axioms treeBackgroundValidB_of_facts
#print axioms occurrenceTreeCarrierCodeWeight_of_certified

end YMGap.Continuum.XiExceptionalOccurrenceTreeMajorant
