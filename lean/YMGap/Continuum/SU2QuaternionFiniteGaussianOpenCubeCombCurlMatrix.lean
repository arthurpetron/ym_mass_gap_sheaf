/-
# Matrix injectivity of the open-cube comb curl

This leaf connects the semantic comb-fixed curl kernel to the actual finite
rational matrix `combGaugeCurl`.  It proves that the finite row sum against a
chord vector is exactly the oriented curl of the corresponding zero-extended
edge field on the selected internal face.  The previously checked coordinate
kernel theorem then gives injectivity of the literal matrix at every width.

This is finite exact topology and rational algebra.  It does not yet construct
an inverse, determinant, positive LDL certificate, Gaussian law,
ORIGINAL-law comparison, continuum theory, or physical mass gap.
-/

import YMGap.Continuum.FiniteWeightedGramSOS
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlKernel

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlMatrix

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlKernel

local infix:50 " ≈ " => Q'.eqv

private def fallbackLink : Z4Link := ((0, 0, 0, 0), .x0)

private def faceLinkA (face : Z4Plaq) : Z4Link :=
  (face.1, (dirsOf face.2).1)

private def faceLinkB (face : Z4Plaq) : Z4Link :=
  (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)

private def faceLinkC (face : Z4Plaq) : Z4Link :=
  (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)

private def faceLinkD (face : Z4Plaq) : Z4Link :=
  (face.1, (dirsOf face.2).2)

private theorem boundaryCoefficient_faceLinkA (face : Z4Plaq) :
    internalBoundaryCoefficient face (faceLinkA face) = 1 := by
  rcases face with ⟨⟨x, y, z, t⟩, plane⟩
  cases plane <;>
    simp [internalBoundaryCoefficient, orientedBoundaryCoefficient,
      faceLinkA, dirsOf]
  all_goals decide

private theorem addE_ne_self_local (vertex : Z4Vertex) (direction : Dir4) :
    addE vertex direction ≠ vertex := by
  rcases vertex with ⟨x, y, z, t⟩
  cases direction
  · intro heq
    have hx : x + 1 = x := congrArg (fun v : Z4Vertex => v.1) heq
    omega
  · intro heq
    have hy : y + 1 = y := congrArg (fun v : Z4Vertex => v.2.1) heq
    omega
  · intro heq
    have hz : z + 1 = z := congrArg (fun v : Z4Vertex => v.2.2.1) heq
    omega
  · intro heq
    have ht : t + 1 = t := congrArg (fun v : Z4Vertex => v.2.2.2) heq
    omega

private theorem orientedBoundaryCoefficient_faceLinkB (face : Z4Plaq) :
    orientedBoundaryCoefficient face (faceLinkB face) = 1 := by
  have hdirections := dirsOf_ne face.2
  have hfirst : faceLinkB face ≠ (face.1, (dirsOf face.2).1) := by
    intro heq
    exact hdirections (congrArg Prod.snd heq).symm
  have hsecond : faceLinkB face ≠ (face.1, (dirsOf face.2).2) := by
    intro heq
    exact addE_ne_self_local face.1 (dirsOf face.2).1
      (congrArg Prod.fst heq)
  have hthird : faceLinkB face ≠
      (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1) := by
    intro heq
    exact hdirections (congrArg Prod.snd heq).symm
  have hfourth : faceLinkB face =
      (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2) := rfl
  unfold orientedBoundaryCoefficient
  rw [if_neg hfirst, if_neg hsecond, if_neg hthird, if_pos hfourth]

private theorem boundaryCoefficient_faceLinkB (face : Z4Plaq) :
    internalBoundaryCoefficient face (faceLinkB face) = 1 := by
  unfold internalBoundaryCoefficient
  rw [orientedBoundaryCoefficient_faceLinkB]
  rfl

private theorem orientedBoundaryCoefficient_faceLinkC (face : Z4Plaq) :
    orientedBoundaryCoefficient face (faceLinkC face) = -1 := by
  have hdirections := dirsOf_ne face.2
  have hfirst : faceLinkC face ≠ (face.1, (dirsOf face.2).1) := by
    intro heq
    exact addE_ne_self_local face.1 (dirsOf face.2).2
      (congrArg Prod.fst heq)
  have hsecond : faceLinkC face ≠ (face.1, (dirsOf face.2).2) := by
    intro heq
    exact hdirections (congrArg Prod.snd heq)
  have hthird : faceLinkC face =
      (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1) := rfl
  unfold orientedBoundaryCoefficient
  rw [if_neg hfirst, if_neg hsecond, if_pos hthird]

private theorem boundaryCoefficient_faceLinkC (face : Z4Plaq) :
    internalBoundaryCoefficient face (faceLinkC face) = -1 := by
  unfold internalBoundaryCoefficient
  rw [orientedBoundaryCoefficient_faceLinkC]
  rfl

private theorem boundaryCoefficient_faceLinkD (face : Z4Plaq) :
    internalBoundaryCoefficient face (faceLinkD face) = -1 := by
  rcases face with ⟨⟨x, y, z, t⟩, plane⟩
  cases plane <;>
    simp [internalBoundaryCoefficient, orientedBoundaryCoefficient,
      faceLinkD, dirsOf]
  all_goals decide

private theorem edgesOf_nodup (face : Z4Plaq) : (edgesOf face).Nodup := by
  rcases face with ⟨⟨x, y, z, t⟩, plane⟩
  have hx : x ≠ x + 1 := by omega
  have hy : y ≠ y + 1 := by omega
  have hy' : y + 1 ≠ y := by omega
  have hz : z ≠ z + 1 := by omega
  have hz' : z + 1 ≠ z := by omega
  have ht : t ≠ t + 1 := by omega
  have ht' : t + 1 ≠ t := by omega
  have h01 : Dir4.x0 ≠ Dir4.x1 := by decide
  have h10 : Dir4.x1 ≠ Dir4.x0 := by decide
  have h02 : Dir4.x0 ≠ Dir4.x2 := by decide
  have h20 : Dir4.x2 ≠ Dir4.x0 := by decide
  have h03 : Dir4.x0 ≠ Dir4.x3 := by decide
  have h30 : Dir4.x3 ≠ Dir4.x0 := by decide
  have h12 : Dir4.x1 ≠ Dir4.x2 := by decide
  have h21 : Dir4.x2 ≠ Dir4.x1 := by decide
  have h13 : Dir4.x1 ≠ Dir4.x3 := by decide
  have h31 : Dir4.x3 ≠ Dir4.x1 := by decide
  have h23 : Dir4.x2 ≠ Dir4.x3 := by decide
  have h32 : Dir4.x3 ≠ Dir4.x2 := by decide
  cases plane <;>
    simp only [edgesOf, dirsOf, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq, addE,
      hx, hy, hy', hz, hz', ht, ht',
      h01, h10, h02, h20, h03, h30, h12, h21, h13, h31, h23, h32,
      and_true, and_false, not_false_eq_true, List.nodup_nil]

private theorem listQSum_map_local
    {A B : Type} (value : B → Q') (map : A → B) :
    ∀ items : List A,
      listQSum value (items.map map) =
        listQSum (fun item => value (map item)) items
  | [] => rfl
  | _ :: tail => by
      simp only [List.map, listQSum]
      rw [listQSum_map_local value map tail]

private theorem listQSum_congr_mem_local
    {A : Type} {left right : A → Q'} :
    ∀ items : List A,
      (∀ item, item ∈ items → left item ≈ right item) →
      listQSum left items ≈ listQSum right items
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hterm => by
      exact Q'.add_eqv_congr'
        (hterm head List.mem_cons_self)
        (listQSum_congr_mem_local tail
          (fun item hitem => hterm item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_perm_local {A : Type} (value : A → Q') :
    ∀ {left right : List A}, left.Perm right →
      listQSum value left ≈ listQSum value right
  | _, _, List.Perm.nil => Q'.eqv_refl 0
  | _, _, List.Perm.cons _ hperm =>
      Q'.add_eqv_congr_left _ _ _ (listQSum_perm_local value hperm)
  | _, _, List.Perm.swap first second rest => by
      change value second + (value first + listQSum value rest) ≈
        value first + (value second + listQSum value rest)
      exact Q'.eqv_trans _ ((value second + value first) + listQSum value rest) _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
        (Q'.eqv_trans _ ((value first + value second) + listQSum value rest) _
          (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _))
          (Q'.add_assoc_eqv _ _ _))
  | _, _, List.Perm.trans hleft hright =>
      Q'.eqv_trans _ _ _
        (listQSum_perm_local value hleft)
        (listQSum_perm_local value hright)

private theorem listQSum_eq_filter_of_zero_local
    {A : Type} (value : A → Q') (test : A → Bool) :
    ∀ source : List A,
      (∀ item, item ∈ source → test item = false → value item ≈ 0) →
      listQSum value source ≈ listQSum value (source.filter test)
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      have htail : ∀ item, item ∈ tail → test item = false →
          value item ≈ 0 := by
        intro item hitem htest
        exact hzero item (List.mem_cons_of_mem head hitem) htest
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _ (0 + listQSum value (tail.filter test)) _
            (Q'.add_eqv_congr'
              (hzero head List.mem_cons_self htest)
              (listQSum_eq_filter_of_zero_local value test tail htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero_local value test tail htail)

private theorem perm_of_nodup_mem_iff_local {A : Type} :
    ∀ (left right : List A), left.Nodup → right.Nodup →
      (∀ item, item ∈ left ↔ item ∈ right) → left.Perm right
  | [], [], _, _, _ => List.Perm.nil
  | [], head :: tail, _, _, hmem => by
      have hfalse : head ∈ ([] : List A) := (hmem head).2 List.mem_cons_self
      cases hfalse
  | head :: tail, right, hleft, hright, hmem => by
      have hleftParts := List.nodup_cons.mp hleft
      have hheadRight : head ∈ right := (hmem head).1 List.mem_cons_self
      obtain ⟨before, after, hsplit⟩ := List.append_of_mem hheadRight
      subst right
      have hmiddle : (head :: (before ++ after)).Perm
          (before ++ head :: after) := List.perm_middle.symm
      have hmiddleNodup : (head :: (before ++ after)).Nodup :=
        hmiddle.symm.nodup hright
      have hmiddleParts := List.nodup_cons.mp hmiddleNodup
      have htailMem : ∀ item, item ∈ tail ↔ item ∈ before ++ after := by
        intro item
        constructor
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hleftParts.1 hitem
          have hy := (hmem item).1 (List.mem_cons_of_mem head hitem)
          rcases List.mem_append.mp hy with hbefore | hrest
          · exact List.mem_append_left after hbefore
          · exact List.mem_append_right before
              ((List.mem_cons.mp hrest).resolve_left hne)
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hmiddleParts.1 hitem
          have hy : item ∈ before ++ head :: after := by
            rcases List.mem_append.mp hitem with hbefore | hafter
            · exact List.mem_append_left (head :: after) hbefore
            · exact List.mem_append_right before
                (List.mem_cons_of_mem head hafter)
          exact (List.mem_cons.mp ((hmem item).2 hy)).resolve_left hne
      have htailPerm := perm_of_nodup_mem_iff_local
        tail (before ++ after) hleftParts.2 hmiddleParts.2 htailMem
      exact (List.Perm.cons head htailPerm).trans hmiddle

private theorem map_range_getD {A : Type} (items : List A) (fallback : A) :
    (List.range items.length).map (fun index => items.getD index fallback) =
      items := by
  induction items with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.length_cons]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      change head :: (List.range tail.length).map
        (fun index => tail.getD index fallback) = head :: tail
      rw [induction]

private theorem getD_mem_local : ∀ {items : List Z4Link} {index : Nat},
    index < items.length → items.getD index fallbackLink ∈ items
  | [], _, hindex => absurd hindex (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.mem_cons_self
  | _ :: _tail, _index + 1, hindex =>
      List.mem_cons_of_mem _
        (getD_mem_local (Nat.lt_of_succ_lt_succ hindex))

private theorem idxOf_getD_local : ∀ (items : List Z4Link), items.Nodup →
    ∀ index, index < items.length →
      items.idxOf (items.getD index fallbackLink) = index
  | [], _, index, hindex => absurd hindex (Nat.not_lt_zero _)
  | head :: tail, _, 0, _ => by
      show (head :: tail).idxOf head = 0
      rw [List.idxOf_cons,
        show (head == head) = true from beq_iff_eq.mpr rfl]
      rfl
  | head :: tail, hnodup, index + 1, hindex => by
      have hnodup' := List.nodup_cons.mp hnodup
      have hindex' : index < tail.length := Nat.lt_of_succ_lt_succ hindex
      have hmem : tail.getD index fallbackLink ∈ tail := getD_mem_local hindex'
      have hne : (head == tail.getD index fallbackLink) = false := by
        cases heq : (head == tail.getD index fallbackLink) with
        | false => rfl
        | true => exact absurd ((beq_iff_eq.mp heq) ▸ hmem) hnodup'.1
      show (head :: tail).idxOf (tail.getD index fallbackLink) = index + 1
      rw [List.idxOf_cons, hne, cond_false,
        idxOf_getD_local tail hnodup'.2 index hindex']

private theorem selectedInternalFace_mem {width faceIndex : Nat}
    (hface : faceIndex < internalOpenCubeFaceCount width) :
    selectedInternalOpenCubeFace width faceIndex ∈ internalOpenCubeFaces width := by
  rw [selectedInternalOpenCubeFace, ← List.getElem_eq_getD (h := hface)]
  exact List.getElem_mem hface

private theorem boundaryEdgeSum_eq_faceCurl
    (field : Z4Link → Q') (face : Z4Plaq) :
    listQSum
        (fun link => internalBoundaryCoefficient face link * field link)
        (edgesOf face) ≈
      combGaugeFaceCurl field face := by
  change
    internalBoundaryCoefficient face (faceLinkA face) * field (faceLinkA face) +
      (internalBoundaryCoefficient face (faceLinkD face) * field (faceLinkD face) +
        (internalBoundaryCoefficient face (faceLinkC face) * field (faceLinkC face) +
          (internalBoundaryCoefficient face (faceLinkB face) * field (faceLinkB face) + 0))) ≈
      combGaugeFaceCurl field face
  rw [boundaryCoefficient_faceLinkA, boundaryCoefficient_faceLinkB,
    boundaryCoefficient_faceLinkC, boundaryCoefficient_faceLinkD]
  unfold combGaugeFaceCurl faceLinkA faceLinkB faceLinkC faceLinkD
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.mul (.const 1) (.var 0))
      (.add (.mul (.neg (.const 1)) (.var 3))
        (.add (.mul (.neg (.const 1)) (.var 2))
          (.add (.mul (.const 1) (.var 1)) (.const 0)))))
    (.add (.var 0)
      (.add (.var 1) (.add (.neg (.var 2)) (.neg (.var 3)))))
    (by decide) (fun
      | 0 => field (faceLinkA face)
      | 1 => field (faceLinkB face)
      | 2 => field (faceLinkC face)
      | _ => field (faceLinkD face))

private theorem internalLinkSum_eq_faceCurl
    {width : Nat} {face : Z4Plaq}
    (hface : face ∈ internalOpenCubeFaces width) (field : Z4Link → Q') :
    listQSum
        (fun link => internalBoundaryCoefficient face link * field link)
        (internalOpenCubeLinks width) ≈
      combGaugeFaceCurl field face := by
  let value := fun link => internalBoundaryCoefficient face link * field link
  let test := fun link : Z4Link => decide (link ∈ edgesOf face)
  have hfiltered := listQSum_eq_filter_of_zero_local value test
    (internalOpenCubeLinks width) (by
      intro link _ htest
      have hnot : link ∉ edgesOf face := by
        intro hlink
        have htrue : test link = true := decide_eq_true hlink
        rw [htrue] at htest
        contradiction
      unfold value
      rw [internalBoundaryCoefficient_zero_of_not_mem hnot]
      exact Q'.zero_mul_eqv _)
  have hperm :
      ((internalOpenCubeLinks width).filter test).Perm (edgesOf face) := by
    apply perm_of_nodup_mem_iff_local
    · exact (internalOpenCubeLinks_nodup width).filter _
    · exact edgesOf_nodup face
    · intro link
      constructor
      · intro hlink
        exact of_decide_eq_true (List.mem_filter.mp hlink).2
      · intro hlink
        exact List.mem_filter.mpr
          ⟨internalOpenCubeFace_edge_mem hface hlink, decide_eq_true hlink⟩
  exact Q'.eqv_trans _ _ _ hfiltered
    (Q'.eqv_trans _ _ _ (listQSum_perm_local value hperm)
      (boundaryEdgeSum_eq_faceCurl field face))

private theorem gaugeLinkSum_eq_internalLinkSum
    {width : Nat} (face : Z4Plaq) (coordinate : Nat → Q') :
    listQSum
        (fun link => internalBoundaryCoefficient face link *
          combGaugeCoordinateField width coordinate link)
        (combGaugeLinks width) ≈
      listQSum
        (fun link => internalBoundaryCoefficient face link *
          combGaugeCoordinateField width coordinate link)
        (internalOpenCubeLinks width) := by
  let value := fun link => internalBoundaryCoefficient face link *
    combGaugeCoordinateField width coordinate link
  let test := fun link : Z4Link => decide (¬ CombTreeLink width link)
  have hfiltered := listQSum_eq_filter_of_zero_local value test
    (internalOpenCubeLinks width) (by
      intro link _ htest
      have hnotGauge : link ∉ combGaugeLinks width := by
        intro hgauge
        have hnotTree := ((combGaugeLinks_mem_iff width link).mp hgauge).2
        have htrue : test link = true := decide_eq_true hnotTree
        rw [htrue] at htest
        contradiction
      unfold value combGaugeCoordinateField
      rw [if_neg hnotGauge]
      exact Q'.mul_zero_eqv _)
  unfold combGaugeLinks
  exact Q'.eqv_symm hfiltered

/-- Literal finite action of one comb-curl matrix row. -/
def combGaugeCurlApply (width faceIndex : Nat) (coordinate : Nat → Q') : Q' :=
  listQSum
    (fun gaugeIndex => combGaugeCurl width faceIndex gaugeIndex *
      coordinate gaugeIndex)
    (List.range (combGaugeEdgeCount width))

private theorem rowSum_eq_gaugeLinkSum
    {width faceIndex : Nat} (coordinate : Nat → Q')
    (hface : faceIndex < internalOpenCubeFaceCount width) :
    combGaugeCurlApply width faceIndex coordinate ≈
      listQSum
        (fun link =>
          internalBoundaryCoefficient
              (selectedInternalOpenCubeFace width faceIndex) link *
            combGaugeCoordinateField width coordinate link)
        (combGaugeLinks width) := by
  let linkValue := fun link =>
    internalBoundaryCoefficient
        (selectedInternalOpenCubeFace width faceIndex) link *
      combGaugeCoordinateField width coordinate link
  have hterms :
      combGaugeCurlApply width faceIndex coordinate ≈
        listQSum
          (fun gaugeIndex => linkValue
            ((combGaugeLinks width).getD gaugeIndex fallbackLink))
          (List.range (combGaugeEdgeCount width)) := by
    unfold combGaugeCurlApply
    apply listQSum_congr_mem_local
    intro gaugeIndex hindex
    have hgauge : gaugeIndex < combGaugeEdgeCount width := List.mem_range.mp hindex
    have hgetD : (combGaugeLinks width).getD gaugeIndex fallbackLink ∈
        combGaugeLinks width := getD_mem_local hgauge
    unfold linkValue combGaugeCurl combGaugeCoordinateField
    rw [if_pos ⟨hface, hgauge⟩]
    change internalBoundaryCoefficient
        (selectedInternalOpenCubeFace width faceIndex)
          ((combGaugeLinks width).getD gaugeIndex fallbackLink) *
        coordinate gaugeIndex ≈
      internalBoundaryCoefficient
        (selectedInternalOpenCubeFace width faceIndex)
          ((combGaugeLinks width).getD gaugeIndex fallbackLink) *
        (if (combGaugeLinks width).getD gaugeIndex fallbackLink ∈
            combGaugeLinks width then
          coordinate ((combGaugeLinks width).idxOf
            ((combGaugeLinks width).getD gaugeIndex fallbackLink))
        else 0)
    rw [if_pos hgetD,
      idxOf_getD_local (combGaugeLinks width) (combGaugeLinks_nodup width)
        gaugeIndex hgauge]
    exact Q'.eqv_refl _
  have hreindex :
      listQSum
          (fun gaugeIndex => linkValue
            ((combGaugeLinks width).getD gaugeIndex fallbackLink))
          (List.range (combGaugeEdgeCount width)) =
        listQSum linkValue (combGaugeLinks width) := by
    unfold combGaugeEdgeCount
    rw [← listQSum_map_local]
    rw [map_range_getD]
  exact Q'.eqv_trans _ _ _ hterms (Q'.eqv_of_eq hreindex)

/-- The actual finite matrix row equals the semantic oriented face curl of the
zero-extended chord-coordinate field. -/
theorem combGaugeCurlApply_eq_faceCurl
    {width faceIndex : Nat} (coordinate : Nat → Q')
    (hface : faceIndex < internalOpenCubeFaceCount width) :
    combGaugeCurlApply width faceIndex coordinate ≈
      combGaugeFaceCurl (combGaugeCoordinateField width coordinate)
        (selectedInternalOpenCubeFace width faceIndex) := by
  have hselected := selectedInternalFace_mem hface
  exact Q'.eqv_trans _ _ _
    (rowSum_eq_gaugeLinkSum coordinate hface)
    (Q'.eqv_trans _ _ _
      (gaugeLinkSum_eq_internalLinkSum
        (selectedInternalOpenCubeFace width faceIndex) coordinate)
      (internalLinkSum_eq_faceCurl hselected
        (combGaugeCoordinateField width coordinate)))

/-- The literal finite rational comb-curl matrix has trivial column kernel at
every width. -/
theorem combGaugeCurl_matrix_injective
    (width : Nat) (coordinate : Nat → Q')
    (hrows : ∀ faceIndex, faceIndex < internalOpenCubeFaceCount width →
      combGaugeCurlApply width faceIndex coordinate ≈ 0)
    {gaugeIndex : Nat} (hgauge : gaugeIndex < combGaugeEdgeCount width) :
    coordinate gaugeIndex ≈ 0 := by
  apply combGaugeCoordinate_eqv_zero_of_face_curls width coordinate
  · intro face hface
    have hindex := List.idxOf_lt_length_of_mem hface
    have hrow := hrows ((internalOpenCubeFaces width).idxOf face) hindex
    have hsemantic := combGaugeCurlApply_eq_faceCurl coordinate hindex
    rw [selectedInternalOpenCubeFace_idxOf hface] at hsemantic
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hsemantic) hrow
  · exact hgauge

private theorem intSquare_nonnegative_local (value : Int) :
    0 ≤ value * value := by
  rcases Int.le_total 0 value with hnonnegative | hnonpositive
  · exact Int.mul_nonneg hnonnegative hnonnegative
  · rw [← Int.neg_mul_neg]
    exact Int.mul_nonneg
      (Int.neg_nonneg_of_nonpos hnonpositive)
      (Int.neg_nonneg_of_nonpos hnonpositive)

private theorem eqvZero_of_numZero_local {value : Q'}
    (hnum : value.num = 0) : value ≈ 0 := by
  show value.num * ((0 : Q').den : Int) =
    (0 : Q').num * (value.den : Int)
  rw [hnum, show (0 : Q').num = 0 from rfl,
    Int.zero_mul, Int.zero_mul]

private theorem square_eqv_zero_of_nonpositive_local {value : Q'}
    (hnonpositive : value * value ≤ (0 : Q')) : value ≈ 0 := by
  have hnumSquareRaw :
      (value * value).num * ((0 : Q').den : Int) ≤
        (0 : Q').num * ((value * value).den : Int) := hnonpositive
  have hzeroDen : ((0 : Q').den : Int) = 1 := rfl
  have hzeroNum : (0 : Q').num = 0 := rfl
  have hmulNum : (value * value).num = value.num * value.num := rfl
  rw [hzeroDen, hzeroNum, hmulNum, Int.mul_one, Int.zero_mul] at hnumSquareRaw
  exact eqvZero_of_numZero_local
    ((Int.mul_eq_zero.mp
      (Int.le_antisymm hnumSquareRaw
        (intSquare_nonnegative_local value.num))).elim id id)

private theorem listQSum_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A, (0 : Q') ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hvalue head)
        (listQSum_nonnegative_local value hvalue tail)

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {selected : A}, selected ∈ items →
      value selected ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, selected, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_local value hvalue tail)
      · have htailBound := listQSum_member_le_nonnegative_local
          value hvalue tail htail
        have htailMonotone : listQSum value tail ≤
            value head + listQSum value tail := by
          have hmono := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hmono
        exact Q'.le_trans' _ _ _ htailBound htailMonotone

private theorem positive_of_nonnegative_not_eqv_zero_local
    {value : Q'} (hnonnegative : (0 : Q') ≤ value)
    (hne : ¬ value ≈ 0) : (0 : Q') < value := by
  have hnumNonnegative : (0 : Int) ≤ value.num :=
    (Q'.zero_le_iff_num_nonneg value).mp hnonnegative
  have hnumNe : value.num ≠ 0 := by
    intro hnum
    exact hne (eqvZero_of_numZero_local hnum)
  show (0 : Int) * (value.den : Int) < value.num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  omega

/-- Sum of squared literal comb-curl row actions on one chord-coordinate
vector. -/
def combGaugeCurlEnergy (width : Nat) (coordinate : Nat → Q') : Q' :=
  listQSum
    (fun faceIndex =>
      combGaugeCurlApply width faceIndex coordinate *
        combGaugeCurlApply width faceIndex coordinate)
    (List.range (internalOpenCubeFaceCount width))

theorem combGaugeCurlEnergy_nonnegative
    (width : Nat) (coordinate : Nat → Q') :
    (0 : Q') ≤ combGaugeCurlEnergy width coordinate := by
  unfold combGaugeCurlEnergy
  exact listQSum_nonnegative_local
    (fun faceIndex =>
      combGaugeCurlApply width faceIndex coordinate *
        combGaugeCurlApply width faceIndex coordinate)
    (fun faceIndex => SumOfSquares.q_mul_self_nonneg
      (combGaugeCurlApply width faceIndex coordinate))
    (List.range (internalOpenCubeFaceCount width))

/-- A nonzero in-range chord coordinate gives strictly positive total
comb-curl energy.  The proof uses all-row injectivity and nonnegativity; it
does not choose a nonzero row. -/
theorem combGaugeCurlEnergy_positive_of_coordinate_not_eqv_zero
    (width : Nat) (coordinate : Nat → Q')
    {gaugeIndex : Nat} (hgauge : gaugeIndex < combGaugeEdgeCount width)
    (hcoordinate : ¬ coordinate gaugeIndex ≈ 0) :
    (0 : Q') < combGaugeCurlEnergy width coordinate := by
  apply positive_of_nonnegative_not_eqv_zero_local
    (combGaugeCurlEnergy_nonnegative width coordinate)
  intro henergy
  apply hcoordinate
  apply combGaugeCurl_matrix_injective width coordinate
  · intro faceIndex hface
    have hsquareLeEnergy := listQSum_member_le_nonnegative_local
      (fun index =>
        combGaugeCurlApply width index coordinate *
          combGaugeCurlApply width index coordinate)
      (fun index => SumOfSquares.q_mul_self_nonneg
        (combGaugeCurlApply width index coordinate))
      (List.range (internalOpenCubeFaceCount width))
      (List.mem_range.mpr hface)
    apply square_eqv_zero_of_nonpositive_local
    exact Q'.le_trans' _ _ _ hsquareLeEnergy (Q'.le_of_eqv henergy)
  · exact hgauge

/-- Complete finite quadratic form of the literal comb-gauge spatial
precision `DᵀD`. -/
def combGaugeSpatialQuadratic (width : Nat) (coordinate : Nat → Q') : Q' :=
  finiteMatrixQuadratic
    (combGaugeEdgeCount width)
    (combGaugeSpatialPrecision width)
    coordinate

private theorem combGaugeWeightedGram_eq_spatialPrecision
    (width left right : Nat) :
    weightedGram
        (List.range (internalOpenCubeFaceCount width))
        (fun _ => (1 : Q'))
        (fun gaugeIndex faceIndex =>
          combGaugeCurl width faceIndex gaugeIndex)
        left right ≈
      combGaugeSpatialPrecision width left right := by
  unfold weightedGram combGaugeSpatialPrecision finiteCurlPrecision
  apply listQSum_congr
  intro faceIndex
  exact Q'.one_mul_eqv _

private theorem combGaugeSpatialQuadratic_eq_weightedGramQuadratic
    (width : Nat) (coordinate : Nat → Q') :
    combGaugeSpatialQuadratic width coordinate ≈
      weightedGramQuadratic
        (List.range (combGaugeEdgeCount width))
        (List.range (internalOpenCubeFaceCount width))
        (fun _ => (1 : Q'))
        (fun gaugeIndex faceIndex =>
          combGaugeCurl width faceIndex gaugeIndex)
        coordinate := by
  unfold combGaugeSpatialQuadratic finiteMatrixQuadratic weightedGramQuadratic
  apply listQSum_congr
  intro left
  apply listQSum_congr
  intro right
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm
      (combGaugeWeightedGram_eq_spatialPrecision width left right))

private theorem combGaugeChannelLinear_eq_apply
    (width faceIndex : Nat) (coordinate : Nat → Q') :
    channelLinear
        (List.range (combGaugeEdgeCount width))
        (fun gaugeIndex selectedFace =>
          combGaugeCurl width selectedFace gaugeIndex)
        coordinate faceIndex ≈
      combGaugeCurlApply width faceIndex coordinate := by
  unfold channelLinear combGaugeCurlApply
  apply listQSum_congr
  intro gaugeIndex
  exact Q'.mul_comm_eqv _ _

private theorem combGaugeWeightedGramSOS_eq_energy
    (width : Nat) (coordinate : Nat → Q') :
    weightedGramSOS
        (List.range (combGaugeEdgeCount width))
        (List.range (internalOpenCubeFaceCount width))
        (fun _ => (1 : Q'))
        (fun gaugeIndex faceIndex =>
          combGaugeCurl width faceIndex gaugeIndex)
        coordinate ≈
      combGaugeCurlEnergy width coordinate := by
  unfold weightedGramSOS combGaugeCurlEnergy
  apply listQSum_congr
  intro faceIndex
  have hlinear := combGaugeChannelLinear_eq_apply width faceIndex coordinate
  refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
  exact Q'.eqv_trans _
    (combGaugeCurlApply width faceIndex coordinate *
      channelLinear
        (List.range (combGaugeEdgeCount width))
        (fun gaugeIndex selectedFace =>
          combGaugeCurl width selectedFace gaugeIndex)
        coordinate faceIndex) _
    (Q'.mul_eqv_congr_right _ _ _ hlinear)
    (Q'.mul_eqv_congr_left _ _ _ hlinear)

/-- The quadratic form of the actual finite spatial precision is exactly the
sum of squared literal comb-curl row actions. -/
theorem combGaugeSpatialQuadratic_eq_energy
    (width : Nat) (coordinate : Nat → Q') :
    combGaugeSpatialQuadratic width coordinate ≈
      combGaugeCurlEnergy width coordinate := by
  exact Q'.eqv_trans _ _ _
    (combGaugeSpatialQuadratic_eq_weightedGramQuadratic width coordinate)
    (Q'.eqv_trans _ _ _
      (weightedGramQuadratic_eq_sos
        (List.range (combGaugeEdgeCount width))
        (List.range (internalOpenCubeFaceCount width))
        (fun _ => (1 : Q'))
        (fun gaugeIndex faceIndex =>
          combGaugeCurl width faceIndex gaugeIndex)
        coordinate)
      (combGaugeWeightedGramSOS_eq_energy width coordinate))

theorem combGaugeSpatialQuadratic_nonnegative
    (width : Nat) (coordinate : Nat → Q') :
    (0 : Q') ≤ combGaugeSpatialQuadratic width coordinate := by
  exact Q'.le_trans' _ _ _
    (combGaugeCurlEnergy_nonnegative width coordinate)
    (Q'.ge_of_eqv (combGaugeSpatialQuadratic_eq_energy width coordinate))

private theorem q_lt_of_lt_of_le_local {left middle right : Q'}
    (hleft : left < middle) (hright : middle ≤ right) : left < right := by
  have hleftCross :
      left.num * (middle.den : Int) <
        middle.num * (left.den : Int) := hleft
  have hrightCross :
      middle.num * (right.den : Int) ≤
        right.num * (middle.den : Int) := hright
  show left.num * (right.den : Int) <
    right.num * (left.den : Int)
  have hrightDen : (0 : Int) < (right.den : Int) := by
    exact_mod_cast right.den_pos
  have hleftDen : (0 : Int) ≤ (left.den : Int) := by
    exact_mod_cast Nat.zero_le _
  have hfirst :
      (left.num * (right.den : Int)) * (middle.den : Int) <
        (middle.num * (left.den : Int)) * (right.den : Int) := by
    have hscaled := Int.mul_lt_mul_of_pos_right hleftCross hrightDen
    have hreorder :
        (left.num * (middle.den : Int)) * (right.den : Int) =
          (left.num * (right.den : Int)) * (middle.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (middle.den : Int) (right.den : Int)]
    rwa [hreorder] at hscaled
  have hsecond :
      (middle.num * (left.den : Int)) * (right.den : Int) ≤
        (right.num * (left.den : Int)) * (middle.den : Int) := by
    have hscaled := Int.mul_le_mul_of_nonneg_left hrightCross hleftDen
    have hleftReorder :
        (left.den : Int) * (middle.num * (right.den : Int)) =
          (middle.num * (left.den : Int)) * (right.den : Int) := by
      rw [Int.mul_comm middle.num (left.den : Int), Int.mul_assoc]
    have hrightReorder :
        (left.den : Int) * (right.num * (middle.den : Int)) =
          (right.num * (left.den : Int)) * (middle.den : Int) := by
      rw [Int.mul_comm right.num (left.den : Int), Int.mul_assoc]
    rwa [hleftReorder, hrightReorder] at hscaled
  have hchain :
      (left.num * (right.den : Int)) * (middle.den : Int) <
        (right.num * (left.den : Int)) * (middle.den : Int) :=
    Int.lt_of_lt_of_le hfirst hsecond
  exact Int.lt_of_mul_lt_mul_right hchain
    (by exact_mod_cast Nat.zero_le _)

/-- The actual finite `DᵀD` quadratic is strictly positive on every vector
with a nonzero in-range chord coordinate. -/
theorem combGaugeSpatialQuadratic_positive_of_coordinate_not_eqv_zero
    (width : Nat) (coordinate : Nat → Q')
    {gaugeIndex : Nat} (hgauge : gaugeIndex < combGaugeEdgeCount width)
    (hcoordinate : ¬ coordinate gaugeIndex ≈ 0) :
    (0 : Q') < combGaugeSpatialQuadratic width coordinate := by
  exact q_lt_of_lt_of_le_local
    (combGaugeCurlEnergy_positive_of_coordinate_not_eqv_zero
      width coordinate hgauge hcoordinate)
    (Q'.ge_of_eqv (combGaugeSpatialQuadratic_eq_energy width coordinate))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlMatrix

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlMatrix.combGaugeCurlApply_eq_faceCurl
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlMatrix.combGaugeCurl_matrix_injective
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlMatrix.combGaugeCurlEnergy_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlMatrix.combGaugeCurlEnergy_positive_of_coordinate_not_eqv_zero
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlMatrix.combGaugeSpatialQuadratic_eq_energy
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlMatrix.combGaugeSpatialQuadratic_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlMatrix.combGaugeSpatialQuadratic_positive_of_coordinate_not_eqv_zero
