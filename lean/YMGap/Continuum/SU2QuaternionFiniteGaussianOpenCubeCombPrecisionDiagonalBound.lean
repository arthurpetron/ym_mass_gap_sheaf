/-
# Uniform diagonal bound for the open-cube comb precision

Each chord coordinate meets at most six internal spatial plaquettes, and every
oriented curl coefficient has square at most one.  Consequently the diagonal
of the spatial comb precision is at most six.  Adding the single endpoint
time bond gives the uniform bound seven for the time-zero diagonal of the
one-bond free-history precision.

Consumer: the positive-LDL pivot bound for the central retained Gaussian row.
This file proves only a finite rational coordinate bound.  It does not identify
the ORIGINAL interacting law, construct a continuum limit, or prove a physical
mass gap.
-/

import YMGap.Continuum.CayleyPruferInjection
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPrecisionDiagonalBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge

local infix:50 " ≈ " => Q'.eqv

/-- Every oriented cubical incidence coefficient is `0`, `1`, or `-1`, so its
square is bounded by one. -/
theorem internalBoundaryCoefficient_square_le_one
    (face : Z4Plaq) (link : Z4Link) :
    internalBoundaryCoefficient face link *
        internalBoundaryCoefficient face link ≤ 1 := by
  unfold internalBoundaryCoefficient
  simp only [orientedBoundaryCoefficient]
  by_cases hfirst : link = (face.1, (dirsOf face.2).1)
  · rw [if_pos hfirst]
    decide
  · by_cases hsecond : link = (face.1, (dirsOf face.2).2)
    · rw [if_neg hfirst, if_pos hsecond]
      decide
    · by_cases hthird :
        link = (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)
      · rw [if_neg hfirst, if_neg hsecond, if_pos hthird]
        decide
      · by_cases hfourth :
          link = (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)
        · rw [if_neg hfirst, if_neg hsecond, if_neg hthird, if_pos hfourth]
          decide
        · rw [if_neg hfirst, if_neg hsecond, if_neg hthird, if_neg hfourth]
          decide

/-- Internal spatial faces incident to one link. -/
def internalIncidentFaces (width : Nat) (link : Z4Link) : List Z4Plaq :=
  (internalOpenCubeFaces width).filter
    (fun face => decide (link ∈ edgesOf face))

/-- An internal link is carried by at most the six plaquettes in its ambient
four-dimensional link star. -/
theorem internalIncidentFaces_length_le_six
    (width : Nat) (link : Z4Link) :
    (internalIncidentFaces width link).length ≤ 6 := by
  rcases link with ⟨vertex, direction⟩
  have hnodup : (internalIncidentFaces width (vertex, direction)).Nodup := by
    unfold internalIncidentFaces
    exact List.filter_sublist.nodup (internalOpenCubeFaces_nodup width)
  have hsubset : ∀ face,
      face ∈ internalIncidentFaces width (vertex, direction) →
        face ∈ edgePlaqs vertex direction := by
    intro face hface
    have hincident : (vertex, direction) ∈ edgesOf face := by
      have hfiltered := (List.mem_filter.mp hface).2
      exact of_decide_eq_true hfiltered
    exact edge_complete face vertex direction hincident
  have hlength := nodup_subset_length_le
    (internalIncidentFaces width (vertex, direction))
    (edgePlaqs vertex direction) hnodup hsubset
  rw [edgePlaqs_length] at hlength
  exact hlength

private theorem listQSum_eq_filter_of_zero_local
    {A : Type} (value : A → Q') (test : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items → test item = false → value item ≈ 0) →
      listQSum value items ≈ listQSum value (items.filter test)
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

private theorem listQSum_le_length_mul_local
    {A : Type} (value : A → Q') {bound : Q'}
    (hbound0 : (0 : Q') ≤ bound) :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≤ bound) →
      listQSum value items ≤ Q'.ofNat items.length * bound
  | [], _ => Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound => by
      have hhead := hbound head List.mem_cons_self
      have htail := listQSum_le_length_mul_local value hbound0 tail
        (fun item hitem => hbound item (List.mem_cons_of_mem head hitem))
      refine Q'.le_trans' _ _ _ (Q'.add_le_add hhead htail) ?_
      refine Q'.le_of_eqv (Q'.eqv_symm ?_)
      refine Q'.eqv_trans _ ((Q'.ofNat tail.length + 1) * bound) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ bound
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + (1 : Q') * bound) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 bound) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + bound) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv bound))
        (Q'.add_comm_eqv (Q'.ofNat tail.length * bound) bound)

private theorem listQSum_congr_mem_local
    {A : Type} {left right : A → Q'} :
    ∀ items : List A,
      (∀ item, item ∈ items → left item ≈ right item) →
      listQSum left items ≈ listQSum right items
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hcongr =>
      Q'.add_eqv_congr'
        (hcongr head List.mem_cons_self)
        (listQSum_congr_mem_local tail
          (fun item hitem => hcongr item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_map_local
    {A B : Type} (value : B → Q') (map : A → B) :
    ∀ items : List A,
      listQSum value (items.map map) =
        listQSum (fun item => value (map item)) items
  | [] => rfl
  | _ :: tail => by
      simp only [List.map, listQSum]
      rw [listQSum_map_local value map tail]

private theorem map_range_getD_local
    {A : Type} (items : List A) (fallback : A) :
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

/-- The sum of squared oriented coefficients on all internal faces incident to
one link is at most six. -/
theorem internalBoundarySquareSum_le_six
    (width : Nat) (link : Z4Link) :
    listQSum
        (fun face => internalBoundaryCoefficient face link *
          internalBoundaryCoefficient face link)
        (internalOpenCubeFaces width) ≤ 6 := by
  let value : Z4Plaq → Q' := fun face =>
    internalBoundaryCoefficient face link *
      internalBoundaryCoefficient face link
  let test : Z4Plaq → Bool := fun face => decide (link ∈ edgesOf face)
  have hfilter :
      listQSum value (internalOpenCubeFaces width) ≈
        listQSum value (internalIncidentFaces width link) := by
    unfold internalIncidentFaces
    apply listQSum_eq_filter_of_zero_local
    intro face _ htest
    have hnot : link ∉ edgesOf face := by
      intro hmem
      have htrue : decide (link ∈ edgesOf face) = true :=
        decide_eq_true hmem
      rw [htrue] at htest
      cases htest
    unfold value
    rw [internalBoundaryCoefficient_zero_of_not_mem hnot]
    exact Q'.zero_mul_eqv 0
  have hsum : listQSum value (internalIncidentFaces width link) ≤
      Q'.ofNat (internalIncidentFaces width link).length * 1 := by
    apply listQSum_le_length_mul_local value Q'.zero_le_one
    intro face _
    exact internalBoundaryCoefficient_square_le_one face link
  have hlength := internalIncidentFaces_length_le_six width link
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hfilter) ?_
  refine Q'.le_trans' _ _ _ hsum ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) ?_
  exact Q'.ofNat_le_ofNat hlength

/-- Every valid chord coordinate has spatial precision diagonal at most six. -/
theorem combGaugeSpatialPrecision_diagonal_le_six
    {width gaugeIndex : Nat}
    (hgauge : gaugeIndex < combGaugeEdgeCount width) :
    combGaugeSpatialPrecision width gaugeIndex gaugeIndex ≤ 6 := by
  let link := selectedCombGaugeLink width gaugeIndex
  let value : Z4Plaq → Q' := fun face =>
    internalBoundaryCoefficient face link *
      internalBoundaryCoefficient face link
  have hindexed :
      listQSum
          (fun faceIndex =>
            combGaugeCurl width faceIndex gaugeIndex *
              combGaugeCurl width faceIndex gaugeIndex)
          (List.range (internalOpenCubeFaceCount width)) ≈
        listQSum
          (fun faceIndex => value
            (selectedInternalOpenCubeFace width faceIndex))
          (List.range (internalOpenCubeFaceCount width)) := by
    apply listQSum_congr_mem_local
    intro faceIndex hfaceIndex
    have hface : faceIndex < internalOpenCubeFaceCount width :=
      List.mem_range.mp hfaceIndex
    unfold combGaugeCurl value link
    rw [if_pos ⟨hface, hgauge⟩]
    exact Q'.eqv_refl _
  have hfaces :
      listQSum
          (fun faceIndex => value
            (selectedInternalOpenCubeFace width faceIndex))
          (List.range (internalOpenCubeFaceCount width)) =
        listQSum value (internalOpenCubeFaces width) := by
    symm
    have hmap := listQSum_map_local value
      (fun faceIndex => selectedInternalOpenCubeFace width faceIndex)
      (List.range (internalOpenCubeFaceCount width))
    unfold selectedInternalOpenCubeFace internalOpenCubeFaceCount at hmap
    rw [map_range_getD_local] at hmap
    exact hmap
  unfold combGaugeSpatialPrecision finiteCurlPrecision
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ hindexed (Q'.eqv_of_eq hfaces))) ?_
  exact internalBoundarySquareSum_le_six width link

/-- At the time-zero endpoint of a one-bond history, the temporal diagonal adds
exactly one to the spatial comb precision, so every valid chord-coordinate
diagonal is at most seven. -/
theorem combGaugeFreeHistoryPrecision_timeZero_diagonal_le_seven
    {width gaugeIndex : Nat}
    (hgauge : gaugeIndex < combGaugeEdgeCount width) :
    combGaugeFreeHistoryPrecision 1 width
        (historyIndex (combGaugeEdgeCount width) 0 gaugeIndex)
        (historyIndex (combGaugeEdgeCount width) 0 gaugeIndex) ≤ 7 := by
  have hedgeCount : 0 < combGaugeEdgeCount width :=
    Nat.zero_lt_of_lt hgauge
  unfold combGaugeFreeHistoryPrecision freeHistoryCurlPrecision
  change freeHistoryPrecision 1 (combGaugeEdgeCount width)
    (combGaugeSpatialPrecision width)
    (historyIndex (combGaugeEdgeCount width) 0 gaugeIndex)
    (historyIndex (combGaugeEdgeCount width) 0 gaugeIndex) ≤ 7
  rw [freeHistoryPrecision_sameTime 1 (combGaugeEdgeCount width)
    (combGaugeSpatialPrecision width) 0 gaugeIndex gaugeIndex
    hedgeCount hgauge hgauge]
  simp [freeTemporalDegree]
  have hspatial := combGaugeSpatialPrecision_diagonal_le_six hgauge
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add hspatial (Q'.le_refl' 1)) ?_
  decide

#print axioms internalBoundaryCoefficient_square_le_one
#print axioms internalIncidentFaces_length_le_six
#print axioms internalBoundarySquareSum_le_six
#print axioms combGaugeSpatialPrecision_diagonal_le_six
#print axioms combGaugeFreeHistoryPrecision_timeZero_diagonal_le_seven

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPrecisionDiagonalBound
