/-
# Uniform central Heron-row norm floor

The central `p01` face has exactly two comb-gauge chord coefficients, `-1` on
its base `y` link and `+1` on its upper-`x` `y` link.  Selecting the smaller of
their comb-coordinate indices gives the first nonzero coordinate of the face
curl.  The covariance LDL factor is unit upper triangular, so the pulled row
at that noise coordinate isolates one Heron square-root iterate.  The uniform
covariance-pivot floor then gives a width- and stage-independent row-norm floor
`1/7`.

Consumer: the central weighted radial-ratio lower bound.  This remains a
finite rational FREE-reference statement.  It does not identify the ORIGINAL
interacting law, construct a continuum limit, or prove a physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralCrossCovarianceFloor
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCovarianceDiagonalFloor

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronRowNormFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralCrossCovarianceFloor
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCovarianceDiagonalFloor
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows

local infix:50 " ≈ " => Q'.eqv

/-- The base `y`-directed chord of the selected central `p01` face. -/
def bulkSourceCentralBaseChordLink (m : Nat) : Z4Link :=
  ((bulkSourceCentralFace m).1, .x1)

/-- The base central-face edge is a comb-gauge chord. -/
theorem bulkSourceCentralBaseChordLink_mem (m : Nat) (hm : 0 < m) :
    bulkSourceCentralBaseChordLink m ∈
      combGaugeLinks (bulkSourceWidth (4 * m)) := by
  have hfaceMem := bulkSourceCentralFace_mem_source m hm
  have hfaceInternal := bulkSourceFace_internal hfaceMem
  have hfaceProperty :=
    (internalOpenCubeFaces_mem_iff (bulkSourceWidth (4 * m))
      (bulkSourceCentralFace m)).mp hfaceInternal
  have hedge : bulkSourceCentralBaseChordLink m ∈
      edgesOf (bulkSourceCentralFace m) := by
    simp [bulkSourceCentralBaseChordLink, bulkSourceCentralFace,
      bulkSourceFaceAt, edgesOf, dirsOf]
  apply (combGaugeLinks_mem_iff
    (bulkSourceWidth (4 * m)) (bulkSourceCentralBaseChordLink m)).mpr
  refine ⟨internalOpenCubeFace_edge_property hfaceProperty hedge, ?_⟩
  rintro ⟨_hinternal, hshape⟩
  unfold bulkSourceCentralBaseChordLink bulkSourceCentralFace bulkSourceFaceAt at hshape
  simp only at hshape
  omega

/-- Comb-coordinate index of the base central-face chord. -/
def bulkSourceCentralBaseChordIndex (m : Nat) : Nat :=
  (combGaugeLinks (bulkSourceWidth (4 * m))).idxOf
    (bulkSourceCentralBaseChordLink m)

theorem bulkSourceCentralBaseChordIndex_lt (m : Nat) (hm : 0 < m) :
    bulkSourceCentralBaseChordIndex m <
      combGaugeEdgeCount (bulkSourceWidth (4 * m)) :=
  List.idxOf_lt_length_of_mem (bulkSourceCentralBaseChordLink_mem m hm)

/-- The base central chord has oriented curl coefficient `-1`. -/
theorem bulkSourceCentralFace_curl_baseChord_eq_neg_one
    (m : Nat) (hm : 0 < m) :
    combGaugeCurl (bulkSourceWidth (4 * m))
        (bulkSourceInternalFaceIndex (4 * m)
          (bulkSourceCentralFaceIndex m))
        (bulkSourceCentralBaseChordIndex m) = -1 := by
  have hface := bulkSourceFace_internal
    (bulkSourceCentralFace_mem_source m hm)
  have hlink := bulkSourceCentralBaseChordLink_mem m hm
  have hcurl := combGaugeCurl_idxOf hface hlink
  unfold bulkSourceInternalFaceIndex bulkSourceCentralBaseChordIndex
  rw [selectedBulkSourceFace_centralFaceIndex m hm]
  refine Eq.trans hcurl ?_
  unfold internalBoundaryCoefficient orientedBoundaryCoefficient
    bulkSourceCentralBaseChordLink bulkSourceCentralFace bulkSourceFaceAt
  simp [dirsOf]
  rfl

/-- The first of the two nonzero central-face chord coordinates, independent
of how the global chord list happens to order them. -/
def bulkSourceCentralFirstChordIndex (m : Nat) : Nat :=
  Nat.min (bulkSourceCentralBaseChordIndex m)
    (bulkSourceCentralChordIndex m)

theorem bulkSourceCentralFirstChordIndex_lt (m : Nat) (hm : 0 < m) :
    bulkSourceCentralFirstChordIndex m <
      combGaugeEdgeCount (bulkSourceWidth (4 * m)) := by
  unfold bulkSourceCentralFirstChordIndex
  have hbase := bulkSourceCentralBaseChordIndex_lt m hm
  exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) hbase

private theorem selectedInternalCentralFace
    (m : Nat) (hm : 0 < m) :
    selectedInternalOpenCubeFace (bulkSourceWidth (4 * m))
        (bulkSourceInternalFaceIndex (4 * m)
          (bulkSourceCentralFaceIndex m)) =
      bulkSourceCentralFace m := by
  rw [selectedInternalOpenCubeFace_bulkSourceIndex
    (bulkSourceCentralFaceIndex_lt m hm),
    selectedBulkSourceFace_centralFaceIndex m hm]

/-- A nonzero central-face comb curl can occur only at its two `y`-directed
chord links; the two `x`-directed face edges belong to the comb tree. -/
theorem bulkSourceCentralFace_curl_support
    (m : Nat) (hm : 0 < m) {gaugeIndex : Nat}
    (hgauge : gaugeIndex <
      combGaugeEdgeCount (bulkSourceWidth (4 * m)))
    (hnonzero :
      combGaugeCurl (bulkSourceWidth (4 * m))
          (bulkSourceInternalFaceIndex (4 * m)
            (bulkSourceCentralFaceIndex m)) gaugeIndex ≠ 0) :
    selectedCombGaugeLink (bulkSourceWidth (4 * m)) gaugeIndex =
        bulkSourceCentralBaseChordLink m ∨
      selectedCombGaugeLink (bulkSourceWidth (4 * m)) gaugeIndex =
        bulkSourceCentralChordLink m := by
  let width := bulkSourceWidth (4 * m)
  let faceIndex := bulkSourceInternalFaceIndex (4 * m)
    (bulkSourceCentralFaceIndex m)
  change selectedCombGaugeLink width gaugeIndex =
        bulkSourceCentralBaseChordLink m ∨
      selectedCombGaugeLink width gaugeIndex =
        bulkSourceCentralChordLink m
  have hfaceMem := bulkSourceFace_internal
    (bulkSourceCentralFace_mem_source m hm)
  have hface : faceIndex < internalOpenCubeFaceCount width := by
    unfold faceIndex bulkSourceInternalFaceIndex width
    rw [selectedBulkSourceFace_centralFaceIndex m hm]
    exact List.idxOf_lt_length_of_mem hfaceMem
  have hboundary :
      internalBoundaryCoefficient (bulkSourceCentralFace m)
          (selectedCombGaugeLink width gaugeIndex) ≠ 0 := by
    unfold combGaugeCurl at hnonzero
    rw [if_pos ⟨hface, hgauge⟩, selectedInternalCentralFace m hm] at hnonzero
    exact hnonzero
  have hedge : selectedCombGaugeLink width gaugeIndex ∈
      edgesOf (bulkSourceCentralFace m) := by
    by_cases hmem : selectedCombGaugeLink width gaugeIndex ∈
        edgesOf (bulkSourceCentralFace m)
    · exact hmem
    · exact False.elim (hboundary
        (internalBoundaryCoefficient_zero_of_not_mem hmem))
  have hselected := selectedCombGaugeLink_mem hgauge
  have hpartition := (combGaugeLinks_mem_iff width _).mp hselected
  have hedges := hedge
  unfold width bulkSourceCentralFace bulkSourceFaceAt at hedges
  simp only [edgesOf, dirsOf, addE, List.mem_cons, List.not_mem_nil,
    or_false] at hedges
  rcases hedges with hfirst | hbase | hthird | hupper
  · have htree : CombTreeLink width
        (selectedCombGaugeLink width gaugeIndex) := by
      refine ⟨hpartition.1, ?_⟩
      rw [hfirst]
      trivial
    exact False.elim (hpartition.2 htree)
  · exact Or.inl hbase
  · have htree : CombTreeLink width
        (selectedCombGaugeLink width gaugeIndex) := by
      refine ⟨hpartition.1, ?_⟩
      rw [hthird]
      trivial
    exact False.elim (hpartition.2 htree)
  · exact Or.inr hupper

private def fallbackLink : Z4Link := ((0, 0, 0, 0), .x0)

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
      show (head :: tail).idxOf
          (tail.getD index fallbackLink) = index + 1
      rw [List.idxOf_cons, hne, cond_false,
        idxOf_getD_local tail hnodup'.2 index hindex']

private theorem idxOf_selectedCombGaugeLink
    {width gaugeIndex : Nat}
    (hgauge : gaugeIndex < combGaugeEdgeCount width) :
    (combGaugeLinks width).idxOf
        (selectedCombGaugeLink width gaugeIndex) = gaugeIndex := by
  unfold selectedCombGaugeLink
  unfold combGaugeEdgeCount at hgauge
  exact idxOf_getD_local (combGaugeLinks width)
    (combGaugeLinks_nodup width) gaugeIndex hgauge

/-- The selected minimum chord coordinate carries coefficient `-1` or `1`. -/
theorem bulkSourceCentralFace_curl_firstChord_eq_neg_one_or_eq_one
    (m : Nat) (hm : 0 < m) :
    combGaugeCurl (bulkSourceWidth (4 * m))
          (bulkSourceInternalFaceIndex (4 * m)
            (bulkSourceCentralFaceIndex m))
          (bulkSourceCentralFirstChordIndex m) = -1 ∨
      combGaugeCurl (bulkSourceWidth (4 * m))
          (bulkSourceInternalFaceIndex (4 * m)
            (bulkSourceCentralFaceIndex m))
          (bulkSourceCentralFirstChordIndex m) = 1 := by
  by_cases horder : bulkSourceCentralBaseChordIndex m ≤
      bulkSourceCentralChordIndex m
  · left
    have hmin : bulkSourceCentralFirstChordIndex m =
        bulkSourceCentralBaseChordIndex m := by
      unfold bulkSourceCentralFirstChordIndex
      exact Nat.min_eq_left horder
    rw [hmin]
    exact bulkSourceCentralFace_curl_baseChord_eq_neg_one m hm
  · right
    have hreverse : bulkSourceCentralChordIndex m ≤
        bulkSourceCentralBaseChordIndex m := Nat.le_of_not_ge horder
    have hmin : bulkSourceCentralFirstChordIndex m =
        bulkSourceCentralChordIndex m := by
      unfold bulkSourceCentralFirstChordIndex
      exact Nat.min_eq_right hreverse
    rw [hmin]
    exact bulkSourceCentralFace_curl_chord_eq_one m hm

/-- Every chord coordinate before the selected minimum has zero central-face
curl coefficient. -/
theorem bulkSourceCentralFace_curl_eq_zero_of_lt_firstChord
    (m : Nat) (hm : 0 < m) {gaugeIndex : Nat}
    (hgauge : gaugeIndex <
      combGaugeEdgeCount (bulkSourceWidth (4 * m)))
    (hbefore : gaugeIndex < bulkSourceCentralFirstChordIndex m) :
    combGaugeCurl (bulkSourceWidth (4 * m))
        (bulkSourceInternalFaceIndex (4 * m)
          (bulkSourceCentralFaceIndex m)) gaugeIndex = 0 := by
  by_cases hzero :
      combGaugeCurl (bulkSourceWidth (4 * m))
          (bulkSourceInternalFaceIndex (4 * m)
            (bulkSourceCentralFaceIndex m)) gaugeIndex = 0
  · exact hzero
  · have hsupport := bulkSourceCentralFace_curl_support
      m hm hgauge hzero
    have hselectedIndex := idxOf_selectedCombGaugeLink hgauge
    have hfalse : False := hsupport.elim
      (fun hbase => by
        have hcongr := congrArg
          (combGaugeLinks (bulkSourceWidth (4 * m))).idxOf hbase
        have heq : gaugeIndex = bulkSourceCentralBaseChordIndex m := by
          exact hselectedIndex.symm.trans hcongr
        rw [heq] at hbefore
        exact (Nat.not_lt_of_ge (Nat.min_le_left _ _)) hbefore)
      (fun hupper => by
        have hcongr := congrArg
          (combGaugeLinks (bulkSourceWidth (4 * m))).idxOf hupper
        have heq : gaugeIndex = bulkSourceCentralChordIndex m := by
          exact hselectedIndex.symm.trans hcongr
        rw [heq] at hbefore
        exact (Nat.not_lt_of_ge (Nat.min_le_right _ _)) hbefore)
    exact False.elim hfalse

/-- The flattened time-zero history row retains the selected `±1` curl
coefficient at the first chord coordinate. -/
theorem bulkSourceCentralHistoryCurlRow_firstChord_eq_neg_one_or_eq_one
    (m : Nat) (hm : 0 < m) :
    combGaugeFreeHistoryCurlRow (bulkSourceWidth (4 * m)) 0
          (bulkSourceInternalFaceIndex (4 * m)
            (bulkSourceCentralFaceIndex m))
          (bulkSourceCentralFirstChordIndex m) = -1 ∨
      combGaugeFreeHistoryCurlRow (bulkSourceWidth (4 * m)) 0
          (bulkSourceInternalFaceIndex (4 * m)
            (bulkSourceCentralFaceIndex m))
          (bulkSourceCentralFirstChordIndex m) = 1 := by
  have hfirst := bulkSourceCentralFirstChordIndex_lt m hm
  have hedgeCount : 0 <
      combGaugeEdgeCount (bulkSourceWidth (4 * m)) :=
    Nat.zero_lt_of_lt hfirst
  unfold combGaugeFreeHistoryCurlRow
  rw [show historyTime
      (combGaugeEdgeCount (bulkSourceWidth (4 * m)))
      (bulkSourceCentralFirstChordIndex m) = 0 by
        unfold historyTime
        exact Nat.div_eq_of_lt hfirst,
    if_pos rfl,
    show historySpatial
      (combGaugeEdgeCount (bulkSourceWidth (4 * m)))
      (bulkSourceCentralFirstChordIndex m) =
        bulkSourceCentralFirstChordIndex m by
      unfold historySpatial
      exact Nat.mod_eq_of_lt hfirst]
  exact bulkSourceCentralFace_curl_firstChord_eq_neg_one_or_eq_one m hm

/-- Every flattened time-zero history coordinate before the selected first
chord has zero central-face curl coefficient. -/
theorem bulkSourceCentralHistoryCurlRow_eq_zero_of_lt_firstChord
    (m : Nat) (hm : 0 < m) {coordinate : Nat}
    (hbefore : coordinate < bulkSourceCentralFirstChordIndex m) :
    combGaugeFreeHistoryCurlRow (bulkSourceWidth (4 * m)) 0
        (bulkSourceInternalFaceIndex (4 * m)
          (bulkSourceCentralFaceIndex m)) coordinate = 0 := by
  have hfirst := bulkSourceCentralFirstChordIndex_lt m hm
  have hcoordinate : coordinate <
      combGaugeEdgeCount (bulkSourceWidth (4 * m)) :=
    Nat.lt_trans hbefore hfirst
  unfold combGaugeFreeHistoryCurlRow
  rw [show historyTime
      (combGaugeEdgeCount (bulkSourceWidth (4 * m))) coordinate = 0 by
        unfold historyTime
        exact Nat.div_eq_of_lt hcoordinate,
    if_pos rfl,
    show historySpatial
      (combGaugeEdgeCount (bulkSourceWidth (4 * m))) coordinate = coordinate by
      unfold historySpatial
      exact Nat.mod_eq_of_lt hcoordinate]
  exact bulkSourceCentralFace_curl_eq_zero_of_lt_firstChord
    m hm hcoordinate hbefore

private theorem qListSum_eqv_zero_local
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≈ 0) →
      qListSum (items.map value) ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      simp only [List.map, qListSum]
      exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (hzero head List.mem_cons_self)
          (qListSum_eqv_zero_local value tail
            (fun item hitem =>
              hzero item (List.mem_cons_of_mem head hitem))))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem qListSum_eqv_selected_of_nodup_local
    {A : Type} [DecidableEq A] (value : A → Q') :
    ∀ (items : List A) {selected : A},
      items.Nodup → selected ∈ items →
      (∀ item, item ∈ items → item ≠ selected → value item ≈ 0) →
      qListSum (items.map value) ≈ value selected
  | [], _, _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, selected, hnodup, hmem, hzero => by
      have hnodup' := List.nodup_cons.mp hnodup
      by_cases hhead : head = selected
      · subst head
        simp only [List.map, qListSum]
        have htailZero : qListSum (tail.map value) ≈ 0 :=
          qListSum_eqv_zero_local value tail (by
            intro item hitem
            exact hzero item (List.mem_cons_of_mem selected hitem)
              (fun heq => hnodup'.1 (heq ▸ hitem)))
        exact Q'.eqv_trans _ (value selected + 0) _
          (Q'.add_eqv_congr' (Q'.eqv_refl _) htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · have hselectedTail : selected ∈ tail :=
          (List.mem_cons.mp hmem).resolve_left (fun heq => hhead heq.symm)
        simp only [List.map, qListSum]
        exact Q'.eqv_trans _ (0 + value selected) _
          (Q'.add_eqv_congr'
            (hzero head List.mem_cons_self hhead)
            (qListSum_eqv_selected_of_nodup_local value tail
              hnodup'.2 hselectedTail
              (fun item hitem hne =>
                hzero item (List.mem_cons_of_mem head hitem) hne)))
          (Q'.eqv_of_eq (Q'.zero_add' _))

/-- The single-color Heron-pulled central curl row before three-color block
placement. -/
def bulkSourceCentralHeronPulledRow
    (m stage coordinate : Nat) : Q' :=
  let width := bulkSourceWidth (4 * m)
  let coordinateCount := historyCoordinateCount 1 (combGaugeEdgeCount width)
  pulledRow coordinateCount
    (combGaugeFreeHistoryHeronTransform 1 width stage)
    (combGaugeFreeHistoryCurlRow width 0
      (bulkSourceInternalFaceIndex (4 * m)
        (bulkSourceCentralFaceIndex m))) coordinate

private theorem neg_mul_neg_self_eqv (value : Q') :
    (-value) * (-value) ≈ value * value := by
  exact Q'.eqv_trans _ _ _
    (Q'.neg_mul_eqv value (-value))
    (Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv value value))
      (Q'.neg_neg_eqv (value * value)))

/-- At the first nonzero central chord coordinate, the pulled-row square is
exactly the Heron iterate square of the corresponding covariance pivot. -/
theorem bulkSourceCentralHeronPulledRow_firstChord_square
    (m : Nat) (hm : 0 < m) (stage : Nat) :
    bulkSourceCentralHeronPulledRow m stage
          (bulkSourceCentralFirstChordIndex m) *
        bulkSourceCentralHeronPulledRow m stage
          (bulkSourceCentralFirstChordIndex m) ≈
      CReal.heronSeq
          ((combGaugeFreeHistoryCovariancePositiveLDL
            1 (bulkSourceWidth (4 * m))).diagonal
              (bulkSourceCentralFirstChordIndex m)) stage *
        CReal.heronSeq
          ((combGaugeFreeHistoryCovariancePositiveLDL
            1 (bulkSourceWidth (4 * m))).diagonal
              (bulkSourceCentralFirstChordIndex m)) stage := by
  let width := bulkSourceWidth (4 * m)
  let coordinateCount := historyCoordinateCount 1 (combGaugeEdgeCount width)
  let faceIndex := bulkSourceInternalFaceIndex (4 * m)
    (bulkSourceCentralFaceIndex m)
  let first := bulkSourceCentralFirstChordIndex m
  let row := combGaugeFreeHistoryCurlRow width 0 faceIndex
  let transform := combGaugeFreeHistoryHeronTransform 1 width stage
  let diagonal :=
    (combGaugeFreeHistoryCovariancePositiveLDL 1 width).diagonal first
  let root := CReal.heronSeq diagonal stage
  have hfirstEdge : first < combGaugeEdgeCount width := by
    unfold first width
    exact bulkSourceCentralFirstChordIndex_lt m hm
  have hfirstCount : first < coordinateCount := by
    unfold coordinateCount historyCoordinateCount historySliceCount
    omega
  have hpulled : bulkSourceCentralHeronPulledRow m stage first ≈
      row first * transform first first := by
    unfold bulkSourceCentralHeronPulledRow
    dsimp only
    change qListSum
        ((List.range coordinateCount).map
          (fun physicalIndex =>
            row physicalIndex * transform physicalIndex first)) ≈
      row first * transform first first
    apply qListSum_eqv_selected_of_nodup_local
    · exact
        YMGap.Continuum.FiniteRationalPositiveDefiniteLDL.rangeNodupLocal _
    · exact List.mem_range.mpr hfirstCount
    · intro physicalIndex hphysical hne
      have hphysicalCount : physicalIndex < coordinateCount :=
        List.mem_range.mp hphysical
      rcases Nat.lt_or_gt_of_ne hne with hbefore | hafter
      · have hrowZero : row physicalIndex = 0 := by
          change physicalIndex < bulkSourceCentralFirstChordIndex m at hbefore
          unfold row faceIndex width
          exact bulkSourceCentralHistoryCurlRow_eq_zero_of_lt_firstChord
            m hm hbefore
        rw [hrowZero]
        exact Q'.zero_mul_eqv _
      · have hlowerZero :=
          combGaugeFreeHistoryCovariancePositiveLDL_lower_zero_of_column_lt_row
            (timeBonds := 1) (width := width)
            hphysicalCount hfirstCount hafter
        unfold transform combGaugeFreeHistoryHeronTransform heronLDLTransform
        rw [hlowerZero]
        exact Q'.eqv_trans _ (row physicalIndex * 0) _
          (Q'.mul_eqv_congr_left (row physicalIndex) _ _
            (Q'.zero_mul_eqv _))
          (Q'.mul_zero_eqv _)
  have htransform : transform first first ≈ root := by
    have hlower :=
      combGaugeFreeHistoryCovariancePositiveLDL_lower_diagonal_eq_one
        (timeBonds := 1) (width := width) hfirstCount
    unfold transform combGaugeFreeHistoryHeronTransform heronLDLTransform
      root diagonal
    rw [hlower]
    exact Q'.one_mul_eqv _
  have hsign :=
    bulkSourceCentralHistoryCurlRow_firstChord_eq_neg_one_or_eq_one m hm
  change row first = -1 ∨ row first = 1 at hsign
  change
    bulkSourceCentralHeronPulledRow m stage first *
        bulkSourceCentralHeronPulledRow m stage first ≈
      root * root
  rcases hsign with hnegative | hpositive
  · have hterm : row first * transform first first ≈ -root := by
      rw [hnegative]
      exact Q'.eqv_trans _ ((-1 : Q') * root) _
        (Q'.mul_eqv_congr_left (-1) _ _ htransform)
        (Q'.eqv_trans _ _ _
          (Q'.neg_mul_eqv 1 root)
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv root)))
    have hrow : bulkSourceCentralHeronPulledRow m stage first ≈ -root :=
      Q'.eqv_trans _ _ _ hpulled hterm
    exact Q'.eqv_trans _ ((-root) * (-root)) _
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hrow)
        (Q'.mul_eqv_congr_left _ _ _ hrow))
      (neg_mul_neg_self_eqv root)
  · have hterm : row first * transform first first ≈ root := by
      rw [hpositive]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left 1 _ _ htransform)
        (Q'.one_mul_eqv root)
    have hrow : bulkSourceCentralHeronPulledRow m stage first ≈ root :=
      Q'.eqv_trans _ _ _ hpulled hterm
    exact Q'.eqv_trans _ (root *
        bulkSourceCentralHeronPulledRow m stage first) _
      (Q'.mul_eqv_congr_right _ _ _ hrow)
      (Q'.mul_eqv_congr_left _ _ _ hrow)

/-- The Heron square-root iterate at the first central chord retains the
uniform covariance-pivot floor. -/
theorem combCovarianceDiagonalFloor_le_centralHeronRootSquare
    (m : Nat) (hm : 0 < m) (stage : Nat) :
    combCovarianceDiagonalFloor ≤
      CReal.heronSeq
          ((combGaugeFreeHistoryCovariancePositiveLDL
            1 (bulkSourceWidth (4 * m))).diagonal
              (bulkSourceCentralFirstChordIndex m)) stage *
        CReal.heronSeq
          ((combGaugeFreeHistoryCovariancePositiveLDL
            1 (bulkSourceWidth (4 * m))).diagonal
              (bulkSourceCentralFirstChordIndex m)) stage := by
  have hfirst := bulkSourceCentralFirstChordIndex_lt m hm
  have hfirstCount : bulkSourceCentralFirstChordIndex m <
      historyCoordinateCount 1
        (combGaugeEdgeCount (bulkSourceWidth (4 * m))) := by
    unfold historyCoordinateCount historySliceCount
    omega
  have hfloor : combCovarianceDiagonalFloor ≤
      (combGaugeFreeHistoryCovariancePositiveLDL
        1 (bulkSourceWidth (4 * m))).diagonal
          (bulkSourceCentralFirstChordIndex m) := by
    simpa [historyIndex] using
      (combGaugeFreeHistoryCovariancePositiveLDL_timeZero_diagonal_floor
        (width := bulkSourceWidth (4 * m)) hfirst)
  exact Q'.le_trans' _ _ _ hfloor
    (CReal.heronSeq_sq_ge
      ((combGaugeFreeHistoryCovariancePositiveLDL
        1 (bulkSourceWidth (4 * m))).diagonal
          (bulkSourceCentralFirstChordIndex m))
      ((combGaugeFreeHistoryCovariancePositiveLDL
        1 (bulkSourceWidth (4 * m))).diagonal_pos hfirstCount)
      stage)

/-- The selected pulled-row square itself retains the same uniform floor. -/
theorem combCovarianceDiagonalFloor_le_centralHeronPulledRowSquare
    (m : Nat) (hm : 0 < m) (stage : Nat) :
    combCovarianceDiagonalFloor ≤
      bulkSourceCentralHeronPulledRow m stage
          (bulkSourceCentralFirstChordIndex m) *
        bulkSourceCentralHeronPulledRow m stage
          (bulkSourceCentralFirstChordIndex m) := by
  exact Q'.le_trans' _ _ _
    (combCovarianceDiagonalFloor_le_centralHeronRootSquare m hm stage)
    (Q'.ge_of_eqv
      (bulkSourceCentralHeronPulledRow_firstChord_square m hm stage))

/-- The first color block of the actual central source row contains the
single-color pulled row at the selected coordinate. -/
theorem bulkSourceCentralHeronColorCurlRow_firstChord
    (m : Nat) (hm : 0 < m) (stage : Nat) :
    bulkSourceHeronColorCurlRow 1 (4 * m) stage 0
        (bulkSourceCentralFaceIndex m * 3)
        (bulkSourceCentralFirstChordIndex m) =
      bulkSourceCentralHeronPulledRow m stage
        (bulkSourceCentralFirstChordIndex m) := by
  have hfirst := bulkSourceCentralFirstChordIndex_lt m hm
  have hfirstCount : bulkSourceCentralFirstChordIndex m <
      historyCoordinateCount 1
        (combGaugeEdgeCount (bulkSourceWidth (4 * m))) := by
    unfold historyCoordinateCount historySliceCount
    omega
  have hdiv : bulkSourceCentralFaceIndex m * 3 / 3 =
      bulkSourceCentralFaceIndex m := by omega
  have hmod : bulkSourceCentralFaceIndex m * 3 % 3 = 0 := by omega
  unfold bulkSourceHeronColorCurlRow
    combGaugeFreeHistoryHeronColorCurlRow
    bulkSourceCentralHeronPulledRow
  rw [hdiv, hmod]
  simp only [threeColorRows, appendRow, if_pos hfirstCount]

private theorem qListSum_map_eq_listQSum_local
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      qListSum (items.map value) = listQSum value items
  | [] => rfl
  | head :: tail => congrArg (fun sum => value head + sum)
      (qListSum_map_eq_listQSum_local value tail)

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A → Q') :
    ∀ (items : List A) {witness : A},
      (∀ item, item ∈ items → (0 : Q') ≤ value item) →
      witness ∈ items →
      value witness ≤ listQSum value items
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, witness, hnonnegative, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst witness
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun item hitem =>
              hnonnegative item (List.mem_cons_of_mem head hitem)))
      · have htailLe := listQSum_member_le_nonnegative_local
          value tail
          (fun item hitem =>
            hnonnegative item (List.mem_cons_of_mem head hitem))
          htail
        have hsumLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail)
            (hnonnegative head List.mem_cons_self)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ htailLe hsumLe

private theorem square_le_finiteRowNorm2_local
    (count : Nat) (row : Nat → Q') {coordinate : Nat}
    (hcoordinate : coordinate < count) :
    row coordinate * row coordinate ≤ finiteRowNorm2 count row := by
  unfold finiteRowNorm2
  rw [qListSum_map_eq_listQSum_local]
  apply listQSum_member_le_nonnegative_local
  · intro index _
    exact SumOfSquares.q_mul_self_nonneg (row index)
  · exact List.mem_range.mpr hcoordinate

/-- The actual central color-zero Heron row has squared norm at least `1/7`,
uniformly in the positive cutoff parameter and Heron stage. -/
theorem combCovarianceDiagonalFloor_le_bulkSourceCentralHeronColorRowNorm
    (m : Nat) (hm : 0 < m) (stage : Nat) :
    let coordinateCount :=
      historyCoordinateCount 1
        (combGaugeEdgeCount (bulkSourceWidth (4 * m)))
    let rowIndex := bulkSourceCentralFaceIndex m * 3
    combCovarianceDiagonalFloor ≤
      finiteRowNorm2
        (coordinateCount + (coordinateCount + coordinateCount))
        (bulkSourceHeronColorCurlRow 1 (4 * m) stage 0 rowIndex) := by
  let coordinateCount :=
    historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth (4 * m)))
  let rowIndex := bulkSourceCentralFaceIndex m * 3
  let first := bulkSourceCentralFirstChordIndex m
  let colorRow :=
    bulkSourceHeronColorCurlRow 1 (4 * m) stage 0 rowIndex
  change combCovarianceDiagonalFloor ≤
    finiteRowNorm2
      (coordinateCount + (coordinateCount + coordinateCount)) colorRow
  have hfirstCount : first < coordinateCount := by
    unfold first coordinateCount historyCoordinateCount historySliceCount
    have hfirst := bulkSourceCentralFirstChordIndex_lt m hm
    omega
  have hcolor : colorRow first =
      bulkSourceCentralHeronPulledRow m stage first := by
    unfold colorRow rowIndex first
    exact bulkSourceCentralHeronColorCurlRow_firstChord m hm stage
  have hpointFloor : combCovarianceDiagonalFloor ≤
      colorRow first * colorRow first := by
    rw [hcolor]
    exact combCovarianceDiagonalFloor_le_centralHeronPulledRowSquare
      m hm stage
  have hpointNorm : colorRow first * colorRow first ≤
      finiteRowNorm2
        (coordinateCount + (coordinateCount + coordinateCount)) colorRow := by
    exact square_le_finiteRowNorm2_local _ colorRow (by omega)
  exact Q'.le_trans' _ _ _ hpointFloor hpointNorm

#print axioms bulkSourceCentralBaseChordLink_mem
#print axioms bulkSourceCentralFace_curl_baseChord_eq_neg_one
#print axioms bulkSourceCentralFirstChordIndex_lt
#print axioms bulkSourceCentralFace_curl_support
#print axioms bulkSourceCentralFace_curl_firstChord_eq_neg_one_or_eq_one
#print axioms bulkSourceCentralFace_curl_eq_zero_of_lt_firstChord
#print axioms bulkSourceCentralHistoryCurlRow_firstChord_eq_neg_one_or_eq_one
#print axioms bulkSourceCentralHistoryCurlRow_eq_zero_of_lt_firstChord
#print axioms bulkSourceCentralHeronPulledRow_firstChord_square
#print axioms combCovarianceDiagonalFloor_le_centralHeronRootSquare
#print axioms combCovarianceDiagonalFloor_le_centralHeronPulledRowSquare
#print axioms bulkSourceCentralHeronColorCurlRow_firstChord
#print axioms combCovarianceDiagonalFloor_le_bulkSourceCentralHeronColorRowNorm

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronRowNormFloor
