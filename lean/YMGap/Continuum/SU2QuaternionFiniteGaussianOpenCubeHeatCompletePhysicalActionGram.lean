/-
# Complete literal physical action Gram

The corrected heat action is enumerated by the actual internal-face and
comb-gauge-link lists, while the checked precision theorem uses their canonical
finite index ranges.  This leaf reindexes those literal carriers and proves
that the complete physical plaquette-plus-kinetic Gram is exactly the
canonical physical action Gram.  The kinetic row retains its opposite
orientation until the product of the two row entries, where the two signs
cancel.

This is a finite physical-coordinate identity.  It does not yet transport the
complete list through the three-color Heron pullback, identify the resulting
noise-coordinate scaling kernel with the covariance-residual bilinear, prove
a uniform bound, compare the ORIGINAL law, control higher remainders, or
establish a continuum theory or mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionRows

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCompletePhysicalActionGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatPhysicalActionRows

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr_local {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

private theorem listQSum_congr_local {Index : Type}
    (left right : Index → Q') : ∀ items : List Index,
    (∀ item, item ∈ items → left item ≈ right item) →
    listQSum left items ≈ listQSum right items
  | [], _ => Q'.eqv_refl _
  | item :: items, hypothesis =>
      Q'.add_eqv_congr'
        (hypothesis item List.mem_cons_self)
        (listQSum_congr_local left right items
          (fun other membership =>
            hypothesis other (List.mem_cons_of_mem item membership)))

private theorem listQSum_map_local {Index Value : Type}
    (value : Value → Q') (transform : Index → Value) :
    ∀ items : List Index,
      listQSum value (items.map transform) =
        listQSum (fun item => value (transform item)) items
  | [] => rfl
  | _item :: items => by
      simp only [List.map, listQSum]
      rw [listQSum_map_local value transform items]

private theorem map_range_getD_local {Value : Type}
    (items : List Value) (fallback : Value) :
    (List.range items.length).map
        (fun index => items.getD index fallback) = items := by
  induction items with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.length_cons]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      change head :: (List.range tail.length).map
        (fun index => tail.getD index fallback) = head :: tail
      rw [induction]

private theorem getD_mem_local {Value : Type} :
    ∀ {items : List Value} {fallback : Value} {index : Nat},
      index < items.length → items.getD index fallback ∈ items
  | [], _, _, hindex => absurd hindex (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => List.mem_cons_self
  | _ :: _tail, _, _index + 1, hindex =>
      List.mem_cons_of_mem _
        (getD_mem_local (Nat.lt_of_succ_lt_succ hindex))

private theorem idxOf_getD_local {Value : Type} [BEq Value] [LawfulBEq Value] :
    ∀ (items : List Value) (fallback : Value), items.Nodup →
      ∀ index, index < items.length →
        items.idxOf (items.getD index fallback) = index
  | [], _, _, index, hindex => absurd hindex (Nat.not_lt_zero _)
  | head :: tail, _, _, 0, _ => by
      show (head :: tail).idxOf head = 0
      rw [List.idxOf_cons,
        show (head == head) = true from beq_iff_eq.mpr rfl]
      rfl
  | head :: tail, fallback, hnodup, index + 1, hindex => by
      have hnodup' := List.nodup_cons.mp hnodup
      have hindex' : index < tail.length := Nat.lt_of_succ_lt_succ hindex
      have hmem : tail.getD index fallback ∈ tail :=
        getD_mem_local hindex'
      have hne : (head == tail.getD index fallback) = false := by
        cases heq : (head == tail.getD index fallback) with
        | false => rfl
        | true => exact absurd ((beq_iff_eq.mp heq) ▸ hmem) hnodup'.1
      show (head :: tail).idxOf (tail.getD index fallback) = index + 1
      rw [List.idxOf_cons, hne, cond_false,
        idxOf_getD_local tail fallback hnodup'.2 index hindex']

private def fallbackFace : Z4Plaq := ((0, 0, 0, 0), .p01)

private def fallbackLink : Z4Link := ((0, 0, 0, 0), .x0)

/-- Complete literal physical action-row Gram over the actual finite face and
comb-gauge-link carriers. -/
def combGaugeFreeHistoryLiteralPhysicalActionGram
    (timeBonds width left right : Nat) : Q' :=
  listQSum
      (fun time => listQSum
        (fun face =>
          combGaugeFreeHistoryPlaquettePhysicalActionRow
              width time face left *
            combGaugeFreeHistoryPlaquettePhysicalActionRow
              width time face right)
        (internalOpenCubeFaces width))
      (List.range (timeBonds + 1)) +
    listQSum
      (fun bond => listQSum
        (fun link =>
          combGaugeFreeHistoryKineticPhysicalActionRow
              width bond link left *
            combGaugeFreeHistoryKineticPhysicalActionRow
              width bond link right)
        (combGaugeLinks width))
      (List.range timeBonds)

private theorem plaquettePhysicalActionRow_face_sum
    (timeBonds width time left right : Nat)
    (hleft : left <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hright : right <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    listQSum
        (fun face =>
          combGaugeFreeHistoryPlaquettePhysicalActionRow
              width time face left *
            combGaugeFreeHistoryPlaquettePhysicalActionRow
              width time face right)
        (internalOpenCubeFaces width) ≈
      listQSum
        (fun faceIndex =>
          combGaugeFreeHistorySpatialActionRow
              width time faceIndex left *
            combGaugeFreeHistorySpatialActionRow
              width time faceIndex right)
        (List.range (internalOpenCubeFaceCount width)) := by
  let faceValue := fun face : Z4Plaq =>
    combGaugeFreeHistoryPlaquettePhysicalActionRow width time face left *
      combGaugeFreeHistoryPlaquettePhysicalActionRow width time face right
  have hreindex :
      listQSum faceValue (internalOpenCubeFaces width) =
        listQSum
          (fun faceIndex => faceValue
            ((internalOpenCubeFaces width).getD faceIndex fallbackFace))
          (List.range (internalOpenCubeFaceCount width)) := by
    unfold internalOpenCubeFaceCount
    calc
      listQSum faceValue (internalOpenCubeFaces width) =
          listQSum faceValue
            ((List.range (internalOpenCubeFaces width).length).map
              (fun faceIndex =>
                (internalOpenCubeFaces width).getD faceIndex fallbackFace)) :=
        congrArg (listQSum faceValue)
          (map_range_getD_local
            (internalOpenCubeFaces width) fallbackFace).symm
      _ = listQSum
          (fun faceIndex => faceValue
            ((internalOpenCubeFaces width).getD faceIndex fallbackFace))
          (List.range (internalOpenCubeFaces width).length) :=
        listQSum_map_local faceValue
          (fun faceIndex =>
            (internalOpenCubeFaces width).getD faceIndex fallbackFace)
          (List.range (internalOpenCubeFaces width).length)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq hreindex) ?_
  apply listQSum_congr_local
  intro faceIndex hfaceIndex
  have hindex : faceIndex < internalOpenCubeFaceCount width :=
    List.mem_range.mp hfaceIndex
  have hface :
      (internalOpenCubeFaces width).getD faceIndex fallbackFace ∈
        internalOpenCubeFaces width := by
    exact getD_mem_local hindex
  have hidxOf :
      (internalOpenCubeFaces width).idxOf
          ((internalOpenCubeFaces width).getD faceIndex fallbackFace) =
        faceIndex := by
    exact idxOf_getD_local (internalOpenCubeFaces width) fallbackFace
      (internalOpenCubeFaces_nodup width) faceIndex hindex
  have hleftRow :=
    combGaugeFreeHistoryPlaquettePhysicalActionRow_eq_spatialActionRow
      timeBonds width time left
      ((internalOpenCubeFaces width).getD faceIndex fallbackFace)
      hleft hface
  have hrightRow :=
    combGaugeFreeHistoryPlaquettePhysicalActionRow_eq_spatialActionRow
      timeBonds width time right
      ((internalOpenCubeFaces width).getD faceIndex fallbackFace)
      hright hface
  rw [hidxOf] at hleftRow hrightRow
  exact mul_congr_local hleftRow hrightRow

private theorem kineticPhysicalActionRow_link_sum
    (timeBonds width bond left right : Nat)
    (hleft : left <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hright : right <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    listQSum
        (fun link =>
          combGaugeFreeHistoryKineticPhysicalActionRow
              width bond link left *
            combGaugeFreeHistoryKineticPhysicalActionRow
              width bond link right)
        (combGaugeLinks width) ≈
      listQSum
        (fun gaugeIndex =>
          combGaugeFreeHistoryTemporalActionRow
              width bond gaugeIndex left *
            combGaugeFreeHistoryTemporalActionRow
              width bond gaugeIndex right)
        (List.range (combGaugeEdgeCount width)) := by
  let linkValue := fun link : Z4Link =>
    combGaugeFreeHistoryKineticPhysicalActionRow width bond link left *
      combGaugeFreeHistoryKineticPhysicalActionRow width bond link right
  have hreindex :
      listQSum linkValue (combGaugeLinks width) =
        listQSum
          (fun gaugeIndex => linkValue
            ((combGaugeLinks width).getD gaugeIndex fallbackLink))
          (List.range (combGaugeEdgeCount width)) := by
    unfold combGaugeEdgeCount
    calc
      listQSum linkValue (combGaugeLinks width) =
          listQSum linkValue
            ((List.range (combGaugeLinks width).length).map
              (fun gaugeIndex =>
                (combGaugeLinks width).getD gaugeIndex fallbackLink)) :=
        congrArg (listQSum linkValue)
          (map_range_getD_local
            (combGaugeLinks width) fallbackLink).symm
      _ = listQSum
          (fun gaugeIndex => linkValue
            ((combGaugeLinks width).getD gaugeIndex fallbackLink))
          (List.range (combGaugeLinks width).length) :=
        listQSum_map_local linkValue
          (fun gaugeIndex =>
            (combGaugeLinks width).getD gaugeIndex fallbackLink)
          (List.range (combGaugeLinks width).length)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq hreindex) ?_
  apply listQSum_congr_local
  intro gaugeIndex hgaugeIndex
  have hindex : gaugeIndex < combGaugeEdgeCount width :=
    List.mem_range.mp hgaugeIndex
  have hlink :
      (combGaugeLinks width).getD gaugeIndex fallbackLink ∈
        combGaugeLinks width := by
    exact getD_mem_local hindex
  have hidxOf :
      (combGaugeLinks width).idxOf
          ((combGaugeLinks width).getD gaugeIndex fallbackLink) =
        gaugeIndex := by
    exact idxOf_getD_local (combGaugeLinks width) fallbackLink
      (combGaugeLinks_nodup width) gaugeIndex hindex
  have hleftRow :=
    combGaugeFreeHistoryKineticPhysicalActionRow_eq_neg_temporalActionRow
      timeBonds width bond left
      ((combGaugeLinks width).getD gaugeIndex fallbackLink)
      hleft hlink
  have hrightRow :=
    combGaugeFreeHistoryKineticPhysicalActionRow_eq_neg_temporalActionRow
      timeBonds width bond right
      ((combGaugeLinks width).getD gaugeIndex fallbackLink)
      hright hlink
  rw [hidxOf] at hleftRow hrightRow
  refine Q'.eqv_trans _ _ _
    (mul_congr_local hleftRow hrightRow) ?_
  exact poly_identity_of_normal_eq
    (.mul (.neg (.var 0)) (.neg (.var 1)))
    (.mul (.var 0) (.var 1))
    (by decide) (fun
      | 0 => combGaugeFreeHistoryTemporalActionRow
          width bond gaugeIndex left
      | _ => combGaugeFreeHistoryTemporalActionRow
          width bond gaugeIndex right)

/-- The complete literal physical insertion lists have exactly the canonical
physical action Gram used by the precision theorem. -/
theorem combGaugeFreeHistoryLiteralPhysicalActionGram_eq_canonical
    (timeBonds width left right : Nat)
    (hleft : left <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hright : right <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    combGaugeFreeHistoryLiteralPhysicalActionGram
        timeBonds width left right ≈
      combGaugeFreeHistoryPhysicalActionGram
        timeBonds width left right := by
  unfold combGaugeFreeHistoryLiteralPhysicalActionGram
    combGaugeFreeHistoryPhysicalActionGram
  exact Q'.add_eqv_congr'
    (listQSum_congr_local _ _ (List.range (timeBonds + 1))
      (fun time _membership =>
        plaquettePhysicalActionRow_face_sum
          timeBonds width time left right hleft hright))
    (listQSum_congr_local _ _ (List.range timeBonds)
      (fun bond _membership =>
        kineticPhysicalActionRow_link_sum
          timeBonds width bond left right hleft hright))

/-- The complete literal physical insertion lists have entrywise Gram equal
to the FREE-history precision. -/
theorem combGaugeFreeHistoryLiteralPhysicalActionGram_eq_precision
    (timeBonds width left right : Nat)
    (hleft : left <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hright : right <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    combGaugeFreeHistoryLiteralPhysicalActionGram
        timeBonds width left right ≈
      combGaugeFreeHistoryPrecision timeBonds width left right := by
  exact Q'.eqv_trans _ _ _
    (combGaugeFreeHistoryLiteralPhysicalActionGram_eq_canonical
      timeBonds width left right hleft hright)
    (combGaugeFreeHistoryPhysicalActionGram_eq_precision
      timeBonds width left right hleft hright)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCompletePhysicalActionGram

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCompletePhysicalActionGram.combGaugeFreeHistoryLiteralPhysicalActionGram_eq_canonical
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCompletePhysicalActionGram.combGaugeFreeHistoryLiteralPhysicalActionGram_eq_precision
