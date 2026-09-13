/-
# A certified lower-half amplitude supplies the ORIGINAL full-action floor

The original lower-product Cauchy modulus controls absolute amplitudes, so
either sign of a finite retained channel is allowed. If b + epsilon is at
most its absolute Haar value at a tail-certified anchor, every later lower
amplitude has magnitude at least b. The retained-channel square bound gives
Z_K >= b^2 and the SAME full action limit has the explicit floor b^2.

This produces the existing finite full-action certificate and non-nullness
of the actual completed full unit. It needs finite lower-half data; no
successful family of such data, universal non-nullness, normalization,
stationarity, strict gap or continuum limit is asserted.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel
import YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCertifiedNonzero

namespace YMGap.Continuum.BF4ExactSlabAllExtentLowerActionFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
open YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS
open YMGap.Continuum.BF4ExactSlabAllExtentFiniteBoundaryObservable
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

private theorem add_cancel {a b c : Q'} (h : a + c ≤ b + c) : a ≤ b := by
  have hc (x : Q') : (x + c) + (-c) ≈ x :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv x c (-c))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left x _ _ (Q'.add_neg_self_eqv c))
        (Q'.eqv_of_eq (Q'.add_zero' x)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (hc a))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (-c) h) (Q'.le_of_eqv (hc b)))

private theorem abs_close {a b e : Q'} (h1 : a ≤ b + e) (h2 : b ≤ a + e) :
    Q'.abs a ≤ Q'.abs b + e := by
  by_cases ha : (0 : Q') ≤ a
  · rw [Q'.abs, if_pos ha]
    exact Q'.le_trans' _ _ _ h1 (Q'.add_le_add_right _ _ e (Q'.le_abs_self b))
  · rw [Q'.abs, if_neg ha]
    have hn := Q'.add_le_add_right _ _ e (Q'.neg_le_neg h2)
    have hc : (-(a + e)) + e ≈ -a :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ e (Q'.neg_add_eqv a e))
        (Q'.sub_add_cancel_eqv (-a) e)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hc)
      (Q'.le_trans' _ _ _ hn (Q'.add_le_add_right _ _ e (Q'.neg_le_abs b)))

private theorem abs_square (a : Q') : Q'.abs a * Q'.abs a ≈ a * a := by
  by_cases ha : (0 : Q') ≤ a
  · rw [Q'.abs, if_pos ha]; exact Q'.eqv_refl _
  · rw [Q'.abs, if_neg ha]
    exact Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv a (-a))
      (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv a a)) (Q'.neg_neg_eqv _))

def lowerActionCutoff (w : Q') (half : Nat) (epsilon : Q') : Nat :=
  heatProductCutoff w (centralExtent half) (centralLowerFaceIds half) epsilon

theorem lowerAction_abs_close (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (anchor K : Nat)
    (ha : lowerActionCutoff w half epsilon ≤ anchor) (hK : lowerActionCutoff w half epsilon ≤ K) :
    Q'.abs (lowerActionValue w anchor half) ≤ Q'.abs (lowerActionValue w K half) + epsilon := by
  have h := (heatProductHaarCauchy w hw0 hw1
    (boundaryCompleteSlabLinks (centralExtent half)).length (centralExtent half)
    (centralLowerFaceIds half)).bound epsilon hepsilon anchor K ha hK
  exact abs_close h.1 h.2

theorem lowerAction_abs_floor (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (epsilon b : Q') (hepsilon : (0 : Q') < epsilon) (anchor : Nat)
    (ha : lowerActionCutoff w half epsilon ≤ anchor)
    (hb : b + epsilon ≤ Q'.abs (lowerActionValue w anchor half))
    (K : Nat) (hK : lowerActionCutoff w half epsilon ≤ K) :
    b ≤ Q'.abs (lowerActionValue w K half) :=
  add_cancel (Q'.le_trans' _ _ _ hb (lowerAction_abs_close w hw0 hw1 half epsilon hepsilon anchor K ha hK))

theorem fullAction_finite_floor_from_lower (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (epsilon b : Q') (hepsilon : (0 : Q') < epsilon) (hb0 : (0 : Q') ≤ b) (anchor : Nat)
    (ha : lowerActionCutoff w half epsilon ≤ anchor)
    (hb : b + epsilon ≤ Q'.abs (lowerActionValue w anchor half))
    (K : Nat) (hK : lowerActionCutoff w half epsilon ≤ K) :
    b * b ≤ fullActionValue w K half := by
  have h := lowerAction_abs_floor w hw0 hw1 half epsilon b hepsilon anchor ha hb K hK
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ b h hb0)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h (Q'.abs_nonneg _))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_square _)) (fullAction_lower_square (Q'.le_of_lt hw0) K half)))

theorem fullActionLimit_floor_from_lower (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (epsilon b : Q') (hepsilon : (0 : Q') < epsilon) (hb0 : (0 : Q') ≤ b) (anchor : Nat)
    (ha : lowerActionCutoff w half epsilon ≤ anchor)
    (hb : b + epsilon ≤ Q'.abs (lowerActionValue w anchor half)) :
    ExpPos.geRat (fullActionLimit w hw0 hw1 half) (b * b) := by
  apply ExpPos.geRat_of_eventually
  refine ⟨lowerActionCutoff w half epsilon, fun n hn => ?_⟩
  unfold fullActionLimit
  rw [heatProductHaarLimit_approx]
  exact fullAction_finite_floor_from_lower w hw0 hw1 half epsilon b hepsilon hb0 anchor ha hb _
    (Nat.le_trans hn (CReal.self_le_QMhat _ _ n))

private theorem square_pos {b : Q'} (hb : (0 : Q') < b) : (0 : Q') < b * b :=
  CReal.pos_of_num_pos (Int.mul_pos (CReal.num_pos_of_pos hb) (CReal.num_pos_of_pos hb))

/-- A producer for the existing certificate, using only a smaller original integral. -/
def actionFloorFromLowerAnchor (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (epsilon b : Q') (hepsilon : (0 : Q') < epsilon) (hb0 : (0 : Q') < b) (anchor : Nat)
    (ha : lowerActionCutoff w half epsilon ≤ anchor)
    (hb : b + epsilon ≤ Q'.abs (lowerActionValue w anchor half)) : FiniteActionFloor w half :=
  FiniteActionFloor.ofLimitFloor w hw0 hw1 half (b * b) (square_pos hb0)
    (fullActionLimit_floor_from_lower w hw0 hw1 half epsilon b hepsilon (Q'.le_of_lt hb0) anchor ha hb)

theorem completedHeatUnit_ne_zero_from_lower (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (epsilon b : Q') (hepsilon : (0 : Q') < epsilon) (hb0 : (0 : Q') < b) (anchor : Nat)
    (ha : lowerActionCutoff w half epsilon ≤ anchor)
    (hb : b + epsilon ≤ Q'.abs (lowerActionValue w anchor half)) :
    completedHeatUnit w hw0 hw1 half ≠
      cutoffLimitEmbed w (Q'.le_of_lt hw0) (BoundaryObservable.zero half) :=
  BF4ExactSlabAllExtentHeatUnitCertifiedNonzero.completedHeatUnit_ne_zero hw0 hw1
    (actionFloorFromLowerAnchor w hw0 hw1 half epsilon b hepsilon hb0 anchor ha hb)

end YMGap.Continuum.BF4ExactSlabAllExtentLowerActionFloor

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentLowerActionFloor.lowerActionCutoff
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentLowerActionFloor.lowerAction_abs_close
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentLowerActionFloor.lowerAction_abs_floor
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentLowerActionFloor.fullAction_finite_floor_from_lower
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentLowerActionFloor.fullActionLimit_floor_from_lower
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentLowerActionFloor.actionFloorFromLowerAnchor
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentLowerActionFloor.completedHeatUnit_ne_zero_from_lower
