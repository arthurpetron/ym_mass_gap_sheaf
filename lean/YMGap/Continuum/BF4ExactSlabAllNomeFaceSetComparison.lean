/-
# All-nome normalized comparison between original intermediate actions

An eventual same-cutoff determinant estimate passes to the constructed
face-set expectations, for every rational 0<w<1. Both actual partitions
cancel BEFORE the cutoff limit. The output keeps exactly the supplied
coefficient b, without a volume-dependent reciprocal penalty.

The one-face specialization uses its actual cutoff-dependent heat insertion.
It does not pass that changing insertion through a fixed-observable limit.
The spatial bound on the determinant/covariance remains an explicit input;
this module removes a normalization guard, not the missing decay estimate.
-/

import YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
import YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison
import YMGap.Continuum.BF4ExactSlabFaceInsertionDeterminant

namespace YMGap.Continuum.BF4ExactSlabAllNomeFaceSetComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabFaceInsertionDeterminant
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent : Nat)
  (left : List Nat) (hl : ∀ id, id ∈ left → id ∈ slabPhysicalFaceEdges extent)
  (right : List Nat) (hr : ∀ id, id ∈ right → id ∈ slabPhysicalFaceEdges extent)

local notation "blocks" => List.length (boundaryCompleteSlabLinks extent)
local notation "Nl" => numerator w blocks extent left
local notation "Nr" => numerator w blocks extent right
local notation "Zl" => heatProductHaar w blocks extent left
local notation "Zr" => heatProductHaar w blocks extent right
local notation "El" => expectation w hw0 hw1 extent left hl
local notation "Er" => expectation w hw0 hw1 extent right hr
local notation "Fl" => finiteValue w hw0 hw1 extent left hl
local notation "Fr" => finiteValue w hw0 hw1 extent right hr

/-- No reciprocal ceiling survives the finite same-action cancellation. -/
theorem finite_comparison_bound (p : RatPoly) (b : Q') (n : Nat)
    (h : Q'.abs (Nl p (headCutoff w+n) * Zr (headCutoff w+n) +
      -(Nr p (headCutoff w+n) * Zl (headCutoff w+n))) ≤
        b * (Zl (headCutoff w+n) * Zr (headCutoff w+n))) :
    Q'.abs (Fl p n + -(Fr p n)) ≤ b :=
  BF4ExactSlabFaceSetBoundaryComparison.ratio_difference_bound _ _ _ _ b
    (Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 left)
      (partition_floor hw0 hw1 extent left hl _ (Nat.le_add_right _ _)))
    (Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 right)
      (partition_floor hw0 hw1 extent right hr _ (Nat.le_add_right _ _))) h

/-- The coefficient is preserved exactly, including an arbitrary initial
cutoff threshold. Its spatial smallness is NOT assumed to be automatic. -/
theorem comparison_bound_eventually (p : RatPoly) (b : Q') (K0 : Nat)
    (h : ∀ K, K0 ≤ K → Q'.abs (Nl p K * Zr K + -(Nr p K * Zl K)) ≤ b * (Zl K * Zr K)) :
    leEv (CReal.abs (CReal.sub (El p) (Er p))) (ofQ' b) := by
  have hsum := convergesTo_abs (convergesTo_add
    (finite_converges w hw0 hw1 extent left hl p)
    (TrigAddCReal.convergesTo_neg (finite_converges w hw0 hw1 extent right hr p)))
  have hc : ConvergesTo (fun n => ofQ' (Q'.abs (Fl p n + -(Fr p n))))
      (CReal.abs (CReal.sub (El p) (Er p))) := by
    refine TrigAddCReal.convergesTo_congr_seq ?_ hsum
    intro n
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  apply leEv_of_ofQ'_limit_le hc (convergesTo_const (ofQ' b))
  intro epsilon he
  refine ⟨K0, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _
    (finite_comparison_bound w hw0 hw1 extent left hl right hr p b n
      (h _ (Nat.le_trans hn (Nat.le_add_left _ _))))
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))

/-- Actual one-face covariance under the preceding action, with both
original partitions. The heat insertion depends on K and stays inside
the finite hypothesis throughout the limit passage. -/
theorem insertion_bound_eventually (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (id : Nat) (hid : id ∈ slabPhysicalFaceEdges extent) (p : RatPoly) (b : Q') (K0 : Nat)
    (h : ∀ K, K0 ≤ K →
      Q'.abs (numerator w blocks extent ids (polyMul p (faceHeatPolynomial w K extent id)) K *
          heatProductHaar w blocks extent ids K +
        -(numerator w blocks extent ids p K *
          numerator w blocks extent ids (faceHeatPolynomial w K extent id) K)) ≤
      b * (heatProductHaar w blocks extent (ids++[id]) K * heatProductHaar w blocks extent ids K)) :
    let hnew : ∀ j, j ∈ ids++[id] → j ∈ slabPhysicalFaceEdges extent := fun j hj => by
      rcases List.mem_append.mp hj with hleft | hright
      · exact hi j hleft
      · have he := List.mem_singleton.mp hright
        subst j
        exact hid
    leEv (CReal.abs (CReal.sub (expectation w hw0 hw1 extent (ids++[id]) hnew p)
      (expectation w hw0 hw1 extent ids hi p))) (ofQ' b) := by
  dsimp only
  apply comparison_bound_eventually w hw0 hw1 extent (ids++[id]) _ ids hi p b K0
  intro K hK
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (face_insertion_determinant w K extent ids id p))) (h K hK)

end YMGap.Continuum.BF4ExactSlabAllNomeFaceSetComparison

#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetComparison.finite_comparison_bound
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetComparison.comparison_bound_eventually
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetComparison.insertion_bound_eventually
