/-
# Every intrinsic ORIGINAL channel is controlled by the SAME OS form

The actual leaf's weighted limiting amplitude square is bounded by the
original full reflected numerator. The original partition reciprocal's
computed lower bound gives F*A^2 <= form(e,e), with F>0 independent of e.
F depends explicitly on the retained leaf, nome and finite volume.

Together with actual channel reconstruction this proves that an embedded
original expression is zero iff every intrinsic packet-leaf coefficient
vanishes. No completed coefficient map, Hilbert-space resolution, transfer
kernel/range theorem, volume-uniform floor or continuum/Clay claim.
-/

import YMGap.Continuum.BF4ExactSlabIntrinsicChannelOrder

namespace YMGap.Continuum.BF4ExactSlabIntrinsicChannelNormBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit
open YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction
open YMGap.Continuum.BF4ExactSlabIntrinsicChannelOrder
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private theorem weighted_square_zero (A : CReal) (v : Q') (hv : (0 : Q') < v)
    (hz : CReal.Equiv (CReal.mul (CReal.ofQ' v) (CReal.mul A A)) (CReal.ofQ' 0)) :
    CReal.Equiv A (CReal.ofQ' 0) := by
  intro epsilon he
  obtain ⟨N, hN⟩ := hz (v*(epsilon*epsilon)) (Q'.mul_pos hv (Q'.mul_pos he he))
  refine ⟨N, fun n hn => ?_⟩
  have hsq : A.approx n*A.approx n ≤ epsilon*epsilon := by
    apply Q'.le_of_mul_le_mul_left (c := v) _ hv
    have h := (hN n hn).1
    change v*(A.approx n*A.approx n) ≤ 0+v*(epsilon*epsilon) at h
    rwa [Q'.zero_add'] at h
  have ha := Q'.abs_le_two_sided (Q'.abs_le_of_sq_le_sq he hsq)
  constructor
  · exact Q'.le_trans' _ _ _ ha.1 (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _)))
  · apply Q'.le_add_of_sub_le
    change 0 + -A.approx n ≤ epsilon
    rw [Q'.zero_add']
    exact ha.2

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat} (e : PlaquetteExpression half)

local notation "actualTree" N => BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion.tree
  (interfaceExpansion (Q'.le_of_lt hw0) N half)
local notation "originalLimit" => numeratorLimit w hw0 hw1
  (List.length (boundaryCompleteSlabLinks (centralExtent half))) (centralExtent half)
  (slabPhysicalFaceEdges (centralExtent half)) (reflectedInsertion e)

theorem intrinsic_energy_bound (N : Nat) (l : Leaf (actualTree N)) :
    CReal.leEv (energyLimit w hw0 hw1 half (lower e) (.term l.weight l.channel)) originalLimit := by
  apply CReal.leEv_of_ofQ'_limit_le
    (energy_converges w hw0 hw1 half (lower e) (.term l.weight l.channel)
      (Q'.le_of_lt (interface_leaf_positive w hw0 N half l)))
    (numerator_converges w hw0 hw1 (boundaryCompleteSlabLinks (centralExtent half)).length
      (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) (reflectedInsertion e))
  intro epsilon he
  exact ⟨N, fun K hK => Q'.le_trans' _ _ _
    (intrinsic_leaf_finite_bound w (Q'.le_of_lt hw0) N K e l hK)
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he))⟩

theorem intrinsic_energy_zero_of_original_null (N : Nat) (l : Leaf (actualTree N))
    (hz : CReal.Equiv originalLimit (CReal.ofQ' 0)) :
    CReal.Equiv (energyLimit w hw0 hw1 half (lower e) (.term l.weight l.channel)) (CReal.ofQ' 0) := by
  have hu := CReal.leEv_trans (intrinsic_energy_bound w hw0 hw1 e N l) (CReal.leEv_of_equiv hz)
  have hl := CReal.leEv_ofQ'_of_approx_ge (energyLimit_nonnegative w hw0 hw1 half (lower e)
    (.term l.weight l.channel) (Q'.le_of_lt (interface_leaf_positive w hw0 N half l)))
  intro epsilon he
  obtain ⟨M, hM⟩ := hu epsilon he
  obtain ⟨L, hL⟩ := hl epsilon he
  exact ⟨max M L, fun n hn => ⟨hM n (Nat.le_trans (Nat.le_max_left _ _) hn),
    hL n (Nat.le_trans (Nat.le_max_right _ _) hn)⟩⟩

theorem intrinsic_coefficient_zero_of_original_null (N : Nat) (l : Leaf (actualTree N))
    (hz : CReal.Equiv originalLimit (CReal.ofQ' 0)) :
    CReal.Equiv (coefficientLimit w hw0 hw1 half (polyMul (lower e) l.channel)) (CReal.ofQ' 0) :=
  weighted_square_zero _ l.weight (interface_leaf_positive w hw0 N half l)
    (intrinsic_energy_zero_of_original_null w hw0 hw1 e N l hz)

theorem original_null_iff_channel_coefficients_zero :
    CReal.Equiv originalLimit (CReal.ofQ' 0) ↔
      ∀ N : Nat, ∀ l : Leaf (actualTree N),
        CReal.Equiv (coefficientLimit w hw0 hw1 half (polyMul (lower e) l.channel)) (CReal.ofQ' 0) :=
  ⟨fun hz N l => intrinsic_coefficient_zero_of_original_null w hw0 hw1 e N l hz,
    original_null_of_all_channel_coefficients_zero w hw0 hw1 e⟩

/-- Multiply back by the SAME original partition function, never cancel an
unspecified positive scalar or substitute an auxiliary law. -/
theorem original_null_of_form_null (hz : CReal.Equiv (form w hw0 hw1 e e) (CReal.ofQ' 0)) :
    CReal.Equiv originalLimit (CReal.ofQ' 0) :=
  (expectation_recover w hw0 hw1 half (reflectedInsertion e)).symm.trans
    ((Pivot2.mul_congr_left (B := fullActionLimit w hw0 hw1 half)
      ((expectation_reflection_eq_upper w e e hw0 hw1).trans hz)).trans
        (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_zero_mul
          ((fullActionLimit w hw0 hw1 half).approx n))))

theorem form_null_iff_channel_coefficients_zero :
    CReal.Equiv (form w hw0 hw1 e e) (CReal.ofQ' 0) ↔
      ∀ N : Nat, ∀ l : Leaf (actualTree N),
        CReal.Equiv (coefficientLimit w hw0 hw1 half (polyMul (lower e) l.channel)) (CReal.ofQ' 0) :=
  ⟨fun hz => (original_null_iff_channel_coefficients_zero w hw0 hw1 e).mp (original_null_of_form_null w hw0 hw1 e hz),
    form_null_of_all_channel_coefficients_zero w hw0 hw1 e⟩

theorem embedded_zero_iff_channel_coefficients_zero :
    embedExpression w hw0 hw1 e = completedZero w hw0 hw1 half ↔
      ∀ N : Nat, ∀ l : Leaf (actualTree N),
        CReal.Equiv (coefficientLimit w hw0 hw1 half (polyMul (lower e) l.channel)) (CReal.ofQ' 0) :=
  ⟨fun hz => (form_null_iff_channel_coefficients_zero w hw0 hw1 e).mp
    (Quotient.exact ((null_zero_iff w hw0 hw1 e).mp
      ((embedExpression_eq_iff w hw0 hw1 e (zeroExpression half)).mp hz))),
    embedded_zero_of_all_channel_coefficients_zero w hw0 hw1 e⟩

/-- Positive rational factor; importantly, the observable e is NOT a parameter. -/
def intrinsicNormFloor (N : Nat) (l : Leaf (actualTree N)) : Q' := l.weight * reciprocalFloor w hw0 half

theorem intrinsicNormFloor_positive (N : Nat) (l : Leaf (actualTree N)) :
    (0 : Q') < intrinsicNormFloor w hw0 N l :=
  Q'.mul_pos (interface_leaf_positive w hw0 N half l) (reciprocalFloor_pos w hw0 half)

theorem intrinsic_normalized_energy_bound (N : Nat) (l : Leaf (actualTree N)) :
    CReal.leEv
      (CReal.mul (CReal.ofQ' (intrinsicNormFloor w hw0 N l))
        (CReal.mul (coefficientLimit w hw0 hw1 half (polyMul (lower e) l.channel))
          (coefficientLimit w hw0 hw1 half (polyMul (lower e) l.channel))))
      (form w hw0 hw1 e e) := by
  let E := energyLimit w hw0 hw1 half (lower e) (.term l.weight l.channel)
  let lambda := actionReciprocal w hw0 hw1 half
  have hE := energyLimit_nonnegative w hw0 hw1 half (lower e) (.term l.weight l.channel)
    (Q'.le_of_lt (interface_leaf_positive w hw0 N half l))
  have hscaled := CReal.leEv_mul_nonneg_left (reciprocal_nonnegative w hw0 hw1 half)
    (intrinsic_energy_bound w hw0 hw1 e N l)
  have hfloor : CReal.leEv
      (CReal.mul (CReal.ofQ' (intrinsicNormFloor w hw0 N l))
        (CReal.mul (coefficientLimit w hw0 hw1 half (polyMul (lower e) l.channel))
          (coefficientLimit w hw0 hw1 half (polyMul (lower e) l.channel)))) (CReal.mul lambda E) := by
    intro epsilon he
    refine ⟨0, fun n _ => Q'.le_trans' _ _ _ ?_ (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he))⟩
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv l.weight (reciprocalFloor w hw0 half)))
        (Q'.mul_assoc_eqv _ _ _)))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (actionReciprocal_approx_ge w hw0 hw1 half n) (hE n))
  exact CReal.leEv_trans hfloor (CReal.leEv_trans hscaled
    (CReal.leEv_of_equiv ((CRealAlg.cmul_comm _ _).trans (expectation_reflection_eq_upper w e e hw0 hw1))))

end YMGap.Continuum.BF4ExactSlabIntrinsicChannelNormBound

#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelNormBound.intrinsic_energy_bound
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelNormBound.intrinsic_energy_zero_of_original_null
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelNormBound.intrinsic_coefficient_zero_of_original_null
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelNormBound.original_null_iff_channel_coefficients_zero
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelNormBound.original_null_of_form_null
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelNormBound.form_null_iff_channel_coefficients_zero
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelNormBound.embedded_zero_iff_channel_coefficients_zero
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelNormBound.intrinsicNormFloor
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelNormBound.intrinsicNormFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelNormBound.intrinsic_normalized_energy_bound
