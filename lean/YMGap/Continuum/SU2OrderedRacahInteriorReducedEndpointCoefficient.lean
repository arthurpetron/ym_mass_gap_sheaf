/-
# Interior raw-forward coefficient from a reduced endpoint

For adjacent physical right channels, remove their common `p` inner
contractions.  The remaining last-pair labels are `b-p,c-p`, whose total
degree is the current intermediate label `f`.  The raw coefficient from
order `p` to `p+1` is the endpoint coefficient on these reduced labels,
times the exact inner-row normalization ratio

`(b+c-p+1)/(f+1)`.

The theorem is stated without division and proves the normalization identity
directly in exact rationals.
-/

import YMGap.Continuum.SU2OrderedLeftCasimirPairing
import YMGap.Continuum.SU2OrderedRacahEndpointCasimirAllOrder
import YMGap.Continuum.SU2OrderedRacahInteriorActualGramTranspose
import YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients

namespace YMGap.Continuum.SU2OrderedRacahInteriorReducedEndpointCoefficient

open YMGap.Constructive
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahEndpointCasimirAllOrder
open YMGap.Continuum.SU2OrderedRacahInteriorActualGramTranspose
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; ac_rfl))

private theorem fixedRight_rightOrderOK {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    rightOrderOK a b c d q.p = true := by
  apply (rightOrderOK_spec a b c d q.p).2
  refine ⟨q.p_le, ?_⟩
  rw [show rightLabel b c q.p = q.intermediate by rfl]
  apply (fusionOK_iff_ladder a q.intermediate d).2
  have hr := Nat.le_min.mp q.r_le
  have hd : a + q.intermediate = d + 2 * q.r := by
    have h := q.degree_eq
    unfold FixedRightCGChannel.intermediate at h ⊢
    omega
  exact ⟨q.r, hr.1, hr.2, hd⟩

/-- **All-label reduced-endpoint coefficient identity.**  The raw forward
coefficient of the current order `p` is `jacobiBackward` in the neighboring
row `p+1`.  After removing the common inner contractions it is exactly the
proved endpoint coefficient, with the displayed normalization ratio. -/
theorem adjacent_raw_forward_eq_reduced_endpoint {a b c d : Nat}
    (q0 q1 : FixedRightCGChannel a b c d)
    (hp : q1.p = q0.p + 1) :
    Q'.ofNat (q0.intermediate + 1) *
        jacobiBackward a b c d q1.p ≈
      Q'.ofNat (b + c - q0.p + 1) *
        rawEndpointForward a (b - q0.p) (c - q0.p) q0.r := by
  have hp0 := Nat.le_min.mp q0.p_le
  have hp1 := Nat.le_min.mp q1.p_le
  have hr0 := Nat.le_min.mp q0.r_le
  have hr1 := Nat.le_min.mp q1.r_le
  have hf : q1.intermediate = q0.intermediate - 2 := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hd0 := q0.degree_eq
  have hd1 := q1.degree_eq
  have hr : q0.r = q1.r + 1 := by
    unfold FixedRightCGChannel.intermediate at hf hd0 hd1
    omega
  have hsum : (b - q0.p) + (c - q0.p) = q0.intermediate := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hsum0 : 0 < (b - q0.p) + (c - q0.p) := by omega
  have hprev : q1.p - 1 = q0.p := by omega
  have hguard : 0 < q1.p ∧
      rightOrderOK a b c d (q1.p - 1) = true := by
    rw [hprev]
    exact ⟨by omega, fixedRight_rightOrderOK q0⟩
  have hlabel : rightLabel b c q1.p = q0.intermediate - 2 := by
    rw [← hf]
    rfl
  have houter : outerOrder a b c d q1.p = q1.r := by
    unfold outerOrder
    rw [show rightLabel b c q1.p = q1.intermediate by rfl]
    exact fixedRight_outer_couplingOrder q1
  have hq0a : q0.r ≤ a := hr0.1
  have hq0f : q0.r ≤ q0.intermediate := hr0.2
  have hsumInt :
      (b : Int) - q0.p + ((c : Int) - q0.p) = q0.intermediate := by
    have h := congrArg Int.ofNat hsum
    simpa only [Int.ofNat_eq_natCast, Int.natCast_add,
      Int.ofNat_sub hp0.1,
      Int.ofNat_sub hp0.2] using h
  unfold rawEndpointForward
  rw [dif_pos hsum0]
  unfold jacobiBackward
  rw [dif_pos hguard]
  unfold backwardNum backwardDen
  dsimp only
  simp only [hlabel, houter, hsum]
  simp only [show q1.r + 1 = q0.r by omega,
    show a - q1.r = a - q0.r + 1 by omega,
    show a + (q0.intermediate - 2) - q1.r + 2 =
      a + q0.intermediate - q0.r + 1 by omega,
    show b + c - q1.p + 2 = b + c - q0.p + 1 by omega,
    show q0.intermediate - 2 + 2 = q0.intermediate by omega,
    show q0.intermediate - 2 + 3 = q0.intermediate + 1 by omega]
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  rw [Int.ofNat_sub hq0a,
    Int.ofNat_sub (by omega : q0.r ≤ a + q0.intermediate),
    Int.ofNat_sub hp0.1, Int.ofNat_sub hp0.2,
    Int.ofNat_sub (by omega : q0.p ≤ b + c)]
  rw [hsumInt]
  simp only [Int.natCast_add]
  ac_rfl

/-- The same reduced endpoint datum determines the reconstructed-section
forward coefficient after the exact physical Gram transpose.  This is the
all-label off-diagonal normalization package in a single division-free
identity. -/
theorem adjacent_section_forward_eq_reduced_endpoint_gram_weighted
    {a b c d : Nat}
    (q0 q1 : FixedRightCGChannel a b c d)
    (hp : q1.p = q0.p + 1) :
    Q'.ofNat (q0.intermediate + 1) *
        (triRightChannelWeight a b c d q0.intermediate *
          jacobiForward a b c d q0.p) ≈
      Q'.ofNat (b + c - q0.p + 1) *
        (triRightChannelWeight a b c d q1.intermediate *
          rawEndpointForward a (b - q0.p) (c - q0.p) q0.r) := by
  let C := Q'.ofNat (q0.intermediate + 1)
  let D := Q'.ofNat (b + c - q0.p + 1)
  let W0 := triRightChannelWeight a b c d q0.intermediate
  let W1 := triRightChannelWeight a b c d q1.intermediate
  let F := jacobiForward a b c d q0.p
  let B := jacobiBackward a b c d q1.p
  let E := rawEndpointForward a (b - q0.p) (c - q0.p) q0.r
  have hgram : W0 * F ≈ W1 * B := by
    simpa only [W0, W1, F, B] using
      adjacent_actual_right_channel_gram_ratio q0 q1 hp
  have hendpoint : C * B ≈ D * E := by
    simpa only [C, D, B, E] using
      adjacent_raw_forward_eq_reduced_endpoint q0 q1 hp
  refine Q'.eqv_trans _ (C * (W1 * B)) _
    (Q'.mul_eqv_congr_left C _ _ hgram) ?_
  refine Q'.eqv_trans _ (W1 * (C * B)) _ (by ring_qeqv) ?_
  refine Q'.eqv_trans _ (W1 * (D * E)) _
    (Q'.mul_eqv_congr_left W1 _ _ hendpoint) ?_
  simpa only [C, D, W0, W1, F, B, E] using
    (show W1 * (D * E) ≈ D * (W1 * E) by ring_qeqv)

end YMGap.Continuum.SU2OrderedRacahInteriorReducedEndpointCoefficient

#print axioms YMGap.Continuum.SU2OrderedRacahInteriorReducedEndpointCoefficient.adjacent_raw_forward_eq_reduced_endpoint
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorReducedEndpointCoefficient.adjacent_section_forward_eq_reduced_endpoint_gram_weighted
