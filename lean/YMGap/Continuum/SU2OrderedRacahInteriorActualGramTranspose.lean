/-
# All-label interior Gram transpose for the ordered Racah Jacobi operator

For two adjacent proof-carrying right channels, this file derives detailed
balance for the exact finite-box channel weights.  The proof first evaluates
the closed factorial binary-Gram ratio at an arbitrary interior edge, then
substitutes the independently derived nested-channel Gram factorization and
cancels the two positive intermediate dimensions.
-/

import YMGap.Continuum.SU2OrderedRacahEndpointActualGramTranspose

namespace YMGap.Continuum.SU2OrderedRacahInteriorActualGramTranspose

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantAdmissibleExtremal
open YMGap.Continuum.SU2TransvectantNormalizedRows
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRightNestedGramFactorization
open YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients
open YMGap.Continuum.SU2ClosedBinaryGramIdentification
open YMGap.Continuum.SU2SignedRacahSquareNormalization
open YMGap.Continuum.TreeGraphBoundProgress

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_congr {a b c d : Q'}
    (hab : a ≈ b) (hcd : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

private theorem ofNat_pos_of_pos (N : Nat) (hN : 0 < N) :
    (0 : Q') < Q'.ofNat N := by
  cases N with
  | zero => omega
  | succ N => exact Q'.ofNat_succ_pos N

private theorem adjacent_left_reassoc (A B W J : Q') :
    (B * A) * (W * J) ≈ B * ((A * W) * J) := by
  refine Q'.eqv_trans _ (B * (A * (W * J))) _ ?_ ?_
  · exact Q'.mul_assoc_eqv B A (W * J)
  · exact Q'.mul_eqv_congr_left B _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv A W J))

private theorem adjacent_right_reassoc (A B W J : Q') :
    A * ((B * W) * J) ≈ (B * A) * (W * J) := by
  refine Q'.eqv_trans _ (A * (B * (W * J))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left A _ _ (Q'.mul_assoc_eqv B W J)
  refine Q'.eqv_trans _ ((A * B) * (W * J)) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv A B (W * J))) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv A B)

private theorem fixedRight_rightOrderOK {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    rightOrderOK a b c d q.p = true := by
  apply (rightOrderOK_spec a b c d q.p).2
  refine ⟨q.p_le, ?_⟩
  rw [show rightLabel b c q.p = q.intermediate by rfl]
  apply (fusionOK_iff_ladder a q.intermediate d).2
  have hr := Nat.le_min.mp q.r_le
  have hdegree : a + q.intermediate = d + 2 * q.r := by
    have hd := q.degree_eq
    unfold FixedRightCGChannel.intermediate at hd
    unfold FixedRightCGChannel.intermediate
    omega
  exact ⟨q.r, hr.1, hr.2, hdegree⟩

private theorem fixedRight_outerOrder {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    outerOrder a b c d q.p = q.r := by
  unfold outerOrder
  rw [show rightLabel b c q.p = q.intermediate by rfl]
  exact fixedRight_outer_couplingOrder q

private theorem adjacent_intermediate {a b c d : Nat}
    (q0 q1 : FixedRightCGChannel a b c d) (hp : q1.p = q0.p + 1) :
    q1.intermediate = q0.intermediate - 2 := by
  have hp1 := Nat.le_min.mp q1.p_le
  unfold FixedRightCGChannel.intermediate
  omega

private theorem adjacent_outer_order {a b c d : Nat}
    (q0 q1 : FixedRightCGChannel a b c d) (hp : q1.p = q0.p + 1) :
    q0.r = q1.r + 1 := by
  have hf := adjacent_intermediate q0 q1 hp
  have hr0 := Nat.le_min.mp q0.r_le
  have hr1 := Nat.le_min.mp q1.r_le
  have hp1 := Nat.le_min.mp q1.p_le
  have hf2 : 2 ≤ q0.intermediate := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hd0 := q0.degree_eq
  have hd1 := q1.degree_eq
  have hd0' : a + q0.intermediate = d + 2 * q0.r := by
    unfold FixedRightCGChannel.intermediate at hd0 ⊢
    omega
  have hd1' : a + q1.intermediate = d + 2 * q1.r := by
    unfold FixedRightCGChannel.intermediate at hd1 ⊢
    omega
  omega

private theorem adjacent_forward_num {a b c d : Nat}
    (q0 : FixedRightCGChannel a b c d) :
    forwardNum a b c d q0.p =
      (q0.p + 1) * (b - q0.p) * (c - q0.p) *
        (q0.intermediate - q0.r) := by
  unfold forwardNum
  rw [show rightLabel b c q0.p = q0.intermediate by rfl,
    fixedRight_outerOrder q0]

private theorem adjacent_forward_den {a b c d : Nat}
    (q0 : FixedRightCGChannel a b c d) :
    forwardDen b c q0.p =
      q0.intermediate * (q0.intermediate - 1) := by
  rfl

private theorem adjacent_backward_num {a b c d : Nat}
    (q0 q1 : FixedRightCGChannel a b c d) (hp : q1.p = q0.p + 1) :
    backwardNum a b c d q1.p =
      q0.r * (a - q0.r + 1) *
        (a + q0.intermediate - q0.r + 1) *
          (b + c - q0.p + 1) := by
  have hf := adjacent_intermediate q0 q1 hp
  have hr := adjacent_outer_order q0 q1 hp
  have hp1 := Nat.le_min.mp q1.p_le
  have hr0 := Nat.le_min.mp q0.r_le
  have hr1 := Nat.le_min.mp q1.r_le
  have hf2 : 2 ≤ q0.intermediate := by
    unfold FixedRightCGChannel.intermediate
    omega
  unfold backwardNum
  rw [show rightLabel b c q1.p = q1.intermediate by rfl,
    fixedRight_outerOrder q1]
  dsimp only
  rw [show q1.r + 1 = q0.r by omega,
    show a - q1.r = a - q0.r + 1 by omega,
    show a + q1.intermediate - q1.r + 2 =
      a + q0.intermediate - q0.r + 1 by omega,
    show b + c - q1.p + 2 = b + c - q0.p + 1 by omega]

private theorem adjacent_backward_den {a b c d : Nat}
    (q0 q1 : FixedRightCGChannel a b c d) (hp : q1.p = q0.p + 1) :
    backwardDen b c q1.p =
      q0.intermediate * (q0.intermediate + 1) := by
  have hf := adjacent_intermediate q0 q1 hp
  have hp1 := Nat.le_min.mp q1.p_le
  have hf2 : 2 ≤ q0.intermediate := by
    unfold FixedRightCGChannel.intermediate
    omega
  unfold backwardDen
  rw [show rightLabel b c q1.p = q1.intermediate by rfl, hf]
  dsimp only
  rw [show q0.intermediate - 2 + 2 = q0.intermediate by omega,
    show q0.intermediate - 2 + 3 = q0.intermediate + 1 by omega]

/-- Closed factorial detailed balance on every adjacent physical right edge. -/
theorem adjacent_closed_binary_gram_ratio {a b c d : Nat}
    (q0 q1 : FixedRightCGChannel a b c d)
    (hp : q1.p = q0.p + 1) :
    Q'.ofNat (q1.intermediate + 1) *
        ((closedBinaryGram b c q0.intermediate *
            closedBinaryGram a q0.intermediate d) *
          jacobiForward a b c d q0.p) ≈
      Q'.ofNat (q0.intermediate + 1) *
        ((closedBinaryGram b c q1.intermediate *
            closedBinaryGram a q1.intermediate d) *
          jacobiBackward a b c d q1.p) := by
  have hp1 := Nat.le_min.mp q1.p_le
  have hr0 := Nat.le_min.mp q0.r_le
  have hr1 := Nat.le_min.mp q1.r_le
  have hf := adjacent_intermediate q0 q1 hp
  have hr := adjacent_outer_order q0 q1 hp
  have hf2 : 2 ≤ q0.intermediate := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hq0ok := fixedRight_rightOrderOK q0
  have hq1ok := fixedRight_rightOrderOK q1
  have hforwardGuard : rightOrderOK a b c d (q0.p + 1) = true := by
    simpa only [← hp] using hq1ok
  have hbackwardGuard :
      0 < q1.p ∧ rightOrderOK a b c d (q1.p - 1) = true := by
    constructor
    · omega
    · simpa only [show q1.p - 1 = q0.p by omega] using hq0ok
  have hkbc0 := fixedRight_inner_couplingOrder q0
  have hkaf0 := fixedRight_outer_couplingOrder q0
  have hkbc1 := fixedRight_inner_couplingOrder q1
  have hkaf1 := fixedRight_outer_couplingOrder q1
  have hFnum := adjacent_forward_num q0
  have hFden := adjacent_forward_den q0
  have hBnum := adjacent_backward_num q0 q1 hp
  have hBden := adjacent_backward_den q0 q1 hp
  have hfp : fact (q0.p + 1) = (q0.p + 1) * fact q0.p := by rfl
  have hb : fact (b - q0.p) =
      (b - q0.p) * fact (b - q0.p - 1) := by
    rw [show b - q0.p = (b - q0.p - 1) + 1 by omega]
    rfl
  have hc : fact (c - q0.p) =
      (c - q0.p) * fact (c - q0.p - 1) := by
    rw [show c - q0.p = (c - q0.p - 1) + 1 by omega]
    rfl
  have hsum : fact (b + c - q0.p + 1) =
      (b + c - q0.p + 1) * fact (b + c - q0.p) := by rfl
  have hrr : fact q0.r = q0.r * fact q1.r := by
    rw [hr]
    rfl
  have har : fact (a - q1.r) =
      (a - q0.r + 1) * fact (a - q0.r) := by
    rw [show a - q1.r = a - q0.r + 1 by omega,
      show a - q0.r + 1 = (a - q0.r) + 1 by omega]
    rfl
  have hfr : fact (q0.intermediate - q0.r) =
      (q0.intermediate - q0.r) *
        fact (q1.intermediate - q1.r) := by
    have hq1r : q1.r ≤ q1.intermediate :=
      (Nat.le_min.mp q1.r_le).2
    have hq0r : q0.r ≤ q0.intermediate - 1 := by
      calc
        q0.r = q1.r + 1 := hr
        _ ≤ q1.intermediate + 1 := Nat.add_le_add_right hq1r 1
        _ = q0.intermediate - 1 := by omega
    have hpos : 0 < q0.intermediate - q0.r := by omega
    have hindex : q1.intermediate - q1.r =
        q0.intermediate - q0.r - 1 := by omega
    rw [hindex,
      show q0.intermediate - q0.r =
        (q0.intermediate - q0.r - 1) + 1 by omega]
    rfl
  have hafr : fact (a + q0.intermediate - q0.r + 1) =
      (a + q0.intermediate - q0.r + 1) *
        fact (a + q1.intermediate - q1.r + 1) := by
    have hq1a : q1.r ≤ a := (Nat.le_min.mp q1.r_le).1
    have hq0a : q0.r ≤ a := (Nat.le_min.mp q0.r_le).1
    have hindex : a + q1.intermediate - q1.r + 1 =
        a + q0.intermediate - q0.r := by
      rw [hf, hr]
      omega
    rw [hindex]
    rfl
  unfold closedBinaryGram closedBinaryGramNum closedBinaryGramDen
  simp only [hkbc0, hkaf0, hkbc1, hkaf1]
  unfold jacobiForward jacobiBackward
  rw [dif_pos hforwardGuard, dif_pos hbackwardGuard]
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den]
  rw [hFnum, hFden, hBnum, hBden]
  rw [hb, hc, hsum, hrr, har, hfr, hafr]
  rw [hp, hfp, hf]
  rw [show b - (q0.p + 1) = b - q0.p - 1 by omega,
    show c - (q0.p + 1) = c - q0.p - 1 by omega,
    show b + c - (q0.p + 1) + 1 = b + c - q0.p by omega,
    show q0.intermediate - 2 + 1 = q0.intermediate - 1 by omega]
  push_cast
  ac_rfl

/-! ## Actual finite-box channel weights -/

private theorem adjacent_binary_product_closed {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) :
    binaryTransvectantGram b c q.p *
        binaryTransvectantGram a q.intermediate q.r ≈
      closedBinaryGram b c q.intermediate *
        closedBinaryGram a q.intermediate d := by
  have hp := Nat.le_min.mp q.p_le
  have hr := Nat.le_min.mp q.r_le
  apply mul_eqv_congr
  · simpa only [FixedRightCGChannel.intermediate] using
      binaryTransvectantGram_eq_closedBinaryGram b c q.p hp.1 hp.2
  · have h := binaryTransvectantGram_eq_closedBinaryGram
      a q.intermediate q.r hr.1 hr.2
    have hdegree : a + q.intermediate - 2 * q.r = d := q.degree_eq
    rw [hdegree] at h
    exact h

/-- **Concrete all-label adjacent detailed balance.**  The tridiagonal
left-pair exchange is self-adjoint in the literal right-channel Gram metric,
on every adjacent physical edge. -/
theorem adjacent_actual_right_channel_gram_ratio {a b c d : Nat}
    (q0 q1 : FixedRightCGChannel a b c d)
    (hp : q1.p = q0.p + 1) :
    triRightChannelWeight a b c d q0.intermediate *
        jacobiForward a b c d q0.p ≈
      triRightChannelWeight a b c d q1.intermediate *
        jacobiBackward a b c d q1.p := by
  let W0 := triRightChannelWeight a b c d q0.intermediate
  let W1 := triRightChannelWeight a b c d q1.intermediate
  let F := jacobiForward a b c d q0.p
  let Bk := jacobiBackward a b c d q1.p
  let A := Q'.ofNat (q0.intermediate + 1)
  let B := Q'.ofNat (q1.intermediate + 1)
  let G0 := closedBinaryGram b c q0.intermediate *
    closedBinaryGram a q0.intermediate d
  let G1 := closedBinaryGram b c q1.intermediate *
    closedBinaryGram a q1.intermediate d
  have hn0 := triRightChannelWeight_nested_binary_gram q0
  have hn1 := triRightChannelWeight_nested_binary_gram q1
  have hc0 := adjacent_binary_product_closed q0
  have hc1 := adjacent_binary_product_closed q1
  have h0 : A * W0 ≈ G0 := by
    exact Q'.eqv_trans _ _ _ hn0 hc0
  have h1 : B * W1 ≈ G1 := by
    exact Q'.eqv_trans _ _ _ hn1 hc1
  have hclosed : B * (G0 * F) ≈ A * (G1 * Bk) := by
    simpa only [A, B, G0, G1, F, Bk] using
      adjacent_closed_binary_gram_ratio q0 q1 hp
  have hscaled : (B * A) * (W0 * F) ≈ (B * A) * (W1 * Bk) := by
    refine Q'.eqv_trans _ (B * ((A * W0) * F)) _
      (adjacent_left_reassoc A B W0 F) ?_
    refine Q'.eqv_trans _ (B * (G0 * F)) _
      (Q'.mul_eqv_congr_left B _ _
        (Q'.mul_eqv_congr_right _ _ F h0)) ?_
    refine Q'.eqv_trans _ (A * (G1 * Bk)) _ hclosed ?_
    refine Q'.eqv_trans _ (A * ((B * W1) * Bk)) _
      (Q'.mul_eqv_congr_left A _ _
        (Q'.mul_eqv_congr_right _ _ Bk (Q'.eqv_symm h1))) ?_
    exact adjacent_right_reassoc A B W1 Bk
  have hA : (0 : Q') < A := Q'.ofNat_succ_pos q0.intermediate
  have hB : (0 : Q') < B := Q'.ofNat_succ_pos q1.intermediate
  exact Q'.mul_left_cancel_of_pos (Q'.mul_pos hB hA) hscaled

end YMGap.Continuum.SU2OrderedRacahInteriorActualGramTranspose

#print axioms YMGap.Continuum.SU2OrderedRacahInteriorActualGramTranspose.adjacent_closed_binary_gram_ratio
#print axioms YMGap.Continuum.SU2OrderedRacahInteriorActualGramTranspose.adjacent_actual_right_channel_gram_ratio
