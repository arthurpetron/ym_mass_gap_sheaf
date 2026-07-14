/-
# Finite Jacobi recurrence consumer for ordered Racah coefficients

This file adapts the pointwise Casimir equation used by the ordered Racah
development to the division-free forward recurrence consumed by constructive
finite uniqueness.  It also proves strict positivity of every actual forward
pivot from two adjacent proof-carrying right channels.
-/

import YMGap.Continuum.SU2OrderedRacahInteriorActualGramTranspose
import YMGap.Continuum.SU2RacahThreeTermUniqueness

namespace YMGap.Continuum.SU2OrderedRacahFiniteJacobiConsumer

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients
open YMGap.Continuum.SU2OrderedRacahInteriorActualGramTranspose
open YMGap.Continuum.SU2RacahThreeTermUniqueness

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; ac_rfl))

/-- The Jacobi/Casimir eigen-equation for an arbitrary coefficient sequence. -/
def JacobiSolutionAt (a b c d e : Nat) (x : Nat → Q') (p : Nat) : Prop :=
  leftExchangeEigenvalue a b e * x p ≈
    jacobiForward a b c d p * x (p + 1) +
      jacobiDiagonal a b c d p * x p +
      jacobiBackward a b c d p * x (p - 1)

def forwardA (a b c d : Nat) (p : Nat) : Q' :=
  jacobiForward a b c d p

def forwardB (a b c d e : Nat) (p : Nat) : Q' :=
  leftExchangeEigenvalue a b e + -jacobiDiagonal a b c d p

def forwardC (a b c d : Nat) (p : Nat) : Q' :=
  -jacobiBackward a b c d p

private theorem jacobi_to_forward_algebra
    (L X F Y D B Z : Q')
    (h : L * X ≈ F * Y + D * X + B * Z) :
    F * Y ≈ (L + -D) * X + (-B) * Z := by
  have hadd : L * X ≈ F * Y + (D * X + B * Z) :=
    Q'.eqv_trans _ _ _ h (Q'.add_assoc_eqv _ _ _)
  have hsolve : F * Y ≈ L * X + -(D * X + B * Z) := by
    refine Q'.eqv_trans _ (F * Y + 0) _
      (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _))) ?_
    refine Q'.eqv_trans _ (F * Y + ((D * X + B * Z) + -(D * X + B * Z))) _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_symm (Q'.add_neg_self_eqv _))) ?_
    refine Q'.eqv_trans _
      ((F * Y + (D * X + B * Z)) + -(D * X + B * Z)) _
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
    exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hadd)
  refine Q'.eqv_trans _ (L * X + -(D * X + B * Z)) _ hsolve ?_
  ring_qeqv

private theorem forward_to_jacobi_algebra
    (L X F Y D B Z : Q')
    (h : F * Y ≈ (L + -D) * X + (-B) * Z) :
    L * X ≈ F * Y + D * X + B * Z := by
  have hrearrange : (L + -D) * X + (-B) * Z ≈
      L * X + -(D * X + B * Z) := by
    ring_qeqv
  have hsub : F * Y ≈ L * X + -(D * X + B * Z) :=
    Q'.eqv_trans _ _ _ h hrearrange
  have hsolve : L * X ≈ F * Y + -(-(D * X + B * Z)) := by
    refine Q'.eqv_trans _ (L * X + 0) _
      (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _))) ?_
    refine Q'.eqv_trans _
      (L * X + (-(D * X + B * Z) + -(-(D * X + B * Z)))) _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_symm (Q'.add_neg_self_eqv _))) ?_
    refine Q'.eqv_trans _
      ((L * X + -(D * X + B * Z)) + -(-(D * X + B * Z))) _
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
    exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hsub)
  refine Q'.eqv_trans _ (F * Y + (D * X + B * Z)) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _ hsolve
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv _))
  exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

/-- The Casimir eigen-equation is exactly the forward recurrence step. -/
theorem jacobiSolutionAt_iff_forward_step
    (a b c d e : Nat) (x : Nat → Q') (p : Nat) :
    JacobiSolutionAt a b c d e x p ↔
      forwardA a b c d p * x (p + 1) ≈
        forwardB a b c d e p * x p +
          forwardC a b c d p * x (p - 1) := by
  constructor
  · intro h
    exact jacobi_to_forward_algebra _ _ _ _ _ _ _ h
  · intro h
    exact forward_to_jacobi_algebra _ _ _ _ _ _ _ h

/-- The explicit signed factorial candidate uses the same generic equation. -/
theorem candidateJacobiAt_iff_solutionAt
    (a b c d e p : Nat) :
    CandidateJacobiAt a b c d e p ↔
      JacobiSolutionAt a b c d e
        (signedCandidateByOrder a b c d e) p := by
  rfl

/-- A pointwise Jacobi solution through `0..N` is a solution of the exact
forward recurrence consumed by `forwardThreeTermThrough_unique`. -/
theorem jacobiSolutionThrough_to_forwardThreeTermThrough
    (N a b c d e : Nat) (x : Nat → Q')
    (hx : ∀ p, p ≤ N → JacobiSolutionAt a b c d e x p) :
    SatisfiesForwardThreeTermThrough N
      (forwardA a b c d) (forwardB a b c d e)
      (forwardC a b c d) x := by
  constructor
  · intro hN
    have h := (jacobiSolutionAt_iff_forward_step a b c d e x 0).1
      (hx 0 (by omega))
    have hC : forwardC a b c d 0 * x (0 - 1) ≈ 0 := by
      refine Q'.eqv_trans _ ((0 : Q') * x (0 - 1)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _ (by
          unfold forwardC jacobiBackward
          rw [dif_neg (by omega)]
          decide)
      · exact Q'.zero_mul_eqv _
    refine Q'.eqv_trans _
      (forwardB a b c d e 0 * x 0 + forwardC a b c d 0 * x (0 - 1)) _
      (by simpa only [Nat.zero_add] using h) ?_
    exact Q'.eqv_trans _ (forwardB a b c d e 0 * x 0 + 0) _
      (Q'.add_eqv_congr_left _ _ _ hC)
      (Q'.eqv_of_eq (Q'.add_zero' _))
  · intro n hn
    have h := (jacobiSolutionAt_iff_forward_step a b c d e x (n + 1)).1
      (hx (n + 1) (by omega))
    simpa only [Nat.add_assoc] using h

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

/-- Every actual physical adjacent edge has a strictly positive forward
pivot, exactly the hypothesis required by finite recurrence uniqueness. -/
theorem jacobiForward_pos_of_adjacent_channels {a b c d : Nat}
    (q0 q1 : FixedRightCGChannel a b c d)
    (hp : q1.p = q0.p + 1) :
    (0 : Q') < jacobiForward a b c d q0.p := by
  have hp1 := Nat.le_min.mp q1.p_le
  have hr0 := Nat.le_min.mp q0.r_le
  have hr1 := Nat.le_min.mp q1.r_le
  have hf : q1.intermediate = q0.intermediate - 2 := by
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
  have hr : q0.r = q1.r + 1 := by omega
  have hfr : 0 < q0.intermediate - q0.r := by
    have hq1r : q1.r ≤ q1.intermediate := hr1.2
    omega
  have hguard : rightOrderOK a b c d (q0.p + 1) = true := by
    rw [← hp]
    exact fixedRight_rightOrderOK q1
  unfold jacobiForward
  rw [dif_pos hguard]
  apply CReal.pos_of_num_pos
  rw [Q'.mkPos_num]
  unfold forwardNum
  rw [show rightLabel b c q0.p = q0.intermediate by rfl]
  have houter : outerOrder a b c d q0.p = q0.r := by
    unfold outerOrder
    rw [show rightLabel b c q0.p = q0.intermediate by rfl]
    exact fixedRight_outer_couplingOrder q0
  rw [houter]
  exact Int.ofNat_lt.mpr
    (Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos (Nat.succ_pos q0.p) (by omega)) (by omega)) hfr)

/-- **Finite constructive coefficient identification.**  Two concrete
Jacobi/Casimir coefficient sequences on the same physical channel window,
with the actual adjacent-channel pivot certificates and one common endpoint
value, agree at every physical index. -/
theorem finite_jacobi_coefficient_unique
    (N a b c d e : Nat)
    (channel : Nat → FixedRightCGChannel a b c d)
    (hchannelP : ∀ n, n ≤ N → (channel n).p = n)
    (x y : Nat → Q')
    (hx : ∀ p, p ≤ N → JacobiSolutionAt a b c d e x p)
    (hy : ∀ p, p ≤ N → JacobiSolutionAt a b c d e y p)
    (hzero : x 0 ≈ y 0) :
    ∀ n, n ≤ N → x n ≈ y n := by
  apply forwardThreeTermThrough_unique N
    (forwardA a b c d) (forwardB a b c d e)
    (forwardC a b c d) x y
  · intro n hn
    have hadj : (channel (n + 1)).p = (channel n).p + 1 := by
      rw [hchannelP (n + 1) (by omega), hchannelP n (by omega)]
    simpa only [forwardA, hchannelP n (by omega)] using
      jacobiForward_pos_of_adjacent_channels
        (channel n) (channel (n + 1)) hadj
  · exact jacobiSolutionThrough_to_forwardThreeTermThrough N a b c d e x hx
  · exact jacobiSolutionThrough_to_forwardThreeTermThrough N a b c d e y hy
  · exact hzero

end YMGap.Continuum.SU2OrderedRacahFiniteJacobiConsumer

#print axioms YMGap.Continuum.SU2OrderedRacahFiniteJacobiConsumer.jacobiSolutionAt_iff_forward_step
#print axioms YMGap.Continuum.SU2OrderedRacahFiniteJacobiConsumer.jacobiForward_pos_of_adjacent_channels
#print axioms YMGap.Continuum.SU2OrderedRacahFiniteJacobiConsumer.finite_jacobi_coefficient_unique
