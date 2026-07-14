/-
# Core-B second shifted residual: factored adverse-mass payment

The exact quotient at `(s,r) = (0,2)` has a common positive monomial:

  R_(0,2)/(w^2-h^2) = w^36 h^36 P_02(w,h),

where `P_02` has degree only 20.  Its six adverse monomials have total
coefficient mass `13500`.  Since every one is bounded by `w` and `4w <= 1`,
the whole adverse block is at most `3375`, below the constant reserve `3840`.
This compact payment avoids materializing the 231-entry elevated simplex table
while retaining the same factor-aware mechanism.
-/

import YMGap.Continuum.CoreBResidualOffsetTwoFactor

namespace YMGap.Continuum.CoreBResidualOffsetTwo

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.CoreBStructuralRecurrence
open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.CoreBResidualOffsetTwoFactor

local infix:50 " ≈ " => Q'.eqv

private theorem add_le_add' {a b c d : Q'} (h1 : a ≤ b) (h2 : c ≤ d) :
    a + c ≤ b + d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right a b c h1)
    (Q'.add_le_add_left b c d h2)

private theorem coeff_mul_add_eqv (a b x : Q') :
    a * x + b * x ≈ (a + b) * x := by
  have hcomm : a * x + b * x ≈ x * a + x * b :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.mul_comm_eqv a x))
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_comm_eqv b x))
  exact Q'.eqv_trans _ _ _ hcomm
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv x a b))
      (Q'.mul_comm_eqv x (a + b)))

private theorem coeffBlock {a b c x : Q'} (hc : a + b ≈ c) :
    a * x + b * x ≈ c * x :=
  Q'.eqv_trans _ _ _ (coeff_mul_add_eqv a b x)
    (Q'.mul_eqv_congr_right _ _ x hc)

private theorem rnqpow_eqv_qpow (x : Q') : ∀ n,
    RingNormaliser.qpow x n ≈ RGTransport.qpow x n
  | 0 => Q'.eqv_refl 1
  | n + 1 => Q'.mul_eqv_congr_right _ _ x (rnqpow_eqv_qpow x n)

private theorem rnqpow_nonneg {x : Q'} (hx : (0 : Q') ≤ x) (n : Nat) :
    (0 : Q') ≤ RingNormaliser.qpow x n :=
  Q'.le_trans' _ _ _ (RGTransport.qpow_nonneg x hx n)
    (Q'.ge_of_eqv (rnqpow_eqv_qpow x n))

private theorem rnqpow_le_one {x : Q'} (hx0 : (0 : Q') ≤ x)
    (hx1 : x ≤ (1 : Q')) (n : Nat) :
    RingNormaliser.qpow x n ≤ (1 : Q') :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (rnqpow_eqv_qpow x n))
    (HeatKernelGap.qpow_le_one hx0 hx1 n)

private theorem rnqpow_succ_le_self {x : Q'} (hx0 : (0 : Q') ≤ x)
    (hx1 : x ≤ (1 : Q')) (n : Nat) :
    RingNormaliser.qpow x (n + 1) ≤ x :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (rnqpow_eqv_qpow x (n + 1)))
    (HeatKernelGap.qpow_succ_le_self hx0 hx1 n)

private theorem rn_monomial_le_w {w h : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hh0 : (0 : Q') ≤ h) (hh1 : h ≤ (1 : Q'))
    (nw nh : Nat) :
    RingNormaliser.qpow w (nw + 1) * RingNormaliser.qpow h nh ≤ w := by
  have hwp0 := rnqpow_nonneg hw0 (nw + 1)
  have hprod : RingNormaliser.qpow w (nw + 1) *
      RingNormaliser.qpow h nh ≤ RingNormaliser.qpow w (nw + 1) := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left
        (RingNormaliser.qpow h nh) 1
        (RingNormaliser.qpow w (nw + 1))
        (rnqpow_le_one hh0 hh1 nh) hwp0)
      (Q'.le_of_eqv (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ hprod (rnqpow_succ_le_self hw0 hw1 nw)

/-- The positive-coefficient part of `P_02` is nonnegative. -/
theorem r02Tail_nonneg {w h : Q'} (hw0 : (0 : Q') ≤ w)
    (hh0 : (0 : Q') ≤ h) :
    (0 : Q') ≤ RingNormaliser.eval
      (fun i => if i = 0 then w else h) r02TailExpr := by
  apply eval_nonneg_of_coefficients
  · intro i
    by_cases hi : i = 0
    · simp [hi, hw0]
    · simp [hi, hh0]
  · decide

/-- All six adverse monomials are paid simultaneously by the physical cap.
The only feature used here is that every `w` exponent is positive. -/
theorem r02Adverse_paid {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q')) :
    RingNormaliser.eval (fun i => if i = 0 then w else h) r02AdverseExpr ≤
      (3840 : Q') := by
  have hw0 : (0 : Q') ≤ w := Q'.le_trans' _ _ _ hh0 hhw
  have hwle4w := Q'.mul_le_mul_of_nonneg_right 1 4 w
    (by decide : (1 : Q') ≤ 4) hw0
  have hw1 : w ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv w))) hwle4w)
      hwcap
  have hh1 : h ≤ (1 : Q') := Q'.le_trans' _ _ _ hhw hw1
  have h900 := Q'.mul_le_mul_of_nonneg_left _ _ (900 : Q')
    (rn_monomial_le_w hw0 hw1 hh0 hh1 9 10) (by decide)
  have h1000a := Q'.mul_le_mul_of_nonneg_left _ _ (1000 : Q')
    (rn_monomial_le_w hw0 hw1 hh0 hh1 9 6) (by decide)
  have h1000b := Q'.mul_le_mul_of_nonneg_left _ _ (1000 : Q')
    (rn_monomial_le_w hw0 hw1 hh0 hh1 7 8) (by decide)
  have h1000c := Q'.mul_le_mul_of_nonneg_left _ _ (1000 : Q')
    (rn_monomial_le_w hw0 hw1 hh0 hh1 5 10) (by decide)
  have h4800a := Q'.mul_le_mul_of_nonneg_left _ _ (4800 : Q')
    (rn_monomial_le_w hw0 hw1 hh0 hh1 3 2) (by decide)
  have h4800b := Q'.mul_le_mul_of_nonneg_left _ _ (4800 : Q')
    (rn_monomial_le_w hw0 hw1 hh0 hh1 1 4) (by decide)
  have hsum := add_le_add' h900
    (add_le_add' h1000a
      (add_le_add' h1000b
        (add_le_add' h1000c
          (add_le_add' h4800a
            (add_le_add' h4800b (Q'.le_refl' 0))))))
  have hmass : RingNormaliser.eval
      (fun i => if i = 0 then w else h) r02AdverseExpr ≤
      (13500 : Q') * w := by
    have hsum' : RingNormaliser.eval
        (fun i => if i = 0 then w else h) r02AdverseExpr ≤
        (900 : Q') * w +
          (1000 * w + (1000 * w +
            (1000 * w + (4800 * w + (4800 * w + 0))))) := by
      simpa [r02AdverseExpr, sumTerms, monoTerm, RingNormaliser.eval] using hsum
    have heq :
        (900 : Q') * w +
          (1000 * w + (1000 * w +
            (1000 * w + (4800 * w + (4800 * w + 0))))) ≈
          (13500 : Q') * w := by
      have h0 : (4800 : Q') * w + 0 ≈ 4800 * w := by
        rw [Q'.add_zero']
        exact Q'.eqv_refl _
      have h1 : (4800 : Q') * w + (4800 * w + 0) ≈ 9600 * w :=
        Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h0)
          (coeffBlock (by decide))
      have h2 : (1000 : Q') * w + (4800 * w + (4800 * w + 0)) ≈
          10600 * w :=
        Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h1)
          (coeffBlock (by decide))
      have h3 : (1000 : Q') * w +
          (1000 * w + (4800 * w + (4800 * w + 0))) ≈ 11600 * w :=
        Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h2)
          (coeffBlock (by decide))
      have h4 : (1000 : Q') * w +
          (1000 * w + (1000 * w + (4800 * w + (4800 * w + 0)))) ≈
          12600 * w :=
        Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h3)
          (coeffBlock (by decide))
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h4)
        (coeffBlock (by decide))
    exact Q'.le_trans' _ _ _ hsum' (Q'.le_of_eqv heq)
  have hscaled := Q'.mul_le_mul_of_nonneg_left ((4 : Q') * w) 1
    (3375 : Q') hwcap (by decide)
  have hcap : (13500 : Q') * w ≤ (3375 : Q') := by
    have heqscale : (13500 : Q') * w ≈ (3375 : Q') * (4 * w) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ w
          (by decide : (13500 : Q') ≈ (3375 : Q') * 4)) ?_
      exact Q'.mul_assoc_eqv 3375 4 w
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heqscale)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (Q'.mul_one_eqv 3375)))
  exact Q'.le_trans' _ _ _ hmass
    (Q'.le_trans' _ _ _ hcap (by decide))

/-- The reduced degree-20 factor is nonnegative.  This is the compact
adverse-mass counterpart of its (much larger) simplex degree elevation. -/
theorem r02Reduced_nonneg {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q')) :
    (0 : Q') ≤ RingNormaliser.eval
      (fun i => if i = 0 then w else h) r02ReducedExpr := by
  let rho : Nat → Q' := fun i => if i = 0 then w else h
  have hw0 : (0 : Q') ≤ w := Q'.le_trans' _ _ _ hh0 hhw
  have ht := r02Tail_nonneg hw0 hh0
  have ha := r02Adverse_paid hh0 hhw hwcap
  change (0 : Q') ≤
    ((3840 : Q') + RingNormaliser.eval rho r02TailExpr) +
      -RingNormaliser.eval rho r02AdverseExpr
  exact Q'.sub_nonneg_of_le
    (Q'.le_trans' _ _ _ ha
      (Q'.add_le_self_of_nonneg 3840
        (RingNormaliser.eval rho r02TailExpr) ht))

/-- The full square quotient is nonnegative, by the exact common-monomial
factorization and the reduced adverse-mass certificate. -/
theorem residualQuotient_zero_two_nonneg {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q')) :
    (0 : Q') ≤ RingNormaliser.eval
      (fun i => if i = 0 then w else h) (residualQuotientExpr 0 2) := by
  let rho : Nat → Q' := fun i => if i = 0 then w else h
  have hw0 : (0 : Q') ≤ w := Q'.le_trans' _ _ _ hh0 hhw
  have hcommon : (0 : Q') ≤ RingNormaliser.eval rho r02CommonExpr := by
    change (0 : Q') ≤
      RingNormaliser.qpow w 36 * RingNormaliser.qpow h 36
    exact Q'.mul_nonneg _ _ (rnqpow_nonneg hw0 36) (rnqpow_nonneg hh0 36)
  have hreduced : (0 : Q') ≤ RingNormaliser.eval rho r02ReducedExpr :=
    r02Reduced_nonneg hh0 hhw hwcap
  have hprod : (0 : Q') ≤
      RingNormaliser.eval rho (.mul r02CommonExpr r02ReducedExpr) :=
    Q'.mul_nonneg _ _ hcommon hreduced
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _ quotientNormal02 rho
  exact Q'.le_trans' _ _ _ hprod (Q'.ge_of_eqv hn)

/-- Exact square-Abel factorization at `(0,2)`, stated semantically. -/
theorem boundaryResidualAt_zero_two_factor (w h : Q') :
    boundaryResidualAt w h 0 2 ≈
      (RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2)) *
        RingNormaliser.eval (fun i => if i = 0 then w else h)
          (residualQuotientExpr 0 2) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _ factorNormal02
    (fun i => if i = 0 then w else h)
  exact Q'.eqv_trans _ _ _
    (boundaryResidualAt_eq_eval_residualExpr w h 0 2) hn

/-- **Second shifted residual positivity.**  `R_(0,2) >= 0` on the full
physical simplex.  This is a closed theorem at a new offset, obtained from a
factored reduced certificate rather than an assumed certificate family. -/
theorem boundaryResidualAt_zero_two_nonneg {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q')) :
    (0 : Q') ≤ boundaryResidualAt w h 0 2 := by
  have hsq : (0 : Q') ≤
      RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2) :=
    Q'.sub_nonneg_of_le
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (rnqpow_eqv_qpow h 2))
        (Q'.le_trans' _ _ _ (HeatKernelGap.qpow_mono hh0 hhw 2)
          (Q'.ge_of_eqv (rnqpow_eqv_qpow w 2))))
  have hp := Q'.mul_nonneg _ _ hsq
    (residualQuotient_zero_two_nonneg hh0 hhw hwcap)
  exact Q'.le_trans' _ _ _ hp
    (Q'.ge_of_eqv (boundaryResidualAt_zero_two_factor w h))

#print axioms residualQuotient_zero_two_nonneg
#print axioms r02Tail_nonneg
#print axioms r02Adverse_paid
#print axioms r02Reduced_nonneg
#print axioms boundaryResidualAt_zero_two_factor
#print axioms boundaryResidualAt_zero_two_nonneg

end YMGap.Continuum.CoreBResidualOffsetTwo
