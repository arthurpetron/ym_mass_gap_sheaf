/-
# Core-B row-one cell `(1,1)` — simplex positivity

Order proof for the second cell of the shifted row: the reduced `(1,1)`
quotient is nonnegative on the physical simplex because its thirteen adverse
monomials all carry `w^2 h^2`, hence are jointly bounded by `64188 (w*w)`,
and the physical cap gives `65536 (w*w) <= 4096 <= 11664`, the constant
reserve.  Combined with the exact factorizations of the companion factor
module this closes `R(1,1) >= 0` on the whole simplex.
-/

import YMGap.Continuum.CoreBResidualRowOneCellOneFactor
import YMGap.Continuum.CoreBResidualOffsetTwo

namespace YMGap.Continuum.CoreBResidualRowOneCellOne

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.CoreBStructuralRecurrence
open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.CoreBResidualOffsetTwoFactor (monoTerm sumTerms)
open YMGap.Continuum.CoreBResidualRowOneCellOneFactor

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

private theorem rnqpow_succ_le_self {x : Q'} (hx0 : (0 : Q') ≤ x)
    (hx1 : x ≤ (1 : Q')) (n : Nat) :
    RingNormaliser.qpow x (n + 1) ≤ x :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (rnqpow_eqv_qpow x (n + 1)))
    (HeatKernelGap.qpow_succ_le_self hx0 hx1 n)

/-- Any monomial with both exponents positive is at most `w * w` on the
ordered unit box `0 <= h <= w <= 1`. -/
private theorem rn_monomial_le_ww {w h : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hh0 : (0 : Q') ≤ h) (hh1 : h ≤ (1 : Q')) (hhw : h ≤ w)
    (nw nh : Nat) :
    RingNormaliser.qpow w (nw + 1) * RingNormaliser.qpow h (nh + 1) ≤
      w * w := by
  have hA : RingNormaliser.qpow w (nw + 1) ≤ w :=
    rnqpow_succ_le_self hw0 hw1 nw
  have hB : RingNormaliser.qpow h (nh + 1) ≤ h :=
    rnqpow_succ_le_self hh0 hh1 nh
  have hBw : RingNormaliser.qpow h (nh + 1) ≤ w :=
    Q'.le_trans' _ _ _ hB hhw
  have hB0 : (0 : Q') ≤ RingNormaliser.qpow h (nh + 1) :=
    rnqpow_nonneg hh0 (nh + 1)
  have h1 := Q'.mul_le_mul_of_nonneg_right
    (RingNormaliser.qpow w (nw + 1)) w
    (RingNormaliser.qpow h (nh + 1)) hA hB0
  have h2 := Q'.mul_le_mul_of_nonneg_left
    (RingNormaliser.qpow h (nh + 1)) w w hBw hw0
  exact Q'.le_trans' _ _ _ h1 h2

/-- All thirteen adverse monomials are paid simultaneously from the constant
reserve: they jointly total `64188 (w*w)`, and `65536 (w*w) <= 4096` on the
physical cap. -/
theorem r11Adverse_paid {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q')) :
    RingNormaliser.eval (fun i => if i = 0 then w else h) r11AdverseExpr ≤
      (11664 : Q') := by
  have hw0 : (0 : Q') ≤ w := Q'.le_trans' _ _ _ hh0 hhw
  have hwle4w := Q'.mul_le_mul_of_nonneg_right 1 4 w
    (by decide : (1 : Q') ≤ 4) hw0
  have hw1 : w ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv w))) hwle4w)
      hwcap
  have hh1 : h ≤ (1 : Q') := Q'.le_trans' _ _ _ hhw hw1
  have hww0 : (0 : Q') ≤ w * w := Q'.mul_nonneg _ _ hw0 hw0
  have m01 := Q'.mul_le_mul_of_nonneg_left _ _ (9720 : Q')
    (rn_monomial_le_ww hw0 hw1 hh0 hh1 hhw 1 5) (by decide)
  have m02 := Q'.mul_le_mul_of_nonneg_left _ _ (5760 : Q')
    (rn_monomial_le_ww hw0 hw1 hh0 hh1 hhw 1 7) (by decide)
  have m03 := Q'.mul_le_mul_of_nonneg_left _ _ (1656 : Q')
    (rn_monomial_le_ww hw0 hw1 hh0 hh1 hhw 1 13) (by decide)
  have m04 := Q'.mul_le_mul_of_nonneg_left _ _ (2808 : Q')
    (rn_monomial_le_ww hw0 hw1 hh0 hh1 hhw 3 3) (by decide)
  have m05 := Q'.mul_le_mul_of_nonneg_left _ _ (5760 : Q')
    (rn_monomial_le_ww hw0 hw1 hh0 hh1 hhw 3 5) (by decide)
  have m06 := Q'.mul_le_mul_of_nonneg_left _ _ (9720 : Q')
    (rn_monomial_le_ww hw0 hw1 hh0 hh1 hhw 5 1) (by decide)
  have m07 := Q'.mul_le_mul_of_nonneg_left _ _ (5760 : Q')
    (rn_monomial_le_ww hw0 hw1 hh0 hh1 hhw 5 3) (by decide)
  have m08 := Q'.mul_le_mul_of_nonneg_left _ _ (9288 : Q')
    (rn_monomial_le_ww hw0 hw1 hh0 hh1 hhw 5 5) (by decide)
  have m09 := Q'.mul_le_mul_of_nonneg_left _ _ (2700 : Q')
    (rn_monomial_le_ww hw0 hw1 hh0 hh1 hhw 5 13) (by decide)
  have m10 := Q'.mul_le_mul_of_nonneg_left _ _ (5760 : Q')
    (rn_monomial_le_ww hw0 hw1 hh0 hh1 hhw 7 1) (by decide)
  have m11 := Q'.mul_le_mul_of_nonneg_left _ _ (1656 : Q')
    (rn_monomial_le_ww hw0 hw1 hh0 hh1 hhw 13 1) (by decide)
  have m12 := Q'.mul_le_mul_of_nonneg_left _ _ (2700 : Q')
    (rn_monomial_le_ww hw0 hw1 hh0 hh1 hhw 13 5) (by decide)
  have m13 := Q'.mul_le_mul_of_nonneg_left _ _ (900 : Q')
    (rn_monomial_le_ww hw0 hw1 hh0 hh1 hhw 13 13) (by decide)
  have hsum := add_le_add' m01
    (add_le_add' m02
      (add_le_add' m03
        (add_le_add' m04
          (add_le_add' m05
            (add_le_add' m06
              (add_le_add' m07
                (add_le_add' m08
                  (add_le_add' m09
                    (add_le_add' m10
                      (add_le_add' m11
                        (add_le_add' m12
                          (add_le_add' m13 (Q'.le_refl' 0)))))))))))))
  have hmass : RingNormaliser.eval
      (fun i => if i = 0 then w else h) r11AdverseExpr ≤
      (64188 : Q') * (w * w) := by
    have hsum' : RingNormaliser.eval
        (fun i => if i = 0 then w else h) r11AdverseExpr ≤
        (9720 : Q') * (w * w) +
          (5760 * (w * w) + (1656 * (w * w) +
            (2808 * (w * w) + (5760 * (w * w) +
              (9720 * (w * w) + (5760 * (w * w) +
                (9288 * (w * w) + (2700 * (w * w) +
                  (5760 * (w * w) + (1656 * (w * w) +
                    (2700 * (w * w) +
                      (900 * (w * w) + 0)))))))))))) := by
      simpa [r11AdverseExpr, sumTerms, monoTerm, RingNormaliser.eval]
        using hsum
    have h00 : (900 : Q') * (w * w) + 0 ≈ 900 * (w * w) := by
      rw [Q'.add_zero']
      exact Q'.eqv_refl _
    have h01 : (2700 : Q') * (w * w) + (900 * (w * w) + 0) ≈
        3600 * (w * w) :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h00)
        (coeffBlock (by decide))
    have h02 : (1656 : Q') * (w * w) +
        (2700 * (w * w) + (900 * (w * w) + 0)) ≈ 5256 * (w * w) :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h01)
        (coeffBlock (by decide))
    have h03 : (5760 : Q') * (w * w) +
        (1656 * (w * w) + (2700 * (w * w) + (900 * (w * w) + 0))) ≈
        11016 * (w * w) :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h02)
        (coeffBlock (by decide))
    have h04 : (2700 : Q') * (w * w) +
        (5760 * (w * w) + (1656 * (w * w) +
          (2700 * (w * w) + (900 * (w * w) + 0)))) ≈
        13716 * (w * w) :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h03)
        (coeffBlock (by decide))
    have h05 : (9288 : Q') * (w * w) +
        (2700 * (w * w) + (5760 * (w * w) + (1656 * (w * w) +
          (2700 * (w * w) + (900 * (w * w) + 0))))) ≈
        23004 * (w * w) :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h04)
        (coeffBlock (by decide))
    have h06 : (5760 : Q') * (w * w) +
        (9288 * (w * w) + (2700 * (w * w) + (5760 * (w * w) +
          (1656 * (w * w) + (2700 * (w * w) + (900 * (w * w) + 0)))))) ≈
        28764 * (w * w) :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h05)
        (coeffBlock (by decide))
    have h07 : (9720 : Q') * (w * w) +
        (5760 * (w * w) + (9288 * (w * w) + (2700 * (w * w) +
          (5760 * (w * w) + (1656 * (w * w) +
            (2700 * (w * w) + (900 * (w * w) + 0))))))) ≈
        38484 * (w * w) :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h06)
        (coeffBlock (by decide))
    have h08 : (5760 : Q') * (w * w) +
        (9720 * (w * w) + (5760 * (w * w) + (9288 * (w * w) +
          (2700 * (w * w) + (5760 * (w * w) + (1656 * (w * w) +
            (2700 * (w * w) + (900 * (w * w) + 0)))))))) ≈
        44244 * (w * w) :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h07)
        (coeffBlock (by decide))
    have h09 : (2808 : Q') * (w * w) +
        (5760 * (w * w) + (9720 * (w * w) + (5760 * (w * w) +
          (9288 * (w * w) + (2700 * (w * w) + (5760 * (w * w) +
            (1656 * (w * w) +
              (2700 * (w * w) + (900 * (w * w) + 0))))))))) ≈
        47052 * (w * w) :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h08)
        (coeffBlock (by decide))
    have h10 : (1656 : Q') * (w * w) +
        (2808 * (w * w) + (5760 * (w * w) + (9720 * (w * w) +
          (5760 * (w * w) + (9288 * (w * w) + (2700 * (w * w) +
            (5760 * (w * w) + (1656 * (w * w) +
              (2700 * (w * w) + (900 * (w * w) + 0)))))))))) ≈
        48708 * (w * w) :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h09)
        (coeffBlock (by decide))
    have h11 : (5760 : Q') * (w * w) +
        (1656 * (w * w) + (2808 * (w * w) + (5760 * (w * w) +
          (9720 * (w * w) + (5760 * (w * w) + (9288 * (w * w) +
            (2700 * (w * w) + (5760 * (w * w) + (1656 * (w * w) +
              (2700 * (w * w) + (900 * (w * w) + 0))))))))))) ≈
        54468 * (w * w) :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h10)
        (coeffBlock (by decide))
    have h12 : (9720 : Q') * (w * w) +
        (5760 * (w * w) + (1656 * (w * w) + (2808 * (w * w) +
          (5760 * (w * w) + (9720 * (w * w) + (5760 * (w * w) +
            (9288 * (w * w) + (2700 * (w * w) + (5760 * (w * w) +
              (1656 * (w * w) +
                (2700 * (w * w) + (900 * (w * w) + 0)))))))))))) ≈
        64188 * (w * w) :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h11)
        (coeffBlock (by decide))
    exact Q'.le_trans' _ _ _ hsum' (Q'.le_of_eqv h12)
  have h4ww0 := Q'.mul_le_mul_of_nonneg_right ((4 : Q') * w) 1 w hwcap hw0
  have h4ww_le_w : (4 : Q') * (w * w) ≤ w := by
    have hassoc : (4 : Q') * (w * w) ≈ ((4 : Q') * w) * w :=
      Q'.eqv_symm (Q'.mul_assoc_eqv 4 w w)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc)
      (Q'.le_trans' _ _ _ h4ww0 (Q'.le_of_eqv (Q'.one_mul_eqv w)))
  have h16ww : (16 : Q') * (w * w) ≤ (1 : Q') := by
    have hsplit : (16 : Q') * (w * w) ≈ (4 : Q') * ((4 : Q') * (w * w)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (w * w)
          (by decide : (16 : Q') ≈ (4 : Q') * 4)) ?_
      exact Q'.mul_assoc_eqv 4 4 (w * w)
    have hstep := Q'.mul_le_mul_of_nonneg_left ((4 : Q') * (w * w)) w
      (4 : Q') h4ww_le_w (by decide)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
      (Q'.le_trans' _ _ _ hstep hwcap)
  have hscaled := Q'.mul_le_mul_of_nonneg_left ((16 : Q') * (w * w)) 1
    (4096 : Q') h16ww (by decide)
  have h65536 : (65536 : Q') * (w * w) ≤ (4096 : Q') := by
    have heq : (65536 : Q') * (w * w) ≈
        (4096 : Q') * ((16 : Q') * (w * w)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (w * w)
          (by decide : (65536 : Q') ≈ (4096 : Q') * 16)) ?_
      exact Q'.mul_assoc_eqv 4096 16 (w * w)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (Q'.mul_one_eqv 4096)))
  have hmono := Q'.mul_le_mul_of_nonneg_right (64188 : Q') 65536 (w * w)
    (by decide) hww0
  exact Q'.le_trans' _ _ _ hmass
    (Q'.le_trans' _ _ _ hmono
      (Q'.le_trans' _ _ _ h65536 (by decide)))

/-- The positive-coefficient part of the reduced `(1,1)` quotient is
nonnegative. -/
theorem r11Tail_nonneg {w h : Q'} (hw0 : (0 : Q') ≤ w)
    (hh0 : (0 : Q') ≤ h) :
    (0 : Q') ≤ RingNormaliser.eval
      (fun i => if i = 0 then w else h) r11TailExpr := by
  apply eval_nonneg_of_coefficients
  · intro i
    by_cases hi : i = 0
    · simp [hi, hw0]
    · simp [hi, hh0]
  · decide

/-- The reduced degree-28 factor is nonnegative on the physical simplex. -/
theorem r11Reduced_nonneg {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q')) :
    (0 : Q') ≤ RingNormaliser.eval
      (fun i => if i = 0 then w else h) r11ReducedExpr := by
  let rho : Nat → Q' := fun i => if i = 0 then w else h
  have hw0 : (0 : Q') ≤ w := Q'.le_trans' _ _ _ hh0 hhw
  have ht := r11Tail_nonneg hw0 hh0
  have ha := r11Adverse_paid hh0 hhw hwcap
  change (0 : Q') ≤
    ((11664 : Q') + RingNormaliser.eval rho r11TailExpr) +
      -RingNormaliser.eval rho r11AdverseExpr
  exact Q'.sub_nonneg_of_le
    (Q'.le_trans' _ _ _ ha
      (Q'.add_le_self_of_nonneg 11664
        (RingNormaliser.eval rho r11TailExpr) ht))

/-- The full square quotient at `(1,1)` is nonnegative. -/
theorem residualQuotient_one_one_nonneg {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q')) :
    (0 : Q') ≤ RingNormaliser.eval
      (fun i => if i = 0 then w else h) (residualQuotientExpr 1 1) := by
  let rho : Nat → Q' := fun i => if i = 0 then w else h
  have hw0 : (0 : Q') ≤ w := Q'.le_trans' _ _ _ hh0 hhw
  have hcommon : (0 : Q') ≤ RingNormaliser.eval rho r11CommonExpr := by
    change (0 : Q') ≤
      RingNormaliser.qpow w 32 * RingNormaliser.qpow h 32
    exact Q'.mul_nonneg _ _ (rnqpow_nonneg hw0 32) (rnqpow_nonneg hh0 32)
  have hreduced : (0 : Q') ≤ RingNormaliser.eval rho r11ReducedExpr :=
    r11Reduced_nonneg hh0 hhw hwcap
  have hprod : (0 : Q') ≤
      RingNormaliser.eval rho (.mul r11CommonExpr r11ReducedExpr) :=
    Q'.mul_nonneg _ _ hcommon hreduced
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _ quotientNormal11 rho
  exact Q'.le_trans' _ _ _ hprod (Q'.ge_of_eqv hn)

/-- Exact square-Abel factorization at `(1,1)`, stated semantically. -/
theorem boundaryResidualAt_one_one_factor (w h : Q') :
    boundaryResidualAt w h 1 1 ≈
      (RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2)) *
        RingNormaliser.eval (fun i => if i = 0 then w else h)
          (residualQuotientExpr 1 1) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _ factorNormal11
    (fun i => if i = 0 then w else h)
  exact Q'.eqv_trans _ _ _
    (boundaryResidualAt_eq_eval_residualExpr w h 1 1) hn

/-- **Second row-one residual positivity.**  `R(1,1) >= 0` on the full
physical simplex. -/
theorem boundaryResidualAt_one_one_nonneg {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q')) :
    (0 : Q') ≤ boundaryResidualAt w h 1 1 := by
  have hsq : (0 : Q') ≤
      RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2) :=
    Q'.sub_nonneg_of_le
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (rnqpow_eqv_qpow h 2))
        (Q'.le_trans' _ _ _ (HeatKernelGap.qpow_mono hh0 hhw 2)
          (Q'.ge_of_eqv (rnqpow_eqv_qpow w 2))))
  have hp := Q'.mul_nonneg _ _ hsq
    (residualQuotient_one_one_nonneg hh0 hhw hwcap)
  exact Q'.le_trans' _ _ _ hp
    (Q'.ge_of_eqv (boundaryResidualAt_one_one_factor w h))

#print axioms r11Adverse_paid
#print axioms r11Tail_nonneg
#print axioms r11Reduced_nonneg
#print axioms residualQuotient_one_one_nonneg
#print axioms boundaryResidualAt_one_one_factor
#print axioms boundaryResidualAt_one_one_nonneg

end YMGap.Continuum.CoreBResidualRowOneCellOne
