/-
# Core-B row-one residual, cell `(s,r) = (1,0)`

First cell of the shifted row `s = 1` — the row whose cumulative payment
`C(0,r,2) = R(0,r+1) + R(1,r)` makes it the honest residual after the uniform
base-row theorem.  The simplex quotient for `(1,0)` has content `(wh)^22`,
nineteen quotient monomials, and exactly one negative coefficient
(`-6720·w^2h^2`), which the constant term `11232` pays directly on the
physical interval `4w <= 1` (with room: `6720·(hw)^2 <= 1680 <= 11232`).

Exact-rational scouting (2026-07-16) confirms the whole row is a proof
target, not a fence target: no negative value of `R(1,r)` exists on a
972-point simplex sweep for `r <= 8`, and the 42-family elementary-chain
decomposition admits an anchor payment (the pure-boundary `E*E` family,
`C = 81(r+1)(r+2)^2(r+3)` at `(wh)^{2r^2+8r+22}`) whose per-family discount
inequality holds with ~10^16 slack from `r = 4`.  This module banks the
first finite cell of that programme.
-/

import YMGap.Continuum.CoreBResidualSimplex
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.CoreBResidualRowOneCellZero

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.CoreBStructuralRecurrence
open YMGap.Continuum.CoreBResidualSimplex

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.add_zero, Int.zero_add]; ac_rfl))

private theorem rnqpow_eqv_qpow (x : Q') : ∀ n,
    RingNormaliser.qpow x n ≈ RGTransport.qpow x n
  | 0 => Q'.eqv_refl 1
  | n + 1 =>
      Q'.mul_eqv_congr_right _ _ x (rnqpow_eqv_qpow x n)

private theorem rnqpow_nonneg {x : Q'} (hx : (0 : Q') ≤ x) (n : Nat) :
    (0 : Q') ≤ RingNormaliser.qpow x n :=
  Q'.le_trans' _ _ _ (RGTransport.qpow_nonneg x hx n)
    (Q'.ge_of_eqv (rnqpow_eqv_qpow x n))

private theorem rnqpow_two (x : Q') :
    RingNormaliser.qpow x 2 ≈ x * x := by
  refine Q'.eqv_trans _ _ _ (rnqpow_eqv_qpow x 2) ?_
  unfold RGTransport.qpow
  exact Q'.mul_eqv_congr_right _ _ x (Q'.one_mul_eqv x)

/-- The seventeen positive non-constant monomials of the `(1,0)` quotient. -/
def r10Tail (w h : Q') : Q' :=
  (2592 : Q') * RingNormaliser.qpow h 2
    + (1584 : Q') * RingNormaliser.qpow h 6
    + (3780 : Q') * RingNormaliser.qpow h 8
    + (2592 : Q') * RingNormaliser.qpow w 2
    + (1584 : Q') *
        (RingNormaliser.qpow w 2 * RingNormaliser.qpow h 4)
    + (2916 : Q') *
        (RingNormaliser.qpow w 2 * RingNormaliser.qpow h 6)
    + (1584 : Q') *
        (RingNormaliser.qpow w 4 * RingNormaliser.qpow h 2)
    + (2916 : Q') *
        (RingNormaliser.qpow w 4 * RingNormaliser.qpow h 4)
    + (576 : Q') *
        (RingNormaliser.qpow w 4 * RingNormaliser.qpow h 6)
    + (2160 : Q') *
        (RingNormaliser.qpow w 4 * RingNormaliser.qpow h 8)
    + (1584 : Q') * RingNormaliser.qpow w 6
    + (2916 : Q') *
        (RingNormaliser.qpow w 6 * RingNormaliser.qpow h 2)
    + (576 : Q') *
        (RingNormaliser.qpow w 6 * RingNormaliser.qpow h 4)
    + (2160 : Q') *
        (RingNormaliser.qpow w 6 * RingNormaliser.qpow h 6)
    + (3780 : Q') * RingNormaliser.qpow w 8
    + (2160 : Q') *
        (RingNormaliser.qpow w 8 * RingNormaliser.qpow h 4)
    + (240 : Q') *
        (RingNormaliser.qpow w 8 * RingNormaliser.qpow h 8)

def r10P (w h : Q') : Q' :=
  ((11232 : Q') +
      -((6720 : Q') *
        (RingNormaliser.qpow w 2 * RingNormaliser.qpow h 2))) +
    r10Tail w h

def r10Quotient (w h : Q') : Q' :=
  (RingNormaliser.qpow w 22 * RingNormaliser.qpow h 22) * r10P w h

private def r10PExpr : RingNormaliser.PolyExpr :=
  let wp (n : Nat) := RingNormaliser.PolyExpr.pow (.var 0) n
  let hp (n : Nat) := RingNormaliser.PolyExpr.pow (.var 1) n
  let tail :=
    .add (.add (.add (.add (.add (.add (.add (.add
      (.add (.add (.add (.add (.add (.add (.add (.add
        (.mul (.const 2592) (hp 2))
        (.mul (.const 1584) (hp 6)))
        (.mul (.const 3780) (hp 8)))
        (.mul (.const 2592) (wp 2)))
        (.mul (.const 1584) (.mul (wp 2) (hp 4))))
        (.mul (.const 2916) (.mul (wp 2) (hp 6))))
        (.mul (.const 1584) (.mul (wp 4) (hp 2))))
        (.mul (.const 2916) (.mul (wp 4) (hp 4))))
      (.mul (.const 576) (.mul (wp 4) (hp 6))))
      (.mul (.const 2160) (.mul (wp 4) (hp 8))))
      (.mul (.const 1584) (wp 6)))
      (.mul (.const 2916) (.mul (wp 6) (hp 2))))
      (.mul (.const 576) (.mul (wp 6) (hp 4))))
      (.mul (.const 2160) (.mul (wp 6) (hp 6))))
      (.mul (.const 3780) (wp 8)))
      (.mul (.const 2160) (.mul (wp 8) (hp 4))))
      (.mul (.const 240) (.mul (wp 8) (hp 8)))
  .add
    (.add (.const 11232)
      (.neg (.mul (.const 6720) (.mul (wp 2) (hp 2)))))
    tail

private def r10QuotientExpr : RingNormaliser.PolyExpr :=
  .mul (.mul (.pow (.var 0) 22) (.pow (.var 1) 22)) r10PExpr

/-- Local copy of the square-difference factor wrapper (the Simplex module's
`squareFactorExpr` is private); only normal forms are compared, so the
syntactic copy is immaterial. -/
private def sqFactorExpr (q : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .mul (.add (.pow (.var 0) 2) (.neg (.pow (.var 1) 2))) q

theorem factorNormal10 :
    RingNormaliser.normalize (residualExpr 1 0) =
      RingNormaliser.normalize (sqFactorExpr (residualQuotientExpr 1 0)) := by
  decide

private theorem r10_quotient_normal :
    RingNormaliser.normalize (residualQuotientExpr 1 0) =
      RingNormaliser.normalize r10QuotientExpr := by
  decide

theorem boundaryResidualAt_one_zero_factor (w h : Q') :
    boundaryResidualAt w h 1 0 ≈
      (RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2)) *
        RingNormaliser.eval (fun i => if i = 0 then w else h)
          (residualQuotientExpr 1 0) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _ factorNormal10
    (fun i => if i = 0 then w else h)
  exact Q'.eqv_trans _ _ _
    (boundaryResidualAt_eq_eval_residualExpr w h 1 0) hn

theorem residualQuotient_one_zero_eq (w h : Q') :
    RingNormaliser.eval (fun i => if i = 0 then w else h)
        (residualQuotientExpr 1 0) ≈ r10Quotient w h := by
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _ r10_quotient_normal
    (fun i => if i = 0 then w else h)
  simpa [r10QuotientExpr, r10PExpr, r10Quotient, r10P, r10Tail,
    RingNormaliser.eval] using hn

theorem r10Tail_nonneg {w h : Q'} (hw0 : (0 : Q') ≤ w)
    (hh0 : (0 : Q') ≤ h) : (0 : Q') ≤ r10Tail w h := by
  have hw2 := rnqpow_nonneg hw0 2
  have hw4 := rnqpow_nonneg hw0 4
  have hw6 := rnqpow_nonneg hw0 6
  have hw8 := rnqpow_nonneg hw0 8
  have hh2 := rnqpow_nonneg hh0 2
  have hh4 := rnqpow_nonneg hh0 4
  have hh6 := rnqpow_nonneg hh0 6
  have hh8 := rnqpow_nonneg hh0 8
  unfold r10Tail
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.zero_le_add _ _
          (Q'.zero_le_add _ _
            (Q'.zero_le_add _ _
              (Q'.zero_le_add _ _
                (Q'.zero_le_add _ _
                  (Q'.zero_le_add _ _
                    (Q'.zero_le_add _ _
                      (Q'.zero_le_add _ _
                        (Q'.zero_le_add _ _
                          (Q'.zero_le_add _ _
                            (Q'.zero_le_add _ _
                              (Q'.zero_le_add _ _
                                (Q'.zero_le_add _ _
                                  (Q'.mul_nonneg _ _ (by decide) hh2)
                                  (Q'.mul_nonneg _ _ (by decide) hh6))
                                (Q'.mul_nonneg _ _ (by decide) hh8))
                              (Q'.mul_nonneg _ _ (by decide) hw2))
                            (Q'.mul_nonneg _ _ (by decide)
                              (Q'.mul_nonneg _ _ hw2 hh4)))
                          (Q'.mul_nonneg _ _ (by decide)
                            (Q'.mul_nonneg _ _ hw2 hh6)))
                        (Q'.mul_nonneg _ _ (by decide)
                          (Q'.mul_nonneg _ _ hw4 hh2)))
                      (Q'.mul_nonneg _ _ (by decide)
                        (Q'.mul_nonneg _ _ hw4 hh4)))
                    (Q'.mul_nonneg _ _ (by decide)
                      (Q'.mul_nonneg _ _ hw4 hh6)))
                  (Q'.mul_nonneg _ _ (by decide)
                    (Q'.mul_nonneg _ _ hw4 hh8)))
                (Q'.mul_nonneg _ _ (by decide) hw6))
              (Q'.mul_nonneg _ _ (by decide)
                (Q'.mul_nonneg _ _ hw6 hh2)))
            (Q'.mul_nonneg _ _ (by decide)
              (Q'.mul_nonneg _ _ hw6 hh4)))
          (Q'.mul_nonneg _ _ (by decide)
            (Q'.mul_nonneg _ _ hw6 hh6)))
        (Q'.mul_nonneg _ _ (by decide) hw8))
      (Q'.mul_nonneg _ _ (by decide)
        (Q'.mul_nonneg _ _ hw8 hh4)))
    (Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hw8 hh8))

private theorem negative_monomial_paid {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q')) :
    (6720 : Q') *
        (RingNormaliser.qpow w 2 * RingNormaliser.qpow h 2) ≤ (11232 : Q') := by
  have hw0 : (0 : Q') ≤ w := Q'.le_trans' _ _ _ hh0 hhw
  have h1le4 : (1 : Q') ≤ (4 : Q') := by decide
  have hwle4w := Q'.mul_le_mul_of_nonneg_right 1 4 w h1le4 hw0
  have hw1 : w ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv w))) hwle4w)
      hwcap
  have hh1 : h ≤ (1 : Q') := Q'.le_trans' _ _ _ hhw hw1
  let x := h * w
  have hx0 : (0 : Q') ≤ x := Q'.mul_nonneg _ _ hh0 hw0
  have hxw0 := Q'.mul_le_mul_of_nonneg_right h 1 w hh1 hw0
  have hxw : x ≤ w :=
    Q'.le_trans' _ _ _ hxw0 (Q'.le_of_eqv (Q'.one_mul_eqv w))
  have hx1 : x ≤ (1 : Q') := Q'.le_trans' _ _ _ hxw hw1
  have hxx0 := Q'.mul_le_mul_of_nonneg_left x 1 x hx1 hx0
  have hxx : x * x ≤ x :=
    Q'.le_trans' _ _ _ hxx0 (Q'.le_of_eqv (Q'.mul_one_eqv x))
  have h4xw := Q'.mul_le_mul_of_nonneg_left x w 4 hxw (by decide)
  have h4x1 : (4 : Q') * x ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ h4xw hwcap
  have hscaled := Q'.mul_le_mul_of_nonneg_left ((4 : Q') * x) 1 1680 h4x1
    (by decide)
  have h6720x1680 : (6720 : Q') * x ≤ (1680 : Q') := by
    have heq : (6720 : Q') * x ≈ (1680 : Q') * ((4 : Q') * x) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ x
          (by decide : (6720 : Q') ≈ (1680 : Q') * 4)) ?_
      exact Q'.mul_assoc_eqv 1680 4 x
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) ?_
    exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (Q'.mul_one_eqv 1680))
  have h6720xx := Q'.mul_le_mul_of_nonneg_left (x * x) x 6720 hxx
    (by decide)
  have hplain : (6720 : Q') * (x * x) ≤ (11232 : Q') :=
    Q'.le_trans' _ _ _ h6720xx
      (Q'.le_trans' _ _ _ h6720x1680 (by decide))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hplain
  change (6720 : Q') *
      (RingNormaliser.qpow w 2 * RingNormaliser.qpow h 2) ≈
        (6720 : Q') * (x * x)
  have hz : RingNormaliser.qpow w 2 * RingNormaliser.qpow h 2 ≈
      x * x := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (RingNormaliser.qpow h 2) (rnqpow_two w)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (w * w) _ _ (rnqpow_two h)) ?_
    unfold x
    ring_qeqv
  exact Q'.mul_eqv_congr_left 6720 _ _ hz

theorem r10P_nonneg {w h : Q'} (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q')) : (0 : Q') ≤ r10P w h := by
  have hw0 := Q'.le_trans' _ _ _ hh0 hhw
  unfold r10P
  exact Q'.zero_le_add _ _
    (Q'.sub_nonneg_of_le (negative_monomial_paid hh0 hhw hwcap))
    (r10Tail_nonneg hw0 hh0)

theorem r10Quotient_nonneg {w h : Q'} (hh0 : (0 : Q') ≤ h)
    (hhw : h ≤ w) (hwcap : (4 : Q') * w ≤ (1 : Q')) :
    (0 : Q') ≤ r10Quotient w h := by
  have hw0 := Q'.le_trans' _ _ _ hh0 hhw
  unfold r10Quotient
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (rnqpow_nonneg hw0 22) (rnqpow_nonneg hh0 22))
    (r10P_nonneg hh0 hhw hwcap)

/-- **The first row-one Core-B residual is nonnegative on the full physical
simplex.**  This is the `r = 0` cell of the shifted row `R(1,·)` whose
uniform payment (anchor mechanism, `r >= 4`) is the banked next target. -/
theorem boundaryResidualAt_one_zero_nonneg {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q')) :
    (0 : Q') ≤ boundaryResidualAt w h 1 0 := by
  have hsq : (0 : Q') ≤
      RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2) :=
    Q'.sub_nonneg_of_le
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (rnqpow_eqv_qpow h 2))
        (Q'.le_trans' _ _ _ (HeatKernelGap.qpow_mono hh0 hhw 2)
          (Q'.ge_of_eqv (rnqpow_eqv_qpow w 2))))
  have hq : (0 : Q') ≤ RingNormaliser.eval
      (fun i => if i = 0 then w else h) (residualQuotientExpr 1 0) :=
    Q'.le_trans' _ _ _ (r10Quotient_nonneg hh0 hhw hwcap)
      (Q'.ge_of_eqv (residualQuotient_one_zero_eq w h))
  have hp := Q'.mul_nonneg _ _ hsq hq
  exact Q'.le_trans' _ _ _ hp
    (Q'.ge_of_eqv (boundaryResidualAt_one_zero_factor w h))

#print axioms residualQuotient_one_zero_eq
#print axioms r10Tail_nonneg
#print axioms r10P_nonneg
#print axioms r10Quotient_nonneg
#print axioms boundaryResidualAt_one_zero_nonneg

end YMGap.Continuum.CoreBResidualRowOneCellZero
