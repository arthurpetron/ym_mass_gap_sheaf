/-
# Core-B first shifted residual

The simplex quotient for `(s,r) = (0,1)` has eighteen monomials and exactly
one negative coefficient.  On the physical interval `4w <= 1`, its constant
term pays that coefficient directly.  This gives a small exact proof of the
next-offset residual without asking the kernel to expand the full degree-56
three-variable Bernstein table.
-/

import YMGap.Continuum.CoreBResidualSimplex
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.CoreBResidualOffsetOne

set_option maxRecDepth 100000

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

/-- The positive tail after isolating the sole negative monomial. -/
def r01Tail (w h : Q') : Q' :=
  (864 : Q') * RingNormaliser.qpow h 2
    + (720 : Q') * RingNormaliser.qpow h 6
    + (540 : Q') * RingNormaliser.qpow h 8
    + (864 : Q') * RingNormaliser.qpow w 2
    + (720 : Q') *
        (RingNormaliser.qpow w 2 * RingNormaliser.qpow h 4)
    + (28 : Q') *
        (RingNormaliser.qpow w 2 * RingNormaliser.qpow h 6)
    + (720 : Q') *
        (RingNormaliser.qpow w 4 * RingNormaliser.qpow h 2)
    + (28 : Q') *
        (RingNormaliser.qpow w 4 * RingNormaliser.qpow h 4)
    + (576 : Q') *
        (RingNormaliser.qpow w 4 * RingNormaliser.qpow h 6)
    + (720 : Q') *
        (RingNormaliser.qpow w 4 * RingNormaliser.qpow h 8)
    + (720 : Q') * RingNormaliser.qpow w 6
    + (28 : Q') *
        (RingNormaliser.qpow w 6 * RingNormaliser.qpow h 2)
    + (576 : Q') *
        (RingNormaliser.qpow w 6 * RingNormaliser.qpow h 4)
    + (720 : Q') *
        (RingNormaliser.qpow w 6 * RingNormaliser.qpow h 6)
    + (540 : Q') * RingNormaliser.qpow w 8
    + (720 : Q') *
        (RingNormaliser.qpow w 8 * RingNormaliser.qpow h 4)

/-- The remaining polynomial after extracting `w^22 h^22`. -/
def r01P (w h : Q') : Q' :=
  ((1152 : Q') +
      -((1536 : Q') *
        (RingNormaliser.qpow w 2 * RingNormaliser.qpow h 2))) +
    r01Tail w h

def r01Quotient (w h : Q') : Q' :=
  (RingNormaliser.qpow w 22 * RingNormaliser.qpow h 22) * r01P w h

private def r01PExpr : RingNormaliser.PolyExpr :=
  let wp (n : Nat) := RingNormaliser.PolyExpr.pow (.var 0) n
  let hp (n : Nat) := RingNormaliser.PolyExpr.pow (.var 1) n
  let tail :=
    .add (.add (.add (.add (.add (.add (.add (.add
      (.add (.add (.add (.add (.add (.add (.add
        (.mul (.const 864) (hp 2))
        (.mul (.const 720) (hp 6)))
        (.mul (.const 540) (hp 8)))
        (.mul (.const 864) (wp 2)))
        (.mul (.const 720) (.mul (wp 2) (hp 4))))
        (.mul (.const 28) (.mul (wp 2) (hp 6))))
        (.mul (.const 720) (.mul (wp 4) (hp 2))))
        (.mul (.const 28) (.mul (wp 4) (hp 4))))
      (.mul (.const 576) (.mul (wp 4) (hp 6))))
      (.mul (.const 720) (.mul (wp 4) (hp 8))))
      (.mul (.const 720) (wp 6)))
      (.mul (.const 28) (.mul (wp 6) (hp 2))))
      (.mul (.const 576) (.mul (wp 6) (hp 4))))
      (.mul (.const 720) (.mul (wp 6) (hp 6))))
      (.mul (.const 540) (wp 8)))
      (.mul (.const 720) (.mul (wp 8) (hp 4)))
  .add
    (.add (.const 1152)
      (.neg (.mul (.const 1536) (.mul (wp 2) (hp 2)))))
    tail

private def r01QuotientExpr : RingNormaliser.PolyExpr :=
  .mul (.mul (.pow (.var 0) 22) (.pow (.var 1) 22)) r01PExpr

private theorem r01_quotient_normal :
    RingNormaliser.normalize (residualQuotientExpr 0 1) =
      RingNormaliser.normalize r01QuotientExpr := by
  decide

theorem residualQuotient_zero_one_eq (w h : Q') :
    RingNormaliser.eval (fun i => if i = 0 then w else h)
        (residualQuotientExpr 0 1) ≈ r01Quotient w h := by
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _ r01_quotient_normal
    (fun i => if i = 0 then w else h)
  simpa [r01QuotientExpr, r01PExpr, r01Quotient, r01P, r01Tail,
    RingNormaliser.eval] using hn

theorem r01Tail_nonneg {w h : Q'} (hw0 : (0 : Q') ≤ w)
    (hh0 : (0 : Q') ≤ h) : (0 : Q') ≤ r01Tail w h := by
  have hw2 := rnqpow_nonneg hw0 2
  have hw4 := rnqpow_nonneg hw0 4
  have hw6 := rnqpow_nonneg hw0 6
  have hw8 := rnqpow_nonneg hw0 8
  have hh2 := rnqpow_nonneg hh0 2
  have hh4 := rnqpow_nonneg hh0 4
  have hh6 := rnqpow_nonneg hh0 6
  have hh8 := rnqpow_nonneg hh0 8
  unfold r01Tail
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
    (Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hw8 hh4))

private theorem negative_monomial_paid {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q')) :
    (1536 : Q') *
        (RingNormaliser.qpow w 2 * RingNormaliser.qpow h 2) ≤ (1152 : Q') := by
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
  have hscaled := Q'.mul_le_mul_of_nonneg_left ((4 : Q') * x) 1 384 h4x1
    (by decide)
  have h1536x384 : (1536 : Q') * x ≤ (384 : Q') := by
    have heq : (1536 : Q') * x ≈ (384 : Q') * ((4 : Q') * x) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ x
          (by decide : (1536 : Q') ≈ (384 : Q') * 4)) ?_
      exact Q'.mul_assoc_eqv 384 4 x
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) ?_
    exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (Q'.mul_one_eqv 384))
  have h1536xx := Q'.mul_le_mul_of_nonneg_left (x * x) x 1536 hxx
    (by decide)
  have hplain : (1536 : Q') * (x * x) ≤ (1152 : Q') :=
    Q'.le_trans' _ _ _ h1536xx
      (Q'.le_trans' _ _ _ h1536x384 (by decide))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hplain
  change (1536 : Q') *
      (RingNormaliser.qpow w 2 * RingNormaliser.qpow h 2) ≈
        (1536 : Q') * (x * x)
  have hz : RingNormaliser.qpow w 2 * RingNormaliser.qpow h 2 ≈
      x * x := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (RingNormaliser.qpow h 2) (rnqpow_two w)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (w * w) _ _ (rnqpow_two h)) ?_
    unfold x
    ring_qeqv
  exact Q'.mul_eqv_congr_left 1536 _ _ hz

theorem r01P_nonneg {w h : Q'} (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q')) : (0 : Q') ≤ r01P w h := by
  have hw0 := Q'.le_trans' _ _ _ hh0 hhw
  unfold r01P
  exact Q'.zero_le_add _ _
    (Q'.sub_nonneg_of_le (negative_monomial_paid hh0 hhw hwcap))
    (r01Tail_nonneg hw0 hh0)

theorem r01Quotient_nonneg {w h : Q'} (hh0 : (0 : Q') ≤ h)
    (hhw : h ≤ w) (hwcap : (4 : Q') * w ≤ (1 : Q')) :
    (0 : Q') ≤ r01Quotient w h := by
  have hw0 := Q'.le_trans' _ _ _ hh0 hhw
  unfold r01Quotient
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (rnqpow_nonneg hw0 22) (rnqpow_nonneg hh0 22))
    (r01P_nonneg hh0 hhw hwcap)

/-- The first genuinely shifted Core-B residual is nonnegative on the full
physical simplex. -/
theorem boundaryResidualAt_zero_one_nonneg {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q')) :
    (0 : Q') ≤ boundaryResidualAt w h 0 1 := by
  have hsq : (0 : Q') ≤
      RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2) :=
    Q'.sub_nonneg_of_le
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (rnqpow_eqv_qpow h 2))
        (Q'.le_trans' _ _ _ (HeatKernelGap.qpow_mono hh0 hhw 2)
          (Q'.ge_of_eqv (rnqpow_eqv_qpow w 2))))
  have hq : (0 : Q') ≤ RingNormaliser.eval
      (fun i => if i = 0 then w else h) (residualQuotientExpr 0 1) :=
    Q'.le_trans' _ _ _ (r01Quotient_nonneg hh0 hhw hwcap)
      (Q'.ge_of_eqv (residualQuotient_zero_one_eq w h))
  have hp := Q'.mul_nonneg _ _ hsq hq
  exact Q'.le_trans' _ _ _ hp
    (Q'.ge_of_eqv (boundaryResidualAt_zero_one_factor w h))

#print axioms residualQuotient_zero_one_eq
#print axioms r01Tail_nonneg
#print axioms r01P_nonneg
#print axioms r01Quotient_nonneg
#print axioms boundaryResidualAt_zero_one_nonneg

end YMGap.Continuum.CoreBResidualOffsetOne
