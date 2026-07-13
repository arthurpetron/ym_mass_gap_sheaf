/-
# Core-B residual Abel regrouping

The raw antisymmetric coefficient array of a boundary residual is not
coefficientwise nonnegative.  The useful regrouping first extracts the common
square difference `w^2-h^2`.  This file packages that corrected invariant and
proves its first genuine instance:

  R_(0,0)(w,h)
    ≃ 8 h^12 w^12 (w^2-h^2)
        (9h^4w^4 + 48h^4w^2 + 32h^4
         + 48h^2w^4 + 5h^2w^2 + 32w^4 + 48).

The quotient has only nonnegative coefficients, so `R_(0,0) ≥ 0` whenever
`0 ≤ h ≤ w`.  The `SquareAbelCertificate` interface records the all-range
version of exactly this factorization.  A certificate family implies termwise,
cumulative, and therefore all-offset determinant nonnegativity through the
previous diagonal telescope.

This is a base case and a sharpened reduction, not an all-`s,r` inhabitant.
-/

import YMGap.Continuum.CoreBResidualPotential
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.CoreBResidualAbel

set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.CoreBStructuralRecurrence
open YMGap.Continuum.CoreBResidualPotential

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Ring-normaliser powers: order helpers -/

private theorem rnqpow_eqv_qpow (x : Q') : ∀ n,
    RingNormaliser.qpow x n ≈ qpow x n
  | 0 => Q'.eqv_refl 1
  | n + 1 =>
      Q'.mul_eqv_congr_right _ _ x (rnqpow_eqv_qpow x n)

private theorem rnqpow_nonneg {x : Q'} (hx : (0 : Q') ≤ x) (n : Nat) :
    (0 : Q') ≤ RingNormaliser.qpow x n :=
  Q'.le_trans' _ _ _ (qpow_nonneg x hx n)
    (Q'.ge_of_eqv (rnqpow_eqv_qpow x n))

private theorem rnqpow_mono {h w : Q'} (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (n : Nat) : RingNormaliser.qpow h n ≤ RingNormaliser.qpow w n :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (rnqpow_eqv_qpow h n))
    (Q'.le_trans' _ _ _ (qpow_mono hh0 hhw n)
      (Q'.ge_of_eqv (rnqpow_eqv_qpow w n)))

/-! ## 2. Exact first quotient factorization -/

/-- The nonnegative quotient polynomial after removing the common monomial and
square difference from `R_(0,0)`. -/
def r00P (w h : Q') : Q' :=
  (9 : Q') * (RingNormaliser.qpow h 4 * RingNormaliser.qpow w 4)
    + (48 : Q') * (RingNormaliser.qpow h 4 * RingNormaliser.qpow w 2)
    + (32 : Q') * RingNormaliser.qpow h 4
    + (48 : Q') * (RingNormaliser.qpow h 2 * RingNormaliser.qpow w 4)
    + (5 : Q') * (RingNormaliser.qpow h 2 * RingNormaliser.qpow w 2)
    + (32 : Q') * RingNormaliser.qpow w 4 + (48 : Q')

/-- The full nonnegative factor apart from `w^2-h^2`. -/
def r00Quotient (w h : Q') : Q' :=
  (8 : Q') * (RingNormaliser.qpow h 12 * RingNormaliser.qpow w 12) * r00P w h

private def r00FactorExpr : RingNormaliser.PolyExpr :=
  let hp (n : Nat) := .pow (.var 1) n
  let wp (n : Nat) := .pow (.var 0) n
  let P :=
    .add (.add (.add (.add (.add (.add
      (.mul (.const 9) (.mul (hp 4) (wp 4)))
      (.mul (.const 48) (.mul (hp 4) (wp 2))))
      (.mul (.const 32) (hp 4)))
      (.mul (.const 48) (.mul (hp 2) (wp 4))))
      (.mul (.const 5) (.mul (hp 2) (wp 2))))
      (.mul (.const 32) (wp 4)))
      (.const 48)
  .mul
    (.mul (.const 8) (.mul (hp 12) (wp 12)))
    (.mul (.add (wp 2) (.neg (hp 2))) P)

private theorem r00_factor_normal :
    RingNormaliser.normalize residual00NormalExpr =
      RingNormaliser.normalize r00FactorExpr := by
  set_option maxRecDepth 100000 in
    decide

/-- **Exact Abel factorization of the first residual.** -/
theorem boundaryResidualAt_zero_zero_factor (w h : Q') :
    boundaryResidualAt w h 0 0 ≈
      (RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2)) * r00Quotient w h := by
  have hnorm := RingNormaliser.poly_identity_of_normal_eq residual00NormalExpr
    r00FactorExpr r00_factor_normal (fun n => if n = 0 then w else h)
  refine Q'.eqv_trans _ _ _ (boundaryResidualAt_zero_zero_normal w h) ?_
  refine Q'.eqv_trans _ _ _ hnorm ?_
  have hshape : RingNormaliser.eval (fun n => if n = 0 then w else h) r00FactorExpr =
      ((8 : Q') * (RingNormaliser.qpow h 12 * RingNormaliser.qpow w 12)) *
        ((RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2)) * r00P w h) := by
    rfl
  rw [hshape]
  unfold r00Quotient
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv
      ((8 : Q') * (RingNormaliser.qpow h 12 * RingNormaliser.qpow w 12))
      (RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2)) (r00P w h)))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (r00P w h)
        (Q'.mul_comm_eqv
          ((8 : Q') * (RingNormaliser.qpow h 12 * RingNormaliser.qpow w 12))
          (RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2))))
      (Q'.mul_assoc_eqv
          (RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2))
          ((8 : Q') * (RingNormaliser.qpow h 12 * RingNormaliser.qpow w 12))
          (r00P w h)))

theorem r00P_nonneg {w h : Q'} (hw0 : (0 : Q') ≤ w) (hh0 : (0 : Q') ≤ h) :
    (0 : Q') ≤ r00P w h := by
  have hw2 := rnqpow_nonneg hw0 2
  have hw4 := rnqpow_nonneg hw0 4
  have hh2 := rnqpow_nonneg hh0 2
  have hh4 := rnqpow_nonneg hh0 4
  unfold r00P
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.zero_le_add _ _
          (Q'.zero_le_add _ _
            (Q'.zero_le_add _ _
              (Q'.mul_nonneg _ _ (by decide)
                (Q'.mul_nonneg _ _ hh4 hw4))
              (Q'.mul_nonneg _ _ (by decide)
                (Q'.mul_nonneg _ _ hh4 hw2)))
            (Q'.mul_nonneg _ _ (by decide) hh4))
          (Q'.mul_nonneg _ _ (by decide)
            (Q'.mul_nonneg _ _ hh2 hw4)))
        (Q'.mul_nonneg _ _ (by decide)
          (Q'.mul_nonneg _ _ hh2 hw2)))
      (Q'.mul_nonneg _ _ (by decide) hw4))
    (by decide)

theorem r00Quotient_nonneg {w h : Q'} (hw0 : (0 : Q') ≤ w) (hh0 : (0 : Q') ≤ h) :
    (0 : Q') ≤ r00Quotient w h := by
  unfold r00Quotient
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (rnqpow_nonneg hh0 12) (rnqpow_nonneg hw0 12)))
    (r00P_nonneg hw0 hh0)

/-- The first one-step residual is nonnegative on the entire ordered quadrant;
no upper coupling bound is needed for this base instance. -/
theorem boundaryResidualAt_zero_zero_nonneg {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w) :
    (0 : Q') ≤ boundaryResidualAt w h 0 0 := by
  have hw0 := Q'.le_trans' _ _ _ hh0 hhw
  have hsq : (0 : Q') ≤
      RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2) :=
    Q'.sub_nonneg_of_le (rnqpow_mono hh0 hhw 2)
  have hprod := Q'.mul_nonneg _ _ hsq (r00Quotient_nonneg hw0 hh0)
  exact Q'.le_trans' _ _ _ hprod
    (Q'.ge_of_eqv (boundaryResidualAt_zero_zero_factor w h))

/-! ## 3. The corrected all-range aggregate invariant -/

/-- A square-difference quotient certificate for every one-step residual.
This is the two-variable Abel/Bernstein target suggested by the exact base
factorization. -/
structure SquareAbelCertificate (w h : Q') : Type where
  quotient : Nat → Nat → Q'
  quotient_nonneg : ∀ s r, (0 : Q') ≤ quotient s r
  factor : ∀ s r, boundaryResidualAt w h s r ≈
    (RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2)) * quotient s r

/-- A square-Abel certificate signs every one-step residual. -/
theorem boundaryResidualAt_nonneg_of_squareAbel {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (C : SquareAbelCertificate w h) (s r : Nat) :
    (0 : Q') ≤ boundaryResidualAt w h s r := by
  have hsq : (0 : Q') ≤
      RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2) :=
    Q'.sub_nonneg_of_le (rnqpow_mono hh0 hhw 2)
  have hp := Q'.mul_nonneg _ _ hsq (C.quotient_nonneg s r)
  exact Q'.le_trans' _ _ _ hp (Q'.ge_of_eqv (C.factor s r))

/-- A square-Abel family discharges the cumulative invariant and hence every
offset determinant through the diagonal telescope. -/
theorem offsetDelta_nonneg_of_squareAbel {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (C : SquareAbelCertificate w h) (s r : Nat) :
    (0 : Q') ≤ offsetDelta w h s r :=
  offsetDelta_nonneg_of_termwise hh0 hhw
    (fun s r => boundaryResidualAt_nonneg_of_squareAbel hh0 hhw C s r) s r

#print axioms boundaryResidualAt_zero_zero_factor
#print axioms r00P_nonneg
#print axioms r00Quotient_nonneg
#print axioms boundaryResidualAt_zero_zero_nonneg
#print axioms boundaryResidualAt_nonneg_of_squareAbel
#print axioms offsetDelta_nonneg_of_squareAbel

end YMGap.Continuum.CoreBResidualAbel
