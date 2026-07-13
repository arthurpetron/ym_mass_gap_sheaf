/-
# Core-B residual potential: terminal sign and diagonal propagation

`CoreBStructuralRecurrence` proves the exact diagonal telescope

  D_(s+n,r) ≃ D_(s,r+n) + cumulativeResidual(s,r,n).

This file supplies the unconditional terminal boundary condition: for
`0 ≤ h ≤ w`, every range-one potential `D_(0,r)` is nonnegative.  At range
one the autoconvolution has a single summand and

  A_r(w) / M_r(w) = const(r) * w^2,

because the Casimir has constant second difference two.  The proof below uses
the existing mixed-power comparison rather than division.

It then packages the precise remaining aggregate invariant: nonnegativity of
the cumulative diagonal residual.  Such a witness propagates the terminal
sign to every `D_(s,r)`.  A termwise residual witness is shown sufficient, but
is deliberately not postulated or fabricated.

The simplest coefficientwise route is fenced separately at `(s,r)=(0,0)`:
the exact antisymmetric normal form of the range increment contains coefficient
`-216` on `w^16 h^14`.  Therefore a proof must use weighted prefix / Abel
dominance among antisymmetric monomials, not coefficientwise nonnegativity.
-/

import YMGap.Continuum.CoreBStructuralRecurrence
import YMGap.Continuum.CrossRatioMonotone
import YMGap.Continuum.MeanExpConvexProgress
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.CoreBResidualPotential

set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.CrossRatioMonotone
open YMGap.Continuum.MeanExpConvexProgress
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.CoreBStructuralRecurrence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Range-one window and monomial forms -/

/-- A range-one window has only its `p=0` summand. -/
theorem modeWindow_zero_eq_coeffW (w : Q') (k : Nat) :
    modeWindow w 0 k ≈ coeffW w k := by
  unfold modeWindow acN
  simp only [Nat.zero_add, fsum_succ, fsum_zero, Nat.sub_zero]
  have h0 : (0 : Q') + coeffW w 0 * coeffW w k ≈
      coeffW w 0 * coeffW w k := q_zero_add_eqv _
  refine Q'.eqv_trans _ _ _ h0 ?_
  rw [coeffW_zero]
  exact Q'.one_mul_eqv _

private theorem coeff_pair_monomial (w : Q') (a b : Nat) :
    coeffW w a * coeffW w b ≈
      (dimQ a * dimQ b) * qpow w (c4 a + c4 b) := by
  unfold coeffW
  refine Q'.eqv_trans _ _ _
    (mul_swap4 (dimQ a) (qpow w (c4 a)) (dimQ b) (qpow w (c4 b))) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm (qpow_add w (c4 a) (c4 b)))

/-- Range-one numerator is one monomial. -/
theorem offsetA_zero_monomial (w : Q') (r : Nat) :
    offsetA w 0 r ≈
      (dimQ r * dimQ (r + 2)) * qpow w (c4 r + c4 (r + 2)) := by
  unfold offsetA
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (modeWindow_zero_eq_coeffW w r))
      (Q'.mul_eqv_congr_left _ _ _ (modeWindow_zero_eq_coeffW w (r + 2)))) ?_
  exact coeff_pair_monomial w r (r + 2)

/-- Range-one midpoint square is one monomial. -/
theorem offsetM_zero_monomial (w : Q') (r : Nat) :
    offsetM w 0 r ≈
      (dimQ (r + 1) * dimQ (r + 1)) * qpow w (2 * c4 (r + 1)) := by
  unfold offsetM
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (modeWindow_zero_eq_coeffW w (r + 1)))
      (Q'.mul_eqv_congr_left _ _ _ (modeWindow_zero_eq_coeffW w (r + 1)))) ?_
  refine Q'.eqv_trans _ _ _ (coeff_pair_monomial w (r + 1) (r + 1)) ?_
  rw [show c4 (r + 1) + c4 (r + 1) = 2 * c4 (r + 1) by omega]
  exact Q'.eqv_refl _

/-! ## 2. The unconditional terminal boundary condition -/

private def detMonoL : RingNormaliser.PolyExpr :=
  .add
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
    (.neg (.mul (.mul (.var 2) (.var 4)) (.mul (.var 0) (.var 5))))

private def detMonoR : RingNormaliser.PolyExpr :=
  .mul (.mul (.var 0) (.var 2))
    (.add (.mul (.var 1) (.var 3)) (.neg (.mul (.var 4) (.var 5))))

private theorem detMono_normal : RingNormaliser.normalize detMonoL =
    RingNormaliser.normalize detMonoR := by decide

private theorem det_monomial_factor (a m wp hp wq hq : Q') :
    (a * wp) * (m * hq) + -((m * wq) * (a * hp)) ≈
      (a * m) * (wp * hq + -(wq * hp)) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq detMonoL detMonoR detMono_normal
    (fun n => match n with
      | 0 => a | 1 => wp | 2 => m | 3 => hq | 4 => wq | _ => hp)
  simpa [RingNormaliser.eval, detMonoL, detMonoR] using hn

/-- **Terminal sign.**  For `0 ≤ h ≤ w`, the range-one determinant is
nonnegative at every offset.  Its two exponents differ by exactly two. -/
theorem offsetDelta_zero_nonneg {w h : Q'} (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (r : Nat) : (0 : Q') ≤ offsetDelta w h 0 r := by
  let p := c4 r + c4 (r + 2)
  let q := 2 * c4 (r + 1)
  let a := dimQ r * dimQ (r + 2)
  let m := dimQ (r + 1) * dimQ (r + 1)
  have hqp : q ≤ p := by
    dsimp [p, q]
    rw [casimir_secondDiff_eq_two]
    omega
  have hcross0 := qpow_cross_le hh0 hhw hqp
  have hcross : qpow w q * qpow h p ≤ qpow w p * qpow h q :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv (qpow w q) (qpow h p)))
      (Q'.le_trans' _ _ _ hcross0
        (Q'.le_of_eqv (Q'.mul_comm_eqv (qpow h q) (qpow w p))))
  have hdiff : (0 : Q') ≤ qpow w p * qpow h q + -(qpow w q * qpow h p) :=
    Q'.sub_nonneg_of_le hcross
  have ham : (0 : Q') ≤ a * m :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (dimQ_nonneg r) (dimQ_nonneg (r + 2)))
      (Q'.mul_nonneg _ _ (dimQ_nonneg (r + 1)) (dimQ_nonneg (r + 1)))
  have hprod : (0 : Q') ≤ (a * m) *
      (qpow w p * qpow h q + -(qpow w q * qpow h p)) :=
    Q'.mul_nonneg _ _ ham hdiff
  have hA_w := offsetA_zero_monomial w r
  have hA_h := offsetA_zero_monomial h r
  have hM_w := offsetM_zero_monomial w r
  have hM_h := offsetM_zero_monomial h r
  have hdelta : offsetDelta w h 0 r ≈
      (a * m) * (qpow w p * qpow h q + -(qpow w q * qpow h p)) := by
    unfold offsetDelta determinant
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hA_w)
          (Q'.mul_eqv_congr_left _ _ _ hM_h))
        (Q'.neg_eqv_congr _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hM_w)
            (Q'.mul_eqv_congr_left _ _ _ hA_h)))) ?_
    exact det_monomial_factor a m (qpow w p) (qpow h p) (qpow w q) (qpow h q)
  exact Q'.le_trans' _ _ _ hprod (Q'.ge_of_eqv hdelta)

/-! ## 3. The aggregate invariant and its propagation theorem -/

/-- The exact remaining aggregate target: every diagonal cumulative residual
is nonnegative.  This is weaker than asking each of the eleven component
minors, or even each one-step residual, to have a sign. -/
structure CumulativeResidualNonnegative (w h : Q') : Type where
  nonneg : ∀ s r n, (0 : Q') ≤ cumulativeResidual w h s r n

/-- A stronger one-step residual sign implies the cumulative invariant. -/
def cumulativeResidualNonnegativeOfTermwise {w h : Q'}
    (H : ∀ s r, (0 : Q') ≤ boundaryResidualAt w h s r) :
    CumulativeResidualNonnegative w h where
  nonneg := by
    intro s r n
    induction n generalizing r with
    | zero => exact Q'.le_refl' 0
    | succ n ih =>
        simp only [cumulativeResidual]
        exact Q'.zero_le_add _ _ (ih (r + 1)) (H (s + n) r)

/-- **All-range propagation from the cumulative invariant.**  The terminal
boundary sign and the diagonal telescope imply every offset determinant. -/
theorem offsetDelta_nonneg_of_cumulative {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (H : CumulativeResidualNonnegative w h) (s r : Nat) :
    (0 : Q') ≤ offsetDelta w h s r := by
  have hbase := offsetDelta_zero_nonneg hh0 hhw (r + s)
  have hcum := H.nonneg 0 r s
  have hsum : (0 : Q') ≤
      offsetDelta w h 0 (r + s) + cumulativeResidual w h 0 r s :=
    Q'.zero_le_add _ _ hbase hcum
  have htel := offsetDelta_diagonal_telescope w h 0 r s
  simpa only [Nat.zero_add] using
    Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv htel)

/-- Termwise residual nonnegativity is a sufficient, but intentionally
stronger, all-range criterion. -/
theorem offsetDelta_nonneg_of_termwise {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (H : ∀ s r, (0 : Q') ≤ boundaryResidualAt w h s r) (s r : Nat) :
    (0 : Q') ≤ offsetDelta w h s r :=
  offsetDelta_nonneg_of_cumulative hh0 hhw
    (cumulativeResidualNonnegativeOfTermwise H) s r

/-! ## 4. Coefficientwise range-increment fence -/

private def cE (v : Nat) (d : Int) (e : Nat) : RingNormaliser.PolyExpr :=
  .mul (.const d) (.pow (.var v) e)

private def fsum1E (a : RingNormaliser.PolyExpr) : RingNormaliser.PolyExpr :=
  .add (.const 0) a

private def fsum2E (a b : RingNormaliser.PolyExpr) : RingNormaliser.PolyExpr :=
  .add (fsum1E a) b

private def detE (Aw Ah Mw Mh : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .add (.mul Aw Mh) (.neg (.mul Mw Ah))

private def windowOneE (v k : Nat) : RingNormaliser.PolyExpr :=
  match k with
  | 0 => fsum2E (.mul (cE v 1 0) (cE v 2 3))
      (.mul (cE v 2 3) (cE v 1 0))
  | 1 => fsum2E (.mul (cE v 1 0) (cE v 3 8))
      (.mul (cE v 2 3) (cE v 2 3))
  | _ => fsum2E (.mul (cE v 1 0) (cE v 4 15))
      (.mul (cE v 2 3) (cE v 3 8))

private def windowZeroE (v k : Nat) : RingNormaliser.PolyExpr :=
  match k with
  | 0 => fsum1E (.mul (cE v 1 0) (cE v 2 3))
  | 1 => fsum1E (.mul (cE v 1 0) (cE v 3 8))
  | _ => fsum1E (.mul (cE v 1 0) (cE v 4 15))

/-- The recurrence-side syntax `D_(1,0)-D_(0,1)`, before normalization. -/
private def residual00SourceExpr : RingNormaliser.PolyExpr :=
  let A1v (v : Nat) := .mul (windowOneE v 0) (windowOneE v 2)
  let M1v (v : Nat) := .mul (windowOneE v 1) (windowOneE v 1)
  let A0v (v : Nat) := .mul (windowZeroE v 0) (windowZeroE v 2)
  let M0v (v : Nat) := .mul (windowZeroE v 1) (windowZeroE v 1)
  .add (detE (A1v 0) (A1v 1) (M1v 0) (M1v 1))
    (.neg (detE (A0v 0) (A0v 1) (M0v 0) (M0v 1)))

/-- Exact antisymmetric normal form of the first residual, in variables
`w = var 0`, `h = var 1`. -/
def residual00NormalExpr : RingNormaliser.PolyExpr :=
  let mono (ew eh : Nat) :=
    .mul (.pow (.var 0) ew) (.pow (.var 1) eh)
  let anti (c : Int) (ew eh : Nat) :=
    .mul (.const c) (.add (mono ew eh) (.neg (mono eh ew)))
  .add (.add (.add (.add
    (anti 384 14 12)
    (anti (-216) 16 14))
    (anti 256 18 12))
    (anti 384 18 14))
    (anti 72 18 16)

private theorem residual00_normal_eq :
    RingNormaliser.normalize residual00SourceExpr =
      RingNormaliser.normalize residual00NormalExpr := by
  set_option maxRecDepth 100000 in
    decide

/-- The displayed antisymmetric polynomial is genuinely the first recurrence
residual, not merely a disconnected scout computation. -/
theorem boundaryResidualAt_zero_zero_normal (w h : Q') :
    boundaryResidualAt w h 0 0 ≈
      RingNormaliser.eval (fun n => if n = 0 then w else h) residual00NormalExpr := by
  refine Q'.eqv_trans _ _ _
    (boundaryResidualAt_eq_potential_difference w h 0 0) ?_
  have hn := RingNormaliser.poly_identity_of_normal_eq residual00SourceExpr
    residual00NormalExpr residual00_normal_eq
    (fun n => if n = 0 then w else h)
  set_option maxRecDepth 100000 in
    simpa [RingNormaliser.eval, residual00SourceExpr, residual00NormalExpr,
      windowOneE, windowZeroE, detE, fsum1E, fsum2E, cE,
      offsetDelta, offsetA, offsetM, determinant, modeWindow, acN,
      coeffW, dimQ, c4, fsum_succ, fsum_zero,
      YMGap.Continuum.RGTransport.qpow, RingNormaliser.qpow] using hn

/-- The normal form contains the negative coefficient `-216` on
`w^16 h^14`.  This closed kernel check refutes coefficientwise
nonnegativity of the first range residual. -/
theorem residual00_has_negative_coefficient :
    ([16, 14], (-216 : Int)) ∈ RingNormaliser.normalize residual00NormalExpr := by
  decide

#print axioms modeWindow_zero_eq_coeffW
#print axioms offsetA_zero_monomial
#print axioms offsetM_zero_monomial
#print axioms offsetDelta_zero_nonneg
#print axioms cumulativeResidualNonnegativeOfTermwise
#print axioms offsetDelta_nonneg_of_cumulative
#print axioms offsetDelta_nonneg_of_termwise
#print axioms boundaryResidualAt_zero_zero_normal
#print axioms residual00_has_negative_coefficient

end YMGap.Continuum.CoreBResidualPotential
