/-
Track B / R2 — REDUCING the cubic heat-kernel gap margin `1 − w³` to the LINEAR
margin `1 − w` via the exact geometric factorization, and reducing the open
residual accordingly.

# Why this module exists

The closed-form SU(2) heat-kernel per-spacing eigenvalue-gap margin is the CUBIC
quantity `heatKernelMargin w = 1 − w³` (the spin-`1` excited eigenvalue `w³`
below the vacuum `1`).  The open continuum content is a uniform lower bound on
`(1 − w(a)³)/a` along asymptotic freedom `w(a) = e^{−t(a)/4}`.  The cubic is
GENUINELY HARDER to analyze than the linear difference quotient `(1 − w(a))/a ≈
t(a)/4`.  This module proves the EXACT factorization

    1 − w³ = (1 − w) · (1 + w + w²)

and the two-sided comparison `1 ≤ 1 + w + w² ≤ 3` on `w ∈ [0,1]`, hence the
sandwich

    (1 − w)  ≤  1 − w³  ≤  3 · (1 − w)        (for 0 ≤ w ≤ 1),

and lifts it through `divPos` to the residual level:

    (1 − w)/a  ≤  (1 − w³)/a  ≤  3 · (1 − w)/a,

so a positive LINEAR floor `c₀ ≤ (1 − w_j)/a_j` is EQUIVALENT (up to the harmless
factor `3`) to the cubic floor `c ≤ (1 − w_j³)/a_j`.  The cubic open content thus
reduces to the strictly simpler one-variable LINEAR inequality.

# What is genuine — and what remains OPEN (honest)

The factorization, the `1 ≤ 1+w+w² ≤ 3` sandwich, the cubic↔linear `divPos`
comparison, and the overlap-regime implication `(∀j, c₀ ≤ (1−w_j)/a_j) →
(∀j, c₀ ≤ (1−w_j³)/a_j)` are all PROVED here (elementary, but a real
simplification of the residual).  What remains OPEN is the LINEAR one-variable
inequality `(1 − w(a))/a ≥ c₀ > 0` along the asymptotic-freedom relation
`w(a) = e^{−t(a)/4}` — the `w(a) ↔ a` (heat-kernel-time vs spacing) relation is
the remaining frontier.  NO inhabitant of that linear floor is provided.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` arithmetic: the reflective polynomial ring `QPoly` (for the exact
factorization identity), the reused `Q'` order/`divPos` lemmas, and a minimal
numerator-monotonicity lemma for `divPos`.  Every load-bearing declaration is
gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.
No `Classical.*`, no `native_decide` (only `decide` on the decidable `allZero`
coefficient check), no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.HeatKernelGap
import YMGap.Continuum.HeatKernelPersistence
import YMGap.Constructive.QPoly
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.HeatKernelLinearBound

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelPersistence
open YMGap.Continuum.RGTransport

/-! ## 0. The quadratic geometric cofactor `1 + w + w²` -/

/-- The geometric cofactor `quadFactor w = 1 + w + w²` of the factorization
`1 − w³ = (1 − w)(1 + w + w²)`.  Provided as an explicit `Q'` expression. -/
def quadFactor (w : Q') : Q' := (1 : Q') + w + w * w

/-! ## 1. The exact factorization `1 − w³ = (1 − w)(1 + w + w²)`

We discharge the polynomial identity through the reflective `Q'` polynomial ring
`QPoly`: both sides are evaluations of explicit coefficient lists at `w`, and
`psub`-of-the-two has all coefficients `≃ 0` (`decide`), so `poly_eqv` gives the
`eqv`.  Bridging `eval`-of-list back to the concrete arithmetic trees `1 − w³`
and `(1 − w)·(1 + w + w²)` is done with the `QPoly` eval homomorphisms. -/

/-- Coefficient list of `1 − w³`: `[1, 0, 0, −1]`. -/
private def cubicMarginPoly : Poly := [(1 : Q'), 0, 0, -1]

/-- Coefficient list of `1 − w`: `[1, −1]`. -/
private def linFactorPoly : Poly := [(1 : Q'), -1]

/-- Coefficient list of `1 + w + w²`: `[1, 1, 1]`. -/
private def quadFactorPoly : Poly := [(1 : Q'), 1, 1]

/-- `eval [1,0,0,-1] w ≃ 1 − w³`. -/
private theorem eval_cubicMarginPoly (w : Q') :
    (eval cubicMarginPoly w).eqv (heatKernelMargin w) := by
  -- eval [1,0,0,-1] w = 1 + w*(0 + w*(0 + w*(-1 + w*0)))
  show ((1 : Q') + w * (0 + w * (0 + w * ((-1) + w * 0)))).eqv
        ((1 : Q') - qpow w 3)
  -- unfold qpow w 3 = ((1 * w) * w) * w
  show ((1 : Q') + w * (0 + w * (0 + w * ((-1) + w * 0)))).eqv
        ((1 : Q') + -(((qpow w 0 * w) * w) * w))
  refine Q'.add_eqv_congr_left (1 : Q') _ _ ?_
  -- w*(0 + w*(0 + w*(-1 + w*0))) ≃ -(w*w*w)
  -- collapse the innermost w*0 ≃ 0, then -1 + 0 ≃ -1, etc.
  have e0 : (w * 0).eqv 0 := q_mul_zero w
  have e1 : ((-1 : Q') + w * 0).eqv (-1) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (-1) (w * 0) 0 e0) (q_add_zero_eqv (-1))
  have e2 : (w * ((-1 : Q') + w * 0)).eqv (w * (-1)) :=
    Q'.mul_eqv_congr_left w _ _ e1
  have e3 : (w * (-1 : Q')).eqv (-(w)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv w 1) (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv w))
  have e4 : (w * ((-1 : Q') + w * 0)).eqv (-(w)) := Q'.eqv_trans _ _ _ e2 e3
  have e5 : ((0 : Q') + w * ((-1 : Q') + w * 0)).eqv (-(w)) :=
    Q'.eqv_trans _ _ _ (q_zero_add_eqv _) e4
  have e6 : (w * ((0 : Q') + w * ((-1 : Q') + w * 0))).eqv (w * (-(w))) :=
    Q'.mul_eqv_congr_left w _ _ e5
  have e7 : (w * (-(w))).eqv (-(w * w)) := Q'.mul_neg_eqv w w
  have e8 : (w * ((0 : Q') + w * ((-1 : Q') + w * 0))).eqv (-(w * w)) :=
    Q'.eqv_trans _ _ _ e6 e7
  have e9 : ((0 : Q') + w * ((0 : Q') + w * ((-1 : Q') + w * 0))).eqv (-(w * w)) :=
    Q'.eqv_trans _ _ _ (q_zero_add_eqv _) e8
  have e10 : (w * ((0 : Q') + w * ((0 : Q') + w * ((-1 : Q') + w * 0)))).eqv
              (w * (-(w * w))) :=
    Q'.mul_eqv_congr_left w _ _ e9
  have e11 : (w * (-(w * w))).eqv (-(w * (w * w))) := Q'.mul_neg_eqv w (w * w)
  have e12 : (w * ((0 : Q') + w * ((0 : Q') + w * ((-1 : Q') + w * 0)))).eqv
              (-(w * (w * w))) :=
    Q'.eqv_trans _ _ _ e10 e11
  -- target RHS: -(((qpow w 0 * w) * w) * w) = -((1 * w * w) * w)
  -- show w*(w*w) ≃ ((1*w)*w)*w
  refine Q'.eqv_trans _ _ _ e12 ?_
  refine Q'.neg_eqv_congr _ _ ?_
  -- w*(w*w) ≃ ((1*w)*w)*w  (= qpow w 0 * w * w * w with qpow w 0 = 1)
  show (w * (w * w)).eqv ((((1 : Q') * w) * w) * w)
  -- ((1*w)*w)*w ≃ (w*w)*w ≃ w*(w*w)
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ w
      (Q'.mul_eqv_congr_right _ _ w (Q'.one_mul_eqv w))) ?_
  exact Q'.mul_assoc_eqv w w w

/-- `eval [1,-1] w ≃ 1 − w`. -/
private theorem eval_linFactorPoly (w : Q') :
    (eval linFactorPoly w).eqv ((1 : Q') - w) := by
  show ((1 : Q') + w * ((-1) + w * 0)).eqv ((1 : Q') + -w)
  refine Q'.add_eqv_congr_left (1 : Q') _ _ ?_
  have e0 : (w * 0).eqv 0 := q_mul_zero w
  have e1 : ((-1 : Q') + w * 0).eqv (-1) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (-1) (w * 0) 0 e0) (q_add_zero_eqv (-1))
  have e2 : (w * ((-1 : Q') + w * 0)).eqv (w * (-1)) := Q'.mul_eqv_congr_left w _ _ e1
  refine Q'.eqv_trans _ _ _ e2 ?_
  exact Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv w 1) (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv w))

/-- `eval [1,1,1] w ≃ 1 + w + w² = quadFactor w`. -/
private theorem eval_quadFactorPoly (w : Q') :
    (eval quadFactorPoly w).eqv (quadFactor w) := by
  show ((1 : Q') + w * ((1 : Q') + w * ((1 : Q') + w * 0))).eqv
        ((1 : Q') + w + w * w)
  -- collapse the tail, then re-associate: 1 + w*(1 + w*1) ≃ 1 + (w + w*w) ≃ (1+w)+w*w
  have e0 : (w * 0).eqv 0 := q_mul_zero w
  have e1 : ((1 : Q') + w * 0).eqv 1 :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 (w * 0) 0 e0) (q_add_zero_eqv 1)
  have e2 : (w * ((1 : Q') + w * 0)).eqv (w * 1) := Q'.mul_eqv_congr_left w _ _ e1
  have e3 : (w * (1 : Q')).eqv w := Q'.mul_one_eqv w
  have e4 : (w * ((1 : Q') + w * 0)).eqv w := Q'.eqv_trans _ _ _ e2 e3
  have e5 : ((1 : Q') + w * ((1 : Q') + w * 0)).eqv ((1 : Q') + w) :=
    Q'.add_eqv_congr_left 1 _ _ e4
  -- now w * ((1) + w*((1)+w*0)) ≃ w * (1 + w) ≃ w + w*w
  have e6 : (w * ((1 : Q') + w * ((1 : Q') + w * 0))).eqv (w * ((1 : Q') + w)) :=
    Q'.mul_eqv_congr_left w _ _ e5
  have e7 : (w * ((1 : Q') + w)).eqv (w * 1 + w * w) := Q'.mul_add_eqv w 1 w
  have e8 : (w * (1 : Q') + w * w).eqv (w + w * w) :=
    Q'.add_eqv_congr_right _ _ (w * w) (Q'.mul_one_eqv w)
  have e9 : (w * ((1 : Q') + w * ((1 : Q') + w * 0))).eqv (w + w * w) :=
    Q'.eqv_trans _ _ _ e6 (Q'.eqv_trans _ _ _ e7 e8)
  -- 1 + (w + w*w) ≃ (1 + w) + w*w
  have e10 : ((1 : Q') + w * ((1 : Q') + w * ((1 : Q') + w * 0))).eqv
              ((1 : Q') + (w + w * w)) := Q'.add_eqv_congr_left 1 _ _ e9
  refine Q'.eqv_trans _ _ _ e10 ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv 1 w (w * w))

/-- **The exact geometric factorization** (as a `Q'` `eqv`):
`1 − w³ = (1 − w)·(1 + w + w²)`. -/
theorem heatKernelMargin_factor (w : Q') :
    (heatKernelMargin w).eqv (((1 : Q') - w) * quadFactor w) := by
  -- 1 − w³ ≃ eval cubicMarginPoly ≃ eval (pmul lin quad) ≃ (eval lin)·(eval quad)
  --       ≃ (1 − w)·quadFactor
  have hpoly : (eval cubicMarginPoly w).eqv (eval (pmul linFactorPoly quadFactorPoly) w) :=
    poly_eqv cubicMarginPoly (pmul linFactorPoly quadFactorPoly) w (by decide)
  have hmul : (eval (pmul linFactorPoly quadFactorPoly) w).eqv
      (eval linFactorPoly w * eval quadFactorPoly w) :=
    eval_pmul linFactorPoly quadFactorPoly w
  have hfac : (eval linFactorPoly w * eval quadFactorPoly w).eqv
      (((1 : Q') - w) * quadFactor w) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (eval quadFactorPoly w) (eval_linFactorPoly w)) ?_
    exact Q'.mul_eqv_congr_left ((1 : Q') - w) _ _ (eval_quadFactorPoly w)
  -- chain, starting from heatKernelMargin = 1 − w³ ≃ eval cubicMarginPoly (symm)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (eval_cubicMarginPoly w)) ?_
  exact Q'.eqv_trans _ _ _ hpoly (Q'.eqv_trans _ _ _ hmul hfac)

/-! ## 2. Two-sided comparison `1 ≤ 1 + w + w² ≤ 3` on `[0,1]`

The cofactor `1 + w + w²` is between `1` (since `w + w² ≥ 0`) and `3` (since each
of `1, w, w²` is `≤ 1` for `w ∈ [0,1]`).  Multiplying the factorization by these
two bounds, and using `1 − w ≥ 0`, gives the linear↔cubic sandwich. -/

/-- `0 ≤ w → 1 ≤ 1 + w + w²` (the cofactor exceeds `1`: `w + w² ≥ 0`). -/
theorem one_le_quadFactor {w : Q'} (hw : (0 : Q') ≤ w) :
    (1 : Q') ≤ quadFactor w := by
  -- 1 ≤ 1 + w + w² ⇐ 0 ≤ w + w²; then 1 ≃ 1 + 0 ≤ 1 + (w + w²) ≃ quadFactor.
  have hww : (0 : Q') ≤ w * w := Q'.mul_nonneg w w hw hw
  have hsum : (0 : Q') ≤ w + w * w :=
    Q'.le_trans' _ _ _ hw (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (q_add_zero_eqv w)))
      (Q'.add_le_add_left w 0 (w * w) hww))
  -- 1 + 0 ≤ 1 + (w + w²)
  have hstep : (1 : Q') + 0 ≤ (1 : Q') + (w + w * w) :=
    Q'.add_le_add_left 1 0 (w + w * w) hsum
  have h1 : (1 : Q') ≤ (1 : Q') + (w + w * w) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' 1)))) hstep
  -- (1 + (w + w²)) ≃ ((1 + w) + w²) = quadFactor
  exact Q'.le_trans' _ _ _ h1 (Q'.ge_of_eqv (Q'.add_assoc_eqv 1 w (w * w)))

/-- `0 ≤ w → w ≤ 1 → 1 + w + w² ≤ 3` (each summand is `≤ 1`). -/
theorem quadFactor_le_three {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    quadFactor w ≤ (3 : Q') := by
  -- w² = w*w ≤ 1*w ≃ w ≤ 1, so w² ≤ 1; then 1 + w + w² ≤ 1 + 1 + 1 = 3.
  have hww : w * w ≤ (1 : Q') * w :=
    Q'.mul_le_mul_of_nonneg_right w 1 w hw1 hw0
  have hww1 : w * w ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hww (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv w)) hw1)
  -- 1 + w ≤ 1 + 1
  have ha : (1 : Q') + w ≤ (1 : Q') + 1 := Q'.add_le_add_left 1 w 1 hw1
  -- (1 + w) + w² ≤ (1 + 1) + 1
  have hb : ((1 : Q') + w) + w * w ≤ ((1 : Q') + 1) + 1 :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (w * w) ha)
      (Q'.add_le_add_left ((1 : Q') + 1) (w * w) 1 hww1)
  -- (1 + 1) + 1 ≃ 3 and quadFactor = (1 + w) + w²
  refine Q'.le_trans' _ _ _ hb ?_
  exact Q'.le_of_eqv (by decide)

/-! ## 3. The linear↔cubic margin sandwich on `[0,1]`

Multiplying `1 − w³ = (1 − w)·(1 + w + w²)` by `1 ≤ 1 + w + w²` (with `1 − w ≥ 0`)
gives the lower comparison; by `1 + w + w² ≤ 3` the upper one. -/

/-- `0 ≤ w → w ≤ 1 → 0 ≤ 1 − w` (the linear margin is nonnegative on `[0,1]`). -/
theorem one_sub_nonneg {w : Q'} (hw1 : w ≤ (1 : Q')) : (0 : Q') ≤ (1 : Q') - w :=
  Q'.sub_nonneg_of_le hw1

/-- **Lower comparison:** `0 ≤ w → w ≤ 1 → (1 − w) ≤ 1 − w³`.
(`1 − w³ = (1 − w)(1 + w + w²) ≥ (1 − w)·1 = 1 − w`, using `1 − w ≥ 0`.) -/
theorem linear_le_cubicMargin {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    ((1 : Q') - w) ≤ heatKernelMargin w := by
  have hnn : (0 : Q') ≤ (1 : Q') - w := one_sub_nonneg hw1
  -- (1 − w) ≃ (1 − w)·1 ≤ (1 − w)·quadFactor ≃ 1 − w³
  have hq : (1 : Q') ≤ quadFactor w := one_le_quadFactor hw0
  have hstep : ((1 : Q') - w) * 1 ≤ ((1 : Q') - w) * quadFactor w :=
    Q'.mul_le_mul_of_nonneg_left 1 (quadFactor w) ((1 : Q') - w) hq hnn
  have hl : ((1 : Q') - w) ≤ ((1 : Q') - w) * quadFactor w :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv ((1 : Q') - w))) hstep
  exact Q'.le_trans' _ _ _ hl (Q'.ge_of_eqv (heatKernelMargin_factor w))

/-- **Upper comparison:** `0 ≤ w → w ≤ 1 → 1 − w³ ≤ 3 · (1 − w)`.
(`1 − w³ = (1 − w)(1 + w + w²) ≤ (1 − w)·3 = 3(1 − w)`, using `1 − w ≥ 0`.) -/
theorem cubicMargin_le_three_linear {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) :
    heatKernelMargin w ≤ (3 : Q') * ((1 : Q') - w) := by
  have hnn : (0 : Q') ≤ (1 : Q') - w := one_sub_nonneg hw1
  have hq : quadFactor w ≤ (3 : Q') := quadFactor_le_three hw0 hw1
  -- 1 − w³ ≃ (1 − w)·quadFactor ≤ (1 − w)·3 ≃ 3·(1 − w)
  have hstep : ((1 : Q') - w) * quadFactor w ≤ ((1 : Q') - w) * 3 :=
    Q'.mul_le_mul_of_nonneg_left (quadFactor w) 3 ((1 : Q') - w) hq hnn
  have hu : heatKernelMargin w ≤ ((1 : Q') - w) * 3 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (heatKernelMargin_factor w)) hstep
  exact Q'.le_trans' _ _ _ hu (Q'.le_of_eqv (Q'.mul_comm_eqv ((1 : Q') - w) 3))

/-! ## 4. Lifting the sandwich through `divPos` — the residual reduction

`divPos` is monotone in its numerator (multiply by the nonnegative reciprocal),
and `divPos (k·p) q ≃ k · divPos p q`.  So the margin sandwich lifts to the
per-spacing physical quotient, reducing the cubic floor to the linear one. -/

/-- **`divPos` numerator-monotonicity** (minimal, proved here):
`p₁ ≤ p₂ → divPos p₁ q ≤ divPos p₂ q`. -/
theorem divPos_le_divPos_of_le {p₁ p₂ q : Q'} (hq : (0 : Q') < q)
    (h : p₁ ≤ p₂) : Q'.divPos p₁ q hq ≤ Q'.divPos p₂ q hq := by
  show p₁ * Q'.recipPos q hq ≤ p₂ * Q'.recipPos q hq
  exact Q'.mul_le_mul_of_nonneg_right p₁ p₂ (Q'.recipPos q hq) h
    (Q'.le_of_lt (Q'.recipPos_pos q hq))

/-- `divPos (k · p) q ≃ k · divPos p q` (pull a scalar out of the quotient). -/
theorem divPos_scalar (k p q : Q') (hq : (0 : Q') < q) :
    (Q'.divPos (k * p) q hq).eqv (k * Q'.divPos p q hq) := by
  show ((k * p) * Q'.recipPos q hq).eqv (k * (p * Q'.recipPos q hq))
  exact Q'.mul_assoc_eqv k p (Q'.recipPos q hq)

/-- **Linear floor ⇒ cubic floor.**  `(1 − w)/a ≤ (1 − w³)/a`, so a lower bound on
the linear quotient gives one on the cubic quotient. -/
theorem linDivPos_le_cubicDivPos {w a : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (ha : (0 : Q') < a) :
    Q'.divPos ((1 : Q') - w) a ha
      ≤ Q'.divPos (heatKernelMargin w) a ha :=
  divPos_le_divPos_of_le ha (linear_le_cubicMargin hw0 hw1)

/-- **Cubic floor ⇒ 3× linear floor.**  `(1 − w³)/a ≤ 3 · (1 − w)/a`. -/
theorem cubicDivPos_le_three_linDivPos {w a : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (ha : (0 : Q') < a) :
    Q'.divPos (heatKernelMargin w) a ha
      ≤ (3 : Q') * Q'.divPos ((1 : Q') - w) a ha := by
  -- (1 − w³)/a ≤ (3·(1 − w))/a ≃ 3·((1 − w)/a)
  have h1 : Q'.divPos (heatKernelMargin w) a ha
      ≤ Q'.divPos ((3 : Q') * ((1 : Q') - w)) a ha :=
    divPos_le_divPos_of_le ha (cubicMargin_le_three_linear hw0 hw1)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (divPos_scalar 3 ((1 : Q') - w) a ha))

/-! ## 5. The cubic↔linear residual equivalence (up to the factor 3)

The open content `∃ c > 0, ∀ j, c ≤ (1 − w_j³)/a_j` is EQUIVALENT, up to the
harmless factor `3`, to the LINEAR residual `∃ c₀ > 0, ∀ j, c₀ ≤ (1 − w_j)/a_j`.
We state both directions as clean implications on the per-`j` bounds. -/

/-- **Linear residual ⇒ cubic residual (verbatim constant).**  A uniform linear
floor `c ≤ (1 − w_j)/a_j` gives the SAME constant as a cubic floor
`c ≤ (1 − w_j³)/a_j`.  This is the genuine simplification: the cubic open content
follows from the strictly simpler LINEAR one. -/
theorem cubic_floor_of_linear_floor
    {w a : Nat → Q'} {c : Q'}
    (hw0 : ∀ j, (0 : Q') ≤ w j) (hw1 : ∀ j, w j ≤ (1 : Q'))
    (ha : ∀ j, (0 : Q') < a j)
    (hlin : ∀ j, c ≤ Q'.divPos ((1 : Q') - w j) (a j) (ha j)) :
    ∀ j, c ≤ Q'.divPos (heatKernelMargin (w j)) (a j) (ha j) :=
  fun j => Q'.le_trans' _ _ _ (hlin j)
    (linDivPos_le_cubicDivPos (hw0 j) (hw1 j) (ha j))

/-- **Cubic residual ⇒ 3× linear residual.**  A uniform cubic floor
`c ≤ (1 − w_j³)/a_j` gives the linear floor `c ≤ 3·(1 − w_j)/a_j`, i.e. the cubic
floor is no stronger than `3` times the linear floor.  Together with the previous
direction this is the equivalence up to the factor `3`. -/
theorem three_linear_floor_of_cubic_floor
    {w a : Nat → Q'} {c : Q'}
    (hw0 : ∀ j, (0 : Q') ≤ w j) (hw1 : ∀ j, w j ≤ (1 : Q'))
    (ha : ∀ j, (0 : Q') < a j)
    (hcub : ∀ j, c ≤ Q'.divPos (heatKernelMargin (w j)) (a j) (ha j)) :
    ∀ j, c ≤ (3 : Q') * Q'.divPos ((1 : Q') - w j) (a j) (ha j) :=
  fun j => Q'.le_trans' _ _ _ (hcub j)
    (cubicDivPos_le_three_linDivPos (hw0 j) (hw1 j) (ha j))

/-! ## 6. The overlap-regime conditional — the LINEAR open input

In any regime where the heat-kernel-time-to-spacing ratio is bounded below,
`(1 − w(a))/a ≥ c₀ > 0` (the LINEAR difference quotient; `1 − w = 1 − e^{−t/4} ≈
t/4` for small `t`), the cubic floor `(1 − w(a)³)/a ≥ c₀` follows.  This is the
genuine reduction: the OPEN input is now the strictly simpler LINEAR one-variable
inequality, with the `w(a) ↔ a` (heat-kernel-time vs spacing) relation the
remaining frontier.  NO inhabitant of the linear floor is provided. -/

/-- **The overlap-regime implication.**  From the LINEAR floor
`∀ j, c₀ ≤ (1 − w_j)/a_j` conclude the CUBIC floor `∀ j, c₀ ≤ (1 − w_j³)/a_j`
with the SAME constant `c₀`.  The open input has been reduced from the cubic to
the LINEAR one-variable inequality. -/
theorem cubicFloor_of_linearFloor
    {w a : Nat → Q'} {c₀ : Q'}
    (hw0 : ∀ j, (0 : Q') ≤ w j) (hw1 : ∀ j, w j ≤ (1 : Q'))
    (ha : ∀ j, (0 : Q') < a j)
    (hlin : ∀ j, c₀ ≤ Q'.divPos ((1 : Q') - w j) (a j) (ha j)) :
    ∀ j, c₀ ≤ Q'.divPos (heatKernelMargin (w j)) (a j) (ha j) :=
  cubic_floor_of_linear_floor hw0 hw1 ha hlin

/-- **Linear floor ⇒ the explicit `HeatKernelResidual`.**  Packaging the overlap
implication: a strictly-positive LINEAR floor `c₀ ≤ (1 − w_j)/a_j` for all `j`
(with `0 ≤ w_j < 1`, `a_j > 0`) yields a `HeatKernelResidual w a …` (the explicit
cubic residual) with the SAME constant `c₀`.  Hence the cubic residual is
inhabited from the strictly simpler LINEAR one — its sole remaining open input.
NO inhabitant of the linear floor for 4D Yang–Mills is provided. -/
def heatKernelResidual_of_linearFloor
    {w a : Nat → Q'} {c₀ : Q'}
    (hw0 : ∀ j, (0 : Q') ≤ w j) (hw1 : ∀ j, w j < (1 : Q'))
    (ha : ∀ j, (0 : Q') < a j)
    (hc₀ : (0 : Q') < c₀)
    (hlin : ∀ j, c₀ ≤ Q'.divPos ((1 : Q') - w j) (a j) (ha j)) :
    HeatKernelResidual w a hw0 hw1 ha where
  c := c₀
  c_pos := hc₀
  bound := cubicFloor_of_linearFloor hw0 (fun j => Q'.le_of_lt (hw1 j)) ha hlin

end YMGap.Continuum.HeatKernelLinearBound

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HeatKernelLinearBound.heatKernelMargin_factor
#print axioms YMGap.Continuum.HeatKernelLinearBound.one_le_quadFactor
#print axioms YMGap.Continuum.HeatKernelLinearBound.quadFactor_le_three
#print axioms YMGap.Continuum.HeatKernelLinearBound.linear_le_cubicMargin
#print axioms YMGap.Continuum.HeatKernelLinearBound.cubicMargin_le_three_linear
#print axioms YMGap.Continuum.HeatKernelLinearBound.divPos_le_divPos_of_le
#print axioms YMGap.Continuum.HeatKernelLinearBound.divPos_scalar
#print axioms YMGap.Continuum.HeatKernelLinearBound.linDivPos_le_cubicDivPos
#print axioms YMGap.Continuum.HeatKernelLinearBound.cubicDivPos_le_three_linDivPos
#print axioms YMGap.Continuum.HeatKernelLinearBound.cubic_floor_of_linear_floor
#print axioms YMGap.Continuum.HeatKernelLinearBound.three_linear_floor_of_cubic_floor
#print axioms YMGap.Continuum.HeatKernelLinearBound.cubicFloor_of_linearFloor
#print axioms YMGap.Continuum.HeatKernelLinearBound.heatKernelResidual_of_linearFloor
