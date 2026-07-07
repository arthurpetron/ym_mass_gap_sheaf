/-
Track B / R2 — the EXACT single-mode single-polymer activity bound `|z_1| ≤ g²`,
proved to ALL ORDERS via the library's constructive exponential `ExpNeg.expNeg`.

# What this file proves (the all-orders upgrade of the leading bound)

`Continuum/SinglePolymerGaussian.lean` proved the LEADING-order activity bound
`|z_1| = (3/4)g² ≤ g²` in `Q'` (the fundamental-Casimir suppression, one term of the
expansion).  This file proves the EXACT, all-orders bound for the same minimal
single-mode su(2) Gaussian model.  The exact connected single-plaquette activity is the
transcendental object

    z_1(w)  =  1 − e^{−g²/4}(1 − g²/2) ,     g² = −log w ,

(the closed-form single-mode radial-Gaussian integral).  Writing `t := g²/4 ≥ 0`
(so `g² = 4t`), this is

    z_1  =  1 − e^{−t}(1 − 2t) ,

a genuine `CReal` built from the constructive exponential `ExpNeg.expNeg t` (the
`e^{−t}` whose approximations are the rational partial sums `∑ (−t)^k/k!`).  The theorem
`z1Exact_leRat_g2` proves

    z_1  ≤  g²  =  4t          for ALL `t ≥ 0`  (equivalently all `w ∈ (0,1)`),

i.e. `CReal.leRat (z1Exact t) (4*t)` — the exact single-mode `|z_1| ≤ g²`, to all orders,
through the transcendental `CRealExp`, not merely its leading term.

# The proof (two library exponential inequalities, no per-order truncation)

Algebraically `z_1 = (1 − e^{−t}) + 2t·e^{−t}` (the `CReal` identity `z1Exact_equiv_split`,
proved approx-wise).  The two summands are bounded by the constructive exponential's
two genuine transcendental inequalities:

  * the CONVEXITY bound   `1 − e^{−t} ≤ t`   (`CReal.oneSub_le_expNeg`, for `0 ≤ t ≤ 1`),
    and its coarse form  `1 − e^{−t} ≤ 1`   (`subConeExpNeg_le_one`, from `e^{−t} ≥ 0`);
  * the BOUNDEDNESS bound  `2t·e^{−t} ≤ 2t`  (`mul_bound`, from `e^{−t} ≤ 1` via
    `CReal.leRat_mul`).

Two regimes assemble the exact bound:

  * `t ≤ 1/2`:  `z_1 ≤ t + 2t = 3t ≤ 4t`      (convexity + boundedness);
  * `t ≥ 1/2`:  `z_1 ≤ 1 + 2t ≤ 4t`           (`1 − e^{−t} ≤ 1`, and `1 ≤ 2t`).

At `t → 0` the ratio `z_1/g² → 3/4` — the leading Casimir margin recovered as a limit of
the exact bound (numerically, mpmath dps 60: `z_1 ≤ g²` for all `w ∈ (0,1)`, worst ratio
`3/4`, zero violations in both regimes).

# HONEST SCOPE (AGENTS.md Rule 6 / Rule 9 — read before citing)

This closes the EXACT single-mode GAUSSIAN activity scalar `|z_1| ≤ g²` to all orders.
It is a GENUINE advance over `z1Leading_le_variance` (that bounded only the leading term
`(3/4)g²`; this bounds the full transcendental `1 − e^{−t}(1−2t)`).  It is NOT the full
config-space YM measure:

  * The bound proved is `z_1 ≤ g²` (the task's stated target), which is LOOSER than the
    KP field `z1_le_g2 : z1 k ≤ fieldActivity = (1 − w_k)` in
    `KPFieldAmplitude.SinglePolymerActivity`.  This module therefore does NOT inhabit
    `SinglePolymerActivity` or any KP structure; it is a standalone analytic theorem
    about the exact single-mode activity.
  * The REAL single-plaquette activity carries the full su(2)/Wilson (NON-Gaussian)
    structure; the single-mode Gaussian is the LEADING field-space model.  The
    field-Ursell SUBSTRATE (`treeDom`, the config-space measure) remains OPEN.

So: the exact single-mode Gaussian `|z_1| ≤ g²` is CLOSED to all orders; the real
activity + the field-Ursell substrate remain the genuine 4D-YM frontier.  No guarded
frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `CReal`/`Q'` via `ExpNeg.expNeg` (constructive `e^{−t}`, rational partial sums) and
the exponential inequalities `oneSub_le_expNeg`, `expNeg_le_one`, `expNeg_geRat_zero`,
`leRat_mul`.  Every load-bearing declaration is `#print axioms`-gated to
`propext`/`Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
-/
import YMGap.Constructive.CRealExp
import YMGap.Constructive.CRealMulLe
import YMGap.Constructive.CRealLe
import YMGap.Constructive.CRealAdd
import YMGap.Constructive.ExpPos
import YMGap.Constructive.Soundness
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.Reals

namespace YMGap.Continuum.ExactSinglePolymerActivity

open YMGap.Constructive

/-! ## 0. The rational `1/2` (the regime split point). -/

/-- The rational `1/2` — the boundary between the convexity regime (`t ≤ 1/2`) and the
boundedness regime (`t ≥ 1/2`). -/
def oneHalf : Q' := Q'.mkPos 1 2 (by decide)

/-! ## 1. The exact single-mode `z_1` as a `CReal`, and its linear split.

`z1Exact t = 1 − e^{−t}(1 − 2t)`.  Its approximations are `1 − (∑_{k<n}(−t)^k/k!)·(1−2t)`,
pure `Q'`; only the limit is transcendental.  `z1Split t = (1 − e^{−t}) + 2t·e^{−t}` is the
algebraically-equal reorganisation whose two summands the exponential inequalities bound. -/

/-- **The exact single-mode Gaussian activity** `z_1 = 1 − e^{−t}(1 − 2t)` as a `CReal`,
built from the constructive exponential `ExpNeg.expNeg t` (`= e^{−t}`). -/
def z1Exact (t : Q') (ht : (0 : Q') ≤ t) : CReal :=
  CReal.sub CReal.cone (CReal.mul (ExpNeg.expNeg t ht) (CReal.ofQ' (1 - 2 * t)))

/-- The linear split `z_1 = (1 − e^{−t}) + 2t·e^{−t}`. -/
def z1Split (t : Q') (ht : (0 : Q') ≤ t) : CReal :=
  CReal.add (CReal.sub CReal.cone (ExpNeg.expNeg t ht))
            (CReal.mul (ExpNeg.expNeg t ht) (CReal.ofQ' (2 * t)))

/-- Two-sided additive `eqv`-congruence (composed from the one-sided `Q'` versions). -/
private theorem add2 {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') :
    (a + b).eqv (a' + b') :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

/-- **The algebraic split identity** `1 − p·(1−2t) ≃ (1 − p) + p·(2t)`, for arbitrary
`p, t : Q'` (degree 1 in `p`): the core reorganisation of `z_1`. -/
private theorem split_identity (p t : Q') :
    ((1 : Q') + -(p * (1 - 2 * t))).eqv (((1 : Q') + -p) + p * (2 * t)) := by
  -- p * (1 - 2t) ≃ p + -(p * (2t))
  have hmul : (p * (1 - 2 * t)).eqv (p + -(p * (2 * t))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv p 1 (-(2 * t)))
      (add2 (Q'.mul_one_eqv p) (Q'.mul_neg_eqv p (2 * t)))
  -- -(p * (1 - 2t)) ≃ -p + p * (2t)
  have hneg : (-(p * (1 - 2 * t))).eqv (-p + p * (2 * t)) :=
    Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hmul)
      (Q'.eqv_trans _ _ _ (Q'.neg_add_eqv p (-(p * (2 * t))))
        (Q'.add_eqv_congr_left (-p) (-(-(p * (2 * t)))) (p * (2 * t))
          (Q'.neg_neg_eqv (p * (2 * t)))))
  -- 1 + -(p*(1-2t)) ≃ 1 + (-p + p*(2t)) ≃ (1 + -p) + p*(2t)
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 _ _ hneg)
    (Q'.eqv_symm (Q'.add_assoc_eqv 1 (-p) (p * (2 * t))))

/-- **The approx-wise identity** `z1Exact.approx n ≃ z1Split.approx n`. -/
theorem z1Exact_approx_eqv (t : Q') (ht : (0 : Q') ≤ t) (n : Nat) :
    ((z1Exact t ht).approx n).eqv ((z1Split t ht).approx n) :=
  split_identity (ExpNeg.partialSum t n) t

/-- **`z1Exact ≃ z1Split`** as constructive reals (approx-wise). -/
theorem z1Exact_equiv_split (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (z1Exact t ht) (z1Split t ht) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => z1Exact_approx_eqv t ht n)

/-! ## 2. `leRat` transports across `Equiv` (ε/2 split). -/

/-- If `A ≃ B` and `B`'s limit is `≤ b`, then `A`'s limit is `≤ b`. -/
theorem leRat_of_equiv {A B : CReal} {b : Q'} (h : CReal.Equiv A B)
    (hB : CReal.leRat B b) : CReal.leRat A b := by
  intro ε hε
  have hhε : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨N1, hN1⟩ := h (HalfPow.half * ε) hhε
  obtain ⟨N2, hN2⟩ := hB (HalfPow.half * ε) hhε
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hAB : A.approx n ≤ B.approx n + HalfPow.half * ε := (hN1 n hn1).1
  have hBb : B.approx n ≤ b + HalfPow.half * ε := hN2 n hn2
  have h1 : A.approx n ≤ (b + HalfPow.half * ε) + HalfPow.half * ε :=
    Q'.le_trans' _ _ _ hAB (Q'.add_le_add_right _ _ (HalfPow.half * ε) hBb)
  have h2 : ((b + HalfPow.half * ε) + HalfPow.half * ε).eqv (b + ε) :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv b (HalfPow.half * ε) (HalfPow.half * ε))
      (Q'.add_eqv_congr_left b _ _ (ExpNeg.two_halves ε))
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv h2)

/-! ## 3. The two exponential summand bounds. -/

/-- **Boundedness bound** `2t·e^{−t} ≤ 2t`, from `e^{−t} ≤ 1` via `CReal.leRat_mul`
(`e^{−t} ∈ [0,1]`, `2t ∈ [0,2t]`). -/
theorem mul_bound (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.leRat (CReal.mul (ExpNeg.expNeg t ht) (CReal.ofQ' (2 * t))) (2 * t) := by
  have h2t : (0 : Q') ≤ 2 * t := Q'.mul_nonneg 2 t (by decide) ht
  have hA : CReal.leRat (ExpNeg.expNeg t ht) 1 := CReal.expNeg_le_one t ht
  have hC : CReal.leRat (CReal.ofQ' (2 * t)) (2 * t) := CReal.leRat_ofQ' (Q'.le_refl' (2 * t))
  have hA0 : ExpPos.geRat (ExpNeg.expNeg t ht) 0 := expNeg_geRat_zero t ht
  have hC0 : ExpPos.geRat (CReal.ofQ' (2 * t)) 0 :=
    ExpPos.geRat_of_eventually ⟨0, fun n _ => h2t⟩
  have hmul := CReal.leRat_mul hA hC hA0 hC0 (by decide) h2t
  exact CReal.leRat_mono hmul (Q'.le_of_eqv (Q'.one_mul_eqv (2 * t)))

/-- **Coarse convexity bound** `1 − e^{−t} ≤ 1`, from `e^{−t} ≥ 0` (`expNeg_geRat_zero`).
Valid for ALL `t ≥ 0` (the regime `t ≥ 1/2` where the sharp `≤ t` needs `t ≤ 1`). -/
theorem subConeExpNeg_le_one (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.leRat (CReal.sub CReal.cone (ExpNeg.expNeg t ht)) 1 := by
  intro ε hε
  obtain ⟨N, hN⟩ := expNeg_geRat_zero t ht ε hε
  refine ⟨N, fun n hn => ?_⟩
  show (1 : Q') + -(ExpNeg.partialSum t n) ≤ 1 + ε
  have hge : (0 : Q') ≤ ExpNeg.partialSum t n + ε := hN n hn
  have h' : (0 : Q') ≤ ε + ExpNeg.partialSum t n :=
    Q'.le_trans' _ _ _ hge (Q'.le_of_eqv (Q'.add_comm_eqv (ExpNeg.partialSum t n) ε))
  exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_of_zero_le_add h')

/-! ## 4. The two rational tail inequalities (`3t ≤ 4t`, `1 + 2t ≤ 4t` for `t ≥ 1/2`). -/

/-- `t + 2t ≤ 4t` for `t ≥ 0` (the convexity-regime closing inequality). -/
theorem three_t_le_four_t (t : Q') (ht : (0 : Q') ≤ t) : t + 2 * t ≤ 4 * t := by
  have e : (t + 2 * t).eqv (3 * t) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right t (1 * t) (2 * t) (Q'.eqv_symm (Q'.one_mul_eqv t)))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv 1 2 t))
        (Q'.mul_eqv_congr_right ((1 : Q') + 2) 3 t (by decide)))
  have h34 : (3 : Q') * t ≤ (4 : Q') * t :=
    Q'.mul_le_mul_of_nonneg_right 3 4 t (by decide) ht
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e) h34

/-- `1 + 2t ≤ 4t` for `t ≥ 1/2` (the boundedness-regime closing inequality). -/
theorem one_add_two_t_le_four_t (t : Q') (hhalf : oneHalf ≤ t) :
    (1 : Q') + 2 * t ≤ 4 * t := by
  have h1 : (1 : Q') ≤ 2 * t := by
    have hstep : (2 : Q') * oneHalf ≤ (2 : Q') * t :=
      Q'.mul_le_mul_of_nonneg_left oneHalf t 2 hhalf (by decide)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (by decide : ((2 : Q') * oneHalf).eqv 1)) hstep
  have h2 : (1 : Q') + 2 * t ≤ 2 * t + 2 * t := Q'.add_le_add_right 1 (2 * t) (2 * t) h1
  have e : (2 * t + 2 * t).eqv (4 * t) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv 2 2 t))
      (Q'.mul_eqv_congr_right ((2 : Q') + 2) 4 t (by decide))
  exact Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv e)

/-! ## 5. The exact all-orders bound `z_1 ≤ g² = 4t`. -/

/-- **THE EXACT SINGLE-MODE `|z_1| ≤ g²`, ALL ORDERS.**  For every `t ≥ 0` (equivalently
every `w = e^{−4t} ∈ (0,1)`), the exact single-mode Gaussian activity
`z_1 = 1 − e^{−t}(1 − 2t)` satisfies `z_1 ≤ g² = 4t`, proved through the transcendental
constructive exponential `ExpNeg.expNeg` (not a truncation).  Two regimes:
`t ≤ 1/2` gives `z_1 ≤ 3t ≤ 4t`; `t ≥ 1/2` gives `z_1 ≤ 1 + 2t ≤ 4t`. -/
theorem z1Exact_leRat_g2 (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.leRat (z1Exact t ht) (4 * t) := by
  refine leRat_of_equiv (z1Exact_equiv_split t ht) ?_
  by_cases hcase : t ≤ oneHalf
  · -- convexity regime `t ≤ 1/2`: `z_1 ≤ t + 2t = 3t ≤ 4t`
    have ht1 : t ≤ (1 : Q') := Q'.le_trans' _ _ _ hcase (by decide : oneHalf ≤ (1 : Q'))
    have hsub : CReal.leRat (CReal.sub CReal.cone (ExpNeg.expNeg t ht)) t :=
      CReal.oneSub_le_expNeg ht ht1
    have hadd : CReal.leRat (z1Split t ht) (t + 2 * t) :=
      CReal.leRat_add hsub (mul_bound t ht)
    exact CReal.leRat_mono hadd (three_t_le_four_t t ht)
  · -- boundedness regime `t ≥ 1/2`: `z_1 ≤ 1 + 2t ≤ 4t`
    have hhalf : oneHalf ≤ t := by
      have hnot : ¬ (t.num * (oneHalf.den : Int) ≤ oneHalf.num * (t.den : Int)) := hcase
      show oneHalf.num * (t.den : Int) ≤ t.num * (oneHalf.den : Int)
      exact Int.le_of_lt (Int.not_le.mp hnot)
    have hadd : CReal.leRat (z1Split t ht) (1 + 2 * t) :=
      CReal.leRat_add (subConeExpNeg_le_one t ht) (mul_bound t ht)
    exact CReal.leRat_mono hadd (one_add_two_t_le_four_t t hhalf)

/-! ## 6. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **PROVED (axiom-clean, all-orders):** `z1Exact_leRat_g2` — the exact single-mode
Gaussian activity `z_1 = 1 − e^{−t}(1 − 2t) ≤ g² = 4t` for all `t ≥ 0`, via the
transcendental constructive exponential `ExpNeg.expNeg` and its two genuine inequalities
`oneSub_le_expNeg` (convexity) and `expNeg_le_one`/`expNeg_geRat_zero` (boundedness).
This is the ALL-ORDERS upgrade of `SinglePolymerGaussian.z1Leading_le_variance` (leading
term only).

**HONEST SCOPE.**  The bound is `z_1 ≤ g²` (looser than the KP field's `z_1 ≤ 1 − w`);
this module inhabits NO KP structure and NO frontier bundle.  The single-mode Gaussian is
the LEADING field-space model; the REAL su(2)/Wilson activity and the field-Ursell
substrate (`treeDom`, the config-space measure) remain OPEN.  Nothing is faked; the 4D
Yang–Mills mass gap remains OPEN. -/
theorem exactSinglePolymer_honesty : True := trivial

end YMGap.Continuum.ExactSinglePolymerActivity

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ExactSinglePolymerActivity.z1Exact_approx_eqv
#print axioms YMGap.Continuum.ExactSinglePolymerActivity.z1Exact_equiv_split
#print axioms YMGap.Continuum.ExactSinglePolymerActivity.leRat_of_equiv
#print axioms YMGap.Continuum.ExactSinglePolymerActivity.mul_bound
#print axioms YMGap.Continuum.ExactSinglePolymerActivity.subConeExpNeg_le_one
#print axioms YMGap.Continuum.ExactSinglePolymerActivity.three_t_le_four_t
#print axioms YMGap.Continuum.ExactSinglePolymerActivity.one_add_two_t_le_four_t
#print axioms YMGap.Continuum.ExactSinglePolymerActivity.z1Exact_leRat_g2
