/-
The **Δ-space Turán bridge**: an honest RELOCATION of the all-order heat-kernel
Gram PSD wall from the opaque coefficient fact `UniformTuranNonneg` to the
canonical *moment-functional positivity* `MomentFunctionalPositive` — the
log-convexity of the q-Hankel determinants `Δ_N`, i.e. the statement that the
heat-kernel moment functional is a genuine inner product (the physical
Osterwalder–Schrader positivity content).

# Setting (same uniform base variable as `Favard`/`FavardUniform`/`TuranPositivity`)

`a = e^{−t/4} ∈ (0,1]`; the order-`N` heat-kernel Gram leading minor factors
uniformly as `Δ_N = S_N²·P_N`, with `S_N = SN N` the explicit q-product square
factor and `P_N = Pseq N` the residual.  We work with the *factored* minor
`Δ_N(a) := (ceval (SN N) a)²·(ceval (Pseq N) a)` throughout.

Write `T_k := turanPoly k = P_{k+1}·P_{k−1} − P_k²` (the discrete Turán
determinant) and `f := a^{2k} − 1 = eval (qFac k) a` (the cyclotomic monomial).

# The bridge identity (the new, fully PROVED fact — all `k ≥ 2`)

From the `N`-indexed telescope `SN_telescope_gen` (PROVED, all `k`):

    S_{k+1}·S_{k−1} = (a^{2k}−1)·S_k²                              (telescope)

we derive, by squaring and pure ring algebra, the **Δ-space bridge**:

    f²·S_k⁴·T_k  =  Δ_{k+1}·Δ_{k−1}  −  f²·Δ_k²                     (bridge)

(`turan_delta_bridge`).  Both `f²` and `S_k⁴ = (S_k²)²` are perfect squares,
hence `≥ 0`; the denominator `f²·S_k⁴ = (f·S_k²)²` is a perfect square and is
strictly positive on `(0,1)` (each cyclotomic factor `a^{2j}−1 ≠ 0` there).

# The reduction (the genuine relocation)

GIVEN the log-convexity `Δ_k² ≤ Δ_{k+1}·Δ_{k−1}` (`MomentFunctionalPositive`),
and `0 < a < 1` (so `0 < f² < 1`, since `0 < a^{2k} < 1 ⇒ −1 < f < 0`), the
bracket obeys

    Δ_{k+1}Δ_{k−1} − f²Δ_k²  ≥  Δ_k² − f²Δ_k²  =  Δ_k²(1 − f²)  ≥  0,

so the LHS `f²·S_k⁴·T_k ≥ 0`; dividing by the strictly-positive perfect square
`f²·S_k⁴` gives `T_k(a) ≥ 0` on `(0,1)` (`turan_pointwise_of_momentPositive`),
the genuine pointwise input to the per-step Turán engine.  Composing with the
engine (`turan_step_pointwise`) and the uniform square factor gives the
all-order Gram PSD on `(0,1)`, conditional on `MomentFunctionalPositive`
(`delta_nonneg_all_of_momentPositive`).

# What is PROVED here (axiom-clean; no `Classical`/`sorry`/`native_decide`)

  * `turan_step_pointwise` — the pointwise per-step engine: from `0 < a < 1`,
    `P_{k−1}(a) > 0`, `P_k(a) > 0`, and the *pointwise* `T_k(a) ≥ 0` (`geRat`,
    NOT `nonnegCoeffs`), conclude `P_{k+1}(a) > 0`.  (A one-line generalization
    of `TuranPositivity.turan_step`, reusing the same `PosEv` cancellation.)

  * `turan_delta_bridge` — **THE NEW IDENTITY**, fully PROVED for all `k ≥ 2`
    from `SN_telescope_gen` + `ceval`/ring algebra:
    `f²·S_k⁴·T_k ≃ Δ_{k+1}Δ_{k−1} − f²·Δ_k²` at the constructive-real point.

  * `turan_pointwise_of_momentPositive` — the REDUCTION:
    `MomentFunctionalPositive ⇒ ∀ k a, 0<a → a<1 → T_k(a) ≥ 0`, via the bridge,
    log-convexity, and the strict positivity of the perfect-square denominator.

  * `delta_nonneg_all_of_momentPositive` — the CAPSTONE:
    `MomentFunctionalPositive ⇒ ∀ N a, 0<a → a<1 → Δ_N(a) ≥ 0`, composing the
    reduction with the pointwise engine (two-step induction) and the uniform
    square factor `S_N² ≥ 0`.

# NAMED-open (the canonical, cleaner wall)

`MomentFunctionalPositive : ∀ k a, 0<a → a<1 → Δ_k(a)² ≤ Δ_{k+1}(a)·Δ_{k−1}(a)`.

This is the **log-convexity of the q-Hankel determinants**, i.e. the statement
that the heat-kernel moment functional is a genuine inner product (Hankel
log-convexity ⇔ Cauchy–Schwarz on the representing moment measure).  It is the
*physical OS-positivity content*, and is a far cleaner, better-motivated
frontier than the opaque coefficient cone `UniformTuranNonneg` it relocates:
that wall asked for an `N`-indexed `nonnegCoeffs` fact with no representation-
theoretic meaning; this one is exactly the inner-product positivity of the
reconstructed Hilbert space.  Proving it uniformly is the canonical remaining
task (it needs the representing measure / Cauchy–Schwarz).

  **OPEN QUESTION (to investigate later).**  Whether `MomentFunctionalPositive`
  follows from the already-PROVED OS2 reflection positivity (the unconditional
  Osterwalder–Seiler/Schur Gram positivity of the reconstruction).  Hankel
  log-convexity is the determinant form of moment-matrix PSD, so a Sylvester /
  minor-of-a-PSD-matrix argument from the proved OS2 form positivity is the
  natural attack.  Not attempted here; named for follow-up.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`,
no `native_decide`.
-/

import YMGap.Continuum.TuranPositivity
import YMGap.Continuum.FavardUniform
import YMGap.Continuum.CyclotomicPositivity
import YMGap.Continuum.PNInduction
import YMGap.Continuum.CRealContinuumAlg

namespace YMGap.Continuum.TuranBridge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.PNInduction
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.FavardUniform
open YMGap.Continuum.CyclotomicPositivity

/-! ## The factored order-`N` minor `Δ_N(a) = (ceval (SN N) a)²·(ceval (Pseq N) a)`

We carry `Δ_N` in its factored constructive-real form throughout.  All bridge
and log-convexity statements are about this object. -/

/-- The factored order-`N` heat-kernel Gram minor at a constructive-real point:
`Δ_N(a) = (ceval (SN N) a)²·(ceval (Pseq N) a)`. -/
def deltaC (N : Nat) (a : CReal) : CReal :=
  CReal.mul (CReal.mul (ceval (SN N) a) (ceval (SN N) a)) (ceval (Pseq N) a)

/-! ## §1. The pointwise per-step engine `turan_step_pointwise`

A one-line generalization of `TuranPositivity.turan_step`: the only change is
that the Turán-remainder nonnegativity is supplied *pointwise*
(`geRat (ceval (turanPoly k) a) 0`) rather than as the coefficient fact
`nonnegCoeffs (turanPoly k)`.  Everything else (the `PosEv` algebra and the
cancellation `posEv_left_of_mul`) is reused verbatim. -/

/-- **The pointwise Turán step.**  For `a ≥ 0`, from `P_{k−1}(a) > 0`,
`P_k(a) > 0`, and the *pointwise* remainder bound `T_k(a) ≥ 0`, conclude
`P_{k+1}(a) > 0`.  Identical to `turan_step` except the remainder hypothesis is
the value-level `geRat (ceval (turanPoly k) a) 0`. -/
theorem turan_step_pointwise (k : Nat) {a : CReal} (ha : ExpPos.geRat a 0)
    (hPkm1 : PosEv (ceval (Pseq (k - 1)) a))
    (hPk : PosEv (ceval (Pseq k) a))
    (hTk : ExpPos.geRat (ceval (turanPoly k) a) 0) :
    PosEv (ceval (Pseq (k + 1)) a) := by
  have hPk2 : PosEv (CReal.mul (ceval (Pseq k) a) (ceval (Pseq k) a)) := posEv_sq hPk
  have hsum : PosEv (CReal.add (CReal.mul (ceval (Pseq k) a) (ceval (Pseq k) a))
      (ceval (turanPoly k) a)) := posEv_add_geRat hPk2 hTk
  have hprod : PosEv (ceval (QPoly.pmul (Pseq (k + 1)) (Pseq (k - 1))) a) :=
    posEv_of_equiv hsum (CReal.Equiv.symm (turan_value_identity k a))
  have hprod' : PosEv (CReal.mul (ceval (Pseq (k + 1)) a) (ceval (Pseq (k - 1)) a)) :=
    posEv_of_equiv hprod (ceval_pmul_equiv (Pseq (k + 1)) (Pseq (k - 1)) a)
  exact posEv_left_of_mul hprod' hPkm1

/-! ## §2. The bridge identity, at the `Q'`-`eval` level (the algebra)

`SN_telescope_gen` is a `QPoly.eval` identity over `Q'`.  We do all the ring
algebra in `Q'.eqv` (where the full congruence/assoc/comm/distrib API lives),
proving the bridge *at every base point* `x`, and lift to the constructive-real
statement afterwards by `ceval_approx`.

We abbreviate, at a fixed `x`:
  `u := eval(SN (k+1)) x`, `v := eval(SN (k−1)) x`, `s := eval(SN k) x`,
  `f := eval(qFac k) x`, and the residual values `pp,pm,pk := eval(Pseq _) x`.

The telescope (after `eval_pmul`) reads `u·v ≃ f·(s·s)`; squaring,
`(u·v)·(u·v) ≃ (f·f)·((s·s)·(s·s))`. -/

/-- `(−a)·(−b) ≃ a·b` over `Q'` (local; `TrigAdd` not in the import chain). -/
theorem q_neg_mul_neg (a b : Q') : ((-a) * (-b)).eqv (a * b) := by
  refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv a (-b)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv a b)) ?_
  exact Q'.neg_neg_eqv (a * b)

/-- Squaring the telescope value identity: `u·v ≃ f·(s·s)` gives
`(u·v)·(u·v) ≃ (f·f)·((s·s)·(s·s))`.  Pure `Q'` algebra. -/
theorem sq_telescope {u v f s : Q'} (h : (u * v).eqv (f * (s * s))) :
    ((u * v) * (u * v)).eqv ((f * f) * ((s * s) * (s * s))) := by
  -- (u·v)·(u·v) ≃ (f·s²)·(f·s²) ≃ (f·f)·(s²·s²) by 4-factor interchange.
  refine Q'.eqv_trans _ _ _ (q_mul_congr h h) ?_
  -- (f·(s·s))·(f·(s·s)) ≃ (f·f)·((s·s)·(s·s))
  exact q_mul4_swap f (s * s) f (s * s)

/-- The Δ-space bridge **as a `Q'.eqv` value identity** at a fixed base point `x`,
parametrized by the (squared) telescope hypothesis.  Writes
`Δ_{k+1}Δ_{k−1} − f²Δ_k²` (with `Δ_N = (s_N·s_N)·p_N`) as `f²·(s²)²·T_k`.

Let `uu := u·u = s_{k+1}²`, `vv := v·v = s_{k−1}²`, `ss := s·s = s_k²`,
`pp := p_{k+1}`, `pm := p_{k−1}`, `pk := p_k`, `f := eval(qFac k) x`.  The
hypothesis `hsq : (uu·vv) ≃ (f·f)·(ss·ss)` is the squared telescope (note
`uu·vv = (u·v)²`).  Conclusion (T_k = pp·pm − pk·pk):

  `((f·f)·(ss·ss)) · (pp·pm + −(pk·pk))
       ≃  (uu·pp)·(vv·pm)  +  −((f·f)·((ss·pk)·(ss·pk)))`. -/
theorem bridge_value {uu vv ss pp pm pk f : Q'}
    (hsq : (uu * vv).eqv ((f * f) * (ss * ss))) :
    (((f * f) * (ss * ss)) * (pp * pm + -(pk * pk))).eqv
      ((uu * pp) * (vv * pm) + -((f * f) * ((ss * pk) * (ss * pk)))) := by
  -- Let D := (f·f)·(ss·ss).  LHS = D·(pp·pm) + D·(−(pk·pk)) = D·(pp·pm) − D·(pk·pk).
  -- RHS term 1: (uu·pp)·(vv·pm) ≃ (uu·vv)·(pp·pm) ≃ D·(pp·pm)   [by hsq]
  -- RHS term 2: D·(pk·pk) ≃ (f·f)·((ss·pk)·(ss·pk))             [interchange]
  -- So LHS ≃ RHS.  (Write `D := (f·f)·(ss·ss)` literally throughout.)
  -- LHS distribute
  have hLHS : (((f * f) * (ss * ss)) * (pp * pm + -(pk * pk))).eqv
      (((f * f) * (ss * ss)) * (pp * pm) + ((f * f) * (ss * ss)) * (-(pk * pk))) :=
    Q'.mul_add_eqv ((f * f) * (ss * ss)) (pp * pm) (-(pk * pk))
  -- term1 of RHS: (uu·pp)·(vv·pm) ≃ (uu·vv)·(pp·pm) ≃ D·(pp·pm)
  have hT1 : ((uu * pp) * (vv * pm)).eqv (((f * f) * (ss * ss)) * (pp * pm)) := by
    refine Q'.eqv_trans _ _ _ (q_mul4_swap uu pp vv pm) ?_
    exact Q'.mul_eqv_congr_right _ _ _ hsq
  -- term2 of RHS: (f·f)·((ss·pk)·(ss·pk)) ≃ ((f·f)·(ss·ss))·(pk·pk) = D·(pk·pk)
  have hT2 : ((f * f) * ((ss * pk) * (ss * pk))).eqv (((f * f) * (ss * ss)) * (pk * pk)) := by
    -- (ss·pk)·(ss·pk) ≃ (ss·ss)·(pk·pk)  by interchange
    have hi : ((ss * pk) * (ss * pk)).eqv ((ss * ss) * (pk * pk)) :=
      q_mul4_swap ss pk ss pk
    -- (f·f)·((ss·pk)·(ss·pk)) ≃ (f·f)·((ss·ss)·(pk·pk)) ≃ ((f·f)·(ss·ss))·(pk·pk)
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hi) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv (f * f) (ss * ss) (pk * pk))
  -- D·(−(pk·pk)) ≃ −(D·(pk·pk)) ≃ −((f·f)·((ss·pk)·(ss·pk)))
  have hneg : (((f * f) * (ss * ss)) * (-(pk * pk))).eqv (-((f * f) * ((ss * pk) * (ss * pk)))) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv ((f * f) * (ss * ss)) (pk * pk)) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.eqv_symm hT2)
  -- assemble:  LHS ≃ D·(pp·pm) + D·(−(pk·pk))
  --                ≃ (uu·pp)·(vv·pm) + −((f·f)·((ss·pk)·(ss·pk)))
  refine Q'.eqv_trans _ _ _ hLHS ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (((f * f) * (ss * ss)) * (pp * pm)) ((uu * pp) * (vv * pm))
      (((f * f) * (ss * ss)) * (-(pk * pk))) (Q'.eqv_symm hT1)) ?_
  exact Q'.add_eqv_congr_left ((uu * pp) * (vv * pm)) (((f * f) * (ss * ss)) * (-(pk * pk)))
    (-((f * f) * ((ss * pk) * (ss * pk)))) hneg

/-! ## §3. The bridge identity at the constructive-real point — `turan_delta_bridge`

We lift `bridge_value` to a `CReal.Equiv`, reducing at every approximation index
`n` to `bridge_value` at the base point `x = a.approx n`, with the squared-
telescope hypothesis obtained from `SN_telescope_gen` (PROVED for all `k ≥ 2`)
via `eval_pmul` and `sq_telescope`.

Naming the constructive-real building blocks:
  `sq A := A·A`,  `qf := ceval (qFac k) a`,  `sk := ceval (SN k) a`,
  `Δ_N := deltaC N a`.  The bridge states

    (qf·qf)·((sk·sk)·(sk·sk))·T_k  ≃  Δ_{k+1}·Δ_{k−1} − (qf·qf)·(Δ_k·Δ_k). -/

/-- **THE Δ-SPACE TURÁN BRIDGE (new, fully PROVED for all `k ≥ 2`).**
At the constructive-real point `a`:

  `(f²·S_k⁴)·T_k  ≃  Δ_{k+1}·Δ_{k−1}  −  f²·Δ_k²`,

with `f = ceval (qFac k) a` (`= a^{2k}−1`), `S_k² = (ceval (SN k) a)²`,
`Δ_N = deltaC N a`, `T_k = ceval (turanPoly k) a`.  Proved from the
`N`-indexed telescope `SN_telescope_gen` + `sq_telescope` + `bridge_value`
(pure ring algebra), lifted approx-wise. -/
theorem turan_delta_bridge (k : Nat) (hk : 2 ≤ k) (a : CReal) :
    CReal.Equiv
      (CReal.mul
        (CReal.mul
          (CReal.mul (ceval (qFac k) a) (ceval (qFac k) a))
          (CReal.mul
            (CReal.mul (ceval (SN k) a) (ceval (SN k) a))
            (CReal.mul (ceval (SN k) a) (ceval (SN k) a))))
        (ceval (turanPoly k) a))
      (CReal.sub
        (CReal.mul (deltaC (k + 1) a) (deltaC (k - 1) a))
        (CReal.mul
          (CReal.mul (ceval (qFac k) a) (ceval (qFac k) a))
          (CReal.mul (deltaC k a) (deltaC k a)))) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  -- abbreviate the base point
  -- squared telescope at x = a.approx n :  (u·v) ≃ f·(s·s)
  have htel : (QPoly.eval (QPoly.pmul (SN (k + 1)) (SN (k - 1))) (a.approx n)).eqv
      (QPoly.eval (QPoly.pmul (qFac k) (QPoly.pmul (SN k) (SN k))) (a.approx n)) :=
    SN_telescope_gen k hk (a.approx n)
  -- rewrite both sides via eval_pmul to the value form u·v ≃ f·(s·s)
  have huv : ((QPoly.eval (SN (k + 1)) (a.approx n)) * (QPoly.eval (SN (k - 1)) (a.approx n))).eqv
      ((QPoly.eval (qFac k) (a.approx n))
        * ((QPoly.eval (SN k) (a.approx n)) * (QPoly.eval (SN k) (a.approx n)))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (QPoly.eval_pmul (SN (k + 1)) (SN (k - 1)) (a.approx n))) ?_
    refine Q'.eqv_trans _ _ _ htel ?_
    refine Q'.eqv_trans _ _ _ (QPoly.eval_pmul (qFac k) (QPoly.pmul (SN k) (SN k)) (a.approx n)) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (QPoly.eval_pmul (SN k) (SN k) (a.approx n))
  -- squared telescope:  (u·u)·(v·v) ≃ (f·f)·((s·s)·(s·s))
  have hsq : ((QPoly.eval (SN (k + 1)) (a.approx n) * QPoly.eval (SN (k + 1)) (a.approx n))
        * (QPoly.eval (SN (k - 1)) (a.approx n) * QPoly.eval (SN (k - 1)) (a.approx n))).eqv
      (((QPoly.eval (qFac k) (a.approx n)) * (QPoly.eval (qFac k) (a.approx n)))
        * (((QPoly.eval (SN k) (a.approx n)) * (QPoly.eval (SN k) (a.approx n)))
            * ((QPoly.eval (SN k) (a.approx n)) * (QPoly.eval (SN k) (a.approx n))))) := by
    -- (uu)·(vv) ≃ (u·v)·(u·v)  [interchange], then sq_telescope
    refine Q'.eqv_trans _ _ _
      (q_mul4_swap (QPoly.eval (SN (k + 1)) (a.approx n)) (QPoly.eval (SN (k + 1)) (a.approx n))
        (QPoly.eval (SN (k - 1)) (a.approx n)) (QPoly.eval (SN (k - 1)) (a.approx n))) ?_
    exact sq_telescope huv
  -- `eval (turanPoly k) x ≃ pp·pm + −(pk·pk)`  (eval_psub + eval_pmul ×2)
  have hT : (QPoly.eval (turanPoly k) (a.approx n)).eqv
      (QPoly.eval (Pseq (k + 1)) (a.approx n) * QPoly.eval (Pseq (k - 1)) (a.approx n)
        + -(QPoly.eval (Pseq k) (a.approx n) * QPoly.eval (Pseq k) (a.approx n))) := by
    refine Q'.eqv_trans _ _ _
      (QPoly.eval_psub (QPoly.pmul (Pseq (k + 1)) (Pseq (k - 1)))
        (QPoly.pmul (Pseq k) (Pseq k)) (a.approx n)) ?_
    refine Q'.add_eqv_congr' (QPoly.eval_pmul (Pseq (k + 1)) (Pseq (k - 1)) (a.approx n)) ?_
    exact Q'.neg_eqv_congr _ _ (QPoly.eval_pmul (Pseq k) (Pseq k) (a.approx n))
  -- both sides of the goal reduce definitionally (mul/add/neg/sub act approx-wise)
  -- to those of `hbv` after `ceval_approx`, except the LHS Turán factor needs `hT`.
  have hgoal := bridge_value (uu := QPoly.eval (SN (k + 1)) (a.approx n) * QPoly.eval (SN (k + 1)) (a.approx n))
    (vv := QPoly.eval (SN (k - 1)) (a.approx n) * QPoly.eval (SN (k - 1)) (a.approx n))
    (ss := QPoly.eval (SN k) (a.approx n) * QPoly.eval (SN k) (a.approx n))
    (pp := QPoly.eval (Pseq (k + 1)) (a.approx n))
    (pm := QPoly.eval (Pseq (k - 1)) (a.approx n))
    (pk := QPoly.eval (Pseq k) (a.approx n))
    (f := QPoly.eval (qFac k) (a.approx n)) hsq
  -- rewrite the Turán factor on the LHS of `hgoal` back to `eval (turanPoly k)`
  have hgoal' := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      ((QPoly.eval (qFac k) (a.approx n) * QPoly.eval (qFac k) (a.approx n))
        * ((QPoly.eval (SN k) (a.approx n) * QPoly.eval (SN k) (a.approx n))
            * (QPoly.eval (SN k) (a.approx n) * QPoly.eval (SN k) (a.approx n))))
      (QPoly.eval (turanPoly k) (a.approx n))
      (QPoly.eval (Pseq (k + 1)) (a.approx n) * QPoly.eval (Pseq (k - 1)) (a.approx n)
        + -(QPoly.eval (Pseq k) (a.approx n) * QPoly.eval (Pseq k) (a.approx n)))
      hT) hgoal
  simpa only [CReal.mul, CReal.sub, CReal.add, CReal.neg, deltaC, ceval_approx] using hgoal'

/-! ## §4. Strict positivity of the perfect-square denominator `f²·S_k⁴` on `(0,1)`

To cancel `f²·S_k⁴ = (f·S_k²)²` from the bridge we need it *strictly* positive
on `(0,1)`.  Each cyclotomic factor `eval (qFac j) x = x^{2j} − 1 < 0` there
(nonzero), so the `SNaux` product is nonzero and its square is `> 0`; likewise
`f = eval (qFac k) x` is nonzero so `f² > 0`.

The strict-positivity vocabulary is `PosEv` (eventual strictly-positive limit).
We represent `0 < a` as `PosEv a` and `a < 1` as `PosEv (CReal.sub CReal.cone a)`. -/

/-- `eval (qZeros m ++ p) x ≃ qpow x m · eval p x`: the `m` leading zeros pull out
`x^m` (Horner).  By induction on `m`. -/
theorem eval_qZeros_append (p : QPoly.Poly) (x : Q') :
    ∀ m, (QPoly.eval (qZeros m ++ p) x).eqv (qpow x m * QPoly.eval p x)
  | 0 => by
      -- qZeros 0 ++ p = p ; qpow x 0 = 1
      show (QPoly.eval p x).eqv (1 * QPoly.eval p x)
      exact Q'.eqv_symm (Q'.one_mul_eqv (QPoly.eval p x))
  | (m + 1) => by
      -- qZeros (m+1) ++ p = 0 :: (qZeros m ++ p)
      show ((0 : Q') + x * QPoly.eval (qZeros m ++ p) x).eqv (qpow x (m + 1) * QPoly.eval p x)
      -- LHS ≃ x · eval(qZeros m ++ p) ≃ x · (qpow x m · eval p) ≃ (x·qpow x m)·eval p
      refine Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv (x * QPoly.eval (qZeros m ++ p) x)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left x _ _ (eval_qZeros_append p x m)) ?_
      -- x·(qpow x m · eval p) ≃ (x · qpow x m)·eval p = qpow x (m+1)·eval p
      exact Q'.eqv_symm (Q'.mul_assoc_eqv x (qpow x m) (QPoly.eval p x))

/-- `eval (qFac (j+1)) x ≃ qpow x (2(j+1)) + (−1)` (`= x^{2(j+1)} − 1`). -/
theorem eval_qFac_eqv (x : Q') (j : Nat) :
    (QPoly.eval (qFac (j + 1)) x).eqv (qpow x (2 * (j + 1)) + -(1 : Q')) := by
  -- qFac (j+1) = (-1) :: (qZeros (2(j+1)-1) ++ [1])
  show ((-(1 : Q')) + x * QPoly.eval (qZeros (2 * (j + 1) - 1) ++ [Q'.ofNat 1]) x).eqv
      (qpow x (2 * (j + 1)) + -(1 : Q'))
  -- eval(qZeros m ++ [1]) ≃ qpow x m · eval [1] ≃ qpow x m · 1 ≃ qpow x m
  have hm : (QPoly.eval (qZeros (2 * (j + 1) - 1) ++ [Q'.ofNat 1]) x).eqv
      (qpow x (2 * (j + 1) - 1)) := by
    refine Q'.eqv_trans _ _ _ (eval_qZeros_append [Q'.ofNat 1] x (2 * (j + 1) - 1)) ?_
    -- qpow x m · eval [1] x ; eval [1] x = 1 + x*0 ≃ 1
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (qpow x (2 * (j + 1) - 1)) _ _ (eval_pone x)) ?_
    exact Q'.mul_one_eqv (qpow x (2 * (j + 1) - 1))
  -- x · eval(...) ≃ x · qpow x m = qpow x (m+1) ; and m+1 = 2(j+1)
  have hexp : (2 * (j + 1) - 1) + 1 = 2 * (j + 1) := by omega
  have hxm : (x * QPoly.eval (qZeros (2 * (j + 1) - 1) ++ [Q'.ofNat 1]) x).eqv
      (qpow x (2 * (j + 1))) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left x _ _ hm) ?_
    -- x · qpow x m = qpow x (m+1) (definitional), then rewrite exponent
    have : x * qpow x (2 * (j + 1) - 1) = qpow x ((2 * (j + 1) - 1) + 1) := rfl
    rw [this, hexp]
    exact Q'.eqv_refl _
  -- assemble: (-1) + x·(...) ≃ (-1) + qpow x (2(j+1)) ≃ qpow x (2(j+1)) + (-1)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (-(1 : Q')) _ _ hxm) ?_
  exact Q'.add_comm_eqv (-(1 : Q')) (qpow x (2 * (j + 1)))

/-- Monotonicity of the cyclotomic `qpow` in the base on `0 ≤ ·`:
`0 ≤ x → x ≤ y → qpow x n ≤ qpow y n`.  (Induction on `n`.) -/
theorem qpow_mono_base {x y : Q'} (hx : (0 : Q') ≤ x) (hxy : x ≤ y) :
    ∀ n, qpow x n ≤ qpow y n
  | 0 => by show (1 : Q') ≤ 1; exact Q'.le_refl' 1
  | (n + 1) => by
      -- x·x^n ≤ y·x^n ≤ y·y^n
      have hy : (0 : Q') ≤ y := Q'.le_trans' _ _ _ hx hxy
      have h1 : x * qpow x n ≤ y * qpow x n :=
        Q'.mul_le_mul_of_nonneg_right x y (qpow x n) hxy (qpow_nonneg_of_nonneg hx n)
      have h2 : y * qpow x n ≤ y * qpow y n :=
        CyclotomicPositivity.mul_le_mul_of_nonneg_left (qpow_mono_base hx hxy n) hy
      exact Q'.le_trans' _ _ _ h1 h2

/-! ### Eventual two-sided bound on `a.approx n` from `0 < a` and `a < 1` -/

/-- From `PosEv a` and `PosEv (cone − a)` extract a stage past which
`0 ≤ a.approx n` and `a.approx n ≤ 1 − c` for a fixed `0 < c`. -/
theorem eventually_in_unit {a : CReal} (ha0 : PosEv a)
    (ha1 : PosEv (CReal.sub CReal.cone a)) :
    ∃ c : Q', (0 : Q') < c ∧
      ∃ N : Nat, ∀ n, N ≤ n → (0 : Q') ≤ a.approx n ∧ a.approx n ≤ 1 + -c := by
  obtain ⟨ε0, hε0, N0, hN0⟩ := eventually_ge_of_posEv ha0
  obtain ⟨ε1, hε1, N1, hN1⟩ := eventually_ge_of_posEv ha1
  refine ⟨ε1, hε1, max N0 N1, fun n hn => ?_⟩
  have hn0 : N0 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  refine ⟨Q'.le_trans' _ _ _ (Q'.le_of_lt hε0) (hN0 n hn0), ?_⟩
  -- (cone − a).approx n = 1 + (-a_n) ≥ ε1, so a_n ≤ 1 + (-ε1)
  have hca : ε1 ≤ (1 : Q') + -(a.approx n) := hN1 n hn1
  -- a_n + ε1 ≤ a_n + (1 + -a_n) = 1  ⟹  a_n ≤ 1 + -ε1
  have hstep : a.approx n + ε1 ≤ a.approx n + (1 + -(a.approx n)) :=
    Q'.add_le_add_left (a.approx n) _ _ hca
  -- a_n + (1 + -a_n) ≃ 1
  have hcollapse : (a.approx n + (1 + -(a.approx n))).eqv (1 : Q') := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (a.approx n) 1 (-(a.approx n)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (a.approx n + 1) (1 + a.approx n) (-(a.approx n))
        (Q'.add_comm_eqv (a.approx n) 1)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv 1 (a.approx n) (-(a.approx n))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 1 (a.approx n + -(a.approx n)) 0 (Q'.add_neg_self_eqv (a.approx n))) ?_
    exact Q'.eqv_of_eq' (Q'.add_zero' 1)
  have hle1 : a.approx n + ε1 ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hcollapse)
  have hsub := Q'.add_le_add_right (a.approx n + ε1) 1 (-ε1) hle1
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) hsub
  -- (a_n + ε1) + -ε1 ≃ a_n
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (a.approx n) ε1 (-ε1)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (a.approx n) (ε1 + -ε1) 0 (Q'.add_neg_self_eqv ε1)) ?_
  exact Q'.eqv_of_eq' (Q'.add_zero' (a.approx n))

/-- `0 < c → 1 + -c < 1` over `Q'` (Int cross-product). -/
theorem one_add_neg_lt_one {c : Q'} (hc : (0 : Q') < c) : (1 : Q') + -c < 1 := by
  -- 1 + -c < 1 : (1+-c).num·1.den < 1.num·(1+-c).den
  have hcpos : (0 : Int) < c.num * ((1 : Q').den : Int) := by
    have : (0 : Int) * (c.den : Int) < c.num * ((0 : Q').den : Int) := hc
    simpa using this
  show ((1 : Q') + -c).num * ((1 : Q').den : Int) < (1 : Q').num * ((1 : Q') + -c).den
  have hnum : ((1 : Q') + -c).num = (1 : Q').num * (c.den : Int) + (-c.num) * ((1 : Q').den : Int) := rfl
  have hden : ((1 : Q') + -c).den = (1 : Q').den * c.den := rfl
  rw [hnum, hden]
  -- (1.num·c.den + (-c.num)·1.den)·1.den  <  1.num·(1.den·c.den)
  have e1 : (1 : Q').num = 1 := rfl
  have e2 : ((1 : Q').den : Int) = 1 := rfl
  rw [e1, e2]
  -- (1·c.den + (-c.num)·1)·1 < 1·(1·c.den)
  have hcn : (0 : Int) < c.num := by simpa [e2] using hcpos
  -- LHS = c.den − c.num ; RHS = c.den ; need c.den − c.num < c.den ⟺ 0 < c.num
  have hL : (1 * (c.den : Int) + (-c.num) * 1) * 1 = (c.den : Int) - c.num := by
    rw [Int.one_mul, Int.mul_one, Int.mul_one]; rfl
  have hlt : (1 * (c.den : Int) + (-c.num) * 1) * 1 < 1 * (1 * (c.den : Int)) := by
    rw [hL, Int.one_mul, Int.one_mul]; omega
  exact hlt

/-- **Each cyclotomic factor is strictly negative on `(0,1)`.**  For `0 < a < 1`
(as `PosEv a`, `PosEv (cone − a)`), `PosEv (neg (ceval (qFac (j+1)) a))`, i.e.
`eval (qFac (j+1)) a = a^{2(j+1)} − 1 < 0`. -/
theorem posEv_neg_qFac {a : CReal} (ha0 : PosEv a)
    (ha1 : PosEv (CReal.sub CReal.cone a)) (j : Nat) :
    PosEv (CReal.neg (ceval (qFac (j + 1)) a)) := by
  obtain ⟨c, hc, N, hN⟩ := eventually_in_unit ha0 ha1
  have hb := hN N (Nat.le_refl N)
  have h1mc_nonneg : (0 : Q') ≤ 1 + -c := Q'.le_trans' _ _ _ hb.1 hb.2
  have h1mc_lt1 : (1 : Q') + -c < 1 := one_add_neg_lt_one hc
  -- the positive witness ε := 1 − (1−c)^{2(j+1)} = 1 + -(qpow (1+-c) (2(j+1)))
  have hm : 2 * (j + 1) = (2 * (j + 1) - 1) + 1 := by omega
  have hεpos : (0 : Q') < 1 + -(qpow (1 + -c) (2 * (j + 1))) := by
    rw [hm]; exact one_sub_qpow_pos h1mc_nonneg h1mc_lt1 (2 * (j + 1) - 1)
  refine posEv_of_eventually hεpos ⟨N, fun n hn => ?_⟩
  -- goal: ε ≤ (neg (ceval (qFac (j+1)) a)).approx n = -(eval (qFac (j+1)) (a_n))
  obtain ⟨ha_nn, ha_le⟩ := hN n hn
  rw [CReal.neg_approx, ceval_approx]
  show (1 : Q') + -(qpow (1 + -c) (2 * (j + 1))) ≤ -(QPoly.eval (qFac (j + 1)) (a.approx n))
  -- -(eval(qFac(j+1)) a_n) ≃ 1 + -(qpow a_n (2(j+1)))
  have hval : (-(QPoly.eval (qFac (j + 1)) (a.approx n))).eqv
      ((1 : Q') + -(qpow (a.approx n) (2 * (j + 1)))) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (eval_qFac_eqv (a.approx n) j)) ?_
    -- -(qpow + -1) ≃ -qpow + 1 ≃ 1 + -qpow
    refine Q'.eqv_trans _ _ _
      (Q'.neg_add_eqv (qpow (a.approx n) (2 * (j + 1))) (-(1 : Q'))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-(qpow (a.approx n) (2 * (j + 1)))) (-(-(1 : Q'))) 1
        (Q'.neg_neg_eqv 1)) ?_
    exact Q'.add_comm_eqv (-(qpow (a.approx n) (2 * (j + 1)))) 1
  -- qpow a_n (2m) ≤ qpow (1-c) (2m)  ⟹  1 + -(qpow (1-c) 2m) ≤ 1 + -(qpow a_n 2m)
  have hmono : qpow (a.approx n) (2 * (j + 1)) ≤ qpow (1 + -c) (2 * (j + 1)) :=
    qpow_mono_base ha_nn ha_le (2 * (j + 1))
  have hneg_mono : -(qpow (1 + -c) (2 * (j + 1))) ≤ -(qpow (a.approx n) (2 * (j + 1))) :=
    Q'.neg_le_neg hmono
  -- assemble
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_left 1 _ _ hneg_mono) (Q'.ge_of_eqv hval)

/-- `PosEv (neg A) → PosEv (A·A)`: the square of a strictly-negative is
strictly positive (`(−A)·(−A) ≃ A·A`). -/
theorem posEv_sq_of_neg {A : CReal} (h : PosEv (CReal.neg A)) :
    PosEv (CReal.mul A A) := by
  have hsq : PosEv (CReal.mul (CReal.neg A) (CReal.neg A)) := posEv_sq h
  refine posEv_of_equiv hsq ?_
  -- (−A)·(−A) ≃ A·A
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((CReal.neg A).approx n * (CReal.neg A).approx n).eqv (A.approx n * A.approx n)
  rw [CReal.neg_approx]
  exact q_neg_mul_neg (A.approx n) (A.approx n)

/-- `PosEv` of the squared `ppow` of a factor whose square is `PosEv`.
`PosEv ((ceval p a)²) → PosEv ((ceval (ppow p m) a)²)`, by induction on `m`. -/
theorem posEv_ceval_ppow_sq {p : QPoly.Poly} {a : CReal}
    (hp : PosEv (CReal.mul (ceval p a) (ceval p a))) :
    ∀ m, PosEv (CReal.mul (ceval (ppow p m) a) (ceval (ppow p m) a))
  | 0 => by
      -- ppow p 0 = pone ; ceval pone a ≃ 1 ; square ≃ 1 > 0
      refine posEv_of_eventually (ε := Q'.ofNat 1) (by decide) ⟨0, fun n _ => ?_⟩
      show (Q'.ofNat 1) ≤ (ceval pone a).approx n * (ceval pone a).approx n
      rw [ceval_approx]
      -- eval pone (a_n) = 1 + a_n*0 ≃ 1, so square ≃ 1
      have he : (QPoly.eval pone (a.approx n)).eqv (1 : Q') := eval_pone (a.approx n)
      refine Q'.le_trans' _ _ _ (Q'.le_refl' (Q'.ofNat 1)) (Q'.ge_of_eqv ?_)
      refine Q'.eqv_trans _ _ _ (q_mul_congr he he) ?_
      exact Q'.one_mul_eqv 1
  | (m + 1) => by
      -- ppow p (m+1) = pmul p (ppow p m)
      -- ceval(ppow p (m+1)) a ≃ ceval p a · ceval(ppow p m) a, so square ≃ (p²)·(ppow²)
      have hstep := posEv_ceval_ppow_sq hp m
      have hprod : PosEv (CReal.mul (CReal.mul (ceval p a) (ceval p a))
          (CReal.mul (ceval (ppow p m) a) (ceval (ppow p m) a))) := posEv_mul hp hstep
      refine posEv_of_equiv hprod ?_
      -- (ceval(ppow p (m+1)) a)² ≃ (p²)·(ppow²)  -- prove by approx
      refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
      have hpe : (ceval (ppow p (m + 1)) a).approx n
          = QPoly.eval (QPoly.pmul p (ppow p m)) (a.approx n) := by rw [ceval_approx]; rfl
      show (((ceval p a).approx n * (ceval p a).approx n)
            * ((ceval (ppow p m) a).approx n * (ceval (ppow p m) a).approx n)).eqv
          ((ceval (ppow p (m + 1)) a).approx n * (ceval (ppow p (m + 1)) a).approx n)
      rw [hpe, ceval_approx, ceval_approx]
      -- eval(pmul p (ppow p m)) = eval p · eval(ppow p m)
      have hpm : (QPoly.eval (QPoly.pmul p (ppow p m)) (a.approx n)).eqv
          (QPoly.eval p (a.approx n) * QPoly.eval (ppow p m) (a.approx n)) :=
        QPoly.eval_pmul p (ppow p m) (a.approx n)
      -- (P·P)·(G·G) ≃ (P·G)·(P·G) ≃ (e·e)  with e = eval(pmul..)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _ (q_mul_congr hpm hpm) ?_
      exact q_mul4_swap (QPoly.eval p (a.approx n)) (QPoly.eval (ppow p m) (a.approx n))
        (QPoly.eval p (a.approx n)) (QPoly.eval (ppow p m) (a.approx n))

/-- **`PosEv` of `(ceval (SNaux N j) a)²` on `(0,1)`.**  By induction on `j`:
each `SNaux` factor is a `ppow` of a cyclotomic `qFac`, whose square is `PosEv`
(`posEv_neg_qFac` + `posEv_sq_of_neg`), and products of `PosEv`s are `PosEv`. -/
theorem posEv_ceval_SNaux_sq {a : CReal} (ha0 : PosEv a)
    (ha1 : PosEv (CReal.sub CReal.cone a)) :
    ∀ N j, PosEv (CReal.mul (ceval (SNaux N j) a) (ceval (SNaux N j) a))
  | _, 0 => by
      -- SNaux N 0 = pone
      refine posEv_of_eventually (ε := Q'.ofNat 1) (by decide) ⟨0, fun n _ => ?_⟩
      show (Q'.ofNat 1) ≤ (ceval pone a).approx n * (ceval pone a).approx n
      rw [ceval_approx]
      have he : (QPoly.eval pone (a.approx n)).eqv (1 : Q') := eval_pone (a.approx n)
      refine Q'.le_trans' _ _ _ (Q'.le_refl' (Q'.ofNat 1)) (Q'.ge_of_eqv ?_)
      refine Q'.eqv_trans _ _ _ (q_mul_congr he he) ?_
      exact Q'.one_mul_eqv 1
  | N, (j + 1) => by
      -- SNaux N (j+1) = pmul (ppow (qFac (j+1)) (N-(j+1))) (SNaux N j)
      have hqf : PosEv (CReal.mul (ceval (qFac (j + 1)) a) (ceval (qFac (j + 1)) a)) :=
        posEv_sq_of_neg (posEv_neg_qFac ha0 ha1 j)
      have hpow : PosEv (CReal.mul (ceval (ppow (qFac (j + 1)) (N - (j + 1))) a)
          (ceval (ppow (qFac (j + 1)) (N - (j + 1))) a)) :=
        posEv_ceval_ppow_sq hqf (N - (j + 1))
      have haux : PosEv (CReal.mul (ceval (SNaux N j) a) (ceval (SNaux N j) a)) :=
        posEv_ceval_SNaux_sq ha0 ha1 N j
      have hprod : PosEv (CReal.mul
          (CReal.mul (ceval (ppow (qFac (j + 1)) (N - (j + 1))) a)
            (ceval (ppow (qFac (j + 1)) (N - (j + 1))) a))
          (CReal.mul (ceval (SNaux N j) a) (ceval (SNaux N j) a))) :=
        posEv_mul hpow haux
      refine posEv_of_equiv hprod ?_
      -- (ceval(SNaux N (j+1)) a)² ≃ (pow²)·(aux²)
      refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
      have hse : (ceval (SNaux N (j + 1)) a).approx n
          = QPoly.eval (QPoly.pmul (ppow (qFac (j + 1)) (N - (j + 1))) (SNaux N j)) (a.approx n) := by
        rw [ceval_approx]; rfl
      show (((ceval (ppow (qFac (j + 1)) (N - (j + 1))) a).approx n
              * (ceval (ppow (qFac (j + 1)) (N - (j + 1))) a).approx n)
            * ((ceval (SNaux N j) a).approx n * (ceval (SNaux N j) a).approx n)).eqv
          ((ceval (SNaux N (j + 1)) a).approx n * (ceval (SNaux N (j + 1)) a).approx n)
      rw [hse, ceval_approx, ceval_approx]
      have hpm : (QPoly.eval (QPoly.pmul (ppow (qFac (j + 1)) (N - (j + 1))) (SNaux N j)) (a.approx n)).eqv
          (QPoly.eval (ppow (qFac (j + 1)) (N - (j + 1))) (a.approx n)
            * QPoly.eval (SNaux N j) (a.approx n)) :=
        QPoly.eval_pmul (ppow (qFac (j + 1)) (N - (j + 1))) (SNaux N j) (a.approx n)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _ (q_mul_congr hpm hpm) ?_
      exact q_mul4_swap (QPoly.eval (ppow (qFac (j + 1)) (N - (j + 1))) (a.approx n))
        (QPoly.eval (SNaux N j) (a.approx n))
        (QPoly.eval (ppow (qFac (j + 1)) (N - (j + 1))) (a.approx n))
        (QPoly.eval (SNaux N j) (a.approx n))

/-- **`PosEv (S_N(a)²)` on `(0,1)`** (`SN N = SNaux N (N−1)`). -/
theorem posEv_ceval_SN_sq {a : CReal} (ha0 : PosEv a)
    (ha1 : PosEv (CReal.sub CReal.cone a)) (N : Nat) :
    PosEv (CReal.mul (ceval (SN N) a) (ceval (SN N) a)) :=
  posEv_ceval_SNaux_sq ha0 ha1 N (N - 1)

/-- **`PosEv (f²·S_k⁴)` — the perfect-square bridge denominator is strictly
positive on `(0,1)`** (for `k ≥ 1`).  `f²` is `posEv_sq_of_neg (posEv_neg_qFac)`;
`S_k⁴ = (S_k²)²` is `posEv_sq` of `posEv_ceval_SN_sq`; product is `PosEv`. -/
theorem posEv_bridge_denom {a : CReal} (ha0 : PosEv a)
    (ha1 : PosEv (CReal.sub CReal.cone a)) (k : Nat) (hk : 1 ≤ k) :
    PosEv (CReal.mul
      (CReal.mul (ceval (qFac k) a) (ceval (qFac k) a))
      (CReal.mul
        (CReal.mul (ceval (SN k) a) (ceval (SN k) a))
        (CReal.mul (ceval (SN k) a) (ceval (SN k) a)))) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hf2 : PosEv (CReal.mul (ceval (qFac (k' + 1)) a) (ceval (qFac (k' + 1)) a)) :=
    posEv_sq_of_neg (posEv_neg_qFac ha0 ha1 k')
  have hs2 : PosEv (CReal.mul (ceval (SN (k' + 1)) a) (ceval (SN (k' + 1)) a)) :=
    posEv_ceval_SN_sq ha0 ha1 (k' + 1)
  exact posEv_mul hf2 (posEv_sq hs2)

/-! ## §5. Nonnegative cancellation + the moment-functional wall + the reduction -/

/-- **Nonnegative cancellation core.**  `geRat (A·B) 0 → PosEv B → geRat A 0`.
Pointwise: eventually `Aₙ·Bₙ ≥ −δ'` and `Bₙ ≥ e > 0`; if `Aₙ < 0` then
`Aₙ·Bₙ ≤ Aₙ·e`, so `Aₙ·e ≥ −δ'`, i.e. `Aₙ ≥ −δ'/e`; choosing `δ' = δ·e` gives
`Aₙ ≥ −δ`.  (The nonneg analogue of `posEv_left_of_mul`.) -/
theorem geRat_left_of_mul_posEv {A B : CReal} (hAB : ExpPos.geRat (CReal.mul A B) 0)
    (hB : PosEv B) : ExpPos.geRat A 0 := by
  obtain ⟨e, he, Ne, hNe⟩ := eventually_ge_of_posEv hB
  intro δ hδ
  -- δ' := δ·e > 0
  have hδe : (0 : Q') < δ * e := Q'.mul_pos hδ he
  obtain ⟨Nd, hNd⟩ := hAB (δ * e) hδe
  refine ⟨max Nd Ne, fun n hn => ?_⟩
  have hnd : Nd ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hne : Ne ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  -- 0 ≤ Aₙ·Bₙ + δ·e   (geRat at δ·e)
  have hABn : (0 : Q') ≤ A.approx n * B.approx n + δ * e := hNd n hnd
  have hBn : e ≤ B.approx n := hNe n hne
  have hBpos : (0 : Q') < B.approx n := q_lt_of_lt_of_le he hBn
  -- goal: 0 ≤ Aₙ + δ
  show (0 : Q') ≤ A.approx n + δ
  -- case split on sign of Aₙ
  rcases (inferInstance : Decidable ((0 : Q') ≤ A.approx n)) with hneg | hpos
  · -- ¬(0 ≤ Aₙ): Aₙ ≤ 0.  Then Aₙ·Bₙ ≤ Aₙ·e (since Bₙ ≥ e, Aₙ ≤ 0)
    have hAle : A.approx n ≤ 0 := Q'.le_of_not_le hneg
    -- −Aₙ ≥ 0 :  Aₙ + -Aₙ ≤ 0 + -Aₙ, LHS ≃ 0, RHS ≃ -Aₙ
    have hnAnn : (0 : Q') ≤ -(A.approx n) := by
      have hstep := Q'.add_le_add_right (A.approx n) 0 (-(A.approx n)) hAle
      refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv (A.approx n)))
        (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (QPoly.q_zero_add_eqv (-(A.approx n)))))
    -- (−Aₙ)·e ≤ (−Aₙ)·Bₙ
    have hge : -(A.approx n) * e ≤ -(A.approx n) * B.approx n :=
      CyclotomicPositivity.mul_le_mul_of_nonneg_left hBn hnAnn
    -- ⟹ Aₙ·Bₙ ≤ Aₙ·e   (negate both, using (−x)·y ≃ −(x·y))
    have hmul : A.approx n * B.approx n ≤ A.approx n * e := by
      have hng := Q'.neg_le_neg hge   -- −((−Aₙ)·Bₙ) ≤ −((−Aₙ)·e)
      refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) (Q'.le_trans' _ _ _ hng (Q'.le_of_eqv ?_))
      · -- Aₙ·Bₙ ≃ −((−Aₙ)·Bₙ)   [−((−Aₙ)·Bₙ) ≃ −(−(Aₙ·Bₙ)) ≃ Aₙ·Bₙ]
        exact Q'.eqv_trans _ _ _
          (Q'.neg_eqv_congr _ _ (Q'.neg_mul_eqv (A.approx n) (B.approx n)))
          (Q'.neg_neg_eqv (A.approx n * B.approx n))
      · -- −((−Aₙ)·e) ≃ Aₙ·e
        refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.neg_mul_eqv (A.approx n) e)) ?_
        exact Q'.neg_neg_eqv (A.approx n * e)
    -- 0 ≤ Aₙ·Bₙ + δe ≤ Aₙ·e + δe = (Aₙ+δ)·e
    have h0 : (0 : Q') ≤ A.approx n * e + δ * e :=
      Q'.le_trans' _ _ _ hABn (Q'.add_le_add_right _ _ (δ * e) hmul)
    -- (Aₙ+δ)·e ≃ Aₙ·e + δ·e
    have hfac : ((A.approx n + δ) * e).eqv (A.approx n * e + δ * e) := Q'.add_mul_eqv _ _ _
    have h0' : (0 : Q') ≤ (A.approx n + δ) * e :=
      Q'.le_trans' _ _ _ h0 (Q'.ge_of_eqv hfac)
    -- 0 = e·0, so e·0 ≤ e·(Aₙ+δ) ⟹ 0 ≤ Aₙ+δ   (left cancellation)
    have h0e : e * 0 ≤ e * (A.approx n + δ) := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (QPoly.q_mul_zero e)) ?_
      refine Q'.le_trans' _ _ _ h0' (Q'.le_of_eqv (Q'.mul_comm_eqv (A.approx n + δ) e))
    exact Q'.le_of_mul_le_mul_left h0e he
  · exact Q'.le_trans' _ _ _ hpos (Q'.add_le_self_of_nonneg (A.approx n) δ (Q'.le_of_lt hδ))

/-- `0 ≤ x → x ≤ 1 → x·x ≤ 1` over `Q'`. -/
theorem q_sq_le_one {x : Q'} (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) : x * x ≤ 1 := by
  -- x·x ≤ x·1 = x ≤ 1
  have h1 : x * x ≤ x * 1 := CyclotomicPositivity.mul_le_mul_of_nonneg_left hx1 hx0
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv x)) hx1)

/-- **`f² ≤ 1` on `(0,1)`** (`f = ceval (qFac k) a`, `k ≥ 1`): the cyclotomic
square is bounded by `1`, i.e. `geRat (cone − f²) 0`.  (`f² = (1 − a^{2k})²`
with `0 ≤ 1 − a^{2k} ≤ 1`.) -/
theorem geRat_one_sub_qFac_sq {a : CReal} (ha0 : PosEv a)
    (ha1 : PosEv (CReal.sub CReal.cone a)) (k : Nat) (hk : 1 ≤ k) :
    ExpPos.geRat (CReal.sub CReal.cone (CReal.mul (ceval (qFac k) a) (ceval (qFac k) a))) 0 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨c, hc, N, hN⟩ := eventually_in_unit ha0 ha1
  refine ExpPos.geRat_of_eventually ⟨N, fun n hn => ?_⟩
  obtain ⟨ha_nn, ha_le⟩ := hN n hn
  -- a_n ≤ 1 (from a_n ≤ 1 + -c ≤ 1)
  have ha_le1 : a.approx n ≤ 1 := by
    refine Q'.le_trans' _ _ _ ha_le ?_
    -- 1 + -c ≤ 1 (since 0 ≤ c)
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 (-c) 0 ?_) (Q'.le_of_eqv (Q'.eqv_of_eq' (Q'.add_zero' 1)))
    -- -c ≤ 0
    have := Q'.neg_le_neg (Q'.le_of_lt hc)  -- -c ≤ -0
    refine Q'.le_trans' _ _ _ this (Q'.le_of_eqv ?_)
    -- -0 ≃ 0 :  0 + -0 ≃ -0 and 0 + -0 ≃ 0
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (QPoly.q_zero_add_eqv (-(0:Q')))) ?_
    exact Q'.add_neg_self_eqv 0
  -- goal: 0 ≤ (sub cone (mul f f)).approx n = 1 + -(f_n · f_n)
  show (0 : Q') ≤ (1 : Q') + -((ceval (qFac (k' + 1)) a).approx n * (ceval (qFac (k' + 1)) a).approx n)
  rw [ceval_approx]
  -- f_n ≃ qpow a_n (2(k'+1)) + -1 ; let q := qpow a_n (2(k'+1)), 0 ≤ q ≤ 1
  have hq0 : (0 : Q') ≤ qpow (a.approx n) (2 * (k' + 1)) := qpow_nonneg_of_nonneg ha_nn _
  have hq1 : qpow (a.approx n) (2 * (k' + 1)) ≤ 1 := qpow_le_one ha_nn ha_le1 _
  -- f_n · f_n ≃ (q + -1)·(q + -1), and (q-1)·(q-1) = (1-q)·(1-q) ≤ 1
  have hfe : (QPoly.eval (qFac (k' + 1)) (a.approx n)).eqv
      (qpow (a.approx n) (2 * (k' + 1)) + -(1 : Q')) := eval_qFac_eqv (a.approx n) k'
  have hsqe : (QPoly.eval (qFac (k' + 1)) (a.approx n)
        * QPoly.eval (qFac (k' + 1)) (a.approx n)).eqv
      ((1 + -(qpow (a.approx n) (2 * (k' + 1))))
        * (1 + -(qpow (a.approx n) (2 * (k' + 1))))) := by
    -- f_n ≃ q-1 ≃ -(1-q), so f_n² ≃ (1-q)²
    have hneg : (QPoly.eval (qFac (k' + 1)) (a.approx n)).eqv
        (-(1 + -(qpow (a.approx n) (2 * (k' + 1))))) := by
      refine Q'.eqv_trans _ _ _ hfe ?_
      -- q + -1 ≃ -(1 + -q)
      refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.neg_add_eqv 1 (-(qpow (a.approx n) (2 * (k' + 1))))))
      -- q + -1 ≃ -1 + q ≃ -1 + -(-q)
      refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (qpow (a.approx n) (2 * (k' + 1))) (-1)) ?_
      exact Q'.add_eqv_congr_left (-1) _ _ (Q'.eqv_symm (Q'.neg_neg_eqv (qpow (a.approx n) (2 * (k' + 1)))))
    refine Q'.eqv_trans _ _ _ (q_mul_congr hneg hneg) ?_
    exact q_neg_mul_neg _ _
  -- 0 ≤ 1-q ≤ 1, so (1-q)² ≤ 1
  have h1mq0 : (0 : Q') ≤ 1 + -(qpow (a.approx n) (2 * (k' + 1))) :=
    Q'.sub_nonneg_of_le hq1
  have h1mq1 : (1 : Q') + -(qpow (a.approx n) (2 * (k' + 1))) ≤ 1 := by
    -- 1 + -q ≤ 1 since 0 ≤ q
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ 0 ?_) (Q'.le_of_eqv (Q'.eqv_of_eq' (Q'.add_zero' 1)))
    have := Q'.neg_le_neg hq0  -- -q ≤ -0
    refine Q'.le_trans' _ _ _ this (Q'.le_of_eqv ?_)
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (QPoly.q_zero_add_eqv (-(0:Q')))) ?_
    exact Q'.add_neg_self_eqv 0
  have hsqle : (1 + -(qpow (a.approx n) (2 * (k' + 1))))
        * (1 + -(qpow (a.approx n) (2 * (k' + 1)))) ≤ 1 :=
    q_sq_le_one h1mq0 h1mq1
  -- f_n² ≤ 1  ⟹  0 ≤ 1 + -(f_n²)
  have hfsqle : QPoly.eval (qFac (k' + 1)) (a.approx n)
      * QPoly.eval (qFac (k' + 1)) (a.approx n) ≤ 1 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hsqe) hsqle
  exact Q'.sub_nonneg_of_le hfsqle

/-- Generic `Q'` bracket split: `(U·V) − (F·W) ≃ ((U·V) − W) + ((1 − F)·W)`.
(`W = Δ_k²`, `F = f²`, `U·V = Δ_{k+1}Δ_{k−1}`.)  Pure ring algebra. -/
theorem bracket_split (U V F W : Q') :
    (U * V + -(F * W)).eqv ((U * V + -W) + (1 + -F) * W) := by
  -- RHS = (U·V + -W) + (W + -(F·W))  ≃ U·V + (-W + (W + -(F·W))) ≃ U·V + -(F·W)
  -- (1+-F)·W ≃ W + -(F·W)
  have hdist : ((1 + -F) * W).eqv (W + -(F * W)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 (-F) W) ?_
    refine Q'.add_eqv_congr' (Q'.one_mul_eqv W) ?_
    exact Q'.neg_mul_eqv F W
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (U * V + -W) _ _ hdist) ?_
  -- (U·V + -W) + (W + -(F·W)) ≃ U·V + (-W + (W + -(F·W)))
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (U * V) (-W) (W + -(F * W))) ?_
  refine Q'.add_eqv_congr_left (U * V) _ _ ?_
  -- -W + (W + -(F·W)) ≃ (-W + W) + -(F·W) ≃ 0 + -(F·W) ≃ -(F·W)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (-W) W (-(F * W)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (-W + W) 0 (-(F * W)) (Q'.neg_add_self_eqv W)) ?_
  exact QPoly.q_zero_add_eqv (-(F * W))

/-! ## §5b. The named, canonical wall and the reduction -/

/-- **NAMED-OPEN — the canonical, cleaner wall.**  The *log-convexity of the
q-Hankel determinants* `Δ_N` on `(0,1)`:

    Δ_k(a)²  ≤  Δ_{k+1}(a)·Δ_{k−1}(a)        (`Δ_k = deltaC k a`),

stated as `geRat (Δ_{k+1}Δ_{k−1} − Δ_k²) 0`.  This is exactly the statement
that the heat-kernel **moment functional is a genuine inner product** (Hankel
log-convexity ⇔ Cauchy–Schwarz on the representing moment measure), i.e. the
physical Osterwalder–Schrader positivity content.  It RELOCATES the opaque
coefficient wall `TuranPositivity.UniformTuranNonneg` to this motivated,
canonical frontier.

`0 < a` / `a < 1` are carried as `PosEv a` / `PosEv (cone − a)`.

  *Open question (follow-up):* whether this follows from the already-proved OS2
  reflection positivity (`ReflectionPositivity.lean`) — Hankel log-convexity is
  the determinant form of moment-matrix PSD, so a Sylvester/minor argument from
  the proved OS2 Gram positivity is the natural attack.  Not attempted here. -/
def MomentFunctionalPositive : Prop :=
  ∀ (k : Nat) (a : CReal), PosEv a → PosEv (CReal.sub CReal.cone a) →
    ExpPos.geRat
      (CReal.sub (CReal.mul (deltaC (k + 1) a) (deltaC (k - 1) a))
        (CReal.mul (deltaC k a) (deltaC k a))) 0

/-- **THE REDUCTION (genuine relocation).**  `MomentFunctionalPositive` implies
the *pointwise* Turán-remainder nonnegativity `T_k(a) ≥ 0` on `(0,1)` for every
`k ≥ 2`.  Proof: bracket `Δ_{k+1}Δ_{k−1} − f²Δ_k² ≥ Δ_k²(1−f²) ≥ 0` (MFP +
`f² ≤ 1` + `Δ_k² ≥ 0`); the bridge `f²·S_k⁴·T_k = bracket`; then cancel the
strictly-positive perfect square `f²·S_k⁴` (`posEv_bridge_denom`). -/
theorem turan_pointwise_of_momentPositive (hMFP : MomentFunctionalPositive)
    (k : Nat) (hk : 2 ≤ k) {a : CReal} (ha0 : PosEv a)
    (ha1 : PosEv (CReal.sub CReal.cone a)) :
    ExpPos.geRat (ceval (turanPoly k) a) 0 := by
  have hk1 : 1 ≤ k := by omega
  -- abbreviations
  -- W := Δ_k² ; F := f² ; U·V := Δ_{k+1}Δ_{k-1}
  -- bracket = sub (mul Δkp1 Δkm1) (mul F W)
  -- (1) MFP quantity ≥ 0
  have hMFPq : ExpPos.geRat
      (CReal.sub (CReal.mul (deltaC (k + 1) a) (deltaC (k - 1) a))
        (CReal.mul (deltaC k a) (deltaC k a))) 0 := hMFP k a ha0 ha1
  -- (2) Δ_k² ≥ 0
  have hW : ExpPos.geRat (CReal.mul (deltaC k a) (deltaC k a)) 0 :=
    SumOfSquares.geRat_sq_nonneg (deltaC k a)
  -- (3) (1 − f²) ≥ 0
  have hF : ExpPos.geRat
      (CReal.sub CReal.cone (CReal.mul (ceval (qFac k) a) (ceval (qFac k) a))) 0 :=
    geRat_one_sub_qFac_sq ha0 ha1 k hk1
  -- (4) (1 − f²)·Δ_k² ≥ 0
  have hB : ExpPos.geRat
      (CReal.mul (CReal.sub CReal.cone (CReal.mul (ceval (qFac k) a) (ceval (qFac k) a)))
        (CReal.mul (deltaC k a) (deltaC k a))) 0 := CReal.mul_nonneg hF hW
  -- (5) bracket ≥ 0  via bracket ≃ (MFPq) + ((1−f²)·Δ_k²)
  have hsum : ExpPos.geRat
      (CReal.add
        (CReal.sub (CReal.mul (deltaC (k + 1) a) (deltaC (k - 1) a))
          (CReal.mul (deltaC k a) (deltaC k a)))
        (CReal.mul (CReal.sub CReal.cone (CReal.mul (ceval (qFac k) a) (ceval (qFac k) a)))
          (CReal.mul (deltaC k a) (deltaC k a)))) 0 :=
    ExpPos.geRat_mono (SumOfSquares.geRat_add hMFPq hB)
      (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_add_zero_eqv 0)))
  -- bracket ≃ that sum (Equiv via approx + bracket_split)
  have hbracket_eq : CReal.Equiv
      (CReal.sub (CReal.mul (deltaC (k + 1) a) (deltaC (k - 1) a))
        (CReal.mul (CReal.mul (ceval (qFac k) a) (ceval (qFac k) a))
          (CReal.mul (deltaC k a) (deltaC k a))))
      (CReal.add
        (CReal.sub (CReal.mul (deltaC (k + 1) a) (deltaC (k - 1) a))
          (CReal.mul (deltaC k a) (deltaC k a)))
        (CReal.mul (CReal.sub CReal.cone (CReal.mul (ceval (qFac k) a) (ceval (qFac k) a)))
          (CReal.mul (deltaC k a) (deltaC k a)))) := by
    refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
    -- both sides reduce to `bracket_split` at the Q' values; cone.approx n = 1
    have hcone : CReal.cone.approx n = (1 : Q') := rfl
    show ((deltaC (k + 1) a).approx n * (deltaC (k - 1) a).approx n
        + -((ceval (qFac k) a).approx n * (ceval (qFac k) a).approx n
            * ((deltaC k a).approx n * (deltaC k a).approx n))).eqv
      (((deltaC (k + 1) a).approx n * (deltaC (k - 1) a).approx n
          + -((deltaC k a).approx n * (deltaC k a).approx n))
        + (CReal.cone.approx n
            + -((ceval (qFac k) a).approx n * (ceval (qFac k) a).approx n))
          * ((deltaC k a).approx n * (deltaC k a).approx n))
    rw [hcone]
    exact bracket_split ((deltaC (k + 1) a).approx n) ((deltaC (k - 1) a).approx n)
      ((ceval (qFac k) a).approx n * (ceval (qFac k) a).approx n)
      ((deltaC k a).approx n * (deltaC k a).approx n)
  have hbracket : ExpPos.geRat
      (CReal.sub (CReal.mul (deltaC (k + 1) a) (deltaC (k - 1) a))
        (CReal.mul (CReal.mul (ceval (qFac k) a) (ceval (qFac k) a))
          (CReal.mul (deltaC k a) (deltaC k a)))) 0 :=
    SU3CharFactor.geRat_of_equiv hbracket_eq hsum
  -- (6) bridge:  denom · T_k ≃ bracket   ⟹   geRat (denom · T_k) 0
  have hbridge := turan_delta_bridge k hk a
  have hdenomT : ExpPos.geRat
      (CReal.mul
        (CReal.mul
          (CReal.mul (ceval (qFac k) a) (ceval (qFac k) a))
          (CReal.mul
            (CReal.mul (ceval (SN k) a) (ceval (SN k) a))
            (CReal.mul (ceval (SN k) a) (ceval (SN k) a))))
        (ceval (turanPoly k) a)) 0 :=
    SU3CharFactor.geRat_of_equiv hbridge hbracket
  -- (7) commute to put T_k on the right unchanged, denom as the cancelled factor.
  -- hdenomT is geRat (denom · T_k) 0 ; rewrite as geRat (T_k · denom) 0
  have hcomm : CReal.Equiv
      (CReal.mul
        (CReal.mul
          (CReal.mul (ceval (qFac k) a) (ceval (qFac k) a))
          (CReal.mul
            (CReal.mul (ceval (SN k) a) (ceval (SN k) a))
            (CReal.mul (ceval (SN k) a) (ceval (SN k) a))))
        (ceval (turanPoly k) a))
      (CReal.mul (ceval (turanPoly k) a)
        (CReal.mul
          (CReal.mul (ceval (qFac k) a) (ceval (qFac k) a))
          (CReal.mul
            (CReal.mul (ceval (SN k) a) (ceval (SN k) a))
            (CReal.mul (ceval (SN k) a) (ceval (SN k) a))))) :=
    CRealAlg.cmul_comm _ _
  have hTdenom : ExpPos.geRat
      (CReal.mul (ceval (turanPoly k) a)
        (CReal.mul
          (CReal.mul (ceval (qFac k) a) (ceval (qFac k) a))
          (CReal.mul
            (CReal.mul (ceval (SN k) a) (ceval (SN k) a))
            (CReal.mul (ceval (SN k) a) (ceval (SN k) a))))) 0 :=
    SU3CharFactor.geRat_of_equiv (CReal.Equiv.symm hcomm) hdenomT
  -- (8) cancel the strictly-positive perfect-square denominator
  exact geRat_left_of_mul_posEv hTdenom (posEv_bridge_denom ha0 ha1 k hk1)

/-! ## §6. The capstone — all-order Gram PSD on `(0,1)`, conditional on the wall -/

/-- `PosEv a → geRat a 0` (the bridge to the nonnegativity vocabulary). -/
theorem geRat_zero_of_posEv' {a : CReal} (h : PosEv a) : ExpPos.geRat a 0 :=
  TuranPositivity.geRat_zero_of_posEv h

/-- `PosEv (ofQ' 1)`: the constant `1` is strictly positive. -/
theorem posEv_ofQ'_one : PosEv (CReal.ofQ' 1) := by
  refine posEv_of_eventually (ε := 1) (by decide) ⟨0, fun n _ => ?_⟩
  show (1 : Q') ≤ (CReal.ofQ' 1).approx n
  exact Q'.le_refl' 1

/-- **`P_2(a) > 0`** for `a ≥ 0`: `Pseq 2 = 1 :: tail` with `nonnegCoeffs tail`,
so `ceval (Pseq 2) a = 1 + a·(tail ≥ 0) ≥ 1 > 0`.  (The `k = 1` base of the
two-step induction, where the bridge `k ≥ 2` is unavailable.) -/
theorem posEv_Pseq_two {a : CReal} (ha : ExpPos.geRat a 0) :
    PosEv (ceval (Pseq 2) a) := by
  -- Pseq 2 = P2 = (1) :: [0,2,0,3] ;  ceval = add (ofQ' 1) (mul a (ceval tail a))
  have htail : ExpPos.geRat (ceval [(0 : Q'), Q'.ofNat 2, 0, Q'.ofNat 3] a) 0 :=
    geRat_ceval_of_nonnegCoeffs _ ha (by decide)
  have hmul : ExpPos.geRat (CReal.mul a (ceval [(0 : Q'), Q'.ofNat 2, 0, Q'.ofNat 3] a)) 0 :=
    CReal.mul_nonneg ha htail
  have hadd : PosEv (CReal.add (CReal.ofQ' (Q'.ofNat 1))
      (CReal.mul a (ceval [(0 : Q'), Q'.ofNat 2, 0, Q'.ofNat 3] a))) := by
    refine posEv_add_geRat ?_ hmul
    refine posEv_of_eventually (ε := 1) (by decide) ⟨0, fun n _ => ?_⟩
    show (1 : Q') ≤ (CReal.ofQ' (Q'.ofNat 1)).approx n
    exact Q'.le_refl' 1
  -- ceval (Pseq 2) a is definitionally this add
  exact hadd

/-- **`P_N(a) > 0` for all `N`, conditional on `MomentFunctionalPositive`**, on
`(0,1)`.  Two-step induction (base `P_0,P_1 > 0`; step the pointwise Turán
engine fed by the reduction `turan_pointwise_of_momentPositive`). -/
theorem Pseq_pos_of_momentPositive (hMFP : MomentFunctionalPositive)
    {a : CReal} (ha0 : PosEv a) (ha1 : PosEv (CReal.sub CReal.cone a)) :
    ∀ N : Nat, PosEv (ceval (Pseq N) a) := by
  have ha : ExpPos.geRat a 0 := geRat_zero_of_posEv' ha0
  have hpair : ∀ N : Nat, PosEv (ceval (Pseq N) a) ∧ PosEv (ceval (Pseq (N + 1)) a) := by
    intro N
    induction N with
    | zero =>
        exact ⟨TuranPositivity.posEv_Pseq_base a 0 (by omega),
          TuranPositivity.posEv_Pseq_base a 1 (by omega)⟩
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        -- need PosEv (P_{n+2}).  Apply turan_step_pointwise at k = n+1 (≥ 2 only if n ≥ 1);
        -- for n = 0 use the base case P_2 directly via the engine on k = 1?  k=1 < 2.
        -- Instead: handle n = 0 by the base, n ≥ 1 by the reduction (k = n+1 ≥ 2).
        match n, ih with
        | 0, _ =>
            -- P_2 base: the bridge needs `k ≥ 2`, unreachable at `k = 1`.  But `P_2` is a
            -- fixed nonneg-coefficient list with constant term `1`, so `P_2(a) > 0`
            -- directly (constant-term bound), independent of the wall.
            exact posEv_Pseq_two ha
        | (m + 1), ih =>
            -- k := m+2 ≥ 2.  (n+1)-1 = n = m+1 = k-1 ; k = m+2 ; k+1 = m+3 = n+2.
            have hTk : ExpPos.geRat (ceval (turanPoly (m + 2)) a) 0 :=
              turan_pointwise_of_momentPositive hMFP (m + 2) (by omega) ha0 ha1
            have hstep := turan_step_pointwise (m + 2) ha
              (by simpa using ih.1) ih.2 hTk
            simpa using hstep
  exact fun N => (hpair N).1

/-- **CAPSTONE.**  `MomentFunctionalPositive ⟹ Δ_N(a) ≥ 0` for every `N` and
every `a ∈ (0,1)` (`0 < a` / `a < 1` as `PosEv a` / `PosEv (cone − a)`),
where `Δ_N = deltaC N a = (ceval (SN N) a)²·(ceval (Pseq N) a)`.

So the ALL-ORDER heat-kernel Gram PSD on `(0,1)` is PROVED conditional on the
single named, canonical wall `MomentFunctionalPositive` (the moment-functional
log-convexity = the OS inner-product positivity), which subsumes and relocates
`TuranPositivity.UniformTuranNonneg`.  The per-step engine, the bridge, and the
reduction are all UNCONDITIONAL. -/
theorem delta_nonneg_all_of_momentPositive (hMFP : MomentFunctionalPositive)
    (N : Nat) {a : CReal} (ha0 : PosEv a) (ha1 : PosEv (CReal.sub CReal.cone a)) :
    ExpPos.geRat (deltaC N a) 0 := by
  have ha : ExpPos.geRat a 0 := geRat_zero_of_posEv' ha0
  have hSN2 : ExpPos.geRat (CReal.mul (ceval (SN N) a) (ceval (SN N) a)) 0 :=
    FavardUniform.geRat_SN_sq_nonneg_uniform N a
  have hPN : ExpPos.geRat (ceval (Pseq N) a) 0 :=
    geRat_zero_of_posEv' (Pseq_pos_of_momentPositive hMFP ha0 ha1 N)
  exact CReal.mul_nonneg hSN2 hPN

end YMGap.Continuum.TuranBridge

/-! ## Summary — PROVED vs NAMED-open

**PROVED here (axiom-clean; the bridge, engine, reduction and capstone are all
genuine theorems).**

  * `turan_step_pointwise` — the pointwise per-step engine (pointwise `T_k ≥ 0`,
    not `nonnegCoeffs`), `P_{k+1} > 0` from `P_{k−1}, P_k > 0`.

  * `turan_delta_bridge` — **THE NEW IDENTITY**, fully PROVED for all `k ≥ 2`
    from `SN_telescope_gen` + `sq_telescope` + `bridge_value` (ring algebra):
    `f²·S_k⁴·T_k ≃ Δ_{k+1}Δ_{k−1} − f²·Δ_k²`.

  * `turan_pointwise_of_momentPositive` — the REDUCTION: log-convexity
    (`MomentFunctionalPositive`) ⟹ pointwise `T_k(a) ≥ 0` on `(0,1)`, via the
    bridge, the bracket bound `≥ Δ_k²(1 − f²) ≥ 0`, and cancelling the
    strictly-positive perfect square `f²·S_k⁴` (`posEv_bridge_denom`).

  * `delta_nonneg_all_of_momentPositive` — the CAPSTONE: `MomentFunctionalPositive`
    ⟹ `Δ_N(a) ≥ 0` for all `N`, all `a ∈ (0,1)`.

  Supporting genuine theorems: `sq_telescope`, `bridge_value`,
  `eval_qZeros_append`, `eval_qFac_eqv`, `qpow_mono_base`, `eventually_in_unit`,
  `posEv_neg_qFac`, `posEv_ceval_ppow_sq`, `posEv_ceval_SNaux_sq`,
  `posEv_ceval_SN_sq`, `posEv_bridge_denom`, `geRat_left_of_mul_posEv`,
  `geRat_one_sub_qFac_sq`, `bracket_split`, `Pseq_pos_of_momentPositive`.

**NAMED-open — the canonical, cleaner wall.**

  `MomentFunctionalPositive : ∀ k a, 0<a → a<1 → Δ_k(a)² ≤ Δ_{k+1}(a)·Δ_{k−1}(a)`
  — the log-convexity of the q-Hankel determinants = the moment functional being
  a genuine inner product (the physical OS-positivity content).  This RELOCATES
  the opaque `TuranPositivity.UniformTuranNonneg` (an `N`-indexed `nonnegCoeffs`
  fact with no representation-theoretic meaning) to a motivated, canonical
  frontier (the inner-product positivity of the reconstructed Hilbert space).

  **Open question (follow-up).**  Whether `MomentFunctionalPositive` follows from
  the already-PROVED OS2 reflection positivity (the unconditional Gram positivity
  of the OS reconstruction): Hankel log-convexity is the determinant form of
  moment-matrix PSD, so a Sylvester / minor-of-a-PSD-matrix argument from the
  proved OS2 form positivity is the natural attack.  Not attempted here.

**Honest weakening.**  `Δ_N` is carried in its *factored* form
`deltaC N a = (ceval (SN N) a)²·(ceval (Pseq N) a)` (the same constructive-real
value as the expanded minor, the datum every per-order minor result already
consumes).  The base `k = 1` of the two-step induction (`P_2 > 0`) is discharged
directly from the fixed nonneg-coefficient list `P_2` (constant term `1`), since
the telescope/bridge requires `k ≥ 2`; this is unconditional and wall-free.
-/

#print axioms YMGap.Continuum.TuranBridge.turan_step_pointwise
#print axioms YMGap.Continuum.TuranBridge.turan_delta_bridge
#print axioms YMGap.Continuum.TuranBridge.turan_pointwise_of_momentPositive
#print axioms YMGap.Continuum.TuranBridge.delta_nonneg_all_of_momentPositive
