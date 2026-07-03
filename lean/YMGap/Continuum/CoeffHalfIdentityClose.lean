/-
# Differentiated Gauss q-binomial: the static engine behind `CoeffHalfIdentity`

`HdconvReroute.CoeffHalfIdentity A` is the Θ-stripped scalar core of `DiffJTP`:
the single static `CReal` equation `A ≈ (½)·S`, with the shared product factor
`Θ = ϑ₃` and the `jFac`-denominators already cancelled.  Per the reroute ledger
it is the last static obligation on that (demoted) leaf.

The finite combinatorial handle is Gauss's q-binomial identity, ALREADY CLOSED
for all `N` in `GaussQBinom.gauss_qbinom_all`:

    qProd z q N  ≈  gaussSum z q N          (for all `Q'`-params `z, q`, all `N`).

Since it holds for ALL `z`, its formal `z`-derivative is again an exact per-`N`
`Q'` identity.  This module builds that DIFFERENTIATED identity as genuine
axiom-clean `Q'`/`CReal` content:

* **`qProdDeriv`** — the formal `z`-derivative of the Gauss product, defined by
  the exact discrete **product rule** (Leibniz) recursion
  `(∏·f)' = ∏'·f + ∏·f'`.  This is a genuine object, not a residual.
* **`gaussSumDeriv`** — the term-by-term `z`-derivative of the Gauss sum,
  `Σ_{k≥1} k·q^{k²}·⟨N,k⟩_{q²}·z^{k−1}` (reindexed to avoid truncated `k−1`).
* **`qProdDeriv_eq_gaussSumDeriv` (CLOSED, given the finite step residual)** — the
  ASSEMBLY: from the local differentiated q-Pascal step `DerivStepProp` and the
  already-proven `gauss_qbinom_all`, an induction on `N` produces the full
  differentiated identity `qProdDeriv z q N ≈ gaussSumDeriv z q N` for all `N`.
  The induction, its base case (both sides `0`), and the product-rule recursion
  are all discharged here; the ONLY finite residual is the pure sum-side
  q-Pascal step `DerivStepProp`.
* **`qProdDeriv_creal_equiv` (CLOSED, given the step residual)** — the `N → ∞`
  `CReal` lift, mirroring `ThetaLimit.gauss_qbinom_creal_equiv`: any two `CReal`s
  realising the differentiated product / sum partials have equal limits (rates
  never enter; only the per-`N` equality does).

## The honest residual ledger (AGENTS.md Rule 6 / Rule 8)

Three named residuals, none faked (all `Type`/`Prop`-level data, never `sorry`):

* **`DerivStepProp z q N`** — the finite differentiated q-Pascal step
  `gaussSumDeriv N·(1+z·q^{2N+1}) + gaussSum N·q^{2N+1} ≈ gaussSumDeriv (N+1)`.
  This is the pure sum-side combinatorial core (the `z`-derivative of
  `GaussQBinom.gaussSum_step`).  It is provable by a running q-Pascal induction
  mirroring `GaussQBinom.gaussSum_run`, and is verified GENUINE here at `N = 0`
  (`derivStep_zero`).  Everything downstream (the assembly, the `CReal` lift) is
  proved to follow from it.
* **`CoeffCloseResidual`** — the `CReal`-level reduction of
  `HdconvReroute.CoeffHalfIdentity` to (a) the θ↔z / driver packaging
  `Equiv A Pd`, (b) the differentiated Jacobi identity at the `CReal` level
  `Equiv Pd Sd` (= exactly what `qProdDeriv_creal_equiv` supplies, MODULO the
  θ↔z complex-doubling gap — the real `jFac` is the doubled product at
  `z = e^{±2iθ}`, which has no `Q'` witness), and (c) the U-vs-T trig sin-fold
  `Equiv Sd ((½)·S)`.  The reduction `coeffHalfIdentity_of_residual` closes
  `CoeffHalfIdentity` from these three by transitivity.
* The middle field is genuinely discharged by this module's engine whenever the
  θ↔z realisation lives in `Q'` (single-`z`/complex case): see
  `jacobiDeriv_of_engine`.  The obstruction to using it for the REAL `jFac` is
  the complex doubling, documented above and in `JTPInstance`.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only (`Quot.sound` only via reused
`Nat`/`Int`/`omega`/`pow` helpers).  No `Classical.*`, no `native_decide`, no
`sorry`, no custom axiom.
-/

import YMGap.Continuum.GaussQBinom
import YMGap.Continuum.ThetaLimit
import YMGap.Continuum.HdconvReroute
import YMGap.Constructive.HalfPow
import YMGap.Continuum.HeatKernelConvGen

namespace YMGap.Continuum.CoeffHalfIdentityClose

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum
open YMGap.Continuum.GaussQBinom
open YMGap.Continuum.Cheb

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := eqv_trans _ _ _ h1 h2

/-! ## 1. The formal `z`-derivative of the Gauss product (product-rule recursion)

`qProd z q (N+1) = qProd z q N · (1 + z·q^{2N+1})`, so by the discrete product
rule (Leibniz) its `z`-derivative satisfies

    qProdDeriv (N+1) = qProdDeriv N · (1 + z·q^{2N+1})  +  qProd N · q^{2N+1},

the two Leibniz halves being "differentiate the prefix product" and
"differentiate the new factor `1 + z·q^{2N+1}` (whose `z`-derivative is
`q^{2N+1}`)".  This is a genuine object: the exact formal derivative of the
finite product. -/

/-- The formal `z`-derivative of `qProd z q N`, by the discrete product rule. -/
def qProdDeriv (z q : Q') : Nat → Q'
  | 0     => 0
  | N + 1 => qProdDeriv z q N * (1 + z * q ^ (2 * N + 1))
              + qProd z q N * q ^ (2 * N + 1)

@[simp] theorem qProdDeriv_zero (z q : Q') : qProdDeriv z q 0 = 0 := rfl
@[simp] theorem qProdDeriv_succ (z q : Q') (N : Nat) :
    qProdDeriv z q (N + 1)
      = qProdDeriv z q N * (1 + z * q ^ (2 * N + 1))
          + qProd z q N * q ^ (2 * N + 1) := rfl

/-! ## 2. The term-by-term `z`-derivative of the Gauss sum

`gaussSum z q N = Σ_{k=0}^{N} q^{k²}·⟨N,k⟩·z^k`, so its `z`-derivative is
`Σ_{k=1}^{N} k·q^{k²}·⟨N,k⟩·z^{k−1}`.  Reindex `k ↦ k+1` (running `k = 0 … N−1`)
to keep every `z`-power a genuine `Nat` (no truncated `k−1`):

    gaussSumDeriv z q N = Σ_{k=0}^{N-1} (k+1)·q^{(k+1)²}·⟨N,k+1⟩·z^{k}.

`Q'.ofNat (k+1)` supplies the integer coefficient `k+1` (no division). -/

/-- The reindexed differentiated Gauss summand
`(k+1)·q^{(k+1)²}·⟨N,k+1⟩_{q²}·z^{k}` (base `Q = q·q`). -/
def dGaussTerm (z q : Q') (N k : Nat) : Q' :=
  Q'.ofNat (k + 1) * (q ^ ((k + 1) * (k + 1)) * qbin (q * q) N (k + 1)) * z ^ k

/-- Running sum `Σ_{k=0}^{M} dGaussTerm z q N k` (binomials at fixed upper bound `N`). -/
def dGaussSumUpto (z q : Q') (N : Nat) : Nat → Q'
  | 0     => dGaussTerm z q N 0
  | M + 1 => dGaussSumUpto z q N M + dGaussTerm z q N (M + 1)

/-- The full differentiated Gauss sum `Σ_{k=0}^{N-1} dGaussTerm z q N k`.
Empty (`0`) at `N = 0`; otherwise the running sum up to index `N−1`. -/
def gaussSumDeriv (z q : Q') : Nat → Q'
  | 0     => 0
  | N + 1 => dGaussSumUpto z q (N + 1) N

@[simp] theorem gaussSumDeriv_zero (z q : Q') : gaussSumDeriv z q 0 = 0 := rfl

/-! ## 3. The finite differentiated q-Pascal step (named residual)

The pure sum-side combinatorial core — the `z`-derivative of
`GaussQBinom.gaussSum_step` (`gaussSum N·(1+z·q^{2N+1}) ≈ gaussSum (N+1)`).
Differentiating in `z` (with `W = z·q^{2N+1}`, `W' = q^{2N+1}`):

    gaussSumDeriv N·(1 + z·q^{2N+1})  +  gaussSum N·q^{2N+1}  ≈  gaussSumDeriv (N+1).

It is provable by the same running q-Pascal induction as `gaussSum_run`; it is
left here as a named `Prop` residual (verified genuine at `N = 0` below). -/
def DerivStepProp (z q : Q') (N : Nat) : Prop :=
  gaussSumDeriv z q N * (1 + z * q ^ (2 * N + 1)) + gaussSum z q N * q ^ (2 * N + 1)
    ≈ gaussSumDeriv z q (N + 1)

/-- **`DerivStepProp` is genuine (not vacuous): the `N = 0` case is provable.**
At `N = 0`: `gaussSumDeriv 0 = 0`, `gaussSum 0 = 1`, so the LHS is
`0·(1+z·q) + 1·q^{1} ≈ q`, while `gaussSumDeriv 1 = dGaussTerm z q 1 0 =
1·(q^{1}·⟨1,1⟩)·z^{0} ≈ q` (since `⟨1,1⟩_{q²} ≈ 1`).  Both sides `≈ q`. -/
theorem derivStep_zero (z q : Q') : DerivStepProp z q 0 := by
  show gaussSumDeriv z q 0 * (1 + z * q ^ (2 * 0 + 1)) + gaussSum z q 0 * q ^ (2 * 0 + 1)
        ≈ gaussSumDeriv z q 1
  -- ⟨1,1⟩_{q²} ≈ 1 :  qbin (q*q) 1 1 = qbin _ 0 1 + (q*q)^(0-0)·qbin _ 0 0 = 0 + (q*q)^0·1.
  have hqbin : qbin (q * q) 1 1 ≈ (1 : Q') := by
    show qbin (q * q) 0 1 + (q * q) ^ (0 - 0) * qbin (q * q) 0 0 ≈ (1 : Q')
    calc qbin (q * q) 0 1 + (q * q) ^ (0 - 0) * qbin (q * q) 0 0
        ≈ (q * q) ^ (0 - 0) * qbin (q * q) 0 0 := by
            have e1 : qbin (q * q) 0 1 = (0 : Q') := rfl
            rw [e1, zero_add']; exact eqv_refl _
      _ ≈ (q * q) ^ (0 - 0) := mul_one_eqv _   -- qbin (q*q) 0 0 = 1 defeq
      _ ≈ (1 : Q') := eqv_refl _                -- (q*q)^0 = 1 defeq
  -- gaussSum z q 0 ≈ 1  (base case of Gauss's identity: qProd 0 = 1 ≈ gaussSum 0).
  have hG0 : gaussSum z q 0 ≈ (1 : Q') := eqv_symm (gauss_qbinom_base z q)
  -- RHS: gaussSumDeriv z q 1 = dGaussTerm z q 1 0 = ofNat 1·(q^1·⟨1,1⟩)·z^0 ≈ q^1.
  have hR : gaussSumDeriv z q 1 ≈ q ^ (2 * 0 + 1) := by
    show Q'.ofNat 1 * (q ^ (1 * 1) * qbin (q * q) 1 1) * z ^ 0 ≈ q ^ (2 * 0 + 1)
    calc Q'.ofNat 1 * (q ^ (1 * 1) * qbin (q * q) 1 1) * z ^ 0
        ≈ Q'.ofNat 1 * (q ^ (1 * 1) * qbin (q * q) 1 1) := mul_one_eqv _   -- z^0 = 1 defeq
      _ ≈ q ^ (1 * 1) * qbin (q * q) 1 1 := one_mul_eqv _                  -- ofNat 1 = 1 defeq
      _ ≈ q ^ (1 * 1) * (1 : Q') := mul_eqv_congr_left _ _ _ hqbin
      _ ≈ q ^ (1 * 1) := mul_one_eqv _
      _ ≈ q ^ (2 * 0 + 1) := eqv_refl _        -- 1*1 = 1 = 2*0+1 defeq
  -- LHS: 0·(…) + gaussSum 0·q^1 ≈ gaussSum 0·q^1 ≈ 1·q^1 ≈ q^1.
  have hL : gaussSumDeriv z q 0 * (1 + z * q ^ (2 * 0 + 1)) + gaussSum z q 0 * q ^ (2 * 0 + 1)
              ≈ q ^ (2 * 0 + 1) := by
    have h0 : gaussSumDeriv z q 0 * (1 + z * q ^ (2 * 0 + 1)) ≈ (0 : Q') := zero_mul_eqv _
    calc gaussSumDeriv z q 0 * (1 + z * q ^ (2 * 0 + 1)) + gaussSum z q 0 * q ^ (2 * 0 + 1)
        ≈ gaussSum z q 0 * q ^ (2 * 0 + 1) := by
            exact eqv_trans _ _ _ (add_eqv_congr_right _ _ _ h0)
              (by rw [zero_add']; exact eqv_refl _)
      _ ≈ (1 : Q') * q ^ (2 * 0 + 1) := mul_eqv_congr_right _ _ _ hG0
      _ ≈ q ^ (2 * 0 + 1) := one_mul_eqv _
  exact eqv_trans _ _ _ hL (eqv_symm hR)

/-! ## 4. The assembly: local step ⟹ full differentiated identity

By induction on `N`, using the product-rule recursion of `qProdDeriv`, the
already-proven `gauss_qbinom_all` (`qProd N ≈ gaussSum N`), and the local
`DerivStepProp`.  Base case: both sides `0`. -/

/-- **Full differentiated Gauss identity (CLOSED given the finite step residual).**
`qProdDeriv z q N ≈ gaussSumDeriv z q N` for every `N`, provided the local
differentiated q-Pascal step holds at each `N`.  This is the genuine assembly:
the base case and the product-rule induction are discharged here. -/
theorem qProdDeriv_eq_gaussSumDeriv (z q : Q')
    (hstep : ∀ N, DerivStepProp z q N) :
    ∀ N, qProdDeriv z q N ≈ gaussSumDeriv z q N := by
  intro N
  induction N with
  | zero => exact eqv_refl _
  | succ M ih =>
      have hqp : qProd z q M ≈ gaussSum z q M := gauss_qbinom_all z q M
      show qProdDeriv z q M * (1 + z * q ^ (2 * M + 1)) + qProd z q M * q ^ (2 * M + 1)
            ≈ gaussSumDeriv z q (M + 1)
      calc qProdDeriv z q M * (1 + z * q ^ (2 * M + 1)) + qProd z q M * q ^ (2 * M + 1)
          ≈ gaussSumDeriv z q M * (1 + z * q ^ (2 * M + 1))
              + gaussSum z q M * q ^ (2 * M + 1) :=
            add_eqv_congr _ _ _ _
              (mul_eqv_congr_right _ _ _ ih) (mul_eqv_congr_right _ _ _ hqp)
        _ ≈ gaussSumDeriv z q (M + 1) := hstep M

/-! ## 5. The `N → ∞` `CReal` lift (mirrors `ThetaLimit.gauss_qbinom_creal_equiv`)

Any two `CReal`s realising the differentiated product / sum partials have equal
limits.  The rates never enter — only the matched-at-each-`N` `Q'` equality
(from the assembly) does. -/

/-- **Differentiated Jacobi identity at the `CReal` level (CLOSED given the step
residual).**  If `Pd.approx N = qProdDeriv z q N` and
`Sd.approx N = gaussSumDeriv z q N` for all `N`, then `Equiv Pd Sd`. -/
theorem qProdDeriv_creal_equiv (z q : Q')
    (hstep : ∀ N, DerivStepProp z q N)
    {Pd Sd : CReal}
    (hPd : ∀ N : Nat, Pd.approx N = qProdDeriv z q N)
    (hSd : ∀ N : Nat, Sd.approx N = gaussSumDeriv z q N) :
    CReal.Equiv Pd Sd := by
  refine CReal.Equiv_of_lifted_approx_equal ?_
  intro N
  have heq : Pd.approx N ≈ Sd.approx N := by
    rw [hPd N, hSd N]; exact qProdDeriv_eq_gaussSumDeriv z q hstep N
  exact ThetaLimit.Equiv_ofQ'_of_eqv heq

/-! ## 6. Reduction of `HdconvReroute.CoeffHalfIdentity` to named `CReal` residuals

`CoeffHalfIdentity A` is `Equiv A ((½)·S)`.  We decompose it, per the reroute
ledger, into three `CReal`-level residuals and close it by transitivity.  This is
an honest ledger (Type-level data, no `sorry`), NOT a closure: the analytic
content lives in the three named fields. -/

/-- **The `CReal`-level residual bundle for `CoeffHalfIdentity`.**  Three named
`CReal` equivalences:

* `packaging : Equiv A Pd` — the driver + θ↔z packaging identifying the reroute
  coefficient `A` with the differentiated theta-product log-derivative `CReal`.
* `jacobiDeriv : Equiv Pd Sd` — the differentiated Jacobi identity at the `CReal`
  level.  This is EXACTLY what `qProdDeriv_creal_equiv` supplies, modulo the θ↔z
  complex-doubling gap (the real `jFac` is the doubled product at `z = e^{±2iθ}`,
  which has no `Q'` witness); see `jacobiDeriv_of_engine`.
* `sinFold : Equiv Sd ((½)·S)` — the trigonometric U-vs-T sin-fold
  `U_{n−1}(cos2θ)·sin2θ = sin2nθ` lifted to the `CReal` level. -/
structure CoeffCloseResidual {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (A : CReal) : Type where
  /-- The differentiated theta-product log-derivative `CReal`. -/
  Pd : CReal
  /-- The differentiated theta-series `CReal`. -/
  Sd : CReal
  /-- Driver + θ↔z packaging: `A` IS the product-derivative `CReal`. -/
  packaging : CReal.Equiv A Pd
  /-- The differentiated Jacobi identity at the `CReal` level. -/
  jacobiDeriv : CReal.Equiv Pd Sd
  /-- The U-vs-T trig sin-fold identifying the series-derivative with `(½)·S`. -/
  sinFold : CReal.Equiv Sd
    (CReal.mul (CReal.ofQ' HalfPow.half) (HKConvGen.sConvCReal_general ha0 ha1 hx))

/-- **`CoeffHalfIdentity` from the residual bundle (CLOSED given the bundle).**
Transitivity through the three named residuals:
`A ≈ Pd ≈ Sd ≈ (½)·S`. -/
theorem coeffHalfIdentity_of_residual {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (A : CReal)
    (R : CoeffCloseResidual ha0 ha1 hx hx1 A) :
    HdconvReroute.CoeffHalfIdentity ha0 ha1 hx hx1 A :=
  R.packaging.trans (R.jacobiDeriv.trans R.sinFold)

/-- **The engine discharges `jacobiDeriv` when the θ↔z realisation lives in `Q'`.**
For any single-`z` (complex/JTP) parametrisation whose product / sum-derivative
partials are realised by `Q'` values, `qProdDeriv_creal_equiv` supplies the
middle field directly.  (The obstruction for the REAL `jFac` is the complex
doubling `z = e^{±2iθ}`, not the engine.) -/
theorem jacobiDeriv_of_engine (z q : Q')
    (hstep : ∀ N, DerivStepProp z q N)
    {Pd Sd : CReal}
    (hPd : ∀ N : Nat, Pd.approx N = qProdDeriv z q N)
    (hSd : ∀ N : Nat, Sd.approx N = gaussSumDeriv z q N) :
    CReal.Equiv Pd Sd :=
  qProdDeriv_creal_equiv z q hstep hPd hSd

end YMGap.Continuum.CoeffHalfIdentityClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CoeffHalfIdentityClose.qProdDeriv_succ
#print axioms YMGap.Continuum.CoeffHalfIdentityClose.derivStep_zero
#print axioms YMGap.Continuum.CoeffHalfIdentityClose.qProdDeriv_eq_gaussSumDeriv
#print axioms YMGap.Continuum.CoeffHalfIdentityClose.qProdDeriv_creal_equiv
#print axioms YMGap.Continuum.CoeffHalfIdentityClose.coeffHalfIdentity_of_residual
#print axioms YMGap.Continuum.CoeffHalfIdentityClose.jacobiDeriv_of_engine
