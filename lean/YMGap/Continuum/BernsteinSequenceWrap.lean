/-
Bernstein → `SpectralUnifCauchy` wrap: assembling the `Type`-level uniform
Cauchy datum the continuous functional calculus consumes from the proved
Bernstein uniform-approximation machinery.

`BernsteinUniformConvergence.lean` proved the `x`-explicit approximation bound
`|Bₙf − f| ≤ ω δ + (2M·recip δ²)·quadSum n x` (`bernstein_close_variance`,
conditional on the per-`(n,x)` variance identity).  What this module adds:

# GENUINELY PROVED here (`[propext]`/`[propext, Quot.sound]` only)

  * `half_pos`, `quarter_key`, `quarterBound` — the unconditional
    sum-of-squares completion `x(1−x) ≤ 1/4` on `[0,1]`, discharging the
    `QuarterBoundStmt` residual.  `quarter_key` factors it through the reflective
    `QPoly` identity prover: `x(1−x) + (x−½)² ≃ ¼` by `decide` on coefficient
    lists, transported to the closed forms by the `eval_*` homomorphisms.
  * `bernstein_uniform_bound` — THE ANALYTIC BRICK.  From
    `bernstein_close_variance` (given the per-`(n,x)` variance identity) and
    `quarterBound`, the fully `x`-uniform, `n`-only error
    `|Bₙf − f| ≤ ω δ + (2M·recip δ²·recip n)·¼`.
  * `eval_ppow`, `pow_eqv_congr`, `finPadd`, `eval_finPadd` — the missing `QPoly`
    utilities: closed-form power evaluation and the `padd`-fold with its
    `finSum` evaluation law.
  * `bmonoPoly`, `bernsteinPoly`, `eval_bmonoPoly`, `eval_bernsteinPoly` — the
    `QPoly` packaging of the Bernstein polynomial as a genuine `p : Nat → Poly`,
    with `QPoly.eval (bernsteinPoly F n) x ≃ bernstein F n x`.
  * `bernsteinSpectralCauchy` / `bernsteinPolySpectralCauchy` — the wrap: from an
    `ErrorModulus` (the `x`-uniform, antitone vanishing-error datum) and the
    `QPoly` packaging, a genuine `SpectralUnifCauchy (bernsteinPoly F) lam`.

# Honest named residuals (NOT closed here)

  * `QuadSumVarianceStmt0` — the sampled-second-moment identity
    `quadSum n x ≃ recip n · x(1−x)`, restricted to `0 < n` (the unrestricted
    statement is FALSE at `n = 0`: there `quadSum 0 x ≃ x·x` while the RHS
    `≃ x−x²`, since `ofNat 0 · recip(ofNat 0) = 0·1 = 0 ≠ 1`).  Reduces to the
    proved `bernsteinVariance` via the `(k/n−x)² = (k−nx)²·(recip n)²` rescaling.
  * `ErrorModulus F` — the `Type`-level `x`-uniform vanishing-error datum: an
    antitone stage function `stage : Q' → Nat` with a two-sided error bound past
    it.  Its content is exactly the diagonal `δ`/`natCeil` construction from
    `OmegaVanishing` + `bernstein_uniform_bound` — the sole remaining new
    utility (a monotone `natCeil` from the Archimedean principle).

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorryAx`, no custom `axiom`.
-/

import YMGap.Continuum.BernsteinUniformConvergence
import YMGap.Continuum.ContinuousTransferCalculus
import YMGap.Continuum.FavardUniform

namespace YMGap.Continuum.BernsteinSequenceWrap

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG
open YMGap.Continuum
open YMGap.Continuum.FavardUniform
open YMGap.Continuum.BernsteinVariance
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.ContinuousTransferCalculus

/-! ## Small `QPoly.eval` closed forms for the linear atoms -/

/-- `eval [c] x ≃ c`. -/
theorem eval_single (c x : Q') : (QPoly.eval [c] x).eqv c := by
  show (c + x * QPoly.eval ([] : QPoly.Poly) x).eqv c
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left c (x * QPoly.eval ([] : QPoly.Poly) x) 0 (QPoly.q_mul_zero x)) ?_
  exact QPoly.q_add_zero_eqv c

/-- `eval [0,1] x ≃ x`. -/
theorem eval01 (x : Q') : (QPoly.eval [(0 : Q'), 1] x).eqv x := by
  show ((0 : Q') + x * QPoly.eval [(1 : Q')] x).eqv x
  refine Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv (x * QPoly.eval [(1 : Q')] x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left x (QPoly.eval [(1 : Q')] x) 1 (eval_single 1 x)) ?_
  exact Q'.mul_one_eqv x

/-- `eval [1,-1] x ≃ 1 − x`. -/
theorem eval1m (x : Q') : (QPoly.eval [(1 : Q'), -1] x).eqv (1 - x) := by
  show ((1 : Q') + x * QPoly.eval [(-1 : Q')] x).eqv (1 - x)
  have hxm : (x * (-1 : Q')).eqv (-x) :=
    Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv x 1)
      (Q'.neg_eqv_congr (x * 1) x (Q'.mul_one_eqv x))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 (x * QPoly.eval [(-1 : Q')] x) (x * (-1 : Q'))
      (Q'.mul_eqv_congr_left x (QPoly.eval [(-1 : Q')] x) (-1) (eval_single (-1) x))) ?_
  exact Q'.add_eqv_congr_left 1 (x * (-1 : Q')) (-x) hxm

/-- `eval [-½, 1] x ≃ x − ½`. -/
theorem evalHalfLin (x : Q') :
    (QPoly.eval [(-HalfPow.half), 1] x).eqv (x - HalfPow.half) := by
  show ((-HalfPow.half) + x * QPoly.eval [(1 : Q')] x).eqv (x - HalfPow.half)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (-HalfPow.half) (x * QPoly.eval [(1 : Q')] x) x
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left x (QPoly.eval [(1 : Q')] x) 1 (eval_single 1 x))
        (Q'.mul_one_eqv x))) ?_
  exact Q'.add_comm_eqv (-HalfPow.half) x

/-! ## `¼ − x(1−x) = (x−½)²`: the sum-of-squares completion -/

/-- `x(1−x) + (x−½)² ≃ ¼` — the reflective-`QPoly` core.  The coefficient
identity is discharged by `decide`; the two `eval` sides are transported to the
closed forms by the homomorphism lemmas. -/
theorem quarter_key (x : Q') :
    (x * (1 - x) + (x - HalfPow.half) * (x - HalfPow.half)).eqv
      (Q'.recip (Q'.ofNat 4)) := by
  -- The two coefficient lists.
  let P : QPoly.Poly :=
    QPoly.padd (QPoly.pmul [(0 : Q'), 1] [(1 : Q'), -1])
      (QPoly.pmul [(-HalfPow.half), 1] [(-HalfPow.half), 1])
  let Q : QPoly.Poly := [Q'.recip (Q'.ofNat 4)]
  -- eval of the two `pmul` atoms.
  have hA : (QPoly.eval (QPoly.pmul [(0 : Q'), 1] [(1 : Q'), -1]) x).eqv (x * (1 - x)) :=
    Q'.eqv_trans _ _ _ (QPoly.eval_pmul [(0 : Q'), 1] [(1 : Q'), -1] x)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ x _ (eval01 x))
        (Q'.mul_eqv_congr_left x _ (1 - x) (eval1m x)))
  have hB : (QPoly.eval (QPoly.pmul [(-HalfPow.half), 1] [(-HalfPow.half), 1]) x).eqv
      ((x - HalfPow.half) * (x - HalfPow.half)) :=
    Q'.eqv_trans _ _ _ (QPoly.eval_pmul [(-HalfPow.half), 1] [(-HalfPow.half), 1] x)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ (x - HalfPow.half) _ (evalHalfLin x))
        (Q'.mul_eqv_congr_left (x - HalfPow.half) _ (x - HalfPow.half) (evalHalfLin x)))
  have hP : (QPoly.eval P x).eqv (x * (1 - x) + (x - HalfPow.half) * (x - HalfPow.half)) :=
    Q'.eqv_trans _ _ _
      (QPoly.eval_padd (QPoly.pmul [(0 : Q'), 1] [(1 : Q'), -1])
        (QPoly.pmul [(-HalfPow.half), 1] [(-HalfPow.half), 1]) x)
      (QPoly.q_add_congr hA hB)
  have hQ : (QPoly.eval Q x).eqv (Q'.recip (Q'.ofNat 4)) := eval_single (Q'.recip (Q'.ofNat 4)) x
  have hpe : (QPoly.eval P x).eqv (QPoly.eval Q x) := QPoly.poly_eqv P Q x (by decide)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hP) (Q'.eqv_trans _ _ _ hpe hQ)

/-- `0 < ½`. -/
theorem half_pos : (0 : Q') < HalfPow.half := by decide

/-- **`x(1−x) ≤ ¼` on `[0,1]`** (discharges `QuarterBoundStmt`). -/
theorem quarterBound (x : Q') (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) :
    x * (1 - x) ≤ Q'.recip (Q'.ofNat 4) := by
  have hnn : (0 : Q') ≤ (x - HalfPow.half) * (x - HalfPow.half) :=
    SumOfSquares.q_mul_self_nonneg (x - HalfPow.half)
  have hself : x * (1 - x) ≤ x * (1 - x) + (x - HalfPow.half) * (x - HalfPow.half) :=
    Q'.add_le_self_of_nonneg (x * (1 - x)) _ hnn
  exact Q'.le_trans' _ _ _ hself (Q'.le_of_eqv (quarter_key x))

/-! ## The analytic brick — `x`-uniform, `n`-only error -/

/-- **`x`-uniform Bernstein error.**  From `bernstein_close_variance` (given the
per-`(n,x)` variance identity `H`) and `quarterBound`,
`|Bₙf − f| ≤ ω δ + (2M·recip δ²·recip n)·¼`. -/
theorem bernstein_uniform_bound (F : CtsMod) (n : Nat) (x : Q')
    (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) (δ : Q') (hδ : (0 : Q') < δ)
    (H : (quadSum n x).eqv (Q'.recip (Q'.ofNat n) * (x * (1 - x)))) :
    Q'.abs (bernstein F n x - F.f x)
      ≤ F.ω δ
        + ((2 * F.bound) * Q'.recip (δ * δ) * Q'.recip (Q'.ofNat n))
            * Q'.recip (Q'.ofNat 4) := by
  have base := bernstein_close_variance F n x hx0 hx1 δ hδ H
  refine Q'.le_trans' _ _ _ base ?_
  refine Q'.add_le_add_left _ _ _ ?_
  have hC1 : (0 : Q') ≤ (2 * F.bound) * Q'.recip (δ * δ) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg 2 F.bound (by decide) (bound_nonneg F))
      (Q'.le_of_lt (Q'.recip_pos (δ * δ)))
  have hCn : (0 : Q') ≤ (2 * F.bound) * Q'.recip (δ * δ) * Q'.recip (Q'.ofNat n) :=
    Q'.mul_nonneg _ _ hC1 (Q'.le_of_lt (Q'.recip_pos (Q'.ofNat n)))
  have hassoc :
      ((2 * F.bound) * Q'.recip (δ * δ) * (Q'.recip (Q'.ofNat n) * (x * (1 - x)))).eqv
        (((2 * F.bound) * Q'.recip (δ * δ) * Q'.recip (Q'.ofNat n)) * (x * (1 - x))) :=
    Q'.eqv_symm
      (Q'.mul_assoc_eqv ((2 * F.bound) * Q'.recip (δ * δ)) (Q'.recip (Q'.ofNat n))
        (x * (1 - x)))
  have hbound :
      (((2 * F.bound) * Q'.recip (δ * δ) * Q'.recip (Q'.ofNat n)) * (x * (1 - x)))
        ≤ ((2 * F.bound) * Q'.recip (δ * δ) * Q'.recip (Q'.ofNat n))
            * Q'.recip (Q'.ofNat 4) :=
    Q'.mul_le_mul_of_nonneg_left (x * (1 - x)) (Q'.recip (Q'.ofNat 4)) _
      (quarterBound x hx0 hx1) hCn
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc) hbound

/-! ## Missing `QPoly` utilities -/

/-- Power congruence for `eqv`. -/
theorem pow_eqv_congr {a b : Q'} (h : a.eqv b) : ∀ m : Nat, (a ^ m).eqv (b ^ m)
  | 0 => Q'.eqv_refl 1
  | m + 1 => by
      show (a * a ^ m).eqv (b * b ^ m)
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a b (a ^ m) h)
        (Q'.mul_eqv_congr_left b (a ^ m) (b ^ m) (pow_eqv_congr h m))

/-- Closed-form `ppow` evaluation: `eval (ppow p m) x ≃ (eval p x)^m`. -/
theorem eval_ppow (p : QPoly.Poly) (x : Q') :
    ∀ m, (QPoly.eval (ppow p m) x).eqv ((QPoly.eval p x) ^ m)
  | 0 => eval_pone x
  | m + 1 =>
      Q'.eqv_trans _ _ _ (eval_ppow_succ p m x)
        (Q'.mul_eqv_congr_left (QPoly.eval p x) _ _ (eval_ppow p x m))

/-- The `padd`-fold `Σ'_{k<n} f k` of polynomials. -/
def finPadd (f : Nat → QPoly.Poly) : Nat → QPoly.Poly
  | 0 => []
  | (n + 1) => QPoly.padd (finPadd f n) (f n)

/-- `eval (finPadd f n) x ≃ Σ_{k<n} eval (f k) x`. -/
theorem eval_finPadd (f : Nat → QPoly.Poly) (x : Q') :
    ∀ n, (QPoly.eval (finPadd f n) x).eqv (finSum (fun k => QPoly.eval (f k) x) n)
  | 0 => Q'.eqv_refl 0
  | (n + 1) => by
      show (QPoly.eval (QPoly.padd (finPadd f n) (f n)) x).eqv
        (finSum (fun k => QPoly.eval (f k) x) n + QPoly.eval (f n) x)
      refine Q'.eqv_trans _ _ _ (QPoly.eval_padd (finPadd f n) (f n) x) ?_
      exact Q'.add_eqv_congr_right _ _ (QPoly.eval (f n) x) (eval_finPadd f x n)

/-! ## `QPoly` packaging of the Bernstein polynomial -/

/-- The Bernstein monomial `C(n,k)·xᵏ·(1−x)^{n−k}` as a `QPoly.Poly`. -/
def bmonoPoly (n k : Nat) : QPoly.Poly :=
  QPoly.pscale (Q'.ofNat (binom n k))
    (QPoly.pmul (ppow [(0 : Q'), 1] k) (ppow [(1 : Q'), -1] (n - k)))

/-- `eval (bmonoPoly n k) x ≃ bmono n x (1−x) k`. -/
theorem eval_bmonoPoly (n k : Nat) (x : Q') :
    (QPoly.eval (bmonoPoly n k) x).eqv (bmono n x (1 - x) k) := by
  have hx : (QPoly.eval (ppow [(0 : Q'), 1] k) x).eqv (x ^ k) :=
    Q'.eqv_trans _ _ _ (eval_ppow [(0 : Q'), 1] x k) (pow_eqv_congr (eval01 x) k)
  have hy : (QPoly.eval (ppow [(1 : Q'), -1] (n - k)) x).eqv ((1 - x) ^ (n - k)) :=
    Q'.eqv_trans _ _ _ (eval_ppow [(1 : Q'), -1] x (n - k)) (pow_eqv_congr (eval1m x) (n - k))
  have hmul :
      (QPoly.eval (QPoly.pmul (ppow [(0 : Q'), 1] k) (ppow [(1 : Q'), -1] (n - k))) x).eqv
        (x ^ k * (1 - x) ^ (n - k)) :=
    Q'.eqv_trans _ _ _
      (QPoly.eval_pmul (ppow [(0 : Q'), 1] k) (ppow [(1 : Q'), -1] (n - k)) x)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ (x ^ k) _ hx)
        (Q'.mul_eqv_congr_left (x ^ k) _ ((1 - x) ^ (n - k)) hy))
  show (QPoly.eval (bmonoPoly n k) x).eqv (bmono n x (1 - x) k)
  refine Q'.eqv_trans _ _ _
    (QPoly.eval_pscale (Q'.ofNat (binom n k))
      (QPoly.pmul (ppow [(0 : Q'), 1] k) (ppow [(1 : Q'), -1] (n - k))) x) ?_
  exact Q'.mul_eqv_congr_left (Q'.ofNat (binom n k)) _ (x ^ k * (1 - x) ^ (n - k)) hmul

/-- The Bernstein polynomial `Σ_k f(k/n)·bₙₖ` as a genuine `QPoly.Poly`. -/
def bernsteinPoly (F : CtsMod) (n : Nat) : QPoly.Poly :=
  finPadd (fun k => QPoly.pscale (F.f (smp n k)) (bmonoPoly n k)) (n + 1)

/-- `eval (bernsteinPoly F n) x ≃ bernstein F n x`. -/
theorem eval_bernsteinPoly (F : CtsMod) (n : Nat) (x : Q') :
    (QPoly.eval (bernsteinPoly F n) x).eqv (bernstein F n x) := by
  refine Q'.eqv_trans _ _ _
    (eval_finPadd (fun k => QPoly.pscale (F.f (smp n k)) (bmonoPoly n k)) x (n + 1)) ?_
  refine finSum_eqv_congr _ _ (fun k => ?_) (n + 1)
  refine Q'.eqv_trans _ _ _ (QPoly.eval_pscale (F.f (smp n k)) (bmonoPoly n k) x) ?_
  exact Q'.mul_eqv_congr_left (F.f (smp n k)) _ _ (eval_bmonoPoly n k x)

/-! ## The residual datum and the `SpectralUnifCauchy` wrap -/

/-- **Residual input (Type-level).**  The `x`-uniform vanishing-error datum: an
antitone stage function `stage : Q' → Nat` such that past `stage ε` the Bernstein
value approximates `F.f` two-sidedly within `ε` uniformly on `[0,1]`.  Its content
is the diagonal `δ`/`natCeil` construction from `OmegaVanishing` +
`bernstein_uniform_bound`. -/
structure ErrorModulus (F : CtsMod) where
  stage : Q' → Nat
  stage_antitone : ∀ a b : Q', (0 : Q') < a → a ≤ b → stage b ≤ stage a
  twobound : ∀ ε : Q', (0 : Q') < ε → ∀ n : Nat, stage ε ≤ n → ∀ x : Q',
    (0 : Q') ≤ x → x ≤ 1 →
      bernstein F n x ≤ F.f x + ε ∧ F.f x ≤ bernstein F n x + ε

/-- The genuine `QPoly` package of the Bernstein sequence. -/
def bernsteinQPolyPackage (F : CtsMod) :
    Σ' p : Nat → QPoly.Poly,
      (∀ n : Nat, ∀ x : Q', (QPoly.eval (p n) x).eqv (bernstein F n x)) :=
  ⟨bernsteinPoly F, fun n x => eval_bernsteinPoly F n x⟩

/-- **The wrap.**  From an `ErrorModulus` and the `QPoly` packaging, a genuine
`SpectralUnifCauchy (bernsteinPoly F) lam` for `lam ∈ [0,1]`. -/
def bernsteinPolySpectralCauchy (F : CtsMod) (EM : ErrorModulus F)
    (lam : Q') (h0 : (0 : Q') ≤ lam) (h1 : lam ≤ 1) :
    SpectralUnifCauchy (bernsteinPoly F) lam where
  Nmod := fun ε => EM.stage (HalfPow.half * ε)
  Mmono := fun ε δ hδpos hδε =>
    EM.stage_antitone (HalfPow.half * δ) (HalfPow.half * ε)
      (ExpNeg.half_mul_pos δ hδpos)
      (Q'.mul_le_mul_of_nonneg_left δ ε HalfPow.half hδε HalfPow.half_nonneg)
  cauchy := fun ε hε m n hm hn => by
    -- abbreviations
    have hpos : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
    have Am := EM.twobound (HalfPow.half * ε) hpos m hm lam h0 h1
    have Bn := EM.twobound (HalfPow.half * ε) hpos n hn lam h0 h1
    have eqm : (QPoly.eval (bernsteinPoly F m) lam).eqv (bernstein F m lam) :=
      eval_bernsteinPoly F m lam
    have eqn : (QPoly.eval (bernsteinPoly F n) lam).eqv (bernstein F n lam) :=
      eval_bernsteinPoly F n lam
    -- the two-halves collapse `(t + e) + e ≃ t + ε`
    have collapse : ∀ t : Q',
        ((t + HalfPow.half * ε) + HalfPow.half * ε).eqv (t + ε) := fun t =>
      Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv t (HalfPow.half * ε) (HalfPow.half * ε))
        (Q'.add_eqv_congr_left t (HalfPow.half * ε + HalfPow.half * ε) ε
          (ExpNeg.two_halves ε))
    refine ⟨?_, ?_⟩
    · -- `eval (p m) ≤ eval (p n) + ε`
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv eqm) ?_
      refine Q'.le_trans' _ _ _ Am.1 ?_
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add_right (F.f lam) (bernstein F n lam + HalfPow.half * ε)
          (HalfPow.half * ε) Bn.2) ?_
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (collapse (bernstein F n lam))) ?_
      exact Q'.le_of_eqv
        (Q'.add_eqv_congr_right (bernstein F n lam) (QPoly.eval (bernsteinPoly F n) lam) ε
          (Q'.eqv_symm eqn))
    · -- `eval (p n) ≤ eval (p m) + ε`
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv eqn) ?_
      refine Q'.le_trans' _ _ _ Bn.1 ?_
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add_right (F.f lam) (bernstein F m lam + HalfPow.half * ε)
          (HalfPow.half * ε) Am.2) ?_
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (collapse (bernstein F m lam))) ?_
      exact Q'.le_of_eqv
        (Q'.add_eqv_congr_right (bernstein F m lam) (QPoly.eval (bernsteinPoly F m) lam) ε
          (Q'.eqv_symm eqm))

/-! ## Honest named residuals -/

/-- **Residual (corrected).**  The sampled second moment equals `recip n · x(1−x)`,
restricted to `0 < n`.  The unrestricted `QuadSumVarianceStmt` is FALSE at `n = 0`.
Reduces to the proved `bernsteinVariance` via `(k/n−x)² = (k−nx)²·(recip n)²`. -/
def QuadSumVarianceStmt0 : Prop :=
  ∀ (n : Nat), 0 < n → ∀ (x : Q'), (0 : Q') ≤ x → x ≤ 1 →
    (quadSum n x).eqv (Q'.recip (Q'.ofNat n) * (x * (1 - x)))

end YMGap.Continuum.BernsteinSequenceWrap

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BernsteinSequenceWrap.quarter_key
#print axioms YMGap.Continuum.BernsteinSequenceWrap.quarterBound
#print axioms YMGap.Continuum.BernsteinSequenceWrap.bernstein_uniform_bound
#print axioms YMGap.Continuum.BernsteinSequenceWrap.eval_ppow
#print axioms YMGap.Continuum.BernsteinSequenceWrap.eval_finPadd
#print axioms YMGap.Continuum.BernsteinSequenceWrap.eval_bmonoPoly
#print axioms YMGap.Continuum.BernsteinSequenceWrap.eval_bernsteinPoly
#print axioms YMGap.Continuum.BernsteinSequenceWrap.bernsteinPolySpectralCauchy
