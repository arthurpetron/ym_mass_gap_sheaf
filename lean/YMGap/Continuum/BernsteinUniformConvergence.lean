/-
Bernstein uniform convergence — the constructive Chebyshev/quadratic-majorant
estimate that closes the `BernsteinUniform` residual left open in
`BernsteinVarianceClose.lean`.

The proved variance identity `Σ (k − n x)²·bₙₖ ≃ n·x(1−x)` bounds the second
moment; what remained was the *pointwise* comparison turning a continuous
modulus into an `x`-uniform approximation error.  This module supplies that
comparison over `Q'`, entirely below `CReal`:

# What is GENUINELY PROVED here (no residual, `[propext]`/`[propext,Quot.sound]`)

  * `term_majorant` — **THE CRUX.**  For a continuous datum `F` with modulus `ω`
    and bound `M = ‖f‖`, the decidable near/far dichotomy on `|a − x| ≤ δ` gives
        `|f a − f x| ≤ ω δ + 2M·(a−x)²·recip(δ²)`
    uniformly in `a, x` — the Chebyshev quadratic majorant (no `Classical`, the
    split is `by_cases` on `DecidableRel Q'.le`).
  * `abs_finSum_le` — the finite-sum triangle inequality (`abs_add_le'` induction).
  * `bmono_nonneg` — Bernstein weights are `≥ 0` on `[0,1]`.
  * `bernstein_sub_self` — centering the Bernstein sum via `partition_of_unity`.
  * `bernstein_close_termwise` — termwise majorant of the centered sum.
  * `majorant_split` — collapsing the majorant sum through `partition_of_unity`
    into `ω δ + (2M·recip δ²)·quadSum`, where `quadSum` is the sampled second
    moment `Σ (k/n − x)²·bₙₖ`.
  * `bernstein_close` — the assembled, `x`-EXPLICIT approximation bound
        `|Bₙf − f| ≤ ω δ + (2M·recip δ²)·quadSum n x`.
  * `bernstein_close_variance` — the clean form obtained once the sampled second
    moment is replaced by its closed value `recip n · x(1−x)` (the named residual).

# Honest named residuals (NOT closed here)

  * `QuadSumVarianceStmt` — `quadSum n x ≃ recip n · x(1−x)`; reduces to the
    proved `bernsteinVariance` via the `(k/n−x)² = (k−nx)²·(recip n)²` rescaling
    (recip-multiplicativity algebra).
  * `QuarterBoundStmt` — `x(1−x) ≤ 1/4` (constructive sum-of-squares completion),
    the last step to a fully `x`-uniform, `n`-only error `ω δ + M·recip(2 n δ²)`.
  * `OmegaVanishing` — the single genuinely-new *input* for the uniform-Cauchy
    wrap: a Type-level vanishing modulus for `ω` at `0`.  Assembling the
    `SpectralUnifCauchy` datum the continuous functional calculus consumes needs,
    beyond this, a diagonal `δₙ` with `n·δₙ² → ∞` and the `QPoly` packaging of
    `Bₙ`; that outer wrap is the remaining wall.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorryAx`, no custom `axiom`.
-/

import YMGap.Continuum.BernsteinVarianceClose
import YMGap.Constructive.Sqrt
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealExp
import YMGap.Constructive.ExpNeg
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.BernsteinUniformConvergence

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG
open YMGap.Continuum.BernsteinVariance
open YMGap.Continuum.BernsteinVarianceClose
open YMGap.Continuum.BinomialTheorem

/-! ## Small `Q'` glue not already in scope -/

/-- `|q| = q` when `0 ≤ q` (defeq unfolding of the `if`). -/
theorem abs_of_nonneg {q : Q'} (h : (0 : Q') ≤ q) : Q'.abs q = q := by
  unfold Q'.abs; rw [if_pos h]

/-- `¬ (a ≤ b) → b ≤ a` (totality of the decidable `Q'` order, no `Classical`). -/
theorem q_le_of_not_le {a b : Q'} (h : ¬ a ≤ b) : b ≤ a := by
  show b.num * (a.den : Int) ≤ a.num * (b.den : Int)
  have hnot : ¬ (a.num * (b.den : Int) ≤ b.num * (a.den : Int)) := h
  exact Int.le_of_lt (Int.not_le.mp hnot)

/-- `q^n ≥ 0` for `q ≥ 0` (local induction; `q^0 = 1`, `q^(n+1) = q·q^n`). -/
theorem powNonneg (q : Q') (h : (0 : Q') ≤ q) : ∀ n : Nat, (0 : Q') ≤ q ^ n
  | 0 => by show (0 : Q') ≤ (1 : Q'); decide
  | n + 1 => Q'.mul_nonneg q (q ^ n) h (powNonneg q h n)

/-- `0 ≤ 1 − x` from `x ≤ 1`. -/
theorem one_sub_nonneg {x : Q'} (h : x ≤ 1) : (0 : Q') ≤ 1 - x := by
  show (0 : Q') ≤ 1 + (-x)
  have h1 : x + (-x) ≤ 1 + (-x) := Q'.add_le_add_right x 1 (-x) h
  have h2 : ((x : Q') + (-x)).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv x (-x)) (Q'.neg_add_self_eqv x)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv h2) h1

/-- `2·b ≃ b + b`. -/
theorem two_mul_eqv (b : Q') : ((2 : Q') * b).eqv (b + b) := by
  have h1 : ((2 : Q') * b).eqv (((1 : Q') + 1) * b) :=
    Q'.mul_eqv_congr_right 2 (1 + 1) b (by decide)
  have h2 : (((1 : Q') + 1) * b).eqv ((1 : Q') * b + 1 * b) := Q'.add_mul_eqv 1 1 b
  have h3 : ((1 : Q') * b + 1 * b).eqv (b + b) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ ((1 : Q') * b) (Q'.one_mul_eqv b))
      (Q'.add_eqv_congr_left b ((1 : Q') * b) b (Q'.one_mul_eqv b))
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h2 h3)

/-- `|t|·|t| ≃ t·t`. -/
theorem abs_sq (t : Q') : (Q'.abs t * Q'.abs t).eqv (t * t) := by
  unfold Q'.abs
  by_cases h : (0 : Q') ≤ t
  · rw [if_pos h]; exact Q'.eqv_refl _
  · rw [if_neg h]; exact neg_mul_neg_eqv t t

/-- Reassociation `((A·B)·C)·D ≃ (A·C)·(B·D)`. -/
theorem rearrange4 (A B C D : Q') :
    (((A * B) * C) * D).eqv ((A * C) * (B * D)) := by
  have s1 : (((A * B) * C) * D).eqv ((A * (B * C)) * D) :=
    Q'.mul_eqv_congr_right _ _ D (Q'.mul_assoc_eqv A B C)
  have s2 : ((A * (B * C)) * D).eqv ((A * (C * B)) * D) :=
    Q'.mul_eqv_congr_right _ _ D (Q'.mul_eqv_congr_left A (B * C) (C * B) (Q'.mul_comm_eqv B C))
  have s3 : ((A * (C * B)) * D).eqv (((A * C) * B) * D) :=
    Q'.mul_eqv_congr_right _ _ D (Q'.eqv_symm (Q'.mul_assoc_eqv A C B))
  have s4 : (((A * C) * B) * D).eqv ((A * C) * (B * D)) :=
    Q'.mul_assoc_eqv (A * C) B D
  exact Q'.eqv_trans _ _ _ s1 (Q'.eqv_trans _ _ _ s2 (Q'.eqv_trans _ _ _ s3 s4))

/-! ## The continuous datum -/

/-- A continuous function on `[0,1]` presented constructively: a value map `f`,
a uniform bound `‖f‖ = bound`, and a modulus of continuity `ω` *at the
threshold* `δ` (the exact strength the Bernstein estimate consumes). -/
structure CtsMod where
  f     : Q' → Q'
  bound : Q'
  ω     : Q' → Q'
  f_le  : ∀ t, Q'.abs (f t) ≤ bound
  ω_nn  : ∀ δ, (0 : Q') ≤ ω δ
  mod   : ∀ s t δ, Q'.abs (s - t) ≤ δ → Q'.abs (f s - f t) ≤ ω δ

/-- `‖f‖ ≥ 0`. -/
theorem bound_nonneg (F : CtsMod) : (0 : Q') ≤ F.bound :=
  Q'.le_trans' _ _ _ (Q'.abs_nonneg (F.f 0)) (F.f_le 0)

/-! ## The crux: the quadratic (Chebyshev) majorant -/

/-- **THE CRUX.**  Decidable near/far dichotomy on `|a − x| ≤ δ`:

* near: `|f a − f x| ≤ ω δ` and the quadratic remainder is `≥ 0`;
* far (`δ < |a − x|`): `(a−x)²·recip(δ²) ≥ 1`, so
  `2M·(a−x)²·recip(δ²) ≥ 2M ≥ |f a| + |f x| ≥ |f a − f x|`. -/
theorem term_majorant (F : CtsMod) (δ : Q') (hδ : (0 : Q') < δ) (a x : Q') :
    Q'.abs (F.f a - F.f x)
      ≤ F.ω δ + (2 * F.bound) * ((a - x) * (a - x)) * Q'.recip (δ * δ) := by
  have hMnn : (0 : Q') ≤ F.bound := bound_nonneg F
  have h2M : (0 : Q') ≤ 2 * F.bound := Q'.mul_nonneg 2 F.bound (by decide) hMnn
  have hsq : (0 : Q') ≤ (a - x) * (a - x) := SumOfSquares.q_mul_self_nonneg (a - x)
  have hδ2 : (0 : Q') < δ * δ := Q'.mul_pos hδ hδ
  have hR : (0 : Q') ≤ Q'.recip (δ * δ) := Q'.le_of_lt (Q'.recip_pos (δ * δ))
  have hquad : (0 : Q') ≤ (2 * F.bound) * ((a - x) * (a - x)) * Q'.recip (δ * δ) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ h2M hsq) hR
  by_cases hcase : Q'.abs (a - x) ≤ δ
  · -- near
    exact Q'.le_trans' _ _ _ (F.mod a x δ hcase)
      (Q'.add_le_self_of_nonneg (F.ω δ) _ hquad)
  · -- far
    have hle : δ ≤ Q'.abs (a - x) := q_le_of_not_le hcase
    have habsnn : (0 : Q') ≤ Q'.abs (a - x) := Q'.abs_nonneg _
    have hδδ_le : δ * δ ≤ Q'.abs (a - x) * Q'.abs (a - x) :=
      Q'.mul_le_mul_of_nonneg hle hle habsnn (Q'.le_of_lt hδ)
    have hδδ_le2 : δ * δ ≤ (a - x) * (a - x) :=
      Q'.le_trans' _ _ _ hδδ_le (Q'.le_of_eqv (abs_sq (a - x)))
    have hstep : δ * δ * Q'.recip (δ * δ) ≤ ((a - x) * (a - x)) * Q'.recip (δ * δ) :=
      Q'.mul_le_mul_of_nonneg_right (δ * δ) ((a - x) * (a - x)) (Q'.recip (δ * δ)) hδδ_le2 hR
    have h1le : (1 : Q') ≤ ((a - x) * (a - x)) * Q'.recip (δ * δ) :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_recip_eqv (δ * δ) hδ2)) hstep
    have h2Mle : (2 * F.bound) * 1
        ≤ (2 * F.bound) * (((a - x) * (a - x)) * Q'.recip (δ * δ)) :=
      Q'.mul_le_mul_of_nonneg_left 1 (((a - x) * (a - x)) * Q'.recip (δ * δ)) (2 * F.bound) h1le h2M
    have h2Mle' : (2 * F.bound)
        ≤ ((2 * F.bound) * ((a - x) * (a - x))) * Q'.recip (δ * δ) :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv (2 * F.bound)))
        (Q'.le_trans' _ _ _ h2Mle
          (Q'.le_of_eqv (Q'.eqv_symm
            (Q'.mul_assoc_eqv (2 * F.bound) ((a - x) * (a - x)) (Q'.recip (δ * δ))))))
    -- triangle: |f a − f x| ≤ |f a| + |f x| ≤ 2M
    have htri : Q'.abs (F.f a - F.f x) ≤ Q'.abs (F.f a) + Q'.abs (F.f x) := by
      have hh1 : Q'.abs (F.f a + (-(F.f x))) ≤ Q'.abs (F.f a) + Q'.abs (-(F.f x)) :=
        Q'.abs_add_le' (F.f a) (-(F.f x))
      exact Q'.le_trans' _ _ _ hh1
        (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (Q'.abs_neg' (F.f x))))
    have hsum2M : Q'.abs (F.f a) + Q'.abs (F.f x) ≤ 2 * F.bound :=
      Q'.le_trans' _ _ _ (Q'.add_le_add (F.f_le a) (F.f_le x))
        (Q'.ge_of_eqv (two_mul_eqv F.bound))
    have hfa : Q'.abs (F.f a - F.f x)
        ≤ ((2 * F.bound) * ((a - x) * (a - x))) * Q'.recip (δ * δ) :=
      Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ htri hsum2M) h2Mle'
    -- add ω δ ≥ 0 on the left
    refine Q'.le_trans' _ _ _ hfa ?_
    refine Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ (F.ω δ) (F.ω_nn δ)) ?_
    exact Q'.le_of_eqv (Q'.add_comm_eqv _ _)

/-! ## Finite-sum triangle inequality -/

/-- `|Σ g| ≤ Σ |g|`. -/
theorem abs_finSum_le (g : Nat → Q') :
    ∀ n, Q'.abs (finSum g n) ≤ finSum (fun k => Q'.abs (g k)) n
  | 0 => by
      show Q'.abs (0 : Q') ≤ (0 : Q')
      have h0 : Q'.abs (0 : Q') = (0 : Q') := abs_of_nonneg (Q'.le_refl' 0)
      rw [h0]; exact Q'.le_refl' 0
  | n + 1 => by
      show Q'.abs (finSum g n + g n)
          ≤ finSum (fun k => Q'.abs (g k)) n + Q'.abs (g n)
      exact Q'.le_trans' _ _ _ (Q'.abs_add_le' (finSum g n) (g n))
        (Q'.add_le_add_right _ _ _ (abs_finSum_le g n))

/-! ## The Bernstein sequence and its sampled second moment -/

/-- The sample point `k / n`. -/
def smp (n k : Nat) : Q' := Q'.ofNat k * Q'.recip (Q'.ofNat n)

/-- The Bernstein polynomial value `Σ_k f(k/n)·bₙₖ(x)` at `x`. -/
def bernstein (F : CtsMod) (n : Nat) (x : Q') : Q' :=
  finSum (fun k => F.f (smp n k) * bmono n x (1 - x) k) (n + 1)

/-- The sampled second moment `Σ_k (k/n − x)²·bₙₖ(x)` (`F`-free). -/
def quadSum (n : Nat) (x : Q') : Q' :=
  finSum (fun k => ((smp n k - x) * (smp n k - x)) * bmono n x (1 - x) k) (n + 1)

/-- Bernstein weights are nonnegative on `[0,1]`. -/
theorem bmono_nonneg (n : Nat) (x : Q') (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) (k : Nat) :
    (0 : Q') ≤ bmono n x (1 - x) k := by
  unfold bmono
  exact Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' (binom n k))
    (Q'.mul_nonneg _ _ (powNonneg x hx0 k) (powNonneg (1 - x) (one_sub_nonneg hx1) (n - k)))

/-! ## Centering (partition of unity) -/

/-- Centering: `Bₙf − f x ≃ Σ_k (f(k/n) − f x)·bₙₖ`. -/
theorem bernstein_sub_self (F : CtsMod) (n : Nat) (x : Q') :
    (bernstein F n x - F.f x).eqv
      (finSum (fun k => (F.f (smp n k) - F.f x) * bmono n x (1 - x) k) (n + 1)) := by
  have e1 : (finSum (fun k => (F.f (smp n k) - F.f x) * bmono n x (1 - x) k) (n + 1)).eqv
      (finSum (fun k => F.f (smp n k) * bmono n x (1 - x) k
                        + (-(F.f x)) * bmono n x (1 - x) k) (n + 1)) :=
    finSum_eqv_congr _ _
      (fun k => Q'.add_mul_eqv (F.f (smp n k)) (-(F.f x)) (bmono n x (1 - x) k)) (n + 1)
  have e2 : (finSum (fun k => F.f (smp n k) * bmono n x (1 - x) k
                        + (-(F.f x)) * bmono n x (1 - x) k) (n + 1)).eqv
      (finSum (fun k => F.f (smp n k) * bmono n x (1 - x) k) (n + 1)
        + finSum (fun k => (-(F.f x)) * bmono n x (1 - x) k) (n + 1)) :=
    finSum_add _ _ (n + 1)
  have e3 : (finSum (fun k => (-(F.f x)) * bmono n x (1 - x) k) (n + 1)).eqv (-(F.f x)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (const_mul_finSum (fun k => bmono n x (1 - x) k) (-(F.f x)) (n + 1))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (-(F.f x)) _ 1 (partition_of_unity n x)) ?_
    exact Q'.mul_one_eqv (-(F.f x))
  have e4 : (finSum (fun k => F.f (smp n k) * bmono n x (1 - x) k) (n + 1)
              + finSum (fun k => (-(F.f x)) * bmono n x (1 - x) k) (n + 1)).eqv
      (finSum (fun k => F.f (smp n k) * bmono n x (1 - x) k) (n + 1) + (-(F.f x))) :=
    Q'.add_eqv_congr_left _ _ _ e3
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 e4))

/-! ## Termwise majorant -/

/-- Termwise majorant of the centered Bernstein sum (via `term_majorant`). -/
theorem bernstein_close_termwise (F : CtsMod) (n : Nat) (x : Q')
    (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) (δ : Q') (hδ : (0 : Q') < δ) :
    finSum (fun k => Q'.abs ((F.f (smp n k) - F.f x) * bmono n x (1 - x) k)) (n + 1)
      ≤ finSum (fun k =>
          (F.ω δ + (2 * F.bound) * ((smp n k - x) * (smp n k - x)) * Q'.recip (δ * δ))
          * bmono n x (1 - x) k) (n + 1) := by
  refine ExpNeg.finSum_le_finSum_of_termwise _ _ (fun k => ?_) (n + 1)
  have hbk_nn : (0 : Q') ≤ bmono n x (1 - x) k := bmono_nonneg n x hx0 hx1 k
  have h1 : Q'.abs ((F.f (smp n k) - F.f x) * bmono n x (1 - x) k)
      ≤ Q'.abs (F.f (smp n k) - F.f x) * Q'.abs (bmono n x (1 - x) k) :=
    ExpNeg.abs_mul_le (F.f (smp n k) - F.f x) (bmono n x (1 - x) k)
  rw [abs_of_nonneg hbk_nn] at h1
  have h3 : Q'.abs (F.f (smp n k) - F.f x) * bmono n x (1 - x) k
      ≤ (F.ω δ + (2 * F.bound) * ((smp n k - x) * (smp n k - x)) * Q'.recip (δ * δ))
          * bmono n x (1 - x) k :=
    Q'.mul_le_mul_of_nonneg_right _ _ (bmono n x (1 - x) k)
      (term_majorant F δ hδ (smp n k) x) hbk_nn
  exact Q'.le_trans' _ _ _ h1 h3

/-! ## Collapsing the majorant sum -/

/-- Split the majorant sum through `partition_of_unity`:
`Σ (ω δ + 2M·(k/n−x)²·recip δ²)·bₙₖ ≃ ω δ + (2M·recip δ²)·quadSum`. -/
theorem majorant_split (F : CtsMod) (n : Nat) (x : Q') (δ : Q') :
    (finSum (fun k =>
        (F.ω δ + (2 * F.bound) * ((smp n k - x) * (smp n k - x)) * Q'.recip (δ * δ))
        * bmono n x (1 - x) k) (n + 1)).eqv
      (F.ω δ + (2 * F.bound) * Q'.recip (δ * δ) * quadSum n x) := by
  have split_term : ∀ k,
      ((F.ω δ + (2 * F.bound) * ((smp n k - x) * (smp n k - x)) * Q'.recip (δ * δ))
        * bmono n x (1 - x) k).eqv
      (F.ω δ * bmono n x (1 - x) k
        + ((2 * F.bound) * Q'.recip (δ * δ))
            * (((smp n k - x) * (smp n k - x)) * bmono n x (1 - x) k)) := by
    intro k
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (F.ω δ)
        ((2 * F.bound) * ((smp n k - x) * (smp n k - x)) * Q'.recip (δ * δ))
        (bmono n x (1 - x) k)) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (rearrange4 (2 * F.bound) ((smp n k - x) * (smp n k - x)) (Q'.recip (δ * δ))
        (bmono n x (1 - x) k))
  have e1 := finSum_eqv_congr _ _ split_term (n + 1)
  have e2 : (finSum (fun k => F.ω δ * bmono n x (1 - x) k
        + ((2 * F.bound) * Q'.recip (δ * δ))
            * (((smp n k - x) * (smp n k - x)) * bmono n x (1 - x) k)) (n + 1)).eqv
      (finSum (fun k => F.ω δ * bmono n x (1 - x) k) (n + 1)
        + finSum (fun k => ((2 * F.bound) * Q'.recip (δ * δ))
            * (((smp n k - x) * (smp n k - x)) * bmono n x (1 - x) k)) (n + 1)) :=
    finSum_add _ _ (n + 1)
  have eω : (finSum (fun k => F.ω δ * bmono n x (1 - x) k) (n + 1)).eqv (F.ω δ) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (const_mul_finSum (fun k => bmono n x (1 - x) k) (F.ω δ) (n + 1))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (F.ω δ) _ 1 (partition_of_unity n x)) ?_
    exact Q'.mul_one_eqv (F.ω δ)
  have eq2 : (finSum (fun k => ((2 * F.bound) * Q'.recip (δ * δ))
            * (((smp n k - x) * (smp n k - x)) * bmono n x (1 - x) k)) (n + 1)).eqv
      (((2 * F.bound) * Q'.recip (δ * δ)) * quadSum n x) :=
    Q'.eqv_symm
      (const_mul_finSum (fun k => ((smp n k - x) * (smp n k - x)) * bmono n x (1 - x) k)
        ((2 * F.bound) * Q'.recip (δ * δ)) (n + 1))
  refine Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 ?_)
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ eω)
    (Q'.add_eqv_congr_left (F.ω δ) _ _ eq2)

/-! ## The assembled approximation bound -/

/-- **The Bernstein uniform-approximation bound (`x`-explicit).**
`|Bₙf − f| ≤ ω δ + (2M·recip δ²)·quadSum n x`. -/
theorem bernstein_close (F : CtsMod) (n : Nat) (x : Q')
    (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) (δ : Q') (hδ : (0 : Q') < δ) :
    Q'.abs (bernstein F n x - F.f x)
      ≤ F.ω δ + (2 * F.bound) * Q'.recip (δ * δ) * quadSum n x := by
  have h_abs : Q'.abs (bernstein F n x - F.f x)
      ≤ Q'.abs (finSum (fun k => (F.f (smp n k) - F.f x) * bmono n x (1 - x) k) (n + 1)) :=
    Q'.le_of_eqv (Q'.abs_eqv_congr (bernstein_sub_self F n x))
  have h_absfin :
      Q'.abs (finSum (fun k => (F.f (smp n k) - F.f x) * bmono n x (1 - x) k) (n + 1))
        ≤ finSum (fun k => Q'.abs ((F.f (smp n k) - F.f x) * bmono n x (1 - x) k)) (n + 1) :=
    abs_finSum_le _ (n + 1)
  exact Q'.le_trans' _ _ _ h_abs
    (Q'.le_trans' _ _ _ h_absfin
      (Q'.le_trans' _ _ _ (bernstein_close_termwise F n x hx0 hx1 δ hδ)
        (Q'.le_of_eqv (majorant_split F n x δ))))

/-- The clean form once the sampled second moment is replaced by its closed
value `recip n · x(1−x)` (the `QuadSumVarianceStmt` residual). -/
theorem bernstein_close_variance (F : CtsMod) (n : Nat) (x : Q')
    (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) (δ : Q') (hδ : (0 : Q') < δ)
    (H : (quadSum n x).eqv (Q'.recip (Q'.ofNat n) * (x * (1 - x)))) :
    Q'.abs (bernstein F n x - F.f x)
      ≤ F.ω δ + (2 * F.bound) * Q'.recip (δ * δ) * (Q'.recip (Q'.ofNat n) * (x * (1 - x))) := by
  have h2M : (0 : Q') ≤ 2 * F.bound := Q'.mul_nonneg 2 F.bound (by decide) (bound_nonneg F)
  have hc : (0 : Q') ≤ (2 * F.bound) * Q'.recip (δ * δ) :=
    Q'.mul_nonneg _ _ h2M (Q'.le_of_lt (Q'.recip_pos (δ * δ)))
  refine Q'.le_trans' _ _ _ (bernstein_close F n x hx0 hx1 δ hδ) ?_
  exact Q'.add_le_add_left _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.le_of_eqv H) hc)

/-! ## Honest named residuals -/

/-- **Residual.**  The sampled second moment equals `recip n · x(1−x)`.  Reduces
to the proved `bernsteinVariance` (`Σ (k − n x)²·bₙₖ ≃ n·x(1−x)`) via
`(k/n − x)² = (k − n x)²·(recip n)²` and `n·(recip n)² ≃ recip n`. -/
def QuadSumVarianceStmt : Prop :=
  ∀ (n : Nat) (x : Q'), (0 : Q') ≤ x → x ≤ 1 →
    (quadSum n x).eqv (Q'.recip (Q'.ofNat n) * (x * (1 - x)))

/-- **Residual.**  The sup bound `x(1−x) ≤ 1/4` on `[0,1]` (constructive
sum-of-squares completion `1/4 − x(1−x) = (x − 1/2)² ≥ 0`).  Combined with
`bernstein_close_variance` it yields the fully `x`-uniform error
`ω δ + M·recip(2 n δ²)`. -/
def QuarterBoundStmt : Prop :=
  ∀ x : Q', (0 : Q') ≤ x → x ≤ 1 → x * (1 - x) ≤ Q'.recip (Q'.ofNat 4)

/-- **Residual input (Type-level).**  A vanishing modulus for `ω` at `0`: the
single genuinely-new datum the uniform-Cauchy wrap needs.  Assembling the
`SpectralUnifCauchy` the continuous functional calculus consumes additionally
requires a diagonal `δₙ` with `n·δₙ² → ∞` and the `QPoly` packaging of `Bₙ`. -/
def OmegaVanishing (F : CtsMod) : Type :=
  ∀ ε : Q', (0 : Q') < ε → Σ' δ : Q', PProd ((0 : Q') < δ) (F.ω δ ≤ ε)

end YMGap.Continuum.BernsteinUniformConvergence

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BernsteinUniformConvergence.term_majorant
#print axioms YMGap.Continuum.BernsteinUniformConvergence.abs_finSum_le
#print axioms YMGap.Continuum.BernsteinUniformConvergence.bmono_nonneg
#print axioms YMGap.Continuum.BernsteinUniformConvergence.bernstein_sub_self
#print axioms YMGap.Continuum.BernsteinUniformConvergence.bernstein_close_termwise
#print axioms YMGap.Continuum.BernsteinUniformConvergence.majorant_split
#print axioms YMGap.Continuum.BernsteinUniformConvergence.bernstein_close
#print axioms YMGap.Continuum.BernsteinUniformConvergence.bernstein_close_variance
