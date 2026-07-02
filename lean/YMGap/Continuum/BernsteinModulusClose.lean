/-
Bernstein modulus close — discharging the `QuadSumVarianceStmt0` residual and
reducing the `SpectralUnifCauchy` wrap to a single honest Type-level stage datum.

# GENUINELY PROVED here (`[propext]`/`[propext, Quot.sound]` only)

  * `quadSumVariance : QuadSumVarianceStmt0` — THE sampled-second-moment identity
    `quadSum n x ≃ recip n · x(1−x)` (restricted to `0 < n`), reduced by pure
    `Q'` algebra to the proved unconditional `bernsteinVariance`
    (`Σ (k − n x)²·bₙₖ ≃ n·x(1−x)`) via the rescaling `k/n − x = recip n·(k − n x)`.
    This turns the standing hypothesis `H` of `bernstein_uniform_bound` into a
    theorem, so the `x`-uniform Bernstein error is now unconditional.
  * `errorBound_of_split` — from the `½ε` split (`ω δ ≤ ½ε` and the reciprocal
    tail `(2M·recip δ²·recip n)·¼ ≤ ½ε`) the clean uniform error
    `|Bₙf − f| ≤ ε`, assembled on top of `bernstein_uniform_bound` and
    `quadSumVariance`.
  * `twoBound_of_split` — the two-sided reading `Bₙf ≤ f + ε ∧ f ≤ Bₙf + ε`
    (via `le_add_of_abs_sub_le` / `abs_sub_comm`).
  * `bernsteinErrorModulus` — the genuine builder `StageData F → ErrorModulus F`
    (each `ErrorModulus` field discharged by the above), and
  * `bernsteinSpectralCauchyOfStage` — the final wrap: `SpectralUnifCauchy` for
    the Bernstein `QPoly` sequence, UNCONDITIONAL given a `StageData F`.

# Honest named residual (NOT closed here)

  * `StageData F` — the Type-level stage datum: an antitone, positive stage
    function `stage`, a positive `δ`-selector with `ω(δ ε) ≤ ½ε`, and the
    Archimedean reciprocal tail bound past `stage ε`.  Its content is exactly the
    `qCeilNat` Archimedean threshold together with the antitone post-processing of
    an `OmegaVanishing` modulus — the sole genuinely-new analytic input flagged
    as the remaining friction.  Everything downstream of it is proved here.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorryAx`, no custom `axiom`.
-/

import YMGap.Continuum.BernsteinSequenceWrap

namespace YMGap.Continuum.BernsteinModulusClose

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BernsteinVariance
open YMGap.Continuum.BernsteinVarianceClose
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap

/-! ## 1. The sampled-second-moment identity `QuadSumVarianceStmt0` -/

/-- `0 < n` (as `Nat`) gives `0 < ofNat n` (as `Q'`). -/
theorem ofNat_pos (n : Nat) (hn : 0 < n) : (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => exact absurd hn (by decide)
  | succ m => exact Q'.ofNat_succ_pos m

/-- `recip n · n ≃ 1` on `0 < n`. -/
theorem rN_one (n : Nat) (hN : (0 : Q') < Q'.ofNat n) :
    (Q'.recip (Q'.ofNat n) * Q'.ofNat n).eqv 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Q'.recip (Q'.ofNat n)) (Q'.ofNat n))
    (Q'.mul_recip_eqv (Q'.ofNat n) hN)

/-- Sample rescaling `k/n − x ≃ recip n · (k − n x)`. -/
theorem sampleRescale (n : Nat) (hN : (0 : Q') < Q'.ofNat n) (x : Q') (k : Nat) :
    (smp n k - x).eqv (Q'.recip (Q'.ofNat n) * (Q'.ofNat k - Q'.ofNat n * x)) := by
  have e1 : (Q'.recip (Q'.ofNat n) * (Q'.ofNat k - Q'.ofNat n * x)).eqv
      (Q'.recip (Q'.ofNat n) * Q'.ofNat k
        + -(Q'.recip (Q'.ofNat n) * (Q'.ofNat n * x))) :=
    mul_sub_eqv (Q'.recip (Q'.ofNat n)) (Q'.ofNat k) (Q'.ofNat n * x)
  have e2 : (Q'.recip (Q'.ofNat n) * Q'.ofNat k).eqv (smp n k) :=
    Q'.mul_comm_eqv (Q'.recip (Q'.ofNat n)) (Q'.ofNat k)
  have hx : (Q'.recip (Q'.ofNat n) * (Q'.ofNat n * x)).eqv x :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.recip (Q'.ofNat n)) (Q'.ofNat n) x))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (Q'.recip (Q'.ofNat n) * Q'.ofNat n) 1 x (rN_one n hN))
        (Q'.one_mul_eqv x))
  have e3 : (-(Q'.recip (Q'.ofNat n) * (Q'.ofNat n * x))).eqv (-x) :=
    Q'.neg_eqv_congr _ _ hx
  have e4 : (Q'.recip (Q'.ofNat n) * Q'.ofNat k
              + -(Q'.recip (Q'.ofNat n) * (Q'.ofNat n * x))).eqv (smp n k + -x) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ e2)
      (Q'.add_eqv_congr_left _ _ _ e3)
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ e1 e4)

/-- Squared sample rescaling `(k/n − x)² ≃ (recip n)²·(k − n x)²`. -/
theorem sampleSqRescale (n : Nat) (hN : (0 : Q') < Q'.ofNat n) (x : Q') (k : Nat) :
    ((smp n k - x) * (smp n k - x)).eqv
      ((Q'.recip (Q'.ofNat n) * Q'.recip (Q'.ofNat n))
        * ((Q'.ofNat k - Q'.ofNat n * x) * (Q'.ofNat k - Q'.ofNat n * x))) := by
  have hs := sampleRescale n hN x k
  have m1 : ((smp n k - x) * (smp n k - x)).eqv
      ((Q'.recip (Q'.ofNat n) * (Q'.ofNat k - Q'.ofNat n * x))
        * (Q'.recip (Q'.ofNat n) * (Q'.ofNat k - Q'.ofNat n * x))) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hs)
      (Q'.mul_eqv_congr_left _ _ _ hs)
  have m2 := Q'.eqv_symm (Q'.mul_assoc_eqv
      (Q'.recip (Q'.ofNat n) * (Q'.ofNat k - Q'.ofNat n * x))
      (Q'.recip (Q'.ofNat n)) (Q'.ofNat k - Q'.ofNat n * x))
  have m3 := rearrange4 (Q'.recip (Q'.ofNat n)) (Q'.ofNat k - Q'.ofNat n * x)
      (Q'.recip (Q'.ofNat n)) (Q'.ofNat k - Q'.ofNat n * x)
  exact Q'.eqv_trans _ _ _ m1 (Q'.eqv_trans _ _ _ m2 m3)

/-- Term rescaling: `(k/n − x)²·bₙₖ ≃ (recip n)²·((k − n x)²·bₙₖ)`. -/
theorem termRescale (n : Nat) (hN : (0 : Q') < Q'.ofNat n) (x : Q') (k : Nat) :
    (((smp n k - x) * (smp n k - x)) * bmono n x (1 - x) k).eqv
      ((Q'.recip (Q'.ofNat n) * Q'.recip (Q'.ofNat n))
        * (((Q'.ofNat k - Q'.ofNat n * x) * (Q'.ofNat k - Q'.ofNat n * x))
            * bmono n x (1 - x) k)) := by
  have t1 := sampleSqRescale n hN x k
  have t2 : (((smp n k - x) * (smp n k - x)) * bmono n x (1 - x) k).eqv
      (((Q'.recip (Q'.ofNat n) * Q'.recip (Q'.ofNat n))
          * ((Q'.ofNat k - Q'.ofNat n * x) * (Q'.ofNat k - Q'.ofNat n * x)))
        * bmono n x (1 - x) k) :=
    Q'.mul_eqv_congr_right _ _ (bmono n x (1 - x) k) t1
  have t3 := Q'.mul_assoc_eqv
      (Q'.recip (Q'.ofNat n) * Q'.recip (Q'.ofNat n))
      ((Q'.ofNat k - Q'.ofNat n * x) * (Q'.ofNat k - Q'.ofNat n * x))
      (bmono n x (1 - x) k)
  exact Q'.eqv_trans _ _ _ t2 t3

/-- **`QuadSumVarianceStmt0`, proved.**  `quadSum n x ≃ recip n · x(1−x)` for
`0 < n`, reduced to the unconditional `bernsteinVariance`. -/
theorem quadSumVariance : QuadSumVarianceStmt0 := by
  intro n hn x hx0 hx1
  have hN : (0 : Q') < Q'.ofNat n := ofNat_pos n hn
  -- step A: rescale every term.
  have stepA : (quadSum n x).eqv
      (finSum (fun k => (Q'.recip (Q'.ofNat n) * Q'.recip (Q'.ofNat n))
          * (((Q'.ofNat k - Q'.ofNat n * x) * (Q'.ofNat k - Q'.ofNat n * x))
              * bmono n x (1 - x) k)) (n + 1)) :=
    finSum_eqv_congr
      (fun k => ((smp n k - x) * (smp n k - x)) * bmono n x (1 - x) k)
      (fun k => (Q'.recip (Q'.ofNat n) * Q'.recip (Q'.ofNat n))
          * (((Q'.ofNat k - Q'.ofNat n * x) * (Q'.ofNat k - Q'.ofNat n * x))
              * bmono n x (1 - x) k))
      (fun k => termRescale n hN x k) (n + 1)
  -- step B: pull the constant `(recip n)²` out of the sum.
  have stepB : (finSum (fun k => (Q'.recip (Q'.ofNat n) * Q'.recip (Q'.ofNat n))
          * (((Q'.ofNat k - Q'.ofNat n * x) * (Q'.ofNat k - Q'.ofNat n * x))
              * bmono n x (1 - x) k)) (n + 1)).eqv
      ((Q'.recip (Q'.ofNat n) * Q'.recip (Q'.ofNat n))
        * finSum (fun k => ((Q'.ofNat k - Q'.ofNat n * x) * (Q'.ofNat k - Q'.ofNat n * x))
              * bmono n x (1 - x) k) (n + 1)) :=
    Q'.eqv_symm
      (const_mul_finSum
        (fun k => ((Q'.ofNat k - Q'.ofNat n * x) * (Q'.ofNat k - Q'.ofNat n * x))
            * bmono n x (1 - x) k)
        (Q'.recip (Q'.ofNat n) * Q'.recip (Q'.ofNat n)) (n + 1))
  -- step C: the proved unconditional variance identity collapses the inner sum.
  have stepC : ((Q'.recip (Q'.ofNat n) * Q'.recip (Q'.ofNat n))
        * finSum (fun k => ((Q'.ofNat k - Q'.ofNat n * x) * (Q'.ofNat k - Q'.ofNat n * x))
              * bmono n x (1 - x) k) (n + 1)).eqv
      ((Q'.recip (Q'.ofNat n) * Q'.recip (Q'.ofNat n))
        * (Q'.ofNat n * (x * (1 - x)))) :=
    Q'.mul_eqv_congr_left _ _ _ (bernsteinVariance n x)
  -- step D: scalar collapse `(recip n)²·(n·M) ≃ recip n · M`.
  have stepD : ((Q'.recip (Q'.ofNat n) * Q'.recip (Q'.ofNat n))
        * (Q'.ofNat n * (x * (1 - x)))).eqv
      (Q'.recip (Q'.ofNat n) * (x * (1 - x))) := by
    have d1 := Q'.mul_assoc_eqv (Q'.recip (Q'.ofNat n)) (Q'.recip (Q'.ofNat n))
      (Q'.ofNat n * (x * (1 - x)))
    have d2 : (Q'.recip (Q'.ofNat n)
          * (Q'.recip (Q'.ofNat n) * (Q'.ofNat n * (x * (1 - x))))).eqv
        (Q'.recip (Q'.ofNat n)
          * ((Q'.recip (Q'.ofNat n) * Q'.ofNat n) * (x * (1 - x)))) :=
      Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.recip (Q'.ofNat n)) (Q'.ofNat n)
          (x * (1 - x))))
    have inner : ((Q'.recip (Q'.ofNat n) * Q'.ofNat n) * (x * (1 - x))).eqv
        (x * (1 - x)) :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ 1 (x * (1 - x)) (rN_one n hN))
        (Q'.one_mul_eqv (x * (1 - x)))
    have d3 : (Q'.recip (Q'.ofNat n)
          * ((Q'.recip (Q'.ofNat n) * Q'.ofNat n) * (x * (1 - x)))).eqv
        (Q'.recip (Q'.ofNat n) * (x * (1 - x))) :=
      Q'.mul_eqv_congr_left _ _ _ inner
    exact Q'.eqv_trans _ _ _ d1 (Q'.eqv_trans _ _ _ d2 d3)
  exact Q'.eqv_trans _ _ _ stepA
    (Q'.eqv_trans _ _ _ stepB (Q'.eqv_trans _ _ _ stepC stepD))

/-! ## 2. The uniform error from the `½ε` split -/

/-- **Uniform error from the split.**  Given `ω δ ≤ ½ε` and the reciprocal tail
`(2M·recip δ²·recip n)·¼ ≤ ½ε`, the Bernstein value approximates `f` within `ε`. -/
theorem errorBound_of_split (F : CtsMod) (n : Nat) (hn : 0 < n) (x : Q')
    (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) (δ : Q') (hδ : (0 : Q') < δ) (ε : Q')
    (hωδ : F.ω δ ≤ HalfPow.half * ε)
    (hrec : (2 * F.bound) * Q'.recip (δ * δ) * Q'.recip (Q'.ofNat n)
              * Q'.recip (Q'.ofNat 4) ≤ HalfPow.half * ε) :
    Q'.abs (bernstein F n x - F.f x) ≤ ε := by
  have H := quadSumVariance n hn x hx0 hx1
  have hb := bernstein_uniform_bound F n x hx0 hx1 δ hδ H
  have hsum : F.ω δ + (2 * F.bound) * Q'.recip (δ * δ) * Q'.recip (Q'.ofNat n)
                * Q'.recip (Q'.ofNat 4)
      ≤ HalfPow.half * ε + HalfPow.half * ε :=
    Q'.add_le_add hωδ hrec
  have hε : (HalfPow.half * ε + HalfPow.half * ε).eqv ε := ExpNeg.two_halves ε
  exact Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hε))

/-- **Two-sided reading.**  The same split gives `Bₙf ≤ f + ε ∧ f ≤ Bₙf + ε`. -/
theorem twoBound_of_split (F : CtsMod) (n : Nat) (hn : 0 < n) (x : Q')
    (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) (δ : Q') (hδ : (0 : Q') < δ) (ε : Q')
    (hωδ : F.ω δ ≤ HalfPow.half * ε)
    (hrec : (2 * F.bound) * Q'.recip (δ * δ) * Q'.recip (Q'.ofNat n)
              * Q'.recip (Q'.ofNat 4) ≤ HalfPow.half * ε) :
    bernstein F n x ≤ F.f x + ε ∧ F.f x ≤ bernstein F n x + ε := by
  have habs := errorBound_of_split F n hn x hx0 hx1 δ hδ ε hωδ hrec
  refine ⟨ExpNeg.le_add_of_abs_sub_le habs, ?_⟩
  have hcomm : Q'.abs (F.f x + -(bernstein F n x)) ≤ ε :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_sub_comm (F.f x) (bernstein F n x))) habs
  exact ExpNeg.le_add_of_abs_sub_le hcomm

/-! ## 3. The honest stage datum and the unconditional `SpectralUnifCauchy` -/

/-- **Residual input (Type-level).**  The stage datum for the uniform-Cauchy wrap:
a positive, antitone stage function, a positive `δ`-selector controlling `ω` by
`½ε`, and the Archimedean reciprocal tail bound past `stage ε`.  Its content is
the `qCeilNat` Archimedean threshold together with the antitone post-processing of
an `OmegaVanishing` modulus — the sole genuinely-new analytic input.  Every
`ErrorModulus`/`SpectralUnifCauchy` obligation downstream is proved from it. -/
structure StageData (F : CtsMod) where
  stage : Q' → Nat
  stage_pos : ∀ ε : Q', (0 : Q') < ε → 0 < stage ε
  stage_antitone : ∀ a b : Q', (0 : Q') < a → a ≤ b → stage b ≤ stage a
  delta : Q' → Q'
  delta_pos : ∀ ε : Q', (0 : Q') < ε → (0 : Q') < delta ε
  omega_small : ∀ ε : Q', (0 : Q') < ε → F.ω (delta ε) ≤ HalfPow.half * ε
  recip_small : ∀ ε : Q', (0 : Q') < ε → ∀ n : Nat, stage ε ≤ n →
    (2 * F.bound) * Q'.recip (delta ε * delta ε) * Q'.recip (Q'.ofNat n)
        * Q'.recip (Q'.ofNat 4)
      ≤ HalfPow.half * ε

/-- **The `ErrorModulus` builder.**  Every field of `ErrorModulus F` is discharged
from a `StageData F` by the proved `twoBound_of_split`. -/
def bernsteinErrorModulus (F : CtsMod) (SD : StageData F) : ErrorModulus F where
  stage := SD.stage
  stage_antitone := SD.stage_antitone
  twobound := by
    intro ε hε n hstage x hx0 hx1
    have hpos : 0 < n := by have := SD.stage_pos ε hε; omega
    exact twoBound_of_split F n hpos x hx0 hx1 (SD.delta ε) (SD.delta_pos ε hε) ε
      (SD.omega_small ε hε) (SD.recip_small ε hε n hstage)

/-- **The final wrap.**  `SpectralUnifCauchy` for the Bernstein `QPoly` sequence,
UNCONDITIONAL given a `StageData F`. -/
def bernsteinSpectralCauchyOfStage (F : CtsMod) (SD : StageData F)
    (lam : Q') (h0 : (0 : Q') ≤ lam) (h1 : lam ≤ 1) :
    ContinuousTransferCalculus.SpectralUnifCauchy (bernsteinPoly F) lam :=
  bernsteinPolySpectralCauchy F (bernsteinErrorModulus F SD) lam h0 h1

end YMGap.Continuum.BernsteinModulusClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BernsteinModulusClose.quadSumVariance
#print axioms YMGap.Continuum.BernsteinModulusClose.errorBound_of_split
#print axioms YMGap.Continuum.BernsteinModulusClose.twoBound_of_split
#print axioms YMGap.Continuum.BernsteinModulusClose.bernsteinErrorModulus
#print axioms YMGap.Continuum.BernsteinModulusClose.bernsteinSpectralCauchyOfStage
