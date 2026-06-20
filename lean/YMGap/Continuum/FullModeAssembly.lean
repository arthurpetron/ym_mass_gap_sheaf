/-
Track B / R2 — the **full-mode assembly**: composing the two proved halves of the
renormalized bond-moving crack (the all-mode quadratic ENVELOPE and the
Gaussian/Casimir MOMENT bound) into ONE scalar `O((1−w)²)` bound on the
scaled-norm renormalized defect, and then composing the full-mode chain
`scalar-A bound → inverse-square per-step → summable → exponential product floor`
to a STRICTLY POSITIVE product floor for the renormalized full-mode per-block
rates.

# What this module assembles (and exactly how honest the assembly is)

Two already-proved engines are combined at the scalar level:

  1. The all-mode quadratic ENVELOPE: the per-mode renormalized transverse defect
     `δ_s(w)` is `≤ dimQ s · C₄(s)² · (1−w)²` for EVERY mode `s`, with the
     envelope `(1−w)²·(dimQ s·C₄(s)²)` surviving the bond-moving fusion
     convolution by positive domination.  (The `s = 1`-matched residual is proved
     quadratic for all modes.)

  2. The Gaussian/Casimir MOMENT bound: for any nonneg-coefficient test
     polynomial `P`, power `q`, precision `r`, and moving cutoff `S`, the
     `τ`-weighted moment `∑_s μ_τ(s)·qfac(w,s)^q·P((1−w)·C₄(s))` is `≤
     momentM P q r S`, a constant INDEPENDENT of `w` (for a FIXED cutoff `S`).

The scalar-A assembly here:

  * **The square test polynomial `sqPoly = y²`** (`[0,0,1]`, nonneg coeffs) makes
    the moment summand carry the envelope shape: `Peval sqPoly (yArg w s) =
    ((1−w)·C₄(s))² = (1−w)²·C₄(s)²`.

  * **The `(1−w)²` factor pulls OUT of the whole scaled moment**
    (`momentSum_sq_factor`): each summand is `(1−w)²` times the `w`-attenuated
    Casimir-square moment summand `μ_τ(s)·qfac(w,s)^q·C₄(s)²`, so the finite
    moment sum equals `(1−w)² · (Casimir-square moment sum)`.

  * **The scalar defect** `δ_ren(w,N,q,S,M) := momentSum w N hZ q sqPoly (S+M)` is
    the scaled-norm renormalized full-mode defect proxy.  The assembly gives the
    two faithful bounds (`fullMode_defect_scalar_bound`):

        δ_ren  ≤  momentM sqPoly q r S            (the moment bound directly), and
        δ_ren  =  (1−w)² · (Casimir-square moment) (the quadratic factorization).

# PIN THE RESIDUAL — the moment uniformity (the honest crux, AGENTS.md Rule 6)

The clean `δ_ren ≤ C·(1−w)²` with `C` a SINGLE `w`-independent constant requires
the Casimir-square moment `∑ μ_τ·qfac^q·C₄(s)²` to be bounded UNIFORMLY in `w` as
`w → 1`.  `moment_bound`'s constant `momentM P q r S` is `w`-independent only for
a FIXED cutoff `S`; to cover `w → 1` the tail cutoff must grow `S = S(w) ≍
τ^{−1/2}`, and `momentM`'s head term `ofNat S · (1 + C₄(S))^q · P(C₄(S))` then
carries that growth.  Writing `S(w) ≍ τ^{−1/2}` and `M(w) = momentM sqPoly q r
S(w) ≍ τ^{−α}` for an explicit `α ≥ 0`, the scalar bound reads

        δ_ren  ≤  M(w) · (1−w)²  ≍  C · τ^{2−α}      (with `(1−w) ≍ τ`).

  * **If the moment is UNIFORM (`α = 0`):** clean `δ_ren ≤ C·τ²`, and the chain
    closes with the inverse-square summability endpoint verbatim (the heat-kernel
    SCALING is DESIGNED so the active-mode count is offset by the `μ_τ` Gaussian
    decay, making the moments τ-independent — this is the intended `α = 0`).

  * **If the moment carries the cutoff growth (`α > 0`):** `δ_ren ≤ C·τ^{2−α}`,
    summable along the `1/k` AF rate iff `2 − α > 1`, i.e. `α < 1`.

This module does NOT prove the moment uniform.  It PINS the residual exactly: the
chain capstone takes the uniform Casimir-square moment as a NAMED hypothesis
`hMoment` (a single `w`-independent bound on `∑ μ_τ·qfac^q·C₄(s)²`), composes the
rest unconditionally, and the residual is precisely the inhabitation of
`hMoment` (equivalently `α = 0`, or `α < 1` with the `τ^{2−α}` series).  This is
the ONE remaining quantitative residual of Theorem A (scalar, full-mode).

# The full-mode chain (composed here, conditional on the named residual)

  scalar-A bound (`hMoment` ⇒ `δ_ren ≤ C·(1−w)²`)
    →  AF rate `1 − w_k ≤ A/(k+B)`  (the named two-loop input, via `afRate`)
    →  inverse-square per-step `δ_ren(w_k) ≤ D/(k+2)²`
    →  summable `∑ δ_ren < ∞`  (`summableBound_of_invSq`)
    →  exponential product floor `∏ ρ_k ≥ e^{−2R} > 0`
       (`sum_loss_to_productFloor_exp`).

Capstone `fullMode_gap_of_AFRate`: the full-mode analogue of the dominant-mode
`renormalized_gap_of_AFRate`, taking the AF rate and the uniform-moment residual
as inputs and producing a strictly-positive product floor.

# SCOPE and honesty (CRITICAL)

  * `modeDefect` is the `s = 1`-MATCHED renormalized residual (the retuning
    matches the `s = 1` direction only); it is proved quadratic for ALL modes.
  * FINITE fusion degree `N` (the moment cutoff `N₀`).
  * The AF recurrence is the NAMED two-loop input (carried as `AFRateModulus`).
  * The ONE remaining quantitative residual is the moment uniformity (clean `τ²`
    iff `α = 0`; `α < 1` suffices for summability), carried as the explicit
    hypothesis `hMoment`.

This is the full-mode chain ASSEMBLED, conditional on those named/quantitative
residuals — NOT a 4D Yang–Mills mass-gap proof.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and composition; every load-bearing declaration is
gated with `#print axioms` (permitted: `propext` / `Quot.sound`).  No
`Classical.*`, no `native_decide`, no `sorry`.  All constants and moduli are
`Type`-level data.
-/

import YMGap.Continuum.FullModeQuadratic
import YMGap.Continuum.BondMovingMoment
import YMGap.Continuum.AFRateCalibration
import YMGap.Continuum.SummableInverseSquare
import YMGap.Continuum.ExpProductFloor
import YMGap.Continuum.SummabilityCapstone

namespace YMGap.Continuum.FullModeAssembly

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.FullModeQuadratic
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.ProductFloor
open YMGap.Continuum.ExpProductFloor

/-! ## −1. Small local helpers (proved here, axiom-clean) -/

/-- `RationalTail.finSum` of a nonnegative sequence is nonnegative. -/
theorem finSum_nonneg {f : Nat → Q'} (hf : ∀ i, (0 : Q') ≤ f i) :
    ∀ n, (0 : Q') ≤ RationalTail.finSum f n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
      show (0 : Q') ≤ RationalTail.finSum f n + f n
      exact Q'.zero_le_add _ _ (finSum_nonneg hf n) (hf n)

/-- The square regroup `(A·B)·(A·B) ≃ (A·A)·(B·B)` (pure assoc/comm, at the
num/den cross-product level). -/
theorem sq_regroup (A B : Q') :
    ((A * B) * (A * B)).eqv ((A * A) * (B * B)) := by
  show ((A * B) * (A * B)).num * (((A * A) * (B * B)).den : Int)
      = ((A * A) * (B * B)).num * (((A * B) * (A * B)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  push_cast
  ac_rfl

/-- Pull a leading constant out through the `μ·qfac^q` weight:
`b·(c·(F·E)) ≃ F·(b·(c·E))` (here `F = (1−w)²`, `b = μ`, `c = qfac^q`,
`E = C₄·C₄`).  Pure assoc/comm at the num/den cross-product level. -/
theorem moment_pull_factor (F b c E : Q') :
    (b * (c * (F * E))).eqv (F * (b * (c * E))) := by
  show (b * (c * (F * E))).num * ((F * (b * (c * E))).den : Int)
      = (F * (b * (c * E))).num * ((b * (c * (F * E))).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  push_cast
  ac_rfl

/-! ## 0. The square test polynomial `sqPoly = y²`

`P_p(y) = y²` is the envelope polynomial.  As a `QPoly.Poly` it is `[0, 0, 1]`
(coefficients low-to-high: `0 + 0·y + 1·y²`), with nonnegative coefficients, and
`Peval sqPoly y = y·(y·1) = y²` (up to the `Q'` unit/zero laws). -/

/-- The square test polynomial `sqPoly = y²` as `[0,0,1]`. -/
def sqPoly : Poly := [(0 : Q'), (0 : Q'), (1 : Q')]

/-- `sqPoly` has nonnegative coefficients. -/
theorem sqPoly_nonneg : nonnegCoeffs sqPoly :=
  ⟨by decide, ⟨by decide, ⟨by decide, True.intro⟩⟩⟩

/-- `Peval sqPoly y ≃ y·y` (the square).  PROOF: `Peval [0,0,1] y =
0 + y·(0 + y·(1 + y·0))`; collapse the `Q'` zero/unit laws to `y·y`. -/
theorem Peval_sqPoly_eqv (y : Q') : (Peval sqPoly y).eqv (y * y) := by
  -- Peval [0,0,1] y = 0 + y * (0 + y * (1 + y * 0))
  show ((0 : Q') + y * ((0 : Q') + y * ((1 : Q') + y * (0 : Q')))).eqv (y * y)
  -- innermost: 1 + y*0 ≃ 1
  have h0 : ((1 : Q') + y * (0 : Q')).eqv (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 _ 0 (Q'.mul_zero_eqv y))
      (Q'.eqv_of_eq (Q'.add_zero' 1))
  -- y*(1 + y*0) ≃ y*1 ≃ y
  have h1 : (y * ((1 : Q') + y * (0 : Q'))).eqv y :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left y _ 1 h0) (Q'.mul_one_eqv y)
  -- 0 + y*(1 + y*0) ≃ y
  have h2 : ((0 : Q') + y * ((1 : Q') + y * (0 : Q'))).eqv y :=
    Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) h1
  -- y*(0 + y*(1 + y*0)) ≃ y*y
  have h3 : (y * ((0 : Q') + y * ((1 : Q') + y * (0 : Q')))).eqv (y * y) :=
    Q'.mul_eqv_congr_left y _ y h2
  -- 0 + y*(…) ≃ y*y
  exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) h3

/-! ## 1. The Casimir-square moment summand and the `(1−w)²` factorization

The square test polynomial makes `momentTerm` carry the envelope shape
`Peval sqPoly (yArg w s) ≃ yArg(w,s)² = ((1−w)·C₄(s))²`.  We split this as
`(1−w)² · C₄(s)²` and pull the universal quadratic margin `(1−w)²` out of the
WHOLE finite moment sum, leaving the `w`-attenuated Casimir-square moment. -/

/-- The Casimir-square moment summand
`μ_τ(s)·qfac(w,s)^q·C₄(s)²` (the `(1−w)²`-stripped per-mode moment summand). -/
def casimirSqTerm (w : Q') (N : Nat) (hZ : (0 : Q') < Zsum w N) (q : Nat)
    (s : Nat) : Q' :=
  μ w N hZ s * (qfac w s ^ q * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)))

theorem casimirSqTerm_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N : Nat)
    (hZ : (0 : Q') < Zsum w N) (q s : Nat) : (0 : Q') ≤ casimirSqTerm w N hZ q s := by
  refine Q'.mul_nonneg _ _ (μ_nonneg hw0 N hZ s) ?_
  exact Q'.mul_nonneg _ _ (Q'.pow_nonneg _ (qfac_nonneg hw1 s) q)
    (Q'.mul_nonneg _ _ (zero_le_ofNat _) (zero_le_ofNat _))

/-- The Casimir-square moment sum `∑_{s<n} μ_τ(s)·qfac^q·C₄(s)²`. -/
def casimirSqSum (w : Q') (N : Nat) (hZ : (0 : Q') < Zsum w N) (q : Nat)
    (n : Nat) : Q' :=
  RationalTail.finSum (fun s => casimirSqTerm w N hZ q s) n

theorem casimirSqSum_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N : Nat)
    (hZ : (0 : Q') < Zsum w N) (q n : Nat) : (0 : Q') ≤ casimirSqSum w N hZ q n :=
  finSum_nonneg (fun s => casimirSqTerm_nonneg hw0 hw1 N hZ q s) n

/-- **The per-mode `(1−w)²` split.**  With the square test polynomial,

    momentTerm w N hZ q sqPoly s
      ≃  ((1−w)·(1−w)) · casimirSqTerm w N hZ q s.

PROOF.  `Peval sqPoly (yArg w s) ≃ yArg² = ((1−w)·C₄(s))²`, and
`((1−w)·C₄(s))² ≃ (1−w)²·C₄(s)²`; reassociate the `μ·qfac^q` weight back. -/
theorem momentTerm_sqPoly_factor {w : Q'} (N : Nat) (hZ : (0 : Q') < Zsum w N)
    (q s : Nat) :
    (momentTerm w N hZ q sqPoly s).eqv
      (((1 : Q') - w) * ((1 : Q') - w) * casimirSqTerm w N hZ q s) := by
  -- momentTerm = μ · (qfac^q · Peval sqPoly (yArg w s))
  show (μ w N hZ s * (qfac w s ^ q * Peval sqPoly (yArg w s))).eqv
      (((1 : Q') - w) * ((1 : Q') - w)
        * (μ w N hZ s * (qfac w s ^ q * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)))))
  -- Peval sqPoly (yArg w s) ≃ yArg·yArg ≃ (1−w)²·C₄(s)²
  -- yArg w s = (1−w)·C₄(s)
  have hyy : (Peval sqPoly (yArg w s)).eqv
      (((1 : Q') - w) * ((1 : Q') - w) * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))) := by
    refine Q'.eqv_trans _ _ _ (Peval_sqPoly_eqv (yArg w s)) ?_
    -- yArg·yArg = ((1−w)·C₄)·((1−w)·C₄) ≃ ((1−w)·(1−w))·(C₄·C₄)
    show ((((1 : Q') - w) * Q'.ofNat (c4 s)) * (((1 : Q') - w) * Q'.ofNat (c4 s))).eqv
        ((((1 : Q') - w) * ((1 : Q') - w)) * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)))
    -- (A·B)·(A·B) ≃ (A·A)·(B·B) : the four-factor regroup mul_four_swap gives
    -- (A·B)·(A·B) ≃ (A·B)·(B·A) (swap), better to use a direct ac route via
    -- the existing mul_four_swap (A B C D): (A·B)·(C·D) ≃ (A·D)·(B·C) at C=A,D=B
    -- gives (A·B)·(A·B) ≃ (A·B)·(B·A) — not what we want.  Use a num/den cross.
    exact sq_regroup ((1 : Q') - w) (Q'.ofNat (c4 s))
  -- assemble:  μ·(qfac^q·Peval) ≃ μ·(qfac^q·((1−w)²·C₄²))
  --   ≃ (1−w)²·(μ·(qfac^q·C₄²))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (μ w N hZ s) _ _
      (Q'.mul_eqv_congr_left (qfac w s ^ q) _ _ hyy)) ?_
  -- μ·(qfac^q·((1−w)²·(C₄·C₄))) ≃ (1−w)²·(μ·(qfac^q·(C₄·C₄)))
  exact moment_pull_factor (((1 : Q') - w) * ((1 : Q') - w))
    (μ w N hZ s) (qfac w s ^ q) (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))

/-- **The whole-sum `(1−w)²` factorization.**  The square-test moment sum is
`(1−w)²` times the Casimir-square moment sum:

    momentSum w N hZ q sqPoly n  ≃  (1−w)² · casimirSqSum w N hZ q n.

PROOF.  Termwise `(1−w)²`-split (`momentTerm_sqPoly_factor`), then pull the
constant out of the finite sum (`const_mul_finSum`). -/
theorem momentSum_sq_factor {w : Q'} (N : Nat) (hZ : (0 : Q') < Zsum w N)
    (q n : Nat) :
    (momentSum w N hZ q sqPoly n).eqv
      (((1 : Q') - w) * ((1 : Q') - w) * casimirSqSum w N hZ q n) := by
  -- momentSum = finSum momentTerm ; termwise ≃ (1−w)²·casimirSqTerm ; pull out.
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr (fun s => momentTerm w N hZ q sqPoly s)
      (fun s => ((1 : Q') - w) * ((1 : Q') - w) * casimirSqTerm w N hZ q s)
      (fun s => momentTerm_sqPoly_factor N hZ q s) n) ?_
  exact Q'.eqv_symm (RationalTail.const_mul_finSum
    (fun s => casimirSqTerm w N hZ q s) (((1 : Q') - w) * ((1 : Q') - w)) n)

/-! ## 2. SCALAR THEOREM A — the assembly

The scalar renormalized full-mode defect proxy is the square-test scaled moment
`δ_ren := momentSum w N hZ q sqPoly (S+M)`.  Two faithful bounds:

  (A)  the MOMENT bound `δ_ren ≤ momentM sqPoly q r S` (directly from
       `moment_bound`), with `momentM` independent of `w` for the FIXED cutoff `S`;
  (B)  the QUADRATIC FACTORIZATION `δ_ren = (1−w)²·casimirSqSum`
       (`momentSum_sq_factor`), exposing the `(1−w)²` structure.

Combining (A)+(B): `δ_ren ≤ M·(1−w)²` precisely when the Casimir-square moment
`casimirSqSum` is bounded by a `w`-independent `M` — the residual pinned below. -/

/-- **SCALAR THEOREM A — the moment-bound half.**  The square-test scaled moment
`δ_ren = momentSum w N₀ hZ q sqPoly (S+M)` is bounded by the explicit
`w`-independent constant `momentM sqPoly q r S` (for a fixed cutoff `S`),
uniformly in the tail window `M`.  This is `moment_bound` instantiated at
`P = sqPoly = y²`.  HONEST: `momentM` is `w`-independent only for FIXED `S`; the
moving cutoff `S = S(w)` is the residual (pinned below). -/
theorem fullMode_defect_scalar_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (q m r S N₀ : Nat) (hSN : S ≤ N₀)
    (hZ : (0 : Q') < Zsum w N₀)
    (hsummand : ∀ k,
      momentTerm w N₀ hZ q sqPoly (S + k) ≤ tailTerm w (m + 2) (S + k))
    (hcut : Q'.ofNat (2 ^ (m + 2)) * qpow w (2 * S + 3) ≤ HalfPow.half)
    (hhead : tailTerm w (m + 2) S ≤ dyad (r + 1)) :
    ∀ M, momentSum w N₀ hZ q sqPoly (S + M) ≤ momentM sqPoly q r S :=
  moment_bound hw0 hw1 sqPoly sqPoly_nonneg q m r S N₀ hSN hZ hsummand hcut hhead

/-- **SCALAR THEOREM A — the quadratic-factorization half.**  The same scaled
moment EQUALS `(1−w)²` times the Casimir-square moment:

    δ_ren  =  (1−w)² · casimirSqSum w N hZ q n.

This is `momentSum_sq_factor`; it makes the QUADRATIC-in-margin structure manifest
and is what turns a UNIFORM Casimir-square moment into the clean `δ_ren ≤
C·(1−w)²`. -/
theorem fullMode_defect_quadratic_factor {w : Q'} (N : Nat) (hZ : (0 : Q') < Zsum w N)
    (q n : Nat) :
    (momentSum w N hZ q sqPoly n).eqv
      (((1 : Q') - w) * ((1 : Q') - w) * casimirSqSum w N hZ q n) :=
  momentSum_sq_factor N hZ q n

/-- **SCALAR THEOREM A — the clean `C·(1−w)²` bound, GIVEN the uniform moment.**
If the Casimir-square moment is bounded by a `w`-independent `M ≥ 0`
(`hMoment : casimirSqSum w N hZ q n ≤ M`), then the scalar full-mode defect is
genuinely quadratic in the margin:

    δ_ren  =  (1−w)²·casimirSqSum  ≤  M·(1−w)².

This is the clean Theorem A (scalar, full-mode): the assembly of the all-mode
quadratic envelope (via the square test polynomial) with a uniform moment.  The
inhabitation of `hMoment` (the moment uniformity, `α = 0`) is the residual. -/
theorem fullMode_defect_clean_quadratic {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) (hZ : (0 : Q') < Zsum w N) (q n : Nat) (M : Q')
    (hMoment : casimirSqSum w N hZ q n ≤ M) :
    momentSum w N hZ q sqPoly n ≤ M * (((1 : Q') - w) * ((1 : Q') - w)) := by
  -- δ_ren = (1−w)²·casimirSqSum ≤ (1−w)²·M ≃ M·(1−w)².
  have hfac := momentSum_sq_factor N hZ q n
  have hmarnn : (0 : Q') ≤ ((1 : Q') - w) * ((1 : Q') - w) :=
    Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hw1) (Q'.sub_nonneg_of_le hw1)
  have hstep : ((1 : Q') - w) * ((1 : Q') - w) * casimirSqSum w N hZ q n
      ≤ ((1 : Q') - w) * ((1 : Q') - w) * M :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hMoment hmarnn
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hfac) ?_
  exact Q'.le_trans' _ _ _ hstep
    (Q'.le_of_eqv (Q'.mul_comm_eqv (((1 : Q') - w) * ((1 : Q') - w)) M))

/-! ## 3. The full-mode chain — composing to a positive product floor

With the clean scalar-A bound `δ_ren(w_k) ≤ M·(1−w_k)²` (GIVEN the uniform
moment), the AF rate `1 − w_k ≤ A/(k+B)`, the offset adapter, and the
inverse-square summability + exponential product-floor endpoints, we get a
strictly positive floor for the running product of the renormalized full-mode
per-block rates `ρ_k = 1 − δ_ren(w_k)`.

We reuse the proved offset adapter and inverse-square machinery from the
dominant-mode capstone (the offset constants `inflM`, `harmDen2`, `rateScaled`,
the adapter `margin_le_scaled`, and the term `invSqTerm 2`), now with the
full-mode scalar defect carried as an abstract per-step sequence
`fmDefect afr k` satisfying `fmDefect afr k ≤ M·(1−w_k)²`. -/

/-- The full-mode per-step scalar defect along an AF rate, as an abstract sequence
`d : Nat → Q'` (the assembled `δ_ren(w_k)`), carried with its proved properties
as hypotheses.  We package the chain over such a sequence. -/
structure FullModeDefect (afr : AFRateModulus) : Type where
  /-- The per-step scalar full-mode defect `δ_ren(w_k)`. -/
  d : Nat → Q'
  /-- Nonnegativity (the defect is a scaled norm / moment). -/
  d_nonneg : ∀ k, (0 : Q') ≤ d k
  /-- The uniform quadratic constant `M ≥ 0` (the uniform-moment residual). -/
  M : Q'
  M_nonneg : (0 : Q') ≤ M
  /-- The clean scalar-A bound `δ_ren(w_k) ≤ M·(1−w_k)²` (the assembled Theorem
      A, conditional on the uniform moment). -/
  d_quad : ∀ k, d k ≤ M * (((1 : Q') - afr.w k) * ((1 : Q') - afr.w k))

/-- The full-mode inverse-square constant `D = M·(M·A)²` (the analogue of the
dominant-mode `Aconst`, with the quadratic constant `M` in place of `C_p`). -/
def fmAconst (afr : AFRateModulus) (fm : FullModeDefect afr) : Q' :=
  fm.M * (SummabilityCapstone.rateScaled afr * SummabilityCapstone.rateScaled afr)

theorem fmAconst_nonneg (afr : AFRateModulus) (fm : FullModeDefect afr) :
    (0 : Q') ≤ fmAconst afr fm :=
  Q'.mul_nonneg _ _ fm.M_nonneg
    (Q'.mul_nonneg _ _ (SummabilityCapstone.rateScaled_nonneg afr)
      (SummabilityCapstone.rateScaled_nonneg afr))

/-- **The per-step inverse-square bound for the full-mode defect.**  Along an AF
rate, `δ_ren(w_k) ≤ D · 1/(k+2)²` with `D = M·(M·A)²`.  PROOF: the clean
scalar-A bound `δ_ren(w_k) ≤ M·(1−w_k)²` composes with the offset adapter
`margin_le_scaled` (`1−w_k ≤ (M·A)/(k+2)`) and the square-to-inverse-square
bound `scaledMargin_sq_le_invSq`, exactly as in the dominant-mode capstone. -/
theorem fmDefect_invSq (afr : AFRateModulus) (fm : FullModeDefect afr) (k : Nat) :
    fm.d k ≤ fmAconst afr fm * invSqTerm 2 (by decide) k := by
  -- abbreviations matching SummabilityCapstone.
  let r := Q'.divPos (SummabilityCapstone.rateScaled afr)
    (SummabilityCapstone.harmDen2 k) (SummabilityCapstone.harmDen2_pos k)
  -- (1−w_k) ≤ r  (the offset adapter).
  have hmargin : (1 : Q') - afr.w k ≤ r := SummabilityCapstone.margin_le_scaled afr k
  have hmarnn : (0 : Q') ≤ (1 : Q') - afr.w k :=
    Q'.sub_nonneg_of_le (Q'.le_of_lt (afr.w_lt_one k))
  -- (1−w_k)² ≤ r·r.
  have hrnn : (0 : Q') ≤ r := by
    show (0 : Q') ≤ SummabilityCapstone.rateScaled afr
        * Q'.recipPos (SummabilityCapstone.harmDen2 k) (SummabilityCapstone.harmDen2_pos k)
    exact Q'.mul_nonneg _ _ (SummabilityCapstone.rateScaled_nonneg afr)
      (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have hsq : ((1 : Q') - afr.w k) * ((1 : Q') - afr.w k) ≤ r * r := by
    have h1 : ((1 : Q') - afr.w k) * ((1 : Q') - afr.w k) ≤ r * ((1 : Q') - afr.w k) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hmargin hmarnn
    have h2 : r * ((1 : Q') - afr.w k) ≤ r * r :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hmargin hrnn
    exact Q'.le_trans' _ _ _ h1 h2
  -- δ ≤ M·(1−w)² ≤ M·(r·r).
  have hquad : fm.d k ≤ fm.M * (((1 : Q') - afr.w k) * ((1 : Q') - afr.w k)) :=
    fm.d_quad k
  have hMrr : fm.M * (((1 : Q') - afr.w k) * ((1 : Q') - afr.w k)) ≤ fm.M * (r * r) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsq fm.M_nonneg
  -- r·r ≤ rateScaled²·invSqTerm 2 k  (the proved square-to-inverse-square bound).
  have hrr : r * r
      ≤ (SummabilityCapstone.rateScaled afr * SummabilityCapstone.rateScaled afr)
          * invSqTerm 2 (by decide) k :=
    SummabilityCapstone.scaledMargin_sq_le_invSq afr k
  have hM2 : fm.M * (r * r)
      ≤ fm.M * ((SummabilityCapstone.rateScaled afr * SummabilityCapstone.rateScaled afr)
          * invSqTerm 2 (by decide) k) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hrr fm.M_nonneg
  -- M·(rateScaled²·invSqTerm) ≃ (M·rateScaled²)·invSqTerm = fmAconst·invSqTerm.
  have hassoc : (fm.M * ((SummabilityCapstone.rateScaled afr
        * SummabilityCapstone.rateScaled afr) * invSqTerm 2 (by decide) k)).eqv
      (fmAconst afr fm * invSqTerm 2 (by decide) k) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv fm.M
      (SummabilityCapstone.rateScaled afr * SummabilityCapstone.rateScaled afr)
      (invSqTerm 2 (by decide) k))
  exact Q'.le_trans' _ _ _ hquad
    (Q'.le_trans' _ _ _ hMrr
      (Q'.le_trans' _ _ _ hM2 (Q'.le_of_eqv hassoc)))

/-- **Summability of the full-mode defect.**  Every tail window of `δ_ren` is
bounded by `D·pot 2 N = D/(N+1)`. -/
theorem fmDefect_summable (afr : AFRateModulus) (fm : FullModeDefect afr) (N M : Nat) :
    tailSum fm.d N M ≤ fmAconst afr fm * pot 2 (by decide) N :=
  summableBound_of_invSq 2 (by decide) (fmAconst afr fm) (fmAconst_nonneg afr fm)
    fm.d (fmDefect_invSq afr fm) N M

/-! ## 4. The tail product floor — restricting to `k ≥ k₀` where `δ_ren ≤ 1/2` -/

/-- The full-mode defect head-cutoff `k₀ = 2·D.num.toNat`: for `k ≥ k₀`,
`δ_ren k ≤ 1/2`. -/
def fmCutoff (afr : AFRateModulus) (fm : FullModeDefect afr) : Nat :=
  2 * (fmAconst afr fm).num.toNat

/-- For `k ≥ k₀`, the full-mode defect is `≤ 1/2`.  Same chain as the
dominant-mode `renDefect_le_half`: `δ ≤ D·1/(k+2)² ≤ D·1/(k+2) ≤ 1/2`. -/
theorem fmDefect_le_half (afr : AFRateModulus) (fm : FullModeDefect afr) {k : Nat}
    (hk : fmCutoff afr fm ≤ k) :
    fm.d k ≤ HalfPow.half := by
  have hAnn : (0 : Q') ≤ fmAconst afr fm := fmAconst_nonneg afr fm
  have hAnum : 0 ≤ (fmAconst afr fm).num := (Q'.zero_le_iff_num_nonneg _).mp hAnn
  have h1 : fm.d k ≤ fmAconst afr fm * invSqTerm 2 (by decide) k := fmDefect_invSq afr fm k
  have hk2 : 0 < k + 2 := by omega
  have hk2sq : 0 < (k + 2) * (k + 2) := Nat.mul_pos hk2 hk2
  have hanti : unit ((k + 2) * (k + 2)) hk2sq ≤ unit (k + 2) hk2 := by
    refine unit_antitone hk2 hk2sq ?_
    calc k + 2 = (k + 2) * 1 := by omega
      _ ≤ (k + 2) * (k + 2) := Nat.mul_le_mul_left (k + 2) (by omega)
  have h2 : fmAconst afr fm * invSqTerm 2 (by decide) k
      ≤ fmAconst afr fm * unit (k + 2) hk2 := by
    show fmAconst afr fm * unit ((k + 2) * (k + 2)) _ ≤ fmAconst afr fm * unit (k + 2) hk2
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hanti hAnn
  have h3 : fmAconst afr fm * unit (k + 2) hk2 ≤ HalfPow.half := by
    show (fmAconst afr fm * unit (k + 2) hk2).num * (HalfPow.half.den : Int)
        ≤ HalfPow.half.num * ((fmAconst afr fm * unit (k + 2) hk2).den : Int)
    have hhn : HalfPow.half.num = 1 := rfl
    have hhd : (HalfPow.half.den : Int) = 2 := rfl
    rw [hhn, hhd, Int.one_mul]
    have hLn : (fmAconst afr fm * unit (k + 2) hk2).num = (fmAconst afr fm).num := by
      show (fmAconst afr fm).num * (unit (k + 2) hk2).num = (fmAconst afr fm).num
      rw [unit_num, Int.mul_one]
    have hLd : ((fmAconst afr fm * unit (k + 2) hk2).den : Int)
        = ((fmAconst afr fm).den : Int) * ((k + 2 : Nat) : Int) := by
      rw [Q'.mul_den_cast, unit_den]
    rw [hLn, hLd]
    have htoNat : ((fmAconst afr fm).num.toNat : Int) = (fmAconst afr fm).num :=
      Int.toNat_of_nonneg hAnum
    have hkge : 2 * (fmAconst afr fm).num.toNat ≤ k := hk
    have hden1 : (1 : Int) ≤ ((fmAconst afr fm).den : Int) := by
      have := (fmAconst afr fm).den_pos; exact_mod_cast this
    have hstepA : (fmAconst afr fm).num * 2 ≤ ((k + 2 : Nat) : Int) := by
      have hc : (2 * (fmAconst afr fm).num.toNat : Nat) ≤ k + 2 := by omega
      have hc' : ((2 * (fmAconst afr fm).num.toNat : Nat) : Int) ≤ ((k + 2 : Nat) : Int) := by
        exact_mod_cast hc
      have heqI : ((2 * (fmAconst afr fm).num.toNat : Nat) : Int)
          = (fmAconst afr fm).num * 2 := by push_cast [htoNat]; omega
      rw [heqI] at hc'; exact hc'
    have hkpos : (0 : Int) ≤ ((k + 2 : Nat) : Int) := by exact_mod_cast Nat.zero_le _
    have hstepB : ((k + 2 : Nat) : Int)
        ≤ ((fmAconst afr fm).den : Int) * ((k + 2 : Nat) : Int) := by
      have := Int.mul_le_mul_of_nonneg_right hden1 hkpos
      rwa [Int.one_mul] at this
    exact Int.le_trans hstepA hstepB
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 h3)

/-- The shifted (tail) renormalized per-block rate `ρ_j = 1 − δ_ren(k₀+j)`. -/
def fmTailRate (afr : AFRateModulus) (fm : FullModeDefect afr) (k0 : Nat) (j : Nat) : Q' :=
  1 - fm.d (k0 + j)

/-- `lossSum (δ∘(k₀+·)) n = tailSum δ k₀ n`. -/
theorem fmLossSum_shift_eq (afr : AFRateModulus) (fm : FullModeDefect afr) (k0 : Nat) :
    ∀ n, lossSum (fun j => fm.d (k0 + j)) n = tailSum fm.d k0 n
  | 0 => rfl
  | n + 1 => by
    show lossSum (fun j => fm.d (k0 + j)) n + fm.d (k0 + n)
        = tailSum fm.d k0 n + fm.d (k0 + n)
    rw [fmLossSum_shift_eq afr fm k0 n]

/-- `1 − fmTailRate j ≃ δ_ren(k₀+j)`. -/
theorem one_sub_fmTailRate_eqv (afr : AFRateModulus) (fm : FullModeDefect afr)
    (k0 j : Nat) : ((1 : Q') - fmTailRate afr fm k0 j).eqv (fm.d (k0 + j)) :=
  one_sub_one_sub_eqv (fm.d (k0 + j))

/-- `lossSum (1 − fmTailRate) n ≃ lossSum (δ∘(k₀+·)) n`. -/
theorem fmLossSum_oneSub_eqv (afr : AFRateModulus) (fm : FullModeDefect afr) (k0 : Nat) :
    ∀ n, (lossSum (fun j => 1 - fmTailRate afr fm k0 j) n).eqv
      (lossSum (fun j => fm.d (k0 + j)) n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (lossSum (fun j => 1 - fmTailRate afr fm k0 j) n + (1 - fmTailRate afr fm k0 n)).eqv
        (lossSum (fun j => fm.d (k0 + j)) n + fm.d (k0 + n))
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (1 - fmTailRate afr fm k0 n)
        (fmLossSum_oneSub_eqv afr fm k0 n))
      (Q'.add_eqv_congr_left _ _ _ (one_sub_fmTailRate_eqv afr fm k0 n))

/-- The tail total-defect bound `R(k₀) = D·pot 2 k₀`. -/
def fmTailR (afr : AFRateModulus) (fm : FullModeDefect afr) (k0 : Nat) : Q' :=
  fmAconst afr fm * pot 2 (by decide) k0

/-- `lossSum (1 − fmTailRate) n ≤ R(k₀)` for all `n`. -/
theorem fmLossSum_tailRate_le (afr : AFRateModulus) (fm : FullModeDefect afr)
    (k0 n : Nat) :
    lossSum (fun j => 1 - fmTailRate afr fm k0 j) n ≤ fmTailR afr fm k0 := by
  have heqv : (lossSum (fun j => 1 - fmTailRate afr fm k0 j) n).eqv
      (tailSum fm.d k0 n) := by
    refine Q'.eqv_trans _ _ _ (fmLossSum_oneSub_eqv afr fm k0 n) ?_
    exact Q'.eqv_of_eq (fmLossSum_shift_eq afr fm k0 n)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv) ?_
  exact fmDefect_summable afr fm k0 n

/-! ## 5. THE FULL-MODE CHAIN CAPSTONE -/

/-- **THE FULL-MODE CHAIN CAPSTONE.**  Along ANY AF rate `afr`, and given the
assembled full-mode scalar defect `fm` (which carries the clean scalar-A bound
`δ_ren(w_k) ≤ M·(1−w_k)²` — i.e. the uniform-moment residual is inhabited as
`fm.M` / `fm.d_quad`), the running product of the renormalized FULL-MODE per-block
rates `ρ_j = 1 − δ_ren(w_{k₀+j})` over the tail `k ≥ k₀` has a STRICTLY POSITIVE
floor: there is a constructive-real `floor` with a positive rational lower bound
`ε > 0`, and `floor ≤ ∏_{j<n} ρ_j` for every prefix `n`.

This composes (full-mode analogue of `SummabilityCapstone.renormalized_gap_of_AFRate`):
clean scalar-A bound (`fm.d_quad`) ⇒ inverse-square per-step (`fmDefect_invSq`)
⇒ summable (`fmDefect_summable`) ⇒ exponential product floor `e^{−2R} > 0`
(`sum_loss_to_productFloor_exp`).

SCOPE: full-mode (all `s`) scalar defect; `s = 1`-MATCHED renormalization; finite
fusion degree (the moment cutoff `N₀`); tail `k ≥ k₀`; AF rate the named two-loop
input; and the uniform-moment residual carried by `fm.M`/`fm.d_quad`. -/
def fullMode_gap_of_AFRate (afr : AFRateModulus) (fm : FullModeDefect afr) :
    Σ' (floor : CReal) (ε : Q'),
      (0 : Q') < ε ∧ ExpPos.geRat floor ε
      ∧ ∀ n, CReal.leRat floor
          (RGGapPersistence.prodPrefix (fmTailRate afr fm (fmCutoff afr fm)) n) := by
  let k0 := fmCutoff afr fm
  -- tail rates: 0 ≤ ρ_j ≤ 1, and 1 − ρ_j ≤ 1/2.
  have hρ0 : ∀ j, (0 : Q') ≤ fmTailRate afr fm k0 j := by
    intro j
    show (0 : Q') ≤ 1 - fm.d (k0 + j)
    have hhalf : fm.d (k0 + j) ≤ HalfPow.half := fmDefect_le_half afr fm (by omega)
    have hle1 : fm.d (k0 + j) ≤ 1 := Q'.le_trans' _ _ _ hhalf (by decide)
    have hstep := Q'.add_le_add_right (fm.d (k0 + j)) 1 (-(fm.d (k0 + j))) hle1
    refine Q'.le_trans' _ _ _ ?_ hstep
    exact Q'.ge_of_eqv (Q'.add_neg_self_eqv (fm.d (k0 + j)))
  have hρ1 : ∀ j, fmTailRate afr fm k0 j ≤ 1 := by
    intro j
    show (1 : Q') - fm.d (k0 + j) ≤ 1
    have hnn : (0 : Q') ≤ fm.d (k0 + j) := fm.d_nonneg (k0 + j)
    have hnegle : (-(fm.d (k0 + j))) ≤ (0 : Q') := by
      have h : (0 : Q') + (-(fm.d (k0 + j)))
          ≤ fm.d (k0 + j) + (-(fm.d (k0 + j))) :=
        Q'.add_le_add_right 0 (fm.d (k0 + j)) (-(fm.d (k0 + j))) hnn
      refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.add_neg_self_eqv (fm.d (k0 + j)))))
      exact Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (-(fm.d (k0 + j)))))
    show (1 : Q') + (-(fm.d (k0 + j))) ≤ 1
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ 0 hnegle) ?_
    exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1))
  have hρhalf : ∀ j, (1 - fmTailRate afr fm k0 j) ≤ HalfPow.half := by
    intro j
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (one_sub_fmTailRate_eqv afr fm k0 j)) ?_
    exact fmDefect_le_half afr fm (by omega)
  exact sum_loss_to_productFloor_exp (fmTailRate afr fm k0) hρ0 hρ1 hρhalf
    (fmTailR afr fm k0) (fmLossSum_tailRate_le afr fm k0)

/-! ## 6. Doc-section — the full chain and the EXACT residual (CRITICAL honesty)

THE FULL CHAIN ASSEMBLED HERE:

  Theorem A (scalar, full-mode):  δ_ren  =  (1−w)²·(Casimir-square moment)
    [`fullMode_defect_quadratic_factor` / `momentSum_sq_factor`], AND
    δ_ren  ≤  momentM sqPoly q r S  (the moment bound, `fullMode_defect_scalar_bound`).
    GIVEN a uniform Casimir-square moment `M`, δ_ren ≤ M·(1−w)²
    [`fullMode_defect_clean_quadratic`].
  →  inverse-square per-step  δ_ren(w_k) ≤ D·1/(k+2)²  [`fmDefect_invSq`]
  →  summable  ∑ δ_ren ≤ D/(N+1)  [`fmDefect_summable`]
  →  exponential product floor  ∏ ρ_k ≥ e^{−2R} > 0  [`fullMode_gap_of_AFRate`].

THE ONE REMAINING QUANTITATIVE RESIDUAL — moment uniformity (exact):

  The scalar-A bound is δ_ren = (1−w)²·casimirSqSum.  The clean `δ_ren ≤ C·τ²`
  (`α = 0`) holds iff casimirSqSum is bounded UNIFORMLY in `w` as `w → 1`.
  `moment_bound`'s constant `momentM P q r S` is `w`-independent for a FIXED
  cutoff `S`; covering `w → 1` needs the moving cutoff `S = S(w) ≍ τ^{−1/2}`,
  whose head term inflates `momentM` to `M(w) ≍ τ^{−α}`, giving
  `δ_ren ≤ C·τ^{2−α}`.  Summability along the `1/k` AF rate needs `2 − α > 1`,
  i.e. `α < 1`.  The heat-kernel SCALING is designed so the active-mode count
  is offset by the `μ_τ` Gaussian decay (intended `α = 0`).  This module does
  NOT prove `α = 0`; it carries the uniform moment as the hypothesis `fm.M` /
  `fm.d_quad` (equivalently `hMoment` in `fullMode_defect_clean_quadratic`).
  Inhabiting that — proving casimirSqSum uniform — is the residual.

SCOPE / RESTRICTIONS (each load-bearing, none hidden):
  (i)   `modeDefect` is the `s = 1`-MATCHED renormalized residual (proved
        quadratic for ALL modes, not separately re-matched per mode).
  (ii)  FINITE fusion degree (the moment cutoff `N₀`).
  (iii) TAIL `k ≥ k₀ = fmCutoff` — the finite head is honestly excluded.
  (iv)  AF rate the NAMED two-loop input (`AFRateModulus`).
  (v)   The uniform-moment residual (`α = 0`, or `α < 1` with the `τ^{2−α}`
        series) is carried as `fm.M`/`fm.d_quad`, NOT proved.

This is the full-mode chain ASSEMBLED, conditional on those named/quantitative
residuals — NOT a 4D Yang–Mills mass-gap proof. -/

end YMGap.Continuum.FullModeAssembly

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FullModeAssembly.sqPoly_nonneg
#print axioms YMGap.Continuum.FullModeAssembly.Peval_sqPoly_eqv
#print axioms YMGap.Continuum.FullModeAssembly.casimirSqTerm_nonneg
#print axioms YMGap.Continuum.FullModeAssembly.casimirSqSum_nonneg
#print axioms YMGap.Continuum.FullModeAssembly.momentTerm_sqPoly_factor
#print axioms YMGap.Continuum.FullModeAssembly.momentSum_sq_factor
#print axioms YMGap.Continuum.FullModeAssembly.fullMode_defect_scalar_bound
#print axioms YMGap.Continuum.FullModeAssembly.fullMode_defect_quadratic_factor
#print axioms YMGap.Continuum.FullModeAssembly.fullMode_defect_clean_quadratic
#print axioms YMGap.Continuum.FullModeAssembly.fmAconst_nonneg
#print axioms YMGap.Continuum.FullModeAssembly.fmDefect_invSq
#print axioms YMGap.Continuum.FullModeAssembly.fmDefect_summable
#print axioms YMGap.Continuum.FullModeAssembly.fmDefect_le_half
#print axioms YMGap.Continuum.FullModeAssembly.fmLossSum_tailRate_le
#print axioms YMGap.Continuum.FullModeAssembly.fullMode_gap_of_AFRate
