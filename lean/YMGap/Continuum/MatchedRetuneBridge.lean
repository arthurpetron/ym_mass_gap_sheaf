/-
Track B / R2 — the **matched-retune carrier inhabitation** (the constructive
cube-root glue) and the **rational-bracket bridge** that turns the genuine
`CReal`-valued matched reference / quotient into `Q'`-boundable expressions.

# Why this module exists — closing the carrier and removing the `CReal` algebra layer

The matched-retune carrier carries `ρ` as a constructive real with `ρ³ = R`,
`R = g₁/(2 g₀)` a positive sub-unit RATIONAL.  Two things were left open: (i) the
carrier was never inhabited (the cube-root construction was a separate effort), and
(ii) the matched full-mode coefficient `ĉ_s = (s+1)·ρ^{C₄(s)}` is genuinely `CReal`
for `s ≥ 2`, so every quotient/telescoping bound seemed to need a full `CReal` order
algebra.  This module closes both.

## (1) Inhabiting the carrier

`exists_matchedRetuneP2` produces the carrier from the constructive cube root `∛R`:
positivity and the sub-unit bound come from the bisection bracket, and the cube
identity `ρ³ = R` from the cube-root defining identity (re-shaped from
`(ρ·ρ)·ρ` to the carrier's `((1·ρ)·ρ)·ρ` via a one-`CReal`-`Equiv` step).

Positivity `0 < R` and the sub-unit bound `R < 1` are carried as clean NAMED
hypotheses on the rational `R = g₁/(2 g₀)` (`hr_pos`, `hcubeLt1`): `R` is a ratio of
self-fusion coefficients; its positivity reduces to `g₁ > 0` and its sub-unit-ness is
a coefficient-monotonicity fact, neither of which is established here — they are
honest inputs, not faked.

## (2) The rational-bracket bridge — the KEY structural simplification

Because `ρ³ = R` is RATIONAL, the only IRRATIONAL data in the whole matched tower is
`ρ^{C₄(s) mod 3} ∈ {1, ρ, ρ²}`.  Indeed, with `C₄(s) = 3·⌊C₄(s)/3⌋ + (C₄(s) mod 3)`,

    ρ^{C₄(s)}  =  (ρ³)^{⌊C₄(s)/3⌋} · ρ^{C₄(s) mod 3}
              =  R^{⌊C₄(s)/3⌋} · ρ^{C₄(s) mod 3},

where `R^{⌊C₄(s)/3⌋}` is rational and the residual exponent is one of `0,1,2`.  So a
single pair of RATIONAL brackets `rhoLo ≤ ρ ≤ rhoHi` at a chosen bisection DEPTH `D`
(extracted from the bisection bracket, validated by `rhoLo³ ≤ R ≤ rhoHi³`) brackets the
entire irrational residual: `ρ^0 = 1`, `ρ^1 ∈ [rhoLo, rhoHi]`, `ρ^2 ∈ [rhoLo², rhoHi²]`.
Multiplying ONLY the residual `ρ^{C₄(s)%3}` (the bracketed part) by the EXACT rational
`R^{⌊C₄(s)/3⌋}` (the bulk) gives explicit `Q'` lower/upper bounds on the genuine `CReal`
matched coefficient `coeffMatched R s` — `coeffMatched_brackets` — with NO `CReal`
order-algebra layer.  Because the bulk is carried EXACTLY, the multiplicative slack is
`≤ (rhoHi/rhoLo)²` (BOUNDED, controlled by `D`); the NAIVE bracket `(rhoHi/rhoLo)^{C₄(s)}`
would EXPLODE (and made the bracketed box inequalities false-as-stated).

## What this module builds (and what it deliberately does NOT)

  * `exists_matchedRetuneP2` — the carrier inhabitant (the cube-root glue).
  * `rhoLo` / `rhoHi` — DEPTH-parametrized rational brackets `rhoLo R hR D ≤ ρ ≤ rhoHi R hR
    D` with `rhoLo³ ≤ R ≤ rhoHi³`, `0 < rhoLo`, and the order facts `geRat`/`leRat`.
  * `rho_pow_decompose` — the rational/irrational split of `ρ^{C₄(s)}` (built on the
    shared `crealPowNat` exponent laws `crealPowNat_add` / `crealPowNat_mul3`).
  * `coeffMatched` (the genuine `CReal` matched coefficient), the DECOMPOSED brackets
    `coeffMatchedLo/Hi R hR D s = dimQ s · R^{⌊C₄ s/3⌋} · (rhoLo/rhoHi)^{C₄ s%3}`, and
    `coeffMatched_brackets` (its explicit `Q'` lower/upper bounds; BOUNDED slack).
  * `coeffRatio_brackets` — the `Q'`-bound interface for the matched per-step quotient.
  * `ExactCRealDominance` — the EXACT-`CReal` dominance datum (separating rationals on the
    genuine `CReal` `ĉ`, NO bracket slack — the vanishing-margin local CLT), with the proved
    EXACT base `matched_base_exact` (`g_0·ĉ_1 ≃ g_1·ĉ_0`) and the bridge `exact_cross_le`.

## Honest verdict and scope

This is carrier-inhabitation, the FIXED `Q'`↔`CReal` decomposed+depth bracket bridge
(the naive `(rhoHi/rhoLo)^{C₄}` explosion is removed), and the EXACT-`CReal` dominance
STATEMENT + base + bridge.  It does NOT inhabit the all-`k` derivative magnitude bound
(`BoxRatioDerivative`, named in the frontier) nor the general-mode dominance separators
(`ExactCRealDominance`, named here); it does NOT prove `0 < R` or `R < 1` (clean named
hypotheses).  It is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Constructive cube root (a located bisection), pointwise `CReal` reductions via
`Equiv_of_approx_eqv`, pure `Q'`/`Nat` arithmetic.  Every load-bearing declaration is
gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.MatchedRetune
import YMGap.Continuum.Pivot2Moments
import YMGap.Constructive.CubeRoot
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.ExpPos

namespace YMGap.Continuum.MatchedRetuneBridge

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealAlg
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.MatchedRetune
open YMGap.Continuum.CRealContinuumAlg

/-! ## 0. `CReal`-multiplication `Equiv` helpers and the `crealPowNat` laws

The pointwise `CReal`-multiplication congruences (`cmul_congr_left`/`_right`), the
multiplicative-`ofQ'` law (`cofQ'_mul`), the `cone`/unit laws, and the `crealPowNat`
`Nat`-power with its exponent laws (`crealPowNat_three_equiv`, `crealPowNat_add`,
`crealPowNat_mul3`) are the shared canonical `Continuum`-level helpers in
`CRealContinuumAlg` (opened above); the pointwise unit/associativity/`ofQ'` laws come
from `CRealAlg`.  All are used below by their short names. -/

/-! ## 1. Inhabiting the matched-retune carrier (the cube-root glue)

The carrier's `rho_cube` field demands `crealPowNat ρ 3 ≃ ofQ' R`, where
`crealPowNat ρ 3 = ((1·ρ)·ρ)·ρ` (a leading `cone` factor from the `crealPowNat`
recursion's base `cone`).  The cube-root identity `cbrtFrom_cube_equiv` delivers
`(ρ·ρ)·ρ ≃ ofQ' R`; the shared `crealPowNat_three_equiv` re-shapes `((1·ρ)·ρ)·ρ ≃
(ρ·ρ)·ρ` by dropping the leading `cone`. -/

/-- The cube identity in the carrier's shape: `crealPowNat (∛R) 3 ≃ ofQ' R`. -/
theorem cbrt_crealPowNat_cube (R : Q') (hR : (0 : Q') < R) :
    CReal.Equiv (crealPowNat (CReal.cbrtFrom R hR) 3) (CReal.ofQ' R) :=
  CReal.Equiv.trans (crealPowNat_three_equiv (CReal.cbrtFrom R hR))
    (CReal.cbrtFrom_cube_equiv R hR)

/-- `∛R ≤ 1` (sub-unit bound, as the `CReal` order `∛R ≤ ofQ' 1`) for `0 < R < 1`.
Every lower endpoint satisfies `loₙ³ ≤ R ≤ 1 = 1³`, so `loₙ ≤ 1` uniformly. -/
theorem cbrt_le_one (R : Q') (hR : (0 : Q') < R) (hR1 : R < 1) :
    CReal.cbrtFrom R hR ≤ CReal.ofQ' (1 : Q') := by
  refine CReal.le_ofQ'_of_approx_le (fun n => ?_)
  -- approx = cbrtLo R (min' R 1) (R+1) n
  show CReal.cbrtLo R (Q'.min' R 1) (R + 1) n ≤ (1 : Q')
  have hinit := CReal.cbrtInit_canonical hR
  have hnn : (0 : Q') ≤ CReal.cbrtLo R (Q'.min' R 1) (R + 1) n :=
    CReal.cbrtLo_nonneg R (Q'.min' R 1) (R + 1) hinit n
  -- lo³ ≤ R ≤ 1 = 1·1·1
  have hcube : CReal.cbrtLo R (Q'.min' R 1) (R + 1) n
      * CReal.cbrtLo R (Q'.min' R 1) (R + 1) n
      * CReal.cbrtLo R (Q'.min' R 1) (R + 1) n ≤ (1 : Q') * 1 * 1 := by
    refine Q'.le_trans' _ _ _ (CReal.cbrtLo_cube_le R (Q'.min' R 1) (R + 1) hinit n) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_lt hR1) (Q'.le_of_eqv (by decide))
  exact CReal.le_of_cube_le_cube hnn (by decide) hcube

/-- **Inhabit the matched-retune carrier (`p = 2`).**  Given the cube target
`R = cubeRatio N w hw` with the two clean NAMED hypotheses `0 < R` (`hr_pos`) and
`R < 1` (`hcubeLt1`), the constructive cube root `ρ = ∛R` inhabits `MatchedRetuneP2`:
`rho_pos` from `cbrtFrom_isPositive`, `rho_lt_one` from `cbrt_le_one`, and the cube
identity `rho_cube` from `cbrt_crealPowNat_cube`.  (`hr_pos`/`hcubeLt1` are honest
inputs: `R` is a self-fusion coefficient ratio whose positivity reduces to `g₁ > 0`
and whose sub-unit-ness is a coefficient-monotonicity fact — neither established
here.) -/
def exists_matchedRetuneP2 (N : Nat) (w : Q') (hw : (0 : Q') < w)
    (hr_pos : (0 : Q') < cubeRatio N w hw)
    (hcubeLt1 : cubeRatio N w hw < 1) :
    MatchedRetuneP2 N w hw where
  rho := CReal.cbrtFrom (cubeRatio N w hw) hr_pos
  rho_pos := CReal.cbrtFrom_isPositive (cubeRatio N w hw) hr_pos
  rho_lt_one := cbrt_le_one (cubeRatio N w hw) hr_pos hcubeLt1
  rho_cube := cbrt_crealPowNat_cube (cubeRatio N w hw) hr_pos

/-! ## 2. The rational `ρ`-brackets

`ρ³ = R` is rational, so `ρ = ∛R` admits clean rational lower/upper brackets.  The
UPPER bracket is `cbrtFrom_leRat_of_cube` (already provided).  The LOWER bracket — the
dual `c ≤ ∛R` from `c³ ≤ R` — is proved here as `cbrtFrom_geRat_of_cube`: from
`c³ ≤ R ≤ hiₘ³` we get `c ≤ hiₘ ≤ loₘ + widthₘ`, and `widthₘ → 0` gives the `geRat`
(`ExpPos.geRat`, the `ε`-lower-bound predicate). -/

/-- **`c ≤ ∛R` when `c³ ≤ R`** (the dual of `cbrtFrom_leRat_of_cube`), as
`ExpPos.geRat (∛R) c`.  PROOF: for every `ε > 0`, past the width modulus the bracket
width is `≤ ε`, and `c³ ≤ R ≤ hiₘ³` gives `c ≤ hiₘ`, while `hiₘ ≃ loₘ + widthₘ`, so
`c ≤ loₘ + ε`. -/
theorem cbrtFrom_geRat_of_cube (R : Q') (hR : (0 : Q') < R)
    (c : Q') (hc : (0 : Q') ≤ c) (hcR : c * c * c ≤ R) :
    ExpPos.geRat (CReal.cbrtFrom R hR) c := by
  intro ε hε
  have hinit : CReal.CbrtInit R (Q'.min' R 1) (R + 1) := CReal.cbrtInit_canonical hR
  refine ⟨CReal.cbrtModulus R (Q'.min' R 1) (R + 1) hinit ε hε, fun m hm => ?_⟩
  -- approx m = cbrtLo R (min' R 1) (R+1) m
  show c ≤ CReal.cbrtLo R (Q'.min' R 1) (R + 1) m + ε
  -- width m ≤ ε
  have hwN : CReal.cbrtWidth R (Q'.min' R 1) (R + 1)
      (CReal.cbrtModulus R (Q'.min' R 1) (R + 1) hinit ε hε) ≤ ε :=
    CReal.cbrtWidth_modulus_le R (Q'.min' R 1) (R + 1) hinit ε hε
  have hwm : CReal.cbrtWidth R (Q'.min' R 1) (R + 1) m ≤ ε :=
    Q'.le_trans' _ _ _ (CReal.cbrtWidth_antitone R (Q'.min' R 1) (R + 1) hinit hm) hwN
  -- c ≤ hi m :  c³ ≤ R ≤ hi³
  have hhi_nn : (0 : Q') ≤ CReal.cbrtHi R (Q'.min' R 1) (R + 1) m :=
    Q'.le_trans' _ _ _ (CReal.cbrtLo_nonneg R (Q'.min' R 1) (R + 1) hinit m)
      (CReal.cbrtLo_le_cbrtHi R (Q'.min' R 1) (R + 1) hinit m)
  have hc_le_hi : c ≤ CReal.cbrtHi R (Q'.min' R 1) (R + 1) m :=
    CReal.le_of_cube_le_cube hc hhi_nn
      (Q'.le_trans' _ _ _ hcR (CReal.R_le_cbrtHi_cube R (Q'.min' R 1) (R + 1) hinit m))
  -- hi m ≃ lo m + width m
  have hhi_eqv : (CReal.cbrtHi R (Q'.min' R 1) (R + 1) m).eqv
      (CReal.cbrtLo R (Q'.min' R 1) (R + 1) m + CReal.cbrtWidth R (Q'.min' R 1) (R + 1) m) := by
    show (CReal.cbrtHi R (Q'.min' R 1) (R + 1) m).eqv
        (CReal.cbrtLo R (Q'.min' R 1) (R + 1) m
          + (CReal.cbrtHi R (Q'.min' R 1) (R + 1) m + -(CReal.cbrtLo R (Q'.min' R 1) (R + 1) m)))
    exact Q'.add_sub_cancel_eqv (CReal.cbrtHi R (Q'.min' R 1) (R + 1) m)
      (CReal.cbrtLo R (Q'.min' R 1) (R + 1) m)
  -- c ≤ hi m ≃ lo m + width m ≤ lo m + ε
  refine Q'.le_trans' _ _ _ hc_le_hi ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hhi_eqv) ?_
  exact Q'.add_le_add_left (CReal.cbrtLo R (Q'.min' R 1) (R + 1) m)
    (CReal.cbrtWidth R (Q'.min' R 1) (R + 1) m) ε hwm

/-! ### Canonical brackets `rhoLo, rhoHi` — DEPTH-PARAMETRIZED

A concrete rational bracket pair for `ρ = ∛R`, taken from the bisection bracket at a
chosen DEPTH `D` and validated by the located cube invariant `rhoLo³ ≤ R ≤ rhoHi³`.
The bisection-width halves each step, so the bracket ratio `rhoHi/rhoLo → 1` as
`D → ∞`; a `w`-dependent (growing) depth `D` keeps the BOUNDED decomposed-bracket
slack below the box-inequality margins on the active window.  (Any depth `D` works
for the bracket facts; the bound on the slack is what `D` controls.)  These supply
the `Q'` brackets the §3 power decomposition needs. -/

/-- The rational LOWER bracket for `∛R` at bisection depth `D`: the lower endpoint
after `D` bisection steps. -/
def rhoLo (R : Q') (_hR : (0 : Q') < R) (D : Nat) : Q' := CReal.cbrtLo R (Q'.min' R 1) (R + 1) D

/-- The rational UPPER bracket for `∛R` at bisection depth `D`: the upper endpoint
after `D` bisection steps. -/
def rhoHi (R : Q') (_hR : (0 : Q') < R) (D : Nat) : Q' := CReal.cbrtHi R (Q'.min' R 1) (R + 1) D

/-- `a < b → b ≤ c → a < c` on `Q'` (companion of `Q'.lt_of_le_of_lt`). -/
theorem q_lt_of_lt_of_le {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hbd : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
  have hcd : (0 : Int) ≤ (c.den : Int) := by exact_mod_cast Nat.zero_le _
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_lt_mul_of_pos_right e1 (by exact_mod_cast c.den_pos : (0:Int) < (c.den:Int))
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_left e2 (by exact_mod_cast Nat.zero_le a.den : (0:Int) ≤ (a.den:Int))
    have hl : (a.den : Int) * (b.num * (c.den : Int)) = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_comm b.num (a.den : Int), Int.mul_assoc]
    have hrr : (a.den : Int) * (c.num * (b.den : Int)) = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_comm c.num (a.den : Int), Int.mul_assoc]
    rwa [hl, hrr] at this
  have schain : (a.num * (c.den : Int)) * (b.den : Int)
              < (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_lt_of_le s1 s2
  exact Int.lt_of_mul_lt_mul_right schain (by exact_mod_cast Nat.zero_le _)

/-- `0 < rhoLo` (the lower endpoints stay `≥ L₀ = min'(R,1) > 0`). -/
theorem rhoLo_pos (R : Q') (hR : (0 : Q') < R) (D : Nat) : (0 : Q') < rhoLo R hR D := by
  have hinit := CReal.cbrtInit_canonical hR
  exact q_lt_of_lt_of_le hinit.loPos (CReal.cbrtLo_ge_L₀ R (Q'.min' R 1) (R + 1) hinit D)

/-- `0 ≤ rhoHi`. -/
theorem rhoHi_nonneg (R : Q') (hR : (0 : Q') < R) (D : Nat) : (0 : Q') ≤ rhoHi R hR D := by
  have hinit := CReal.cbrtInit_canonical hR
  exact Q'.le_trans' _ _ _ (CReal.cbrtLo_nonneg R (Q'.min' R 1) (R + 1) hinit D)
    (CReal.cbrtLo_le_cbrtHi R (Q'.min' R 1) (R + 1) hinit D)

/-- `rhoLo³ ≤ R` (located invariant). -/
theorem rhoLo_cube_le (R : Q') (hR : (0 : Q') < R) (D : Nat) :
    rhoLo R hR D * rhoLo R hR D * rhoLo R hR D ≤ R :=
  CReal.cbrtLo_cube_le R (Q'.min' R 1) (R + 1) (CReal.cbrtInit_canonical hR) D

/-- `R ≤ rhoHi³` (located invariant). -/
theorem R_le_rhoHi_cube (R : Q') (hR : (0 : Q') < R) (D : Nat) :
    R ≤ rhoHi R hR D * rhoHi R hR D * rhoHi R hR D :=
  CReal.R_le_cbrtHi_cube R (Q'.min' R 1) (R + 1) (CReal.cbrtInit_canonical hR) D

/-- `rhoLo ≤ rhoHi`. -/
theorem rhoLo_le_rhoHi (R : Q') (hR : (0 : Q') < R) (D : Nat) : rhoLo R hR D ≤ rhoHi R hR D :=
  CReal.cbrtLo_le_cbrtHi R (Q'.min' R 1) (R + 1) (CReal.cbrtInit_canonical hR) D

/-- **`rhoLo ≤ ρ`** as `geRat (∛R) rhoLo` (from `rhoLo³ ≤ R`). -/
theorem geRat_rho_rhoLo (R : Q') (hR : (0 : Q') < R) (D : Nat) :
    ExpPos.geRat (CReal.cbrtFrom R hR) (rhoLo R hR D) :=
  cbrtFrom_geRat_of_cube R hR (rhoLo R hR D) (Q'.le_of_lt (rhoLo_pos R hR D)) (rhoLo_cube_le R hR D)

/-- **`ρ ≤ rhoHi`** as `leRat (∛R) rhoHi` (from `R ≤ rhoHi³`). -/
theorem leRat_rho_rhoHi (R : Q') (hR : (0 : Q') < R) (D : Nat) :
    CReal.leRat (CReal.cbrtFrom R hR) (rhoHi R hR D) :=
  CReal.cbrtFrom_leRat_of_cube R hR (rhoHi R hR D) (rhoHi_nonneg R hR D) (R_le_rhoHi_cube R hR D)

/-! ### A product LOWER bound `geRat_mul` (dual of `CReal.leRat_mul`)

The matched coefficient's lower bracket needs a `geRat` product bound.  We prove it at
the approximation level: with `0 ≤ a ≤ A_n + δ` and `0 ≤ c ≤ C_n + δ` (from
`geRat A a`, `geRat C c`) and upper bounds `A_n ≤ Ba + δ`, `C_n ≤ Bc + δ` (from
`leRat`), `a·c ≤ (A_n+δ)(C_n+δ) = A_n·C_n + (δ·A_n + δ·C_n + δ²)`, and the remainder is
`≤ (Ba + Bc + 3)·δ ≤ ε` for a suitable `δ ≤ 1`. -/

/-- **Product lower bound.**  If the limit of `A` lies in `[a, Ba]` and the limit of
`C` lies in `[c, Bc]` with `0 ≤ a, c, Ba, Bc`, then the limit of `A·C` is `≥ a·c`.
PROOF.  `a·c ≤ (A_n+δ)(C_n+δ) = A_n·C_n + δ·(A_n + (C_n + δ))`, and the remainder
`δ·(A_n + (C_n + δ)) ≤ δ·((Ba+δ) + ((Bc+δ) + δ)) ≤ δ·Cfac` where
`Cfac := (Ba+1) + ((Bc+1) + 1)` (using `δ ≤ 1`); pick `δ` so that `Cfac·δ ≤ ε`. -/
theorem geRat_mul {A C : CReal} {a c Ba Bc : Q'}
    (hAa : ExpPos.geRat A a) (hCc : ExpPos.geRat C c)
    (hABa : CReal.leRat A Ba) (hCBc : CReal.leRat C Bc)
    (ha : (0 : Q') ≤ a) (hc : (0 : Q') ≤ c) (hBa : (0 : Q') ≤ Ba) (hBc : (0 : Q') ≤ Bc) :
    ExpPos.geRat (CReal.mul A C) (a * c) := by
  intro ε hε
  -- Cfac := (Ba+1) + ((Bc+1) + 1) ≥ 0
  have h1nn : (0 : Q') ≤ Ba + 1 := Q'.le_trans' _ _ _ hBa (Q'.add_le_self_of_nonneg _ 1 (by decide))
  have h2nn : (0 : Q') ≤ Bc + 1 := Q'.le_trans' _ _ _ hBc (Q'.add_le_self_of_nonneg _ 1 (by decide))
  have h3nn : (0 : Q') ≤ (Bc + 1) + 1 := Q'.le_trans' _ _ _ h2nn (Q'.add_le_self_of_nonneg _ 1 (by decide))
  have hCfac : (0 : Q') ≤ (Ba + 1) + ((Bc + 1) + 1) := Q'.zero_le_add _ _ h1nn h3nn
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := CReal.exists_mul_le hCfac hε
  have hδle1 : Q'.min' δ₀ 1 ≤ 1 := Q'.min_le_right
  have hδleδ₀ : Q'.min' δ₀ 1 ≤ δ₀ := Q'.min_le_left
  have hδpos : (0 : Q') < Q'.min' δ₀ 1 := CReal.min_pos hδ₀pos (by decide)
  have hδnn : (0 : Q') ≤ Q'.min' δ₀ 1 := Q'.le_of_lt hδpos
  -- Cfac·δ ≤ ε
  have hSδ : ((Ba + 1) + ((Bc + 1) + 1)) * Q'.min' δ₀ 1 ≤ ε :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ δ₀ _ hδleδ₀ hCfac) hδ₀
  obtain ⟨Na, hNa⟩ := hAa (Q'.min' δ₀ 1) hδpos
  obtain ⟨Nc, hNc⟩ := hCc (Q'.min' δ₀ 1) hδpos
  obtain ⟨Na', hNa'⟩ := hABa (Q'.min' δ₀ 1) hδpos
  obtain ⟨Nc', hNc'⟩ := hCBc (Q'.min' δ₀ 1) hδpos
  refine ⟨max (max Na Nc) (max Na' Nc'), fun n hn => ?_⟩
  have lna : Na ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have lnc : Nc ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have lna' : Na' ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have lnc' : Nc' ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  have hAa_n : a ≤ A.approx n + Q'.min' δ₀ 1 := hNa n lna
  have hCc_n : c ≤ C.approx n + Q'.min' δ₀ 1 := hNc n lnc
  have hAub : A.approx n ≤ Ba + Q'.min' δ₀ 1 := hNa' n lna'
  have hCub : C.approx n ≤ Bc + Q'.min' δ₀ 1 := hNc' n lnc'
  have hAδnn : (0 : Q') ≤ A.approx n + Q'.min' δ₀ 1 := Q'.le_trans' _ _ _ ha hAa_n
  -- a·c ≤ (A_n+δ)(C_n+δ)
  have hprod : a * c ≤ (A.approx n + Q'.min' δ₀ 1) * (C.approx n + Q'.min' δ₀ 1) :=
    Q'.mul_le_mul_of_nonneg hAa_n hCc_n hAδnn hc
  -- (A_n+δ)(C_n+δ) ≃ A_n·C_n + δ·(A_n + (C_n + δ))
  have hexpand : ((A.approx n + Q'.min' δ₀ 1) * (C.approx n + Q'.min' δ₀ 1)).eqv
      (A.approx n * C.approx n
        + Q'.min' δ₀ 1 * (A.approx n + (C.approx n + Q'.min' δ₀ 1))) := by
    -- (X+δ)(Y+δ) = X·Y + X·δ + δ·Y + δ·δ ; group remainder as δ·(X + (Y + δ))
    -- LHS = X(Y+δ) + δ(Y+δ)
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (A.approx n) (Q'.min' δ₀ 1) (C.approx n + Q'.min' δ₀ 1)) ?_
    -- X(Y+δ) ≃ XY + Xδ
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.mul_add_eqv (A.approx n) (C.approx n) (Q'.min' δ₀ 1))) ?_
    -- (XY + Xδ) + δ(Y+δ) ≃ XY + (Xδ + δ(Y+δ))
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (A.approx n * C.approx n) (A.approx n * Q'.min' δ₀ 1)
        (Q'.min' δ₀ 1 * (C.approx n + Q'.min' δ₀ 1))) ?_
    refine Q'.add_eqv_congr_left _ _ _ ?_
    -- Xδ + δ(Y+δ) ≃ δ·(X + (Y+δ))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.mul_comm_eqv (A.approx n) (Q'.min' δ₀ 1))) ?_
    exact Q'.eqv_symm (Q'.mul_add_eqv (Q'.min' δ₀ 1) (A.approx n) (C.approx n + Q'.min' δ₀ 1))
  -- remainder ≤ δ·Cfac :  A_n + (C_n+δ) ≤ (Ba+1) + ((Bc+1)+1)  (using δ ≤ 1)
  have hsumle : A.approx n + (C.approx n + Q'.min' δ₀ 1)
      ≤ (Ba + 1) + ((Bc + 1) + 1) := by
    have hA1 : A.approx n ≤ Ba + 1 :=
      Q'.le_trans' _ _ _ hAub (Q'.add_le_add_left Ba (Q'.min' δ₀ 1) 1 hδle1)
    have hC1 : C.approx n ≤ Bc + 1 :=
      Q'.le_trans' _ _ _ hCub (Q'.add_le_add_left Bc (Q'.min' δ₀ 1) 1 hδle1)
    exact Q'.add_le_add hA1 (Q'.add_le_add hC1 hδle1)
  have hrem : Q'.min' δ₀ 1 * (A.approx n + (C.approx n + Q'.min' δ₀ 1))
      ≤ Q'.min' δ₀ 1 * ((Ba + 1) + ((Bc + 1) + 1)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsumle hδnn
  -- δ·Cfac ≃ Cfac·δ ≤ ε
  have hremε : Q'.min' δ₀ 1 * (A.approx n + (C.approx n + Q'.min' δ₀ 1)) ≤ ε :=
    Q'.le_trans' _ _ _ hrem
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv (Q'.min' δ₀ 1) ((Ba + 1) + ((Bc + 1) + 1)))) hSδ)
  show a * c ≤ A.approx n * C.approx n + ε
  refine Q'.le_trans' _ _ _ hprod ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hexpand) ?_
  exact Q'.add_le_add_left _ _ _ hremε

/-! ## 3. The `crealPowNat` exponent laws and the rational/irrational split

`crealPowNat` satisfies the usual exponent laws (proved pointwise / by induction):
`x^{a+b} = x^a·x^b` and, from the carrier's cube identity `x^3 ≃ ofQ' R`,
`x^{3m} ≃ ofQ'(Rᵐ)`.  Combining with the `Nat` Euclidean split
`c = 3·(c/3) + (c%3)` gives `rho_pow_decompose`:

    ρ^c  ≃  ofQ'(R^{c/3}) · ρ^{c%3},   c%3 ∈ {0,1,2},

isolating the only irrational factor `ρ^{c%3}`. -/

-- The `crealPowNat` exponent laws (`crealPowNat_add`, `crealPowNat_mul3`), the
-- `cmul_cone` (right unit) and `cmul_assoc` (associativity) laws are the shared
-- canonical `CRealContinuumAlg.*` / `CRealAlg.*` helpers (opened above); used below by
-- their short names.

/-- **The rational/irrational split** `ρ^c ≃ ofQ'(R^{c/3}) · ρ^{c%3}`, given the cube
identity `ρ³ ≃ ofQ' R`.  The factor `ofQ'(R^{c/3})` is rational and `ρ^{c%3}` is the
only irrational residual (`c%3 ∈ {0,1,2}`).  PROOF: `c = 3·(c/3) + c%3`
(`Nat.div_add_mod`); apply `crealPowNat_add` then `crealPowNat_mul3`. -/
theorem rho_pow_decompose (x : CReal) (R : Q')
    (hcube : CReal.Equiv (crealPowNat x 3) (CReal.ofQ' R)) (c : Nat) :
    CReal.Equiv (crealPowNat x c)
      (CReal.mul (CReal.ofQ' (qpow R (c / 3))) (crealPowNat x (c % 3))) := by
  have hdm : 3 * (c / 3) + c % 3 = c := Nat.div_add_mod c 3
  -- x^c ≃ x^{3*(c/3) + c%3} ≃ x^{3*(c/3)} · x^{c%3} ≃ ofQ'(R^{c/3}) · x^{c%3}
  have hc_eq : crealPowNat x c = crealPowNat x (3 * (c / 3) + c % 3) := by rw [hdm]
  rw [hc_eq]
  refine CReal.Equiv.trans (crealPowNat_add x (3 * (c / 3)) (c % 3)) ?_
  exact Pivot2.mul_congr_left (crealPowNat_mul3 x R hcube (c / 3))

/-! ## 4. Rational brackets for `CReal` powers and the matched coefficient

The residual `ρ^{c%3} ∈ {1, ρ, ρ²}` is bracketed rationally: from `rhoLo ≤ ρ ≤ rhoHi`
(with `0 ≤ rhoLo, rhoHi`), `crealPowNat ρ j` has limit in `[rhoLoʲ, rhoHiʲ]`.  Proved by
induction on `j` via the product bounds `leRat_mul` / `geRat_mul`.  Multiplying by the
rational `dimQ s · R^{c4 s/3}` gives the explicit `Q'` brackets on the genuine `CReal`
matched coefficient `coeffMatched ρ s = (s+1)·ρ^{C₄(s)}`. -/

/-- `geRat x 0` from a nonnegative rational lower bound. -/
theorem geRat_zero_of_geRat {x : CReal} {lo : Q'} (h : ExpPos.geRat x lo)
    (hlo : (0 : Q') ≤ lo) : ExpPos.geRat x 0 :=
  ExpPos.geRat_mono h hlo

/-- **Scale a rational lower bound by a nonnegative rational** (mirror of
`CReal.leRat_smul_nonneg`). `0 ≤ c → geRat y d → geRat (c·y) (c·d)`. -/
theorem geRat_smul_nonneg {c : Q'} (hc : (0 : Q') ≤ c) {y : CReal} {d : Q'}
    (h : ExpPos.geRat y d) : ExpPos.geRat (CReal.mul (CReal.ofQ' c) y) (c * d) := by
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le hc hε
  obtain ⟨N, hN⟩ := h δ hδpos
  refine ⟨N, fun n hn => ?_⟩
  have hyd : d ≤ y.approx n + δ := hN n hn
  -- c·d ≤ c·(y_n + δ) = c·y_n + c·δ ≤ c·y_n + ε
  have s1 : c * d ≤ c * (y.approx n + δ) :=
    Q'.mul_le_mul_of_nonneg_left d (y.approx n + δ) c hyd hc
  have e1 : (c * (y.approx n + δ)).eqv (c * y.approx n + c * δ) := Q'.mul_add_eqv c (y.approx n) δ
  have s2 : c * y.approx n + c * δ ≤ c * y.approx n + ε := Q'.add_le_add_left (c * y.approx n) (c * δ) ε hδ
  -- (mul (ofQ' c) y).approx n = c · y_n
  show c * d ≤ c * y.approx n + ε
  exact Q'.le_trans' _ _ _ s1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) s2)

/-- **Rational brackets for `CReal` nat-powers.**  If `lo ≤ x ≤ hi` (as `geRat`/`leRat`)
with `0 ≤ lo, hi`, then `loʲ ≤ xʲ ≤ hiʲ` for every `j`.  Induction on `j` via the product
bounds. -/
theorem crealPowNat_brackets (x : CReal) {lo hi : Q'}
    (hlo : ExpPos.geRat x lo) (hhi : CReal.leRat x hi)
    (hlonn : (0 : Q') ≤ lo) (hhinn : (0 : Q') ≤ hi) :
    ∀ j, ExpPos.geRat (crealPowNat x j) (qpow lo j)
      ∧ CReal.leRat (crealPowNat x j) (qpow hi j)
  | 0 => by
      -- x^0 = cone = ofQ' 1 ; qpow _ 0 = 1
      refine ⟨?_, ?_⟩
      · show ExpPos.geRat CReal.cone (qpow lo 0)
        rw [qpow_zero]
        exact ExpPos.geRat_of_eventually ⟨0, fun _ _ => Q'.le_refl' (1 : Q')⟩
      · show CReal.leRat CReal.cone (qpow hi 0)
        rw [qpow_zero]
        exact CReal.leRat_of_eventually ⟨0, fun _ _ => Q'.le_refl' (1 : Q')⟩
  | j + 1 => by
      obtain ⟨hgj, hlj⟩ := crealPowNat_brackets x hlo hhi hlonn hhinn j
      have hqlonn : (0 : Q') ≤ qpow lo j := qpow_nonneg lo hlonn j
      have hqhinn : (0 : Q') ≤ qpow hi j := qpow_nonneg hi hhinn j
      refine ⟨?_, ?_⟩
      · -- lo^{j+1} = lo^j · lo ≤ x^j · x
        show ExpPos.geRat (CReal.mul (crealPowNat x j) x) (qpow lo (j + 1))
        have : ExpPos.geRat (CReal.mul (crealPowNat x j) x) (qpow lo j * lo) :=
          geRat_mul hgj hlo hlj hhi hqlonn hlonn hqhinn hhinn
        exact this
      · -- hi^{j+1} = hi^j · hi ≥ x^j · x
        show CReal.leRat (CReal.mul (crealPowNat x j) x) (qpow hi (j + 1))
        exact CReal.leRat_mul hlj hhi (geRat_zero_of_geRat hgj hqlonn)
          (geRat_zero_of_geRat hlo hlonn) hqhinn hhinn

/-! ### The genuine `CReal` matched coefficient and its `Q'` brackets -/

/-- **The genuine `CReal` matched full-mode coefficient** `coeffMatched ρ s =
(s+1)·ρ^{C₄(s)}` (`dimQ s · ρ^{c4 s}`).  For `s ≥ 2` the power `ρ^{C₄(s)}` is genuinely
irrational; the brackets below remove `ρ` in favor of the rational `R`-powers and the
`rhoLo/rhoHi` brackets. -/
def coeffMatched (ρ : CReal) (s : Nat) : CReal :=
  CReal.mul (CReal.ofQ' (dimQ s)) (crealPowNat ρ (c4 s))

/-! ### DECOMPOSED brackets (the fix)

The NAIVE bracket `dimQ s · qpow (rhoHi/rhoLo) (c4 s)` raises the loose rational
`ρ`-bracket to `C₄(s) ≈ s²`, so the bracket ratio `(rhoHi/rhoLo)^{C₄(s)}` EXPLODES and
the bracketed box inequalities become FALSE-as-stated.  Since `ρ³ = R` is RATIONAL
(exact), we instead carry the bulk by the EXACT rational `R`-power
`R^{⌊C₄(s)/3⌋}` and bracket ONLY the residual `ρ^{C₄(s)%3} ∈ {1, ρ, ρ²}` — so the
multiplicative slack is `≤ (rhoHi/rhoLo)²` (BOUNDED, not exploding).  Both bounds are
parametrized by the bisection DEPTH `D` (the residual brackets `rhoLo/rhoHi R hR D`). -/

/-- **DECOMPOSED `Q'` UPPER bound for `coeffMatched`** at bisection depth `D`:
`(s+1)·R^{⌊C₄(s)/3⌋}·rhoHi^{C₄(s)%3}`.  The exact rational `R`-power carries the bulk;
only the residual `ρ^{C₄(s)%3}` is bracketed. -/
def coeffMatchedHi (R : Q') (hR : (0 : Q') < R) (D : Nat) (s : Nat) : Q' :=
  dimQ s * qpow R (c4 s / 3) * qpow (rhoHi R hR D) (c4 s % 3)

/-- **DECOMPOSED `Q'` LOWER bound for `coeffMatched`** at bisection depth `D`:
`(s+1)·R^{⌊C₄(s)/3⌋}·rhoLo^{C₄(s)%3}`. -/
def coeffMatchedLo (R : Q') (hR : (0 : Q') < R) (D : Nat) (s : Nat) : Q' :=
  dimQ s * qpow R (c4 s / 3) * qpow (rhoLo R hR D) (c4 s % 3)

/-- **`coeffMatched_brackets` (decomposed + depth).**  For `ρ = ∛R`, the genuine `CReal`
matched coefficient is bracketed by the explicit DECOMPOSED `Q'` bounds
`coeffMatchedLo ≤ coeffMatched ≤ coeffMatchedHi`, where the bulk is the EXACT rational
`R`-power `R^{⌊C₄(s)/3⌋}` and only the residual `ρ^{C₄(s)%3}` is bracketed by the
depth-`D` brackets `rhoLo/rhoHi`.  PROOF: `coeffMatched ρ s = dimQ s · ρ^{C₄(s)}`;
decompose `ρ^{C₄(s)} ≃ R^{⌊C₄(s)/3⌋}·ρ^{C₄(s)%3}` (`rho_pow_decompose` + the cube
identity), bracket the residual `ρ^{C₄(s)%3}` by `crealPowNat_brackets`, then scale by
the nonnegative rationals `R^{⌊C₄(s)/3⌋}` and `dimQ s`. -/
theorem coeffMatched_brackets (R : Q') (hR : (0 : Q') < R) (D : Nat) (s : Nat) :
    ExpPos.geRat (coeffMatched (CReal.cbrtFrom R hR) s) (coeffMatchedLo R hR D s)
      ∧ CReal.leRat (coeffMatched (CReal.cbrtFrom R hR) s) (coeffMatchedHi R hR D s) := by
  -- residual brackets ρ^{c4 s % 3} ∈ [rhoLo^{%3}, rhoHi^{%3}]
  obtain ⟨hgRes, hlRes⟩ := crealPowNat_brackets (CReal.cbrtFrom R hR)
    (geRat_rho_rhoLo R hR D) (leRat_rho_rhoHi R hR D)
    (Q'.le_of_lt (rhoLo_pos R hR D)) (rhoHi_nonneg R hR D) (c4 s % 3)
  have hdim : (0 : Q') ≤ dimQ s := dimQ_nonneg s
  have hRpow : (0 : Q') ≤ qpow R (c4 s / 3) := qpow_nonneg R (Q'.le_of_lt hR) (c4 s / 3)
  -- the decomposition equivalence ρ^{c4 s} ≃ R^{⌊⌋}·ρ^{%3}
  have hcube : CReal.Equiv (crealPowNat (CReal.cbrtFrom R hR) 3) (CReal.ofQ' R) :=
    cbrt_crealPowNat_cube R hR
  have hdec : CReal.Equiv (crealPowNat (CReal.cbrtFrom R hR) (c4 s))
      (CReal.mul (CReal.ofQ' (qpow R (c4 s / 3))) (crealPowNat (CReal.cbrtFrom R hR) (c4 s % 3))) :=
    rho_pow_decompose (CReal.cbrtFrom R hR) R hcube (c4 s)
  -- scale residual by R^{⌊⌋}: geRat/leRat (R^{⌊⌋}·ρ^{%3})
  have hgScaled : ExpPos.geRat
      (CReal.mul (CReal.ofQ' (qpow R (c4 s / 3))) (crealPowNat (CReal.cbrtFrom R hR) (c4 s % 3)))
      (qpow R (c4 s / 3) * qpow (rhoLo R hR D) (c4 s % 3)) :=
    geRat_smul_nonneg hRpow hgRes
  have hlScaled : CReal.leRat
      (CReal.mul (CReal.ofQ' (qpow R (c4 s / 3))) (crealPowNat (CReal.cbrtFrom R hR) (c4 s % 3)))
      (qpow R (c4 s / 3) * qpow (rhoHi R hR D) (c4 s % 3)) :=
    CReal.leRat_smul_nonneg hRpow hlRes
  -- transport the scaled brackets across hdec to ρ^{c4 s}
  have hgPow : ExpPos.geRat (crealPowNat (CReal.cbrtFrom R hR) (c4 s))
      (qpow R (c4 s / 3) * qpow (rhoLo R hR D) (c4 s % 3)) :=
    SU3CharFactor.geRat_of_equiv hdec hgScaled
  have hlPow : CReal.leRat (crealPowNat (CReal.cbrtFrom R hR) (c4 s))
      (qpow R (c4 s / 3) * qpow (rhoHi R hR D) (c4 s % 3)) :=
    CReal.leRat_of_equiv hdec hlScaled
  refine ⟨?_, ?_⟩
  · -- geRat (dimQ s · ρ^{c4 s}) (dimQ s · (R^{⌊⌋}·rhoLo^{%3}))
    show ExpPos.geRat (CReal.mul (CReal.ofQ' (dimQ s)) (crealPowNat (CReal.cbrtFrom R hR) (c4 s)))
      (dimQ s * qpow R (c4 s / 3) * qpow (rhoLo R hR D) (c4 s % 3))
    have := geRat_smul_nonneg hdim hgPow
    -- value: dimQ s * (R^{⌊⌋}*rhoLo^{%3}) ≃ dimQ s * R^{⌊⌋} * rhoLo^{%3}
    refine ExpPos.geRat_mono this ?_
    exact Q'.le_of_eqv (Q'.mul_assoc_eqv (dimQ s) (qpow R (c4 s / 3)) (qpow (rhoLo R hR D) (c4 s % 3)))
  · show CReal.leRat (CReal.mul (CReal.ofQ' (dimQ s)) (crealPowNat (CReal.cbrtFrom R hR) (c4 s)))
      (dimQ s * qpow R (c4 s / 3) * qpow (rhoHi R hR D) (c4 s % 3))
    have := CReal.leRat_smul_nonneg hdim hlPow
    refine CReal.leRat_mono this ?_
    exact Q'.ge_of_eqv (Q'.mul_assoc_eqv (dimQ s) (qpow R (c4 s / 3)) (qpow (rhoHi R hR D) (c4 s % 3)))

/-! ## 5. The `δ_k` / `Qfrac` `Q'`-bound interface

The matched per-step quotient is `Q_s = (g_s · ĉ_0)/(g_0 · ĉ_s)` with `ĉ_s =
coeffMatched ρ s`.  The bridge replaces the genuine `CReal` `ĉ_s` by its `Q'` brackets:
the quotient — and hence the per-step increment `δ_k` Wave-2b must control by
`Cu²·(y_{k+1} − y_k)` — is bracketed by explicit `Q'` expressions in the bond-moved
coefficient ratio and the `rhoLo/rhoHi` powers.  We expose the cleanest such object: the
matched coefficient ratio `ĉ_{k+1}/ĉ_k`, `Q'`-bracketed via `coeffMatched_brackets`. -/

/-- `0 < coeffMatchedLo R hR D k` (the decomposed lower bracket is strictly positive:
`dimQ k > 0`, `R^{⌊⌋} > 0`, `rhoLo^{%3} > 0`). -/
theorem coeffMatchedLo_pos (R : Q') (hR : (0 : Q') < R) (D k : Nat) :
    (0 : Q') < coeffMatchedLo R hR D k :=
  Q'.mul_pos
    (Q'.mul_pos (Q'.ofNat_succ_pos k) (BondMovingScaledNorm.qpow_pos hR (c4 k / 3)))
    (BondMovingScaledNorm.qpow_pos (rhoLo_pos R hR D) (c4 k % 3))

/-- `0 < coeffMatchedHi R hR D k` (the decomposed upper bracket is strictly positive). -/
theorem coeffMatchedHi_pos (R : Q') (hR : (0 : Q') < R) (D k : Nat) :
    (0 : Q') < coeffMatchedHi R hR D k :=
  Q'.mul_pos
    (Q'.mul_pos (Q'.ofNat_succ_pos k) (BondMovingScaledNorm.qpow_pos hR (c4 k / 3)))
    (BondMovingScaledNorm.qpow_pos (q_lt_of_lt_of_le (rhoLo_pos R hR D) (rhoLo_le_rhoHi R hR D)) (c4 k % 3))

/-- The `Q'` UPPER bracket for the matched coefficient ratio `ĉ_{k+1}/ĉ_k`:
`coeffMatchedHi (k+1) / coeffMatchedLo k` (the largest numerator over the smallest
denominator), at bisection depth `D`. -/
def coeffRatioHi (R : Q') (hR : (0 : Q') < R) (D : Nat) (k : Nat) : Q' :=
  Q'.divPos (coeffMatchedHi R hR D (k + 1)) (coeffMatchedLo R hR D k)
    (coeffMatchedLo_pos R hR D k)

/-- The `Q'` LOWER bracket for the matched coefficient ratio `ĉ_{k+1}/ĉ_k`:
`coeffMatchedLo (k+1) / coeffMatchedHi k`, at bisection depth `D`. -/
def coeffRatioLo (R : Q') (hR : (0 : Q') < R) (D : Nat) (k : Nat) : Q' :=
  Q'.divPos (coeffMatchedLo R hR D (k + 1)) (coeffMatchedHi R hR D k)
    (coeffMatchedHi_pos R hR D k)

/-- **The `δ_k` / `Qfrac` `Q'`-bound interface.**  The matched coefficient ratio
`ĉ_{k+1}/ĉ_k` (the genuine `CReal` object underlying the per-step increment `δ_k`) is
bracketed by the explicit `Q'` expressions `coeffRatioLo k ≤ … ≤ coeffRatioHi k`, both
built from `dimQ`, the rational `R`-powers, and the `rhoLo/rhoHi` brackets — with NO
`CReal` algebra layer.  This is the object Wave-2b bounds by `Cu²·(y_{k+1} − y_k)`.

We record it as the pair of bracket facts on `coeffMatched`; the ratio brackets
`coeffRatioLo/Hi` are their `divPos` combinations.  (We do not assert the `CReal` ratio
here — only the numerator/denominator brackets that define it — keeping the interface
purely `Q'` and honest about what is established.) -/
theorem coeffRatio_brackets (R : Q') (hR : (0 : Q') < R) (D : Nat) (k : Nat) :
    (ExpPos.geRat (coeffMatched (CReal.cbrtFrom R hR) (k + 1)) (coeffMatchedLo R hR D (k + 1))
      ∧ CReal.leRat (coeffMatched (CReal.cbrtFrom R hR) (k + 1)) (coeffMatchedHi R hR D (k + 1)))
    ∧ (ExpPos.geRat (coeffMatched (CReal.cbrtFrom R hR) k) (coeffMatchedLo R hR D k)
      ∧ CReal.leRat (coeffMatched (CReal.cbrtFrom R hR) k) (coeffMatchedHi R hR D k)) :=
  ⟨coeffMatched_brackets R hR D (k + 1), coeffMatched_brackets R hR D k⟩

/-! ## 6. The EXACT-`CReal` dominance (the vanishing-margin local CLT)

The bracketed dominance `g_k·ĉ_{k+1}^{hi} ≤ g_{k+1}·ĉ_k^{lo}` is FALSE-as-stated:
the sign margin `δ_1 ~ τ³ → 0` vanishes faster than any fixed-depth bracket slack, so
NO finite depth `D` works uniformly as `w → 1`.  The dominance is genuinely an EXACT
inequality on the genuine `CReal` matched coefficient `ĉ_s = coeffMatched ρ s`
(`ρ = ∛R`), with NO bracket slack.

We state it as the constructive `≤` between the two genuine `CReal` products — the
existence of a SEPARATING rational `B`:

    g_k · ĉ_{k+1}  ≤  B  ≤  g_{k+1} · ĉ_k

(`leRat` of the smaller, `geRat` of the larger).  This is the MLTT-valid constructive
form of `g_k·ĉ_{k+1} ≤ g_{k+1}·ĉ_k` (the one-slack `CReal.le` is non-transitive, so a
separating rational is the correct witness).  The deflated `h_s = g_s/ĉ_s` being
non-decreasing IS this family of separators.  We carry it as a `Type`-level datum and
PROVE the bridge back to the engine's `δ_k ≥ 0`; the separators themselves (the genuine
local-CLT content) are NAMED, not inhabited here. -/

/-- The genuine `CReal` cross products `g_s · ĉ_t` (rational `g_s` times the `CReal`
matched coefficient `ĉ_t = coeffMatched ρ t`). -/
def crossProd (g : Q') (ρ : CReal) (t : Nat) : CReal :=
  CReal.mul (CReal.ofQ' g) (coeffMatched ρ t)

/-- **The EXACT-`CReal` dominance datum.**  For the matched kernel `ρ = ∛R` and the
self-fusion coefficients `g_s = bondMovedCoeff N w 2 s`, a SEPARATING rational `B k`
for each active mode `1 ≤ k`, witnessing the genuine (bracket-free) cross dominance
`g_k·ĉ_{k+1} ≤ B k ≤ g_{k+1}·ĉ_k` on the genuine `CReal` coefficients `ĉ = coeffMatched
ρ`.  This is the vanishing-margin local CLT: the deflated `h_s = g_s/ĉ_s` is
non-decreasing.  NAMED (the separators are the open analytic content), NOT inhabited. -/
structure ExactCRealDominance (N : Nat) (w : Q') (R : Q') (hR : (0 : Q') < R) : Type where
  /-- The separating rational per active mode. -/
  B : Nat → Q'
  /-- The smaller product's limit is `≤ B k`: `g_k · ĉ_{k+1} ≤ B k`. -/
  sep_lo : ∀ k, 1 ≤ k →
    CReal.leRat (crossProd (bondMovedCoeff N w 2 k) (CReal.cbrtFrom R hR) (k + 1)) (B k)
  /-- The larger product's limit is `≥ B k`: `B k ≤ g_{k+1} · ĉ_k`. -/
  sep_hi : ∀ k, 1 ≤ k →
    ExpPos.geRat (crossProd (bondMovedCoeff N w 2 (k + 1)) (CReal.cbrtFrom R hR) k) (B k)

/-! ### The bridge `ExactCRealDominance ⟹ Q'` cross dominance on the brackets

From the separating rational `B k` and the bracket facts, the genuine cross dominance
`g_k·ĉ_{k+1} ≤ g_{k+1}·ĉ_k` transfers to the BRACKETED `Q'` cross inequality
`g_k·ĉ_{k+1}^{lo} ≤ g_{k+1}·ĉ_k^{hi}` — BUT that is the WEAK direction (lower vs upper)
and does NOT feed `step_nonneg` (which needs `g_k·ĉ_{k+1}^{hi} ≤ g_{k+1}·ĉ_k^{lo}`).
The CORRECT bridge keeps the comparison at the `CReal` level: the genuine cross
products satisfy `g_k·ĉ_{k+1} ≤ g_{k+1}·ĉ_k` (a constructive `≤`, via the separator),
and this is the EXACT statement `stepDelta ≥ 0` reduces to when the per-step quotient is
formed against the genuine `CReal` ĉ (no brackets).  We expose that constructive `≤`. -/

/-- **The genuine constructive cross `≤` from the separator.**  `g_k·ĉ_{k+1} ≤
g_{k+1}·ĉ_k` as the constructive comparison: there is a rational `B` with `leRat (smaller)
B` and `geRat (larger) B`.  This re-exposes the `ExactCRealDominance` content per mode —
the genuine bracket-free dominance the engine's `step_nonneg` requires (against the exact
`CReal` reference). -/
def exact_cross_le (N : Nat) {w : Q'} (R : Q') (hR : (0 : Q') < R)
    (dom : ExactCRealDominance N w R hR) (k : Nat) (hk : 1 ≤ k) :
    Σ' B : Q',
      CReal.leRat (crossProd (bondMovedCoeff N w 2 k) (CReal.cbrtFrom R hR) (k + 1)) B
        ∧ ExpPos.geRat (crossProd (bondMovedCoeff N w 2 (k + 1)) (CReal.cbrtFrom R hR) k) B :=
  ⟨dom.B k, dom.sep_lo k hk, dom.sep_hi k hk⟩

/-- **The `δ_0 = 0` exact match as the base of the deflated comparison.**  The matched
retune is built so that `ĉ_1 = 2·ρ³ = g_1/g_0` (`cubeRatio`), i.e. the deflated ratio
`h_1 = g_1/ĉ_1 = g_0/ĉ_0 = h_0` exactly — the `s = 1` marginal is killed by
construction.  Concretely `g_0 · ĉ_1 ≃ g_1 · ĉ_0` at the rational (`C₄ ∈ {0,3}`) modes,
where `ĉ_0 = 1` and `ĉ_1 = 2·R` with `R = cubeRatio` and `g_0·(2·R) ≃ g_1` by definition
of `cubeRatio`.  This is the EXACT base case (`δ_0 = 0`), proved at the `Q'` level (as an
`eqv`, since the cancellation `divPos·q ≃ p` is value-level not definitional). -/
theorem matched_base_exact (N : Nat) {w : Q'} (hw : (0 : Q') < w) :
    (bondMovedCoeff N w 2 0 * (Q'.ofNat 2 * cubeRatio N w hw)).eqv
      (bondMovedCoeff N w 2 1 * (1 : Q')) := by
  have hden : (0 : Q') < Q'.ofNat 2 * bondMovedCoeff N w 2 0 :=
    Q'.mul_pos (by decide : (0 : Q') < Q'.ofNat 2)
      (YMGap.Continuum.FusionResidualBound.bondMovedCoeff_zero_pos N hw 2)
  -- cubeRatio = divPos g1 (2·g0); the cancellation divPos·(2·g0) ≃ g1
  have hcancel : (cubeRatio N w hw * (Q'.ofNat 2 * bondMovedCoeff N w 2 0)).eqv
      (bondMovedCoeff N w 2 1) :=
    Q'.divPos_mul_eqv (bondMovedCoeff N w 2 1) (Q'.ofNat 2 * bondMovedCoeff N w 2 0) hden
  -- g0·(2·R) ≃ R·(2·g0) ≃ g1 ≃ g1·1
  have hrearr : (bondMovedCoeff N w 2 0 * (Q'.ofNat 2 * cubeRatio N w hw)).eqv
      (cubeRatio N w hw * (Q'.ofNat 2 * bondMovedCoeff N w 2 0)) := by
    -- g0·(2·R) ≃ g0·(R·2) ≃ (g0·R)·2 ≃ (R·g0)·2 ≃ R·(g0·2) ≃ R·(2·g0)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (bondMovedCoeff N w 2 0) _ _
        (Q'.mul_comm_eqv (Q'.ofNat 2) (cubeRatio N w hw))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (bondMovedCoeff N w 2 0) (cubeRatio N w hw) (Q'.ofNat 2))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (Q'.ofNat 2)
        (Q'.mul_comm_eqv (bondMovedCoeff N w 2 0) (cubeRatio N w hw))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (cubeRatio N w hw) (bondMovedCoeff N w 2 0) (Q'.ofNat 2)) ?_
    exact Q'.mul_eqv_congr_left (cubeRatio N w hw) _ _
      (Q'.mul_comm_eqv (bondMovedCoeff N w 2 0) (Q'.ofNat 2))
  refine Q'.eqv_trans _ _ _ hrearr (Q'.eqv_trans _ _ _ hcancel ?_)
  exact Q'.eqv_symm (Q'.mul_one_eqv (bondMovedCoeff N w 2 1))

end YMGap.Continuum.MatchedRetuneBridge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MatchedRetuneBridge.exists_matchedRetuneP2
#print axioms YMGap.Continuum.MatchedRetuneBridge.cbrtFrom_geRat_of_cube
#print axioms YMGap.Continuum.MatchedRetuneBridge.rhoLo_pos
#print axioms YMGap.Continuum.MatchedRetuneBridge.rhoLo_cube_le
#print axioms YMGap.Continuum.MatchedRetuneBridge.R_le_rhoHi_cube
#print axioms YMGap.Continuum.MatchedRetuneBridge.geRat_rho_rhoLo
#print axioms YMGap.Continuum.MatchedRetuneBridge.leRat_rho_rhoHi
#print axioms YMGap.Continuum.MatchedRetuneBridge.rho_pow_decompose
#print axioms YMGap.Continuum.MatchedRetuneBridge.geRat_mul
#print axioms YMGap.Continuum.MatchedRetuneBridge.crealPowNat_brackets
#print axioms YMGap.Continuum.MatchedRetuneBridge.coeffMatched_brackets
#print axioms YMGap.Continuum.MatchedRetuneBridge.coeffRatio_brackets
#print axioms YMGap.Continuum.MatchedRetuneBridge.coeffMatchedLo_pos
#print axioms YMGap.Continuum.MatchedRetuneBridge.coeffMatchedHi_pos
#print axioms YMGap.Continuum.MatchedRetuneBridge.exact_cross_le
#print axioms YMGap.Continuum.MatchedRetuneBridge.matched_base_exact
