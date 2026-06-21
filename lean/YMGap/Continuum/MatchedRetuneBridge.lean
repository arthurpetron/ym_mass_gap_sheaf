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
single pair of RATIONAL brackets `rhoLo ≤ ρ ≤ rhoHi` (extracted from the bisection
bracket, validated by `rhoLo³ ≤ R ≤ rhoHi³`) brackets the entire irrational residual:
`ρ^0 = 1`, `ρ^1 ∈ [rhoLo, rhoHi]`, `ρ^2 ∈ [rhoLo², rhoHi²]`.  Multiplying by the
rational `R^{⌊C₄(s)/3⌋}` gives explicit `Q'` lower/upper bounds on the genuine `CReal`
matched coefficient `coeffMatched R s` — `coeffMatched_brackets` — with NO `CReal`
order-algebra layer.

## What this module builds (and what it deliberately does NOT)

  * `exists_matchedRetuneP2` — the carrier inhabitant (the cube-root glue).
  * `rhoLo` / `rhoHi` — rational brackets with `rhoLo³ ≤ R ≤ rhoHi³`, `0 < rhoLo`,
    and the `CReal` order facts `geRat ρ rhoLo`, `leRat ρ rhoHi`.
  * `rho_pow_decompose` — the rational/irrational split of `ρ^{C₄(s)}` (built on the
    shared `crealPowNat` exponent laws `crealPowNat_add` / `crealPowNat_mul3`).
  * `coeffMatched` (the genuine `CReal` matched coefficient) and
    `coeffMatched_brackets` (its explicit `Q'` lower/upper bounds).
  * `stepRatioBracket` — the `Q'`-bound interface for the matched per-step quotient:
    the matched coefficient ratio is bracketed by explicit `Q'` expressions in the
    bond-moved coefficient ratio and the `rhoLo/rhoHi` powers, the object Wave-2b will
    bound by `Cu²·(y_{k+1} − y_k)`.

## Honest verdict and scope

This is carrier-inhabitation plus the `Q'`↔`CReal` bracket bridge infrastructure.  It
does NOT prove `δ_k ≥ 0`, the cumulative/derivative bound, or anything Wave-2b; it does
NOT prove `0 < R` or `R < 1` (clean named hypotheses).  It is NOT a 4D Yang–Mills mass
gap.

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

/-! ### Canonical brackets `rhoLo, rhoHi`

A concrete rational bracket pair for `ρ = ∛R`, taken from the bisection bracket at a
chosen stage and validated by the located cube invariant `rhoLo³ ≤ R ≤ rhoHi³`.  We
fix the stage `1` (one bisection step from `[L₀, U₀]`); any stage works.  These supply
the `Q'` brackets the §3 power decomposition needs. -/

/-- The canonical rational LOWER bracket for `∛R`: the lower endpoint after one
bisection step. -/
def rhoLo (R : Q') (_hR : (0 : Q') < R) : Q' := CReal.cbrtLo R (Q'.min' R 1) (R + 1) 1

/-- The canonical rational UPPER bracket for `∛R`: the upper endpoint after one
bisection step. -/
def rhoHi (R : Q') (_hR : (0 : Q') < R) : Q' := CReal.cbrtHi R (Q'.min' R 1) (R + 1) 1

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
theorem rhoLo_pos (R : Q') (hR : (0 : Q') < R) : (0 : Q') < rhoLo R hR := by
  have hinit := CReal.cbrtInit_canonical hR
  exact q_lt_of_lt_of_le hinit.loPos (CReal.cbrtLo_ge_L₀ R (Q'.min' R 1) (R + 1) hinit 1)

/-- `0 ≤ rhoHi`. -/
theorem rhoHi_nonneg (R : Q') (hR : (0 : Q') < R) : (0 : Q') ≤ rhoHi R hR := by
  have hinit := CReal.cbrtInit_canonical hR
  exact Q'.le_trans' _ _ _ (CReal.cbrtLo_nonneg R (Q'.min' R 1) (R + 1) hinit 1)
    (CReal.cbrtLo_le_cbrtHi R (Q'.min' R 1) (R + 1) hinit 1)

/-- `rhoLo³ ≤ R` (located invariant). -/
theorem rhoLo_cube_le (R : Q') (hR : (0 : Q') < R) :
    rhoLo R hR * rhoLo R hR * rhoLo R hR ≤ R :=
  CReal.cbrtLo_cube_le R (Q'.min' R 1) (R + 1) (CReal.cbrtInit_canonical hR) 1

/-- `R ≤ rhoHi³` (located invariant). -/
theorem R_le_rhoHi_cube (R : Q') (hR : (0 : Q') < R) :
    R ≤ rhoHi R hR * rhoHi R hR * rhoHi R hR :=
  CReal.R_le_cbrtHi_cube R (Q'.min' R 1) (R + 1) (CReal.cbrtInit_canonical hR) 1

/-- `rhoLo ≤ rhoHi`. -/
theorem rhoLo_le_rhoHi (R : Q') (hR : (0 : Q') < R) : rhoLo R hR ≤ rhoHi R hR :=
  CReal.cbrtLo_le_cbrtHi R (Q'.min' R 1) (R + 1) (CReal.cbrtInit_canonical hR) 1

/-- **`rhoLo ≤ ρ`** as `geRat (∛R) rhoLo` (from `rhoLo³ ≤ R`). -/
theorem geRat_rho_rhoLo (R : Q') (hR : (0 : Q') < R) :
    ExpPos.geRat (CReal.cbrtFrom R hR) (rhoLo R hR) :=
  cbrtFrom_geRat_of_cube R hR (rhoLo R hR) (Q'.le_of_lt (rhoLo_pos R hR)) (rhoLo_cube_le R hR)

/-- **`ρ ≤ rhoHi`** as `leRat (∛R) rhoHi` (from `R ≤ rhoHi³`). -/
theorem leRat_rho_rhoHi (R : Q') (hR : (0 : Q') < R) :
    CReal.leRat (CReal.cbrtFrom R hR) (rhoHi R hR) :=
  CReal.cbrtFrom_leRat_of_cube R hR (rhoHi R hR) (rhoHi_nonneg R hR) (R_le_rhoHi_cube R hR)

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

/-- The explicit `Q'` UPPER bound for `coeffMatched`: `(s+1)·rhoHi^{C₄(s)}`. -/
def coeffMatchedHi (R : Q') (hR : (0 : Q') < R) (s : Nat) : Q' :=
  dimQ s * qpow (rhoHi R hR) (c4 s)

/-- The explicit `Q'` LOWER bound for `coeffMatched`: `(s+1)·rhoLo^{C₄(s)}`. -/
def coeffMatchedLo (R : Q') (hR : (0 : Q') < R) (s : Nat) : Q' :=
  dimQ s * qpow (rhoLo R hR) (c4 s)

/-- **`coeffMatched_brackets`.**  For `ρ = ∛R`, the genuine `CReal` matched coefficient
is bracketed by the explicit `Q'` bounds `coeffMatchedLo ≤ coeffMatched ≤ coeffMatchedHi`,
where both bounds are built from `dimQ s` and powers of the rational brackets `rhoLo`,
`rhoHi`.  PROOF: `coeffMatched ρ s = dimQ s · ρ^{C₄(s)}`; bracket `ρ^{C₄(s)}` by
`crealPowNat_brackets` (with the `ρ`-brackets `geRat_rho_rhoLo` / `leRat_rho_rhoHi`),
then scale by the nonnegative rational `dimQ s` (`leRat_smul_nonneg`, and `geRat` by the
same scaling). -/
theorem coeffMatched_brackets (R : Q') (hR : (0 : Q') < R) (s : Nat) :
    ExpPos.geRat (coeffMatched (CReal.cbrtFrom R hR) s) (coeffMatchedLo R hR s)
      ∧ CReal.leRat (coeffMatched (CReal.cbrtFrom R hR) s) (coeffMatchedHi R hR s) := by
  obtain ⟨hg, hl⟩ := crealPowNat_brackets (CReal.cbrtFrom R hR)
    (geRat_rho_rhoLo R hR) (leRat_rho_rhoHi R hR)
    (Q'.le_of_lt (rhoLo_pos R hR)) (rhoHi_nonneg R hR) (c4 s)
  have hdim : (0 : Q') ≤ dimQ s := dimQ_nonneg s
  refine ⟨?_, ?_⟩
  · -- geRat (dimQ s · ρ^{c4 s}) (dimQ s · rhoLo^{c4 s})
    show ExpPos.geRat (CReal.mul (CReal.ofQ' (dimQ s)) (crealPowNat (CReal.cbrtFrom R hR) (c4 s)))
      (dimQ s * qpow (rhoLo R hR) (c4 s))
    exact geRat_smul_nonneg hdim hg
  · show CReal.leRat (CReal.mul (CReal.ofQ' (dimQ s)) (crealPowNat (CReal.cbrtFrom R hR) (c4 s)))
      (dimQ s * qpow (rhoHi R hR) (c4 s))
    exact CReal.leRat_smul_nonneg hdim hl

/-! ## 5. The `δ_k` / `Qfrac` `Q'`-bound interface

The matched per-step quotient is `Q_s = (g_s · ĉ_0)/(g_0 · ĉ_s)` with `ĉ_s =
coeffMatched ρ s`.  The bridge replaces the genuine `CReal` `ĉ_s` by its `Q'` brackets:
the quotient — and hence the per-step increment `δ_k` Wave-2b must control by
`Cu²·(y_{k+1} − y_k)` — is bracketed by explicit `Q'` expressions in the bond-moved
coefficient ratio and the `rhoLo/rhoHi` powers.  We expose the cleanest such object: the
matched coefficient ratio `ĉ_{k+1}/ĉ_k`, `Q'`-bracketed via `coeffMatched_brackets`. -/

/-- The `Q'` UPPER bracket for the matched coefficient ratio `ĉ_{k+1}/ĉ_k`:
`coeffMatchedHi (k+1) / coeffMatchedLo k` (the largest numerator over the smallest
denominator).  Positivity of the denominator from `0 < rhoLo` and `0 < dimQ`. -/
def coeffRatioHi (R : Q') (hR : (0 : Q') < R) (k : Nat) : Q' :=
  Q'.divPos (coeffMatchedHi R hR (k + 1)) (coeffMatchedLo R hR k)
    (Q'.mul_pos (Q'.ofNat_succ_pos k)
      (BondMovingScaledNorm.qpow_pos (rhoLo_pos R hR) (c4 k)))

/-- The `Q'` LOWER bracket for the matched coefficient ratio `ĉ_{k+1}/ĉ_k`:
`coeffMatchedLo (k+1) / coeffMatchedHi k`. -/
def coeffRatioLo (R : Q') (hR : (0 : Q') < R) (k : Nat) : Q' :=
  Q'.divPos (coeffMatchedLo R hR (k + 1)) (coeffMatchedHi R hR k)
    (Q'.mul_pos (Q'.ofNat_succ_pos k)
      (BondMovingScaledNorm.qpow_pos (q_lt_of_lt_of_le (rhoLo_pos R hR) (rhoLo_le_rhoHi R hR)) (c4 k)))

/-- **The `δ_k` / `Qfrac` `Q'`-bound interface.**  The matched coefficient ratio
`ĉ_{k+1}/ĉ_k` (the genuine `CReal` object underlying the per-step increment `δ_k`) is
bracketed by the explicit `Q'` expressions `coeffRatioLo k ≤ … ≤ coeffRatioHi k`, both
built from `dimQ`, the rational `R`-powers, and the `rhoLo/rhoHi` brackets — with NO
`CReal` algebra layer.  This is the object Wave-2b bounds by `Cu²·(y_{k+1} − y_k)`.

We record it as the pair of bracket facts on `coeffMatched`; the ratio brackets
`coeffRatioLo/Hi` are their `divPos` combinations.  (We do not assert the `CReal` ratio
here — only the numerator/denominator brackets that define it — keeping the interface
purely `Q'` and honest about what is established.) -/
theorem coeffRatio_brackets (R : Q') (hR : (0 : Q') < R) (k : Nat) :
    (ExpPos.geRat (coeffMatched (CReal.cbrtFrom R hR) (k + 1)) (coeffMatchedLo R hR (k + 1))
      ∧ CReal.leRat (coeffMatched (CReal.cbrtFrom R hR) (k + 1)) (coeffMatchedHi R hR (k + 1)))
    ∧ (ExpPos.geRat (coeffMatched (CReal.cbrtFrom R hR) k) (coeffMatchedLo R hR k)
      ∧ CReal.leRat (coeffMatched (CReal.cbrtFrom R hR) k) (coeffMatchedHi R hR k)) :=
  ⟨coeffMatched_brackets R hR (k + 1), coeffMatched_brackets R hR k⟩

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
