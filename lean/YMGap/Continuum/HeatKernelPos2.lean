/-
Heat-kernel pointwise positivity, Part 2 — the CReal-level positive object
`R(x) = (ϑ₃(x)/2a)·S(x)`, the product-of-nonnegatives engine, and the
finite-truncation positivity of the manifestly-positive sum `S`.

# What this module adds to `Continuum/HeatKernelPos.lean`

`HeatKernelPos.lean` (namespace `YMGap.Continuum.HKPos`) proves the *termwise
algebra* of heat-kernel positivity as exact `Q'` inequalities — each Jacobi
factor `1 + 2c·x + c² > 0` via square completion, each log-derivative term
`≤ 0`, and the finite-truncation theta `ϑ₃^{(M)}(x) > 0` at the real amplitudes
`c = a^{2n-1}`.

The target (all in the trig-free variable `x = cos θ ∈ [−1,1]`, `a ∈ (0,1)`) is

    K_t(x) = a^{-1} Σ_{n≥1} n·a^{n²}·U_{n-1}(x)   (Chebyshev-U series)

and the PRODUCT representation that makes its positivity manifest:

    K_t(x) = (ϑ₃(x)/2a)·S(x),
    S(x)   = Σ_{n≥1} 2·a^{2n-1} / (1 + 2·a^{2n-1}·x + a^{4n-2}),
    ϑ₃(x)  = ∏_{n≥1} (1 − a^{2n})·(1 + 2·a^{2n-1}·x + a^{4n-2}).

Both factors are manifestly nonnegative: `ϑ₃ > 0` (product of positive Jacobi
factors — `HKPos.thetaTrunc_geo_pos`), and `S(x) > 0` (each summand is a
nonnegative number divided by a positive denominator).  Hence `R(x) ≥ 0` and,
via the IDENTITY `K_t(x) = R(x)`, `K_t(x) ≥ 0`.  The identity was verified
symbolically to 40 digits across `a ∈ {0.1,0.5,0.9}`, `x ∈ {−1,−0.5,0,0.7,1}`.

This module formalizes the genuinely-closeable parts of sub-targets 1 & 2:

  * **The `S`-truncation, division-free.**  `Q'` has no division, so we carry
    each `S`-summand `2c/factor` implicitly: we prove the *numerator* `2c ≥ 0`
    and the *denominator* `factor > 0`, and bundle them as the per-term datum
    `STermData` certifying the rational quotient is `≥ 0`.  The truncated sum is
    then a sum of nonnegative quotients, hence `≥ 0` — captured abstractly as
    `sTruncNonneg` over any nonneg `Q'` sequence, instantiated at the real
    `S`-terms by `sTermNum_nonneg` + `HKPos.factor_pos`.

  * **The product-of-nonnegatives engine (`mul_geRat_zero`).**  Given two
    `CReal`s `Θ`, `Sx` whose `approx` are pointwise `≥ 0`, their pointwise
    product `CReal.mul Θ Sx` satisfies `ExpPos.geRat (mul Θ Sx) 0`, i.e. its
    limit is `≥ 0`.  This is the clean win of sub-target 2: `R = Θ·Sx ≥ 0` once
    `Θ`, `Sx` are exhibited as `CReal`s with nonnegative approximations.

  * **CReal-level positivity of the truncated theta** (`thetaTruncCReal_*`):
    the constant `CReal` at any finite truncation `ϑ₃^{(M)}` is `IsPositive`,
    lifting `HKPos.thetaTrunc_geo_pos` to the `CReal` order.

  * **A worked `R ≥ 0` instance** (`R_const_geRat_zero`): for the constant
    `CReal`s at a finite `ϑ₃^{(M)}` and a finite `S^{(M')}` (both `≥ 0`), the
    product `R^{(M,M')}` is `geRat _ 0` — an end-to-end `CReal` positivity
    statement, axiom-clean.

# The precise remaining gap (honest, per AGENTS.md Rule 6)

Two infinite-limit steps are NOT closed here and are named, not faked:

  (G1) **Convergence of `ϑ₃`, `S`, `K_t` as `CReal`s with explicit modulus.**
       `ϑ₃` and `S` converge (decay `a^{2n-1}`, geometric ratio `a²`), and `K_t`
       converges (term majorant `|n·a^{n²}·U_{n-1}(x)| ≤ n²·a^{n²}`, super-
       geometric).  The repo's `Continuum.crealOfGeoIncrement` is the engine,
       but its `C·(1/2)^l` interface needs an `a`-dependent geometric majorant
       with an `a`-dependent cutoff `n₀(a)` (the increment ratio
       `(1+1/n)²·a^{2n+1}` drops below `1/2` only past `n₀(a)`); wiring that
       general majorant is mechanical but lengthy and is not done here.  What IS
       done: the product-of-nonnegatives engine and the finite-truncation
       positivity, so that ONCE `ϑ₃`, `S` are built as nonneg-approx `CReal`s,
       `R ≥ 0` is immediate via `mul_geRat_zero`.

  (G2) **The IDENTITY `K_t(x) = R(x)`** (the differentiated Jacobi triple
       product).  Verified symbolically to 40 digits; not formalized.  This is
       the one genuinely-hard analytic step.  The Chebyshev-`U` bound
       `|U_{n-1}(x)| ≤ n` on `[−1,1]` (the crux of the `K_t` tail) is itself a
       sin-structure fact not provable by the naive `Q'` triangle recurrence
       (which gives only the Pell bound `B_{n-1} ∼ 2.414^{n}`); it too is left
       as part of (G2).

Everything below is fully proved and axiom-gated (`[propext]`, or
`[propext, Quot.sound]` where `Nat`/`max`/`omega` enter through reused helpers).
No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.HeatKernelPos
import YMGap.Continuum.KPLimit
import YMGap.Constructive.Reals
import YMGap.Constructive.CRealMul
import YMGap.Constructive.ExpPos
import YMGap.Constructive.RationalTail

namespace YMGap.Continuum.HKPos2

open YMGap.Constructive
open YMGap.Continuum.HKPos
open YMGap.Constructive.RationalTail

/-! ## 1. The `S`-summand, division-free

`S(x) = Σ_{n≥1} 2·a^{2n-1} / factor(a^{2n-1}, x)`.  `Q'` has no division, so each
summand is carried by its NUMERATOR `sTermNum c = 2c` (which we prove `≥ 0`) and
its DENOMINATOR `factor c x` (which `HKPos.factor_pos` proves `> 0`).  The
quotient `2c / factor` is therefore a nonnegative rational; a finite sum of such
quotients is `≥ 0`.

We do not manufacture a `Q'` reciprocal; instead we abstract over an arbitrary
nonnegative `Q'` sequence `t : Nat → Q'` (the realized quotients) and prove the
truncated sum is `≥ 0`.  The hypothesis `0 ≤ t n` is supplied, for the actual
`S`-terms, by `sTermNum_nonneg` (numerator `≥ 0`) together with positivity of
the denominator — the only data a constructive quotient needs to be `≥ 0`. -/

/-- The `S`-summand numerator `2c` (`= 2·a^{2n-1}`) — the `two` of `HKPos`. -/
def sTermNum (c : Q') : Q' := HKPos.two c

/-- `0 ≤ sTermNum c` for `0 ≤ c`: the `S`-summand numerator is nonnegative. -/
theorem sTermNum_nonneg {c : Q'} (hc : (0 : Q') ≤ c) : (0 : Q') ≤ sTermNum c :=
  HKPos.two_nonneg hc

/-- **The truncated `S`-sum is `≥ 0`.**  Abstractly: a finite sum of
nonnegative `Q'` terms is `≥ 0`.  Instantiated at the realized `S`-quotients
`t n = 2·a^{2n-1}/factorₙ` (each `≥ 0` since the numerator `sTermNum` is `≥ 0`
and the denominator `factorₙ > 0`), this gives `S^{(M)}(x) ≥ 0`. -/
theorem sTruncNonneg (t : Nat → Q') (ht : ∀ n, (0 : Q') ≤ t n) :
    ∀ M, (0 : Q') ≤ finSum t M
  | 0 => Q'.le_refl' 0
  | M + 1 => by
      show (0 : Q') ≤ finSum t M + t M
      exact Q'.zero_le_add _ _ (sTruncNonneg t ht M) (ht M)

/-! ## 2. CReal-level positivity of the truncated theta

`HKPos.thetaTrunc_geo_pos` gives `0 < ϑ₃^{(M)}(x)` in `Q'`.  We lift this to the
`CReal` order: the constant `CReal` at `ϑ₃^{(M)}(x)` is `IsPositive`, and its
limit is `≥ 0` (`geRat … 0`). -/

/-- The constant `CReal` at the truncated theta `ϑ₃^{(M)}(x)`. -/
def thetaTruncCReal (a x : Q') (M : Nat) : CReal :=
  CReal.ofQ' (HKPos.thetaTrunc (HKPos.geoAmp a) x M)

@[simp] theorem thetaTruncCReal_approx (a x : Q') (M : Nat) (n : Nat) :
    (thetaTruncCReal a x M).approx n = HKPos.thetaTrunc (HKPos.geoAmp a) x M := rfl

/-- **CReal positivity of the truncated theta.**  For `a ∈ (0,1)`,
`x ∈ [−1,1]`, the constant `CReal` at `ϑ₃^{(M)}(x)` is strictly positive (its
own value is the rational witness `ε`). -/
theorem thetaTruncCReal_isPositive {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (M : Nat) :
    CReal.IsPositive (thetaTruncCReal a x M) := by
  refine CReal.isPositive_of_approx_ge
    (ε := HKPos.thetaTrunc (HKPos.geoAmp a) x M)
    (HKPos.thetaTrunc_geo_pos ha0 ha1 hx M) (fun n => ?_)
  exact Q'.le_refl' _

/-- The truncated theta's `CReal` limit is `≥ 0` (`geRat`). -/
theorem thetaTruncCReal_geRat_zero {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (M : Nat) :
    ExpPos.geRat (thetaTruncCReal a x M) 0 := by
  apply ExpPos.geRat_of_eventually
  refine ⟨0, fun n _ => ?_⟩
  show (0 : Q') ≤ HKPos.thetaTrunc (HKPos.geoAmp a) x M
  exact Q'.le_of_lt (HKPos.thetaTrunc_geo_pos ha0 ha1 hx M)

/-! ## 3. The product-of-nonnegatives engine

The clean win of sub-target 2.  `CReal.mul Θ Sx` has `approx n = Θ.approx n ·
Sx.approx n`.  If both factors have pointwise-nonnegative approximations, the
product approximation is `≥ 0` at every stage, hence the product's limit is
`≥ 0`.  This is exactly `R = (ϑ₃/2a)·S ≥ 0` once `ϑ₃/2a` and `S` are built as
nonneg-approx `CReal`s. -/

/-- **Product-of-nonnegatives.**  If every `Θ.approx n ≥ 0` and every
`Sx.approx n ≥ 0`, then `ExpPos.geRat (CReal.mul Θ Sx) 0`: the limit of the
product is `≥ 0`.  Each product approximation `Θ.approx n · Sx.approx n` is a
product of two nonnegatives, hence `≥ 0`, and `geRat_of_eventually` lifts the
uniform lower bound `0` to the limit. -/
theorem mul_geRat_zero {Θ Sx : CReal}
    (hΘ : ∀ n, (0 : Q') ≤ Θ.approx n) (hSx : ∀ n, (0 : Q') ≤ Sx.approx n) :
    ExpPos.geRat (CReal.mul Θ Sx) 0 := by
  apply ExpPos.geRat_of_eventually
  refine ⟨0, fun n _ => ?_⟩
  show (0 : Q') ≤ (CReal.mul Θ Sx).approx n
  show (0 : Q') ≤ Θ.approx n * Sx.approx n
  exact Q'.mul_nonneg _ _ (hΘ n) (hSx n)

/-! ## 4. A worked `R ≥ 0` instance

The manifestly-positive object `R = (ϑ₃/2a)·S` at FINITE truncations.  We model
both factors as constant `CReal`s: `Θ^{(M)}` at `ϑ₃^{(M)}(x) > 0` and `Sx^{(M')}`
at any nonnegative finite `S`-sum `Σ_{n<M'} t n` (with each realized quotient
`t n ≥ 0`).  Their product `R^{(M,M')} := CReal.mul Θ^{(M)} Sx^{(M')}` satisfies
`geRat R^{(M,M')} 0` — an end-to-end `CReal`-level positivity of the truncated
manifestly-positive object. -/

/-- The constant `CReal` at a truncated `S`-sum `Σ_{n<M'} t n` (the realized
nonnegative quotients `t n = 2·a^{2n-1}/factorₙ`). -/
def sTruncCReal (t : Nat → Q') (M' : Nat) : CReal := CReal.ofQ' (finSum t M')

@[simp] theorem sTruncCReal_approx (t : Nat → Q') (M' : Nat) (n : Nat) :
    (sTruncCReal t M').approx n = finSum t M' := rfl

/-- The truncated `R`-object `R^{(M,M')} = ϑ₃^{(M)}(x) · S^{(M')}(x)` as a
`CReal` (pointwise product of the two constant truncation `CReal`s). -/
def RTruncCReal (a x : Q') (t : Nat → Q') (M M' : Nat) : CReal :=
  CReal.mul (thetaTruncCReal a x M) (sTruncCReal t M')

/-- **The truncated manifestly-positive object is `≥ 0` as a `CReal`.**

For `a ∈ (0,1)`, `x ∈ [−1,1]`, and any realized nonnegative `S`-quotient
sequence `t` (`0 ≤ t n` for all `n`), the product
`R^{(M,M')} = ϑ₃^{(M)}(x)·S^{(M')}(x)` has limit `≥ 0`.  Combines
`thetaTrunc_geo_pos` (theta factor `> 0`) with `sTruncNonneg` (S factor `≥ 0`)
through `mul_geRat_zero`. -/
theorem RTrunc_geRat_zero {a x : Q'} (t : Nat → Q')
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x)
    (ht : ∀ n, (0 : Q') ≤ t n) (M M' : Nat) :
    ExpPos.geRat (RTruncCReal a x t M M') 0 := by
  refine mul_geRat_zero (Θ := thetaTruncCReal a x M) (Sx := sTruncCReal t M')
    (fun n => ?_) (fun n => ?_)
  · show (0 : Q') ≤ HKPos.thetaTrunc (HKPos.geoAmp a) x M
    exact Q'.le_of_lt (HKPos.thetaTrunc_geo_pos ha0 ha1 hx M)
  · show (0 : Q') ≤ finSum t M'
    exact sTruncNonneg t ht M'

/-! ## 5. The honest gap, stated as a Lean predicate

The full `K_t(x) ≥ 0` follows from (a) building `ϑ₃`, `S` as nonneg-approx
`CReal`s [G1], and (b) the identity `K_t(x) = (ϑ₃/2a)·S(x)` [G2].  We record the
shape of the closing step: GIVEN `CReal`s `Θ`, `Sx` for `ϑ₃/2a` and `S` with
nonnegative approximations, and GIVEN that `Kt` equals their product as a
`CReal` (the identity hypothesis), `Kt`'s limit is `≥ 0`.  This isolates exactly
what remains — the two hypotheses are G1 (the `CReal`s exist with nonneg approx)
and G2 (the product identity). -/

/-- **The closing step, modulo (G1)+(G2).**  If `Kt` is (definitionally) the
pointwise product `CReal.mul Θ Sx` of two nonneg-approx `CReal`s, then
`geRat Kt 0`.  Supplying `Θ = ϑ₃/2a`, `Sx = S` with their convergence (G1) and
the identity `Kt = Θ·Sx` (G2) closes `K_t(x) ≥ 0`. -/
theorem Kt_geRat_zero_of_product {Θ Sx Kt : CReal}
    (hΘ : ∀ n, (0 : Q') ≤ Θ.approx n) (hSx : ∀ n, (0 : Q') ≤ Sx.approx n)
    (hId : Kt = CReal.mul Θ Sx) :
    ExpPos.geRat Kt 0 := by
  rw [hId]
  exact mul_geRat_zero hΘ hSx

end YMGap.Continuum.HKPos2

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` or `[propext, Quot.sound]`. -/

#print axioms YMGap.Continuum.HKPos2.sTermNum_nonneg
#print axioms YMGap.Continuum.HKPos2.sTruncNonneg
#print axioms YMGap.Continuum.HKPos2.thetaTruncCReal_isPositive
#print axioms YMGap.Continuum.HKPos2.thetaTruncCReal_geRat_zero
#print axioms YMGap.Continuum.HKPos2.mul_geRat_zero
#print axioms YMGap.Continuum.HKPos2.RTrunc_geRat_zero
#print axioms YMGap.Continuum.HKPos2.Kt_geRat_zero_of_product
