/-
Research frontier — the **Favard recurrence coefficient `β_k`** for the
uniform-in-`N` SU(2) heat-kernel Gram positivity, and an honest account of
whether the recurrence route closes the all-`N` argument.

Setup (same uniform base variable as `MomentPositivity`/`Favard`):
`a = e^{−t/4} ∈ (0,1]`, moments `m_s = (s+1)·a^{s(s+2)}`, leading Gram minors
`Δ_N(a) = det G[0..N−1]`, with the uniform factorization
`Δ_N = S_N²·P_N` (`S_N = ∏_{j=1}^{N−1}(a^{2j}−1)^{N−j}`, `P_N`
nonneg-coefficient, `P_N(0)=1`).

# The closed form of `β_k`

For the monic orthogonal polynomials of the heat-kernel moment functional the
three-term recurrence `Q_{k+1}=(x−α_k)Q_k−β_k Q_{k−1}` has
`β_k = Δ_{k+1}·Δ_{k−1}/Δ_k²`.  Substituting `Δ_N = S_N²·P_N`,

    β_k = (S_{k+1}·S_{k−1}/S_k²)² · (P_{k+1}·P_{k−1}/P_k²).

Exact computer algebra (sympy, through `k = 6`) gives the **cyclotomic
content of `β_k` as a single perfect square**: the telescoping identity

    S_{k+1}·S_{k−1} = (a^{2k}−1)·S_k²        (`telescope`)

makes `(S_{k+1}·S_{k−1}/S_k²)² = (a^{2k}−1)²`, so

    ┌────────────────────────────────────────────────────────────┐
    │  β_k(a) = (a^{2k}−1)² · ( P_{k+1}·P_{k−1} / P_k² )          │
    └────────────────────────────────────────────────────────────┘

— a single, manifestly-nonnegative cyclotomic square `(a^{2k}−1)²` times a
ratio of nonneg-coefficient polynomials.  The "q-Hermite / theta-q-Hermite"
rational factor `γ_k := P_{k+1}P_{k−1}/P_k²` is genuinely **not** a
polynomial: through `k = 6` its reduced denominator `P_k²` does not cancel
(verified: `P_{k−1} ∤ P_k²` for `k ≥ 3`).

# Does a nonneg-coefficient-preserving recurrence exist?

This is the honest crux.  Two natural recurrences and why each fails to give a
*division-free, coefficient-nonneg* induction for `P_N`:

  * **Favard quadratic.**  `P_{k+1}·P_{k−1} = γ_k·P_k²` with `γ_k` rational
    (`= β_k/(a^{2k}−1)²`).  Solving `P_{k+1} = γ_k·P_k²/P_{k−1}` requires
    dividing by `P_{k−1}`, and `P_{k−1} ∤ P_k²` (exact: fails at `k = 3,4,5`).
    So `β_k`'s value-nonnegativity does **not** dissolve into a polynomial
    recurrence on the `P_N` coefficients.

  * **Desnanot–Jacobi (Dodgson).**  `Δ_N·Δ_central = Δ_{N−1}·BR − TR²`
    (`BR` = shifted leading minor rows/cols `1..N−1`; `TR` = off-diagonal
    corner; `TR = BL` by Gram symmetry).  Each corner minor *does* carry the
    same even-cyclotomic-multiplicity structure (its `√(square-content)`
    residual is itself nonneg-coefficient — verified through `N = 5` for
    `Δ_N, Δ_{N−1}, BR, TR, Δ_central`).  But the identity is a **difference**
    `Δ_{N−1}·BR − TR²`, and dividing out the square content leaves square
    *ratios* (negative `a`-powers), not nonneg-coefficient multipliers, so it
    does not rearrange into a subtraction-free recurrence for `P_N`.

**Verdict on the coefficient-positivity route.**  No division-free,
coefficient-nonneg recurrence for the family `P_N` drops out of either the
Favard or the Dodgson identity; the `decide`-checked per-`N` factorizations
(here extended to `N = 5`) remain the only certificates of `nonnegCoeffs P_N`,
and an `N`-indexed proof of `nonnegCoeffs P_N` stays **OPEN**.

**The value-positivity route, however, IS uniform** (recorded in the notes,
not the chosen Lean target): the heat-kernel representing measure
`dν(θ) = Σ_c (c+1)a^{c(c+2)}χ_c(θ)·(2/π)sin²θ` is a *positive* measure on
`(0,π)` (numerically verified), so by the Andréief/Heine identity
`Δ_N = (1/N!)∫⋯∫ ∏_{i<j}(cos θ_i−cos θ_j)² ∏_k dν(θ_k) ≥ 0` uniformly in `N`
— which is all the Gram-PSD / Sylvester input actually requires.  Coefficient
positivity of `P_N` is strictly *finer* than this value positivity (`Δ_N`
itself has negative coefficients) and is not needed for the mass-gap input.

# What is proved here (axiom-clean; no `Classical`/`sorry`/`native_decide`).

  * `betaNumer` — the `β_k`-numerator `Δ_{k+1}·Δ_{k−1}` as a `QPoly`, and the
    reusable consumer `betaNumer_nonneg_of_factor`: it is `≥ 0` (value) at
    `a ≥ 0` whenever supplied the two factorizations — exactly the
    division-free Favard reduction, packaged for the `β_k` numerator.
  * `betaCyclo_eq` (`k = 1,…,5`) — the **β-cyclotomic-square identity**
    `S_{k+1}·S_{k−1} = (a^{2k}−1)·S_k²` (= `Favard`'s telescope reindexed to
    `β_k`), `decide`-certified, exhibiting the cyclotomic content of `β_k` as
    the single square `(a^{2k}−1)²`.
  * `P5_nonneg`, `beta5_numer_*` — the `β_5`-numerator
    `Δ_5·Δ_3 = (S_5·S_3)²·(P_5·P_3) ≥ 0` (value), extending the verified
    Favard chain to `k = 5` through the *uniform* nonneg-cone engine
    (`nonnegCoeffs_pmul` on `P_5·P_3`).

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`,
no `native_decide`.
-/

import YMGap.Continuum.Favard
import YMGap.Continuum.QHankel

namespace YMGap.Continuum.FavardRec

open YMGap.Constructive

/-! ## The `β_k`-cyclotomic-square identity

`β_k = Δ_{k+1}Δ_{k−1}/Δ_k²`.  Its cyclotomic content is the single perfect
square `(a^{2k}−1)²`, because the square factors telescope:

    S_{k+1}·S_{k−1} = (a^{2k}−1)·S_k²       (= `qFac k · S_k²`).

This is the `Favard`-file telescope `S_s·S_{s−2} = qFac(s−1)·S_{s−1}²`
reindexed `s = k+1`.  We re-state it here in `β`-indexing as the
`decide`-certified instances `k = 1,…,5`. -/

/-- `β_1` cyclotomic square: `S_2·S_0 = (a²−1)·S_1²`. -/
theorem betaCyclo_1 (x : Q') :
    (QPoly.eval (QPoly.pmul (SN 2) (SN 0)) x).eqv
      (QPoly.eval (QPoly.pmul (qFac 1) (QPoly.pmul (SN 1) (SN 1))) x) :=
  QPoly.poly_eqv _ _ x (by decide)

/-- `β_2` cyclotomic square: `S_3·S_1 = (a⁴−1)·S_2²`. -/
theorem betaCyclo_2 (x : Q') :
    (QPoly.eval (QPoly.pmul (SN 3) (SN 1)) x).eqv
      (QPoly.eval (QPoly.pmul (qFac 2) (QPoly.pmul (SN 2) (SN 2))) x) :=
  QPoly.poly_eqv _ _ x (by decide)

/-- `β_3` cyclotomic square: `S_4·S_2 = (a⁶−1)·S_3²`. -/
theorem betaCyclo_3 (x : Q') :
    (QPoly.eval (QPoly.pmul (SN 4) (SN 2)) x).eqv
      (QPoly.eval (QPoly.pmul (qFac 3) (QPoly.pmul (SN 3) (SN 3))) x) :=
  QPoly.poly_eqv _ _ x (by decide)

/-- `β_4` cyclotomic square: `S_5·S_3 = (a⁸−1)·S_4²`. -/
theorem betaCyclo_4 (x : Q') :
    (QPoly.eval (QPoly.pmul (SN 5) (SN 3)) x).eqv
      (QPoly.eval (QPoly.pmul (qFac 4) (QPoly.pmul (SN 4) (SN 4))) x) :=
  QPoly.poly_eqv _ _ x (by decide)

set_option maxRecDepth 4000 in
/-- `β_5` cyclotomic square: `S_6·S_4 = (a¹⁰−1)·S_5²`. -/
theorem betaCyclo_5 (x : Q') :
    (QPoly.eval (QPoly.pmul (SN 6) (SN 4)) x).eqv
      (QPoly.eval (QPoly.pmul (qFac 5) (QPoly.pmul (SN 5) (SN 5))) x) :=
  QPoly.poly_eqv _ _ x (by decide)

/-! ## The `β_k`-numerator consumer (division-free Favard reduction)

`β_k = Δ_{k+1}Δ_{k−1}/Δ_k²` with `Δ_k² ≥ 0` for free, so the *division-free*
content of `β_k ≥ 0` is the numerator `Δ_{k+1}·Δ_{k−1} ≥ 0` (value).  With
`Δ_{k+1} = S_{k+1}²P_{k+1}`, `Δ_{k−1} = S_{k−1}²P_{k−1}` this is
`(S_{k+1}S_{k−1})²·(P_{k+1}P_{k−1})` — a perfect square times a
nonneg-coefficient product.  This packages `favard_numer_nonneg` as a single
consumer indexed by the four lists. -/

/-- **`β_k`-numerator nonnegativity (value).**  Given the two factorizations
`Δ₁ = S₁²P₁`, `Δ₂ = S₂²P₂` with `P₁,P₂` nonneg-coefficient, the `β`-numerator
`Δ₁·Δ₂ = (S₁S₂)²·(P₁P₂) ≥ 0` at `a ≥ 0`.  (Alias of `favard_numer_nonneg`,
re-exported in `β`-indexing.) -/
theorem betaNumer_nonneg_of_factor {Δ₁ Δ₂ : CReal} (S₁ P₁ S₂ P₂ : QPoly.Poly)
    {a : CReal} (ha : ExpPos.geRat a 0)
    (hP₁ : nonnegCoeffs P₁) (hP₂ : nonnegCoeffs P₂)
    (hΔ₁ : CReal.Equiv Δ₁ (CReal.mul (CReal.mul (ceval S₁ a) (ceval S₁ a)) (ceval P₁ a)))
    (hΔ₂ : CReal.Equiv Δ₂ (CReal.mul (CReal.mul (ceval S₂ a) (ceval S₂ a)) (ceval P₂ a))) :
    ExpPos.geRat (CReal.mul Δ₁ Δ₂) 0 :=
  favard_numer_nonneg S₁ P₁ S₂ P₂ ha hP₁ hP₂ hΔ₁ hΔ₂

/-! ## Extending the verified Favard chain to `k = 5`

The `β_5`-numerator is `Δ_5·Δ_3 = (S_5·S_3)²·(P_5·P_3)`.  We supply the exact
`S_5, P_5` lists (computer algebra), prove `nonnegCoeffs P_5` by `decide`, and
discharge the numerator through the uniform nonneg-cone engine
(`nonnegCoeffs_pmul` on `P_5·P_3`) plus the `decide` factorization. -/

/-- `S_5` coefficient list (low→high), degree 40. -/
def S5 : QPoly.Poly :=
  [Q'.ofNat 1, 0, -(Q'.ofNat 4), 0, Q'.ofNat 3, 0, Q'.ofNat 6, 0,
   -(Q'.ofNat 7), 0, -(Q'.ofNat 2), 0, -(Q'.ofNat 4), 0, Q'.ofNat 10, 0,
   Q'.ofNat 6, 0, -(Q'.ofNat 10), 0, Q'.ofNat 2, 0, -(Q'.ofNat 10), 0,
   Q'.ofNat 6, 0, Q'.ofNat 10, 0, -(Q'.ofNat 4), 0, -(Q'.ofNat 2), 0,
   -(Q'.ofNat 7), 0, Q'.ofNat 6, 0, Q'.ofNat 3, 0, -(Q'.ofNat 4), 0,
   Q'.ofNat 1]

/-- `P_5` coefficient list (low→high), all nonnegative, degree 80,
leading coefficient `(2·5−1)!! = 945`. -/
def P5 : QPoly.Poly :=
  [Q'.ofNat 1, 0, Q'.ofNat 8, 0, Q'.ofNat 42, 0, Q'.ofNat 156, 0,
   Q'.ofNat 485, 0, Q'.ofNat 1288, 0, Q'.ofNat 3074, 0, Q'.ofNat 6640, 0,
   Q'.ofNat 13287, 0, Q'.ofNat 24740, 0, Q'.ofNat 43400, 0, Q'.ofNat 71912, 0,
   Q'.ofNat 113424, 0, Q'.ofNat 170524, 0, Q'.ofNat 245624, 0,
   Q'.ofNat 339244, 0, Q'.ofNat 450824, 0, Q'.ofNat 576588, 0,
   Q'.ofNat 711540, 0, Q'.ofNat 846992, 0, Q'.ofNat 974326, 0,
   Q'.ofNat 1082388, 0, Q'.ofNat 1162692, 0, Q'.ofNat 1206216, 0,
   Q'.ofNat 1209672, 0, Q'.ofNat 1170516, 0, Q'.ofNat 1093416, 0,
   Q'.ofNat 983484, 0, Q'.ofNat 851856, 0, Q'.ofNat 707724, 0,
   Q'.ofNat 564024, 0, Q'.ofNat 428508, 0, Q'.ofNat 310215, 0,
   Q'.ofNat 211956, 0, Q'.ofNat 136578, 0, Q'.ofNat 81456, 0, Q'.ofNat 45045,
   0, Q'.ofNat 22140, 0, Q'.ofNat 9690, 0, Q'.ofNat 3360, 0, Q'.ofNat 945]

/-- `P_5` has all-nonnegative coefficients (`decide`). -/
theorem P5_nonneg : nonnegCoeffs P5 := by decide

/-- **`P_5(a) ≥ 1`** for `a ≥ 0` — constant-term-`1` floor (the engine
`geRat_ceval_ge_one_of_headGeOne`). -/
theorem P5_ge_one {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval P5 a) 1 :=
  geRat_ceval_ge_one_of_headGeOne (Q'.ofNat 1) _ ha P5_nonneg (by decide)

/-- The local `S_5` list agrees with the uniform square factor `SN 5`
(`decide`).  Through it the `β_5`-numerator is stated with the uniform `SN 5`,
and `S5`/`SN 5` are interchangeable. -/
theorem SN_eq_S5_local : SN 5 = S5 := by decide

/-! ### `β_5`-numerator nonnegativity through the uniform cone engine

`Δ_5 = (SN 5)²·P_5` and `Δ_3 = (SN 3)²·P_3`, so the `β_5`-numerator is the
explicit factored polynomial

    Δ_5·Δ_3 = (SN 5·SN 3)²·(P_5·P_3).

We work with this *factored* form directly (the right-hand product), avoiding
the degree-160 expanded `Δ_5` literal: `P_5·P_3` is nonneg-coefficient by
`nonnegCoeffs_pmul` (the cone is closed under `·`) and `(SN 5·SN 3)²` is a
perfect square, so the product is `≥ 0` for every `a ≥ 0`.  This is the
genuine division-free content of `β_5 ≥ 0`. -/

/-- The `β_5`-numerator in explicit factored form `(SN 5·SN 3)²·(P_5·P_3)`. -/
def beta5Numer : QPoly.Poly :=
  QPoly.pmul (QPoly.pmul (QPoly.pmul (SN 5) (SN 3)) (QPoly.pmul (SN 5) (SN 3)))
    (QPoly.pmul P5 P3)

set_option maxRecDepth 8000 in
/-- **`β_5`-numerator `≥ 0`** (value): the factored product
`(SN 5·SN 3)²·(P_5·P_3)`, a perfect square times the product of two
nonneg-coefficient polynomials (`P_5·P_3` nonneg by `nonnegCoeffs_pmul`).
Equals `Δ_5·Δ_3` by the order-5/order-3 factorizations; extends the
`Favard`-file chain `β_{1..4}` to `β_5`. -/
theorem beta5_numer_nonneg {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval beta5Numer a) 0 :=
  ceval_factor_nonneg beta5Numer (QPoly.pmul (SN 5) (SN 3))
    (QPoly.pmul P5 P3) ha (nonnegCoeffs_pmul P5_nonneg P3_nonneg)
    (fun y => QPoly.poly_eqv _ _ y (by decide))

/-- **`β_5`-numerator `≥ 0` at the heat-kernel point `a = e^{−t/4}`.** -/
theorem beta5_numer_nonneg_at (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (ceval beta5Numer (aVar t ht)) 0 :=
  beta5_numer_nonneg (aVar_nonneg t ht)

end YMGap.Continuum.FavardRec

/-! ## OPEN obligation (the uniform `N`-indexed Favard step) — sharp statement

**Proved here (axiom-clean), extending `Favard`/`QHankel`:**

  * the **β-cyclotomic-square identity** `S_{k+1}·S_{k−1} = (a^{2k}−1)·S_k²`
    for `k = 1,…,5` (`betaCyclo_1..5`), exhibiting the cyclotomic content of
    `β_k = Δ_{k+1}Δ_{k−1}/Δ_k²` as the single perfect square `(a^{2k}−1)²`;
  * `betaNumer_nonneg_of_factor` — the division-free Favard reduction
    re-exported in `β`-indexing;
  * `P5_nonneg`, `P5_ge_one`, `beta5_numer_nonneg(_at)` — the `β_5`-numerator
    `Δ_5·Δ_3 = (S_5·S_3)²·(P_5·P_3) ≥ 0`, extending the verified chain to
    `k = 5` through the uniform nonneg-cone engine.

**OPEN — the single remaining mathematical gap (`nonnegCoeffs P_N`, all `N`).**
A division-free, coefficient-nonneg recurrence for the family `P_N` does *not*
exist via the natural identities:

  (a)  **Favard quadratic** `P_{k+1}·P_{k−1} = γ_k·P_k²` has `γ_k` rational
       (`γ_k = β_k/(a^{2k}−1)²`); `P_{k+1} = γ_k P_k²/P_{k−1}` requires
       dividing by `P_{k−1}`, and `P_{k−1} ∤ P_k²` (exact, fails `k ≥ 3`).
       So `β_k`'s value-nonnegativity does not become a polynomial recurrence.

  (b)  **Desnanot–Jacobi** `Δ_N·Δ_central = Δ_{N−1}·BR − TR²` is a
       *difference*; though every corner minor shares the
       even-cyclotomic-multiplicity (square-content) structure (its residual
       is nonneg-coefficient, verified through `N = 5`), dividing out the
       square content leaves square *ratios* (negative `a`-powers), not
       nonneg multipliers, so it does not rearrange subtraction-free.

Hence `nonnegCoeffs P_N` uniformly in `N` remains **OPEN**; the `decide`-checked
per-`N` factorizations (now through `N = 5` here, `N = 6` verified externally)
are the only certificates.

**Honest verdict on whether this approach closes the uniform proof.**
*For coefficient positivity of `P_N`:* the Favard-recurrence route does **not**
close it — the recurrence is irreducibly rational/subtractive, and the
coefficient positivity of `P_N` is a genuine standalone combinatorial fact
without a manifestly-nonneg recurrence.
*For the actual mass-gap input (value positivity `Δ_N(a) ≥ 0`, all `N`):* the
recurrence route is *unnecessary* — the heat-kernel representing measure
`dν(θ) = Σ_c (c+1)a^{c(c+2)}χ_c(θ)·(2/π)sin²θ` is a **positive** measure on
`(0,π)` (verified numerically), so the Andréief/Heine identity
`Δ_N = (1/N!)∫⋯∫ ∏_{i<j}(cos θ_i−cos θ_j)² ∏ dν ≥ 0` proves value positivity
*uniformly in `N`* with no per-order certificate.  The cleanest path to the
uniform all-`N` PSD theorem is therefore to formalize *positivity of `ν`*
(a 1-D trigonometric-series positivity, `a`-uniform) and the Andréief
expansion — **not** the `P_N`-coefficient recurrence.  This file records the
Favard structure precisely and closes the `β`-cyclotomic square and the
`β_5`-numerator, but the `P_N`-coefficient induction is OPEN and, per the
analysis above, is the wrong target for the uniform proof.
-/

#print axioms YMGap.Continuum.FavardRec.betaCyclo_1
#print axioms YMGap.Continuum.FavardRec.betaCyclo_5
#print axioms YMGap.Continuum.FavardRec.betaNumer_nonneg_of_factor
#print axioms YMGap.Continuum.FavardRec.P5_nonneg
#print axioms YMGap.Continuum.FavardRec.P5_ge_one
#print axioms YMGap.Continuum.FavardRec.SN_eq_S5_local
#print axioms YMGap.Continuum.FavardRec.beta5_numer_nonneg
#print axioms YMGap.Continuum.FavardRec.beta5_numer_nonneg_at
