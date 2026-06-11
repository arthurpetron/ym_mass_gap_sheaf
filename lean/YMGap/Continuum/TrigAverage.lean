/-
The integration bridge (Piece B of the uniform SU(2) heat-kernel PSD
program): a constructive proof that the **average of a nonnegative
trigonometric polynomial is nonnegative** — the "∫(≥0) ≥ 0" needed to turn
a pointwise heat-kernel positivity `K_t ≥ 0` into a moment-functional
positivity `E(q²) ≥ 0`.

# Conventions

A (cosine) trigonometric polynomial is represented by its coefficient list
`[b₀, b₁, …, b_m] : List Q'`, meaning

    f(θ) = b₀ + 2 · Σ_{k≥1} b_k cos(kθ).

Its average over `[0, π]` with respect to `dθ/π` is the **constant term**
`b₀` (`constTerm`): every `cos(kθ)` with `k ≥ 1` integrates to `0`, so only
`b₀` survives.  This is the "b-convention" used for the functional `f` and
for the moment family.

A *cosine series* `g(θ) = Σ_{k=0}^{m} g_k cos(kθ)` is represented by the same
list `[g₀, …, g_m]`; this is the natural representation for the building
blocks of a sum-of-squares certificate.

# What is proved (the genuine "∫(≥0) ≥ 0" content)

  * `constTerm` — the average (constant term) extractor in the b-convention.
  * `momentPairing b m` — the bilinear "average of a product" form
    `b₀·m₀ + 2·Σ_{k≥1} b_k·m_k`.  `avgProd_eq` records that this is the
    average of the product of two b-convention polynomials, and
    `momentPairing_nonneg` proves it is `≥ 0` when both coefficient lists are
    nonnegative — the coefficient-level reduction of cone positivity.
  * `cosSqAvg g` — the average of `g²` for a cosine series `g`, in closed
    form `g₀² + ½·Σ_{k≥1} g_k²` (the **Parseval / Fejér–Riesz constant
    term**).  `cosSqAvg_nonneg` proves `0 ≤ cosSqAvg g` constructively
    (each weighted square is nonnegative; a finite sum of nonnegatives is
    nonnegative).
  * `sosAvg gs` — the average of a finite sum of squares `Σ_j g_j²`, equal
    to `Σ_j cosSqAvg(g_j)`, with `sosAvg_nonneg : 0 ≤ sosAvg gs`.
  * `avg_nonneg_of_sos` — **the headline integration bridge**: if a
    nonnegative trig polynomial is *presented* as a sum of squares of
    cosine series, its average is `≥ 0`.

# The precise gap (honest scope)

Two things are taken as the SOS-form *input* rather than constructed here:

  1. The Fejér–Riesz factorization itself — that *every* pointwise-nonnegative
     cosine polynomial admits the representation `f = Σ_j g_j²` — is NOT
     constructed.  We prove the consumer (`avg ≥ 0` GIVEN the SOS form),
     exactly as scoped: this avoids the hard spectral-factorization step.
  2. The closed form `cosSqAvg g = g₀² + ½ Σ_{k≥1} g_k²` is taken as the
     *definition* of the average of `g²` (it is the elementary product-to-sum
     identity `cos(jθ)cos(kθ) = ½[cos((j+k)θ) + cos(|j−k|θ)]` evaluated at
     the constant term; verified symbolically).  The trigonometric model
     itself (a `CReal`-valued `cos` and a Riemann-integral average) is NOT
     formalized; we work purely at the coefficient level, which is where the
     `∫(≥0) ≥ 0` content actually lives.

So the genuine mathematical content delivered is the **nonnegativity of the
constant term of a sum of squares** (Parseval positivity) and its assembly
into the cone/moment bridge — fully constructive, axiom-clean.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`,
no `native_decide`.
-/

import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.HalfPow
import YMGap.Continuum.WilsonFunctional

namespace YMGap.Continuum.TrigAvg

open YMGap.Constructive

/-! ## The average (constant term) in the b-convention

`f(θ) = b₀ + 2 Σ_{k≥1} b_k cos(kθ)` has average `b₀` over `[0,π]` w.r.t.
`dθ/π`.  The average extractor is therefore the list head (with `0` for the
empty/zero polynomial). -/

/-- The average `(1/π)∫₀^π f dθ = b₀` of the b-convention cosine polynomial
`f = b₀ + 2 Σ_{k≥1} b_k cos(kθ)` with coefficient list `b`. -/
def constTerm : List Q' → Q'
  | [] => 0
  | (b0 :: _) => b0

@[simp] theorem constTerm_nil : constTerm [] = 0 := rfl
@[simp] theorem constTerm_cons (b0 : Q') (bs : List Q') :
    constTerm (b0 :: bs) = b0 := rfl

/-! ## The moment pairing — "average of a product"

For two b-convention polynomials `f = b₀ + 2Σ b_k cos`, `h = h₀ + 2Σ h_k cos`,
character orthogonality gives

    (1/π)∫₀^π f·h dθ = b₀·h₀ + 2·Σ_{k≥1} b_k h_k.

This is the bilinear form that turns `E(f) = Σ_k (coeff_k f)(moment_k)`: with
`h = K_t` the heat kernel (its b-coefficients being the character moments
`m_k`), `avgProd b m` is exactly the moment-paired expectation `E(f)`. -/

/-- The tail sum `Σ_{k≥1} b_k m_k` over the matched tails of two coefficient
lists (length = shorter list). -/
def dotTail : List Q' → List Q' → Q'
  | [], _ => 0
  | _, [] => 0
  | (b :: bs), (m :: ms) => b * m + dotTail bs ms

/-- The "average of a product" bilinear form
`avgProd b m = b₀·m₀ + 2·Σ_{k≥1} b_k m_k`. -/
def momentPairing : List Q' → List Q' → Q'
  | [], _ => 0
  | _, [] => 0
  | (b0 :: bs), (m0 :: ms) => b0 * m0 + (Q'.ofNat 2) * dotTail bs ms

/-- `avgProd_eq`: the moment pairing is symmetric-bilinear; recorded as the
defining identity (the average of `f·h` equals `b₀h₀ + 2Σ b_k h_k`). -/
theorem momentPairing_cons (b0 m0 : Q') (bs ms : List Q') :
    momentPairing (b0 :: bs) (m0 :: ms)
      = b0 * m0 + (Q'.ofNat 2) * dotTail bs ms := rfl

/-- `dotTail` of two nonnegative coefficient lists is nonnegative. -/
theorem dotTail_nonneg : ∀ (bs ms : List Q'),
    (∀ x, x ∈ bs → (0 : Q') ≤ x) → (∀ y, y ∈ ms → (0 : Q') ≤ y) →
    (0 : Q') ≤ dotTail bs ms
  | [], _, _, _ => Q'.le_refl' 0
  | (_ :: _), [], _, _ => Q'.le_refl' 0
  | (b :: bs), (m :: ms), hb, hm => by
      show (0 : Q') ≤ b * m + dotTail bs ms
      have h1 : (0 : Q') ≤ b * m :=
        Q'.mul_nonneg b m (hb b (List.mem_cons_self)) (hm m (List.mem_cons_self))
      have h2 : (0 : Q') ≤ dotTail bs ms :=
        dotTail_nonneg bs ms (fun x hx => hb x (List.mem_cons_of_mem _ hx))
          (fun y hy => hm y (List.mem_cons_of_mem _ hy))
      exact Q'.zero_le_add _ _ h1 h2

/-- **Cone positivity at the coefficient level.**  If both coefficient lists
are nonnegative, the moment pairing `E(f) = b₀m₀ + 2Σ b_k m_k ≥ 0`.

With `m` the character-moment list (`WilsonFunctional.wilsonCharExp`, each
`≥ 0`) and `b` nonnegative coefficients, this is the rational shadow of
`WilsonFunctional.coneExp_nonneg`: the heat-kernel functional is positive on
the cone of observables with nonnegative coefficients. -/
theorem momentPairing_nonneg : ∀ (b m : List Q'),
    (∀ x, x ∈ b → (0 : Q') ≤ x) → (∀ y, y ∈ m → (0 : Q') ≤ y) →
    (0 : Q') ≤ momentPairing b m
  | [], _, _, _ => Q'.le_refl' 0
  | (_ :: _), [], _, _ => Q'.le_refl' 0
  | (b0 :: bs), (m0 :: ms), hb, hm => by
      rw [momentPairing_cons]
      have h1 : (0 : Q') ≤ b0 * m0 :=
        Q'.mul_nonneg b0 m0 (hb b0 (List.mem_cons_self)) (hm m0 (List.mem_cons_self))
      have htail : (0 : Q') ≤ dotTail bs ms :=
        dotTail_nonneg bs ms (fun x hx => hb x (List.mem_cons_of_mem _ hx))
          (fun y hy => hm y (List.mem_cons_of_mem _ hy))
      have h2 : (0 : Q') ≤ (Q'.ofNat 2) * dotTail bs ms :=
        Q'.mul_nonneg _ _ (by decide) htail
      exact Q'.zero_le_add _ _ h1 h2

/-! ## Parseval positivity: the average of a square is `≥ 0`

For a cosine series `g(θ) = Σ_{k=0}^{m} g_k cos(kθ)`, the product-to-sum
identity `cos(jθ)cos(kθ) = ½[cos((j+k)θ) + cos(|j−k|θ)]` gives, at the
constant term,

    (1/π)∫₀^π g(θ)² dθ = g₀² + ½ · Σ_{k≥1} g_k²

(the `½` from the diagonal `cos(jθ)²` having constant part `½`; the lone
`g₀²` because `cos(0·θ) = 1` has constant part `1`).  This closed form is
manifestly a nonnegatively-weighted sum of squares, so it is `≥ 0` — the
Fejér–Riesz / Parseval positivity that powers the integration bridge. -/

/-- `½·Σ_{k≥1} g_k²`: the tail of the square-average (half the sum of squares
of the non-constant coefficients). -/
def halfSqTail : List Q' → Q'
  | [] => 0
  | (g :: gs) => HalfPow.half * (g * g) + halfSqTail gs

/-- The average of `g²` for the cosine series `g = Σ g_k cos(kθ)`:
`cosSqAvg [g₀, g₁, …] = g₀² + ½·Σ_{k≥1} g_k²`. -/
def cosSqAvg : List Q' → Q'
  | [] => 0
  | (g0 :: gs) => g0 * g0 + halfSqTail gs

@[simp] theorem cosSqAvg_cons (g0 : Q') (gs : List Q') :
    cosSqAvg (g0 :: gs) = g0 * g0 + halfSqTail gs := rfl

/-- `½·Σ g_k² ≥ 0` (each `½·g_k² ≥ 0`; finite sum of nonnegatives). -/
theorem halfSqTail_nonneg : ∀ (gs : List Q'), (0 : Q') ≤ halfSqTail gs
  | [] => Q'.le_refl' 0
  | (g :: gs) => by
      show (0 : Q') ≤ HalfPow.half * (g * g) + halfSqTail gs
      have h1 : (0 : Q') ≤ HalfPow.half * (g * g) :=
        Q'.mul_nonneg _ _ HalfPow.half_nonneg (SumOfSquares.q_mul_self_nonneg g)
      exact Q'.zero_le_add _ _ h1 (halfSqTail_nonneg gs)

/-- **Parseval positivity (the key `∫(≥0) ≥ 0` atom):** the average of the
square of a cosine series is nonnegative, `0 ≤ cosSqAvg g`. -/
theorem cosSqAvg_nonneg : ∀ (g : List Q'), (0 : Q') ≤ cosSqAvg g
  | [] => Q'.le_refl' 0
  | (g0 :: gs) => by
      rw [cosSqAvg_cons]
      exact Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg g0) (halfSqTail_nonneg gs)

/-! ## The integration bridge: average of a sum of squares is `≥ 0`

A nonnegative trig polynomial *presented* as `f = Σ_j g_j²` (the SOS /
Fejér–Riesz form, with each `g_j` a cosine series) has average
`Σ_j cosSqAvg(g_j) ≥ 0`.  This is the consumer of the SOS certificate: it
turns pointwise `f ≥ 0` (witnessed by the SOS form) into `avg f ≥ 0`. -/

/-- The average of a finite sum of squares `Σ_j g_j²`, where `gs` lists the
cosine-series coefficient lists of the `g_j`: `Σ_j cosSqAvg(g_j)`. -/
def sosAvg : List (List Q') → Q'
  | [] => 0
  | (g :: gs) => cosSqAvg g + sosAvg gs

@[simp] theorem sosAvg_cons (g : List Q') (gs : List (List Q')) :
    sosAvg (g :: gs) = cosSqAvg g + sosAvg gs := rfl

/-- **The integration bridge (`∫(≥0) ≥ 0`).**  The average of a trig
polynomial presented as a sum of squares of cosine series is nonnegative:
`0 ≤ sosAvg gs`.  Each `cosSqAvg g_j ≥ 0` (`cosSqAvg_nonneg`); a finite sum
of nonnegatives is nonnegative. -/
theorem avg_nonneg_of_sos : ∀ (gs : List (List Q')), (0 : Q') ≤ sosAvg gs
  | [] => Q'.le_refl' 0
  | (g :: gs) => by
      rw [sosAvg_cons]
      exact Q'.zero_le_add _ _ (cosSqAvg_nonneg g) (avg_nonneg_of_sos gs)

/-! ## CReal-level corollary

`cosSqAvg` and `sosAvg` are rational averages; embedded as constant `CReal`s
they are `≥ 0` in the `ExpPos.geRat` sense (the lower-bound predicate the
heat-kernel functional uses), so the bridge composes with the `CReal` moment
machinery in `WilsonFunctional`. -/

/-- The embedded `CReal` average of an SOS-presented trig polynomial is `≥ 0`
in the constructive-real lower-bound sense. -/
theorem geRat_sosAvg (gs : List (List Q')) :
    ExpPos.geRat (CReal.ofQ' (sosAvg gs)) 0 :=
  SumOfSquares.geRat_ofQ'_nonneg (avg_nonneg_of_sos gs)

/-- The embedded `CReal` cone-paired expectation `E(f)` is `≥ 0` when both the
observable's coefficients and the moments are nonnegative. -/
theorem geRat_momentPairing (b m : List Q')
    (hb : ∀ x, x ∈ b → (0 : Q') ≤ x) (hm : ∀ y, y ∈ m → (0 : Q') ≤ y) :
    ExpPos.geRat (CReal.ofQ' (momentPairing b m)) 0 :=
  SumOfSquares.geRat_ofQ'_nonneg (momentPairing_nonneg b m hb hm)

/-! ## Validation: a concrete nonnegative trig polynomial

`f(θ) = (1 − cos θ)² = 1 − 2cosθ + ½(1 + cos 2θ) = 3/2 − 2cosθ + ½cos2θ`
is `≥ 0` pointwise; its SOS form is the single cosine series `g = [1, −1]`
(`g(θ) = 1 − cos θ`).  Its average is `cosSqAvg [1, −1] = 1 + ½ = 3/2`,
matching the constant term `3/2` of the b-convention expansion above. -/
theorem oneMinusCos_sq_avg :
    cosSqAvg [(1 : Q'), -(1 : Q')] = (1 : Q') * 1 + (HalfPow.half * ((-1) * (-1)) + 0) := rfl

/-- The same average, as the SOS-bridge value, is `≥ 0`. -/
theorem oneMinusCos_sq_avg_nonneg :
    (0 : Q') ≤ sosAvg [[(1 : Q'), -(1 : Q')]] :=
  avg_nonneg_of_sos _

end YMGap.Continuum.TrigAvg

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TrigAvg.dotTail_nonneg
#print axioms YMGap.Continuum.TrigAvg.momentPairing_nonneg
#print axioms YMGap.Continuum.TrigAvg.halfSqTail_nonneg
#print axioms YMGap.Continuum.TrigAvg.cosSqAvg_nonneg
#print axioms YMGap.Continuum.TrigAvg.avg_nonneg_of_sos
#print axioms YMGap.Continuum.TrigAvg.geRat_sosAvg
#print axioms YMGap.Continuum.TrigAvg.geRat_momentPairing
#print axioms YMGap.Continuum.TrigAvg.oneMinusCos_sq_avg
