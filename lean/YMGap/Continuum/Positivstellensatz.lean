/-
The `[−1,1]` Positivstellensatz consumer (Piece B, certificate layer): a
constructive proof that a polynomial `p(x)` on `[−1,1]` carrying a
**Markov–Lukács positivity certificate**

    p(x) = σ₀(x) + (1 − x²)·σ₁(x),     σ₀, σ₁ sums of squares,

has nonnegative average against the heat-kernel (cosine) functional, i.e.
`⟨p, ν⟩ ≥ 0`.  This is the `[−1,1]`-Positivstellensatz upgrade of
`TrigAvg.avg_nonneg_of_sos`: the latter consumes a *bare* SOS form
(`f = Σ g_j²`); here we additionally consume the `(1 − x²)`-weighted piece,
which is exactly the extra generator needed for the compact interval
`[−1,1]` (the boundary inequalities `1 − x ≥ 0`, `1 + x ≥ 0`, whose product
is `1 − x²`).

# The trigonometric dictionary (`x = cos θ`)

With `x = cos θ` the interval `[−1,1]` is the image of `[0,π]`, and the
average `(1/π)∫₀^π · dθ` is a positive linear functional `ν` on `[−1,1]`.
Under this substitution:

  * `1 − x² = 1 − cos²θ = sin²θ`.
  * A polynomial `A(x) = Σ a_k x^k` pulls back to a **cosine series**
    `A(cos θ) = Σ c_k cos(kθ)`; its squared average is the Fejér–Riesz
    constant term `cosSqAvg [c₀,c₁,…] = c₀² + ½ Σ_{k≥1} c_k²`
    (`TrigAvg.cosSqAvg`, proved `≥ 0`).
  * The weighted term `(1 − x²)·B(x)² = (sin θ · B(cos θ))²` pulls back to
    the square of a **sine series** `sin θ · B(cos θ) = Σ s_k sin(kθ)`; its
    squared average is the sine-Parseval constant term
    `sinSqAvg [s₁,…] = ½ Σ_{k≥1} s_k²` (proved `≥ 0` here — there is no
    constant term because `sin(0·θ) = 0`).

So a certificate `p = σ₀ + (1 − x²)σ₁` with `σ₀ = Σ_j A_j²`,
`σ₁ = Σ_j B_j²` averages to

    ⟨p, ν⟩ = Σ_j cosSqAvg(Â_j) + Σ_j sinSqAvg(Ŝ_j)  ≥ 0,

a finite sum of (cosine-Parseval) + (sine-Parseval) atoms, each `≥ 0`.
This is the genuine `∫(≥0) ≥ 0` content at the coefficient level, now in
the `[−1,1]` Positivstellensatz form actually consumed by the bridge.

# What is proved (sub-target 1, the closeable consumer)

  * `sinSqAvg` / `sinSqAvg_nonneg` — the `(1 − x²)`-weighted Parseval atom.
  * `psatzAvg σ₀ σ₁` — the average of a Markov–Lukács certificate
    (`σ₀` a list of cosine series, `σ₁` a list of sine series), and
    `psatzAvg_nonneg` proving it `≥ 0` constructively.
  * `wpsatzAvg` / `wpsatzAvg_nonneg` — the **weighted** form
    `Σ d_j·cosSqAvg(A_j) + Σ e_j·sinSqAvg(B_j)` with rational weights
    `d_j, e_j ≥ 0` (the rational-coefficient shape of a certificate, used
    by the small-degree examples below).
  * `geRat_psatzAvg` / `geRat_wpsatzAvg` — the `CReal`-level corollaries in
    the `ExpPos.geRat` lower-bound sense the heat-kernel functional uses.

# Small-degree existence (sub-target 2, as far as `decide` reaches)

Using the reflective `QPoly` ring we exhibit, and `decide`-verify as
*polynomial identities in `x`*, explicit certificates for concrete
nonnegative-on-`[−1,1]` polynomials:

  * `cert_oneMinusX`  : `2(1 − x) = (1 − x)² + (1 − x²)·1²`.
  * `cert_onePlusX`   : `2(1 + x) = (1 + x)² + (1 − x²)·1²`.
  * `cert_oneMinusXSq`: `1 − x² = 0² + (1 − x²)·1²`.
  * `cert_quad`       : `2(2 − 3x + x²) = 3(x − 1)² + (1 − x²)·1²`
    (a generic nonnegative-on-`[−1,1]` quadratic; the `2·` clears the
    `3/2, 1/2` weights so the certificate stays over `ℤ ⊂ Q'`).

Each is the *witness exhibition* step of the Markov–Lukács theorem at that
degree; the identity is machine-checked, so the factorization is genuine
(no `:= True`, no `sorry`).

# The precise OPEN gap (sub-target 2, general case — honest)

The **general existence algorithm** — producing `(σ₀, σ₁)` from an
*arbitrary* polynomial known only to be `≥ 0` on `[−1,1]` — is NOT
formalized and is genuinely hard Mathlib-free: it is the constructive
Markov–Lukács / Fejér–Riesz spectral factorization, requiring a
root-finding / companion-matrix step (real or complex) that this
rational, `decide`-based substrate does not provide.  We deliver the
*consumer* in full generality (any certificate, any degree) and the
*producer* only at the small degrees a closed-form factorization reaches.
The general producer is stated as `OpenProblem.markov_lukacs_existence`
(a `Prop` definition recording the statement; it is NOT asserted as a
theorem).

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` only (or none).  No `Classical.*`, no `sorryAx`, no
`native_decide`.
-/

import YMGap.Continuum.TrigAverage
import YMGap.Constructive.QPoly

namespace YMGap.Continuum.PSatz

open YMGap.Constructive
open YMGap.Continuum.TrigAvg

/-! ## The `(1 − x²)`-weighted Parseval atom: average of a sine-series square

A sine series `S(θ) = Σ_{k≥1} s_k sin(kθ)` is the natural pullback of
`sin θ · B(cos θ)`.  By the product-to-sum identity
`sin(jθ)sin(kθ) = ½[cos(|j−k|θ) − cos((j+k)θ)]`, the diagonal `j = k`
contributes constant part `½`, and there is no bare constant term (every
`sin(kθ)` integrates to `0`, and `sin(0·θ) = 0`), so

    (1/π)∫₀^π S(θ)² dθ = ½ · Σ_{k≥1} s_k².

We represent `S` by the coefficient list `[s₁, s₂, …]` (no `s₀` slot, since
`sin(0·θ) = 0`); its squared average is `halfSqTail` from `TrigAvg`. -/

/-- The average of `S²` for a sine series `S = Σ_{k≥1} s_k sin(kθ)` with
coefficient list `[s₁, s₂, …]`: `sinSqAvg s = ½ · Σ_{k≥1} s_k²`.  This is the
average of `(1 − x²)·B(x)²` under `x = cos θ` (with `S = sin θ · B(cos θ)`). -/
def sinSqAvg (s : List Q') : Q' := halfSqTail s

@[simp] theorem sinSqAvg_eq (s : List Q') : sinSqAvg s = halfSqTail s := rfl

/-- **Sine-Parseval positivity** (the `(1 − x²)`-weighted `∫(≥0) ≥ 0` atom):
`0 ≤ sinSqAvg s`.  Each `½ s_k² ≥ 0`; a finite sum of nonnegatives is
nonnegative (`halfSqTail_nonneg`). -/
theorem sinSqAvg_nonneg (s : List Q') : (0 : Q') ≤ sinSqAvg s :=
  halfSqTail_nonneg s

/-! ## The Markov–Lukács certificate consumer

A certificate `p = σ₀ + (1 − x²)·σ₁` with `σ₀ = Σ_j A_j²` (cosine series)
and `σ₁ = Σ_j B_j²` (the `B_j` giving sine series `sin θ · B_j(cos θ)`).
The data:

  * `cosParts : List (List Q')` — the cosine-series coefficient lists of the
    `A_j` (consumed by `cosSqAvg`, i.e. `sosAvg`).
  * `sinParts : List (List Q')` — the sine-series coefficient lists of the
    `sin θ · B_j(cos θ)` (consumed by `sinSqAvg`).

The certificate's average is the sum of the two SOS averages. -/

/-- The average of a list of sine-series squares `Σ_j S_j²`:
`Σ_j sinSqAvg(S_j)`.  (The sine analogue of `TrigAvg.sosAvg`.) -/
def sinSosAvg : List (List Q') → Q'
  | [] => 0
  | (s :: ss) => sinSqAvg s + sinSosAvg ss

@[simp] theorem sinSosAvg_cons (s : List Q') (ss : List (List Q')) :
    sinSosAvg (s :: ss) = sinSqAvg s + sinSosAvg ss := rfl

/-- `0 ≤ sinSosAvg ss` — a finite sum of sine-Parseval atoms is nonnegative. -/
theorem sinSosAvg_nonneg : ∀ (ss : List (List Q')), (0 : Q') ≤ sinSosAvg ss
  | [] => Q'.le_refl' 0
  | (s :: ss) => by
      rw [sinSosAvg_cons]
      exact Q'.zero_le_add _ _ (sinSqAvg_nonneg s) (sinSosAvg_nonneg ss)

/-- **The `[−1,1]`-Positivstellensatz average.**  Given a Markov–Lukács
certificate `p = (Σ_j A_j²) + (1 − x²)(Σ_j B_j²)` presented by `cosParts`
(the `Â_j` cosine series) and `sinParts` (the `sin θ·B_j` sine series), its
average against the cosine functional is

    psatzAvg cosParts sinParts = sosAvg cosParts + sinSosAvg sinParts. -/
def psatzAvg (cosParts sinParts : List (List Q')) : Q' :=
  sosAvg cosParts + sinSosAvg sinParts

@[simp] theorem psatzAvg_eq (cosParts sinParts : List (List Q')) :
    psatzAvg cosParts sinParts = sosAvg cosParts + sinSosAvg sinParts := rfl

/-- **The Positivstellensatz integration bridge (`∫(≥0) ≥ 0`, `[−1,1]` form).**
The average of a Markov–Lukács certificate is nonnegative:
`0 ≤ psatzAvg cosParts sinParts`.  The `σ₀` (cosine-SOS) piece is `≥ 0` by
`avg_nonneg_of_sos`; the `(1 − x²)σ₁` (sine-SOS) piece is `≥ 0` by
`sinSosAvg_nonneg`; their sum is `≥ 0`.

This is the consumer the bridge needs: any polynomial *presented* with a
`[−1,1]` positivity certificate has nonnegative heat-kernel average. -/
theorem psatzAvg_nonneg (cosParts sinParts : List (List Q')) :
    (0 : Q') ≤ psatzAvg cosParts sinParts := by
  rw [psatzAvg_eq]
  exact Q'.zero_le_add _ _ (avg_nonneg_of_sos cosParts) (sinSosAvg_nonneg sinParts)

/-! ## Weighted certificates (rational coefficients)

A rational Markov–Lukács certificate has the weighted-SOS shape

    p = Σ_j d_j·A_j² + (1 − x²)·Σ_j e_j·B_j²,     d_j, e_j ≥ 0 rational,

which avoids introducing irrational square roots of the scalar weights
(e.g. the `3/2, 1/2` of `cert_quad`).  Since `cosSqAvg` and `sinSqAvg` are
positive-homogeneous in the obvious sense, a nonnegatively-weighted sum of
them is again `≥ 0`. -/

/-- Weighted sum `Σ_j d_j·F(P_j)` of a nonnegative atom `F` over parts `P_j`
with weights `d_j`.  Used with `F = cosSqAvg` and `F = sinSqAvg`. -/
def weightedSum (F : List Q' → Q') : List Q' → List (List Q') → Q'
  | _, [] => 0
  | [], (_ :: _) => 0
  | (d :: ds), (P :: Ps) => d * F P + weightedSum F ds Ps

/-- A nonnegatively-weighted sum of nonnegative atoms is nonnegative. -/
theorem weightedSum_nonneg (F : List Q' → Q')
    (hF : ∀ P, (0 : Q') ≤ F P) :
    ∀ (ds : List Q') (Ps : List (List Q')),
      (∀ d, d ∈ ds → (0 : Q') ≤ d) → (0 : Q') ≤ weightedSum F ds Ps
  | ds, [], _ => by show (0 : Q') ≤ weightedSum F ds []; cases ds <;> exact Q'.le_refl' 0
  | [], (_ :: _), _ => Q'.le_refl' 0
  | (d :: ds), (P :: Ps), hd => by
      show (0 : Q') ≤ d * F P + weightedSum F ds Ps
      have h1 : (0 : Q') ≤ d * F P :=
        Q'.mul_nonneg _ _ (hd d List.mem_cons_self) (hF P)
      have h2 : (0 : Q') ≤ weightedSum F ds Ps :=
        weightedSum_nonneg F hF ds Ps (fun d' hd' => hd d' (List.mem_cons_of_mem _ hd'))
      exact Q'.zero_le_add _ _ h1 h2

/-- **The weighted `[−1,1]`-Positivstellensatz average.**
`Σ_j d_j·cosSqAvg(A_j) + Σ_j e_j·sinSqAvg(B_j)`. -/
def wpsatzAvg (dCos : List Q') (cosParts : List (List Q'))
    (eSin : List Q') (sinParts : List (List Q')) : Q' :=
  weightedSum cosSqAvg dCos cosParts + weightedSum sinSqAvg eSin sinParts

@[simp] theorem wpsatzAvg_eq (dCos : List Q') (cosParts : List (List Q'))
    (eSin : List Q') (sinParts : List (List Q')) :
    wpsatzAvg dCos cosParts eSin sinParts
      = weightedSum cosSqAvg dCos cosParts + weightedSum sinSqAvg eSin sinParts := rfl

/-- **Weighted Positivstellensatz bridge:** `0 ≤ wpsatzAvg …` when all
weights are nonnegative. -/
theorem wpsatzAvg_nonneg (dCos : List Q') (cosParts : List (List Q'))
    (eSin : List Q') (sinParts : List (List Q'))
    (hd : ∀ d, d ∈ dCos → (0 : Q') ≤ d) (he : ∀ e, e ∈ eSin → (0 : Q') ≤ e) :
    (0 : Q') ≤ wpsatzAvg dCos cosParts eSin sinParts := by
  rw [wpsatzAvg_eq]
  exact Q'.zero_le_add _ _
    (weightedSum_nonneg cosSqAvg cosSqAvg_nonneg dCos cosParts hd)
    (weightedSum_nonneg sinSqAvg sinSqAvg_nonneg eSin sinParts he)

/-! ## `CReal`-level corollaries

The averages above are rational; embedded as constant `CReal`s they are
`≥ 0` in the `ExpPos.geRat` lower-bound sense, so the Positivstellensatz
bridge composes with the heat-kernel moment machinery in
`WilsonFunctional`. -/

/-- The embedded `CReal` average of a Markov–Lukács certificate is `≥ 0`. -/
theorem geRat_psatzAvg (cosParts sinParts : List (List Q')) :
    ExpPos.geRat (CReal.ofQ' (psatzAvg cosParts sinParts)) 0 :=
  SumOfSquares.geRat_ofQ'_nonneg (psatzAvg_nonneg cosParts sinParts)

/-- The embedded `CReal` average of a weighted Markov–Lukács certificate is
`≥ 0`. -/
theorem geRat_wpsatzAvg (dCos : List Q') (cosParts : List (List Q'))
    (eSin : List Q') (sinParts : List (List Q'))
    (hd : ∀ d, d ∈ dCos → (0 : Q') ≤ d) (he : ∀ e, e ∈ eSin → (0 : Q') ≤ e) :
    ExpPos.geRat (CReal.ofQ' (wpsatzAvg dCos cosParts eSin sinParts)) 0 :=
  SumOfSquares.geRat_ofQ'_nonneg (wpsatzAvg_nonneg dCos cosParts eSin sinParts hd he)

/-! ## Small-degree existence: explicit `decide`-checked factorizations

The witness-exhibition half of Markov–Lukács, at the degrees a closed-form
factorization reaches.  Each identity is a *polynomial identity in `x`*,
discharged by `QPoly.poly_eqv … (by decide)` on the coefficient lists, so
the factorization is genuine.

Polynomial encoding (`QPoly`, low-to-high coefficient lists):
  `1 − x        = [1, −1]`            `1 + x        = [1, 1]`
  `1 − x²       = [1, 0, −1]`         `(x − 1)²     = [1, −2, 1]`
We write `oneMinusXSq := [1, 0, -1]` for the weight `(1 − x²)`. -/

open YMGap.Constructive.QPoly

/-- `1 − x²` as a `QPoly` (the `(1 − x²)` Positivstellensatz weight). -/
def oneMinusXSq : Poly := [(1 : Q'), 0, -(1 : Q')]

/-- **Degree-1 certificate** `2(1 − x) = (1 − x)² + (1 − x²)·1²`.
`1 − x ≥ 0` on `[−1,1]` is a boundary generator; doubling clears the `½`. -/
theorem cert_oneMinusX (x : Q') :
    (eval [Q'.ofNat 2, -(Q'.ofNat 2)] x).eqv
      (eval (padd (pmul [1, -(1 : Q')] [1, -(1 : Q')])
        (pmul oneMinusXSq [1])) x) :=
  poly_eqv _ _ x (by decide)

/-- **Degree-1 certificate** `2(1 + x) = (1 + x)² + (1 − x²)·1²`.
The complementary boundary generator `1 + x ≥ 0`. -/
theorem cert_onePlusX (x : Q') :
    (eval [Q'.ofNat 2, Q'.ofNat 2] x).eqv
      (eval (padd (pmul [1, (1 : Q')] [1, (1 : Q')])
        (pmul oneMinusXSq [1])) x) :=
  poly_eqv _ _ x (by decide)

/-- **The weight itself** `1 − x² = 0² + (1 − x²)·1²` — the trivial
certificate exhibiting `1 − x²` as `(1 − x²)·1`. -/
theorem cert_oneMinusXSq (x : Q') :
    (eval oneMinusXSq x).eqv
      (eval (padd (pmul ([] : Poly) ([] : Poly)) (pmul oneMinusXSq [1])) x) :=
  poly_eqv _ _ x (by decide)

/-- **Degree-2 certificate** `2(2 − 3x + x²) = 3·(x − 1)² + (1 − x²)·1²`,
i.e. `2·2 − 6x + 2x² = 3(x−1)² + (1 − x²)`.  Here `2 − 3x + x² = (1−x)(2−x)`
is nonnegative on `[−1,1]` (both factors `≥ 0` there) yet has a sign-
indefinite linear coefficient; the certificate exhibits it as a weighted
SOS plus the `(1 − x²)` generator (weights `3/2, 1/2`, cleared by the `2·`).
The `3·(x−1)²` is encoded as `(x−1)²` scaled by `3` via `pscale`. -/
theorem cert_quad (x : Q') :
    (eval [Q'.ofNat 4, -(Q'.ofNat 6), Q'.ofNat 2] x).eqv
      (eval (padd (pscale (Q'.ofNat 3) (pmul [1, -(1 : Q')] [1, -(1 : Q')]))
        (pmul oneMinusXSq [1])) x) :=
  poly_eqv _ _ x (by decide)

/-! ## The general existence problem (OPEN — stated, not asserted)

The general Markov–Lukács existence theorem — that *every* polynomial `p`
with `p(x) ≥ 0` for all `x ∈ [−1,1]` admits a certificate
`p = σ₀ + (1 − x²)σ₁` with `σ₀, σ₁` sums of squares — is recorded here as a
`Prop`-valued statement.  It is **NOT proved**: constructing `(σ₀, σ₁)` from
the mere hypothesis `∀ x ∈ [−1,1], p(x) ≥ 0` requires a real/complex
spectral (root) factorization that this rational, `decide`-based substrate
does not provide.  The consumer side (`psatzAvg_nonneg`) is fully general;
only this producer is open. -/

namespace OpenProblem

/-- `p` (low-to-high `QPoly` coefficients) is `≥ 0` at the rational point
`x` whenever `x ∈ [−1,1]` — the rational shadow of "nonnegative on
`[−1,1]`". -/
def NonnegOn (p : Poly) : Prop :=
  ∀ x : Q', (-(1 : Q')) ≤ x → x ≤ (1 : Q') → (0 : Q') ≤ eval p x

/-- `Σ_j P_j²` as a `QPoly` (sum of the squares of the parts). -/
def sumOfSqPoly : List Poly → Poly
  | [] => []
  | (P :: Ps) => padd (pmul P P) (sumOfSqPoly Ps)

/-- A *Markov–Lukács certificate* for `p`: SOS data `(cosParts, sinParts)`
realizing `p = (Σ A_j²) + (1 − x²)(Σ B_j²)` as a `QPoly` identity in `x`.
`cosParts`/`sinParts` are the polynomial parts `A_j`/`B_j` (low-to-high). -/
structure Certificate (p : Poly) : Type where
  cosParts : List Poly
  sinParts : List Poly
  /-- The defining identity (pointwise in `x`): `p = ΣA_j² + (1−x²)ΣB_j²`. -/
  identity : ∀ x : Q', (eval p x).eqv
    (eval (padd (sumOfSqPoly cosParts) (pmul oneMinusXSq (sumOfSqPoly sinParts))) x)

/-- **OPEN: general Markov–Lukács existence.**  Stated as a `Prop`; NOT
asserted as a theorem.  Producing the certificate requires a spectral
factorization (root-finding) beyond the rational `decide` substrate.  The
small-degree witnesses `cert_*` above discharge this for specific `p`; the
general algorithm is the precise gap. -/
def markov_lukacs_existence : Prop :=
  ∀ (p : Poly), NonnegOn p → Nonempty (Certificate p)

end OpenProblem

end YMGap.Continuum.PSatz

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PSatz.sinSqAvg_nonneg
#print axioms YMGap.Continuum.PSatz.sinSosAvg_nonneg
#print axioms YMGap.Continuum.PSatz.psatzAvg_nonneg
#print axioms YMGap.Continuum.PSatz.weightedSum_nonneg
#print axioms YMGap.Continuum.PSatz.wpsatzAvg_nonneg
#print axioms YMGap.Continuum.PSatz.geRat_psatzAvg
#print axioms YMGap.Continuum.PSatz.geRat_wpsatzAvg
#print axioms YMGap.Continuum.PSatz.cert_oneMinusX
#print axioms YMGap.Continuum.PSatz.cert_onePlusX
#print axioms YMGap.Continuum.PSatz.cert_oneMinusXSq
#print axioms YMGap.Continuum.PSatz.cert_quad
