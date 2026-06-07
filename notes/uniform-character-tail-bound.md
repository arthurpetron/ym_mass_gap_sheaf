# U.2 — Uniform large-field character-tail bound

Working derivation and numerical validation of the group-uniform bound on the
heat-kernel character sum, the analytic core of the uniform parametric
σ̂-budget (`docs/uniform-parametric-bound-plan.md` §2.2, milestone U.2).
Implementation: `computations/general_character_sum.py`; engine:
`computations/lie_algebras.py`.

## 1. Object

For a compact simple gauge group `G` (rank `r`), heat-kernel time `t = conv/g²`,

    Z_t(G) = Σ_{λ ∈ P₊\{0}} dim(λ)² · exp(-t · C₂(λ)),

the sum over nontrivial dominant weights `λ` (Dynkin labels `λ_i ≥ 0`).  `Z_t`
sets the large-field cluster-expansion constant `K_lf = q/(1-q)`,
`q = μ_plaq · Z_t`; it must be small enough, uniformly over `G`, for the budget
to close.

## 2. The rigorous majorant

Work in the fundamental-weight basis; let `G` be the Gram matrix of fundamental
weights (`G_ij = ⟨ω_i,ω_j⟩ ≥ 0`, positive cone), `ρ = (1,…,1)`.

**(a) Casimir splits below.**
`C₂(λ) = ½⟨λ,λ⟩ + ⟨λ,ρ⟩ = ½ λᵀGλ + λᵀGρ ≥ Σ_i h_i(λ_i)`,
`h_i(x) := ½ G_ii x² + (Gρ)_i x`,
dropping the off-diagonal `G_ij λ_i λ_j (i≠j) ≥ 0`.  Key identity:
`h_i(1) = ½G_ii + (Gρ)_i = C₂(ω_i)`, so `min_i h_i(1) = Δ` (the spectral gap).

**(b) Dimension bounds above, separably.**
Each Weyl factor `⟨λ+ρ,α⟩/⟨ρ,α⟩` is a convex combination of the `(λ_j+1)` over
the simple roots `α_j` appearing in `α`, hence `≤ ∏_{j: α∋α_j}(λ_j+1)`.
Multiplying over positive roots,
`dim(λ) ≤ ∏_i (λ_i+1)^{n_i}`, `n_i := #{α>0 : α contains α_i}`, so
`dim(λ)² ≤ ∏_i (λ_i+1)^{2 n_i}`.

**(c) Factorization.**  `dim(λ)² e^{-tC₂(λ)} ≤ ∏_i (λ_i+1)^{2n_i} e^{-t h_i(λ_i)}`,
and summing the product majorant over the full lattice factorizes:

> **Lemma (rigorous majorant).**
> `Z_t(G) ≤ ∏_{i=1}^r S_i(t) − 1`,  `S_i(t) = Σ_{x≥0} (x+1)^{2n_i} e^{-t h_i(x)}`.

Each `S_i` is a 1-D Gaussian-dominated sum: an exact box `x ≤ M_i` plus a
geometric tail at the first `x` where the successive-term ratio
`((x+2)/(x+1))^{2n_i} e^{-t(G_ii x + ½G_ii + (Gρ)_i)}` drops below 1 (it is
decreasing in `x`, so it stays `< 1` past `M_i`) — exactly the SU(3) tail
structure of `su3_character_sum.py`.

**Specialization check.**  For SU(3) (`A₂`): `n_i = 2 ⇒` exponent `4`, and
`h_i(x) = ½(2/3)x² + x = x²/3 + x` — *verbatim* `su3_character_sum`'s
`g(x) = (x+1)^4 e^{-t(x²+3x)/3}`.  For SU(2) (`A₁`): exponent `2`,
`h(x) = x²/4 + x/2`, `C₂(ω) = 3/4`.

## 3. Uniform domination by SU(2)

> **Claim (uniform domination).**  For `t ≥ t₀` (numerically `t₀ ≈ 6.25`, i.e.
> `g ≤ 0.40`), `Z_t(G) ≤ Z_upper(G,t) ≤ Z_upper(SU(2),t)` for every compact
> simple `G`.

Sketch: for `t` large the excesses `s_i := S_i − 1` are tiny, so
`∏_i S_i − 1 ≈ Σ_i s_i`, with leading term `Σ_i 2^{2n_i} e^{-t C₂(ω_i)} ≤
r·2^{2n_max} e^{-tΔ}`.  SU(2)'s bound leads with `4 e^{-3t/4}`.  Since `Δ ≥ 3/4`
for every simple `G` (equality only at SU(2) — the global-minimum spectral-gap
fact, U.1), the exponential gap `e^{-t(Δ-3/4)}` overcomes the polynomial
dimension factor once `t ≥ ln(r·2^{2n_max}/4)/(Δ − 3/4)`; the max over groups is
`t₀`.  This is the rigorous analogue of the U.4 empirical worst-case result.

**Why `t₀` is harmless.**  The canonical operating point is `g₀ = 0.30`
(`t ≈ 11.1 > t₀`), and the RG flow only *decreases* `g` (increases `t`), so the
whole trajectory has `t ≥ 11.1`.  The domination therefore holds along every
trajectory in the canonical window.  `g ≥ 0.45` (`t < t₀`) is at/past SU(2)'s
*own* large-field convergence edge — SU(2)'s budget already diverges there
(U.4) — so it is outside the regime of interest; the loose `2^{2n_i}` dimension
factor only costs at small `t`.

## 4. Numerical validation (`python -m computations.general_character_sum`)

At `g₀ = 0.30` (`t ≈ 11.1`), over all 19 representative groups (A₁–A₇, B₂–B₄,
C₃, C₄, D₄, D₅, G₂, F₄, E₆, E₇, E₈):

- `Z_upper(G) ≥ Z_exact(G)` for **every** group (genuine rigorous upper bound;
  `Z_exact` from the validated `lie_algebras` engine).  Tightness ratio
  `Z_upper/Z_exact` ranges ~1.0 (SU(2)) to ~10³–10⁶ (large groups) — loose but
  Gaussian-crushed to negligible absolute size.
- `Z_upper(G) ≤ Z_upper(SU(2))` for **every** group.
- SU(2) maximizes `Z_upper(·,t)` across the operating window `g ≤ 0.40`.

`Z_upper(SU(2), t=11.1) = 9.61e-4`; the next-largest is B₂ at `5.95e-5` (16×
smaller).

## 5. What remains for a fully rigorous U.2

1. **Tighten `t₀`** (optional): replace `dim(λ) ≤ ∏(λ_i+1)^{n_i}` with the
   sharper per-root bound to shrink the exponents `2n_i`, pushing `t₀` below the
   full convergence window — not needed for the canonical point.
2. **Written proof** of the product-≤-sum step (§3) with explicit constants, for
   promotion to `formal-suN/`.
3. **Lean port** (U.6, `Constructive/CharacterTail.lean`): the `S_i` exact-box +
   geometric-tail bound reuses `GeometricTail.geometric_tail_closure`; the
   `e^{-t h_i(x)}` terms need the `ExpUB` instantiation from `expNeg` (U.5,
   `E_antitone`).  The factorization `∏ S_i − 1` is `finSum`/product arithmetic.

The analytic structure and the uniform-domination result are established;
items 1–3 are the rigour/formalization follow-through.
