# Scoping note: formalising task2h (a) Bessel-ratio bounds and (d) error propagation (2026-11-16)

**Scoping only. No Lean work has started on these items.** I read "(a)" as proof note §2 plus §3 (the I₂/I₁ bounds:
Lemma R, the inputs L1/L1′/L2, and the map Lemmas N/M that consume them). I read "(d)" as §4 (4a)–(4j), including
Lemma F (4f) and Lemma G (4g). The line estimates are rough, extrapolated from today's files: about 310 lines for the
series brackets and 170 lines for the strict floor.

## Infrastructure available in the repo
- `Q'`: exact unnormalised rationals, with the order, eqv and mul/add monotonicity lemmas used today.
- The NQ semantic bridge (`Robust3SeriesBrackets`).
- `CReal` `log2 = 2·artanh(1/3)`, with rational enclosures (`log2_geRat_lower`, `log2_leRat_upper`), and `CReal` `pi`.
- **There is no** calculus library: no derivative, ODE, Gronwall or IVT, and no Bessel I_ν as functions.
  (The existing `*HeatGramBessel` files concern SU(2) heat channels, not I₂/I₁.)
- **There are no** `ring`, `nlinarith` or `positivity` tactics; `omega` and `grind` are excluded (grind pulls in
  Classical.choice). Nonlinear identities can be done with `simp only` AC-normalisation, as today, but slowly.

## (a) Bessel-ratio bounds
**Route A, conditional (recommended): ~350–600 lines.**
- State r(x) = I₂/I₁ abstractly, as a function `Q' → Q'` or as interval data, with named hypotheses:
  - `L1_OPEN`: r is monotone;
  - `RICCATI_COMPARISON_OPEN`: super- and sub-solutions of r′ = 1 − 3r/x − r² bound r on [1000, ∞);
  - `R1000_OPEN`: an interval for r(1000).
- Then formalise:
  1. Lemma P1 in general, for one-variable rational polynomial positivity with p_k > 0 and tail ≤ p_k/2: ~120–180
     lines.
  2. The concrete certificate polynomials from `results/task2i_maps.json`, checked by `decide +kernel` on
     exact-rational coefficients (degree ≤ 23; R±, N±, M±, g±): ~100–200 lines. **Cost risk:** kernel evaluation of
     degree-23 rational polynomials with large coefficients; per-polynomial RSS needs measuring first.
  3. Lemma R from the hypotheses plus P1: ~60 lines.
  4. Lemma N, which needs the log Taylor bounds (I3) as `Q'` interval lemmas: ~80–120 lines.
  5. Lemma M: a sign-change argument through `L1_OPEN`; existence of β_c is either a hypothesis or uses a located
     root: ~80–120 lines.

**Route B, unconditional: blocked, roughly ≥ 2500 lines.** It would need:
- I₁ and I₂ as constructive series, with uniform convergence;
- the derivative identities (DLMF 10.29.2);
- the Riccati ODE;
- a comparison principle (Gronwall) on CReal functions;
- monotonicity of I₂/I₁ (Amos/Segura);
- a constructive IVT (approximate only) for β_c.

None of these exist, and building calculus Mathlib-free is a project in itself.

**Blockers:**
- no calculus;
- L1 is cited, not elementary;
- β_c existence needs a constructive IVT or a reformulation as an interval enclosure;
- `decide` cost on the big certificates is unknown.

## (d) Error propagation §4 (4a)–(4j)
**Estimate: ~1500–3000 lines, conditional on (a) via Lemmas N/M plus `SERIES_LIMITS_OPEN`.**
- The quantities are rational functions of a symbolic m ≥ 10⁶ (via x = 1/m), plus logs and the constants B, κ′, ln2,
  q and a_i.
- Each of (4a)–(4j) is an explicit two-sided interval inequality. In Lean each becomes a symbolic polynomial
  inequality in m, which has to be proved by hand-normalised algebra (no ring or nlinarith). Today's experience is
  roughly 20–40 lines per nontrivial rational inequality.

**Needed interfaces:**
- **I3** (log Taylor bounds) as `Q'`-interval lemmas for −ln(1−x), ln(1+u) and artanh, over the repo's `CReal` log or
  stated via rational enclosures: ~150–250 lines. Partly present: `logRat` window and series.
- **I2** (1 ≤ H_m ≤ ln m + 1) needs a log comparison: ~80–150 lines, or keep it as a named hypothesis.
- **Rational enclosures of B, κ′, ln2 and q.** ln2 is available (`log2Lower/Upper`). π² is available through the
  proved partial-sum bracket plus `SERIES_LIMITS_OPEN`, or via `pi`.
- **Lemma F** (Lean vs ideal constants) uses exactly today's brackets: L_n monotone, P_n monotone, t ≤ 4^{-n-1}.
  This is the most tractable item, at ~150–250 lines.
- **Lemma P (§5)**: 16 multivariate certificates in (x, h, d) with arb-ball coefficients and symbolic B, κ′, ln2, q.
  They would need re-certification with exact rational interval coefficients before Lean can check them. This is a
  Numerics-side task first; the Lean side is then ~200–400 lines plus the kernel-cost risk.

**Blockers:**
- no nonlinear arithmetic automation;
- logs enter non-polynomially;
- the arb-ball certificates must be converted to exact rationals;
- (4a)–(4e), (4h), (4i) and (4j) are still handwritten sketches with crude constants. Numerics plans to recast them as
  interval lemmas, and formalising before that would duplicate work.

## Recommended order (if approved later)
1. Lemma F (uses today's brackets).
2. Lemma P1 plus one small certificate, to measure `decide +kernel` cost.
3. I3 log interval lemmas.
4. Lemma N.
5. Conditional Lemma R/M.
6. (4a)–(4e) once Numerics publishes them in lemma form.

The arb range for 10 ≤ j ≤ 10⁷ stays computer-assisted in every scenario. It is too large for per-j Lean checks.

**δ_min = 0 is only a necessary condition: it removes the obstruction but does not prove hafδ.** Build caveat: all
Lean figures above come from direct lean against copied oleans, not lake-verified (stale-trace caveat). No chart closure
is claimed.
