# Two-route attack on the continuum SU(2) Yang–Mills mass gap (2026-06-18)

Consolidated attack plan synthesising two deep-research strands (heat-kernel decimation;
Polchinski-flow LSI) on the single open inequality `RGGapPersistence`. The encouraging
finding: both routes converge on ONE atomic object — a per-block contraction multiplier
anchored at the exact SU(2) Casimir gap `3/4` — and the early rungs are genuinely buildable
now, with the single hard residual sharply localised.

## The reduction already proved (Lean, axiom-clean)

  Clay 4D gap (all simple groups)
    ⟸ worst-case reduction to SU(2)            [MassGap/SimpleGroup — DONE]
    ⟸ SU(2) continuum gap (RegScalingBand survival, physGapMin>0)
    ⟸ RGGapPersistence                          [RGGapPersistence.lean — DONE]
        (per-block: rho_k with ∏ rho_k ≥ c > 0, RGBlockPersistence.toUniform;
         uniform: c ≤ m_lat(a_j)/a_j; anchor at strong coupling PROVED;
         bridge ⇒ physGapMin>0 pure assembly over divPos.)

Everything except `RGGapPersistence` is proved. The open content is exactly the per-block
gap multiplier staying bounded below along the a→0 (block-spin) flow.

## The unifying anchor: SU(2) ≅ S³, exact Casimir gap 3/4

SU(2) is rank 1; the transfer operator diagonalises in the spin-`j` character basis with
Casimir `j(j+1)`. The slowest nontrivial mode `j=½` has Casimir `3/4` — *the project's own
`c_λ = 3/4`*. BOTH routes are anchored here, which is why they meet.

## Route A — heat-kernel decimation (explicit closed-form gap)

- Heat-kernel (Villain/Manton) action: SU(2) eigenvalue weights are pure Gaussians
  `c_j ∝ (2j+1)·w^{j(j+1)}`. Our `RGTransport.charFunc` already encodes this
  (`E χ_s = dimQ(s)·w^{C₄(s)}`, `C₄(s)=s(s+2)`). The gap separator is the closed form
  **`sep_HK(w) = w^{C₄(1)} = w³`** (excited `s=1` over vacuum `s=0`), manifestly monotone,
  `< 1` for `w<1`. [Lean: HeatKernelGap.lean — sub-results #1/#2, in progress.]
- The heat-kernel action is an EXACT RG fixed point in 2D (Menotti–Onofri NPB190 (1981);
  semigroup/area-additivity) and a NEAR-fixed-point in d>2.
- Combined with two-loop asymptotic freedom `β(a)` (Lüscher–Weisz PLB349 (1995)), the entire
  continuum gap collapses to ONE one-variable inequality:
      **−log sep_HK(β(a)) ≥ c · a·Λ_L**, i.e. liminf_{a→0} (1/a)(−log sep) ≥ c·Λ_L > 0.
- Supporting inequalities are REFEREED and Lean-formalisable: Amos two-sided Bessel bounds
  (Hornik–Grün JMAA 408 (2013)); theta-quotient convexity/monotonicity (Dixit–Roy–Zaharescu,
  JMAA); Turán/log-concavity `I_n² > I_{n−1}I_{n+1}` (Baricz). Matches our
  `ThetaConv`/`RealTheta`/`SigmaHatLimit` machinery.
- Ranked sub-results: (1) `sep_HK=w³` [building]; (2) monotonicity in `w` [trivial];
  (3) one-sided strong-coupling bound `sep ≤ 1−c·…`; (4) per-block `ρ_k` from `sep`;
  (5) the transmutation comparison [the heart — frontier, reduced to one variable].

## Route B — Polchinski-flow LSI (spacing-uniform functional inequality)

- The renormalization-flow LSI method (Bauerschmidt–Bodineau–Dagallier, Prob. Surveys 21
  (2024); Bauerschmidt–Dagallier φ⁴, CPAM 77 (2024)) integrates the LSI constant
  SCALE-BY-SCALE via the multiscale Bakry–Émery criterion
  `1/γ ≤ ∫₀^∞ exp(−2∫₀ᵗ λ̇_s ds) dt`. Curvature need only be positive ON AVERAGE over
  scales — exactly what defeats the spacing-dependence that kills naive Bakry–Émery. The
  φ⁴ spacing-uniformity mechanism: bounded susceptibility ⇒ finite integral ⇒ uniform LSI.
- Obstruction (localised): the method's enabling input is a positive finite-range
  COVARIANCE decomposition (Brydges–Guadagni–Mitter; Bauerschmidt PTRF 157 (2013)) — a
  theorem about Gaussian/quadratic forms. The SU(2) Haar/heat-kernel link measure is
  non-Gaussian (no covariance to decompose). FIX: replace covariance decomposition with the
  GROUP HEAT-FLOW scale decomposition on S³ (heat semigroup contracts mode `j` by
  `e^{−t·j(j+1)}` — exact, computable).
- Dynamic⇒static: Helffer–Sjöstrand (JSP 74 (1994)) converts a dynamic Poincaré/LSI gap to
  static correlation decay (a positive mass). Shen–Zhu–Zhu (CMP 400 (2023)) already run this
  full chain on the non-abelian lattice — uniform in volume, strong coupling, FIXED spacing
  (the only missing piece is spacing-uniformity).
- Ranked sub-results: (1) single-link/single-scale LSI contraction on S³ from the exact
  `3/4` gap (`PerScaleContraction`); (2) Helffer–Sjöstrand `λ>0 ⇒ m>0` (`DynamicToStaticGap`);
  (3) multi-link composition ⇒ per-block multiplier `ρ`; (4) [hardest] non-abelian
  susceptibility / correlation-inequality replacement (field-independence of Hess V_t).

## The convergence (why this is one attack, not two)

Both routes terminate at the SAME object: a per-block contraction multiplier `ρ`
governed by the exact `3/4` Casimir gap, feeding
`RGBlockPersistence.toUniform ⇒ RGGapPersistence ⇒ physGapMin>0`. Route A computes `ρ` from
the explicit `sep=w³`; Route B derives `ρ` from the per-scale LSI contraction. They are two
windows on `∏_k ρ_k ≥ c`.

## The one hard residual (same obstruction, two views) — sharply localised

- Route A: the 4D near-fixed-point DEVIATION of the heat-kernel action is not rigorously
  bounded (Migdal–Kadanoff is exact only on hierarchical lattices; Nauenberg–Toussaint
  NPB190 (1981)). The Balaban-style multiscale frontier.
- Route B: the non-abelian SUSCEPTIBILITY / correlation-inequality step that removes
  field-dependence from Hess V_t has no clean analogue (Nissim: plain Bakry–Émery fails for
  U(N) — non-uniform Ricci — motivating exactly the multiscale criterion).
These are the same crossover obstruction (strong-coupling↔continuum) seen two ways. It is
now ONE localised analytic gap, not a diffuse "continuum limit."

## Buildable NOW vs frontier

PROVABLE NOW (early rungs):
  - `sep_HK = w³`, monotonicity, the located gap `gapMargin = 1−w³ > 0` [Route A #1/#2 — building].
  - per-block `ρ_k` from explicit `sep` ⇒ instantiate `RGBlockPersistence` so the open
    content is the explicit product inequality `∏_k ρ_k ≥ c` in terms of `w(a_k)`.
  - single-link S³ Bakry–Émery contraction at gap `3/4` (`PerScaleContraction`) [Route B #1].
  - `DynamicToStaticGap` (`λ>0 ⇒ m>0`) as a named CReal lemma [Route B #2].
FRONTIER (the one hard residual): Route A #5 (transmutation comparison, one-variable but
needs the deviation bound) / Route B #4 (non-abelian susceptibility). Genuinely open.

## Lean obligation map
  - `heatKernelSep`/`heatKernelLocatedGap` (Route A #1/#2) — HeatKernelGap.lean [building].
  - `RGBlockPersistence` instance from `heatKernelSep` ⇒ explicit `∏ρ_k≥c` [next build].
  - `PerScaleContraction` (Route B #1): field `λ̇_t` + `∫ exp(−2∫λ̇) < ∞` from the 3/4 gap.
  - `DynamicToStaticGap` (Route B #2): `(poincaré λ) → (massGap m)`, `m` a CReal atom.
  - All feed the existing `RGGapPersistence ⇒ physGapMin>0` reduction.

## Honest verdict
This does NOT solve the Clay problem. It (i) reduces it — in Lean, axiom-clean — to ONE
named inequality; (ii) makes the SU(2) gap an EXPLICIT closed form (`w³`); (iii) localises
the single hard residual to one crossover estimate seen identically by two independent
methods; and (iv) makes the early rungs genuinely buildable with refereed supporting tools.
The frontier residual (the 4D near-fixed-point deviation / non-abelian susceptibility) is
the real open mathematics — but it is now ONE sharply-stated one-variable-flavoured
obstruction, anchored at the exact `3/4` Casimir gap, not a diffuse continuum-limit problem.

Sources (refereed unless flagged): Menotti–Onofri NPB190(1981); Osterwalder–Seiler
Ann.Phys.110(1978); Lüscher–Weisz PLB349(1995); Bauerschmidt–Bodineau–Dagallier
Prob.Surveys 21(2024, arXiv:2307.07619); Bauerschmidt–Dagallier CPAM 77(2024,
arXiv:2202.02295); Shen–Zhu–Zhu CMP 400(2023, arXiv:2204.12737); Brydges–Guadagni–Mitter
JSP 115(2004); Bauerschmidt PTRF 157(2013); Helffer–Sjöstrand JSP 74(1994); Hornik–Grün
JMAA 408(2013); Dixit–Roy–Zaharescu (JMAA); Baricz (Expo. Math.); Nauenberg–Toussaint
NPB190(1981); Eldredge–Gordina–Saloff-Coste (arXiv:1708.03021). Flagged/discarded:
arXiv:2506.00284 (withdrawn), ai.vixra 2602.0041, Tomboulis arXiv:0707.2179 (disputed).
</content>
