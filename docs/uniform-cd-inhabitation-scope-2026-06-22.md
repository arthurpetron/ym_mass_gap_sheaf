# Scope: inhabiting `uniform_CD` via the SZZ / BBD toolkit (2026-06-22)

`UniformCurvatureBound.uniform_CD` = a single K>0 with Bakry–Émery `CD(K,∞)` for the SU(N) lattice YM
Langevin generator, uniform over the family. Can the Shen–Zhu–Zhu (SZZ) and Bauerschmidt–Bodineau–Dagallier
(BBD) toolkits inhabit it? Research-grounded, blunt verdict first.

## Headline verdict

- **At FIXED spacing (index = volume): YES, via SZZ — but it is a SECOND PROOF of the already-known
  fixed-spacing gap** (the Osterwalder–Seiler strong-coupling gap in Bakry–Émery clothing). Formalizable-hard;
  reuses our free-curvature anchor. Modest: it does not advance the Clay frontier.
- **In the CONTINUUM (index = spacing, a→0): NO — OPEN research, and not merely "hard."** There is a sharp
  STRUCTURAL reason curvature cannot reach it (functional-form mismatch, below), BBD has no gauge instance
  and needs integration-over-scales our substrate lacks, and the weak-coupling regime is the same wall.
  Formalizing continuum `uniform_CD` today = encoding an open conjecture (a "no" per the project ethos).

## SZZ — what it precisely gives (fixed spacing)

Shen–Zhu–Zhu, *A stochastic analysis approach to lattice YM at strong coupling* (arXiv:2204.12737, CMP 2023):
- PROVES: an LSI (Thm 1.4) ⇒ Poincaré ⇒ strictly positive mass gap (Cor 1.6) for SU(N) lattice YM,
  **uniform in volume and in N**, at **strong coupling** `|β| < 1/(16(d−1))`, **fixed spacing** (Remark 1.7,
  explicit). Continuum a→0 stated OPEN (Sec 1.3).
- MECHANISM (exactly our Γ₂ structure): `K_S = (N+2)/2 − 1 − 8N|β|(d−1) > 0` = [bi-invariant SU(N) Ricci
  `(N+2)/2`] − [Wilson-plaquette Hessian `8N|β|(d−1)`]. Positivity needs β small so the GROUP CURVATURE
  dominates the interaction Hessian. Key technical point: the interaction Hessian is `O(|β|N)`, not `O(N²)`.
- Follow-ups (Cao–Nissim–Sheffield 2509.04688; Nissim 2510.22788) all fixed-spacing, strong/'t Hooft
  coupling; notably Bakry–Émery FAILS for U(N) (Ricci not uniformly positive) — the mechanism is already fragile.

This is the LSI restatement of Osterwalder–Seiler (1978). It genuinely inhabits a FIXED-SPACING
`UniformCurvatureBound` with explicit constants, but yields the gap we already have (cluster route).

## BBD — the continuum tool, and why it does not apply here

Bauerschmidt–Bodineau / Bauerschmidt–Dagallier Polchinski-flow LSI (1907.12308; 2202.02295 CPAM 2024):
- STRUCTURE: continuous RG covariance decomposition `C = ∫₀^∞ Ċ_t dt`, the Polchinski equation for the
  renormalized potential, a per-scale multiscale Bakry–Émery curvature input, and a global constant
  `1/γ ≤ ∫₀^∞ exp(−2∫₀^t ℓ̇_s ds) dt`.
- ACHIEVES a CONTINUUM / cutoff-uniform LSI for φ⁴₂, φ⁴₃, sine-Gordon, near-critical Ising — but ONLY in the
  bounded-susceptibility (subcritical) phase, NEVER across criticality.
- Three blockers for us: (1) NO gauge-theory instance exists (the survey 2307.07619 has zero "Yang–Mills").
  (2) The method is fundamentally an INTEGRATION-OVER-SCALES (`∫₀^∞ dt`) construction — incompatible with our
  no-CReal-integration substrate (even the abstract template needs the scale integral). (3) The per-scale
  input needs bounded susceptibility; the asymptotically-free weak-coupling regime is precisely the
  near-critical `ξ→∞` regime where that margin degenerates — the same wall.

## The deep structural obstruction (why curvature is the WRONG FORM for the continuum)

Dimensional transmutation: the lattice gap in lattice units is `m·a ~ (b₀g²)^{−b₁/2b₀²}·exp(−1/(2b₀g²))`,
`b₀ = 11N/(48π²)` — an ESSENTIAL SINGULARITY at `g=0`. A Bakry–Émery / convexity constant `K(g²)` is
ANALYTIC at the Gaussian point (a power series `K₀ + K₁g² + …`), so a curvature-derived gap `λ₁ ≥ K` is
necessarily POLYNOMIAL in `g²`. That is the wrong functional form to track `exp(−c/g²)`. SZZ's `K_S` goes
NEGATIVE the moment `β` exceeds `1/(16(d−1))` — i.e. immediately on the weak-coupling side. So the geometric
route, like the cluster and ratio routes, RESHAPES the continuum content but cannot CLOSE it — and here we
have a sharp reason it is not merely unproven but functional-form-incompatible: **curvature positivity is
analytic in the coupling; the continuum gap is non-perturbative.** (The only continuum BE–gauge statement,
Mondal JHEP 2023 / arXiv:2301.06996, ASSUMES the regularized BE-Ricci positivity it would need — i.e. assumes
exactly the open thing.)

## The one concrete formalizable sub-obligation (fixed spacing only)

The SZZ strong-coupling Γ₂ Hessian bound: for SU(N), `Ricci_{SU(N)} − Hess(S_Wilson) ≥ K_S =
(N+2)/2 − 1 − 8N|β|(d−1) > 0` under `|β| < 1/(16(d−1))`, giving `CD(K_S)`. Caveats for OUR substrate:
- SZZ's generator is a CONTINUOUS Langevin diffusion on the Lie group SU(N)^edges; our `BakryEmery` template
  is for FINITE discrete Markov generators. Formalizing SZZ requires a CHARACTER/FINITE SURROGATE of the
  diffusion generator (truncate to characters s<n; the Wilson interaction couples them by fusion), and proving
  the truncated generator's `Γ₂ ≥ K_S`. The diagonal/free part reuses our proved anchor `free_DiagCD`
  (CD(3/4) for SU(2)); the off-diagonal Wilson-Hessian smallness is the genuine new estimate.
- This is a real formalization PROJECT (formalizable-hard), not a quick wave, and it inhabits `uniform_CD`
  ONLY at fixed spacing — a geometric SECOND proof of the known fixed-spacing gap, making
  `UniformCurvatureBound` non-vacuously inhabited.

## Verdict and recommendation

- **Fixed-spacing SZZ inhabitation: formalizable-hard, modest, reuses our anchor.** Worth it ONLY to make the
  geometric route non-vacuous (a real second proof of the fixed-spacing gap). It does not advance the frontier
  and overlaps the cluster-route fixed-spacing content.
- **Continuum `uniform_CD`: OPEN research, and structurally wrong-form for curvature.** SZZ's margin is
  negative on the weak-coupling side; BBD has no gauge instance and needs scale-integration we lack; the
  exp(−c/g²) gap cannot be produced by an analytic-in-g² curvature constant. Formalizing it = encoding an open
  conjecture — do NOT.
- **Recommendation:** if pursuing, build only the fixed-spacing SZZ Γ₂ surrogate (the character-truncated
  generator with `Γ₂ ≥ K_S`, reusing `free_DiagCD`), as a non-vacuous geometric inhabitant of a fixed-spacing
  `UniformCurvatureBound`. Record the functional-form obstruction as the definitive reason the curvature route
  reshapes-but-cannot-close the continuum. The continuum gap remains the open Clay content in all three
  languages (cluster / ratio / curvature); curvature is now known to be the wrong functional form to close it
  by convexity alone.
