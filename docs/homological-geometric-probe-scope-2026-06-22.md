# Scope: the homological probe (+ manifold-theory ideas), honestly (2026-06-22)
**STATUS:** Scope/plan dated 2026-06-22; see the canonical ledgers for the outcome (docs/where-the-wall-sits-2026-06-22.md, docs/stage1-completion-ledger-2026-06-22.md, docs/stage2-progress-ledger-2026-06-22.md, docs/continuum-wall-outstanding-2026-06-22.md).

Probe question: can the YM mass gap be expressed as, or bounded below by, a TOPOLOGICAL / HOMOLOGICAL /
GEOMETRIC invariant — making the gap MAGNITUDE (or its persistence under the RG flow) a STRUCTURAL fact
rather than a purely analytic estimate? Literature-grounded (deep-research pass). Blunt verdict first.

## Headline verdict

- **"YM gap as a manifestly-lower-bounded HOMOLOGICAL/TOPOLOGICAL invariant" is a CATEGORY ERROR for
  magnitude.** Topological invariants are integers / homotopy classes; they certify EXISTENCE (index
  theory: zero modes) or STABILITY (K-theory protection: a gap can't close while a class is constant),
  but NEVER the SIZE of a gap. No credible prior art expresses a QFT mass gap as a topological invariant;
  the Clay/OS statement is analytic by construction.
- **"YM gap as a GEOMETRIC (curvature) lower bound" is LEGITIMATE and is the real frontier.**
  Lichnerowicz–Obata / Bakry–Émery genuinely turn a curvature constant into a gap MAGNITUDE, and there is
  a LIVE rigorous lattice-YM program doing exactly this at strong coupling.
- **All routes RESHAPE the analytic content; none removes it.** The most useful reshaping (Route 2)
  converts our Stage-2 wall "Δ/√σ bounded below as a→0" into "the Bakry–Émery / log-Sobolev curvature
  constant of the interacting heat-kernel measure on SU(N)^edges stays bounded below uniformly as a→0" —
  still an open analytic estimate, but tensorizing, dynamically interpretable, routed onto SU(2)=S³, and
  backed by an active toolkit.

So: the user's homology instinct is a category error for MAGNITUDE, but the adjacent MANIFOLD/curvature
instinct is correct and is the single most promising reframing of the continuum wall.

## Route 1 — topological protection / index theory / persistent homology

- **Index theory (Atiyah–Singer, Lichnerowicz vanishing).** The index is an integer; it bounds the
  EXISTENCE/dimension of the kernel (zero modes), never the lowest nonzero eigenvalue. Lichnerowicz
  (D² = ∇*∇ + Scal/4) gives "0 excluded" topologically; the MAGNITUDE version (D² ≥ s₀/4 when Scal ≥ s₀)
  is the GEOMETRIC reading of the same Weitzenböck identity — a curvature estimate, i.e. Route 2, not a
  topological theorem.
- **K-theory topological protection (Kitaev table, bulk–edge).** STABILITY only, and it PRESUPPOSES a
  gap (the invariant is the Fredholm index of the Fermi projection, defined only when the gap exists). It
  certifies "can't close without the invariant jumping" — never produces a gap or its size.
- **Persistent homology.** No rigorous link from a persistence interval to a LOWER bound on a physical
  operator's gap; known inequalities run the wrong way (a known gap shortens persistence). PH on
  lattice-gauge data is a heuristic PHASE detector, not a gap bound.
- Verdict: category error for magnitude (~1–2% of supplying gap content). Possible value: an AFTER-THE-FACT
  stability statement (once a gap is proved analytically, a K-theoretic class could record its robustness).
  Citations: Bochner technique (Bérard, BAMS); Kitaev arXiv:0901.2686; bulk-gap stability Nachtergaele–
  Sims–Young arXiv:2102.07209.

## Route 2 — geometric / manifold: curvature ⇒ gap (THE route)

- **The mechanism is a real theorem.** Lichnerowicz–Obata: Ric ≥ (n−1)K ⇒ λ₁ ≥ nK (sharp). Bakry–Émery
  CD(K,∞): Γ₂ ≥ K·Γ ⇒ Poincaré (gap ≥ K) AND log-Sobolev with constant K. Curvature → gap MAGNITUDE.
- **Live rigorous lattice-YM program.** Shen–Zhu–Zhu, *A stochastic analysis approach to lattice Yang–Mills
  at strong coupling* (arXiv:2204.12737, CMP 2023): log-Sobolev + Poincaré + strictly positive mass gap,
  UNIFORM IN VOLUME, for SU(N)/SO(N), via Bakry–Émery on the Langevin dynamics — at STRONG coupling
  (smallness |β| < c(N,d)), FIXED spacing. Follow-ups: Cao–Nissim–Sheffield arXiv:2509.04688 (area law),
  YM–Higgs arXiv:2401.13299. Method toolkit: Bauerschmidt–Bodineau–Dagallier multiscale Bakry–Émery /
  Polchinski-equation (φ⁴/sine-Gordon/Ising — NO gauge paper yet, but the portable machinery).
- **The manifold facts (our home turf).** A compact simple Lie group with bi-invariant metric has positive
  CONSTANT Ricci (SU(2) = S³, Ric ≈ ¼g); a PRODUCT SU(N)^edges inherits the same K by tensorization. So
  the FREE (Haar) part is manifestly curved-positive; the gap obstruction is entirely the interacting
  Wilson term's Hessian in Γ₂.
- **The continuum landmine.** Uniform-in-a positivity FAILS as written at weak coupling: the physical gap
  scales m ~ e^{−C/g²} (non-perturbatively small), exactly where curvature positivity is not manifest. So
  Route 2 RESHAPES "Δ/√σ bounded below as a→0" into "Γ₂ ≥ K > 0 (or the LSI constant) uniformly as a→0" —
  a CURVATURE wall, still open, as hard as the original, but better-structured.
- Verdict: the least-low-prior route. ~>90% it can re-derive the strong-coupling/fixed-spacing gap as a
  magnitude (already known classically via Osterwalder–Seiler); the uniform-in-a continuum step is exactly
  as hard as the original problem and unsolved by anyone.
- DO NOT cite vixra:2602.0041 (a non-peer-reviewed, conditional, AI-assisted "uniform LSI weak-coupling"
  preprint that explicitly does not prove its claim). It is a landmine, not a result.

## Route 3 — Morse theory / configuration-space topology (the manifold-topology ideas)

- **Atiyah–Bott** (YM over Riemann surfaces, 1983): Morse theory of the YM functional computes the
  equivariant cohomology of moduli of bundles — classical, 2D only, no Hamiltonian spectrum.
- **Center symmetry ℤ_N / center vortices / 't Hooft & Polyakov loops:** genuine ORDER PARAMETERS for the
  confinement–deconfinement PHASE — they detect which phase, not the gap size; no spectral lower bound.
- **Instantons π₃(G)=ℤ:** label tunneling/θ-sectors; do not gap the spectrum around the trivial vacuum.
- **The decisive examples:** Polyakov 3D compact QED (m ~ coupling·e^{−S/2}) and Karabali–Nair 2+1D
  (m = e²·c_A/2π, hep-th/9610002) — config-space topology SELECTS the mechanism/sector, but the MAGNITUDE
  is set by the COUPLING. Singer's positive sectional curvature of 𝒜/𝒢 is itself a Route-2 (curvature)
  observation, not a topological invariant.
- Verdict: category error for magnitude (~2–3%); the quantization step is irreducibly where the gap size
  lives. Useful only as existence-heuristic and as the source of Singer's curvature observation (→ Route 2).

## The genuinely actionable deliverable (if we pursue the probe)

Pursue Route 2 as a FRAMING, not a shortcut. The concrete, honest, bounded formalization deliverables:

1. **A constructive discrete Bakry–Émery template** (`Γ₂ ≥ K·Γ ⇒ Poincaré spectral gap ≥ K`) for a finite
   Markov generator / the SU(N)-product heat-kernel measure. The discrete Γ-calculus (Γ(f) = ½(L(f²)−2fLf),
   Γ₂ = ½(LΓ(f) − 2Γ(f,Lf))) is PURE ALGEBRA on a finite state space — formalizable constructively, no
   integration. This yields a reusable "curvature ⇒ gap" bridge: the GEOMETRIC analog of how
   `UniformClusterBound` is the cluster analog. It converts the gap-MAGNITUDE problem into a
   curvature-MAGNITUDE problem.
2. **Reframe the Stage-2 wall** (`UniformRatioVariation` / `LambdaPositiveLimit`) as a UNIFORM-in-a
   Bakry–Émery / log-Sobolev constant on the interacting heat-kernel measure — a named `UniformCurvatureBound`
   input, with the strong-coupling positivity (SZZ) as the proved/known anchor and the weak-coupling
   uniformity as the precisely-named open content. Anchor the free part on SU(2)=S³ positive Ricci.
3. Honest framing in-doc: this is a RESHAPING (analytic → curvature), not a closure. The discrete template
   (1) is genuinely formalizable; the strong-coupling curvature positivity (SZZ) is known/formalizable-hard;
   the uniform-in-a curvature bound is the reshaped open wall (still the unsolved continuum problem, now in
   curvature language, with the SZZ + Bauerschmidt–Bodineau–Dagallier toolkit attached).

## Honest odds / recommendation

- The pure-homology (Routes 1, 3) hope of a manifestly-lower-bounded TOPOLOGICAL invariant for the gap
  magnitude is a CATEGORY ERROR — recommend NOT pursuing it for magnitude (only as after-the-fact stability /
  existence heuristics).
- The MANIFOLD/curvature route (Route 2) is the realistic frontier and the right reframing of our Stage-2
  wall. Its honest status: solves strong-coupling/fixed-spacing as a MAGNITUDE; the continuum step is as
  hard as ever. The reshaping is valuable because it routes onto controlled objects (SU(N) products, S³
  curvature) and an active research toolkit.
- RECOMMENDED next concrete step: build deliverable (1), the constructive discrete Bakry–Émery `Γ₂ ⇒ gap`
  template, + the `UniformCurvatureBound` reframing (2). That is a genuine, axiom-clean, reusable bridge
  (a NEW geometric reduction of the gap), and it correctly classifies the continuum content as a uniform
  curvature wall. It does NOT close the continuum limit — nothing honestly does.
