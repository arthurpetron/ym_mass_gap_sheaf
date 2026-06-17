# Constructively proving the continuum limit — synthesis & plan (2026-06-17)

Deep-research synthesis (four strands: constructive measure/limit theory; constructive
scaling-limit methods; constructive OS reconstruction + no-go scoping; internal asset
survey) on whether the Clay Yang–Mills continuum limit + mass gap can be attacked
CONSTRUCTIVELY (Bishop-style, Mathlib-free, `Q'`/`CReal`), and how to apply it to the
machinery already in this repo.

## 0. Premise

The Clay problem is worded classically, but a physically realized mass gap should carry
a constructive/computable witness (Bishop's thesis; Church–Turing–Deutsch — motivational,
not a free lemma). The whole repo already bets on this: direct Cauchy-moduli, located
gaps, functional inverse limits. The research confirms the bet is sound and locates
exactly where the genuine frontier is.

## 1. THE decisive distinction: two different limits

"The continuum limit" conflates two logically separate limits:

1. **Infinite-volume limit (Λ→∞, FIXED lattice spacing `a`).** This is **essentially
   constructive**. The convergent cluster/polymer expansion (Glimm–Jaffe–Spencer,
   Annals 1974; Brydges, Les Houches 1986; Kotecký–Preiss, CMP 1986) produces the
   infinite-volume correlators, analyticity, and exponential clustering with an
   EXPLICIT rate, as an absolutely convergent series UNIFORM IN VOLUME, via finite
   inductions — no compactness, no Prokhorov, no subsequence. Osterwalder–Seiler
   (Ann. Phys. 1978; Seiler LNP 159, 1982) do exactly this for strong-coupling lattice
   gauge theory: unique infinite-volume limit + mass gap + area law. Shen–Zhu–Zhu
   (CMP 2023) give the same gap via an explicit-rate Wasserstein contraction (a genuine
   Banach fixed point). Holds in ANY d, including 4D ON THE LATTICE. **We already build
   this for the gap in `ClusterGapReduction.lean`.**

2. **Scaling/continuum limit (`a→0`).** The genuinely OPEN frontier — for YM,
   constructive or classical. The single missing object is a **lattice-spacing-uniform
   functional inequality / two-sided modulus** for the gap to survive `a→0`. It EXISTS
   for scalar φ⁴ in d=2,3 (Bauerschmidt–Dagallier, CPAM 2024, spacing-uniform LSI) but
   **NOT for Yang–Mills in any dimension**. Stochastic-quantization / regularity-structure
   routes hit a hard wall at d<4 (YM stochastic quantization is subcritical iff d<4).

Conflating these made "the continuum gap" look uniformly open. It is not: limit (1) is
constructive and largely in hand; limit (2) is the real prize.

## 2. The constructive object: positive linear functional, never a measure

Strongly converged across strands: the right constructive primitive is a **positive
linear functional** (Daniell integral / valuation / state / expectation) on an algebra
of observables, NOT a σ-additive set function.
- Choice-free Riesz representation: positive functional ⇔ valuation (Coquand–Spitters,
  J. Logic & Analysis 2009; Spitters, Order 2010) — geometric logic, no AC.
- Constructive probability on the Daniell base, incl. weak convergence + CLT
  (Chan, *Foundations of Constructive Probability Theory*, CUP 2021; predicative
  choice-free reconstruction: Petrakis–Zeuner, LMCS 2024).
- OS axioms are stated on Schwinger functions = functional values; reflection
  positivity = GNS positivity of a state. The Hilbert space and measure are THEOREMS,
  not primitives (Segal 1947 + GNS; Osterwalder–Schrader CMP 1973/75).

Repo fit: `ObservableMeasure.ProbFunctional` IS a positive normalized functional
(`E : carrier → Q'`, `positive`, `normalized`); `restrict`/`InvLim` give the functional
Daniell–Kolmogorov inverse limit. The continuum upgrade is a CReal-valued functional
(expectations become real limits): `ContinuumFunctional.CRealProbFunctional`.

## 3. The gap as a located/clustering object (avoid the unbounded spectral theorem)

- OS reconstruction's GNS quotient+completion is constructive; the transfer-matrix
  contraction semigroup is constructive; **clustering ⟹ spectral-gap lower bound** is
  constructive. The one irreducible analytic barrier is Euclidean→Minkowski analytic
  continuation (E0′) — but Clay explicitly licenses the Euclidean route.
- Route the gap through the **COMPACT transfer operator**: Brattka–Dillhage (J.UCS 2005)
  — general bounded self-adjoint spectra are only lower-semicomputable, but COMPACT ⇒
  fully computable spectrum. This is what makes the located 2nd eigenvalue legitimate.
- Need a **TWO-SIDED** modulus (one-sided gap edge ⇒ non-computable resolvent; Specker).
- Possible **Markov's Principle** dependency for spectrum = approximative-spectrum
  (Bridges–Ishihara) — decide explicitly whether our substrate admits MP.
- Faithful constructive restatement of Clay R3: *Euclidean Schwinger functions satisfy
  OS0–OS4 and the truncated 2-point function obeys |S₂ᵀ(x)| ≤ C·e^{−m|x|} with explicit,
  volume-independent constructive rate m>0* ⟹ (OS reconstruction) Spec(H) ⊂ {0}∪[m,∞).

## 4. No-go results — scoped, and they do NOT bind a fixed-theory proof

- **Cubitt–Pérez-García–Wolf** spectral-gap undecidability (Nature 2015 / Forum Math Pi
  2022) is a UNIFORM decision problem over an adversarial FAMILY with an embedded
  universal TM (halting reduction). 4D YM is ONE fixed theory — no free parameter, no
  embedded computer. Undecidability of a family ≠ non-constructibility of an instance;
  the authors explicitly allow "specific cases."
- **Pour-El–Richards** wave-equation non-computability is a low-regularity (C⁰-not-C¹)
  artifact, restored on C¹ data, absent for elliptic/parabolic, irrelevant to a fixed
  compact spectrum. Their POSITIVE result (eigenvalues of a computable s.a. operator are
  computable) FAVORS the fixed-gap route.
- Genuinely binding (must respect): stay on the compact transfer operator (not the
  unbounded generator); the analytic-continuation step stays hard analysis; never a bare
  monotone/Cauchy limit without a supplied modulus (Specker); valuation→Borel extension
  on general sober spaces is open (so stay functional/localic).

## 5. Constructive landmines (where standard treatments smuggle in AC/EM/compactness)

- Prokhorov tightness ⇒ convergent subsequence (the central one; effective converse
  provably fails). Replace with a direct modulus.
- Carathéodory/Kolmogorov σ-additive extension (non-located suprema + non-constructive
  σ-additivity). Use Daniell/valuation.
- Bare monotone/martingale convergence (Specker). Always carry a modulus.
- General constructive Kolmogorov extension with a modulus is OPEN in the literature
  (Goubault-Larrecq 2018 is the closest blueprint, constructivity unverified) — so our
  `InvLim` functional layer is AT the research edge.

## 6. Application plan against repo assets

Already constructive and reusable: `ProbFunctional` + `restrict` + `InvLim` +
`pushforward_limit_eq` (functional Daniell–Kolmogorov); `crealOfTail` /
`crealOfGeoIncrement` (direct-modulus Q'-sequence → CReal); `ofQ'_le_of_approx_ge` +
`IsPositive` (finite→limit positivity); `ClusterGapReduction` (single honest cluster
bound ⇒ proved infinite-volume gap).

Builds (in progress / planned):
- **(A) `ContinuumFunctional.lean`** — `CRealProbFunctional` (CReal-valued positive
  normalized functional) + `continuumFunctional_of_modulus` (consistent lattice family
  + per-observable two-sided modulus ⇒ continuum functional, positivity/normalization
  PROVED via `ofQ'_le_of_approx_ge`), a concrete inhabitant on `RGTransport` char data
  (expectations are exactly stable ⇒ trivially modulus-Cauchy), gap-as-clustering
  packaging, and the a→0 step as ONE honest named interface. Realizes "continuum theory
  = positive functional by direct modulus, no compactness."
- **(B) `CRealComplete.lean`** — the reusable completeness backbone: `CReal.le`
  transitivity ([M7.3-trans]); general modulus-Cauchy `CReal` sequence ⇒ limit +
  `ConvergesTo` (generalizing `crealOfGeoIncrement` beyond geometric); bound-passing to
  the limit; minimal `CReal.add/sub` if required. The mandatory modulus-carrying spine.
- **(C, future) The honest `a→0` interface**, `SpacingUniformGapModulus` — the single
  lattice-spacing-uniform two-sided modulus that, IF supplied, gives the continuum gap
  constructively from the infinite-volume one. This is the genuine open frontier for YM;
  it is provable for scalar φ⁴ d=2,3 (Bauerschmidt–Dagallier) — a possible lower-d
  proof-of-concept that the full constructive pipeline closes end-to-end.

## 7. Honest bottom line

We CAN constructively build: the infinite-volume (Λ→∞, fixed-spacing) functional limit
and gap; the functional primitive and its positivity-passing; the located gap as a
clustering rate via the compact transfer operator; and the scaffolding so the scaling
limit reduces to ONE named two-sided spacing-uniform modulus. We CANNOT (and will not
fake) the a→0 YM modulus itself — it is open research mathematics for YM in every
dimension. The no-go theorems do not forbid a fixed-theory constructive proof; the
missing piece is a genuine estimate, not a logical obstruction.

Sources (refereed unless flagged): Bishop–Cheng (AMS 1972), Bishop–Bridges (Springer
1985), Coquand–Spitters (JLA 2009; J.UCS 2005), Spitters (Order 2010), Vickers (MLQ
2008), Chan (CUP 2021), Petrakis–Zeuner (LMCS 2024), Daniell (Ann. Math. 1918);
Glimm–Jaffe–Spencer (Annals 1974), Brydges (Les Houches 1986), Kotecký–Preiss (CMP 1986),
Fernández–Procacci (CMP 2007), Osterwalder–Seiler (Ann. Phys. 1978; Seiler LNP 159 1982),
Guerra–Rosen–Simon (Annals 1975), Feldman–Osterwalder (Ann. Phys. 1976), Shen–Zhu–Zhu
(CMP 2023), Bauerschmidt–Dagallier (CPAM 2024), Bauerschmidt–Brydges–Slade (LNM 2242);
Osterwalder–Schrader (CMP 1973/75), Glimm–Jaffe (Springer 1987), Brattka–Dillhage (J.UCS
2005), Pour-El–Richards (Springer 1989), Cubitt–Pérez-García–Wolf (Nature 2015 / Forum
Math Pi 2022), Rojas (Arch. Math. Logic 2023), McNicholl–Rojas (Inf.&Comp. 2022).
Flagged unrefereed: Goubault-Larrecq (arXiv:1803.05259), OSforGFF (arXiv:2603.15770),
SU(3)-YM (arXiv:2506.00284), Vickers valuation-monad ms. (2011).
</content>
