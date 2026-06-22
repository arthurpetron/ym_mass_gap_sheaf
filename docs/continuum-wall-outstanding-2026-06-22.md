# What is still outstanding to close the continuum wall (2026-06-22)

After the structural-attack wave (scale-sheaf Λ-cohomology, Spin(4)=SU(2)², dimensionless ratio,
ℤ₂ reflection margin proved, D₄/24-cell rotation reduction), this is the honest accounting of what
remains. None of the structural work CLOSED a continuum limit; it sharpened and routed the named walls.

## The target

Construct continuum 4D YM satisfying the OS axioms (R1), nontrivial (R2), with a mass gap (R3), for all
compact simple groups (worst case SU(2), already reduced in Lean). The wall = the two limits beyond the
fixed-spacing finite-volume theory.

## Stage 1 — Λ→∞ (thermodynamic limit, FIXED spacing). KNOWN math; the wall is FORMALIZATION.

Status: reduced to ONE input, bridge PROVED (`ClusterGapReduction`: UniformClusterBound ⇒ positive
continuum-rate mass). Outstanding:
- **1a. Genuinely inhabit `UniformClusterBound`** = the volume-uniform strong-coupling cluster expansion
  for real SU(2) heat-kernel activities (Λ-independent gap floor + geometric connected-correlator tail).
  KNOWN mathematics (Osterwalder–Seiler 1978; Seiler LNP 159; Shen–Zhu–Zhu) with volume-independent
  constants; UNFORMALIZED. Large but no new math.
- **1b. The real lattice measure (R1 real-object, fixed spacing).** H1 finite-volume character-sum
  functional (TRACTABLE — character orthogonality makes Haar discrete, no integration) + H2.1 Kolmogorov
  consistency + H2.2 polymer-expansion identity (abstract↔real) + H2.3 corr↔Wilson correlator. H1+H2.1
  tractable; H2.2/H2.3 hard-but-known.

Verdict: Stage 1 is KNOWN mathematics; closing it is sustained formalization labor. Payoff: a rigorous
constructive INFINITE-VOLUME mass gap at FIXED lattice spacing — a real result, but NOT the continuum.

## Stage 2 — a→0 (continuum limit). GENUINELY OPEN mathematics. The real Clay content.

- **2a. Existence of the continuum limit (THE core).** Correlation functions converge as a→0 with
  g(a)→0 per asymptotic freedom, to nontrivial OS-satisfying limits. This is the multiscale/RG problem.
  Bałaban controlled the partition function (classical, ~hundreds of pages); the GAP's survival to the
  continuum is OPEN. No constructive/located version exists.
- **2b. Gap survives with positive physical value** = `DimensionlessRatio.ratioConverges` (Δ/√σ → a
  positive limit) = the uniform-in-a lower bound on the dimensionless gap. R3-in-continuum. OPEN.
- **2c. Nontriviality (R2).** The limit is interacting, not Gaussian. Believed to follow from AF (unlike
  trivial φ⁴₄/QED); OPEN, tied to 2a.
- **2d. O(4) restoration.** REDUCED: connected rotation→SU(2) PROVED; reflection ℤ₂ PROVED; rotation-
  breaking pushed to degree-≥6 (D₄/24-cell) PROVED. Remaining = RG-irrelevance of the degree-≥6 operator
  (`rotationRestored.irrelevant`), which is part of 2a's machinery.
- **2e. Dimensional transmutation.** Λ as RG-invariant FRAMED (scale-sheaf cohomology class); `BetaNonzero`
  (β≠0) is the easy named input AF supplies.

Verdict: Stage 2 is GENUINELY OPEN. The single irreducible core is **2a**; 2b, 2c, 2d all follow from or
live inside it. 2e is essentially done modulo the easy BetaNonzero.

## The irreducible core (2a), precisely

A **uniform-in-spacing renormalization-group control of the YM measure across the scaling window** (strong
coupling at large a → weak coupling at small a, harnessing asymptotic freedom) that keeps the dimensionless
gap Δ/√σ bounded below and convergent. This is the unsolved Bałaban-completion for the gap. Proving it
delivers 2a→2d at once (gap survival, nontriviality, the rotation-breaking irrelevance).

### Our specific extra obstruction (constructive)

NO CReal integration exists in the substrate. The a→0 limit is genuinely analytic (a limit of
functionals/measures). The discrete trick that makes the FIXED-spacing theory constructive (character
orthogonality ⇒ finite character sums) does NOT obviously survive the continuum limit. Whether 2a can be
done with LOCATED/computable moduli all the way is itself an open question — a constructive proof would
need genuinely new RG mathematics, OR a computer-assisted / verified-numerics route supplying the constants
(the "measurement bridge": rigorous interval-arithmetic lattice data + a uniform analytic a→0 modulus).

## What the structural wave actually bought

It closed NO continuum limit. It converted diffuse "continuum is open" into precisely-named, quantitative,
partly-controlled walls, and routed parts onto objects we control:
- O(4) → group theory PROVED, only a degree-≥6 irrelevance named.
- gap → framed as the MEASURED dimensionless ratio Δ/√σ.
- Λ → framed as a cohomology class; β≠0 the only (easy) named input.
The genuine open core (2a) is untouched — but the ground is maximally prepared (the exact inputs 2a must
deliver are now named theorems-to-be).

## Reachability

- **Stage 1** (formalize known thermodynamic-limit + real-measure math): reachable with sustained effort;
  yields a genuine constructive infinite-volume LATTICE gap. The highest-value DELIBERATE next target for a
  complete rigorous (if non-continuum) result.
- **Stage 2 core (2a)**: genuinely open research mathematics; NOT reachable by formalization alone; needs
  new constructive RG math or a computer-assisted route. The real Clay-hard part. Our work named the exact
  inputs; the analytic theorem is unwritten anywhere.

## Bottom line

Closing the continuum wall = Stage 1 (KNOWN math, formalization labor — gives the fixed-spacing infinite-
volume gap) + Stage 2 core 2a (OPEN research math — the uniform-in-a RG/gap control, harnessing asymptotic
freedom, with the added constructive question of located moduli without integration). The structural wave
sharpened Stage 2's named inputs and routed O(4)/gap/Λ onto controlled objects, but 2a — the genuine
continuum content — remains, and is where any real closure must happen.
