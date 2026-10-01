# Math-ph listing refresh: constructive Yang--Mills relevance

## Scan record

- Listing scanned: [arXiv math-ph new](https://arxiv.org/list/math-ph/new), which reported **Wednesday, 30 September 2026**; 81 entries total (13 new submissions, 45 cross-lists, 23 replacements).
- Completed scan: **2026-09-30 03:38 UTC**.
- Earliest next routine refresh: **2026-09-30 15:38 UTC**.
- This is a bounded relevance screen of the current listing, not verification of complete papers. Three closest analogues were inspected at abstract level; two pages could not be fetched directly by the browser, so their listing abstracts are the evidence used below.

## Result for the live project

The abstract screen identified no direct producer for the original-action signed-neighbor estimate. This does not establish that the complete papers contain no useful argument.

### Three closest analogues

1. [On the Spectrum of Some Temperley-Lieb Spin Chains](https://arxiv.org/abs/2609.38074): structured one-dimensional spin-chain gap estimates. Analogy only; no identification with the original Wilson operator was found.

2. [Improved estimate of local Markovianity for quantum Gibbs states](https://arxiv.org/abs/2609.38007): conditional-mutual-information decay with boundary-size dependence. A bridge to the project's signed covariance is not supplied by this screen.

3. [Is rapid mixing stable?](https://arxiv.org/abs/2609.36016): instability examples and sufficient stability conditions for Lindbladian dynamics. This is not the project's OS transfer.

## Use and limits

No theorem or hypothesis was imported. No numerical computation or Lean build ran. These cached findings are scope-limited research notes, not proof progress.

## Requested seven-paper review (2026-10-01 22:41 UTC)

This targeted review was requested by the user and performed by a parallel Sol
reviewer, with primary-source record checks by the main agent. All seven v1
records resolve. It is NOT a routine listing refresh; the scan record above
is unchanged. Abstract summaries below are paraphrases. Applicability labels
are our assessment, not a claim that the papers identify the repo's theory.
Theorem screening does not constitute independent verification of full proofs.

### 2609.40171 — boundary reconstruction

[Information-preserving boundary reconstruction for center-flux energetics in a regulated SU(3) gauge ladder](https://arxiv.org/html/2609.40171v1), Hongyu Ma.
The abstract's construction retains unnormalized conditional interior matrices,
including weights and within-branch coherence; path probabilities alone fail
its matched magnetic-observable test. Matched bulk terms cancel, leaving a
length-independent boundary energy cost. Theorems 1–2 (section 6), under H1–H4,
give finite sector/line-energy densities and open/periodic comparison at six
fixed cutoffs. Equations (8)–(10) and (15)–(16) expose the retained information
and cancellation. Spacing, width, coupling and cutoff stay fixed.

Assessment: the closest methodological match for source-preserving boundary
comparisons. Investigate the exact matrix-preservation argument before any
cross-volume energy comparison. No original Wilson norm/covariance estimate,
cutoff removal, transverse limit or continuum mass input is supplied.

### 2609.39802 — quantum sampler localization

[Double Localization for Quantum Gibbs Sampler Gaps: From an Abstract Framework to Finite-Group Models](https://arxiv.org/pdf/2609.39802), Ryu Hayakawa et al.
The abstract separates local quantum updates from a global observable interface.
Theorem 1 (PDF pp. 8–9) combines interface and local bounds under quantitative
assembly conditions. Theorem 2 (pp. 10–11) treats specified Davies dynamics for
vertex-only finite-group quantum-double models, WITHOUT plaquette terms, on
three-regular graphs of girth at least six. Its graph-size-independent gap
requires beta*J < log(5/3); the S3 specialization extends uniformity to
0 <= beta*J <= log(3). Equation (34) records finite assembly counts.

Assessment: local/global assembly method only. The bounded operator is a
thermal sampler generator, not our original OS transfer or physical Hamiltonian.
No identification bridge for this repo is supplied.

### 2609.39475 — blockade Hamiltonian gap

[Excitation gap of a blockade structure with Z2 topological order](https://arxiv.org/html/2609.39475v1), Simon Fell et al.
Theorem 1 and equation (6) establish a size-uniform gap and fourfold ground-state
degeneracy for a two-dimensional blockade Hamiltonian at sufficiently small
Omega and sufficiently large size. The argument uses gap stability and local
symmetry; the paper also discusses extensions to other quantum-double
structures and non-Abelian sector issues.

Assessment: a different interacting Hamiltonian, dimension and perturbative
regime. No original Wilson transfer, scaling, continuum survival or physical
mass input was identified.

### 2609.39780 — obstruction to plaquette-only shortcuts

[No-go theorems for dual Hamiltonians of Non-Abelian Lattice Gauge Theories](https://arxiv.org/html/2609.39780v1), Marco Garofalo et al.
Theorem 1 and Corollary III.2 give a linear-size tree-distance obstruction for
the specified static-constraint dualization, with the additional-link bound
Omega(ell/(K+1)^(1/d)). Theorem 2 shows that the specified dynamic helper-link
plaquette constraint overconstrains the non-Abelian system. These are qualified
duality obstructions, not a no-go theorem for Yang–Mills itself.

Assessment: actionable warning against assuming a plaquette-only rewrite
preserves locality. Retain the original link action and require a proved
operator/locality identification for any proposed dual replacement. The
original-link Wilson/OS path is not refuted by these theorems.

### 2609.38220 — exact hierarchical recursion and certificates

[Positive-temperature spin-glass order on the three-dimensional Migdal–Kadanoff lattice](https://arxiv.org/html/2609.38220v1), Yan Ru Pei.
Theorems A–B establish low-temperature order on a hierarchical Ising spin-glass
lattice using its exact recursion (equation (1.1)). Its effective dimension
1+log2(n) is not a cubic three-dimensional lattice. The Gaussian case includes
computer-assisted rational/interval certificates and associated code.

Assessment: a finite-certificate workflow analogy, not an original Wilson
renormalization law. External computation is not a proof oracle here; any
adapted Rust-produced certificate still needs independent Lean checking.

### 2609.39959 — Davies rapid mixing

[Haah's 3D cubic code thermalizes rapidly](https://arxiv.org/html/2609.39959v1), Sebastian Stengele, Libor Caha, Ángela Capel and Simone Warzel.
The abstract turns a spatial correlation-decay condition into a modified
log-Sobolev inequality for the Davies generator. Theorems 1.1/2.1 yield
fixed-positive-temperature rapid mixing for the cubic stabilizer code, with
the specified bath-rate and correlation assumptions.

Assessment: open-system thermal dynamics, not our original gauge-theory
Hamiltonian. Its mixing estimate cannot be substituted for an OS transfer or
physical mass gap without a same-theory bridge.

### 2609.38295 — unconditional log-concave variance bound

[A dimension-free bound for the isoperimetric constant of unconditional log-concave measures](https://arxiv.org/html/2609.38295v1), Dan Mikulincer and Ilias Zadik.
Theorem 1.1, equation (1.2), bounds the Poincare constant independently of
dimension for isotropic, unconditional, log-concave probability laws on R^n.
The proof transforms the measure and analyzes an associated Dunkl–Langevin
operator; these hypotheses are essential to the stated theorem.

Assessment: relevant variance-bound methodology, but no proof identifies our
compact-group Wilson measure with this hypothesis class. No SAME interacting
variance estimate follows merely from its dimension independence.

## Consequence for the live frontier

No reviewed result supplies the missing original Wilson signed-cost/SAME-variance
estimate on a justified four-dimensional scaling family, nonzero continuum
excitation, physical spacing/mass calibration or every-group realization.
The two prioritized lessons are exact conditional-matrix preservation before
boundary cancellation (40171), and proof of locality before dual substitution
(39780). No theorem was imported as a Lean premise; these notes close no proof
node. Routine literature polling remains at most once per twelve hours.
