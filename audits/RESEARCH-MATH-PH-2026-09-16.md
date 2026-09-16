# New math-ph papers: relevance to the constructive Yang--Mills route

Reviewed 2026-09-16 by a parallel read-only reviewer, with the principal
agent checking the listing and the cited primary-source passages. The
[live listing](https://arxiv.org/list/math-ph/new) was dated 16 September:
5 new primary submissions, 36 cross-lists, 38 replacements. Four promising
full texts were inspected. This is a research screen, not verification of
the papers' proofs or a new Lean theorem.

Whole-project goal: nontrivial continuum quantum Yang--Mills on R^4, the
required QFT axioms, and a positive physical Hamiltonian gap for each compact
simple group, within the repository's constructive witness/axiom contract.

## Outcome

No reviewed paper directly supplies the original-Haar quantitative estimate,
the all-nome stationary OS identification, or the continuum passage. Two
papers offer useful methodological comparisons; a third gives a useful
test for information-losing reductions. None is imported as an assumption.

## 1. Exact backward messages: closest to the current finite-composition task

Vilas Winstein, **Renormalizing small ball events for branching random walk**,
[arXiv:2609.17520v1](https://arxiv.org/html/2609.17520v1), section 2.1,
Definitions 2.1--2.3 and Lemmas 2.4--2.5. A recursively convolved potential
normalizes a tree-indexed Markov chain whose endpoint law is the original
tilted Gaussian branching law. The last potential also identifies the
partition function. The paper explicitly attributes the central identity
to earlier work; it is not claimed here as a new principle.

Project assessment: useful bookkeeping for finite-horizon original-layer
messages before constructing a stationary law. Its covariance estimates
need additional scalar convexity/confinement and branching hypotheses;
they are not estimates for SU(2) quaternion-Haar interactions. No such
applicability bridge was found. Do not transplant its decay rate.

## 2. Scale-aware mass generation: instructive, different model

Abdelghani--Bauerschmidt--Hofstetter--Zeitouni, **Mass gap for the hierarchical
sinh-Gordon model**, [arXiv:2609.17461v1](https://arxiv.org/html/2609.17461v1),
Theorem 1.3, Propositions 2.3--2.4 and Corollary 2.5. For `0 < b^2 < 1` and
`mu > 0`, the theorem constructs the ultraviolet-then-infrared limit and
controls the log-Sobolev constant and covariance using an effective mass
parameter comparable to `mu^(1/(1+b^2))`; comparison constants depend on b.
The central mechanism is quantitative convexification of the renormalized
scalar potential.

Project assessment: worth studying for how a useful estimate survives scale
passage. The theorem concerns a two-dimensional hierarchical scalar model.
The text after (1.16) explicitly distinguishes hierarchical massive decay
from Euclidean exponential decay. It is not an OS Hamiltonian gap for
four-dimensional Yang--Mills, and it supplies no constructive moduli or
original-gauge-action comparison for this repository.

## 3. Compression sanity check: exact state retention matters

Abhishek Chowdhury, **Hidden kinetic correlations control collective phases
of entropy-conditioned histories**,
[arXiv:2609.16355v1](https://arxiv.org/html/2609.16355v1#A11.SS1), Appendix K.1,
Proposition 2 and equation (192). With a finite irreducible visible graph,
visible jumps preserving hidden state, and irreducible finite Metzler
hidden matrices, autonomous visible Doob rates are equivalent to a shared
positive hidden eigenline. In the reversible stationary setting, the
second-order semigroup defect is
`P L^2 P - (P L P)^2 = (Q L P)* (Q L P)`, with `Q = I-P`.

Project assessment: test invariance before claiming that a lossy projection
preserves repeated evolution. This is not the repository's exact coordinate
recoding: the latter reconstructs every supported polynomial coordinate.
The paper does not construct the original Haar Perron vector, OS operator,
or physical-scale estimate.

## 4. A uniform diffusion gap, not an OS gap

Boutiah--Kinzebulatov--Madou, **Uniform many-particle spectral gap inequality
and heat kernel bounds for strong attractive interactions**,
[arXiv:2609.17333v1](https://arxiv.org/html/2609.17333v1), Theorem 1 and
sections 4.1--4.3. For `d >= 3`, `N >= 2`, and
`0 < nu < (d-2)^2/(3d)`, a Gaussian-confined logarithmic gas has Poincare
constant `((d-2)^2-3*d*nu)/(2*s*((d-2)^2-d*nu))`. It is independent of N,
collision regularization, and Gaussian center, but depends on confinement
scale s. Integrated Hardy and Bochner estimates control the negative Hessian.

Project assessment: low immediate priority. This is a diffusion Dirichlet-form
gap, not an OS transfer or Hamiltonian gap. Removing confinement is not
covered by its particle-count uniformity.

## Connection to actual open declarations

- `lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:224`,
  `covariance_response_bound_eventually`: its signed quantitative premise
  is not discharged by any reviewed paper.
- `lean/YMGap/Continuum/BF4ExactSlabAllNomeSpatialHeatCertificate.lean:144`,
  `interface_weighted_floor`, and
  `lean/YMGap/Continuum/BF4BoundaryMessageProjectiveRefresh.lean:706`,
  `terminalProjectiveRefresh_l1_contraction`: the former's original-Haar
  square-certificate estimates do not supply the latter's finite-state
  kernel hypotheses merely by analogy.
- `lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetExpectation.lean:78`,
  `finite_converges`: the insertion is fixed; a cutoff-dependent message
  requires its own compatibility proof or a return to the fixed original
  insertion before taking limits.

Next use: consult the exact backward-message normalization when implementing
finite iteration of the ORIGINAL kinetic/spatial factors. Establish all
Haar identities in Lean and keep stationary normalization, quantitative
control, and continuum passage separate. The goal and axiom gate are unchanged.

## Parallel recheck, 2026-09-16 09:49--09:54 UTC

At the user's renewed request, a parallel reviewer screened all 79 titles
and abstracts in the [live listing](https://arxiv.org/list/math-ph/new),
including replacements. The announcement date and counts remain those above.
The four previously detailed papers' abstract histories still show v1 only.
This is not a byte-level comparison: the earlier screen stored no complete
per-entry version manifest. The parent independently checked the current
source consumers and selected primary-source passages.

### Additional findings

**Defant--Galicer, Intrinsic Bohnenblust--Hille Inequalities for Local Qudit
Systems:** the reviewer inspected the self-labelled
[v2 PDF](https://arxiv.org/pdf/2609.13084), dated 14 September; explicit v2
HTML was unavailable. The parent checked the v2 abstract history and v1 HTML.
Theorem 3.1 (printed p. 8) bounds coefficient l^p by operator norm,
`p = 2*d/(d+1)`, uniformly in site count n, but with local-dimension K and
interaction-order d dependence. Theorem 3.12 (p. 17) gives unavoidable
growth of the asymptotic exponential constant with K. Theorem 5.1 (p. 27)
places the coefficient l^1 normalization between
`c(K)^(-d)*(n/d)^((d-1)/2)` and `c(K)^d*(n/d)^((d-1)/2)`.

Assessment: a useful norm-loss warning, not a volume-uniform l^1/operator
bridge. Here K is local matrix dimension, not our heat cutoff, and d is
interaction order, not spacetime dimension. No original-Haar/OS norm
identification or cutoff-uniform compact-group application was found.

**Frob, A generalization of the Powers--Stormer--Ogata inequality:**
[Theorem 1](https://arxiv.org/html/2609.16184v1) compares normal positive
functionals on a von Neumann algebra in standard form through a relative
modular operator and a positive operator-monotone function. Its proof uses
the variational Lemma 2 and integral representation Theorem 3, spectral
measures, and dominated convergence/Tonelli. Assessment: possible later
state-comparison guidance; it provides neither a dynamical contraction nor
the explicit polynomial certificate or convergence modulus needed here.

**Vladimirov, Renyi's Relative Entropy Lyapunov Functional for Convergence
to Invariant Measure in Dissipative Stochastic Hamiltonian Systems:**
[Theorem 3, section 11](https://arxiv.org/html/2609.16297v1) assumes conditions
(65), (67), (69), (95), and (111), and establishes strict decrease of
chi-square divergence before equilibrium. Assessment: the statement supplies
no explicit decay rate. This finite-dimensional dissipative dynamics result
is not a volume-uniform original transfer estimate or a physical YM gap.

**Jiang, Higher abelian gauge theory in BV formalism:**
[Theorem 2.1](https://arxiv.org/html/2609.17518v1) makes a zero-mode partition
function independent of a maximal admissible Lagrangian under its stated
niceness/admissibility hypotheses, including unimodularity and positivity.
Assessment: abelian quadratic zero-mode integration is not the nonabelian
interacting Haar integration problem. No relevant square-certificate
preservation or transfer estimate was found.

### Updated connection to the live proof path

The earlier "Next use" suggestion is now partly historical:

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOriginalIteration.lean:182`,
  `original_chain_iteration`, already identifies the original selected-chain
  moment with the actual weighted-step iterate.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialIterationLimit.lean:177`,
  `normalized_converges`, already passes the whole normalized scalar stream
  to the same original selected-action expectation. Winstein's finite-message
  bookkeeping now mainly corroborates that implemented finite path.
- `lean/YMGap/Continuum/QuaternionHaarSquareCertificate.lean:62`,
  `Certificate`, requires explicit square/addition/scaling/transport data;
  none of the newly inspected statements supplies a producer preserving
  these certificates under original partial Haar integration.
- `lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:224`,
  `covariance_response_bound_eventually`, still requires its finite signed
  response estimate. No inspected paper discharges that premise.

Conclusion: no inspected theorem closes the original-Haar certificate,
quantitative boundary-forgetting, stationary/OS, or physical-gap bridges.
Retain the norm-loss warning and later state-comparison reference; do not
repoint the proof around an unproved analogy. These are source-screening
findings, not independent verification of the papers or new Lean results.
No Lean file, hypothesis, axiom gate, or goal was changed by this recheck.
