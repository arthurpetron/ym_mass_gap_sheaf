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
