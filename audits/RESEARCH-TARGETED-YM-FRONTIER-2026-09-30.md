# Targeted literature review: signed source cost and the SAME variance

Reviewed 2026-09-30. This is the user's eight-paper request, supplemented by
their `USER FOCUS backfill` attachment, not a routine math-ph listing scan.
The attachment's wider corpus search is user-supplied context; we did not
repeat or independently certify that search. No external graph was changed.
This report records research and a revised proof priority, not a Lean theorem.

Whole-project goal remains constructive continuum Yang--Mills on R^4 for
every compact simple group, with the same theory's QFT axioms and positive
physical mass gap. None of these papers discharges that target or the current
original-SU(2) scaling estimate.

## What to use, and what not to import

### 2609.28091v1 — signed susceptibility deficit

[Abdelghani--Bauerschmidt--Bodineau--Dagallier, full text](https://arxiv.org/html/2609.28091v1).
Proposition 2.3, (2.8), proves for 2D sinh-Gordon, b^2<1/2,

    chi_t <= t - c mu t^(2+b^2) + C^2 mu^2 t^(3+2b^2).

The notation convention makes constants independent of lattice spacing and
volume, not of b. Equations (2.9), (2.12) give a positive curvature quantity
`1/t0 - chi_t0/t0^2`; Theorem 2.1 gives a uniform LSI. This is NOT an already
proved physical transfer/Hamiltonian mass gap: the discussion following
Corollary 2.2 describes exponential correlation decay as expected further work.

The useful proof sequence is Proposition 2.7's exact Schwinger--Dyson identity
(2.46), Proposition 2.5/Corollary 2.6's signed lower estimate, and Lemma 2.8's
uniform remainder bounds. The LSI step also uses scalar ferromagnetic/GHS/DSS
structure, (2.17)--(2.19), not merely integration by parts. Corollary 2.2 gives
tightness/subsequential infinite-volume limits, not our computable limit modulus.
**Use:** a signed comparison template. **Missing:** its gauge counterpart and
the correct comparison to our original temporal energy.

### 2608.05415v1 — finite Haar identities

[Chatterjee--Frasca--Ghoshal--Groote, full text](https://arxiv.org/html/2608.05415v1).
Section II, (6), states zero integral of a link Lie derivative under product
Haar measure. Section III, (18), specializes to a Wilson-action link-source
master equation. Sections I and IV--VI explicitly distinguish these finite
identities from the formal gauge-fixed continuum expansion and scalar closure.
The sources in (16) are gauge-variant link insertions, not automatically our
gauge-invariant Wilson observables.

**Use:** retain the entire action inside a weighted integration-by-parts
identity before estimating the signed terms. Re-derive coefficients from our
actual heat-weight convention; do not substitute the paper's Wilson action,
staple normalization or source for the repository's original objects.
Neither (6) nor (18) supplies a uniform variance bound, a continuum limit, or
the needed non-abelian quantitative improvement. The generic Haar identity
itself does not exclude abelian groups.

### 2608.27828v2 — abelian dynamical scaling control

[Chevyrev--Qu--Shen, full text](https://arxiv.org/html/2608.27828v2).
Theorem 2.5 concerns 3D U(1), canonical weak-coupling scaling
`beta=epsilon^(-1)`, DeTurck gauge and stopped rescaled Langevin dynamics,
converging to a one-form stochastic heat equation. This is a rigorous result
in its stated setting, not a failure of continuum construction. Langevin time
is not OS physical time. **Use:** a negative control against equating a
scaling limit with a non-Gaussian nonabelian theory; it does not refute our
unconstructed 4D SU(2) family or supply its estimates.

### 2608.05998v2 — scope of mean-field triviality

[Borji, full text](https://arxiv.org/html/2608.05998v2).
Theorem 2 establishes Gaussian limiting behavior for the specified
second-order mean-field hierarchy at symmetric momenta. Control of the full
higher-order remainder is not established. **Use:** test whether a proposed
closure has erased the interactions being studied. Do not report this as a
triviality theorem for the full interacting phi^4_4 measure, still less for YM.

### 2608.15923v1 — actual universality, in two dimensions

[Lemoine--Nohra, full text](https://arxiv.org/html/2608.15923v1).
Theorem 1.1 proves convergence of holonomy processes on compact oriented
surfaces for compact connected Lie groups, under infinitesimal Fourier and
uniform spectral summability assumptions. Its Yang--Mills class includes
heat-kernel/Villain, Wilson and Manton actions. Theorems 1.3--1.4 give
partition/observable state sums separating action-dependent Fourier data
from loop/topology coefficients. **Use:** a precise model for a pinned
same-observable action/refinement comparison. The parameter indexing the
holonomy process is a loop, not OS time. No 4D action-universality theorem,
physical Hamiltonian gap or constructive modulus for this repository follows.

### 2606.28945v2 — infinite volume at strong coupling and large N

[Lemoine, full text](https://arxiv.org/html/2606.28945v2).
Theorem 1.1 constructs the U(N) heat-kernel master field on Z^d, d>=2,
for `T>T0(d)`, using volume-uniform 1/N expansions and exponentially local
infinite-volume coefficients. Theorem 1.2 supplies an area-law bound.
**Use:** a genuinely quantitative loop-observable thermodynamic benchmark.
The limits are volume and N, at fixed lattice and strong coupling; this is
not fixed-SU(2) continuum scaling, nor a same-operator transfer-gap proof.

### 2608.10133v2 — a 2+1D Hamiltonian outline

[Nair, paper](https://arxiv.org/pdf/2608.10133v2).
Equations (26)--(31) argue for the kinetic inequality `T^2-mT>=0`, with
`m=e^2 c_A/(2 pi)`, giving a floor for nonzero kinetic eigenvalues. The
article explicitly presents an outline with regularization issues. Extending
the lower bound using `H>=T` depends on the treatment of the potential and
vacuum; even the apparent one-current saturating state is excluded by the
residual holomorphic redundancy. **Use:** distinguish a spectral-polynomial
argument from its required operator/domain/physical-state proofs. This is
SU(N) in two spatial dimensions, not a proved 4D mass calibration.

### 2607.05492v1 — Lean infrastructure, not a compatible dependency

[Kasaura et al., paper](https://arxiv.org/html/2607.05492v1).
Section IV.3 displays `haarUnitary`, Haar/probability instances and
`twirl_eq_smul_one`; the library concerns finite-dimensional quantum
information. Its Haar object is defined noncomputably through `haarMeasure`.
The [official dependency manifest](https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/main/lake-manifest.json)
contains a direct Mathlib dependency. Our project has no Mathlib version to
match: it is deliberately Mathlib-free. **Use:** statement/proof organization
and finite algebra only after independent constructive reconstruction.
No transitive axiom profile for these declarations was certified in this
review; no installation, build, clone or dependency change was performed.

## Repository joins actually available

These are source citations, not claims of a fresh compilation in this review.

| Mathematical ingredient | Existing declaration |
| --- | --- |
| Arbitrary-block Haar derivative cancellation | `lean/YMGap/Continuum/SU2QuaternionHaarAngularIBPAt.lean:77`, `quaternionHaar_angularDerivative_at` |
| Full signed weight/test product rule | `lean/YMGap/Continuum/SU2QuaternionHaarAngularIBPAt.lean:99`, `quaternionHaar_weighted_angular_at` |
| Retain independent background **inside** the integral | `lean/YMGap/Continuum/SU2QuaternionHaarAngularIBP.lean:151`, `quaternionHaar_retained_background` |
| First-order source cancellation, both signed remainders retained | `lean/YMGap/Continuum/SU2QuaternionProductHeatAngularTaylor.lean:107`, `sourceEnergy_taylor_angular` |
| Present source-dependent quadratic budget | `lean/YMGap/Continuum/SU2QuaternionProductHeatAngularTaylor.lean:121`, `sourceEnergy_le_angular_add_quadratic` |
| Infinitesimal common signed-square identity | `lean/YMGap/Continuum/SU2QuaternionProductHeatAngularHessian.lean:144`, `productHeat_upperHessian_eq_neg_square` |
| SAME completed centered variance | `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyVariance.lean:126`, `centered_norm_pin` |
| Whole signed temporal increment = twice SAME transfer defect | `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyEnergy.lean:49`, `family_increment_completed_pin` |
| Consumer for a supplied relative energy upper estimate | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorSourceTransfer.lean:116`, `relative_derivative_bound` |

## Revised proof priority — inference and proposed test, NOT a proved gauge bound

1. Do not rebuild generic Haar integration by parts or add another conditional
   survival package. Start at the actual numerator and denominator above.
2. Keep the two required inequalities distinct. A variance upper bound
   controlled by energy is gap-type information. The present survival input
   instead needs an upper bound on energy relative to the variance of ONE
   nonzero source. The first does not imply the second.
3. For one explicit signed source, apply the existing angular product rule
   with the COMPLETE finite heat/terminal weight and source insertion. Expand
   its signed action derivatives jointly. Keep mean corrections, cross terms,
   partition factors and cutoff errors. Do not identify the auxiliary `a^2`
   angular weight with the stationary marginal without a proof.
4. Test whether the resulting signed correction and remainder can be bounded
   relative to the SAME variance with a useful changing-nome/width budget.
   Required output remains `E_j <= M*tau_j*Var_j`, with actual physical `tau_j`
   and explicit finite M on a justified family. If only the existing local
   absolute costs result, this test has not advanced the frontier.
5. Do not import scalar GHS/DSS positivity, Gaussian domination, or an
   unconstrained free covariance into the nonabelian law. Any proposed gauge
   estimate must expose its group-dependent input and be tested against the
   abelian and boundary-kernel cases. Haar invariance alone is insufficient.
6. Once the useful source estimate is proved, use the existing source/domain
   transfer. Continue the original-carrier resolvent construction as the
   independent reconstruction task, not as evidence for scaling survival.

No canonical diagram state changed; no chart is reprinted. The signed gauge
estimate, justified scaling family, physical OS identification, nontrivial
continuum survival, physical mass, full QFT and all-group result remain OPEN.
