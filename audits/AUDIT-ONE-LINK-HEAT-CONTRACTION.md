# Original one-link heat: contraction from exact marginals

Date: 2026-09-17 UTC. Base revision: `00eca87`.
Whole-project goal: constructive continuum Yang--Mills on R^4 for every
compact simple group, with the required same-theory QFT structure and a
positive physical Hamiltonian gap. That goal remains open.

## Analytic argument

Let W(x,y) be the original finite two-link heat packet, P its actual Haar
integration map, and h=headFloor(w). Both marginals of W are exactly one.
For 0<w<1 and K>=headCutoff(w), W-h has a constructed positive square
certificate. If H(f)=0, then

    H_xy[(W-h) f(x) g(y)] = H_xy[W f(x) g(y)],
    H_xy[(W-h) f(x)^2]    = (1-h) H_x[f(x)^2],
    H_xy[(W-h) g(y)^2]    = (1-h) H_y[g(y)^2].

Weighted Cauchy--Schwarz gives

    <P f,g>^2 <= (1-h)^2 ||f||^2 ||g||^2.

Take g=P f. A positive rational output norm can be cancelled; the zero
case is handled separately. The result is the actual centered squared-norm
contraction with rate (1-h)^2<1. There is no basis restriction on f and no
absolute cap on the whole kernel in this proof.

## Kernel-checked declarations

All paths below start with `lean/YMGap/Continuum/`.

- `SU2QuaternionHaarMarkovContraction.lean:51`, `haar_split_pairing`: exact
  factorization of two supported slots using existing ordered Haar integration.
- Same file `:139`, `kernelMap_square_contraction`: exact unit marginals and
  a positive certificate give the ordinary norm bound one.
- Same file `:155`, `kernelMap_centered_bilinear_bound`, and `:204`,
  `kernelMap_centered_square_bound`: the residual-kernel argument above.
- `SU2QuaternionRelativeHeatMarkovData.lean:57`, `relativeHeat_supported`,
  and `:69`, `relativeHeat_eq_prefix`: original complete packet, every spin
  through K, on the same two-quaternion carrier.
- Same file `:78`, `relativeHeat_floorCertificate`: uses the actual Haar-unit
  relative quaternion and `QuaternionHaarAllNomeHeatCertificate.prefixFloorCertificate`
  (`QuaternionHaarAllNomeHeatCertificate.lean:137`), with its existing cutoff.
- Same file `:126`, `relativeHeat_lower_marginal`, and `:138`,
  `relativeHeat_upper_marginal`: exact marginals on arbitrary supported
  one-block polynomials, at every cutoff and rational nome.
- `SU2QuaternionRelativeHeatContraction.lean:47`, `heatMap`: the actual
  existing `kernelMap` with the original `relativeHeat` polynomial.
- Same file `:55`, `heatMap_mean`, and `:71`, `heatMap_square_contraction`:
  exact mean preservation and ordinary Haar norm contraction.
- Same file `:81`, `heatRate`, and `:83`, `squaredHeatRate`: returned rational
  rates 1-headFloor(w) and its square; `squaredHeatRate_lt_one` at `:104`
  proves strictness under the explicit nome guards.
- Same file `:112`, `heatMap_centered_square_bound`: the concrete estimate
  for every supported Haar-centered polynomial, independent of its degree
  and late cutoff, with no supplied mixing hypothesis.

## Consumer and boundaries

The intended next mathematical consumer is tensorization on the original
`BF4ExactSlabFixedSpatialKineticHeat.kineticWeight`
(`BF4ExactSlabFixedSpatialKineticHeat.lean:68`). A theorem identifying its
full polynomial map with a product of the one-link maps and remaining Haar
projections, and proving a width-independent centered bound, is not supplied
by this increment. Its `baseLinks` include fringe coordinates not paired by
`temporalFaces`; no bijection with ALL base links may be assumed.

The actual weighted transfer additionally contains the spatial potential.
Ordinary Haar centering, norm, and vacuum are not silently identified with
the interacting OS ones. The concrete one-link result is an analytic input
to a stronger kinetic reference estimate, not an interacting mass gap.
No positive margin is claimed uniformly in w or in physical lattice spacing.
The generic positive-kernel argument is not a non-abelian mass-generation
mechanism; its actual heat input here is SU(2).

The preceding width obstruction concerned a different, coarser computed
whole-layer floor/cap rate. This theorem does not contradict it.
Separately, retained-head relative tail bounds control corrections around
an interacting retained head; they do not prove spatial decay of that head.
Inactive-tail faces still carry interacting factors, so separation of tail
supports alone does not justify disconnected-action cancellation.

## Verification and collaboration

One parallel agent supplied the actual kernel inputs; the parent supplied
the general analytic argument and its concrete consumer. An independent
read-only reviewer checked all three complete files and found no mathematical
or scope defect. The parent alone ran six focused serialized checks with one
worker and a 20 GiB ceiling; the three final checks pass all 21 public gates
within {propext, Quot.sound}. The rate definitions are axiom-free. Development
repairs were missing section-variable inclusion, one definitional `rfl`, and
one namespace opening. Final logs have no errors or warnings.

Process preflights found no competing compiler/runner/test process; swap
remained 6797.19 MiB. No safety limit changed. No sorry, axiom, old analytic
guard or canonical frontier statement changed. Root imports added;
root/full-tree/full audit/guard not run. CI stays manual-only.

Final log SHA-256 values:

- `/tmp/ym-haar-markov-contraction-20260917.log`:
  `731cdc76844380e591f367089c4ba345e5d995d4a9f17875ad263b0730721196`.
- `/tmp/ym-relative-heat-markov-data-20260917.log`:
  `09c87fd4d3b667b15bbdfebd2871b2a2046eb76f02b1cce4ba7f699998a4deb8`.
- `/tmp/ym-relative-heat-contraction-20260917.log`:
  `8788c1bec52da6a6aa5ce4c86ad38376f992312e56918768867830992e2e52c2`.
