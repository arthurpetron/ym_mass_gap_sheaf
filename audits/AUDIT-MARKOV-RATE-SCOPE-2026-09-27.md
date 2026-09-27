# Stress test: a useful dynamics gap is sufficient, not a Clay requirement

This is a targeted source/research review, not a refutation or a new
coercivity theorem. No routine math-ph listing was refreshed. Main checked
the cited primary abstracts after Sol's independent review.

## What the current code actually controls

`final_energy_le_625_loss` in
`lean/YMGap/Continuum/BF4ExactSlabConditionalSweepEnergy.lean:71` is an
upper estimate for the conditional-update sweep on the original full-action
completion. It applies to arbitrary duplicate-free schedules. A useful
lower estimate on centered states remains absent. These dynamics are not
identified with the physical-time OS transfer.

The existing `covariance_as_sweep_pairing` in
`lean/YMGap/Continuum/BF4ExactSlabConditionalCovariance.lean:190` is the
actual normalized finite-covariance connection. Its use of specified
observables does not prove a global dynamics gap. The intended Chebyshev
spatial-rate mechanism is recorded in
`AUDIT-SWEEP-ACCELERATION-2026-09-27.md`; the scalar calibration supplies no
original coercivity constant or lattice-spacing law.

## Relevant evidence and its limits

Schaefer--Sommer--Virotta report strong continuum critical slowing of
squared topological charge in HMC-type lattice-QCD simulations, with an
effective exponent about five in their pure-gauge study. They also study
Wilson-loop decoupling from the slow modes. This is numerical evidence
about specified algorithms/observables, not a theorem about this repository's
SU(2) conditional sweep. [Primary abstract](https://arxiv.org/abs/1009.5228).

Luescher--Schaefer study open temporal gauge boundaries using SU(3) HMC/SMD
simulations. They report removal of topology barriers and autocorrelation
times scaling approximately as inverse spacing squared. This cannot be
imported as a proven SU(2) heat-bath estimate or as a statement about the
repository's precise slab boundary. [Primary abstract](https://arxiv.org/abs/1105.4749).

McGlynn--Mawhinney study topological-density autocorrelations in pure SU(3)
HMC simulations with periodic and open boundaries. Their diffusion model
depends on spacing, tunneling and Euclidean time extent, reinforcing that
boundary choice alone is not a supplied uniform estimate here.
[Primary abstract](https://arxiv.org/abs/1406.4551).

No rigorous obstruction for the exact current SU(2) finite-slab sweep was
found in these sources. Conversely, a physical Yang--Mills gap does not
supply the missing algorithmic gap by any declaration cited above. The
observed exponents are not estimates for this operator. They are a reason
to stress-test the strength of the chosen sufficient premise, not to
declare that premise false.

## Execution adjustment, without changing the target

Keep the global centered-coercivity route as a sufficient route, but do
not elevate it to a necessary Clay input. Seek estimates tied to the actual
observables as well. There is already a smaller exact consumer:
`GNSChebyshevEnergy.state_norm_le`
(`lean/YMGap/Continuum/GNSChebyshevEnergy.lean:127`) needs contraction on
the actual auxiliary recurrence vector at the chosen order. Its sector
version `state_norm_le_on` (`:150`) is optional, not a reason to demand a
new globally invariant sector before attempting a direct vector estimate.

For the sector route, membership of the required observables, preservation
under the relevant maps, and the same-action/covariance identities must be
proved. For the vector route, the required bound must hold for every
recurrence vector actually consumed, with a useful common physical rate.
Neither route is supplied by this review. Finite-support vectors cannot
simply be presumed invariant under the sweep; an observable-specific
prefactor is not a uniform norm bound.

The next analytic work should compare the full centered estimate with
these smaller actual consumers before committing to an unnecessarily
strong all-state dynamics claim. No canonical field, scorecard, physical
Hamiltonian requirement, group quantifier or chart marker is changed.
The whole-project continuum Yang--Mills/Clay target remains open.
