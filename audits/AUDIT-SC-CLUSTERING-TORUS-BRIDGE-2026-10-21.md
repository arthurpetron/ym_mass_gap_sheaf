# AUDIT: strong-coupling clustering and the chi1 torus bridge (2026-10-21 PT)

**Labels: U(1)-true. Fixed-coupling gap. NOT evidence for a non-abelian mass gap.**
File: `lean/YMGap/Continuum/BF4StrongCouplingClusteringBridge.lean`.

## Proved (BF4 all-nome heat-kernel carrier, uniform in width)
* `vacuumSq_iterate`: `WilsonVacuumSqContraction r` iterates to `B(T^m y,T^m y) <= (r^2)^m B(y,y)`.
* `even_correlator_decay`: `B(y, T^(2m) y) = B(T^m y, T^m y) <= (r^2)^m B(y,y)`
  (`completedInner_time_sum`).
* `pilot_even_correlator_decay`: at `w = 1/1024`, from `existingNome_allNome_strongCoupling`
  (`allNome_strongCoupling_vacuumSq`), rate `timeRate`; `timeRate ≈ 1/4` checked by `decide`.
  So even-lag decay `(1/4)^n`, `n = 2m`.

## Bridge: explicit OPEN hypothesis
`TorusChiBridge K b c d plane y C`: for all m, `Ehat m <= C · B(y, T^(2m) y)`, where `Ehat m =
SU2ClusterBridge.cov(2m)` is the SU(2) Wilson `T_K` torus chi1 normalized covariance.
`torus_chi_decay_of_bridge` gives `Ehat m <= C (r^2)^m B(y,y)`.

Why it is not closed: the torus carrier (`SU2ClusterBridge`, `SU2ObsInsertion`,
`SU2TorusNormalizedRatio`) and the BF4 carrier (`Completion`) are different constructions with
different couplings (torus β_S = 1/(2·10^12) vs. BF4 nome w), and the repo has no map
taking the torus chi1 plaquette observable to a BF4 vacuum-orthogonal vector with matching
correlator. The torus side already has the unconditional rate 6/7 (`SU2ClusterBridge.cov_decay`),
which this file does not improve.

## Not consumed
`SpectralGap.decay_of_spectralGap_corr0` is a finite diagonal-mode `SpectralModel`; neither
carrier is instantiated as one, so it is not used. `SU2ObsInsertion` is not imported: the bridge
is stated on `Ehat`, which already packages the chi1 insertion covariance.

## Limits
Even lags only (odd lags would need Cauchy-Schwarz on the completed form). Fixed small nome;
no AF, continuum or Clay content.

## Gates
Capped `lake env lean` check, no diagnostics. `#print axioms` for all four theorems:
{propext, Quot.sound}. Banned-token scan clean. `SU2TorusNormalizedRatio.olean` was emitted
box-locally through `safe_lean_build.py --check-output` (not in the copied Mac cache).
