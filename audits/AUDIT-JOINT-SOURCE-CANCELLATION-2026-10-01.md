# Joint source responses in original plaquette energy

Date: 2026-10-01 UTC. The two source tests now have a proved simultaneous
estimate for the complete original terminal source, retaining their mixed
correction and the same odd partition. Comparison with interacting centered
variance and justified physical scaling remains open.

## Exact finite argument

Let H denote one-slice Haar, P the original full product heat and f the
fundamental plaquette character. For the actual projected terminal source q,
use the normalized product-heat pairing and write

    r=(q_x-q_y)*(f_x-f_y),  s=(q_x+q_y)*(f_x+f_y),
    D=<r,r>,  J=<r,1>,  M=<s,1>,  S=<s,s>,
    A=H[q^2],  F=H[q^2*f^2],  R=(1-w^32)*(F-A).

The original heat images give J=2*(1-w^12)*H[q*f],
M=2*(1+w^12)*H[q*f] and <r,s>=2*R. Center both tests along the unit
polynomial. Cauchy--Schwarz gives

    (2*R-J*M)^2 <= (D-J^2)*(S-M^2).

Positivity of D-J^2 and the supplied S<=64*A give the same inequality
with K=64*A-M^2 in place of S-M^2; K>=0 is proved. Substitute the
original exact identity 4*E+D=2*C:

    4*K*E + K*J^2 + (2*R-J*M)^2 <= 2*K*C.

The stronger exact-norm version uses S-M^2. S remains the actual computable
weightedPair; no one-slice norm reduction is asserted. No A or centered norm
is inverted. The centered second response may vanish even when R does not;
this is not an unconditional additive J^2+R^2 gain.

## Declarations and normalization

`GNSUnitCenteredGram.centered_cauchySchwarz`, `centered_cap_nonnegative`,
`capped_centered_cauchySchwarz` and `joint_energy_budget` are in
`lean/YMGap/Continuum/GNSUnitCenteredGram.lean:36`, `:50`, `:57`, `:70`.
They reuse `GNSUnitVacuumProjection.center_pairing_eqv`.
`sumTest_mean`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatSumGram.lean:42`, proves
the generic mean using both original heat marginals and heat symmetry.

The actual consumers are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceJointCancellation.lean`:
`plaquette_sum_mean` at line 98 computes M;
`jointVarianceCap_nonnegative` at line 132 proves K>=0;
`padded_terminal_exact_joint_budget` at line 218 retains S;
`padded_terminal_joint_budget` at line 235 supplies the cap;
`padded_terminal_normalized_joint_budget` at line 256 retains the SAME Z.
With X=2*R-J*M, its statement is

    4*(K/Z)*(E/Z) + (K/Z)*(J^2/Z) + (X/Z)^2
      <= 2*(K/Z)*(C/Z).

J is linear in q, while K,E,C,X are quadratic. Every raw term has source
degree four; normalization multiplies by Z^(-2). In particular the first
response contributes J^2/Z, not (J/Z)^2. Cutoff, width, depth and strict
face padding are explicit. No new analytic or stationarity premise.

## Open consumer and source review

The joint Gram requirement is now supplied. A quantitative estimate of the
complete signed cost versus SAME interacting variance is still required.
Raw q^2 and H[q*f] moments cannot be identified with the q*Pq law. No
strict gain, useful scaling order, survival or physical calibration follows.
The even-only budget floor does not decide the combined bound. Continuum
QFT and every compact simple group remain open.

Parallel source review found that an adjacent fundamental plaquette pair
retains the bare eigenvalue w^12 by linearity. Shared-link contraction
requires a boundary independent of that link, unlike the actual spatial
and terminal weight. These are planning observations, not newly checked
pair estimates; no original mixed temporal-increment lower bound is supplied.

## Verification

Three final focused checks exited 0 with 15 printed gates exactly in
{propext, Quot.sound}. They used the monitored launcher, one worker, 20 GiB
worker cap, 12 GiB OS reserve and dynamic telemetry. Preflight found no
competing compiler/runner and reported 90 percent memory free. Intermediate
namespace and elaboration errors were fixed before accepting final checks.
Independent Sol review confirmed the correction, source degrees and Z powers.

No sorry, new axiom, Classical, native_decide, noncomputable declaration or
frontier weakening. No full root build, tree audit or guard; root imports are
registered only. No canonical chart node changed or chart was reprinted.
The documentation records the checked finite statement and its open consumer.

| Final log in /tmp | SHA-256 |
| --- | --- |
| ym-unit-centered-gram-20261001.log | b489de6312516f6123db149d70639e60f5dcec67e86cd6cc9562aed9fa047f80 |
| ym-product-heat-sum-gram-final-20261001.log | c33e7abe16c07d31a6395b257d0077f9081635c52f2b9930f96f7e93ace6637c |
| ym-original-joint-cancellation-final-20261001.log | 127e2ff9a8612e119fafa9f1a6cabe4db0173a84568ff253d283800dde91478f |
