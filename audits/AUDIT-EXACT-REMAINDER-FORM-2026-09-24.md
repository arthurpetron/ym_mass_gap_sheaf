# Exact Taylor remainder and original signed energy estimate

2026-09-24 UTC. Follows `f5ff049` (complete spectator angular contraction).
This is a checked finite SU(2) estimate on the ORIGINAL source energy.
The continuum Yang--Mills / Clay target remains OPEN.

**Subsequent result:** the proposed spectator-remainder contraction is now
proved by exact kinetic recombination and sharp conditional norm-loss control;
see [the follow-up audit](AUDIT-REMAINDER-CHANNEL-CONTRACTION-2026-09-24.md).
The historical verification and declaration positions below refer to this
earlier increment. The SAME-variance/scaling comparison remains open.

## Mathematical change

Let `H` denote the original finite product Haar functional, `P` the full
finite-cutoff product heat map, and `C` the computed cyclic Casimir pairing.
For supported polynomials p,q define

    R(p,q) = H[q*P(p)] - H[q*p] + (1-w)*C(p,q).

`exactRemainderPair_eq_pairRemainder` identifies this expression with the
already computed degree-path Taylor remainder, without an inequality.
Cyclic integration by parts proves symmetry of C; Haar linearity supplies
its test-side algebra. Symmetry and bilinearity of R then follow from the
actual product heat pairing, not from an assumed common spectral basis.

For `0<=w<1` and `sufficientCutoff w<=K`, the existing diagonal remainder
positivity proves `R(p,p)>=0`. Supported polynomials therefore carry actual
positive symmetric bilinear data, and constructive Cauchy--Schwarz gives

    R(p,q)^2 <= R(p,p)*R(q,q).

This `GNSData` is auxiliary finite algebraic data. It is NOT identified with
the reflected physical carrier, a completed Hilbert space, or an OS norm.
Positivity here means diagonal positive semidefiniteness, not pointwise
positivity of a kernel or positivity of every mixed pairing.

## Actual energy consumer

For arbitrary rational s, put y=a*f^2 and z=a*f. Polarization gives

    2*s*R(a,y) = s^2*R(a,a)+R(y,y)-R(s*a-y,s*a-y).

The existing exact first-order cancellation identity now becomes

    2*s*E(a,f) = 2*s*(1-w)*angular(a,f)
                 +s^2*R(a,a)+R(y,y)-R(s*a-y,s*a-y)-2*s*R(z,z).

Both negative diagonal terms remain visible. Dropping only the nonnegative
balancing-residual square yields the `balancedRemainder` estimate. For s>=0
the retained `-2*s*R(z,z)` is also nonpositive. No reciprocal, square root,
optimal-parameter existence claim or newly assumed analytic estimate is used.
For example s=1 is directly admitted.

For the literal original plaquette, q=P_fringe(V*g), where g is the original
terminal message. The actual spectator channels `(lambda_c,h_c)` give
`b_c=P_S(q*h_c)`. Exact channel recombination and the already proved
coefficient-one angular estimate yield, for s>=0,

    2*s*E_original <= 2*s*(1-w)*angular(q,f)
      +sum_c lambda_c [s^2*R(b_c,b_c)+R(b_c*f^2,b_c*f^2)
                       -R(s*b_c-b_c*f^2,s*b_c-b_c*f^2)
                       -2*s*R(b_c*f,b_c*f)].

The balanced version drops only the middle negative square in this sum.
It retains all original weights and the favorable last diagonal. These
inequalities use no `pairBudget` or absolute mode-tree leaf sum. They are not
asserted to dominate the old absolute-budget numerical estimate for every
input; both remain available.

The original action, nome, cutoff, spatial width, terminal depth and common
partition/centering are unchanged. The usual sufficient-cutoff guard remains;
no cutoff dominating source degree is imposed. The source and channels may
depend on every parameter. Channel weights are not probability weights and
individual channel sources may be signed. No per-channel normalization or
centering is introduced.

## Declaration map

All paths below are relative to the repository root.

| Declaration | Source | Content |
| --- | --- | --- |
| `pairCasimir_symm` | `lean/YMGap/Continuum/SU2QuaternionCyclicCasimirBilinear.lean:136` | Actual full-cycle pairing symmetry by IBP. |
| `pairCasimir_add_right` | `lean/YMGap/Continuum/SU2QuaternionCyclicCasimirBilinear.lean:153` | Test-side additivity. |
| `pairCasimir_smul_right` | `lean/YMGap/Continuum/SU2QuaternionCyclicCasimirBilinear.lean:165` | Test-side rational linearity. |
| `pairCasimir_congr_right` | `lean/YMGap/Continuum/SU2QuaternionCyclicCasimirBilinear.lean:180` | Test-side coefficient equivalence. |
| `exactRemainderPair` | `lean/YMGap/Continuum/SU2QuaternionExactRemainderForm.lean:42` | Original operator expression. |
| `exactRemainderPair_eq_pairRemainder` | `lean/YMGap/Continuum/SU2QuaternionExactRemainderForm.lean:49` | Exact identity with computed remainder. |
| `exactRemainderGNSData` | `lean/YMGap/Continuum/SU2QuaternionExactRemainderForm.lean:217` | PSD bilinear data on supported polynomials. |
| `exactRemainderPair_cauchySchwarz` | `lean/YMGap/Continuum/SU2QuaternionExactRemainderForm.lean:238` | Sharp remainder Cauchy--Schwarz. |
| `exactRemainderPair_polarization` | `lean/YMGap/Continuum/SU2QuaternionExactRemainderEnergy.lean:50` | Exact balanced polarization. |
| `polarizedRemainder` / `balancedRemainder` | `lean/YMGap/Continuum/SU2QuaternionExactRemainderEnergy.lean:91` / `:103` | Explicit signed diagonal expressions. |
| `polarizedRemainder_le_balancedRemainder` | `lean/YMGap/Continuum/SU2QuaternionExactRemainderEnergy.lean:113` | Drops only the PSD residual square. |
| `sourceEnergy_polarized_remainder` | `lean/YMGap/Continuum/SU2QuaternionExactRemainderEnergy.lean:154` | Exact source-energy consumer. |
| `sourceEnergy_eq_polarized_channels` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelRemainder.lean:77` | Exact recombination of every channel. |
| `sourceEnergy_le_angular_add_polarized_channels` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelRemainder.lean:118` | Contracts only the angular channel cost. |
| `sourceEnergy_le_angular_add_balanced_channels` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelRemainder.lean:147` | Positive-form bound with negative diagonal retained. |
| `padded_plaquette_energy_le_angular_add_polarized_channels` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPassiveChannels.lean:199` | ORIGINAL-action stronger consumer. |
| `padded_plaquette_energy_le_angular_add_balanced_channels` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPassiveChannels.lean:241` | ORIGINAL-action balanced consumer. |

## Remaining causal frontier

The complete diagonal costs and angular cost still need a useful comparison
with SAME centered variance for ONE explicitly justified changing-scale
observable family, or a useful direct sampled-response estimate. None of the
new statements proves that comparison or a surviving norm floor.

An operator-valued spectator contraction in the exact remainder seminorm is
a candidate next argument, NOT a theorem in this increment. The existing
scalar family Bessel estimate controls raw Haar squares; PSD and Cauchy--Schwarz
alone do not upgrade it to a remainder-form contraction. A proof along this
route must establish the active-remainder restriction and compatibility with
the spectator operations, and the requisite positive operator comparison.
Separate upper estimates for the heat, identity and Casimir pieces cannot
simply be subtracted. No new field assuming that conclusion is introduced.

The separate EVERY-vector spatial/spacing gap, full SAME-theory
continuum/QFT/YM/UV construction, physical-time Hamiltonian identification,
finite positive physical mass and every compact simple group remain OPEN.
No canonical frontier field was changed, weakened or marked closed.

## Verification boundary

Five final serialized monitored checks with one 4 GiB worker returned exit 0:

- `/tmp/ym-gap-casimir-bilinear-check-3.log`: four gates.
- `/tmp/ym-gap-exact-remainder-form-check-5.log`: four gates.
- `/tmp/ym-gap-exact-remainder-energy-check-2.log`: five gates.
- `/tmp/ym-gap-passive-channel-remainder-check-1.log`: three gates.
- `/tmp/ym-gap-original-polarized-channels-check-1.log`: seven gates, five existing.

All 23 printed gates are within {propext, Quot.sound}. Accepted logs contain
no error, warning or sorryAx. Failed draft checks are not proof evidence.
The form's earlier successful check had a harmless unused-binder warning;
the final accepted check follows its removal.

Two preflight reserve refusals and one runtime stop at 11.9 GiB available
preceded observed recovery above the 12 GiB reserve. Checks resumed with the
same limits. An approval guard also held the next launch until a fresh process
inspection reconfirmed that the previous successful session had exited.
No concurrent Lean build ran, no threshold changed, and no unrelated process
was killed.

Sol supplied the Casimir, exact-form and polarization drafts and reviewed the
actual-consumer scope; root repaired/integrated the drafts, proved the complete
channel and original plaquette consumers, and ran the serialized checks.
No source hole, axiom, analytic premise or canonical-field change was added.
The existing `BF4ExactSlabFixedSpatialPassiveChannels` semantic import includes
all four new modules. No full-root build, full-tree audit, guard or
progress-metric run was performed. CI remains disabled.
