# Actual completed bent signed gain and every integer-time image

The unchanged whole-project goal is continuum quantum Yang--Mills on R^4
for every compact simple group, with full SAME-theory QFT structure and a
positive physical Hamiltonian mass gap. It remains OPEN. This increment
constructs the actual completed signed gain and its fixed-probe time orbit,
then proves the gain ceiling that constrains a scaling extension.

## Actual forward producer, not an assumed gain

Fix w=1/16, width two and the existing centered literal bent state v.
Write C_k=B(v,T(k)v), where B and T are the EXISTING original completed
inner product and time maps. The reference a=w^18 is NOT an interacting
centered eigenvalue. The preceding original producer covers every finite
K satisfying BOTH K>=1 and headCutoff(w)<=K and every terminal depth n.
It retains the actual odd OWN mean, full original spatial action and SAME
even partition E; the original gain G satisfies G>=S/4 and G/E>=2^-130.

The strict bent-source pin identifies that original normalized gain with
the already defined normalizedFiniteGain. Both S and G are divided by the
SAME positive E. The original chronological square pin and the existing
OWN-centered pair limit identify S/E with C2. For the gain stream, the
computed diagonal modulus is max(existing cutoff threshold, existing time
threshold); the independently computed representative threshold remains
separate. The already proved finite-gain approximation therefore constructs
convergence to the EXISTING gainLimit, not a replacement limit.

Eventual order passes the actual relative finite inequality to that limit;
its existing centered/completed pins give

    C2-a*C1 >= C2/4,       C2-a*C1 >= 2^-130.

No favorable-gain hypothesis, Haar-to-OS norm substitution, recentering or
denominator identification is used. Input evidence:
`audits/AUDIT-ALL-DEPTH-ORIGINAL-BENT-GAIN-2026-10-03.md`.

## Exact time propagation on that same state

Clearing the relative gain by rational 4/3 gives rho*C1<=C2 with
rho=(4/3)*w^18>0. Existing positive-power response propagation then gives

    rho*C_(k+1) <= C_(k+2),
    C_(k+2) >= rho^k * 2^-128,
    ||T(n+1)v||^2 >= rho^(2*n) * 2^-128 > 0.

Every integer-time image is consequently nonzero. There is no real division
or spectral construction. The completed drop bound is
C_(k+1)-C_(k+2)<=(1-rho)*C_(k+1). Its coefficient does NOT shrink with
side length; multiplying by side makes it grow. No finite estimate is
inferred by reversing convergence.

## Backward constraint and the sharper analytic target

For the EXISTING original all-nome completion, every state x and integer
lag k, positive time-defect moments prove C_(k+1)<=C_k. Hence, for a>=0,

    gain := C_(k+1)-a*C_k <= (1-a)*C_(k+1),
    (1-a)*C_(k+1)-gain = a*(C_k-C_(k+1)).

If the SAME next response has an explicit positive rational floor and
gain>=gamma*C_(k+1), eventual positive-factor cancellation proves
gamma<=1-a. This excludes continuation of a fixed quarter-gain bound to
reference a>3/4 on positive responses. It does NOT assert that a growing
loop's reference approaches one or that any actual response vanishes.

The identity identifies the stronger input for a gain-based scaling route:
control its deficit to the ceiling relative to the SAME response, retaining
quantitative dependence on the positive reference a. At a=0 that deficit
vanishes regardless of the drop. Mere gain positivity or the fixed quarter
fraction is insufficient. No such
analytic producer or changing family is assumed or constructed here.

The main unpaid meet-in-the-middle proposition stays the COMBINED original
energy and signed multiplication cost against the half-smoothed ell(b^2),
retaining both partitions, on a JUSTIFIED changing family:
s*D<=C*Z1*ell(b^2), or the direct SAME macroscopic-response-ratio alternative.
The exact original split and existing completed cost/variance limit already
provide the joins; another normalization compiler is unnecessary.
Growing-loop/spatial/spacing control, continuum survival, physical mass
calibration, full SAME-theory QFT and every compact simple group remain OPEN.

## Declaration anchors

Source prefix: `lean/YMGap/Continuum/`.

- `BF4WilsonSmallNomeBentSignedLimit.lean:118`, `bentGainDiagonalModulus`;
  :124, `bent_gain_diagonal_converges`; :136, `bent_signed_limit_relative_lower`;
  :156, `bent_signed_limit_floor`; :172, `bent_completed_signed_gain_relative_lower`;
  :178, `bent_completed_signed_gain_floor`.
- `BF4WilsonSmallNomeBentSignedOrbit.lean:57`, `orbitRate`;
  :110, `bent_response_start_floor`; :129, `bent_response_step_floor`;
  :143, `bent_response_geometric_floor`; :164, `bent_time_norm_floor`;
  :171, `bent_time_norm_ne_zero`; :185, `bent_time_ne_zero`;
  :192, `bent_response_drop_bound`.
- `BF4WilsonAllNomeGainStrengthConstraint.lean:46`, `response_time_decreasing`;
  :61, `signed_gain_upper`; :81, `signed_gain_ceiling_deficit`;
  :97, `signed_gain_strength_constraint`.
- Existing actual limit input: `BF4WilsonAllNomeFilteredFiniteGainLimit.lean:111`,
  `normalizedFiniteGain_approx`; `BF4WilsonAllNomeFilteredGainLimit.lean:100`,
  `gainLimit_centered_pin`; :131, `gainLimit_completed_pin`.
- Existing time consumer: `BF4WilsonAllNomeDyadicFilteredGeometricSurvival.lean:78`,
  `response_shifted_step_lower`; :93, `response_shifted_geometric_lower`.
- Existing backward join: `BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:234`,
  `original_block_rayleigh_split`; :261, `boundaryDrift_terminal_abs_le`;
  `BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:157`,
  `originalOwnBlockCost_converges`.

## Verification evidence

Three final serialized focused checks exited zero. All 20 distinct printed
gates (6+10+4) have only {propext, Quot.sound}, or no axioms (Orbit's
definition and two computational lemmas). Accepted logs contain no errors, warnings,
sorryAx or PANIC. Failed Orbit development log a is excluded; explicit Nat
index rewrites and local opacity fixed its elaboration timeout without
changing statements or raising proof/resource limits. Final Orbit log b
supersedes it.

Every launch used a fresh memory/process/swap preflight, the monitored safe
launcher, one worker, a 12GiB reserve and 20GiB worker ceiling. Accepted-run
preflights had 81--84% system-wide free memory, zero swap and no competing
proof process. No limits were raised. Source and accepted log hashes:

| Source basename | Accepted log under /tmp | Gates | Source SHA-256 | Log SHA-256 |
| --- | --- | ---: | --- | --- |
| `BF4WilsonSmallNomeBentSignedLimit.lean` | `ym-bent-signed-limit-20261003-a.log` | 6 | `3674ca255adc1a6235386a95337b260ff0d03992691135ceea90ef052f19e1b6` | `c300dc2b84f3b60459d938974836b84ec4fda388687bdb8e494af8940b66e15d` |
| `BF4WilsonSmallNomeBentSignedOrbit.lean` | `ym-bent-signed-orbit-20261003-b.log` | 10 | `f504cf50ccc63c3571c04f1c5082c084ffc6989083f3595f9c0749df8fbcd682` | `4cd27a3cd3f53b62419acc2a3601eb529be3ace916025d2481bfbd1b373ff7a4` |
| `BF4WilsonAllNomeGainStrengthConstraint.lean` | `ym-gain-strength-constraint-20261003-a.log` | 4 | `014f6902b5cf1724bb102aa7e77e8def25ffc1fcc6dbb1cf6326dccee0f8fd6c` | `84649525ba21c929f0d8f86e537f95c187b8b18311c5bb334980af4bcb98a4de` |

Among Lean source files, only new proof modules and root import registrations
were changed; the live documentation was updated alongside them. The
aggregate root, full-tree build, broad audit/guard and progress metric were
NOT run. No sorry, axiom, classical shortcut or resource option was added.
CI stays off. The first canonical chart fence remains unchanged, SHA-256
`0d9295165945a8acea2c4037bd951f9060a1dfcc22448bde4462d0c795b12145`.
No exact displayed scaling claim closed, so no ASCII chart is reprinted.

Independent Sol mathematical/source reviews passed the completed OWN-center
gain join, ratio/time propagation and necessary strength constraint. Their
source reviews are distinguished from the three accepted kernel checks.
Independent Luna evidence/documentation QA passed the six hashes, 20 gate
outputs, declaration anchors, three imports, fixed-parameter boundary and
unchanged first chart fence; its documentation-scope wording was corrected.
