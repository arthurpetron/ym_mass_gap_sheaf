# Computed logarithm-prefix coercivity on the original domain

The whole-project goal remains nontrivial continuum Yang--Mills on R^4 for
every compact simple group, with SAME-theory QFT axioms and a finite positive
physical mass gap. This increment strengthens a fixed-parameter original
SU(2) domain form; it does not close the physical or scaling frontier.

## New mathematical join

Use the EXISTING original completion, transfer T, vacuum and domain point
p=(x,y). Put D=I-T and r=mixFraction(w,width)=kineticFloor/kineticCap.
For x orthogonal to that vacuum, the now checked results give

    r*B(x,D^k x) <= B(x,D^(k+1) x),
    r^k*B(x,x) <= B(x,D^k x),
    gamma_N*B(x,x) <= B(x,U_N x) <= B(x,y),

where U_N x=sum_(j=1..N) D^j x/j and the computed rational function is
gamma_N=sum_(j=1..N) r^j/j. Already gamma_2=r+r^2/2>r.
There is no positive norm cancellation, scalar logarithm identification,
spectral measure, inverse transfer or new comparison hypothesis.

The moment step retains the nonnegative square ||(D-rI)z||^2 in its odd
case; even powers use the actual one-step floor. Defect powers preserve the
original vacuum complement. The upper form bound uses positive mixed moments,
the EXISTING domain logarithm modulus and completed pairing continuity.
Its rational norm caps come from representatives computed by the supplied
input/output range witnesses, not selection from arbitrary quotient classes.

## Source anchors

All paths have prefix `lean/YMGap/Continuum/`.

| Declaration | File:line | Role |
|---|---|---|
| `unregularizedLogPartial_form_step` | `BF4WilsonAllNomeDomainLogForm.lean:64` | Finite form monotonicity from actual positive moments. |
| `unregularizedLogPartial_form_mono` | `BF4WilsonAllNomeDomainLogForm.lean:73` | Arbitrary finite cutoff order. |
| `domain_logPartial_form_le` | `BF4WilsonAllNomeDomainLogForm.lean:125` | Every prefix is bounded by the actual domain output pairing. |
| `defectPower_vacuum_orthogonal` | `BF4WilsonAllNomeDefectMomentGap.lean:93` | Same vacuum complement at every power. |
| `defect_moment_step_gap` | `BF4WilsonAllNomeDefectMomentGap.lean:158` | Adjacent moment coercivity without spectral calculus. |
| `defect_moment_geometric_lower` | `BF4WilsonAllNomeDefectMomentGap.lean:172` | Actual r^k norm floor. |
| `prefixGap` | `BF4WilsonAllNomeDomainLogPrefixGap.lean:72` | Rational finite coefficient returned as data. |
| `finite_log_prefix_gap` | `BF4WilsonAllNomeDomainLogPrefixGap.lean:77` | Finite sum lower bound on the SAME carrier. |
| `domain_log_prefix_gap` | `BF4WilsonAllNomeDomainLogPrefixGap.lean:97` | Join to the existing domain action for every N. |
| `prefixGap_two` | `BF4WilsonAllNomeDomainLogPrefixGap.lean:105` | Exact rational two-term coefficient. |
| `two_term_coefficient_strict` | `BF4WilsonAllNomeDomainLogPrefixGap.lean:115` | Strict scalar improvement over r. |
| `domain_log_two_term_gap` | `BF4WilsonAllNomeDomainLogPrefixGap.lean:121` | Explicit strengthened original domain form. |

## Verification boundary

Three serialized focused checks exited zero under the monitored launcher:
one worker, 20 GiB cap and 12 GiB OS reserve. The accepted logs report twelve
gates, all within {propext, Quot.sound}, with no error, warning, sorryAx or
PANIC. No resource or heartbeat limit was raised. The initial form-proof
timeout was resolved by splitting the cap and limit arguments and preventing
unnecessary cap/representative unfolding, without weakening any statement.

| Target | Accepted log in /tmp | Gates |
|---|---|---|
| `BF4WilsonAllNomeDomainLogForm.lean` | `ym-original-domain-log-form-20261003-d.log` | 3 |
| `BF4WilsonAllNomeDefectMomentGap.lean` | `ym-original-defect-moment-gap-20261003-a.log` | 3 |
| `BF4WilsonAllNomeDomainLogPrefixGap.lean` | `ym-original-domain-log-prefix-gap-20261003-a.log` | 6 |

Source SHA256, in table order:

    04ac250c4849d3961b0bc75192681c3af1174cb862579529e61dd57813fd7ef4
    0d144736c15a9c09e8155008d211547a265aa698a02a72a27e8e9607994751e8
    be64414ae53c31135ce9131586758096d103a706b957ee1a290c0197c3663169

Accepted-log SHA256, in table order:

    e557e11224088decb1ea3e6a67efb298ea96f543f540f67be8beeeebbc19aec4
    17c756f8b044b0f06be723696db0533445ee94cf0bce3a0b002f2df3f091f1e1
    a7ee9e397d58981eaedb6a97de943215b42041887daf41784cf45f5d3ac5f917

Root imports are registration-only, not an aggregate check. No full build,
audit, guard or progress metric ran. No sorry was added/discharged, no new
axiom or frontier weakening, and no CI or exact displayed chart change.

## Actual consumer and remaining frontier

The consumer is the SAME previously constructed derivative-domain action,
now characterized by its ordinary transfer logarithm, not a hypothesized
Hamiltonian. The coefficient retains nome and spatial-width dependence.
The all-prefix statement does not require r<1 or a scalar infinite-series
limit. No pin to the separate CRealLog implementation is supplied.

The ORIGINAL complete signed cost relative to its SAME filtered norm on a
JUSTIFIED changing family remains unpaid. A positive total conditional-noise
certificate does not produce that relative estimate: its exact loss is
endpoint variance minus filtered norm. Canonical reflected OS realization,
spatial/spacing control, physical calibration, nontrivial continuum survival,
full QFT, every group and Clay remain OPEN. The active goal continues there.
