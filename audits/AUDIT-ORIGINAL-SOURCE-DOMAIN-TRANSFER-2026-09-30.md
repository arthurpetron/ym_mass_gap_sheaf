# Original source energy controls entry into the derivative domain

Date: 2026-09-30 UTC. Classification: PROGRESS. This milestone proves
unconditional original-operator comparisons, a conditional quantitative
source-to-domain transfer, and an actual boundary recovery obstruction.
It does not supply the missing signed scaling estimate or close a Clay node.

## One signed budget serves both source survival and the derivative form

On the original completion write T for the one-step transfer, B for its
actual pairing, E(x)=B(x,(I-T)x), and A for the constructed derivative on
preimages. The existing core domain point is exactly (Tx,Ax); A is not
being declared a bounded Hamiltonian on arbitrary inputs x.

The following inequalities are now proved for EVERY original completed x,
without a smallness or source-energy premise:

    B(Tx,Ax) + B(Tx,Tx) <= B(x,Tx)
    B(Tx,Ax) <= E(x)
    B(x,x) <= B(Tx,Tx) + 2 E(x)
    ||Tx-x||^2 <= E(x).

The first inequality uses the actual dyadic quotient Q_k=m(I-R_k)Tx,
m=2^k. Apply the positive mixed-moment terminal bound at k=m, n=m, l=0:
m*moment(2m,1)+moment(2m,0)<=moment(m,0). The original root square law
and full-unit-time pin identify this as
B(Tx,Q_k x)+B(Tx,Tx)<=B(x,Tx). The computed pairing modulus passes the
inequality to Ax. The nonnegative squared norm of x-Tx gives both the
norm-retention inequality and the remaining derivative upper bound.
The positive split E(x)=B(x,T(I-T)x)+||(I-T)x||^2 gives the distance bound.
There is no spectral theorem, inverse transfer or log-series identification.

Consequently, a SUPPLIED original relative estimate

    E(x) <= c B(x,x),    c >= 0,    r=1-2c > 0

gives ||Tx-x||^2<=c B(x,x), B(Tx,Tx)>=r B(x,x), and

    B(Tx,Ax) <= (c/r) B(Tx,Tx).

An original positive squared-norm floor b becomes the explicit positive
floor r*b. A supplied vacuum-orthogonality condition is preserved. These
claims apply to the already constructed `corePoint` of the original source
representative, not a new operator or independently assumed domain state.
Each application stays at one nome and width; this is not spatial transport.

This joins a future SAME-source signed budget to the derivative-domain
branch without requiring a separately proved nontrivial domain state.
It does NOT prove that budget. In particular, no actual nonzero
vacuum-complement scaling family with c=M*tau is constructed here. The
existing fixed-parameter floors do not by themselves supply c<1/2 or a
uniform physical mass. No further equivalent conditional wrapper is needed
before returning to the analytic estimate.

## Why arbitrary time-zero recovery is not available

Positive real time commutes with the original T(1), preserves zero, and
constructs a range witness for its output. Thus Tx=0 implies S(t)x=0 for
every strictly positive represented real t: the output lies in both the
witnessed range and the time kernel, whose intersection is zero.

For the width-one centered origin plaquette v, the centered vacuum-created
insertion is therefore zero at EVERY positive real time, but B(v,v) has
the existing positive lower floor starRatio(w). Its squared-distance error
from v equals B(v,v), independently of t. The explicit separation
certificate rules out recovery by ANY positive-time schedule with an
all-tail convergence modulus, even a schedule tending to zero.

This refutes equal-time recovery of that boundary source, not recovery of
low-energy bulk sources or a controlled spatial/scaling limit. The
unconditional error and norm comparisons above expose the relevant
distinction quantitatively. Original finite-window generation and
reflection positivity remain valid on their existing carrier.

## Checked source map

| Declaration | Source | Role |
|---|---|---|
| `positiveAction_zero`, `positiveAction_time_one_commutes`, `positiveAction_kills_time_kernel` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorEqualTimeBoundary.lean:57`, `:63`, `:71` | General original positive-time kernel annihilation. |
| `origin_centeredSource_zero`, `origin_recovery_error`, `origin_recovery_floor` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorEqualTimeBoundary.lean:81`, `:86`, `:90` | Exact boundary source and time-independent separation. |
| `originSeparationCertificate`, `no_origin_recovery` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorEqualTimeBoundary.lean:98`, `:106` | Positive rational witness and exclusion of any recovery modulus. |
| `finite_terminal_energy`, `derivative_terminal_energy` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorSmoothingEnergy.lean:113`, `:138` | Actual dyadic bound and its original derivative limit. |
| `norm_retention`, `derivative_core_upper` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorSmoothingEnergy.lean:183`, `:200` | Unconditional same-source comparisons. |
| `retainedFraction`, `energyRatio`, `energyRatio_nonnegative` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorSourceTransfer.lean:51`, `:53`, `:56` | Explicit r and c/r, with scalar guards. |
| `smoothing_distance_le_energy`, `relative_source_error` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorSourceTransfer.lean:79`, `:97` | Replacement error paid by original energy. |
| `relative_norm_retention`, `relative_derivative_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorSourceTransfer.lean:104`, `:116` | Conditional quantitative same-source transfer. |
| `corePoint_relative_bound`, `corePoint_norm_floor`, `transferredFloor_positive`, `corePoint_orthogonal` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorSourceTransfer.lean:130`, `:140`, `:149`, `:154` | Actual represented domain point, not an independent existence premise. |

## Next causal frontier and verification

Return to the actual signed comparison E_j(x_j)<=M*tau_j*B_j(x_j,x_j)
for ONE justified original source/scaling family, retaining every signed
cross term and its interacting normalization. The present transfer provides
its derivative-domain consumer and source-replacement error, not that
estimate. The compatible physical reflected observable/complex Hilbert
join, spatial and spacing control, physical time calibration, nontrivial
continuum theory, full QFT and every compact simple group remain OPEN.

Three final focused serialized checks passed 23 printed gates (8 boundary,
4 smoothing energy, 11 source transfer). Every gate is axiom-free or within
{propext, Quot.sound}; no sorryAx or classical dependency remains. Main
corrected draft notation/namespace and definitional rewrites, without
weakening any theorem. Sol drafted the smoothing argument; main checked
its finite indexing, wrote the boundary and source/error transfer, and
owned compilation. Luna independently reviewed the rational constants,
original core-point identification and conditional scope.

The safe-build skill kept all verification targeted, one worker with a
20 GiB hard ceiling and 12 GiB OS reserve, after live process/memory
inspection. Automatic telemetry remained enabled. No safety stop, limit
increase, concurrent compiler, full root/tree build, broad audit/guard,
new sorry/axiom or canonical frontier change. Root imports are registration,
not root verification. The canonical chart is unchanged and not reprinted.

Final logs and SHA-256:

- `/tmp/ym-wilson-sector-equal-time-boundary-20260930.log`:
  `4ddedf3ad373c3e1a9a5ae149ce5919dc9496fbd8b350d3755dcabac2887daa0`
- `/tmp/ym-wilson-sector-smoothing-energy-20260930.log`:
  `1feefe769b2b1d0635364509ef6e7230a381654c81abe96ccdac00aba42695c3`
- `/tmp/ym-wilson-sector-source-transfer-20260930.log`:
  `40ef533986b73b15d2efd6b88213da7d7f71f8a57d8b44dc9c25928afd5a8f2a`
