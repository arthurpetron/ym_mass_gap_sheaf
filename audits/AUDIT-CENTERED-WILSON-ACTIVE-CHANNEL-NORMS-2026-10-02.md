# Active channel norms for the original centered Wilson square

## Result and scope

The active-footprint cubic estimate now reaches the original growing Wilson
square centered at its OWN interacting mean. A constructed Gram-and-square
certificate retains the literal Casimir square without requiring the
centered observable to be a Casimir eigenvector. The signed curvature,
complete angular weight defect and original Ward term remain under the SAME
partition. This supplies a finite energy ceiling, not its useful smallness
relative to OWN variance along a changing physical family.

Let f be the fundamental character of `paddedSquare scale width hwidth`,
q the original projected endpoint source at terminal depth n, psi=f-OWNmean,
Z=oddMass at that SAME depth, and V=oddVariance. Let A be its actual loop
footprint, H the original product Haar functional, h=1-w, t=h^2/2 and
rho=w^((K+1)*(K+3)). The already constructed active budget is

    S3_A(p) = H[(C_A p)(C_A^2 p)].
    D_A = h^3/6 * [(S3_A(q)+S3_A(q*psi^2))/2+S3_A(q*psi)]
          + rho * [(H[q^2]+H[(q*psi^2)^2])/2+H[(q*psi)^2]].

For the actual passive Gram channels b_c, including their original weights,
define

    R = sum_c weight_c * H[b_c^2 * Cfull Gamma(psi,psi)],
    S = sum_c weight_c * H[(b_c * Cfull psi)^2],
    d = angularWeightDefect(psi) = marginalAngular(psi)-rawAngular(q,psi),
    D = D_A-(h+t)*d+t*(-R-S/3).

At 0<w<1, headCutoff(w)<=K and side(scale)<width, for every terminal depth n,
the original normalized energy satisfies

    E_original(f)/Z <= (h+t)*12*side(scale)*V
                       -(h+t)*OWNWard(f)+D/Z.

No `sufficientCutoff` guard is required. No channel has a separately chosen
mean, normalization or positive-source assumption. The negative square uses
`Cfull psi` literally: the code does NOT substitute `12*side*psi` for it.

## Constructed argument

For arbitrary supported signed q and f, put v=q*C f, x=Gamma(q,f),
y=Gamma(q,q), g=Gamma(f,f), b=v-2x and s=v-3x. The exact identity

    3*(b^2+2*y*g-v^2/3) = 2*s^2+6*(y*g-x^2)

combines the existing angular Gram certificate with a constructed square.
Haar positivity gives H[b^2]+2H[y*g]>=H[(q*C f)^2]/3. In the original
second-moment identity this yields

    sourceSecondMoment <= -H[q^2*C Gamma(f,f)]-H[(q*C f)^2]/3.

Expand the ACTUAL full energy into passive Gram channels FIRST. Apply this
bound and the previously proved cubic Sobolev cap in each channel. The
coefficient-one angular and active third-moment/Haar contractions then give

    E_source <= (h+t)*rawAngular+t*(-R-S/3)+D_A.

The actual Wilson consumer constructs the original supported source and
passive/fringe independence pins. `energy_shifted` transfers this estimate
from psi back to f. `angular_weight_identity` and `marginalAngular_shifted`
rebase raw angular energy to the original marginal, explaining the NEGATIVE
coefficient of d. Divide only by the original positive Z, then use the
existing Ward identity for the ORIGINAL f, not a centered eigenpin.

## Source declarations

| Declaration | Source | Verified content |
| --- | --- | --- |
| `oneThird` | `lean/YMGap/Continuum/SU2QuaternionGeneralRetainedCasimir.lean:38` | Explicit rational fraction |
| `generalRetainedCasimirCertificate` | `lean/YMGap/Continuum/SU2QuaternionGeneralRetainedCasimir.lean:47` | Type-level Gram-and-square witness |
| `general_retained_casimir_bound` | `lean/YMGap/Continuum/SU2QuaternionGeneralRetainedCasimir.lean:117` | Arbitrary signed supported q,f; no eigenpin |
| `sourceSecondMoment_le_retainedCasimir` | `lean/YMGap/Continuum/SU2QuaternionGeneralRetainedCasimir.lean:149` | Signed curvature and literal negative square |
| `channelCurvature` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelRetainedCasimirSobolev.lean:46` | Actual signed channel sum R |
| `channelCasimirSquare` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelRetainedCasimirSobolev.lean:55` | Actual literal channel sum S |
| `sourceEnergy_le_sobolev_retainedCasimir` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelRetainedCasimirSobolev.lean:63` | Per-source finite ceiling |
| `sourceEnergy_le_activeSobolev_retainedCasimir` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelRetainedCasimirSobolev.lean:145` | Exact channel decomposition followed by active contractions |
| `activeChannelSobolevBudget` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareActiveChannelSobolev.lean:96` | Original q, OWN psi and actual active footprint |
| `activeChannelCurvature` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareActiveChannelSobolev.lean:101` | Original R instance |
| `activeChannelCasimirSquare` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareActiveChannelSobolev.lean:106` | Original S instance |
| `activeChannelCenteredDebt` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareActiveChannelSobolev.lean:112` | Complete signed numerator D |
| `normalizedActiveChannelCenteredDebt` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareActiveChannelSobolev.lean:121` | SAME original D/Z |
| `paddedSquare_energy_activeChannel_marginal_bound` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareActiveChannelSobolev.lean:130` | Original unnormalized energy consumer |
| `paddedSquare_energy_activeChannel_sobolev_bound` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareActiveChannelSobolev.lean:195` | Original OWN-variance/Ward ceiling above |

The existing active budget is defined by
`SU2QuaternionPassiveChannelSobolevError.activeSourceSobolevErrorBudget`
at `lean/YMGap/Continuum/SU2QuaternionPassiveChannelSobolevError.lean:110`.
The earlier Casimir-12 plaquette-family result and global projection-gain
route are unchanged. No equality between that global gain and S, numerical
ordering of old/new ceilings, or global cubic-weight substitution is asserted.

## Remaining input

OPEN: useful joint control of D/Z and the original Ward term relative to
OWN variance on a physically justified changing family. The retained signed
curvature has no favorable sign asserted; the raw active norms still depend
on nome, width, cutoff, terminal depth and the growing observable. Removing
passive derivatives and a centered eigenpin does not prove useful spacing
or volume uniformity. Nonzero continuum survival, physical mass calibration,
full same-theory QFT axioms, every actual compact simple group and the Clay
target remain OPEN. No exact canonical chart claim changes.

The requested-paper review identifies methods, not a producer for this
estimate: `RESEARCH-REQUESTED-FIFTEEN-PAPERS-2026-10-02.md`.

## Verification boundary

Three focused checks passed with 4+4+7 printed gates. `oneThird` is
axiom-free; the other fourteen gates use only {propext,Quot.sound}.
The accepted logs below contain no error or warning. Draft elaboration
checks were rejected; explicit rational clearing, a pattern-lambda layout
and unfolding local normalization definitions fixed those issues without
changing the mathematical bound or raising limits. Failed logs are not
proof evidence.

Independent Sol mathematical source review passed: actual channel
decomposition, coefficient-one contractions, OWN centering, signed angular
defect, original Ward pin and SAME partition. Independent Luna evidence
review verified source/log hashes, declaration anchors, gate outputs,
documentation scope, the single root import, whitespace checks and exact
chart fenced blocks against HEAD.

Checks used `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20`, serialized, with a 12-GiB OS reserve. Fresh
capacity checks found no competing Lean/Lake/runner/pytest and zero swap.
No new sorry, axiom, analytic premise or weakened frontier was introduced.
One downstream root import includes the three modules. No root/full-tree
build, broad audit, guard or progress script was run; the automatic axiom
baseline was not regenerated. CI remains manual-only and canonical chart
fenced blocks are unchanged.

## Source and accepted log hashes

| Artifact | SHA256 |
| --- | --- |
| `SU2QuaternionGeneralRetainedCasimir.lean` | `f991a738013583d7d362b6e0c452880f9258fdd19896865815096220fde8e29a` |
| `SU2QuaternionPassiveChannelRetainedCasimirSobolev.lean` | `764b88fd414126136cfece7a33823dcc1a5b8b56fc712c2ead8de16d002b4b00` |
| `BF4DyadicWilsonSquareActiveChannelSobolev.lean` | `644bfde09ab275badeb92b98096468ff3315db7fb9f69e7a1662047cb20eded5` |
| `/tmp/ym-general-retained-casimir-20261002-second.log` | `18e29bc06968cb0d5857b32ce61bc1b7f798b8e22a218bf025c9ae5353423812` |
| `/tmp/ym-channel-retained-casimir-sobolev-20261002-second.log` | `34f37bfe70fa678157435646a5c1651d09fbecb7f1d4e0cca46ff689ece25be1` |
| `/tmp/ym-dyadic-active-channel-sobolev-20261002-third.log` | `4a172f8441ede906c91ece5d933b343a1017bcbba064ce3c83c2e8b1e5cd6ea1` |
