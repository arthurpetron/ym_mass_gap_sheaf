# Whole signed-family temporal join and narrowed survival search

Date: 2026-09-30 UTC. Classification: PROGRESS, exact same-object identities
and transfer of an existing lower bound. Whole-project Clay target OPEN.

## Mathematical step back

The original signed-family variance floor is already present on the literal
Wilson completion in `familyExcitation_norm_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyVariance.lean:151`.
The original family-energy estimate `family_energy_floor`, in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy.lean:174`,
is also a LOWER bound. Two lower bounds cannot yield an upper energy/variance
ratio. The new work closes the exact temporal join, not that analytic estimate.

For a radius-zero signed expression F and its existing centered vector v,
the proved identity is

    E_original[(F_0-F_n)^2] = 2*(B(v,v)-B(v,T^n v)).

It is not ||v-T^n v||^2. In particular, the finite one-step expression uses
the original odd-chain partition already built by `normalizedEnergy_window`,
not an independently chosen stationary measure or a heat-bath dynamics.

## Checked declarations

| Declaration | Source | Content |
| --- | --- | --- |
| `pair_lag` | `lean/YMGap/Continuum/BF4WilsonAllNomeZeroRadiusIncrement.lean:110` | Original stationarity/padding for arbitrary signed radius-zero syntax. |
| `increment_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeZeroRadiusIncrement.lean:133` | Full squared-increment polarization before any absolute bound. |
| `time_pairing_lag` | `lean/YMGap/Continuum/BF4WilsonAllNomeZeroRadiusIncrement.lean:168` | Reflection and original lag use the same source. |
| `increment_reflected_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeZeroRadiusIncrement.lean:187` | Exact twice-reflected-loss identity, every natural lag including zero. |
| `source_family_shift` | `lean/YMGap/Continuum/BF4WilsonPlaquetteFamilyIncrement.lean:70` | Whole signed spatial family is shifted coefficientwise, including empty/repeated lists. |
| `source_difference_family` | `lean/YMGap/Continuum/BF4WilsonPlaquetteFamilyIncrement.lean:96` | Original source difference equals the existing spatial jump. |
| `source_square_family` | `lean/YMGap/Continuum/BF4WilsonPlaquetteFamilyIncrement.lean:107` | Complete square retains every signed cross term. |
| `finite_family_increment_pin` | `lean/YMGap/Continuum/BF4WilsonPlaquetteFamilyIncrement.lean:121` | Finite original ratio equals twice original normalized energy. |
| `finite_family_increment_floor` | `lean/YMGap/Continuum/BF4WilsonPlaquetteFamilyIncrement.lean:137` | Existing energy lower bound, with positive denominator canceled explicitly. |
| `family_increment_floor` | `lean/YMGap/Continuum/BF4WilsonPlaquetteFamilyIncrement.lean:162` | Lower bound passes through the existing diagonal joint limit. |
| `family_increment_completed_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyEnergy.lean:49` | Exact pin to the existing completed family vector and time operator. |
| `family_temporalEnergy_floor` | `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyEnergy.lean:61` | Completed one-step energy >= varianceFloor(w)*sum c_p^2 for distinct physical faces. |

The identities require no distinctness hypothesis. The lower floor requires
the original physical membership and `Nodup` hypotheses. Its coefficient is
unchanged: lower(w)/(600*upper(w)), independent of width, family size and late
cutoff at each fixed strict nome, NOT independent of nome or physical spacing.
No whole-carrier isometry, change of action or new analytic input is assumed.

## Next proposition, not an additional scaffold

For the survival branch, seek ONE explicitly chosen source family v_j with
nonzero norm and a bound

    B_j(v_j,(I-T_j)v_j) <= M*tau_j*B_j(v_j,v_j)

on a justified spatial/spacing trajectory. The physical time tau_j must match
the actual T_j, and M must be explicit and finite. A proof for every signed
coefficient vector would be stronger than needed for this branch. The separate
every-state decay/gap branch still requires its appropriate uniform estimate.
One finite successful test would not prove a bound along the scaling family.

Consumers already exist: `BF4WilsonAllNomeResponseLower.response_step_lower`,
`lean/YMGap/Continuum/BF4WilsonAllNomeResponseLower.lean:102`, propagates a
supplied same-state Rayleigh floor; the specialized conditional consumer
`dyadic_response_ge_fraction_of_relative_energy`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRelativeSurvival.lean:110`,
uses a same-source relative energy bound. Their missing estimates are not
supplied by the identities above. This checkpoint adds no new conditional
consumer or frontier bundle.

## Averaging diagnostic (paper-level, not a Lean result)

The existing `orbitSum` and `orbitSum_pairing`,
`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:166` and `:195`,
already construct polynomial filters of the actual completed time operator.
For y_N=sum_(k<N) T^k x, telescoping gives (I-T)y_N=x-T^N x, but does not
supply a lower bound on ||y_N||. On the elementary positive contraction
T=rho*I, 0<rho<1, every nonzero polynomial-filtered vector retains relative
loss 1-rho. Filtering cannot create spectral support near one.

This is a diagnostic of a proposed general implication, not a counterexample
to the Yang--Mills carrier and not a new kernel-checked obstruction. Existing
strictly positive fixed-nome response floors alone do not establish the
scaling-relative estimate. Do not extend a filtering branch without a genuine
same-source norm/response estimate that repairs this gap.

## Follow-on source review: actual upper bound and the locality limitation

This section is source review and mathematical proof planning, NOT a new
kernel-checked upper estimate or Yang--Mills counterexample.

An original one-loop upper estimate is already proved:
`joint_increment_nome_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomeKineticIncrement.lean:168`, bounds
the joint one-step increment by 24*length^2*(1-w), for active source edges.
`timeIncrement_nome_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeIncrement.lean:120`, gives the
corresponding n-step upper bound with factor n. These preserve the SAME
original joint state; the missing input is not an absolute one-loop upper
bound. The current family variance floor does not provide the useful
changing-nome relative normalization needed for survival.

The finite mechanism is explicit. `alignment_cleared`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKineticAlignment.lean:57`,
retains the full original partition and gives a one-link alignment bound.
`link_displacement_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonKineticIncrement.lean:90`,
turns it into a squared coordinate displacement cost. `word_increment_bound`
in the same file at line 178 applies the deterministic word telescope and
finite square inequality, producing the squared path length. This does not
control the original family's signed off-diagonal displacement terms.

`product_alignment`,
`lean/YMGap/Continuum/SU2QuaternionHeatFusionQuadratic.lean:184`, accepts a
supported certified endpoint a, retaining a(x)*a(y). Its proof does not
allow an arbitrary signed two-copy insertion. Replacing a by a*s changes
both the insertion and the mass; it does not keep the original partition
while supplying a displacement-covariance estimate. The actual edge law
also contains the spatial factors and terminal messages. Local source
incidence therefore does not itself imply independence or orthogonality of
increments on disjoint faces.

The needed estimate remains a same-action comparison of the full signed
displacement Gram with the actual centered covariance Gram for ONE useful
source family. One stronger sufficient route would be a row-summable
displacement-Gram bound at useful nome dependence, followed by a compatible
variance estimate. Neither bound is supplied by local overlap counting or
the preceding one-link theorem. No new conditional wrapper is added, and
even an absolute l2 family upper bound would not alone repair the current
variance-floor/calibration cost. The direct signed comparison remains the
primary target; time-filtering and incidence arguments cannot be recorded
as its discharge without those missing estimates.

## Verification boundary

The three new modules passed serialized focused checks via the monitored
launcher: one worker, 20 GiB worker ceiling, 12 GiB OS reserve. All 17 printed
gates are axiom-free or within {propext, Quot.sound}; no `sorryAx`, classical
choice, new axiom or `sorry` occurs. Sol independently reviewed the analytic
filtering issue; Luna reviewed the source/normalization/completed joins.
No full root build, full-tree audit or guard was run; root imports were added.

Final check logs and SHA-256:

- `/tmp/ym-BF4WilsonAllNomeZeroRadiusIncrement-20260930.log`:
  `1b715ffff410151bf979e86a37de1a33affc12285d5909cd731bde081141d997`
- `/tmp/ym-BF4WilsonPlaquetteFamilyIncrement-20260930.log`:
  `92456511038e0cb4154006e3b9758b3f73faa4b7abf2ee6945b367489bdd6df9`
- `/tmp/ym-BF4WilsonAllNomePlaquetteFamilyEnergy-20260930.log`:
  `526c70755de82506535ccaffde8c681e08a2898f3e86b643e7bc6262bf8e0613`

Relative upper control, scaling survival, every-state scaling decay, continuum
QFT and the physical Clay gap remain OPEN. No canonical chart field changed,
so the chart is not reprinted.
