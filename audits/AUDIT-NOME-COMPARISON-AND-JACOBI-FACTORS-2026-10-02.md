# Original response comparison and Jacobi factor estimates

Date: 2026-10-02 UTC. This increment supplies a comparison of the original
normalized response at two couplings with fixed loop geometry, and two new
quantitative estimates for the original Jacobi factors. It does not supply
cross-scale convergence, a full heat-widening certificate or continuum
survival. The Clay target remains OPEN.

## Original normalized response comparison

For the SAME padded square, width and integer lag, write J_w(j) for its
original joint moment, mu_w for its OWN original mean, V_w=J_w(0)-mu_w^2,
and R_w(j) for the existing norm-one excitation's original time response.
The exact cancellation is

    V_u*(R_v-R_u)
      = (J_v(j)-J_u(j)) - R_v*(J_v(0)-J_u(0))
        - (1-R_v)*(mu_v^2-mu_u^2).

`dyadicUnitResponse_nome_cancellation`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNomeComparison.lean:292`, proves
this equality of pinned CReal scalars. Both completions and means remain
original; no cross-carrier identification is made. The shared mean-square
correction is paid once, not separately for the two centered moments.

For each of the three literal expressions, `momentCost` at
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNomeComparison.lean:200` computes

    d_e = tau + finiteWindowCap(W,u,v,L,e,comparisonDepth(e,tau)+1) + tau.

`momentCost_bound` at line 206 reuses the EXISTING producer
`joint_coupling_tolerance_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeCoupling.lean:158`.
This increment does not introduce another raw-moment or pivot producer.
The native horizons are j, 0 and 0. The finite face cost is explicitly
`ids.length*(2*windowCap(e)*relativeVariation(W,u,v))`, by `finiteSetCap`,
`lean/YMGap/Continuum/BF4ExactSlabTwoNomeExpectationBound.lean:48`.

The actual unit response satisfies 0<=R_v<=1. The existing coarse singleton
mean cap is 32; the positive original norm floor is starRatio(u). Consequently
`dyadicUnitResponse_nome_difference_bound` at
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNomeComparison.lean:315` constructs

    abs(R_v(j)-R_u(j)) <= (d_j+d_0+64*d_mean)/starRatio(u).

No moment or response comparison is supplied as a hypothesis. The parameters
satisfy 0<u<=v<=W<1 and tau>0. Every loop scale, width, lag, nome, finite
pivot and face-count dependence remains explicit. This pays a fixed-geometry
coupling leg of the current scalar samples. A small cost along a justified
changing family and the geometry/width leg are NOT constructed.

## Quantitative original Jacobi factors

Let F(a,x)=1+2*a*x+a^2, exactly `HKPos.factor`, and let S_q(N) be exactly
`HKConv.Spart q x N`. The following are NEW estimates, not assumed kernel
shape bounds.

| Declaration | Source | Proved scope |
| --- | --- | --- |
| `sTerm_pair_bound` | `lean/YMGap/Continuum/SU2HeatJacobiNomeWidening.lean:194` | q times two consecutive original summands is at most (4+q) times the matching squared-nome summand. |
| `Spart_nome_widening` | `lean/YMGap/Continuum/SU2HeatJacobiNomeWidening.lean:246` | q*S_q(2N)<=(4+q)*S_(q*q)(N), for ALL 0<q<1, x>=-1 and N, including x=-1 and N=0. |
| `factor_squared_nome_order` | `lean/YMGap/Continuum/SU2HeatJacobiProductWidening.lean:65` | F(a,x)*F(a*a,1)<=F(a,1)*F(a*a,x), for a>=0 and x<=1. |
| `factor_squared_nome_block` | `lean/YMGap/Continuum/SU2HeatJacobiProductWidening.lean:114` | The left product times (512+1-x) is at most 512 times the right product, for 1/4<=a<=3/4 and x<=1. |

The S proof pairs the literal amplitudes q^(4n+1), q^(4n+3) against
q^(4n+2). Clearing the leading nome avoids a reciprocal nome or heat
minimum. Increasing the amplitude increases its quotient; the intervening
factor obeys F(a*q,x)<=4*F(a,x) for a<=q and x>=-1.

The exact cross-product difference is gain(a)*(1-x), where
gain(a)=2*a*(1-a)^2*(1+a+a^2). On the named amplitude block, gain>=1/32
and F(a,1)*F(a*a,1)<=16. The quantitative block inequality has slack

    [512*gain - F(a,1)*F(a*a,1)]*(1-x)
      + 2*a*F(a*a,1)*(1-x)^2 >= 0.

The normalized factor INCREASES under nome squaring; the displayed
inequalities retain that direction. Both class endpoints are covered when
the two modules are used together on [-1,1]. No hidden near-one constant,
source independence or sign of the original centered source is assumed.

## Remaining causal work

The heat route still needs an explicit count of retained amplitude-block
factors, their product amplification, a controlled theta-height comparison
and the original limit joins. Even a pointwise heat inequality is not an
original Haar `Certificate`: its algebraic witness and cutoff error must
be constructed. The downstream consumer is `affine_original_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialHeatNomeComparison.lean:135`;
its shape-certificate hypothesis is still unsupplied.

That consumer would bound a selected quartic mass of the actual positive
terminal source. It does not apply directly to a SIGNED centered endpoint
source. Whole-word cross-link cancellation and alignment relative to OWN
interacting variance remain separate analytic inputs. None of the new
factor bounds is a completed transfer gap or a physical mass bound.

Full same-theory continuum OS/QFT structure, an acceptable surviving
Yang--Mills field, physical mass calibration and every compact simple group
remain OPEN. No displayed canonical chart claim changes.

## Verification

Three final focused checks passed, serialized through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check ...`.
All 11 public gates are within {propext, Quot.sound}; the final logs contain
no errors, warnings or sorryAx. Dynamic preflights found no competing jobs,
84--85 percent pressure-free memory and zero swap. Limits and the 12-GiB OS
reserve were not changed. No full root/tree build, broad axiom audit, guard
or progress-metric run was performed; three root imports were registered.

The accepted logs are `/tmp/ym-dyadic-nome-comparison-20261002-second.log`,
`/tmp/ym-jacobi-nome-widening-20261002-second.log` and
`/tmp/ym-jacobi-product-widening-20261002-final.log`. Earlier rejected checks
had elaboration/namespace errors; none is accepted as evidence. The product
docstring direction was corrected and the final source rechecked.

| Artifact | SHA256 |
| --- | --- |
| `BF4WilsonAllNomeDyadicNomeComparison.lean` | `9800b6bcef2dc6ad1bf1d4d530a507a4f5e98c01148e183afb343fe9417c6ddb` |
| `SU2HeatJacobiNomeWidening.lean` | `0abc30f76c40b149eb43107de0e7f72bebbb7da182afb0bb270d00bfbc3b278a` |
| `SU2HeatJacobiProductWidening.lean` | `8e0dc2ebfff3dfd1ed02b8dbb11b45e7dcff15734f7f1d919f1e67b36451fc0c` |
| Response log | `6f285c26de167f8734de223c7ae905fa283a346848baf9b093bc5fa84dd18945` |
| S factor log | `1482debb10dcfb2ecadbfae93de35580bf4fb5316ea464e3de1fd4e82809ca0f` |
| Product factor log | `190275bc35931f88a4152276c945b7e36d1f37c661a64f9953ef8edc8ccf71b8` |

Independent mathematical review passed both proof branches. A separate
documentation review checked source lines and corrected the cross-product
difference wording. No new axiom, classical input, sorry, assumed analytic estimate,
canonical-field weakening or CI change was introduced. The canonical chart
block is unchanged and is not reprinted.
