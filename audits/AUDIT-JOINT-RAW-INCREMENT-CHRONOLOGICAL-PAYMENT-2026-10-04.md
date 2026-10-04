# Joint raw-moment / whole-increment chronological payment

The whole-project target remains OPEN: nontrivial continuum Yang--Mills
on R^4 for EVERY compact simple group, with SAME-theory full QFT axioms
and finite positive physical Hamiltonian mass. This milestone proves finite
SU(2) source estimates, not scaling, survival, continuum or Clay closure.

## Forward construction and backward consumer

For arbitrary signed supported source q and observable F, let Q=H[q^2 F^2],
R=H[q^2 P(F^2)], U=H[q F^2 Pq], and let I be the ENTIRE source/observable
jump-square integral. The SAME positive two-copy heat, its symmetry and the
two-term square bound give I<=4*C_swapped. The existing exact identity
C_swapped=Q+R-2U then gives

```
8*U + I <= 4*(Q+R).
```

No positivity of q or F, inverse variance, ground-state equation, absolute
band coefficient or small-loss hypothesis is used. Nodup/valid active
indices, support and positive retained heat/head guards are explicit.

For the literal padded Wilson square, the SAME original projected channels
and the exact image P(F^2)=beta*F^2+(1-beta) give

```
8*U + I <= 4*((1+beta)*Q+(1-beta)*M).
```

Here U is the actual original odd-law raw second moment, not endpoint OWN
variance or filtered-start variance. Let a=w^(12*side), beta=w^(32*side),
d=1-beta and k=2*a-1-beta>=0. Combining this comparison with the exact
original identity 4*E+I=2*(d*M-k*Q) cancels Q and retains BOTH credits:

```
(1+beta)*(4*E+I) + (k/2)*I + 4*k*U <= 4*a*d*M.
```

E in this display is unnormalized energy. The extra k*I/2 is nonnegative
under the explicit k guard. This is a tradeoff, not a proved universal
numerical improvement over the preceding additive-loss payment: dividing
by 4*(1+beta) changes both the raw-moment credit and the mass coefficient.
The scalar k-sign window is proved previously, not a justified physical
scaling trajectory.

New declarations and exact checked source locations:

| Declaration | Source |
| --- | --- |
| `sourceIncrement_le_four_swapped_singleEnded` | `lean/YMGap/Continuum/SU2QuaternionProductHeatSourceYoungMoments.lean:175` |
| `eight_sourceMoment_add_increment_le_raw_heat_square` | `lean/YMGap/Continuum/SU2QuaternionProductHeatSourceYoungMoments.lean:240` |
| `paddedSquare_rawSecond_increment_le_channelMoment_mass` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceLoss.lean:580` |
| `paddedSquare_energy_rawSecond_joint_increment_payment` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceLoss.lean:654` |
| `originalOwnBlockCost_rawSecond_joint_increment_boundary_paid` | `lean/YMGap/Continuum/BF4WilsonAllNomeChronologicalExactChannelCost.lean:390` |

The last theorem supplies the actual chronological consumer. With Z the
original endpoint oddMass, eta the computed terminal tolerance and RawRef
the RAW stage-centered endpoint reference square, it proves

```
(1+beta)*(4*Cost+I/Z) + (k/2)*(I/Z) + 4*k*(U/Z)
 <= 4*a*d*(M/Z) + 4*(1+beta)*(eta*RawRef+Signed).
```

`originalOwnBlockCost_energy_split`,
`lean/YMGap/Continuum/BF4WilsonAllNomeChronologicalExactChannelCost.lean:157`,
preserves the stage OWN center and BOTH chronological partitions. Only
boundary drift is paid using `originalBoundaryDrift_upper` at the same
path, line 212. The COMPLETE signed multiplication correction remains.
Only this drift-paid consumer requires endpoint depth>=1. The entire
increment is kept at every step; no Taylor/cubic/omitted-mode error enters.

## Exact remaining mathematical input

The useful original signed-window aggregate versus the SAME filtered-start
variance is still missing. Its backward consumer remains
`original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`.
This milestone constructs a stronger JOINT endpoint comparison, not that
consumer's hypothesis. M/Z, the raw U/Z credit, the full increment, paid
raw-reference drift and Signed must be controlled together on a justified
changing family. No endpoint/filtered norm identification is made, and no
substitution of Signed=Cost-(energy+drift) is counted as an estimate.

Justified scaling, nontrivial continuum survival, physical mass calibration,
SAME OS/full QFT/continuum and every group remain OPEN. Supporting A03 only;
no exact canonical displayed claim changes and no ASCII/paper-list reprint.

## Verification boundary

Three serialized focused checks exited 0. All FIVE new public theorem
gates report exactly {propext, Quot.sound}. Independent frozen mathematical
and evidence reviews passed. Accepted logs under `/private/tmp/`:

| Log | SHA256 |
| --- | --- |
| `ym-swapped-source-moments-20261004-3.log` | `179410d0e692d2aab096490d0a888cee237a3bdd87a9a76988eefbb660c23f99` |
| `ym-joint-raw-increment-payment-20261004-2.log` | `3bbe21f99525a588432201361a1d88322f7d84f2db1416eccac679930e7e17a9` |
| `ym-chrono-joint-raw-increment-20261004-2.log` | `9aab65617923bcfdb07e85df8bbabce4096319447f273c8ede04a24eb0719ae5` |

Frozen source SHA256, in moments / literal channels / chronology order:

```
d35e83920843f32df177eb247229694ff02df448b7188e8c449afb520bf1a7ca
5d68b7d7ac7244bb4726335d22e57876edf474f082b94f07c87dbe6139a6139e
7307a7fb49f57ff16300073701a6365d6cb9bef60470a4d59b1d1945be54a459
```

Existing unused GNS binder warnings in the channel target are unchanged
HEAD source; the other two accepted logs have no warnings. Rejected early
checks exposed a missing namespace, scalar-negation recoding, an inferred
channelSum function and parser alignment/addition API issues; their output
is not proof evidence. No resources were raised to fix them.

Every accepted check used ONE monitored 20-GiB worker and 12-GiB OS reserve,
with fresh host telemetry, no competing compiler and zero swap. No new
sorry/axiom/Classical/native_decide, analytic budget, weakened frontier or
CI/resource setting. Existing root imports register these modules; this is
NOT root verification. No full/root build, broad audit, guard or metrics run.
The active goal and Clay target remain OPEN.
