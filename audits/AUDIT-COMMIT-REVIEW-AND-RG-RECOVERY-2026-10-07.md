# Recent-commit review and checked continuation (2026-10-07)

Whole-project goal, unchanged: construct a nontrivial continuum quantum
Yang--Mills theory on R^4 for every compact simple gauge group, with the required
QFT axioms and a positive physical mass gap. **OPEN.**

## Review scope

Reviewed recent history through `9181971d`, concentrating on the current
AF-padded Wilson route, RG reduction and finite SU(2) torus RP/clustering route.
This is a source/dependency review with focused checks of the new continuation,
not a full repository build or recertification of every recent commit.

| Recent checkpoint | Source evidence | Scope boundary |
| --- | --- | --- |
| `7bf9dcde`: padded excitation nondegeneracy | `lean/YMGap/Continuum/BF4WilsonAllNomeShiftedPaddedNondegenerate.lean:191`, `pathShiftedNondegenerate_of_padded`; floor defined by `paddedNondegFloor` at line 176 | Positive at each scale, not a scale-uniform surviving excitation. |
| `a5c17995`, `eb7cab00`: AF-shaped rational schedule and coupling convention | `lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean:286`, `afNomeSchedule_AFCalibrated` | A schedule satisfying the stated calibration type, not a justified physical spacing/volume trajectory. |
| `a77b717d`: Doeblin rate ruled out for the AF lower-margin input | `lean/YMGap/Continuum/BF4WilsonAllNomeWilsonMixRateDeadEnd.lean:124`, `not_wilsonLowerMargin_mixRate_afPadded`; `WilsonAFPaddedGapInput` at line 132 | The actual all-vector contraction and positive dyadic margin remain inputs. |
| `0ec28cd2`: width-independent strong-coupling Wilson contraction | `lean/YMGap/Continuum/BF4WilsonAllNomeStrongCouplingUniformRate.lean:436`, `allNome_strongCoupling_vacuumSq`; all-widths statement at line 443 | Rate 1/4, squared factor 1/16, under three small-nome guards. Not AF. |
| `30977c45`, `5f1308ef`, `f28c4bb9`: RG comparison, envelope and seed reductions | `lean/YMGap/Continuum/BF4WilsonAllNomeRGStepComposition.lean:325`, `ApproxRgIntertwiner`; `approxRg_transfers` at line 492; `rgKappa_dyadic_envelope` at line 964; `rg_absolute_seed_lowerMarginFrom` at line 1200 | Comparison functions, errors and seed are not constructed. The rate-transfer scope requires correction below. |
| `1557f350`: finite torus RP/CS for supported polynomials | `lean/YMGap/Continuum/SU2TorusRPPolyCS.lean:56`, `torus_rp_poly`; `torus_cs_poly` at line 60 | Finite SU(2), fixed Taylor cutoff K; not a completed torus transfer or continuum theory. |
| `4eff8928`, `9181971d`: finite conditional ratio/clustering join | `lean/YMGap/Continuum/SU2TorusGapCond.lean:76`, `torus_gap_cond`; `lean/YMGap/Continuum/SU2ClusterBridge.lean:72`, `Z_pos`; `dist_mir_shift` at line 88; `cov_decay` at line 117; `torus_gap_bridge` at line 128 | Strong coupling at fixed K; support, time-shift pairing and SAME covariance identification remain hypotheses. This is a finite correlation-ratio inequality, not a constructed transfer operator's spectral gap. |

## RG arrow corrected

`BF4WilsonAllNomeRGStepComposition.approxRg_transfers` supplies the actual fine
**two-step norm factor**

```
alpha = kappa * (rC^2 + epsilon).
```

It does not supply a fine one-step contraction rate. One-step recovery needs
`alpha <= rF^4`. The existing `RgRateRelationκ` instead assumes `rF^4 <= alpha`
(`lean/YMGap/Continuum/BF4WilsonAllNomeRGStepComposition.lean:211`). Neither
implication is an exact-root construction. The old relation and frontier field
types are retained unchanged; their inhabitability is not inferred from the
transfer. Only documentation in that existing Lean module was corrected.

`ApproxRgIntertwiner` has a function `Phi` and quadratic comparison fields. It
has no linearity field or literal vector-intertwining identity. The corrected
scope is also recorded in `audits/SCOPE-RG-STEP-COMPOSITION-REDUCTION-2026-10-06.md`.

## New checked mathematical recovery

On the SAME completed Wilson carrier, completed Cauchy--Schwarz and time balance
give

```
||T x||^4 <= ||x||^2 * ||T^2 x||^2.
```

Constructive square order reflection then proves the actual one-step
vacuum-square contraction from a supplied two-step factor below `r^4`, including
zero-norm vectors, without division or an excitation floor:

- `lean/YMGap/Continuum/RCNonnegativeSquareReflection.lean:78`,
  `RCsquare_le_reflect_right_nonnegative`.
- `lean/YMGap/Continuum/BF4WilsonAllNomeRGTwoStepRecovery.lean:58`,
  `vacuumSq_of_twoStepFactor`.

For `0 <= alpha <= 1`, the explicit rational rate

```
r = (3 + alpha)/4
alpha <= r^4
1 - r = (1 - alpha)/4
```

avoids selecting an exact fourth root. It is strict when `alpha < 1`:
`lean/YMGap/Continuum/RGExplicitRationalRate.lean:31`, `explicitRate`;
`rate_lt_one` at line 46; `rate_margin` at line 76;
`factor_le_rate_fourth` at line 107.

The supplied actual RG quadratic comparison now feeds that computed one-step
rate: `lean/YMGap/Continuum/BF4WilsonAllNomeRGTwoStepRecovery.lean:90`,
`approxRg_transfers_explicitRate`. The exact direct margin recurrence is
recorded as an inequality in `explicitRate_margin_step` at line 107:

```
mF = (2*mC - mC^2 - effectiveRgDefect)/4.
```

This is the input shape of `scaled_step_core`
(`lean/YMGap/Continuum/BF4WilsonAllNomeRGStepComposition.lean:808`). It does
not inhabit the old opposite-direction fourth-power relation. Actual RG
comparisons, strict factors, summable defects and an AF seed remain OPEN.

## Parallel finite torus observable algebra

- `lean/YMGap/Continuum/SU2TorusRPObservableReflection.lean:56`,
  `theta_chi_spatial`: reflection of the genuine spatial fundamental character,
  with physical link coverage, box membership, nonduplication and reflection
  closure explicit. Its substitution ingredient is `chi_word_sub` at line 38.
- `lean/YMGap/Continuum/SU2WilsonObsExtraction.lean:30`, `obsTK_extract`:
  extraction of exactly one actual `1+chi` insertion, requiring `P.Nodup`,
  `p in P` and `p notin S`. Two applications extract distinct roots while
  preserving all original action factors and remaining selections.

These prove two ingredients, not `SU2ClusterBridge.hcov`. OWN centering,
covariance cancellation, equality of reflected/translated means, positive-half
support and exact RP/time-shift pairing still need to be joined. The displayed
arbitrary spatial coordinates in `torus_gap_bridge` do not themselves provide
the physical-root membership guards needed by insertion extraction.

## Verification evidence

Five final one-file checks passed with one serialized, memory-monitored worker,
12 GiB reserve and a 20 GiB worker ceiling. The final sources use no raised
heartbeat limit. All 16 printed theorem gates are subsets of
`{propext, Quot.sound}`; no source `sorry`, new axiom or classical shortcut was
introduced. Temporary local check logs:

| Checked source | Printed gates | Final log |
| --- | --- | --- |
| `RCNonnegativeSquareReflection.lean` | 3 | `/private/tmp/ym-oct7-square-reflection.log` |
| `RGExplicitRationalRate.lean` | 6 | `/private/tmp/ym-oct7-explicit-rate.log` |
| `BF4WilsonAllNomeRGTwoStepRecovery.lean` | 4 | `/private/tmp/ym-oct7-rg-recovery.log` |
| `SU2TorusRPObservableReflection.lean` | 2 | `/private/tmp/ym-oct7-observable-reflection.log` |
| `SU2WilsonObsExtraction.lean` | 1 | `/private/tmp/ym-oct7-observable-extraction.log` |

The dependency-complete `SU2TorusRPThetaTK:olean` and
`SU2WilsonObsExtraction:olean` targets also passed. Earlier missing-dependency
or failed-elaboration runs are not verification evidence. New leaves are
registered in `lean/YMGap.lean`; no full-root build or repository-wide audit is
claimed. Three pre-existing untracked duplicate Lean files were preserved.

## Continued plan

`work_plan.md` now prioritizes the actual two analytic producers: bounded
step-ratio/window survival and all-vector completed contraction with a positive
dyadic lower margin on the SAME AF-padded family. The next local joins are the
direct computed-margin recurrence into telescoping, and the actual centered
Haar covariance/RP identification. Neither join substitutes for those producers.

Physical spacing/volume justification, nontrivial continuum survival, the SAME
limiting OS theory and generator, full QFT axioms and every compact simple group
remain OPEN. Supporting algebra changed; the canonical chart's broad frontier
states did not, so it is not reprinted.
