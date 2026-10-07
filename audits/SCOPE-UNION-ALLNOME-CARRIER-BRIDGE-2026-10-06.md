# Scope: UnionCompletion ↔ all-nome Completion carrier bridge? (2026-10-06 PT)

Companion to the strong-coupling interface test
(`audits/SCOPE-WILSON-STRONG-COUPLING-UNIFORM-RATE-2026-10-06.md`, commit 58a82d76).

## Exact statement under review

Is there an identification making
`BF4WilsonSpatialUnionSeminorm.UnionCompletion` and
`BF4WilsonAllNomeCompletedInner.Completion width`
the SAME Hilbert space carrying the SAME one-step transfer, so that the Descent
width-independent rate `twoStepRate ≈ 1/16` (`StrongCouplingVacuumSqContraction`)
transports as `WilsonVacuumSqContraction` on the all-nome carrier?

Possible forms of "same":
- definitional equality of types;
- a constructive isometric intertwiner `U` with `U ∘ T_union = T_allnome ∘ U` and
  `B_allnome(Ux,Uy) = B_union(x,y)`, preserving the vacuum complement.

## What each object is (Lean)

| | Spatial Union (`UnionCompletion`) | All-nome (`Completion width`) |
|---|---|---|
| Dense core | `Stage` = `{base > 0, value : IntrinsicExpression base}` (growing bases) | `IntrinsicExpression width` at FIXED literal width |
| Seminorm | limiting `distSq` under Descent guards (`BF4WilsonSpatialUnionSeminorm.lean:98`) | all-nome `intrinsicForm` difference (`BF4WilsonAllNomeSeminorm.lean:151`) |
| Nome regime | `0 < w < 1` AND `heatRatio w ≤ 1/2`, `heatRemainderBound w < 1`, entropy-rate guard | `0 < w < 1` only (all-nome; no strong-coupling window) |
| Width | no fixed width; Cauchy streams may grow the base | parameter `width : Nat` baked into the type |
| Transfer | `completedTime` = completionMap of Stage `time n` (`…Seminorm.lean:143`) | `completedTime` = completionMap of fixed-width `advance n` (`…CompletedTime.lean:73`) |
| Unit | `completedUnit` = embed of `unitStage` | `unitState width` = embed of `unit width` |
| Vacuum sq contraction | `StrongCouplingVacuumSqContraction` at rate `≈ 1/16` (Descent) | `WilsonVacuumSqContraction` currently inhabited only at Doeblin `mixRate` (width-dependent; dead end for X2) |

Citations:
- Union: `BF4WilsonSpatialUnion.lean:37` (`Stage`); `BF4WilsonSpatialUnionSeminorm.lean:98,139,143,166`.
- All-nome: `BF4WilsonAllNomeCompletedInner.lean:59,64,88`; `BF4WilsonAllNomeCompletedTime.lean:73`;
  `BF4WilsonAllNomeSeminorm.lean:151`.
- Rates: Descent `twoStepRate` (`BF4WilsonDescentUniformConnectedDecay.lean:46`);
  all-nome Doeblin `mixRate` / `completed_oneStep_norm_gap` (`BF4WilsonAllNomeCompletedGap.lean:200`).

## Verdict

**Not the same object. The bridge is NOT finite algebra.**

Reasons (any one blocks definitional equality / a trivial intertwiner):
1. **Different dense cores.** Union completes growing-base `Stage` streams; all-nome completes
   fixed-width expressions. A Union Cauchy stream need not live at one `width`.
2. **Different nome hypotheses.** Union's seminorm and Descent gap need the strong-coupling
   guards; the all-nome seminorm is defined for every `0 < w < 1` and its Doeblin gap uses a
   different (width-dependent) rate producer.
3. **Different form constructions.** Union distance is the spatial-union limiting `distSq` at a
   common base; all-nome distance is the all-nome reflected `intrinsicForm` on
   `difference x y`. Coincidence of these forms (even at fixed width and small `w`) is an
   analytic identification, not a `rfl` or a short algebraic rewrite.
4. **Different transfers on the nose.** Stage `time` vs fixed-width `advance`, lifted by
   different `Nonexpansive` maps.

## What a real bridge would need (analytic / structural input)

To transport `StrongCouplingVacuumSqContraction → WilsonVacuumSqContraction`:
- For each fixed `width`, under the Descent guards, an isometry (or dense-core isometric
  embedding with continuous extension) from the all-nome completion into the Union completion
  (or a common third space), intertwining `advance` with `time`, and identifying the
  completed pairings on the vacuum complement;
- OR a direct Descent-style connected-decay argument on the all-nome fixed-width carrier
  that produces a width-independent rate (new analytic work on that carrier, not a bridge).

Neither is finite algebra. No kernel-checked transport is claimed in this pass.

## Honest physics / frontier placement

- The Descent `1/16` rate is **known strong-coupling physics**, packaged as an interface test.
  It is NOT the asymptotic-freedom margin `m·2^-j` on the AF schedule.
- Even if a bridge existed, a constant rate still cannot feed
  `wilsonGapBranch_afPadded_generic` on any `NomeSchedule` trajectory: every such schedule has
  `w_j → 1` (leaves the window), and `constant_rate_not_all_scale_upper` (58a82d76) proves a
  constant rate fails the B04 upper half on unbounded `side_j`.
- Live AF gap input remains `WilsonAFPaddedGapInput` (some rate with `1−r_j ≍ 2^-j`).

## Side task (this commit)

Unconditional non-vacuity of the strong-coupling package at the pilot nome
`w = invSucc 1023 = 1/1024`, discharging all three Descent guards via
`existingNome_guards` and `existingNome_entropyRate` (see
`BF4WilsonStrongCouplingUniformRate.existingNome_package_nonvacuous`).

## Follow-up (2026-10-06 PT)

Route (b) was carried out as a finite adaptation:
`BF4WilsonAllNomeStrongCouplingUniformRate.allNome_strongCoupling_vacuumSq`. It gives
strong-coupling only and is not AF. The bridge verdict above is unchanged; route (b) avoids the bridge.
See `SCOPE-ALLNOME-DESCENT-ROUTE-B-2026-10-06.md`.
