# A checked scaling test of the original local defect

Date: 2026-09-30 UTC. Whole-project Clay target OPEN.
Classification: PROGRESS: a proposed source/schedule combination is ruled
out as a fixed positive relative survival witness. Two focused checks
passed 15 axiom gates. No canonical chart marker changes.

## The supplied test, not an assumed scaling estimate

The previous checkpoint proved, on the literal all-nome Wilson completion,

    (1-w)^24 * ||T^n y||^2 <= 4*K0/(n+1)^2 * ||y||^2,
    y=(I-T)v,  K0=16*F(24582)^2,  F(C)=(5+2*C^2)*(2+3*C^2).

The source v is the existing centered physical plaquette. The operator,
normalization and carrier are unchanged. The new explicit candidate is

    w_j = 1-1/(j+2),  a_j = (1/2)^(j+1),  n_j = 2^(j+1).

The exact identity n_j*a_j=1 is proved. The word "candidate" is essential:
no theorem identifies this assigned spacing with Yang--Mills physical
calibration. No legacy moving-cube completion is substituted for Wilson.

The squared nome weight is exactly (j+2)^(-24), while
1/(n_j+1)^2 <= (1/4)^(j+1). The existing constructive polynomial/geometric
estimate therefore supplies the actual index cutoff

    N(epsilon) = polynomialCutoff(1/4, 4*K0, 24, epsilon).

For every positive rational epsilon, every j>=N(epsilon), every spatial
width, and every physical plaquette in that width, the new theorem gives

    ||T_j^n y_j||^2 <= epsilon*||y_j||^2      for all n>=n_j,
    <y_j,T_j^(2n)y_j> <= epsilon*||y_j||^2.

The second line uses the exact existing time-pairing identity. It is an
actual autocorrelation, not a Markov-chain or auxiliary-filter estimate.
Widths and plaquettes may be chosen differently at each index; no map
between their completions or limit vector is constructed.

The source has its already-proved positive norm at each j. Choosing
epsilon=floor/2 and canceling that positive norm proves that a fixed
positive relative orbit-norm floor is impossible at the computed late
index. Thus nonzero-at-every-cutoff is insufficient for this candidate.

There is also a stronger ceiling version: at n_j the same relative bound
holds for every nome 0<w<=w_j, since (1-w)^24 increases when w decreases.
No small-nome guard or all-state spectral gap is used.

## Exact source map

Paths below are relative to `lean/YMGap/Continuum/`.

| Declaration | Source | Scope |
| --- | --- | --- |
| `nome`, `steps`, `spacing` | `BF4WilsonNomeDyadicDefectSchedule.lean:35`, `:38`, `:41` | Explicit rational/natural candidate data |
| `nome_positive`, `nome_lt_one` | `BF4WilsonNomeDyadicDefectSchedule.lean:43`, `:47` | Admissible strict nome for every index |
| `steps_spacing_normalizes` | `BF4WilsonNomeDyadicDefectSchedule.lean:50` | Candidate elapsed time is exactly one |
| `normWeight_nome_pin` | `BF4WilsonNomeDyadicDefectSchedule.lean:100` | Exact degree-24 reciprocal identity |
| `scaleModulus`, `scalar_budget` | `BF4WilsonNomeDyadicDefectSchedule.lean:123`, `:129` | Computes and proves the late-index scalar comparison |
| `normWeight_antitone` | `BF4WilsonAllNomeDyadicDefectCollapse.lean:39` | Smaller nome improves the normalization weight |
| `ceiling_relative_small` | `BF4WilsonAllNomeDyadicDefectCollapse.lean:62` | Every actual nome below w_j, every width and physical plaquette |
| `sampled_relative_small`, `later_relative_small` | `BF4WilsonAllNomeDyadicDefectCollapse.lean:87`, `:95` | Actual completed source at n_j and all later times |
| `later_autocorrelation_small` | `BF4WilsonAllNomeDyadicDefectCollapse.lean:104` | SAME connected source response at twice the elapsed time |
| `sampled_relative_floor_impossible` | `BF4WilsonAllNomeDyadicDefectCollapse.lean:123` | Positive fixed relative orbit-norm floor contradicts the checked bound |

## Recursive step back: what to investigate next

Do not continue building survival interfaces for this local defect on the
tested schedule. This result does NOT rule out other schedules, other
observables, or continuum Yang--Mills. The next task is an original source
with controlled physical support and a useful relative positive-time bound.

Two source paths were inspected:

- Literal growing Wilson squares already exist:
  `BF4WilsonAllNomeDyadicExcitation.dyadicExcitation_norm_floor`, line 45,
  and `dyadicExcitation_correlator_pin`, line 77, keep the actual Wilson
  carrier. Their old starRatio floor still depends strongly on nome.
  `BF4DyadicWilsonSquarePlacedGeometry.placedSelectedLink_not_mem_placedDyadicTail`
  at line 57 supplies the selected edge's absence from the tail. Extending the new
  relative Ward floor needs a general ordered-word angular identity; it
  cannot be inferred from the old variance estimate.
- Signed plaquette families have a finite original-action lower bound in
  `BF4ExactSlabPlaquetteAffineCoercivity.normalized_variance_floor`, line 242,
  but its coefficient still uses lower(w)/(600*upper(w)). Its completed
  consumer `BF4ExactSlabFixedSpatialPlaquetteFamilyVariance.familyExcitation_norm_floor`,
  line 157, uses the distinct joint face-span completion, not the current
  literal-Wilson completion. A carrier join must be proved, not assumed.

The following shorter signed-source idea was algebraically reviewed by
the main agent and Sol; it is NOT a Lean-checked result of this checkpoint:

1. `Z4PlaquetteBoundaryRigidity.distinct_boundary_overlap_le_one`, line 47,
   says distinct physical plaquettes share at most one edge. Two distinct
   edges of face p therefore suffice to kill every other plaquette term
   in a mixed angular derivative of F=sum_q c_q*f_q.
2. The proposed fundamental-word identity for two distinct edge blocks is
   sum_(a,b) (D_e1^a D_e2^b f_p)^2 = 8+f_p^2 on the unit-quaternion
   carrier. Proving it is a concrete missing algebraic step.
3. `RationalRelativeWardPrediction.energy_le_prediction`, line 73, already
   proves the scalar energy bound with M=24+36*C^2 before using the
   singleton kinematic identity. The incident split is supported by
   `BF4ExactSlabPlaquetteIncidentLinear.incidentObservable_head_degree_one`,
   line 108, and `BF4ExactSlabPlaquetteGradient.observable_derivative_incident`,
   line 180. Applying original-weight relative Ward twice is expected to
   give the per-face detector estimate 8*Z*c_p^2 <= M^2*Z*Var_W(F).
4. Even if this per-face bound is proved, summing over p costs the number
   of faces. A support-uniform result still needs a genuine weighted
   bounded-interference/Bessel estimate. Single-face positive diagonals
   do not supply that signed Gram bound.

No version of this proposed analytic conclusion has been added as an
assumed Lean field. Physical calibration, spatial/scaling passage,
survival, useful every-state decay, full QFT, every group and Clay remain
OPEN. No frontier statement has been weakened.

## Verification

Both final checks used the monitored launcher with one worker, hard
20 GiB worker cap, 12 GiB OS reserve and dynamic pressure/swap monitoring.
Process inspection found no competing Lean/Lake/test/runner job. Sol
implemented the scalar module; the main agent checked and repaired local
elaboration details, and implemented the actual completed consumer.
Luna and Sol performed bounded read-only source/mathematics reviews.

| Module | Gates | Final log under `/tmp/` |
| --- | ---: | --- |
| BF4WilsonNomeDyadicDefectSchedule | 9 | ym-dyadic-defect-schedule-20260930.log |
| BF4WilsonAllNomeDyadicDefectCollapse | 6 | ym-dyadic-defect-collapse-20260930.log |

All 15 gates are within {propext, Quot.sound}; no sorryAx. Failed draft
checks are not evidence of completion. Root imports were added but no
aggregate-root build, broad audit or guard was run. CI remains disabled.
No new sorry, custom axiom, analytic premise or weakened field was added;
no old ledgered sorry was discharged.
