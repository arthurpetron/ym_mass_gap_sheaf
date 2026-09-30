# Original all-state patch-complement estimate

## Goal and mathematical result

The whole-project goal remains OPEN: constructive continuum Yang--Mills on
R^4 for every compact simple group, with SAME-theory QFT axioms, nontriviality
and a finite positive physical Hamiltonian gap.

Let S be any finite list of physical links, N its length, P_i the EXISTING
original full-action singleton conditional projections, Q_S the EXISTING
original block conditional, H_S=sum_i(I-P_i), and E_S(x)=sum_i||(I-P_i)x||^2.
On the SAME original completed carrier, for every x,

    gamma(w,N) ||x-Q_S x||^2 <= E_S(x),
    gamma(w,N) E_S(x) <= ||H_S x||^2,

where the positive rational data are

    L(w,N) = min(headFloor(w),1)^(6*N),
    U(w,N) = (1+prefixCap(w))^(6*N),
    gamma(w,N) = recipPos(U(w,N))*L(w,N).

The actual step x -> x-s H_S x, with s=1/(2*(N+1)), contracts the actual
patch energy by q=1-s*gamma, with 0<q<1. This is conditional-update weighted
L2 dynamics, NOT Euclidean/OS time. No physical mass is calibrated by q.

Quantifiers: every rational 0<w<1, every extent, every K>=headCutoff(w),
every finite physical link list, every completed state. No small-nome,
centering, support-locality, distinctness or fixed-boundary premise.
Lists may be empty or repeated. Exterior-dependent ground states are kept;
the previous exact kernel theorem identifies Q_S's range with ker H_S.
Constants are independent of ambient extent and late cutoff at FIXED w,N;
they are not uniform positive constants in coupling, patch size or spacing.

## Short proof and same-object pins

Use the already constructed identity-on-polynomial maps J:F->G and I:G->F,
where G retains every original action factor detached from S. Their explicit
moduli and bounds give L||Jz||_G^2 <= ||z||_F^2 <= U||Jz||_G^2.
In G, coordinate Haar projections M_i commute and their finite family map M_S
satisfies the completed Poincare inequality

    ||Jx-M_S Jx||_G^2 <= sum_i ||Jx-M_i Jx||_G^2.

The existing mutual range-fixing identities and orthogonal-projection
minimality give

    ||x-Q_Sx||_F^2 <= ||x-I M_S Jx||_F^2,
    ||Jx-M_i Jx||_G^2 <= ||J(x-P_i x)||_G^2.

Compose these comparisons and cancel only the positive rational U. There is
one L/U cost, not its square. No raw Haar map is declared orthogonal for F
or substituted for an original conditional projection.

For the generator consequence, y=x-Q_Sx has the exact pairing
<H_Sx,y>=E_S(x), since H_SQ_Sx=0. Completed Young applied to H_Sx and gamma*y,
together with gamma||y||^2<=E_S(x), gives gamma E_S(x)<=||H_Sx||^2. It does
not divide by the possibly zero energy or use a spectral theorem. The
existing gradient-descent theorem then consumes this actual lower bound.

## Declaration evidence

Paths are relative to `lean/YMGap/Continuum/`.

| Declaration | File:line | Scope |
| --- | --- | --- |
| `residual_distance_minimum` | `GNSProjectionDistanceMinimum.lean:55` | Completed orthogonal projection minimizes distance to its fixed space |
| `commuting_sweep_variance_le_finalEnergy` | `GNSCommutingPatchVariance.lean:98` | Arbitrary finite commuting schedule, original-input energy |
| `sweep_eq_familyProjection` | `SU2QuaternionWeightedHaarFamilyVariance.lean:62` | Exact existing Haar family map, head-first order |
| `family_variance_le_energy` | `SU2QuaternionWeightedHaarFamilyVariance.lean:88` | Every state of the certified spectator-weighted completion |
| `background_singleton_energy_le` | `BF4ExactSlabBlockComplementCoercivity.lean:105` | Raw background residual versus ORIGINAL singleton residual |
| `background_energy_le` | `BF4ExactSlabBlockComplementCoercivity.lean:132` | Same patch list and same unswept state |
| `block_complement_coercivity_mul` | `BF4ExactSlabBlockComplementCoercivity.lean:160` | Division-free actual all-state patch estimate |
| `blockCoercivity` | `BF4ExactSlabBlockComplementCoercivity.lean:183` | Positive nome/patch-size coefficient as rational data |
| `blockCoercivity_le_one` | `BF4ExactSlabBlockComplementCoercivity.lean:202` | Supplies the strict gradient-step rate window |
| `block_complement_coercivity` | `BF4ExactSlabBlockComplementCoercivity.lean:232` | Actual block kernel complement, not global vacuum complement |
| `square_lower_of_coercive_pair` | `GNSProjectionKernelCoercivity.lean:75` | Generic Young argument, no spectral theorem |
| `generator_complement_pair` | `BF4ExactSlabPatchGeneratorCoercivity.lean:56` | Original generator, original block projection, exact energy |
| `patch_generator_square_lower` | `BF4ExactSlabPatchGeneratorCoercivity.lean:70` | Actual patch square-energy lower bound |
| `patchRate_window`, `patch_step_energy_contract` | `BF4ExactSlabPatchGeneratorCoercivity.lean:84`, `:91` | Strict actual gradient-step energy contraction |

## What this removes, and what remains

This removes the absence of ANY quantitative all-state bound on the actual
patch-kernel complement. It provides a baseline for converting a justified
kernel-preserving approximation error into an energy-relative error. It does
not itself construct a finite-core/tail certificate or its sharper margin.
The older support-local bound concerned supported polynomial observables and
the full schedule; it did not provide this all-state subsystem statement.

The coefficient is deliberately conservative. It is no larger than the old
`supportRatio`: its numerator uses min(headFloor,1) rather than headFloor and
its denominator uses 1+prefixCap rather than prefixCap. This comparison is a
source-level observation here, not a new printed Lean theorem.
`BF4ExactSlabPatchCollarBudgetObstruction.scaled_margin_le_neg_fourteen`
at `lean/YMGap/Continuum/BF4ExactSlabPatchCollarBudgetObstruction.lean:43`
already proves that even the larger old coefficient fails the recorded
candidate box-overlap budget. The new result does NOT repair that budget.
This is insufficiency of a lower certificate, not an upper bound on the
true gap or a Yang--Mills counterexample.

NEXT: a genuinely sharper original-action patch/overlap estimate or collective
signed estimate with useful dependence on a justified scaling family. Do not
extend this collar-baseline branch merely to repackage its small coefficient.
The one-shared-face route still lacks its completed commuting retained-action
conditional reference; generic numerator commutation alone does not construct
that normalized reference. A finite computation needs kernel preservation,
all-degree/exterior control, and a proved local-to-global consumer first.

OS/physical-time identification, spatial/spacing control, nontrivial continuum
survival, finite physical mass, full QFT and every group remain open. No
canonical chart claim changed; no ASCII chart was reprinted.

## Verification boundary

Six final focused checks passed all 29 printed gates within
{propext, Quot.sound}; `ValidSlot` is axiom-free. The safe-build procedure used
one serialized worker, a 20 GiB hard ceiling,
12 GiB reserve, continuous safety telemetry and 300-second status cadence.
All checks finished in their initial calls; there was no live polling loop.
No full root/tree build, audit or guard was run. Root imports
are registration only. No new sorry, analytic premise, custom axiom,
classical reasoning, native decision oracle or frontier weakening; no old
sorry discharged. Independent source review confirmed the original operator
pins, exterior-dependent kernel, list scope and conservative coefficient.

Final logs:

- `/tmp/ym-projection-distance-minimum-20260930.log`
- `/tmp/ym-commuting-patch-variance-20260930.log`
- `/tmp/ym-weighted-haar-family-variance-20260930.log`
- `/tmp/ym-block-complement-coercivity-20260930.log`
- `/tmp/ym-projection-kernel-coercivity-20260930.log`
- `/tmp/ym-patch-generator-coercivity-20260930.log`
