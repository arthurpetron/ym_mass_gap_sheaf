# Actual cyclic heat step: rotation separation and angular estimate

Date: 2026-09-23. Parent revision: `26e8bd1`.

Whole-project goal remains OPEN: constructive Lean nontrivial continuum
Yang--Mills on R^4 for every compact simple group, full same-theory QFT
axioms, isolated vacuum, and finite positive physical Hamiltonian mass gap.

## Constructed local operator join

`reverseBlocks` and `reverseTailBlocks`,
`lean/YMGap/Continuum/SU2QuaternionBlockReversal.lean`, construct explicit
involutions A (full reversal) and B (fix head zero, reverse the spectators).
`reverseTail_lift_prefix` and `reverseTail_source_copy_prefix` establish the
finite exponent identities with padding respected. In particular, the fresh
unused output slot is not identified with an existing neighboring variable.

In `lean/YMGap/Continuum/SU2QuaternionProductHeatCyclicRotation.lean`:

- `cycleStep_reversed_pairing`, line 82, transports the actual two-insertion
  cyclic-step pairing to `heatPair` on B-reindexed input and A-reindexed
  insertion, retaining all spectators and signs.
- `cycleStep_rotation_carrier`, line 120, proves `C p ~ A(headMap(B p))`
  under every Haar insertion on n=tail+1 blocks, for supported p. The
  algebraic join holds at every w and K, without an identification premise.
- `cycleRotation`, line 134, is R=A B; `cycleReturn`, line 139, is B A.
- `cycleReturn_step_carrier`, line 144, identifies B A C with the computed
  conjugated head update B headMap B. The two copies of A cancel using the
  supported prefix/carrier equality, not raw trailing-zero list equality.
- `cycleReturn_pairing`, line 158, moves the inverse coordinate motion
  from the output to forward motion of the insertion.

## Quantitative consequence

`cycleStep_rotated_defect_le_head_energy`, same file line 168, proves

    H_n(p*p) - H_n(R(p) * C(p))
      <= (1-w) * H_n(blockAngularSquare 0 p),

for n=tail+1, supported p, 0<=w<1, and `sufficientCutoff w<=K`. It consumes
the actual derotation identity and the already checked conjugated head
angular bound; B fixes block zero. There is no assumed gap or analytic
comparison field in this theorem.

The R(p) term is essential. Neither R=id nor positivity/self-adjointness of
C nor `H(p*p)-H(p*C(p)) <= ...` is asserted. The theorem does not sum local
defects to claim the full-product bound.

## Next consumer and remaining obligations

`productMap_range_cycle_carrier`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatCyclicFold.lean:144`, already
identifies n cyclic steps with the fully active original product operator.
The next quantitative target remains

    H_n(f*f) - H_n(f * productMap(range n) f)
      <= (1-w) * sum_i H_n(blockAngularSquare i f).

Commuting smoothing-map composition with angular control, or an equivalent
positive joint-mode argument, is still required. The new local bound alone
does not establish this endpoint estimate.

The interacting consumer remains `energy_eq_bare_add_correction`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:144`.
It retains the actual source `V*g*f` and signed endpoint correction. Proper
active subsets still require the inactive Haar-projection residual. No
physical OS/time, spatial/spacing, continuum survival, finite physical mass,
full QFT, every-group or Clay obligation is discharged here. The independent
completed BF4 conditional-dynamics gap and the shortcut refutations stand.

## Verification boundary

Two focused checks completed with terminal exit 0:

- `/tmp/ym-gap-block-reversal-check-5.log`: four public axiom gates;
- `/tmp/ym-gap-product-heat-cyclic-rotation-check-1.log`: seven public gates.

Both used `scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 8`
with a named leaf `--check` and cached `--check-output`, retaining the 12 GiB
OS reserve. All eleven gates report only `{propext, Quot.sound}`. Accepted
logs contain no error, warning or `sorryAx`. Earlier failed reversal drafts
are not verification evidence. A separate read-only review confirmed the
rotated-input scope and the remaining full-product/interacting consumers.

No new `sorry`, axiom, or changed frontier field. Root imports are registered,
but no full-root build, audit, progress guard or broad test suite was run.
CI is unchanged. This is a finite, explicit local estimate, not Clay closure.
