# Original product heat as a fresh-output cyclic fold

Date: 2026-09-23. Parent revision: `ca5e26c`.

Whole-project goal remains OPEN: constructive Lean nontrivial continuum
Yang--Mills on R^4 for every compact simple group, full same-theory QFT
axioms, isolated vacuum, and finite positive physical Hamiltonian mass gap.

## What is constructed

`cycleStep`, `lean/YMGap/Continuum/SU2QuaternionProductHeatCyclicFold.lean:56`,
is the explicit polynomial operation

    partialHaarHead (heatAt 0 n w K * p).

For p supported on n blocks, block n is fresh. Integrating/removing block
zero leaves n blocks again: the remaining sources followed by produced
outputs. `cycleIterate` at line 61 composes this computed map. No operator
realization is assumed or selected from a certificate.

`productHeat_prefix_succ_carrier`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatPrefix.lean:113`, proves

    productHeat n (range (m+1))
      = heatAt 0 n * liftHead (productHeat n (range m))

under every Haar insertion on n+m+1 blocks. Lifted character polynomials
are compared with padded coefficient equivalence, not false equality of
raw trailing-zero monomial lists. Support is constructed at line 52.

One exact conditional Fubini step then proves
`productHeat_prefix_fold_carrier`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatCyclicFold.lean:126`:
integrating m source heads from the n+m-block prefix equals m cyclic steps,
under every insertion on the n-block survivor carrier. This holds for every
m. For m>n earlier outputs are evolved again; the proof does not pretend
that this longer prefix lives on only 2n variables. The algebraic carrier
identity needs no support restriction on the insertion or input.

At m=n, `productMap_range_cycle_carrier` (same file line 144) identifies
the ORIGINAL fully active `productMap` with n steps, in its original output
order. `productMap_range_cycle_pairing` (line 151) and
`productMap_range_cycle_defect` (line 159) expose the actual signed pairing
and quadratic defect. `cycleStep_supported` (line 65) and
`cycleIterate_supported` (line 72) ensure supported states stay on the
n-block window. `cycleStep_mean` (line 81) and `cycleIterate_mean` (line 95)
preserve their original Haar mean for n>0, at every finite cutoff.

## Actual consumer and remaining mathematics

The next target remains the original endpoint inequality

    H(f*f) - H(f * productMap(range n) f)
      <= (1-w) * sum_i H(blockAngularSquare i f),

with supported f, 0<=w<1, and `sufficientCutoff w<=K`. The new endpoint
identity removes a realization obligation for a concrete fresh-output fold;
it does NOT prove this inequality. A cyclic step includes a coordinate
rotation. No positivity/self-adjointness or angular defect bound is asserted
for its intermediate maps. Separating this rotation and proving the
commuting-product estimate, or a positive joint-mode argument, remains open.

The original interacting consumer is
`energy_eq_bare_add_correction`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:144`.
It retains the actual source `V*g*f` and the signed endpoint correction.
Its physical `activeBlocks` list is not replaced by `range n`: proper active
subsets still need the explicit inactive-projection residual. None of these
quantitative, physical OS/time, spatial/spacing, continuum, QFT or every-group
obligations is discharged by the new finite algebraic identity.

The existing-neighbor/head-map counterexamples and the independent completed
BF4 conditional-dynamics gap are unchanged.

## Verification boundary

Two successful focused checks, terminal exit 0:

- `/tmp/ym-gap-product-heat-prefix-check-3.log` (two public gates);
- `/tmp/ym-gap-product-heat-cyclic-fold-check-3.log` (ten public gates).

Each used `scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 8`
with a named `--check` leaf and `--check-output` cache. The 12 GiB OS reserve
was retained. All twelve printed axiom sets are within
`{propext, Quot.sound}`; accepted logs contain no errors, warnings or
`sorryAx`. Earlier failed elaboration attempts are not verification evidence.
No new `sorry`, axiom, or frontier-field change. No full-root build, axiom
audit, progress guard, or broad test suite was run; CI remains unchanged.
