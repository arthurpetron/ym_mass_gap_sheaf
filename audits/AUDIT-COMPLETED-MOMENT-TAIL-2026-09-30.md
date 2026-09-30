# Completed original-action tail from finite dual moments

Date: 2026-09-30 UTC. The unchanged constructive, same-theory continuum
Yang--Mills/Clay goal remains open. This increment concerns the original
finite-slab conditional dynamics, not OS time or a physical Hamiltonian.

## Statement and causal use

Fix rational 0<w<1, finite extent, K>=headCutoff(w), and epsilon>0. Use the
existing returned cutoff N=`sweepCutoff w extent epsilon` and finite list
M=`dualMonomials w K extent N`. For EVERY completed original-action vector x,

    <x,embed(m)> = 0 for every m in M
        implies ||S x||^2 <= epsilon * ||x||^2,

where S is the existing all-link conditional sweep. The same finite moment
data for completed x,y imply the corresponding relative bound on
`S x-S y`. No polynomial degree restriction is imposed on either input.

This closes the completed-tail residue of
`AUDIT-FINITE-MOMENT-SWEEP-TAIL-2026-09-30.md`. It does not close that report's
finite-core estimate or the conditional-patch/exterior-coefficient boundary.

## Proof

1. Completed rational linearity extends the finitely many zero pairings
   to every dense polynomial covered by M. Dependent monomials and the
   original weighted radical are retained.
2. For each dense test q, the reverse polynomial approximation A* q has
   precisely that degree bound, so `<x,A* q>=0`.
3. The actual completed adjoint identity gives
   `<Sx,q>=<x,S* q-A* q>`. Reversal preserves schedule length, hence the
   existing N also gives `||S* q-A* q||^2<=epsilon*||q||^2`.
4. Apply the completed Young inequality to epsilon*x and the error vector.
   Cancel only the positive rational epsilon, obtaining
   `2<Sx,q><=epsilon*||x||^2+||q||^2`.
5. Test along the supplied dense Cauchy representative of Sx and pass the
   pairing and norm limits. Subtracting one copy of `||Sx||^2` proves the
   sharp bound. Neither a norm inverse nor a Gram inverse is used.

The proof never asks the approximants of x to have exactly zero moments.
It also does not need to construct a completed finite-rank approximant.
The existing Cauchy moduli and inverse cutoff remain the convergence data.

## Source map

Paths are relative to `lean/YMGap/Continuum/`.

- `GNSDenseDualNormBound.norm_le_of_dense_approximate_dual`, in
  `GNSDenseDualNormBound.lean:118`: constructive dense dual norm estimate.
- `QuaternionHaarCompletedMonomialSpan.completedPair_zero_of_test_list`,
  in `QuaternionHaarCompletedMonomialSpan.lean:74`: completed monomial span.
- `BF4ExactSlabCompletedMomentTail`, in
  `BF4ExactSlabCompletedMomentTail.lean`: `MomentZero` at line 53,
  `momentZero_dual_orthogonal` at 60, `reverseSweep_approximation_error`
  at 72, `completed_tail_of_dual_orthogonal` at 99,
  `completed_sweep_tail_bound` at 134, `momentZero_of_check` at 145,
  `completed_sweep_difference_of_moments` at 161.

## Remaining quantitative boundary

`MomentZero` is a finite family of equalities of constructive-real pairings,
not an executable equality test for arbitrary completed vectors. The earlier
Boolean checker still supplies it on passing dense inputs. No nonzero
passing input is constructed by this increment.

The list depends on nome, cutoff, extent and tolerance. Its annihilator is
not proved invariant under S. Thus the one-sweep estimate cannot be iterated
as though it were a fixed invariant-sector contraction, or relabelled a
uniform vacuum-complement gap. The retained finite moment sector still needs
a useful quantitative bound. Patches still leave arbitrary exterior
coefficients; an isolated-box matrix is not a certificate for them.

Next analytic priority remains original signed-energy control with its
actual error/overlap budget, or the narrower actual auxiliary-state reverse
energy estimate. This result removes a completion obstruction; it supplies
neither that analytic estimate nor spatial/scaling control. A03, full
J02/J03, physical mass calibration, QFT axioms and all-group Clay closure
remain open. No canonical chart node changed.

## Verification

Ten printed gates passed the three final focused file checks, all with
exactly {propext, Quot.sound}. No sorry, new axiom or classical shortcut was
added; no existing sorry was discharged. There is no new assumed analytic
estimate. No full-root, full-tree, broad guard or axiom audit ran. The root
import list includes the new modules but was not separately rebuilt.

All checks used the safe-build skill and monitored launcher, one worker,
20 GiB ceiling, 12 GiB reserve, continuous safety telemetry and 300-second
status cadence. The preflight found 78% free memory and no competing
compiler/runner process. Each check finished in its initial tool call, so
there was no long job to poll. Final logs:

- `/tmp/ym-dense-dual-norm-20260930.log` — one gate.
- `/tmp/ym-completed-monomial-span-20260930.log` — two gates.
- `/tmp/ym-completed-moment-tail-20260930.log` — seven gates.

Sol supplied the dense-dual argument; Luna the completed monomial span;
root the original-action join, compiler fixes and verification. A separate
Sol review found no circularity or scope inflation in the final sources.
No large enumeration, matrix calculation or literature rescan ran.
