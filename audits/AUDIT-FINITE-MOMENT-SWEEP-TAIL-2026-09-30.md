# Finite original-weighted moment criterion for the conditional-sweep tail

Date: 2026-09-30 UTC. Whole-project goal remains OPEN: constructive continuum
Yang--Mills on R^4 for every compact simple group, with full same-theory QFT
axioms and a strictly positive finite physical Hamiltonian mass gap.

## New theorem and its exact scope

For rational 0<w<1, finite extent, K>=headCutoff(w), and epsilon>0, let N be
the previously returned `sweepCutoff w extent epsilon`. The code now returns
a finite monomial list M depending on w,K,extent,N. For EVERY polynomial p
supported on the original slab links, if the exact finite Boolean test

`for every m in M: originalWeightedPair(p, unitMonomial(m)) = 0`

passes, then the TRUE original conditional sweep S satisfies

`||S(embed p)||_F^2 <= epsilon * ||embed p||_F^2`.

There is no degree bound on p. The original full action supplies every
moment and both norms. F is its existing weighted GNS datum, not a new
reference measure. S remains auxiliary conditional L2 dynamics, NOT OS
time. The statement applies to supported dense inputs passing the check,
not all centered states or arbitrary completed states.

## Causal proof

1. The finite inverse iteration commutes with multiplication by the ACTUAL
   normalizer. Symmetry of that multiplier proves symmetry of each finite
   inverse iterate in the detached background form.
2. The actual inserted-numerator pairing transfers symmetry to the PURE
   conditional polynomial update in the ORIGINAL full-action form. No
   original collar, normalizer or shared spectator is discarded.
3. For the head-first polynomial sweep A, reversing the schedule gives
   its exact adjoint A*: `B(Ap,q)=B(p,A*q)`. Every original coordinate is
   visited by the reversed schedule too, so A*q has a computed degree
   budget independent of q.
4. `monomials` enumerates literal exponent lists of length at most 4B,
   including shorter presentations. Each coordinate is bounded by its
   block's ceiling. This over-enumeration covers every monomial obeying
   the block-total degree budget; it need not be an independent basis.
5. Finite weighted monomial vanishing implies vanishing against every
   polynomial covered by the list. Apply it to q=A*Ap:
   `B(Ap,Ap)=B(p,A*Ap)=0`. Thus Ap is null in the ORIGINAL weighted radical.
   Repeated monomials and sphere identities remain allowed.
6. The independently proved all-input approximation estimate
   `||S(embed p)-embed(Ap)||^2 <= epsilon*||embed p||^2` supplies the claim.

The adjoint proof also establishes that equal bounded-degree dual pairings
give equal polynomial-sweep outputs modulo the original radical. It does
not construct an inverse map from moment coordinates to a chosen polynomial.

## Declaration evidence

Paths below are relative to `lean/YMGap/Continuum/`.

| Declaration | File:line | Role |
| --- | --- | --- |
| `approximateInverse_commutes_normalizer`, `approximateInverse_symmetric` | `BF4ExactSlabPolynomialConditionalAdjoint.lean:48`, `:72` | Actual finite inverse algebra. |
| `conditionalApproximation_symmetric` | `BF4ExactSlabPolynomialConditionalAdjoint.lean:119` | Original full-action weighted symmetry. |
| `polynomialSweep_adjoint_reverse` | `BF4ExactSlabPolynomialSweepAdjoint.lean:62` | Exact dual operator, not a surrogate transpose. |
| `dualDegreeBudget`, `reverseSweep_degree_bound` | `BF4ExactSlabPolynomialSweepAdjoint.lean:73`, `:76` | Returned dual degree budget covering all test inputs. |
| `polynomialSweep_null_of_dual_orthogonal`, `polynomialSweep_rad_of_dual_pairings` | `BF4ExactSlabPolynomialSweepAdjoint.lean:86`, `:101` | Null tail and exact radical factorization through dual pairings. |
| `monomials`, `mem_monomials_of_degree`, `length_le_of_mem_monomials` | `SU2QuaternionBoundedMonomials.lean:37`, `:100`, `:133` | Executable finite enumeration, completeness and support. |
| `weightedPair_zero_of_test_list` | `QuaternionHaarWeightedMonomialSpan.lean:99` | Exact finite span consequence without Gram inversion. |
| `dualMonomials`, `momentZeroCheck` | `BF4ExactSlabFiniteMomentTail.lean:47`, `:53` | Returned actual test list and Boolean checker. |
| `dualMonomials_supported`, `dualMonomials_cover` | `BF4ExactSlabFiniteMomentTail.lean:60`, `:74` | Every test is supported and every dual output is covered. |
| `polynomialSweep_null_of_check` | `BF4ExactSlabFiniteMomentTail.lean:98` | Checked finite moments annihilate approximant in weighted radical. |
| `physicalSweep_tail_bound` | `BF4ExactSlabFiniteMomentTail.lean:120` | Actual conditional sweep on all checked supported inputs. |

## What remains open

- The remaining finite moment sector has no new strict bound. No actual
  strict Gram certificate or nonzero input passing the moment test was
  produced. The theorem proves soundness for every supplied passing input.
- Exact zero-moment membership is not automatically preserved by dense
  approximating sequences. No completed-space version of this tail predicate
  or completed finite-rank approximant was constructed.
- The moment list depends on nome, heat cutoff, extent and requested error;
  no parameter-uniform finite-dimensional core or practical complexity bound
  is asserted. A uniform epsilon conclusion on a CHANGING checked input class
  is not a beta-uniform gap on the vacuum complement, including for U(1).
- No useful local-to-global signed estimate, scaling family, same-object OS
  passage, physical mass calibration, continuum QFT or all-group closure.
  A03, full J02/J03 and the canonical chart's displayed states remain open.

## Source review: the patch-to-global consumer is still missing

No fixed-size-patch gap to whole-volume coercivity declaration was found in
the reviewed original conditional-sweep route. Searched modules include
`GNSProjectionSweepSparseRow`, `GNSProjectionSweepEnergy`,
`BF4ExactSlabConditionalSweepEnergy`, `BF4ExactSlabFiniteVolumeCoercivity`,
`BF4ExactSlabCompletedFiniteVolumeCoercivity`,
`BF4ExactSlabFiniteVolumeReverseEnergy`,
`BF4ExactSlabSmallNomeUniformCoercivity`, and
`BF4ExactSlabChebyshevFiniteTest`. A name search under `lean/YMGap/Continuum`
also found no Knabe/detectability theorem. This is a source-search boundary,
not a mathematical impossibility claim.

- `BF4ExactSlabConditionalSweepEnergy.lean:71`,
  `final_energy_le_625_loss`, bounds final energy FROM ABOVE by sweep loss.
  It is not a patch-derived coercivity lower bound.
- `BF4ExactSlabFiniteVolumeReverseEnergy.lean:156`,
  `reverse_energy_of_coercivity_at_balanced`, consumes a supplied original
  coercivity estimate at the actual whole-schedule balanced output.
- `BF4ExactSlabSmallNomeUniformCoercivity.lean:62`,
  `volume_uniform_centered_coercivity`, is an existing alternative producer,
  retaining heatRatio<=1/2, heatRemainderBound<1 and its positive-margin guard.
- `BF4ExactSlabChebyshevFiniteTest.lean:115`,
  `reverse_energy_of_finite_test`, certifies one actual whole-schedule
  auxiliary vector using a computed lower bracket; it is not a patch lift.
- `FiniteRationalLDLCertificate.lean:161`, `finiteLDLCheck`, and `:255`,
  `finiteMatrixQuadratic_nonnegative_of_ldl_check`, are available exact
  matrix witness checks. No actual core matrix/factorization for the new
  sweep is supplied by the present increment.

Accordingly, establish the actual finite-core/global analytic consumer
before launching expensive certificate calculations. The finite-tail result
does not justify a whole-volume matrix computation as the next automatic step.

## Verification

Twenty-three printed gates passed five focused checks, within
{propext, Quot.sound}. No new sorry, axiom, classical shortcut or analytic
premise; no existing sorry discharged. No full-root/full-tree/audit/guard
run. The root import list was updated without claiming a broad rebuild.

All checks used the safe-build skill and monitored launcher with one worker,
20 GiB worker ceiling, 12 GiB reserve and continuous safety telemetry.
Checks finished in their initial tool calls; no long job was repeatedly
polled. No large monomial list or matrix was evaluated. Final local logs:

- `/tmp/ym-polynomial-conditional-adjoint-20260930.log` — 3 gates.
- `/tmp/ym-polynomial-sweep-adjoint-20260930.log` — 7 gates.
- `/tmp/ym-bounded-monomials-20260930.log` — 4 gates; unused-simp warnings only.
- `/tmp/ym-weighted-monomial-span-20260930.log` — 2 gates.
- `/tmp/ym-finite-moment-tail-20260930.log` — 7 gates.

Sol proved local symmetry and reviewed the joined argument; another Sol
proved finite weighted span algebra and reviewed the missing global consumer;
Luna supplied enumeration; root proved reverse adjoint and the actual tail
consumer. Cached literature findings were reused without a new listing scan.
