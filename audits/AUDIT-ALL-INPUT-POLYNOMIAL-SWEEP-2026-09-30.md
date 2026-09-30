# All-input bounded-degree approximation of the original conditional sweep

Date: 2026-09-30 UTC. Whole-project goal remains OPEN: constructive continuum
Yang--Mills on R^4 for every compact simple group, with same-theory QFT
axioms and a strictly positive finite physical Hamiltonian mass gap.

## New mathematical result

Fix rational 0<w<1, finite extent and K>=headCutoff(w). Let F be the existing
original full-action weighted GNS datum, and S its existing eight-color
conditional sweep on the completion. For every positive rational epsilon,
the code returns an iteration count N and a polynomial map A such that,
for EVERY supported polynomial p,

`||S(embed p) - embed(A p)||_F^2 <= epsilon * ||embed p||_F^2`.

The SAME N works for arbitrary input degree and norm, including zero norm.
Each original quaternion block b of A p has degree at most the computed
`degreeBudget w K extent epsilon b`, independently of p. N depends on
w, extent and epsilon, not K or p; the degree budget still depends on K.

This proves approximation error and bounded output degrees, NOT a completed
finite-rank operator or a finite-matrix strict gap. No finite certificate
has been generated or checked. S is conditional L2 dynamics, NOT the OS
transfer operator.

## Why the input degree disappears

Each update uses the PURE conditional prediction: apply the existing
finite inverse-normalizer iteration to the original inserted numerator.
The numerator and normalizer have both been integrated over the selected
block, so every iterate is independent of that block. Later updates
reintroduce that degree only through their fixed original collar and
normalizer polynomials. At iteration n, their cost in block b is

`deg_b(collarHeat) + n * deg_b(normalizer)`.

Once a block has been selected, its original input degree is gone; only
the later costs remain. The literal physical schedule covers every block.
The finite sum of all schedule costs is a safe, input-independent bound.

This argument would fail for `p - approximateResidual p`: its residual
normalization error can retain a high-degree multiple of the original p.
The proof does not use that map.

## Uniform error calculation

For a block with original collar floor L>0 and ceiling U>0, finite inverse
coercivity bounds inverse-row distance by residual-row distance divided
by L^2. The triangle estimate and the original-action norm comparison give
coefficient `4*U*eta/L^2`, where eta is the existing relative residual
tolerance. Passing the row bound to the explicitly constructed completed
conditional projection preserves this inequality.

The internal tolerance is the returned rational
`eta = delta*L^2*oneOver1p(4*U)`. The proved reciprocal budget makes its
coefficient <=delta. `projectionCutoff w size delta` is the existing
geometric relative cutoff evaluated at eta; it does not depend on p, K
or extent. The singleton block projection equals the actual star projection
used by S, on the SAME completed carrier.

For a finite schedule of length m, single-update squared error <=delta
times input squared norm, with 0<delta<=1, gives approximate-update squared
norm <=4 times input norm. The sweep error is at most
`delta*c_m*||p||^2`, where `c_0=0`, `c_(m+1)=2+8*c_m`.
The computed choice
`delta=(epsilon*oneOver1p(epsilon))*oneOver1p(c_m)` is positive, <=1 and
satisfies delta*c_m<=epsilon. This is an approximation-precision budget,
not a physical decay rate. It can be very expensive as extent grows.

## Declaration evidence

Paths below are relative to `lean/YMGap/Continuum/`.

| Declaration | File:line | Role |
| --- | --- | --- |
| `DegreeLE`, `degreeBound` | `SU2QuaternionBlockDegreeBound.lean:40`, `:35` | Literal finite term-degree ceiling and computed bound. |
| `DegreeLE.mul`, `project_degree`, `familyProject_degree` | `SU2QuaternionBlockDegreeBound.lean:95`, `:120`, `:140` | Products add degree; Haar integration does not increase it. |
| `approximateInverse_degree`, `conditionalApproximation_degree` | `BF4ExactSlabPolynomialSweepDegree.lean:54`, `:81` | Actual inverse-iterate and collar degree costs. |
| `polynomialUpdate_selected_degree_zero` | `BF4ExactSlabPolynomialSweepDegree.lean:100` | Exact selected-coordinate erasure. |
| `physicalSweep_degree_bound` | `BF4ExactSlabPolynomialSweepDegree.lean:154` | Full physical coverage removes all input-degree dependence. |
| `conditionalProjection_error_relative` | `BF4ExactSlabBlockConditionalApproximationError.lean:255` | Original completed projection error with explicit coefficient. |
| `projectionTolerance`, `projectionCutoff` | `BF4ExactSlabBlockConditionalApproximationError.lean:105`, `:111` | Returned inverse precision and common cutoff. |
| `conditionalProjection_error_tolerance` | `BF4ExactSlabBlockConditionalApproximationError.lean:304` | Requested delta times the original input squared norm. |
| `errorCoefficient`, `stepTolerance` | `GNSFiniteSweepApproximation.lean:102`, `:119` | Computed sweep amplification and one-step tolerance. |
| `Family.approximateSweep_norm_le`, `Family.sweep_approximation_uniform` | `GNSFiniteSweepApproximation.lean:263`, `:382` | Same-carrier sweep norm/error propagation. |
| `polynomialUpdate_error` | `BF4ExactSlabPolynomialSweepApproximation.lean:64` | Singleton identity pins to original star operator. |
| `sweepCutoff`, `approximation` | `BF4ExactSlabPolynomialSweepApproximation.lean:105`, `:126` | Actual returned all-input approximant. |
| `approximation_error`, `approximation_degree` | `BF4ExactSlabPolynomialSweepApproximation.lean:130`, `:144` | The joined error and degree claims. |

## Exact open residue and route decision

- Finite-span representation, linear factorization and descent through the
  original weighted radical have not been constructed here. Neither has
  the bounded approximant been extended to every completed input.
- A useful finite weighted Gram strict bound is still missing. Bounded
  output degree does not justify testing only bounded-degree INPUTS; the
  actual input functionals/adjoints must also be certified.
- Practical certificate cost, an exterior-uniform local certificate and
  its global signed-energy consumer remain open. Do not launch a
  whole-volume Gram computation merely because the degree is finite.
- No uniform degree as K tends to infinity, useful volume-independent
  sweep budget, scaling family, signed spatial estimate or physical-time
  identification follows. A03, full J02/J03 and all Clay obligations remain
  open. The canonical chart's displayed states did not change.

The preceding volume-cost Chebyshev obstruction remains in force. This
route supplies a genuine omitted-input approximation prerequisite; it
does not rescue that coefficient or turn auxiliary dynamics into OS time.

## Verification and parallel work

Five final focused checks passed with 50 printed axiom gates, all within
{propext, Quot.sound}. No sorry, new axiom or analytic assumption was added;
no existing sorry was discharged. The root import list was updated, but
no full-root/full-tree/audit/guard build was run or claimed.

Each command used `scripts/safe_lean_build.py --jobs 1 --status-seconds 300
--check-worker-limit-gib 20 --check <file> --check-output <matching olean>`.
Only one compiler ran at a time with continuous safety telemetry and the
12 GiB reserve. The initial yielded degree check was revisited after other
work, not repeatedly polled; final checks completed in their initial call.

Final local logs (not committed):

- `/tmp/ym-block-degree-bound-20260930.log` — 15 gates.
- `/tmp/ym-polynomial-sweep-degree-20260930.log` — 10 gates.
- `/tmp/ym-block-conditional-error-20260930.log` — 6 gates.
- `/tmp/ym-finite-sweep-approx-20260930.log` — 11 gates.
- `/tmp/ym-polynomial-sweep-approx-20260930.log` — 8 gates.

Luna supplied degree algebra and reviewed the erasure argument; Sol supplied
the block error, another Sol supplied generic sweep control, and root proved
the actual degree-erasing sweep and same-object join. Sol independently
reviewed the final quantifiers and operator pin. No routine literature
rescan was performed inside the existing 12-hour cache interval.
