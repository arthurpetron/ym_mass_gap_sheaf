# Exact discrete inverse on the SAME reflected unit complement

Date: 2026-09-24 UTC. The continuum Yang--Mills/Clay target remains open.

## What is constructed

For the existing `JointCompletion hw0 hw1 width`, its actual inner product B,
unit U, and discrete transfer T, define R(x)=x-T(2)x. The new `inverse` is a
function on this SAME quotient satisfying:

    B(inverse x,U) = 0
    R(inverse x) = center x
    R(inverse x) = x                  when B(x,U)=0
    inverse(R(x)) = x                when B(x,U)=0.

The representative-level algorithm uses finite even-time orbit sums and the
new explicit represented completeness. Uniqueness makes the output respect
the original quotient relation, permitting `Quotient.lift`. There is no choice
of representatives and no assumption that arbitrary quotient-valued Cauchy
sequences can be lifted.

The map is representative-independent. Its explicit approximation modulus and
computed norm ceiling are supplied relative to a representative X; no
quotient-invariant computable ceiling/modulus is extracted from an opaque x.

## Causal proof

1. `BF4ExactSlabFixedSpatialJointOrbitCauchy.evenOrbitRep` computes a
   representative for every original finite sum S_n=sum_(i<n) T(2i)x;
   `mk_evenOrbitRep` pins its quotient to the pre-existing `evenOrbitSum`.
   Exact ordered differences are the literal finite tails.
2. `even_cross_term_le` bounds each B(T(2i)x,T(2j)x) by q^(i+j)B(x,x), using
   time balance and actual norm decay. No mixed term is discarded.
3. `BF4ExactSlabFixedSpatialJointOrbitTailBound.evenOrbitTail_geometric_norm_le`
   proves

       B(tail(p,l),tail(p,l)) <= (q^p*geomSum(q,l))^2 B(x,x).

   Here `geomSum` is the exclusive partial sum from `HeatKernelRGStep`.
   Explicit equivalences relate its `RGTransport.qpow` to actual Q' powers.
4. `BF4ExactSlabFixedSpatialJointNeumannCauchy.orbitNormCauchy` uses
   C_X=normCeiling(X)/(1-q)^2 and the rate `geometricCutoff q C_X epsilon`.
   This bounds squared distance between late finite sums. The q=0 case starts
   at index one; there is no division by q or by the source norm.
5. `BF4ExactSlabFixedSpatialJointResidualPresentedLimit.mapResidual_limit`
   proves actual residual continuity. Its epsilon/8 input tolerance pays for
   the representative-limit comparison and squared-triangle estimate.
6. `BF4ExactSlabFixedSpatialJointNeumannInverse.sourceCandidate` consumes the
   old `JointRangeApproximation.evenOrbitSum_error_small`: the original source
   is the limit of residuals. Uniqueness of represented limits proves
   `orbitLimit_residual` as exact vector equality.
7. `exactPreimage` applies the existing center projection. It commutes with
   R and fixes the centered source. `residual_injective_on_complement` reduces
   uniqueness to the already proved absence of centered T(2)-fixed vectors.
8. `inverse` descends this algorithm to quotient states; `inverse_residual`,
   `inverse_right`, and `inverse_left` prove the displayed equations.

All new modules are under `lean/YMGap/Continuum/`. No extra analytic hypothesis
is supplied: q<1 is the existing fixed-width theorem, normCeiling is computed
from the supplied representative, and the finite tail bound is proved here.

## Bounded-inverse follow-up

The subsequent `BF4ExactSlabFixedSpatialJointNeumannAlgebra.lean` proves
`inverse_add`, `inverse_smul`, `inverse_sub`, `inverse_time`, and
`inverse_selfAdjoint` by residual uniqueness and symmetry. Scalars in these
linearity statements are rational; no real/complex linearity is asserted.

`BF4ExactSlabFixedSpatialJointNeumannBound.lean` defines the explicit
`inverseNormConstant` g=1/(1-q), with q=`twoStepRate(hw0,hw1,width)`.
`residual_form_bound` is the actual coercive form estimate. For a centered z,
put N=B(z,z), P=B(z,Rz), M=B(Rz,Rz). Scaling coercivity gives N<=gP.
The nonnegative square B(z-gRz,z-gRz)=N-2gP+g^2 M gives
2gP<=N+g^2 M. Thus 2N<=N+g^2 M, and additive cancellation gives N<=g^2 M.
Both mixed terms remain; no vector norm is divided by or tested for zero.

`inverse_norm_centered_bound` applies this to the constructed inverse:

    B(inverse x,inverse x) <= g^2 B(center x,center x) <= g^2 B(x,x).

`inverse_distance_bound` combines it with `inverse_sub` on actual quotient
states. `preimage_error_bound` bounds the distance from any centered y to
inverse(x) by g^2 times the squared distance from R(y) to center(x). This is
the concrete residual-error certificate consumer, with no new analytic input.

The constant is independent of source and representative, NOT of nome or
width. The q=0 case is included; g deteriorates as q approaches one. The
presentation-relative construction moduli are not replaced by a quotient
representative-selection algorithm. A separate mathematical review checked
the square argument and these exact scope boundaries.

Two serialized 4 GiB leaf checks passed:

- `/tmp/ym-gap-joint-neumann-algebra-check-3.log`: nine permitted gates.
- `/tmp/ym-gap-joint-neumann-bound-check-3.log`: eight permitted gates.

Both checks returned terminal success; all seventeen gates use only
{propext, Quot.sound}, with no errors, warnings or sorryAx in accepted logs.
The semantic root imports the new capstone. No full-root build/audit/guard,
new hole/axiom, or canonical frontier field change occurred.

## Limits of the claim

The construction and moduli retain nome and spatial-width dependence. This
checkpoint now supplies the source-independent squared-norm bound above,
but not a continuous-time generator, a Hamiltonian resolvent or spectral
theorem, spatial/spacing-uniform estimates, a continuum theory, physical mass
calibration, or the construction for every compact simple group.

The primary analytic task remains useful original energy/variance control and
the all-vector gap's spatial/scaling passage; the discrete inverse does not
replace those estimates. Full same-theory QFT/YM-field identification is open.

## Verification

Five serialized leaf checks used `scripts/safe_lean_build.py`, one worker,
and a 4 GiB cap. Accepted logs, all terminal success:

- `/tmp/ym-gap-joint-orbit-cauchy-check-2.log`: six gates.
- `/tmp/ym-gap-joint-orbit-tail-check-4.log`: six gates.
- `/tmp/ym-gap-joint-neumann-cauchy-check-1.log`: four gates.
- `/tmp/ym-gap-joint-residual-limit-check-1.log`: five gates.
- `/tmp/ym-gap-joint-neumann-inverse-check-2.log`: fifteen gates.

All thirty-six gates report only permitted axioms {propext, Quot.sound};
accepted logs contain no error/warning/sorryAx. Independent static review
checked same-carrier identity, the residual-limit argument, centering,
uniqueness and q=0. No new hole/axiom or frontier field change was introduced.
The semantic root imports the capstone. No full-root build/audit/guard ran.
