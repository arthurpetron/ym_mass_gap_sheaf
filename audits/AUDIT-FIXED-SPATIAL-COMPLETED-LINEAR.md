# Actual completed linear structure, geometry and physical time

Date: 2026-09-16. Classification: PROGRESS after `db24c1a6`.

WHOLE-PROJECT GOAL: nontrivial continuum Yang--Mills on R^4, the required
QFT axioms and a positive physical Hamiltonian mass gap for every compact
simple group, on the SAME theory, within the constructive axiom gate.
This checkpoint is fixed-nome, fixed-width, fixed-cutoff SU(2) progress
for the selected original spatial-probe domain, not that whole target.

## Result and causal argument

The existing original Cauchy carrier now has actual rational vector
operations, a positive-definite rational-bilinear pairing satisfying sharp
Cauchy--Schwarz, and its corresponding squared-distance geometry. The SAME
physical-time maps are linear and contract that distance with constant one.

1. Append and rational coefficient scaling preserve the original physical
   face guards. Their algebra is tested against every physical presentation
   in the SAME intrinsic pairing. Testing against the physical difference
   proves actual null distance; the existing radical theorem proves the
   converse. No different signed lists are equated literally.
2. Expand differences of sums inside that pairing, replace diagonals using
   actual symmetry, and apply the original reflected squared-sum bound.
   This gives d2(x+y,x'+y')<=2*d2(x,x')+2*d2(y,y'). Signed scalar scaling
   gives exactly d2(c*x,c*y)=c^2*d2(x,y), including zero and negative c.
3. These proved bounds instantiate the existing BinaryQuadraticLipschitz
   and ModulusContinuous constructors. Addition's Cauchy modulus is
   max(MX(epsilon/4),MY(epsilon/4)); scaling's is
   MX(epsilon/(c*c+1)). Both are explicit Type-level data. Pointwise pairing
   equality gives zero-modulus closeness, hence algebra on the SAME quotient.
4. Original pairing identities pass through the already constructed scalar
   limits by uniqueness, yielding both-slot bilinearity. Original sharp CS
   passes through those same limits using general multiplication continuity.
   This does not assert CS for individual rational approximation indices.
5. Define the completed squared distance as B(x-y,x-y). It is nonnegative,
   symmetric, zero iff x=y, agrees with the original dense distance, and
   satisfies d2(x,z)<=2*d2(x,y)+2*d2(y,z). Positive definiteness and proved
   additive cancellation establish the zero criterion without choice.
6. Literal physical advance preserves append and scaling. Pointwise null
   descent gives completed linearity, hence subtraction compatibility.
   Apply the existing diagonal contraction to x-y to obtain
   d2(T_n x,T_n y)<=d2(x,y) for the SAME completed time map.

Expansion exposes the actual algebra, tolerance and representative data;
contraction composes those estimates into well-defined operations and
time-compatible geometry. No new analytic premise is introduced.

## Declaration evidence

All paths in this table have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Role |
|---|---|---|
| `addSpan`, `smulSpan`, `PairingEq` | `BF4ExactSlabFixedSpatialIntrinsicLinear.lean:29`, `:33`, `:37` | Original signed operations and actual form tests. |
| `null_of_pairingEq`, `pairingEq_of_null`, `diagonal_congr` | `BF4ExactSlabFixedSpatialIntrinsicLinear.lean:94`, `:101`, `:107` | SAME-distance equivalence and diagonal replacement. |
| `distSq_add`, `diagonal_smul`, `distSq_smul` | `BF4ExactSlabFixedSpatialIntrinsicLinear.lean:254`, `:307`, `:315` | Actual addition bound and signed c-squared identities. |
| `addition`, `scalarContinuous` | `BF4ExactSlabFixedSpatialCompletionLinear.lean:37`, `:41` | Actual modulus-bearing completion maps. |
| `completedAdd`, `completedSmul`, `completedNeg` | `BF4ExactSlabFixedSpatialCompletionLinear.lean:53`, `:57`, `:60` | Operations on the existing physical carrier. |
| `addition_cauchy_modulus`, `scalar_cauchy_modulus`, `closeOfPointwisePairingEq` | `BF4ExactSlabFixedSpatialCompletionLinear.lean:64`, `:69`, `:74` | Retained explicit moduli and zero-rate descent witness. |
| `completedAdd_assoc`, `completedNeg_add`, `completedSmul_mul`, `completedSmul_congr` | `BF4ExactSlabFixedSpatialCompletionLinear.lean:93`, `:115`, `:137`, `:165` | Actual completed algebra, including rational setoid congruence. |
| `representativeInner_add_left`, `representativeInner_smul_left` | `BF4ExactSlabFixedSpatialCompletedBilinear.lean:41`, `:56` | Original linear identities through the same scalar limits. |
| `completedInner_add_left`, `completedInner_add_right`, `completedInner_smul_left`, `completedInner_smul_right` | `BF4ExactSlabFixedSpatialCompletedBilinear.lean:67`, `:73`, `:79`, `:85` | Both-slot rational bilinearity. |
| `completedInner_cauchySchwarz`, `representativeDist_converges` | `BF4ExactSlabFixedSpatialCompletedGeometry.lean:46`, `:77` | Actual CS and original distance limit. |
| `completedDist`, `completedDist_embedSpan`, `completedDist_zero_iff`, `completedDist_triangle` | `BF4ExactSlabFixedSpatialCompletedGeometry.lean:68`, `:83`, `:112`, `:148` | Completed squared distance, dense pin and separating geometry. |
| `completedTime_additive`, `completedTime_smul`, `completedTime_sub`, `completedDist_time_contraction` | `BF4ExactSlabFixedSpatialCompletedLinearTime.lean:55`, `:70`, `:95`, `:104` | SAME physical-time linearity and constant-one distance contraction. |

Only the generic scalar tolerance is reused from
`BF4ExactSlabPlaquetteCompletionLinear.lean:55` (`scalarTolerance`), and
generic real multiplication continuity from the existing Z4-named module.
No old concrete plaquette form, carrier or operator is substituted.

## Next producer and precise constructive boundary

The next bounded producer is actual real scaling with SUPPLIED Cauchy
moduli. The source template
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteRealScalarCauchy.lean:160`
(`realScalarCauchy`) returns the stream (s.approx n)*X.seq n. Its rate at
`:115` (`realScalarRate`) uses a computed scalar tail ceiling and the
vector's computed norm ceiling. It is not yet instantiated for this new
physical carrier. Scalar congruence and descent use pairing equality and
positive definiteness in the template
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedRealScalar.lean:74`
(`realScalarCauchy_congr`) and `:84` (`completedRealSmul`).

The immediate consumer is a projection onto the actual fixed unit, followed
by centering. The original carrier already supplies its pairing coefficient
with explicit QCauchy data:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPairingLimit.lean:121`
(`representativeInnerCauchy`). The old-model templates are
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteUnitProjection.lean:61`
(`unitProjectionCauchy`), `:78` (`unitProjection`), and
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteCenteredCompletion.lean:156`
(`centered_inner`). Their original-spatial counterparts remain unproved.
The intended consumer is SAME-object connected correlations, not a claim
that the fixed unit is an isolated vacuum.

An independent completeness route must retain its actual hypotheses.
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteCauchyRows.lean:47`
(`CauchyRows`) takes a sequence of supplied Cauchy representatives plus an
outer modulus. Its `rowLimit` at `:98` and `rowLimit_independent` at `:146`
do not select representatives of an arbitrary quotient-valued sequence.
Likewise, the real-scalar template requires Type-valued QCauchy data and
does not extract it from legacy CReal.cauchy's propositional existence.
No unrestricted real-scalar action or full metric-completeness theorem is
claimed by this checkpoint.

Full gauge-observable completeness, Hilbert/OS reconstruction, nonconstant
excitations, isolated vacuum, a strict vacuum-complement form bound,
joint cutoff/time and spatial/spacing limits, continuum QFT and the
physical Hamiltonian gap for every compact simple group remain open.
The constant-one time contraction is not a beta-uniform strict gap.
No canonical field, literal hole, axiom or analytic assumption changed.

## Focused verification

Five modules passed focused monitored checks, serialized with one worker
and a 20 GiB hard ceiling, each preceded by fresh process/swap inspection.
All 77 public gates stay within {propext, Quot.sound}. Final logs contain
no errors, warnings, sorryAx or classical dependencies. The initial dense
check hit three elaboration timeouts; explicit typed intermediates repaired
them without changing mathematical statements or raising resource options.
No root/full-tree check or full axiom audit was run. Five imports were added
to the selective root; that is not a root-build claim.

| Module suffix | Gates | `/tmp/<full module name>.log` SHA-256 |
|---|---:|---|
| `IntrinsicLinear` | 23 | `928765e310779f8793628e774b3a196ba0947caf49c1df2499d7a53439ef76ae` |
| `CompletionLinear` | 21 | `bf51c01b953763173db293c1f1ee5d2bf75cf896c8d38aea22dc03cdba9b50d9` |
| `CompletedBilinear` | 8 | `a42b8889be6d4f55bef492f43c4be79d9757a16106aefbf3ed15025bb79e5d23` |
| `CompletedGeometry` | 19 | `3c78cf73f95787381c5b9814232c479a898a299fbff8c53296bd88b4b25c900a` |
| `CompletedLinearTime` | 6 | `cbccdbf82b414d0723c876cddc61af6f21a87b12889c5d7c833c833dc0cb6673` |

Each suffix has prefix BF4ExactSlabFixedSpatial. Independent source review
found no same-object substitution, representative selection, approximation-
index CS claim or completeness overstatement. Parallel agents worked on
disjoint files and reviews; only the main agent compiled, serially.
CI and capacity limits are unchanged. No literature scan was performed;
the saved math-ph report and its 12-hour cadence were reused.
