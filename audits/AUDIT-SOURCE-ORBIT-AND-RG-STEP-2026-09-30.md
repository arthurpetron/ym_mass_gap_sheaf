# Step back: source-orbit control and the direction of an RG estimate

Date: 2026-09-30 UTC. Source checkpoint: `da3962f`.
Whole-project goal: constructive continuum Yang--Mills on R^4 for every
compact simple group, with same-theory QFT axioms, nontriviality and a finite
positive physical Hamiltonian gap. OPEN.

This is a source/research review and a hand-derived mathematical obstruction,
not a new Lean proof. No `.lean` file, sorry, axiom, frontier field or chart
marker was changed. No compiler or heavy computation ran.

## 1. The useful distinction is a whole source orbit, not just its seed

The new normalized budget remains the immediate consumer:
`lean/YMGap/Continuum/BF4ExactSlabChebyshevBudgetCovariance.lean:96`,
`finiteCovariance_sq_bound_of_finite_budget`. At order n it requires the
test for that SAME order and centered original source. A successful test at
one order does not supply tests at subsequent orders.

Current actual inputs, checked by reading their definitions and premises:

| Input | Declaration and location | What it supplies / does not supply |
| --- | --- | --- |
| Original all-state, volume-uniform coercivity at nome 1/40 | `expandedNome_centered_coercivity`, `lean/YMGap/Continuum/BF4ExactSlabFacePatchUniformCoercivity.lean:161`; `coupled_auxiliary_reverse_energy`, same file:205 | Controls every actual auxiliary order at this fixed nome; not a changing-spacing family. |
| Original supported auxiliary bound at every nome | `coneBudget`, `lean/YMGap/Continuum/BF4ExactSlabLocalAuxiliaryCoercivity.lean:45`; `localCoefficient`, same file:49; `auxiliary_coercivity`, same file:74 | Explicit degree-dependent cost; the resulting multiplier approaches ONE, not zero. |
| Obstruction to that local coefficient | `factor_approaches_one`, `lean/YMGap/Continuum/BF4ExactSlabLocalChebyshevObstruction.lean:203` | An obstruction to the ESTIMATE, not to actual Yang--Mills decay. Allowing negative margin alone supplies no improved value. |
| All-nome finite-volume estimate | `factor_approaches_one`, `lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeChebyshevObstruction.lean:169` | The explicit multiplier approaches one as extent grows in the stated degree window. |
| Physical Wilson moments | `evenMoment`, `lean/YMGap/Continuum/BF4WilsonAllNomeCenteredMoments.lean:55`; `mixedMoment`, `lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectMoments.lean:250` | Moments of physical time T, NOT moments of the ordinary conditional sweep B=W*W. No substitution is justified. |

A source-specific, degree-uniform success theorem for the ordinary B budget
at changing coupling was NOT FOUND in these modules, the normalized-budget
modules, `BF4ExactSlabChebyshevFiniteTest.lean`,
`BF4ExactSlabChebyshevRepresentative.lean`, or
`BF4ExactSlabFiniteVolumeReverseEnergy.lean`. This is a bounded source search,
not a claim that every declaration in the repository was audited.
The exact nome is `expandedNome`,
`lean/YMGap/Continuum/BF4ExactSlabFacePatchGeneratorBound.lean:71`;
`expandedNome_margin_separation` (line 80) checks its positive new margin.

### Why a first-moment floor cannot repair the missing quantifier

Here is an elementary rational family, NOT a Yang--Mills example and NOT a
new kernel-checked result. On a two-dimensional block let

    P = diag(1,0),    v_m = ((m^2-1)/(m^2+1), 2m/(m^2+1)),
    Q_m = v_m v_m^t,  W_m = Q_m P,  B_m = W_m^t W_m,
    lambda_m = ((m^2-1)/(m^2+1))^2,   x = (1,1),   m >= 2.

Both P and Q_m are orthogonal projections, and B_m=diag(lambda_m,0).
Thus 0<lambda_m<1: there is no fixed vector on this block. Adjoining a
separate one-dimensional common fixed block supplies a vacuum orthogonal to x.
Nevertheless

    <x,(I-B_m)x>/||x||^2 = (2-lambda_m)/2 >= 1/2.

For any fixed rational c>2 and order n, put d=T_n(c-1)>0. The actual
normalized polynomial has squared norm ratio

    ||T_n(c B_m-I)x/d||^2 / ||x||^2
      = (T_n(c lambda_m-1)^2+1)/(2*d^2).

This can remain above 1/4 at arbitrarily large n despite the uniform seed
floor 1/2. Explicitly, write the finite rational polynomial
T_n(c z-1)=sum_j a_j z^j and L=sum_j j*|a_j|. For 0<=lambda<=1,
the finite identity 1-lambda^j=(1-lambda)*sum_{i<j}lambda^i gives

    |T_n(c lambda_m-1)-d| <= L*(1-lambda_m) <= 4*L/m^2.

Choose an integer m>=2 with m^2>=16*L/d. Then the ratio is at least
9/32>1/4. This is a finite rational choice, not an appeal to an unspecified
limit. Consequently the seed floor and projection-product structure alone
cannot imply a factor tending to zero UNIFORMLY over this family. Each fixed
m may still have its own decaying rate. The missing datum controls the slow
component throughout the actual source orbit, not merely its initial energy.

## 2. Targeted multiscale-paper check

[Faizal--Shabir, arXiv:2606.19362v1](https://arxiv.org/pdf/2606.19362)
does not supply an importable gap producer in the passages checked:

- After (5.23), printed p.50, mixed-cell PAIRS are treated as a principal
  submatrix and declared positive. An off-diagonal mask is not a principal
  compression.
- (11.3) is a lower operator bound; (11.5), printed p.129, uses an upper bound.
- Theorem 5.6, printed p.55, needs total loss SMALLER than the initial gap;
  finiteness alone is insufficient.
- Appendix D, Proposition D.2 and Corollary D.5, instead give a conditional
  fixed-physical-time comparison with an upper error bound and a strict
  anchor budget. That is a different hypothesis, not a repair of (11.3).

Independent finite checks of the first two implications: the positive matrix
[[1,1/2],[1/2,1]] has mixed mask [[0,1/2],[1/2,0]], whose quadratic value
on (1,-1) is -1. Also S=diag(1,3/4)>=T=diag(1,1/2), with the SAME unique
vacuum and zero lower-bound defect, but S has the smaller gap. Both are
strictly positive contractions. Neither example is Yang--Mills.

Decision: import no gap theorem or defect estimate. The review was targeted,
not another math-ph listing scan. Key displayed pages were visually checked;
an independent Sol reviewer confirmed the defects.

## 3. Reuse the existing backward requirement; do not add a new interface

The repository already distinguishes refinement from coarse blocking:
`MassNormalizedRefinementFlow`,
`lean/YMGap/Continuum/MassNormalizedRefinementPersistence.lean:36`.
Its `rateLoss` (line 56) divides the logarithmic defect by the NEXT spacing;
`MassNormalizedRefinementPersistence` (line 117) explicitly requires
`anchorDominates`. `floorWitness_le_mass` (line 134) consumes the complete
budget. None of these data is an actual Yang--Mills scaling producer.

For a possible fixed-physical-time alternative, the elementary target is
an UPPER quadratic comparison between vacuum-preserving realizations of
exp(-tau H_k), at the SAME tau. If their complementary norm bounds are q_k
and q_(k+1)<=q_k+e_k, a complete error cap E<1-q_0 gives q_k<=q_0+E<1.
At changing one-step times, this argument is unavailable without time-power
and spacing calibration. Positivity of each transfer does not order their
difference. This observation supplies no comparison map or estimate here.

## 4. Execution change and next bounded test

1. Keep the normalized original-source budget as the forward target, but
   reject seed-only variance/Dirichlet bounds as proposed long-orbit producers.
   A candidate must control actual iterates at increasing order, with its
   coupling, cutoff and extent dependence visible. First test its stated
   quantifiers against the rational family above before formalizing it.
2. For a multiscale candidate, first write the ORIGINAL signed quadratic
   defect at matched physical time and retain mixed terms. Seek an upper
   bound whose complete cost fits below the anchor; neither an off-diagonal
   Gram mask nor mere summability pays this cost. Reuse the existing
   mass-normalized consumers if using variable one-step times.
3. Do not build another finite evaluator, conditional-budget wrapper, or
   extrapolation from the 1/40 certificate until it provides one of those
   estimates. Do not identify B with physical T. A dense-source/OS join,
   survival, finite positive physical mass, QFT structure and every-group
   construction remain open.

The review changes which proposed analytic inputs are worth pursuing; it
closes no canonical proof node. The canonical ASCII chart stays unchanged
and is not reprinted. Verification: source inspection, elementary hand
algebra, targeted paper review and independent review only; no Lean build,
full-tree audit, numerical certificate or continuum theorem.
An independent Sol reviewer checked the rational source family, its explicit
finite choice of m and the uniform-over-family quantifier. Luna supplied the
bounded declaration search, with the cited statements re-read by the main agent.
