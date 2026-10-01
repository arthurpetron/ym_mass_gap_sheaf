# Quartic heat coefficients and finite block tail

Date: 2026-10-01 UTC. The previously reviewed bulk coefficient estimate and
finite block-tail bound are now kernel-checked. An exact finite character
expansion is also checked, without regrouping or dropping cutoff terms.
These supply scalar and algebraic ingredients for the quartic correction
in the original radial Wilson increment. They do not yet bound that moment
under the interacting source or compare it with SAME centered variance.
The physical scaling and continuum Clay target remain open.

## Actual bulk coefficient and explicit coupling dependence

Write a_j=(j+1)*w^(j*(j+2)), h=1-w, n=k+3. The definition
`SU2HeatQuarticBulkCoefficient.quarticBulkCoeff`
(`lean/YMGap/Continuum/SU2HeatQuarticBulkCoefficient.lean:32`) is

    b_(k+2) = 6*a_(k+2)-4*(a_(k+1)+a_(k+3))+a_k+a_(k+4).

`quarticBulkCoeff_factor` (same file, line 196) proves

    b_(k+2) = w^(k*(k+2))*P(n,w^(2*k+3),w^2),

where P is the existing signed polynomial. This is an identity of the
ACTUAL `BondMovingStep.coeffW` values, not a newly supplied coefficient
family. It is untruncated: its identification with a regrouped interior
coefficient of a finite prefix still requires k+4<=K and the reindexing proof.

`SU2HeatQuarticNomeBudget.nome_polynomial_le_budget`
(`lean/YMGap/Continuum/SU2HeatQuarticNomeBudget.lean:151`) specializes the
six-positive-term majorant by Bernoulli to prove, for 0<=w<=1,

    P(n,w^(2*k+3),w^2) <= 148*n*h^2 + 16*n^5*h^4.

`quarticBulkCoeff_le_nome_budget`
(`lean/YMGap/Continuum/SU2HeatQuarticBulkCoefficient.lean:277`) retains the
factor w^(k*(k+2)). `coeffW_center_factor` (line 289) and
`quarticBulkCoeff_le_relative` (line 351) give the sharper useful form

    b_(k+2) <= (296*h^2 + 32*(k+3)^4*h^4)*a_(k+2),
    provided 1 <= 2*w^(4*k+8).

All constants are explicit rational data. The guard couples spin and nome;
it is not asserted for every spin or every coupling. This is an upper bound
on a signed coefficient, not an absolute-value estimate or a positivity claim.

## Finite dimension squared tail

`SU2HeatDimensionBlockTail.dimensionTail`
(`lean/YMGap/Continuum/SU2HeatDimensionBlockTail.lean:194`) is

    sum_(s=0)^(M-1) (L+s+1)^2*w^((L+s)*(L+s+2)).

`dimensionTail_le_eight_blocks` (same file, line 199) proves

    dimensionTail(w,L,M) <= 8*L^3*q,
    q=w^(L^2), 0<=w<=1, 1<=L, q<=1/8,

for EVERY natural M, including zero. The bound is uniform in M only;
dependence on w and L is displayed. No physical spacing or volume occurs
in this scalar statement.

The proof groups labels into blocks [rL,(r+1)L), r>=1. Dimension growth
gives (r+1)^2<=4^r, while the Casimir exponent is at least r*L^2.
Each whole block is bounded by L^3*(4*q)^r. The geometric sum with
4*q<=1/2 gives 8*L^3*q. Padding a finite window uses nonnegative terms.
There is no division by q, so the statement includes w=0. The previous
one-index ratio guard is not used.

## Exact finite expansion and its remaining coefficient join

Let chi_j be the original SU(2) character polynomial and r=2-chi_1.
`SU2QuaternionHeatQuarticExpansion.defect_square_basis`
(`lean/YMGap/Continuum/SU2QuaternionHeatQuarticExpansion.lean:120`) proves

    r^2*chi_0 = 5*chi_0-4*chi_1+chi_2,
    r^2*chi_1 = 6*chi_1-4*(chi_0+chi_2)+chi_3,
    r^2*chi_(k+2) = 6*chi_(k+2)-4*(chi_(k+1)+chi_(k+3))
                      +chi_k+chi_(k+4).

`heat_quartic_expansion` (same file, line 196) distributes these identities
over the ORIGINAL `heatPrefix w K x` for every K, including K=0 and K=1.
The result is a coefficient-level polynomial equality with the original
summation order retained. It is not yet a regrouped output-spin formula.
The exceptional basis identities above are proved; the exceptional
heat-coefficient inequalities and boundary payment are not.

## Consumer and exact remaining work

The intended consumer is the quartic correction in
`BF4ExactSlabFixedSpatialWilsonRadialIncrement.wilson_energy_radial_normalized`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonRadialIncrement.lean:154`).
Its complete original edge weight and odd partition must be preserved.
The current increment stops before that insertion estimate.

Next assemble the finite regrouping with zero-extended original coefficients,
prove the low-spin and cutoff-boundary bounds, and apply the guarded bulk and
tail bounds under the original insertion. Existing character positivity and
the full positive-background character bound have distinct hypotheses;
PSD alone does not supply the latter. Their source pins and original
certificate construction are recorded in the preceding audit,
`AUDIT-QUARTIC-MAJORANT-AND-BOND-COMPLETION-2026-10-01.md`.

Even a successful quartic insertion bound leaves the mixed radial moment
versus SAME interacting centered variance and physical time calibration.
The reviewed dyadic nome schedule remains unformalized and is not a
justified physical Yang--Mills scaling trajectory. No spectral, survival,
continuum, all-group or QFT obligation is closed by these four modules.

## Verification boundary

Four final focused file checks passed, with 18 printed gates: three empty
axiom sets and fifteen exactly {propext, Quot.sound}. No sorry, new axiom,
classical shortcut, native_decide or canonical-field weakening was added.
The block-tail check reports two harmless unused-hypothesis warnings.
Only the main agent compiled; parallel agents edited or reviewed source.

Checks used the monitored launcher, one worker, 20 GiB ceiling and 12 GiB
OS reserve. Process preflight found no competing compiler/test/runner;
the latest memory-pressure query reported 89% free. No full root build,
full-tree audit or guard was run. Root imports were added, not root-compiled.
Canonical chart labels and states are unchanged; no chart was reprinted.

Final logs and SHA-256:

- `/tmp/ym-quartic-nome-budget-20261001.log`:
  `0a8a5d55130646e4f0d61b05a217d4402ada346c84c2b0ca65f6d6e2bf15d943`.
- `/tmp/ym-quartic-bulk-coefficient-20261001.log`:
  `052826d6dd8d51246ab02d4f0776d26c9c9704155b2bde8811dfa4590c7ebbdc`.
- `/tmp/ym-heat-dimension-block-tail-20261001.log`:
  `744047f1829d07ac936df3480da9ee60c54f4ca817b41a44031b938536b926ea`.
- `/tmp/ym-heat-quartic-expansion-20261001.log`:
  `fa2d178a5fc8064dcff1f2a26161c3f369d8c903c06b94047059928ced556dd9`.
