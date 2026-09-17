# Stable full-fringe polynomial extraction on the original marginal

Date: 2026-09-17 UTC. Parent checkpoint: `a54d553`.

Whole-project goal: constructive nontrivial continuum Yang--Mills on R^4
for every compact simple group, with same-theory QFT axioms, isolated
vacuum and positive finite physical Hamiltonian gap. This checkpoint is
a finite original-action decomposition estimate, not a mass-gap theorem.

## Constructed objects and exact result

Let F be all inactive kinetic coordinates, P_F their original finite Haar
integration schedule, V the complete spatial weight, g_n=T^n1,
t=T^(n+1)1 and nu=(V*g_n)*t. Define

    m=P_F(V),  M=P_F(V*f),  R=m*f-M,
    J_k=the constructed finite polynomial reciprocal of m,
    r_k=J_k*R,  b_k=J_k*M.

The proved results, for supported f and the existing positivity guards, are

    <r_k,b_k>_nu = 0,
    ||r_k||_nu^2 + ||b_k||_nu^2 = ||(m*J_k)*f||_nu^2 <= ||f||_nu^2,
    ||f-(r_k+b_k)||_nu^2 <= rho^(2k)*||f||_nu^2,
    H[p*T(g_n*r_k)] = 0 for every Haar test p.

The equality and kernel/orthogonality identities do not require positivity.
Positivity is used for the certified multiplier-square and norm inequalities.
The two pieces are explicit finite polynomials; no configuration-space
reciprocal function, noncomputable choice, or completed projection is assumed.

## Checked declaration map

| Result | Declaration and source |
| --- | --- |
| Existing finite integration schedule, not a new carrier | `familyProject`, `lean/YMGap/Continuum/SU2QuaternionHaarFamilyProjection.lean:39` |
| Family-independent factors pull through | `familyProject_mul_of_independent`, same file:105 |
| Full-weight family residual is coefficient-centered | `familyProject_weightedResidual_zero`, same file:151 |
| Orthogonality to every family-independent test | `familyWeightedResidual_orthogonal`, same file:174 |
| Full absent-family centering implies original product-heat nullity under Haar tests | `productMap_family_pair_zero`, `lean/YMGap/Continuum/SU2QuaternionProductHeatFamilyNull.lean:40` |
| Actual m, M and R | `spatialFringeMass`, `spatialFringeMean`, `spatialFringeResidual`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeProjection.lean:56`, :59, :62 |
| Both terminal messages omit all fringe coordinates, including depth zero | `terminal_fringe_independent`, same file:97 |
| Exact conditional denominator and numerator: P_F(nu)=g_n*t*m, P_F(nu*f)=g_n*t*M | `marginal_fringe_mass_pin`, `marginal_fringe_mean_pin`, same file:115, :125 |
| Original-nu residual orthogonality | `spatialFringeResidual_orthogonal`, same file:138 |
| Multiplication by any fringe-independent polynomial preserves weighted transfer nullity | `spatialFringeResidual_scaled_transfer_zero`, same file:174 |
| Project the complete original spatial floor | `lowerCertificate`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeProjectionWindow.lean:95` |
| Actual finite reciprocal and fringe independence | `reciprocal`, `reciprocal_independent`, same file:154, :165 |
| Multiplier-square cap one and geometric error interval | `multiplierSquareCertificate`, `multiplierErrorInterval`, same file:176, :186 |
| Scaled polynomial sum and orthogonality | `scaled_split`, `scaled_pieces_orthogonal`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeProjectionNorm.lean:73`, :84 |
| Pythagoras with no discarded mixed term | `scaled_pieces_pythagoras`, same file:101 |
| Joint coefficient-one norm bound | `reciprocal_pieces_norm_le`, same file:142 |
| Geometric relative squared error | `reciprocal_error_norm_le`, same file:178 |
| Explicit relative-tolerance modulus and every-later-degree guarantee | `relativeApproximationCutoff`, `reciprocal_error_norm_le_tolerance`, same file:202, :205 |

The generic product-heat theorem uses the existing finite-schedule identity
`quaternionHaar_polyMul_eq_after_integratingBlocks`,
`lean/YMGap/Continuum/SU2QuaternionOriginalHaarBlockMarginal.lean:77`,
with one unchanged spectator. No per-coordinate residual representation,
support assumption on the arbitrary Haar test, or new erasure induction
is required for this nullity statement.

## Parameter and normalization audit

The spatial window is explicit:

    ell=headFloor(w)^(number of spatial faces),
    u=polynomialCap(m)+(ell+1),
    rho=1-ell/u,  0<=rho<1.

See `lower`, `upper`, `rate`, `rate_nonnegative`, `rate_lt_one`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeProjectionWindow.lean:87`,
:114, :141, :145, :149. Lower-floor dependence is on nome and width; the
cap and approximation rate may depend on nome, cutoff and width. No
terminal-depth parameter enters J_k, rho or the relative modulus.

The coefficient-one norm budget holds for each named admissible parameter
choice and every depth n; the unnormalized norm on its RHS still depends
on n. The error theorem is relative, not a depth-uniform absolute error.
The approximation index k is not physical time or lattice spacing. This
conditional-projection geometry supplies no non-abelian active-decay
mechanism and cannot by itself imply a full-sector mass gap.

At k=0, J_0=0: both pieces vanish and the error bound is equality. With an
empty fringe, R is coefficient-zero and the other piece approaches f.
These edge cases do not create a false excitation or strict contraction.

## Effect on the causal proof path

This constructs stable fringe extraction rather than assuming a budget on
the old Haar-increment seeds. It does not prove the previous fringeSum or
its component costs are stable, nor is the new r_k identified with that sum.
The exact new approximation pins the specified pieces to the original f.

The next concrete consumer is the original-energy identity

    E_gn(r_k+b_k)=||r_k||_nu^2+E_gn(b_k).

This remains OPEN here. Its available inputs are the checked transfer
nullity and orthogonality, plus `transferStep_weighted_symmetric`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSymmetry.lean:97`.
After this identity, the active piece still needs regulator-controlled
coercivity, and the approximation requires an original energy/centering
passage. None is replaced by the coefficient-one norm budget.

Fringe independence does not imply the original per-link conditional
centering required by FamilyCost. Reduced-marginal tests cannot be inserted
there silently. Any reduced-action route needs its own exact original
transfer pin. No completed OS projection, full completed-sector strict
bound, physical calibration, continuum/QFT or every-group closure is claimed.

## Verification

Five new modules passed final focused serialized one-worker checks via the
monitored launcher, unchanged 20 GiB ceiling, fresh process/swap preflight.
All 56 printed gates use only {propext, Quot.sound}. Final logs contain no
errors, warnings, sorryAx or classical dependencies. An intermediate window
check exposed a missing namespace for coefficient negation; it was fixed
and the final check is clean. No actual sorry was introduced/discharged.

Independent read-only mathematical review passed the original action,
all-depth factors, normalization, Pythagoras, finite reciprocal bounds,
relative uniformity and empty-fringe/zero-degree cases. The final explicit
relative-tolerance consumer was additionally kernel-checked. Five root
imports were added; root/full-tree/full-audit/guard NOT run. No canonical
frontier, CI or resource-safety limit changed.

Final local log SHA-256 values (logs are not repository artifacts):

| Log under `/tmp/` | Gates | SHA-256 |
| --- | ---: | --- |
| ym-haar-family-projection-20260917.log | 15 | `8e2cd37aa2855b585eda62f506676d06eb67d1732e8359d7a4b1550dc9e45e32` |
| ym-product-heat-family-null-20260917.log | 1 | `2f31e14967941203c0e3d072b06aebc8ac78c545888284b5dc06d9404e13cad1` |
| ym-fringe-projection-20260917.log | 18 | `046cae85f349e8562aa5d77c945a09c1d19a573ae99add542f33c6f0c13b2a0a` |
| ym-fringe-projection-window-20260917.log | 15 | `9b1eaa35bf043b6ca15cf1cf9011e53f729c702fe85ac5157bea0f2720051ec7` |
| ym-fringe-projection-norm-20260917.log | 7 | `b5e897b04910d7c0c41553a00bbc56286b21bd9eb1ecf8d653643951e519bff4` |
