# Original weighted test costs and constructive scalar calibration

## Exact forward identities

Fix the existing original SU(2) slab parameters `0<w<1`, extent, heat cutoff
`K>=headCutoff w`, and physical link i. Write F for its original full-action
form, B for the retained complementary action, D for the actual conditional
normalizer, N for its conditional numerator, J for the exterior probe map,
and H for exterior Haar integration. Set

    Phi_p = D*N(p^2) - N(p)^2
    t(p)  = J(D)*p - J(Np)
    E(r,p) = J(r)*p.

These are the existing supported polynomials, not new abstract inputs.
`BF4ExactSlabStarExteriorResidual.exteriorSeed`
(`lean/YMGap/Continuum/BF4ExactSlabStarExteriorResidual.lean:49`) constructs
E. `numerator_exterior_pair` (`:89`) and `numerator_exterior_rad` (`:115`)
prove exterior linearity in the exterior form and its radical. This avoids
asserting a stronger, unnecessary raw coefficient equality. The result
`polynomialResidual_exteriorSeed_completed` (`:233`) is the literal equality
of the original completed embeddings of t(E(r,p)) and E(r,t(p)). No extension
of arbitrary exterior multiplication to every completed state is claimed.

`BF4ExactSlabStarPolynomialCost.varianceFunctional`
(`lean/YMGap/Continuum/BF4ExactSlabStarPolynomialCost.lean:67`) computes
H[B*r*Phi_p]. Its checked identities are:

| Declaration (same module) | Exact quantity |
| --- | --- |
| `exterior_variance_pair` (`:74`) | F(E(r,p),t(p)) = H[B*r*Phi_p] |
| `normCost_variance` (`:125`) | F(t(p),t(p)) = H[B*D*Phi_p] |
| `exterior_cost_pair` (`:143`) | F(E(r,t(p)),t(p)) = H[B*r*D*Phi_p] |
| `exterior_test_cost` (`:176`) | F(E(r,t(p)),E(r,t(p))) = H[B*r^2*D*Phi_p] |
| `exteriorSeed_pairValue` (`:196`) | pairValue(E(r,p),p) = H[B*r*Phi_p] |
| `exteriorSeed_normCost` (`:210`) | normCost(E(r,p)) = H[B*r^2*D*Phi_p] |

Rational equalities here mean the repository's Q' setoid equivalence. The
last two statements feed the already checked exact test-ray optimizer on
the SAME original residual. Thus its numerator and cost for this family
are explicitly exposed with the original D, B and p. The input being
tested is p, not E(r,p); confusing these changes the insertion powers.

### Actual remaining analytic work

The cost contains one MORE normalizer than the unmodulated cross-pair.
Using the checked inverse approximation only in the B-weighted norm does
not by itself control the B*Phi_p-weighted error needed here. The next
approximation target is an exterior polynomial approximation to 1/D with
that variance weight retained. A weighted contraction proof or an explicit
multiplier bound must supply the join. This audit does not claim that
join, local variational sharpness, or a useful global lower coercivity
bound. A fixed polynomial on the compact group is not claimed unbounded;
the absent item is the required controlled estimate and its formal join.

Even exact local optimization would still require a summed-test estimate
against the original globally centered norm, or the smaller observable-
specific estimates actually consumed by the spatial argument, with useful
cutoff/volume/changing-coupling dependence. Positivity and exact algebra
alone do not supply such an estimate.

## Constructive backward scalar calibration

For supplied rational `0<eta<1`,
`RationalSqrtCalibration.index`, `approx`, and `rho`
(`lean/YMGap/Continuum/RationalSqrtCalibration.lean:28`, `:31`, `:35`)
compute an explicit Heron index, x, and rho=eta/x. The checked bounds are
eta<=x^2<=4*eta (`approx_sq_lower`, `:69`; `approx_sq_upper`, `:73`) and
eta/4<=rho^2<=eta (`rho_sq_lower`, `:122`; `rho_sq_upper`, `:106`). Strict
positivity and rho<1 are proved at `:84` and `:143`. No witness is selected
from an erased existential and no new calibration hypothesis is added.

`ChebyshevMarginParameters`
(`lean/YMGap/Continuum/ChebyshevMarginParameters.lean`) constructs

    qbar=1-rho^2, r=(1+rho)/(1-rho), s=(1-rho)/(1+rho).

`s_lt_one` (`:101`), `rs` (`:105`) and `center_eq_margin` (`:211`) give
0<s<1, r*s=1 and (r+s)/2=2/qbar-1, together with the positivity theorems
at `:55`, `:77` and `:81`. `calibrated_recip_le` (`:231`) proves
1/T_n((r+s)/2)<=2*s^n. `normalizationCutoff` (`:246`) computes a Nat from
the existing rational power modulus; `normalization_small` (`:254`) proves
the reciprocal is at most epsilon at EVERY index beyond that cutoff.

This is scalar normalization. It constructs neither eta from the original
interacting action nor the rescaled operator contraction. Applying the
normalization to the actual polynomial/cone/covariance argument still needs
those joins. No accelerated physical rate or continuum conclusion follows
from the scalar theorem alone.

## Verification and unchanged boundary

The four new modules passed focused checks, serialized through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check ...`.
All 41 printed public gates report only `{propext, Quot.sound}`. Sol supplied
independent proof work and reviewed the calibration and exact test-cost
normalizations. No new sorry, axiom, classical input or analytic field.
Root imports were added; no root/full-tree build, audit or guard was run.

The related targeted primary-source stress test is
`AUDIT-MARKOV-RATE-SCOPE-2026-09-27.md`: a useful global conditional-dynamics
gap remains a sufficient route, not a necessary Clay requirement. That
review supplies neither an estimate nor a rigorous obstruction for this
exact SU(2) sweep. No canonical field or chart marker changed. Physical
calibration, same-theory OS/Hamiltonian and continuum QFT construction,
nontrivial survival, every-group estimates and the whole Clay target remain
open.
