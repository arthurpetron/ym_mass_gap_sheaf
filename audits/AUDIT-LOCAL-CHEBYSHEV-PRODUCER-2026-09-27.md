# Actual local completed auxiliary and original covariance producer

Checkpoint `b338a25`. Subsequent result: the
[checked factor obstruction](AUDIT-LOCAL-CHEBYSHEV-FACTOR-OBSTRUCTION-2026-09-27.md)
proves this degree-dependent factor returns to ONE, uniformly in nome and
nonempty seed size. The finite upper bound below remains valid; the next
priority is a stronger estimate, not asymptotic decay from this factor.

## Checked conclusion

Let 0<w<1, K=headCutoff(w)+stage, and p,q be supported polynomials literally
local on link lists S,Q. For every n>=0 with Q disjoint from the 16*(n+1)
star cone of S, the SAME original finite covariance satisfies

    Cov(p,q)^2 <= factor(w,|S|,n)^2 Var(p) Var(q),
    budget(s,n) = 25^(16*(n+1)) * s,
    delta(w,b) = headFloor(w)^(6b) / prefixCap(w)^(6b),
    c_n = 2 + (2/625) delta(w,budget(|S|,n)) > 2,
    factor(w,s,n) = 1 / T_(n+1)(c_n-1).

The statement is constructive-real order on the original rational moments.
The original full face action, reciprocal partition, both diagonal variances,
and actual conditional operators are retained. No analytic auxiliary-energy
or Chebyshev-denominator-positivity premise is supplied by the caller.
The factor has no extent, stage or placement argument. It DOES depend on
nome, initial support-list length, and degree. No asymptotic decay is proved.

## Constructed forward-to-backward connection

1. `LocalRep`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalCauchyRepresentative.lean:37`,
   carries a Type-level Cauchy representative, its termwise literal locality
   and the equality of its class with the named completed vector. The
   `LocalRep.conditional` constructor in that file at line 105 uses the
   existing conditional dense map's explicit cofinal diagonal. Every term
   is a conditional polynomial approximant with the already-proved support
   bound. Its existing Cauchy modulus is retained; no quotient representative
   is selected by choice. Addition, subtraction and rational scaling preserve
   fixed support through the actual original carrier operations.
2. `layerRep` and `runLayersRep`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalCauchyCone.lean:67` and
   `lean/YMGap/Continuum/BF4ExactSlabLocalCauchyCone.lean:77`,
   use the existing exact layer-pruning equality. Every retained link lies
   in the INITIAL region; all its incident faces lie in one expansion of
   that region. Hence any number of retained updates preserves that single
   expanded literal support. Same-color commutation is used for pruning,
   not for an unproved preservation of neighboring free-centered sectors.
3. `balancedRep`, `firstRep` and `auxiliaryRep`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalCauchyCone.lean:89`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalCauchyCone.lean:109`, and
   `lean/YMGap/Continuum/BF4ExactSlabLocalCauchyCone.lean:148`,
   construct the actual balanced output and both actual coupled components.
   The first-kind recurrence keeps the first component at radius 16*n;
   the auxiliary at degree n+1 has radius 16*n. These are explicit recursive
   definitions in Type, with no `noncomputable` marker or erased witness.
4. `completed_of_termwise_bound`,
   `lean/YMGap/Continuum/BF4ExactSlabCompletedFiniteVolumeCoercivity.lean:155`,
   factors the existing closed-limit proof without changing the old
   finite-volume theorem. `completed_local_coercivity`,
   `lean/YMGap/Continuum/BF4ExactSlabCompletedLocalSupportCoercivity.lean:53`,
   centers every supplied local Cauchy term in the ORIGINAL form. Centering
   preserves its literal support and modulus; completed original-vacuum
   orthogonality pins the centered class to the SAME vector. The proved
   dense local estimate then passes to that vector's actual residual sum.
5. `grow_length_le`,
   `lean/YMGap/Continuum/BF4ExactSlabConeSize.lean:61`, gives
   |grow(r,S)|<=25^r |S| from the already-proved 25-link star bound.
   `auxiliary_coercivity`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalAuxiliaryCoercivity.lean:74`,
   constructs the balanced auxiliary's radius-16*(n+1) representative and
   applies the completed estimate with the displayed volume-independent
   budget. Original centering follows from the checked actual recurrence
   and sweep preservation, not an extra analytic condition.
6. `reverse_energy_of_coercivity_at_balanced`,
   `lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeReverseEnergy.lean:156`,
   combines that lower estimate with the SAME reversed physical sweep's
   625 loss bound. `auxiliary_reverse_energy`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalAuxiliaryCoercivity.lean:107`,
   supplies precisely the backward consumer's inequality
   c_n ||B u||^2 <= 2 ||W u||^2 at u=(coupled c_n x (n+1)).2.
7. `finiteCovariance_sq_bound`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalChebyshevCovariance.lean:69`,
   starts with the actual original-centered p, constructs its local seed
   witness and uses that reverse-energy result in the existing squared
   covariance consumer. `covarianceFactor` in that file at line 53 has no
   extent or cutoff argument; `denominator_positive` at line 42 supplies
   its guard. No new action, mean, normalization or surrogate covariance.

## Exact residue and next mathematical priority

The previous local-representative/completion seam is closed for this actual
local-seed orbit. This is not a theorem extracting literal-local data from
EVERY operationally localized quotient state. The construction starts with
supplied literal seed data and follows the same operators explicitly.

The coefficient c_n depends on n through the displayed cone budget. The
proved pointwise strict inequality c_n>2 must NOT be treated as a fixed c>2
for all n. No theorem here proves T_(n+1)(c_n-1) tends to infinity, or that
the returned factor tends to zero. Useful growth/coupling estimates remain
the quantitative frontier. Merely composing more limit wrappers cannot
supply the missing rate.

Uniformity means the displayed relative factor is independent of ambient
volume and late heat cutoff at fixed nome, seed size and degree. It is not
uniform in degree, beta, nome or lattice spacing. No thermodynamic or
cutoff-limit covariance passage is added in this increment.

All operators here are the original finite SU(2) conditional-link dynamics
on ordinary full-action GNS. No physical OS time or Hamiltonian identification
is proved. Same-theory scaling/OS/QFT construction, nontrivial continuum
survival, positive physical mass, every compact simple group, and the Clay
theorem remain open. A03 and the canonical chart markers are unchanged.

## Verification and review

Eight focused checks passed, serialized through `scripts/safe_lean_build.py`
with one worker and a 20 GiB cap: CompletedFiniteVolumeCoercivity (2 printed
gates), CompletedLocalSupportCoercivity (1), FiniteVolumeReverseEnergy (8),
ConeSize (2), LocalCauchyRepresentative (8), LocalCauchyCone (6),
LocalAuxiliaryCoercivity (6), and LocalChebyshevCovariance (3).
All 36 gates stayed within {propext, Quot.sound}. Initial namespace,
notation and recursion-code-generation errors were corrected; constructive
recursive definitions replaced unsupported code-generator recursors, without
adding `noncomputable` or changing the theorem. Local elaboration heartbeat
budgets increased to 2,000,000 where needed; the 20 GiB memory cap did not.

Sol supplied the closed-limit proof, representative constructors, scalar
calibration and covariance consumer. Luna supplied the elementary cone-size
bound. Independent Sol review confirmed the same-object pins, degree/radius
indices and parameter limitations. The main agent constructed the pruned
literal cone and actual auxiliary estimate and ran the serialized checks.

No new sorry, axiom, classical input or canonical frontier field. Root
imports are registered, but no full-root/full-tree build, audit, guard,
progress-metric script, routine literature scan or CI run was performed.
Each check finished in its initial call; there was no live job to poll.
Five-minute manual polling and continuous automatic resource telemetry
remain unchanged. The whole-project goal stays active and open.
