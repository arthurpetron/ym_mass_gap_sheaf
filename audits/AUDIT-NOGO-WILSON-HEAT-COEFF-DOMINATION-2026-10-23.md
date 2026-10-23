# Audit: Wilson vs heat-kernel coefficient-domination no-go (2026-10-23 ET)

File: `lean/YMGap/Continuum/WilsonHeatCoeffDominationNoGo.lean` (84 lines).

## Statement

`CoeffDominated a w := ∀ K s, s ≤ K → wCoeff a K s ≤ wCoeff a K 0 * coeffW w s`.

- `wCoeff (wilsonA β) K s`: exact character coefficients of the truncated Wilson weight
  `T_K` (`SU2WilsonCharacterPower.wilsonPoly_expand`, `SU2WilsonActivity.wilsonA`).
- `coeffW w s = (s+1) w^{s(s+2)}`: the BF4 heat-kernel coefficient (`BondMovingStep.coeffW`),
  the same one `heatKernelPacket` and the heat-kernel torus (`SU2TorusMultiLinkPolyGibbs`) use.
- Couplings: the actual pilot values `SU2LinkDecaySharpInst.betaS = 1/(2·10¹²)` and
  `BF4ExactSlabPlaquetteSmallNomeCertificate.nome = 1/1024`.

## Results (all `decide`, axiom-free)

| theorem | content |
|---|---|
| `pilot_K2_dominated` | holds for K = 2, s ∈ {0,1,2} |
| `wilson_coeff_counterexample` | fails at K = s = 3 |
| `counterexample_lhs` | `c_3^{(3)} = 1/384000000000000000000000000000000000000` (= (β/2)³/3!) |
| `wilson_coeff_counterexample_K4` | fails at K = s = 4 |
| `wilson_not_coeffDominated` | `¬ CoeffDominated (wilsonA betaS) nome` |

RHS at K = s = 3: `(1 + (β/2)²/2)·4·2⁻¹⁵⁰ ≈ 2.80·10⁻⁴⁵`, against LHS `≈ 2.60·10⁻³⁹`.

## Scope

- This closes candidate (c) of the TorusChiBridge scoping. `TorusChiBridge` itself is
  unchanged and stays OPEN.
- Cause: the Wilson coefficients decay factorially in s, the heat-kernel ones Gaussian.
  The general claim, failure for every fixed w < 1 once K is large enough, is NOT
  formalised; only the pilot instance is proved.
- Domination would bound activities, not cross-measure correlators. There is no GKS
  monotonicity for signed non-abelian activities.
- U(1)-true. Not gap, continuum or Clay evidence.

## Checks

Gated capped single-file `--check` passed with no warnings. `#print axioms` (via temp file,
deleted afterwards): all five theorems depend on no axioms. Hygiene grep clean.
