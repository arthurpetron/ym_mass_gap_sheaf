# Scope: an honest finite-volume SU(2) Wilson Gibbs measure on the Z⁴ torus (2026-10-06 PT)

Status: first Lean layer `Continuum/SU2TorusWilsonGibbs.lean` (REDUCTION + proved algebra).
The measure itself is OPEN. Coordination: the J04 audit
`docs/J04-SUN-WILSON-MEASURE-AUDIT-2026-10-06.md` (YM Group Realizer) records that
`wilsonContinuumMeasure` is a one-link character-moment functional
(`charAlg`, lowest-channel `|a−b|` fusion, non-associative), not a lattice Gibbs measure.
This note scopes the lattice object. Group Realizer's files are not edited.

## 1. Target object
Torus `Λ_N = (ℤ/N)⁴` (`Z4TorusGeometry`), link variables `U : torusLinks N → SU(2)`,
plaquette holonomy `U_p` (`TorusWilsonAction.holonomy`), weight `W_β(g) = exp(β(½tr g − 1))`.
`Z = ∫ Π_p W_β(U_p) Π_ℓ dHaar(U_ℓ)`, `⟨F⟩ = Z⁻¹ ∫ F Π_p W_β(U_p) Π_ℓ dHaar`.
Honest requirements: product Haar (normalised, positive, left/right invariant per link),
gauge invariance (`W` a class function), translation invariance, `Z > 0`.

## 2. Constructively available
- Carrier: `RationalQuaternion.UnitNorm.group` (rational points of S³, a `ConstructiveGroup`;
  countable, not compact, not all of SU(2)).
- Characters `χ_s = U_s(Re x)` (Chebyshev-U; `SU2Realized.spinCharacter`), `χ_s(1) = s+1`.
  Proved here: class functions (`Re(g h ḡ) = |g|² Re h`) and setoid-respecting.
- Exact S³ monomial moments `quaternionHaar` (BF4GeometricHaarMehlerProjection), polynomial
  test functions only.
- Heat-kernel coefficients `(s+1) w^{s(s+2)}` (as in `charFunc`).

## 3. Open hypotheses (explicit structures in Lean)
- `ConfigHaar G N`: integral over configurations, linear, congruent, positive, normalised,
  gauge- and translation-invariant. Not constructed on the rational carrier (non-finite;
  needs completion to S³ or a polynomial-algebra restriction).
- `LinkHaar G` + `SU2Schur`: per-link Haar with left/right invariance and
  `h(χ_s χ_t) = δ_{st}`. (Repo proves only finitely many s via `selfPairing_one/_two`.)
- Character expansion of `W_β`: `W_β = Σ_s c_s(β) χ_s` with
  `c_s(β) = (s+1) I_{s+1}(β)/I_1(β)` (up to normalisation, `β` here the SU(2) coupling with
  `½ tr`). Lean has only finite sums `charWeight c J` with explicit `c`; the Bessel values
  and the truncation error are OPEN.

## 4. Proved in the first layer
`su2SpinClass`, `su2CharWeightClass`, `boltzmann`, `partition`, `numerator`,
`boltzmann_gauge_invariant`, `numerator_gauge_invariant`, `partition_ge`
(`W ≥ δ ≥ 0` ⇒ `Z ≥ δ^{6N⁴}`), `partition_pos`. Prerequisites:
`TorusGaugeInvariance.holonomy_gauge`, `wilsonAction_gauge_invariant`; `TorusSlabCover`
(slab nodup, disjoint, cover, permutation).

## 5. Where SU(2) differs from U(1)
| | SU(2) | U(1) |
|---|---|---|
| irreps / characters | spin s/2, `χ_s = U_s(cos θ)` = `sin((s+1)θ)/sin θ` | `e^{inθ}`, n ∈ ℤ |
| dimensions | `s+1` (enter `c_s` and Schur sums) | 1 |
| Wilson coefficients | `(s+1) I_{s+1}(β)/I_1(β)` | `I_n(β)/I_0(β)` |
| fusion | `χ_s χ_t = Σ_{u=|s−t|, step 2}^{s+t} χ_u` (non-commutative group, multiplicities) | `χ_m χ_n = χ_{m+n}` |
| centre | ℤ₂ (`±1`, `χ_s(−1) = (−1)^s(s+1)`) | all of U(1) |
| weak coupling | asymptotically free (not visible at finite β) | Coulomb phase, massless photon |
The finite-volume measure exists for both; nothing at fixed finite N separates them except the
character data above. Any gap argument must consume those data (fusion multiplicities,
dimensions, ℤ₂ centre, or the β-flow), not the abstract structures of §3–4.

## 6. U(1) refutation rule (standing check, scope C1 §7)
Every statement proved in §4 is satisfied by 4D U(1) with its own characters; hence none can
imply a uniform gap. They are infrastructure. A future gap-relevant statement must have a
hypothesis that fails for U(1) at large β (e.g. a bound using `(s+1)`-weighted fusion or the
ℤ₂ centre / vortex free energy).

## 7. Next steps
1. Instantiate `LinkHaar` on polynomial test functions via `quaternionHaar` (needs closure of
   class of tests under translation; restrict `F` to polynomials in coordinates).
2. Prove `SU2Schur` for all s on that polynomial class (Chebyshev orthogonality on S³).
3. Product over 4N⁴ links: iterated `quaternionHaar` on polynomials (finite, decidable per N).
4. Positive truncated weights: choose `c`, `J` with `charWeight ≥ δ > 0` on S³ (OPEN).
