# J04 audit: what a Wilson measure for SU(N), N ≥ 3, would need (2026-10-06)

Status: J04 OPEN.  This note is an inventory, not a result.

## 0. What "the Wilson measure" is in the repo today (SU(2) only)

`Continuum/WilsonConsistency.wilsonContinuumMeasure w hw` (used by
`MassGap/SimpleGroup.SU2WilsonOrigin`) is built from:

* `RGTransport.charAlg`: carrier = SU(2) spin labels `Nat`, `mul a b = |a−b|`
  (Clebsch–Gordan *lowest channel only*; documented as non-associative),
  `star = id`;
* `charFunc w`: `E χ_s = (s+1) · w^{s(s+2)}` — the single-link heat-kernel
  character moment with rational weight `w ≈ e^{−t/4}`;
* `wilsonSystem = stationaryTower charAlg` (identity coarse→fine inclusion) and
  the inverse-limit `ContinuumMeasure`.

Caveat for J04: this is a one-link character-moment functional, not a
lattice Wilson Gibbs measure over plaquettes.  The genuine lattice SU(2)
content lives separately in the quaternion/Haar stack
(`RationalQuaternion*`, `BF4GeometricHaarMehlerProjection.quaternionHaar`,
`SU2Quaternion*` heat/character/Casimir modules).  `SU2WilsonOrigin` is
therefore tied to the repo's *named* Wilson measure, which is weaker than a
lattice Wilson measure.

## 1. Pieces existing for SU(2) and their SU(N) status

| Layer | SU(2) module(s) | SU(N≥3) status |
|---|---|---|
| Group carrier | `RepTheory/RationalQuaternionAlgebra`, `RationalQuaternionUnitNormGroup` (rational points of S³, `ConstructiveGroup`) | **missing**: no rational unitary N×N matrices with det 1, no `ConstructiveGroup` instance |
| Centre / global forms | `RationalQuaternionSignQuotient`, `LocatedCentralQuotient` | generic quotient machinery exists (`ConstructiveGroup`, `CompactSimpleGlobalForm` centre codes ℤ_N); no SU(N) instance |
| Haar functional | `quaternionHaar` (exact S³ monomial moments `sphereMoment4`) | **missing**: no exact moments of matrix-entry monomials on SU(N) (Weingarten / Gelfand–Tsetlin integration) |
| Characters | `characterPolynomial` (Chebyshev-U), `SU2Realized.spinCharacter`, `relativeCharacter_eq_spinCharacter` | **missing as functions on the group**: only scalar data — `RepTheory/SU3` (dim, C₂ of (p,q)), `RG/SUNWeylData` (fundamental-weight C₂), `RG/WeylDimGeneral*`, `RG/WeylCharacterBound` (tail bounds) |
| Casimir eigen-identity | `SU2QuaternionRelativeCharacterCasimir` (angular Laplacian on S³) | **missing**: no Laplace–Beltrami/Casimir operator on SU(N) polynomial algebra |
| Orthonormality | `SU2Realized.selfPairing_one/_two` (finite s only) | **missing** |
| Character algebra / moments | `charAlg`, `charFunc` (lowest-channel) | would need full Littlewood–Richardson fusion `χ_λ χ_μ = Σ N^ν_{λμ} χ_ν` (a genuinely associative algebra) — missing even for SU(2) |
| Projective tower / continuum measure | `WilsonConsistency` (generic `stationaryTower`, `continuumMeasure`) | generic and reusable once a per-scale `ProbFunctional` on an SU(N) character algebra exists |
| Heat-kernel weight | `w^{s(s+2)}` | form `dim(λ)·e^{−t C₂(λ)}`; C₂ data exists (`SU3`, `SUNWeylData`), rationalized weight would need `w^{(rational C₂)}` — denominators `N` need a root or a rescaled `w` |

## 2. Minimal missing modules (in dependency order)

1. `RepTheory/RationalSUNGroup`: rational N×N matrices with `U U* = 1`,
   `det = 1` (over `Q'` or `Q'(i)`), group laws as a `ConstructiveGroup`;
   centre ℤ_N inclusion feeding `LocatedCentralQuotient`.
2. `RepTheory/SUNCharacters`: Schur-polynomial (Weyl) characters `χ_λ` as
   polynomials in matrix entries; `χ_λ(1) = dim λ` against `WeylDimGeneral`.
3. `Continuum/SUNHaarMoments`: exact Haar functional on polynomials in entries
   (Weingarten calculus or Weyl integration in eigenvalue coordinates);
   normalization and left/right invariance on the polynomial algebra.
4. `Continuum/SUNCasimirEigen`: Casimir operator on the polynomial algebra
   with `C χ_λ = C₂(λ) χ_λ`, matching `SU3`/`SUNWeylData` values.
5. `Continuum/SUNCharacterAlgebra`: associative fusion algebra on dominant
   weights and the heat-kernel `ProbFunctional`; positivity on `a*a`.
6. `Continuum/SUNWilsonConsistency`: tower + `ContinuumMeasure`, then an
   `SUNWilsonOrigin` predicate replacing the `R = su2` clause of
   `SU2WilsonOrigin` (lifting `GroupBoundGap.row_eq_su2`).

Items 1–4 correspond to ladder item (e) of work_plan "J04 parallel track";
items 5–6 to (d)/(f).  None of these exist; nothing in this note is proved.
