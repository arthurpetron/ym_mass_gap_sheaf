# Scope: which spectral producer could witness `WilsonAFPaddedGapInput`? (2026-10-06 PT)

This note is scope only and makes NO proof claims.

## Target

Per scale `j`, the transfer `T` lives on the all-nome literal-width Wilson completion: nome
`w_j → 1` (AF schedule), spatial width `width_j = 4^j + 1`, and dyadic block `side_j = 2^j`.
The target is an all-vector bound on the vacuum complement,
`B(Ty,Ty) ≤ r_j²·B(y,y)`, with `1 − r_j ≥ m·2^-j`.

In words: a spectral gap of the slab transfer that is UNIFORM IN THE SPATIAL VOLUME and
scales like the lattice spacing. This is the mass gap.

## Why the Doeblin route fails

The present rate compares the kinetic weight with its floor/cap face by face. That loses a
factor `1/32` per temporal face, i.e. `(1/32)^volume`; this is proved in the dead-end note.

Any producer must avoid per-site multiplicative losses. It needs either a tensorization
(product-stable) inequality, or a decay-of-correlations input that replaces global
minorization.

## Candidates

| Producer | What it would need here | Lean status |
|---|---|---|
| Transfer-matrix Poincaré / spectral gap with tensorization | A one-slice Poincaré inequality for the conditional (single-time-slice) measure, with constant independent of `width`, plus a product/tensorization or Dobrushin–Shlosman-type mixing condition across spatial links. At `w_j → 1` (weak coupling) the single-link gap shrinks like `1−w`, i.e. `~g²`. The needed `2^-j` scaling must come from the block/RG structure, not from a site estimate. | Fixed-volume pulled-Poincaré gaps exist on the CUBE carrier (`BF4PhysicalCutoffVacuumSectorPulled*PoincareGap`, `BF4PhysicalFiniteVacuumSectorPoincareGap`). There is a projected-variance Poincaré on the slab (`BF4ExactSlabFixedSpatialProjectedVariancePoincare`). None is volume-uniform or on the Wilson completion with the all-vector shape. |
| Log-Sobolev (LSI) | A uniform LSI for the slab Gibbs measure, which tensorizes and implies Poincaré. Known rigorously only at strong coupling or high temperature (Zegarlinski / Stroock–Zegarlinski regime), or for the SU(2) heat kernel on a SINGLE link. | No LSI module. The single-link heat-kernel floors exist (pointwise floors and caps). |
| Bakry–Émery / curvature `CD(K,∞)` on `SU(2)^n` | A Bochner inequality `Γ₂ ≥ KΓ` for the slab generator, with `K` uniform in `n`. The Ricci curvature of `SU(2)` helps, but the Wilson interaction contributes a Hessian term of order `β = 4/g²`, which destroys uniform `K` at weak coupling. Known to work at strong coupling (recent Bakry–Émery results for lattice YM at small `β`). | `BakryEmery.lean` and `BakryEmeryGap.lean`: a finite reversible-generator template (curvature ⇒ gap magnitude). There are curvature modules (`…PlaquetteCurvature`, `…FamilyCurvature`, `…CasimirCurvature`). None is instantiated on the Wilson transfer with an `n`-uniform `K`. |
| Cluster / polymer expansion and multiscale RG (Balaban) | A convergent expansion at each scale; at weak coupling this is a multiscale RG with large/small-field decomposition. It would produce exponential clustering at the PHYSICAL mass scale, which is exactly `1 − r_j ~ m·a_j`. This is the only known route at weak coupling, and it is enormous; it is the Clay problem. | Polymer and clustering scaffolding (`AbstractPolymerXi`, `MultiScalePolymerAssembly`, `ClusteringImpliesGap`, `…GeometricClustering`). There is no convergent YM expansion. |
| Reflection positivity / chessboard | Chessboard estimates bound the probability of "bad" configurations by single-plaquette quantities. Combined with Peierls-type arguments they give a gap at strong coupling, or in phase-transition regimes. Not known to give a weak-coupling gap. | RP modules exist (`BF4ExactSlab*ReflectionPositivity`, `…WindowReflectionPositive`). There are no chessboard bounds. |

## What any producer must deliver to plug in

A family `r_j` and proofs of:
- `0 ≤ r_j < 1`;
- `∀ y ∈ VacuumComplement(w_j, width_j), B(T y, T y) ≤ r_j² B(y, y)`;
- `∃ m > 0, ∀ j, m·2^-j ≤ 1 − r_j`.

Then `wilsonGapBranch_afPadded_generic` gives the band and decay unconditionally. A03
needs the step ratio as well.

## Honest bottom line

- At the AF weak-coupling end, every known rigorous route is either a strong-coupling
  method that fails as `w → 1`, or the full multiscale RG.
- No candidate is within reach as finite plumbing.
- The realistic near-term Lean targets are volume-uniform statements in a STRONG-coupling
  window. Those are useful as tests of the interface, but they do not satisfy the
  `2^-j`-scaled margin along the AF schedule.
