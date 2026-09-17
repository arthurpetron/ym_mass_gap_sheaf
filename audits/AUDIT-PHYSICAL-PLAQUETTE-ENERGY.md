# Audit-directed physical plaquette energy route

Date: 2026-09-17 UTC. Parent checkpoint: `1e99e71`.

## Whole-project goal and unchanged boundary

Construct, for every compact simple gauge group, a nontrivial continuum
Yang--Mills QFT on R^4 with the required QFT axioms and a positive physical
Hamiltonian mass gap, constructively within the repository's Lean axiom gate.
The continuum, observables, reconstruction and Hamiltonian must belong to the
same theory. This goal remains OPEN.

The audit-directed plan caps the auxiliary charged-sector branch and returns
to the actual physical plaquette sector. A center-odd estimate does not bound
the original closed plaquette characters: their center-even symmetry is
`character_starSign`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialVertexStar.lean:313`.

## Local mathematical step: checked

Let A be the original selected product of physical face heat factors. For a
link of a physical plaquette, let R retain exactly those selected factors
that do not contain that link. Let p be the fundamental character of that
plaquette and q any supported polynomial localized away from the link.
The new exact identities are

```
H[R*p*q] = 0,
H[R*(p-q)^2] = H[R] + H[R*q^2].
```

They are `retained_cross_zero` and `retained_error_identity`,
`lean/YMGap/Continuum/BF4ExactSlabSelectedStarPredictionError.lean:85`
and `:145`. The predictor need not be constant and may depend on every
other allowed link. The original ordered-word character selection is
`original_character_local_zero`,
`lean/YMGap/Continuum/BF4ExactSlabSingleLinkCharacterSelection.lean:78`.
The proof also uses the SU(2) character identity chi_1^2 = 1 + chi_2.

Restoring at most six selected physical heat factors proves

```
starRatio(w) * H[A] <= H[A*(p-q)^2].
```

This is `polynomial_square_floor`,
`lean/YMGap/Continuum/BF4ExactSlabSelectedStarPredictionError.lean:164`.
The explicit hypotheses retain physical face membership, a nodup selected
factor list, supported q, and literal link-locality with the selected link
excluded. No terminal-message locality is assumed.

## Original temporal-energy consumer: checked

The proved adjacent-time specialization takes q to be the same plaquette
character at the upper time. Its link list is disjoint from the chosen
lower-time link. The existing signed schedule compiler retains both signs,
all cross terms and the same selected-chain partition:
`windowRatio_span_mul_originalFiniteValue`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowProbeSpan.lean:215`.

The actual original transfer energy is normalized by the positive original
odd-chain mass, not by a new reference measure: `normalizedEnergy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:92`.
Its window jump identity includes the necessary factor TWO:
`normalizedEnergy_window`, same file `:109`.

The concrete `plaquette_energy_floor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteEnergyFloor.lean:257`,
now proves starRatio(w) <= 2*normalizedEnergy(c) for the literal fundamental
spatial plaquette c. Its hypotheses quantify every width, terminal depth
and K>=headCutoff(w), with p in the original spatialFaces width. The previous
`plaquette_energy_floor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletCoercivity.lean:314`,
has the weaker supplied lower bound mixFraction(w,width)*starRatio(w).

The exact character-square cap four is constructed by `plaquetteSquareBound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteDefect.lean:55`.
`plaquette_mass_square_le`, same file `:94`, bounds the original raw second
moment by four times the SAME odd-marginal mass. The positive explicit
`plaquetteFraction`, `:110`, is starRatio(w)/8; its positivity is
`plaquetteFraction_positive`, `:112`. Combining these actual bounds gives
`plaquette_clearedDefect_nonnegative`, `:168`, in the existing ORIGINAL
energy/variance consumer on this ONE physical plaquette diagonal.

## Parameters and scope

The constants are explicitly nome-dependent:

| Quantity | Defining declaration and source |
|---|---|
| h(w) | `headFloor`, `lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:50` |
| K_0(w) | `headCutoff`, same file `:55` |
| U(w) | `prefixCap`, `lean/YMGap/Continuum/BF4ExactSlabAllNomeTailInterval.lean:117` |
| L(w) = min(h(w),1)^6 | `localFloor`, `lowerFactor`, `lean/YMGap/Continuum/BF4ExactSlabLocalStarComparison.lean:42`, `:44` |
| C(w) = (1+U(w))^6 | `localCap`, `upperFactor`, same file `:43`, `:45` |
| starRatio(w) = L(w)/C(w) | `starRatio`, same file `:46`; positivity is `starRatio_positive`, `:65` |

The new prediction theorem quantifies extent and the selected physical
factor list without adding them to the constant; it retains 0<w<1 and
K_0(w)<=K. No bound uniform in nome, bare coupling or spacing is claimed.
This is an SU(2) statement using its actual quaternion character/heat data,
not a theorem for every gauge group.

## Remaining signed-sector and scaling obligations

The exact existing general consumer is
`clearedDefect_diagonal_nonnegative_iff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:175`.
For original g=T^n1, Z=m[g*Tg], A_f=m[g*Tg*f^2], B_f=m[g*Tg*f], it requires

```
delta * (Z*A_f - B_f^2) <= Z*energy(g,f).
```

The supplied general fraction is still width-dependent:
`terminal_existing_fraction_nonnegative`, same file `:187`.
A lower bound for one plaquette's jump does not supply this inequality on
signed combinations, products or the physical transfer orbit. No full
center-even, completed-operator or continuum gap follows from this increment.

The private-link proof has a concrete limitation before any completion or
limit: every touched link of the closed six-face unit cube meets two of its
faces (`unitCube_geometricIncidentPlaquettes_length_eq_two`,
`lean/YMGap/Continuum/Z4CoarseUnitCubeBlockGeometry.lean:228`). When isolating
one term in a signed combination, the predictor also contains the other
lower-time terms. Upper-time separation alone no longer supplies its
link-locality hypothesis. This is an obstruction to that direct application,
not a refutation of the desired signed-sector estimate. The plan prioritizes
these shared-link cancellations over accumulating individual diagonal bounds.

The execution plan now asks for control on an explicitly justified scaling
trajectory where that suffices; it does not impose every bare coupling as
a Clay prerequisite. This changes no canonical field. Existing nearby
scaling machinery does not provide the missing current-operator join:

- `retainedHarnack`,
  `lean/YMGap/Continuum/BF4RoundedPositiveAFWindows.lean:155`, bounds the
  supplied heat product without identifying it with the original interacting
  transfer. `matchedWindowFamily`, same file `:139`, still assumes the
  named cubic margin and spacing laws.
- `DynamicVacuumSectorCompletedFamily`,
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorCompletedFamily.lean:53`,
  requires gaps at its scale-indexed nomes, but its completed carrier is the
  legacy central physical vacuum-sector carrier, not the current Wilson
  carrier. `DynamicVacuumSectorPhysicalRateBand`, same file `:121`, assumes
  the physical rate/spacing band. `toContinuumGapTheorem`, `:228`, is a
  conditional scalar compiler, not a construction of the missing family.

A concrete current-original-operator trajectory/blocked-window closure was
NOT FOUND in the rounded AF, Faraut joint-carrier budget, matched/observable/
linked trajectory, grouped/all-cutoff AF comparison, dynamic completed-family,
and current fixed-spatial covariance/Dirichlet modules searched by the
parallel source audit. Physical scale, same-theory continuum/QFT and every
compact simple group remain open.

## Verification

All three new modules passed focused serialized one-worker / 20 GiB checks.
All eleven printed axiom gates lie within {propext, Quot.sound};
`plaquetteFraction` is axiom-free. Final logs have no errors or warnings.
An independent final source review passed the original-action/window join,
factor two, odd-marginal normalization, fraction 1/8, parameter scope and
single-diagonal stopping boundary. No proof or statement change was requested.

Log: `/tmp/ym-selected-star-prediction-error-20260917.log`.
SHA-256: `77873db3f29192e4cf75e1d2681b5d7a17c0d35205ac0ef460a7a92ee5ed00a5`.

Log: `/tmp/ym-physical-plaquette-energy-floor-20260917.log`.
SHA-256: `9c12f6b605b47f63f563eb25c753f976db6242361e7dfeaa2fb388287d2049a8`.

Log: `/tmp/ym-physical-plaquette-defect-20260917.log`.
SHA-256: `4b883038fa0c8cb0c7950e3f64a6f00c55272a65e7cb3472e1d63aac38ddd5b1`.

No sorry, axiom, analytic assumption, canonical field or resource limit was
introduced or changed. Three semantic-root imports were added. Full-root
build, full axiom audit, guard and progress
suite were NOT run. This is targeted verification, not a current full-tree
audit.
