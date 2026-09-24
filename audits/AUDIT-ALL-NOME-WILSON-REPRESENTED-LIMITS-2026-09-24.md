# SAME Wilson represented limits and unique-link geometry — 2026-09-24

## Outcome and scope

Baseline: `b95a514`. The EXISTING literal-width all-nome Wilson completion
now has its actual squared distance and computed represented limits.
Discrete time commutes with these limits, and its actual vacuum complement
is closed under them. A separate finite-geometry proof exposes a selected
link occurring exactly once in every padded dyadic Wilson square.

These are partial J02 and A03 inputs, respectively. No carrier replacement,
arbitrary quotient-representative selection, real-scalar extension, growing-loop
variance floor, scaling-survival result, continuum construction or physical
mass theorem is asserted. The whole-project Clay goal remains open.

## Actual distance, not an assumed completeness field

`BF4WilsonAllNomeDistance.completedDist`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDistance.lean:52`) is exactly
B(x-y,x-y), using the existing all-nome completed subtraction and pairing.
`representativeDist_converges` (`:60`) identifies its actual Cauchy limit.
`completedDist_nonnegative` (`:66`), `completedDist_symm` (`:77`),
`completedDist_triangle` (`:97`) and `completedDist_zero_iff` (`:109`)
prove its laws. The triangle estimate is the SQUARED-distance law
d(x,z) <= 2*d(x,y)+2*d(y,z), not a claimed unsquared metric triangle.
`distanceData` (`:125`) fills the existing generic distance interface with
these proofs; it does not assume completeness.

## Computed represented limits and their consumers

All declarations in this section belong to
`lean/YMGap/Continuum/BF4WilsonAllNomeCauchyRows.lean`.

- `denseApproximation` (`:46`) returns an actual dense expression and a
  completed-distance certificate from a supplied representative's modulus.
- `RepresentedCauchy` (`:54`) is the existing generic row type instantiated
  with the proved actual distance. Each row supplies a Cauchy representative
  and its inner modulus; the outer modulus measures completed distance.
- `limit` (`:59`), `limitRate` (`:62`) and `limit_bound` (`:67`) construct
  the diagonal limit and its rate R.modulus(epsilon/16). The reused generic
  `CRealSeminormCauchyRows.diagonalRate`
  (`lean/YMGap/Continuum/CRealSeminormCauchyRows.lean:66`) is
  max(R.modulus(epsilon/16),(epsilon/16).den). Both layers of rates remain data.
- `limit_unique` (`:74`), `limit_independent` (`:81`) and `limit_original`
  (`:87`) establish uniqueness, independence of supplied representatives
  of the same points, and recovery of an original Cauchy stream's class.
- `completedDist_time` (`:93`) applies the actual time contraction to the
  actual difference. `timeRows` (`:101`) retains the outer modulus and the
  representative map retains each inner modulus. `timeRows_modulus` (`:111`)
  and `timeRows_rowPoint` (`:114`) record these pins.
- `limit_timeRows` (`:119`) is definitional equality: the same diagonal
  sampling indices are used before and after pointwise temporal advance.
- `limit_orthogonal` (`:158`) proves closure of the existing vacuum complement.
  With L the computed limit, each row's orthogonality gives
  B(U,L)=B(U,L-row_n). The actual unit norm and sharp Cauchy--Schwarz yield
  B(U,L)^2 <= B(L-row_n,L-row_n). The explicit row-limit bound forces the
  pairing to zero constructively. `orthogonalLimit` (`:181`) returns the
  corresponding state in the PRE-EXISTING vacuum-complement subtype.

This does not lift an arbitrary Nat-to-quotient sequence to representatives.
No countable choice, new centering projection, or real-scalar action is used.
Nome and spatial width remain fixed throughout each such limit.

## The finite-geometry input and the still-missing Haar calculation

`BF4DyadicWilsonSquareUniqueEdge.squareEdges_succ`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareUniqueEdge.lean:44`) splits a
positive-side square into its literal selected head and tail.
`selectedLink_not_mem_squareTail` (`:114`) excludes either orientation of
the underlying selected link from that tail. For padded dyadic squares,
`paddedSquare_edges_split` (`:170`) and `selectedLink_not_mem_dyadicTail`
(`:182`) provide the same decomposition. These equalities plus tail absence
establish exact occurrence count; membership uniqueness alone would not.

The selected edge is the positive x0 link at the origin (`selectedEdge`,
`:24`; `selectedLink`, `:29`). These declarations are finite list/coordinate
geometry. They introduce no coupling-dependent constant or action comparison.

The original observable is still the right-associated product
`BF4ExactSlabFixedSpatialWilsonProbe.sourceWord`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonProbe.lean:101`). Existing
generic one-link Haar consumers include
`genericBlock_orientedOneValentFundamentalTerm_zero_with_complex_spectator`
(`lean/YMGap/Continuum/SU2QuaternionGenericBlockOddValentHaarVanishing.lean:449`)
and `genericBlock_oriented_fundamental_schur_with_complex_spectator`
(`lean/YMGap/Continuum/SU2QuaternionGenericBlockPartialFundamentalSchur.lean:925`).
Both require actual block-independent spectators and an in-range selected
block. The new geometry alone does not supply the polynomial factorization,
spectator-independence proof or first/second moments for that original word.

The existing local comparison is
`BF4ExactSlabLocalStarComparison.original_star_bounds`
(`lean/YMGap/Continuum/BF4ExactSlabLocalStarComparison.lean:120`) and
`original_star_normalized_cross` (`:144`). The currently specialized moment
proofs are `rest_character_zero` and `rest_square_moment`
(`lean/YMGap/Continuum/BF4ExactSlabSelectedStarVariance.lean:121`, `:134`).
No arbitrary-word replacement of those moment proofs is constructed here.
Even an extension of the existing coarse starRatio floor would not close
A03: its known loss-budget limitation remains recorded in
`audits/AUDIT-ALL-NOME-WILSON-EXCITATION-2026-09-24.md`.

## Verification boundary

Three final serialized narrow checks exited zero, printing 40 gates, all
within `{propext, Quot.sound}` (six geometry declarations have empty axiom
sets). No full-root build, full-tree audit or guard was run.

| Leaf | Final log | Printed gates |
|---|---|---:|
| `BF4WilsonAllNomeDistance` | `/tmp/ym-gap-wilson-all-nome-distance-check-2.log` | 12 |
| `BF4WilsonAllNomeCauchyRows` | `/tmp/ym-gap-wilson-all-nome-cauchy-rows-check-3.log` | 16 |
| `BF4DyadicWilsonSquareUniqueEdge` | `/tmp/ym-gap-dyadic-wilson-square-unique-edge-check-3.log` | 12 |

The checks used one worker, a 2 GiB cap, default elaboration limits and the
unchanged 12 GiB reserve. The initial geometry check compiled but exposed
`Classical.choice` in two impossible-case tactic branches and their consumers.
Explicit `False.elim (Nat.not_lt_zero 0 hside)` removed those dependencies.
An implicit-width application error in the row-limit subtype constructor was
also corrected before acceptance. Only the final successful, axiom-clean
source is included in the milestone; no new source hole or analytic premise.

## Canonical chart delta and next causal frontier

Schema 1, snapshot 14 adds proof evidence only. The chart block is unchanged:
same labels, layout, symbols, proof markers and primary active node A03.
B01--B03 retain their recorded face-span scope; no identification with this
all-nome Wilson carrier is asserted. Full J02 remains open.

A03 still requires useful SAME centered variance or nonzero response along
a justified changing-scale family. The original arbitrary-word one-link
moment calculation is now a concrete next producer for the loop-variance
branch, not a proved useful variance estimate. The complete signed-source
and direct-response alternatives remain available. Separately, EVERY-state
spatial/spacing control, SAME thermodynamic/continuum passage, full QFT/YM/UV,
physical Hamiltonian/mass calibration and every compact simple group remain
open. No canonical frontier field or whole-project goal is changed.
