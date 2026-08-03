# BF4 cutoff-one Haar-five Lean certificate

The executable cutoff-one calculation gives two sparse polynomials on the
five based cycles `[0,4,5,6,10]`:

```text
R(w) = 1 + 4 w^18
C(w) = 1 + 32 w^18 + 96 w^30 + 224 w^36 + 192 w^42 + 3 w^48.
```

The constructive Lean lift now has four checked layers.

1. `BF4CutoffOneBinarySurfaceCertificate` generates the rank-seven binary
   surface space from seven masks, proves that the 128 masks are distinct and
   closed, checks the complete `(V,E,F,chi)` census, and derives `R` and `C`.
2. The same module checks the exact polynomials

   ```text
   C - R   = 28 w^18 + 96 w^30 + 224 w^36 + 192 w^42 + 3 w^48
   C - R^2 = 24 w^18 + 96 w^30 + 208 w^36 + 192 w^42 + 3 w^48
   ```

   and the ten-term expansion of `(C-1)(C-R^2)`.  A generic constructive
   coefficient lemma proves all three are strictly positive for `w > 0`.
3. `BF4CutoffOneBinarySurfaceEmbedding` embeds the compact 24-face masks into
   the literal corrected-slab order.  Kernel computation verifies all 128
   embedded masks are distinct closed labels against the actual 72 plaquette
   boundaries and all 116 link blocks.  It also checks face-count preservation
   and the two vacuum-row masks.  A transparent XOR elimination reduces the
   literal 116-by-72 incidence table to 65 pivots and the seven free columns
   `[0,1,3,6,9,19,39]`; each embedded generator owns exactly one of those
   coordinates.  Generic constructive proofs show that XOR elimination
   preserves the row kernel and that literal even-incidence closure implies
   all 65 echelon constraints.  Triangular reconstruction from the seven free
   coordinates then proves the exact equivalence: a bounded slab mask is
   closed if and only if it belongs to the 128-mask embedded list.  The same
   module now also proves, for every certified compact surface, that the
   literal cutoff-one heat-kernel face product is exactly
   `(2 * w^3)^F`, where `F` is its checked face count
   (`embeddedSurfaceFaceFactor_exact`).
4. `BF4ExactCutoffOneHaarFiveEvaluation` now closes the complete finite
   topological-sum/QPoly assembly.  Its checked singleton-monomial and list
   assembly lemmas identify the 128-term constant sum and two-term vacuum-row
   sum with the sparse polynomials above.  It also proves, pointwise for every
   embedded binary surface, that the literal 116-link Haar coefficient equals
   an exact fivefold marginal on the based cycles `[0,4,5,6,10]`.  The smallest
   nonempty surface is additionally pinned to its six literal raw slab words,
   partitioned into seven local tree links and five chords; the resulting
   256-term compact polynomial has kernel-checked Haar value `1/16`, exactly
   `2^(8-12)`.  The binary-surface certificate additionally checks that all
   128 surfaces are edge-bivalent: every physical edge has selected-face
   valence zero or two, so no higher-valent link intertwiner enters this
   pointwise campaign.

An independent exact quaternion audit contracts one literal gauge-fixed
surface network from each of the nine hyperoctahedral surface orbits.  All
nine representatives agree with `2^(V-E)`, and their orbit sizes cover all
128 surfaces.  This is executable finite evidence; the symmetry transport
and uniform bivalent contraction still have to be kernel-checked in Lean.

`BF4ExactCutoffOneHaarFiveEvaluation` exposes the remaining bridge as the
uninhabited proposition `CutoffOneBinarySurfaceHaarBridge`.  Conditional on
that one honest bridge, the existing 116-link-to-five-cycle theorems yield the
two closed forms, the strict order `R(w) < C(w)`, and the exact positive
centered numerator `C(w)-R(w)^2` for every `w > 0`.

The summary bridge is factored into named interfaces:

- `CutoffOneCharacterExpansionReindex` identifies the actual two fivefold
  Haar expressions with literal corrected-slab dual sums;
- `CutoffOneClosedSurfaceTopologicalAmplitude` asks pointwise for the signed
  contraction `2^(V-E)`; the new pointwise theorem reduces this exactly to
  128 fivefold Haar evaluations;
- `CutoffOneClosedSurfaceSumEvaluation` packages the resulting two finite
  sums as the checked sparse polynomials, and is now constructed
  unconditionally from the pointwise amplitude interface.

Lean proves that the pointwise amplitude, together with the exact face-factor
theorem, reduces every dual summand and both relevant finite sums to their
explicit topological targets.  It also proves that the character reindex and
finite-sum evaluation compose to the original summary bridge.

The bridge now has two sharply separated mathematical tasks remaining; the
heat-weight and QPoly-assembly halves are no longer part of either:

- derive the actual fivefold character expansion as the finite closed-label
  sum (`CutoffOneCharacterExpansionReindex`);
- evaluate the 128 pointwise fivefold surface marginals as `2^(V-E)`.  The
  six-face sphere's compact five-chord value and all nine exact orbit
  representatives are complete; the still-open step is to kernel-check the
  hyperoctahedral transport and generalize the local tree-pruning contraction
  to the now-certified bivalent surfaces, connecting it uniformly to each
  requested based-cycle marginal.

No new axiom, `sorry`, `native_decide`, classical choice, or noncomputable
declaration is used.  The checked dependency sets are contained in
`[propext, Quot.sound]`.
