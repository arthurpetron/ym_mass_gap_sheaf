# BF4 cutoff-one Haar-five Lean certificate

The executable cutoff-one calculation gives two sparse polynomials on the
five based cycles `[0,4,5,6,10]`:

```text
R(w) = 1 + 4 w^18
C(w) = 1 + 32 w^18 + 96 w^30 + 224 w^36 + 192 w^42 + 3 w^48.
```

The constructive Lean lift now has six checked layers.

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
5. `SU2QuaternionFactorizedHaarContraction` proves a constructive exact
   variable-elimination algorithm for polynomial factor networks.  At each
   quaternion it multiplies only incident factors, applies the normalized
   `S^3` moment, canonicalizes that local output, and transports every
   independent factor to the remaining blocks.  Its compact variant also
   deletes literal unit factors.  The load-bearing evaluator theorem is
   axiom-audited to `[propext, Quot.sound]`.

   `BF4ExactCutoffOneSurfaceFactorizedHaar` connects this evaluator to the
   actual geometry: the 72 plaquette factors multiply definitionally to the
   original corrected-slab integrand, every literal 116-link embedded-surface
   coefficient equals its factorized value, and therefore every actual
   five-based-cycle marginal equals that same factorized value.  The known
   six-face/five-chord `1/16` calculation is recovered through this common
   evaluator interface.

   `SU2QuaternionBivalentHaarContraction` now specializes the local step used
   by every nonempty binary-surface edge.  When exactly two factors meet the
   head link, it fuses multiplication, the normalized one-link moment, head
   block deletion, and exact-zero filtering.  Lean proves that the filtered
   rational canonical form is the generic partial-Haar result and that the
   complete compact bivalent recursion is the existing factorized recursion.
   The BF4 module therefore exposes a literal 116-link bivalent value and
   proves it equal to both the original slab coefficient and the factorized
   value.  This closes an optimization/correctness seam; it does not by itself
   prove the remaining `2^(V-E)` theorem.

6. `BF4ExactCutoffOneSurfaceActiveCarrier` proves that all 128 literal
   surface integrands use exactly the displayed 32-link unit-four-cube
   carrier, moves those blocks to the front by a checked swap chain, and
   deletes the other 84 normalized Haar variables.  The resulting 32-link
   value is proved equal both to the original 116-link coefficient and to the
   five-based-cycle marginal.

   `BF4ExactCutoffOneSurfaceActiveFactorizedHaar` removes spin-zero faces at
   the source, before their padded unit monomials can enter contraction.  For
   every nonempty certified mask it proves the literal coefficient equal to
   a selected-face, 32-link fused evaluator carrying at most sixteen genuine
   factors.  Its 127-case premise is proved equivalent in both directions to
   the original pointwise topological-amplitude interface; the empty surface
   is already evaluated exactly.

   `BF4CutoffOneSurfacePrimalForestCertificate` reconstructs the actual
   16-vertex/32-edge four-cube graph from the existing incidence tables and
   kernel-checks deterministic maximal forests for all 128 masks.  It also
   supplies orientation-aware rooted paths and checks that the surviving
   chord count is `E-V+C` on every surface.

   `BF4ExactCutoffOneSurfaceForestGauge` ties the compact 24 face words back
   to the literal corrected-slab geometry and defines the concrete
   chord-only evaluator obtained by deleting each checked forest.  The final
   seam is now split into Haar-preserving forest transport and exact
   evaluation of that concrete network.  The generic evaluator has
   kernel-checked values for two explicit 6-face/5-chord masks, one
   10-face/9-chord mask, both connected 12-face/11-chord orbit
   representatives, and the disconnected two-sphere 12-face/10-chord
   representative, both 14-face/13-chord representatives, and the unique
   16-face/17-chord toroidal representative, each equal to `2^(V-E)`.  Thus
   all eight nonempty orbit representatives are kernel-checked.  Orbit
   computations live in separate modules so each expensive kernel reduction
   is cached independently.  The toroidal case uses seventeen generated
   proof-carrying checkpoints; Lean independently decides every exact
   checkpoint and the final `1/65536` value.

An independent exact quaternion audit contracts one literal gauge-fixed
surface network from each of the nine hyperoctahedral surface orbits.  All
nine representatives agree with `2^(V-E)`, and their orbit sizes cover all
128 surfaces.  This is executable finite evidence; the symmetry transport
and uniform bivalent contraction still have to be kernel-checked in Lean.

`BF4ExactCutoffOneHaarFiveEvaluation` exposes the remaining bridge as the
proposition `CutoffOneBinarySurfaceHaarBridge`.  Conditional on that one
honest bridge, the existing 116-link-to-five-cycle theorems yield the two
closed forms, the strict order `R(w) < C(w)`, and the exact positive centered
numerator `C(w)-R(w)^2` for every `w > 0`.

The summary bridge is factored into named interfaces:

- `CutoffOneCharacterExpansionReindex` identifies the actual two fivefold
  Haar expressions with literal corrected-slab dual sums;
- `CutoffOneClosedSurfaceTopologicalAmplitude` asks pointwise for the signed
  contraction `2^(V-E)`; the new pointwise theorem reduces this exactly to
  128 fivefold Haar evaluations;
- `CutoffOneClosedSurfaceSumEvaluation` packages the resulting two finite
  sums as the checked sparse polynomials, and is now constructed
  unconditionally from the pointwise amplitude interface.

`BF4ExactCutoffOneSurfaceCharacterReindex` now inhabits the first interface.
It encodes every bounded 72-face labelling as a bit mask, constructively
extracts an odd physical-link incidence from every nonclosed mask, annihilates
that summand by selected-block Haar Fubini, and permutes the surviving kernel
exactly onto the 128 embedded surfaces.  The same proof filters the physical
vacuum row to its two embedded surfaces.  It does not enumerate the `2^72`
carrier.

Lean proves that the pointwise amplitude, together with the exact face-factor
theorem, reduces every dual summand and both relevant finite sums to their
explicit topological targets.  It also proves that the character reindex and
finite-sum evaluation compose to the original summary bridge.

The bridge now has one sharply separated mathematical task remaining; the
character reindex, heat-weight, QPoly assembly, and exact factor-network
reduction are closed:

- prove that the checked maximal-forest coordinate change transports the
  selected active evaluator to the new concrete chord-only evaluator, and
  prove the finite hyperoctahedral symmetry transport from all 128 masks to
  the eight checked nonempty representatives (or prove the equivalent
  uniform bivalent pairing theorem).  The active/factorized theorems identify
  the source with both the literal 116-link coefficients and the requested
  fivefold marginals.  All 128 forests and rooted paths, all eight nonempty
  Lean orbit values, the six-face sphere's earlier compact five-chord value,
  and all nine external exact orbit representatives are complete.  Direct
  all-116-block and monolithic fixed-order normalization were benchmarked and
  rejected as impractical certificate paths.  The final toroidal value instead
  uses a generated low-width staged certificate whose every transition is
  checked by the Lean kernel.

No new axiom, `sorry`, `native_decide`, classical choice, or noncomputable
declaration is used.  The checked dependency sets are contained in
`[propext, Quot.sound]`.
