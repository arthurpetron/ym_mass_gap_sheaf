# BF4 cutoff-one Haar-five Lean certificate

The executable cutoff-one calculation gives two sparse polynomials on the
five based cycles `[0,4,5,6,10]`:

```text
R(w) = 1 + 4 w^18
C(w) = 1 + 32 w^18 + 96 w^30 + 224 w^36 + 192 w^42 + 3 w^48.
```

The constructive Lean lift now has three checked layers.

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
   closed if and only if it belongs to the 128-mask embedded list.

`BF4ExactCutoffOneHaarFiveEvaluation` exposes the remaining bridge as the
uninhabited proposition `CutoffOneBinarySurfaceHaarBridge`.  Conditional on
that one honest bridge, the existing 116-link-to-five-cycle theorems yield the
two closed forms, the strict order `R(w) < C(w)`, and the exact positive
centered numerator `C(w)-R(w)^2` for every `w > 0`.

The bridge now has one mathematical package remaining:

- derive the actual fivefold character expansion as the finite closed-label
  sum and prove the fundamental closed-surface Haar amplitude `2^(V-E)`.
  The new literal incidence equivalence then supplies the exact 128-surface
  reindexing automatically.

No new axiom, `sorry`, `native_decide`, classical choice, or noncomputable
declaration is used.  The checked dependency sets are contained in
`[propext, Quot.sound]`.
