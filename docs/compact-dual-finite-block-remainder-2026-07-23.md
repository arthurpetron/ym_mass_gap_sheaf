# Compact-dual finite block remainder gate

## What is now closed

`CompactDualSlabPhysicalData.lean` now exposes the complete corrected-slab
physical summand as a normalized finite law.  It proves:

- nonnegativity of every normalized mass;
- exact total mass one;
- exact invariance of normalized mass under half-time reflection; and
- nonnegativity of the complete normalized reflection quadratic.

`CompactDualFiniteBlockRemainder.lean` then defines one dyadic scale pair with
the reflection-forced affine extent, the lossless four-character cutoff
`K_coarse = 4 K_fine`, and an explicit coupling-flow coordinate.  A
`FiniteSlabKernel` must be nonnegative, row-normalized, source-dependent, and
reflection-intertwining on the literal fine and coarse Cartesian labelling
spaces.

For every such kernel, the retained remainder is computed:

```text
R(y) = sum_x mu_fine(x) K(x,y) - mu_coarse(y).
```

Finite Fubini proves:

```text
sum_y R(y) = 0.
```

Thus zero total mass is not a separate analytic conjecture.  It follows from
normalization once the physical kernel exists.

The same exact algebra proves the cutoff- and volume-independent probability
simplex fence

```text
||R||_1 <= 2.
```

This is the strongest universal estimate possible without using more of the
physics.  It establishes boundedness, not RG smallness.

## What remains open

The current local chain already supplies:

1. a source-dependent character/fusion row;
2. exact reflection intertwining;
3. complete shared-link gluing on a closed six-face cube;
4. the cutoff-one fine-support projector; and
5. exact physical composition for link-separated projected cubes.

`Z4AdjacentCubeCancellationActivity.lean` now closes the first exact
overlap-carrier calculation.  For two adjacent cube boundaries, ordinary
union is not gauge closed: the retained interface-face boundary has
incidence three.  Symmetric-difference gluing deletes both copies of the
shared face and produces a ten-face carrier.  Every touched link then has
incidence exactly two, so the full cutoff-one Haar multiplicity is one and

```text
A_glued(w) = coeffW(w,1)^10.
```

In particular the two independent six-face powers obey the exact correction

```text
coeffW(w,1)^12 = coeffW(w,1)^2 A_glued(w).
```

This is a quantitative shared-link gluing law, not yet a stochastic block
map.  The first open subgate is therefore the globally coupled assembly for
genuinely overlapping blocks with shared fine links.  It must place the
cancelled carrier inside a source-indexed joint state space and normalize
only after every shared production link factor and fine-support/recoupling
projection has been inserted.  Independent local normalization is already
ruled out by an exact zero-mass fence.

After that assembly, two further CD-2 steps remain:

- extend it from the checked cutoff-one projected sector to all bounded spin
  packets on the complete corrected slab; and
- identify the resulting whole-state kernel pushforward with the normalized
  physical Gibbs law at the derived coarse coupling.

Only then does the algebra above produce the physical
`SpinFoamRPBlockRemainder`.

CD-3 is still open even after that: its needed estimate is a vanishing,
cutoff-independent bound such as

```text
||R|| <= c (1-w)^2,
```

in the same norm used by RG-I7.  The universal constant `2` cannot imply
contraction or spacing-uniform gap survival.
