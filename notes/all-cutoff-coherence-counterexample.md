# Counterexample to independent stretched-face coherence

Date: 2026-07-24

## Candidate

For each coarse face, take the stretched output of its four fine labels:

\[
j_{\mathrm{coarse}}=\sum_{f\mapsto F}j_f.
\]

This output always occurs in the local four-fold fusion product, so it gives
strictly positive mass to every individual face factor. It was the simplest
possible candidate for extending the cutoff-one physical Gibbs pushforward
to arbitrary cutoff.

## Exact counterexample

Use coarse slab extent \(1\), fine slab extent \(2\cdot1+1=3\), fine cutoff
one, and the spin-\(\tfrac12\) boundary of the unit cube

```text
base       = (0,0,1,1)
directions = (0,2,3)
```

Its six doubled-spin-one faces are

```text
((0,0,1,1),(0,2))  ((0,0,1,2),(0,2))
((0,0,1,1),(0,3))  ((0,0,2,1),(0,3))
((0,0,1,1),(2,3))  ((1,0,1,1),(2,3))
```

Every fine link sees either zero or two spin-one faces, so every exact SU(2)
invariant multiplicity is positive. The fine Gibbs term is therefore
positive.

The independently stretched dyadic target has exactly one nonzero coarse
face:

```text
((0,0,0,0),(2,3)) -> 2
```

This label is within the lossless coarse cutoff \(4\), but each of its four
boundary links sees a single spin-two representation. The invariant
multiplicity at all four links is zero. Thus the complete coarse link product
vanishes even though every chosen face channel is locally positive.

## Implication

The all-cutoff physical coherence theorem cannot be proved by selecting
positive final spins independently on coarse faces. It must transport the
fine intertwiner field jointly through the dyadic block, or sum over a
globally constrained coarse spin/intertwiner field before selecting a
positive witness.

This narrows the actual missing constructor to a tensor-network statement:

> A nonzero fine invariant tensor network, contracted inside a dyadic block,
> has at least one nonzero boundary spin-network coefficient.

That statement is a finite-dimensional completeness/nondegeneracy theorem,
not a collection of facewise Clebsch–Gordan estimates. It is the appropriate
next route to an all-cutoff Gibbs pushforward.

The executable witness is pinned in
`computations/general_cutoff_coherence_scout.py` and
`tests/test_general_cutoff_coherence_scout.py`.
