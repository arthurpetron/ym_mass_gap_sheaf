# Physical Gibbs semantic gap

Date: 2026-07-24

## Finding

The current corrected-slab law is defined by

\[
\texttt{slabParametricKPhysicalTerm}
=
\left(\prod_f \operatorname{coeffW}(j_f)\right)
\left(\prod_e \dim\operatorname{Inv}
  \bigotimes_{f\ni e}V_{j_f}\right).
\]

This is a useful nonnegative multiplicity-product measure. It is not yet
identified with the exact dual coefficient obtained by expanding the Wilson
or heat-kernel lattice action and performing all Haar integrals.

After each edge Haar integral, the invariant projector has the form

\[
P_e=\sum_{\iota_e}|\iota_e\rangle\langle\iota_e|.
\]

The projectors are then contracted through the vertices of the two-complex.
Those contractions produce signed recoupling amplitudes. Their value is not
the product of the ranks of the projectors.

## Exact witness

On the boundary two-skeleton of the unit four-cube, take the pinned
cutoff-two face assignment

```text
encoding = (0x6F6D9E, 0x21)
```

Every one of the 32 edge invariant spaces has multiplicity one, so the local
multiplicity product is exactly

\[
\prod_e\dim\operatorname{Inv}(\cdots)=1.
\]

The independent quaternion Haar integrator and the product of the sixteen
exact vertex \(6j\) symbols agree on

\[
A(j)=-\frac1{196608}.
\]

Thus local admissibility and positive multiplicity product do not identify
the physical dual amplitude, even when every intertwiner space is
one-dimensional.

## Consequence for the route

The completed cutoff-one slab pushforward and remainder are exact for the
nonnegative multiplicity-product slab law. They must not yet be described as
the actual Yang–Mills Gibbs pushforward or actual physical remainder.

Before the requested physical remainder exists, one of the following must be
constructed:

1. the exact finite corrected-slab Haar-network amplitude, including all
   vertex/intertwiner contractions, followed by a proof of (DP) or a signed
   treatment; or
2. a theorem identifying a complete fusion/intertwiner sum of those
   amplitudes with a nonnegative effective coefficient used by the block map.

The exact dual-positivity program is therefore not ancillary. It is the
semantic bridge required to replace the multiplicity-product surrogate by
the actual physical law.

The regression witness is implemented in
`computations/physical_gibbs_semantic_audit.py` and
`tests/test_physical_gibbs_semantic_audit.py`.
