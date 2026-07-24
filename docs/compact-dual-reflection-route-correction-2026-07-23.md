# Compact-dual CD-2 reflection-route correction

## Decisive obstruction

The originally named CD-2 semantic target,
`CompactDualPhysicalData.physicalTerm`, is built on the legacy
`boxPlaquettes n` face enumeration.  That enumeration is not closed under
half-time reflection at any nonempty extent.

The bottom spatial plaquette

```text
((0,0,0,0), p01)
```

is in `boxPlaquettes n`, while its geometric reflection is

```text
((0,0,0,n), p01),
```

whose base time is outside `[0,n)`.  This is not a numerical accident.
`Z4HalfTimeReflectionGeometry.lean` already proves:

```text
not_physicalFaceReflectionClosed
no_physicalFaceReflectionReindex
```

Therefore no exact reflection-intertwining theorem for the legacy physical
term can be obtained by permuting its existing physical face coordinates.
The old CD-2 wording was structurally impossible as stated.

## Correct physical geometry

The same Lean development constructs the boundary-complete slab:

- spatial plaquette bases on time slices `0,...,M`;
- temporal plaquette bases on `0,...,M-1`;
- vertex reflection `t -> M-t`;
- the required one-step base shift for temporal links and plaquettes.

`computations/dual_half_time_reflection_route.py` mirrors this geometry and
constructs the exact face-ID reflection involution.  At central extent
`M=3`, it also pins the lower direction-zero page carrier at time `1` and its
upper partner at time `2`.  Each has the required four `01/02` active pages
and two `03` temporal pages, and the face permutation maps all six incident
faces exactly to the reflected six.

## Required program change

CD-2 must choose one of two honest routes:

1. define the full coupling-parametric, fusion-complete physical spin-foam
   term directly on the corrected slab faces and links; or
2. construct an exact, reflection-compatible bridge from the legacy
   `CompactDualPhysicalData.physicalTerm` to that corrected slab term.

The first route is cleaner and matches the existing half-time reflection
theorems.  The second carries an additional comparison remainder and would
need its own uniform norm.

The recommended immediate action is to introduce
`CompactDualSlabPhysicalData`, pinning:

```text
boundaryCompleteSlabPlaquettes
boundaryCompleteSlabLinks
slabPhysicalFaceEdges
slabParametricKPhysicalFaceFactor
corrected-slab explicit link multiplicities
corrected-slab physicalTerm
slabFaceReflectId
```

The first four objects and the face-factor reflection theorem already exist.
The load-bearing missing field is the corrected-slab full link-multiplicity
product/physical term on the same enumeration.

Only this corrected object should index
`SpinFoamRPBlockRemainder`.  Once it exists, the four-rim carrier can be
assigned physical half-time slot IDs and the exact-Haar semantic comparison
can target a reflection-closed finite measure.

## Effect on the continuum route

This does not close RG-I7, RG-I8, RG-I9, or any uniform gap estimate.  It
removes a fatal mismatch before those estimates are attempted.  A contraction
theorem on a non-reflection-closed finite carrier could not compose with the
OS limit, so correcting the CD-2 datum is necessary for spacing-uniform gap
survival.
