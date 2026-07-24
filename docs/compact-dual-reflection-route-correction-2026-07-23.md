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

## Closed finite-reflection route

The production Lean development already took the first route in full:

- `slabExplicitLinkMultiplicityProduct` is the complete corrected-slab link
  product;
- `slabParametricKPhysicalTerm` and
  `slabParametricKPhysicalPartition` are the physical summand and partition
  on the boundary-complete slab;
- `slabParametricKPhysicalTerm_supported_reflection` and
  `slabParametricKPhysicalPartition_reflection_reindex` prove exact local and
  global reflection invariance;
- `centralPhysicalReflectedKernel_eq_weightedGram` identifies the physical
  reflected kernel with a weighted Gram kernel;
- `centralAssembledSlabLabellings_perm_full` proves that the assembled
  lower/interface/upper states cover the independently enumerated full
  Cartesian slab space exactly once; and
- `centralFullPhysicalReflectionQuadratic_nonnegative` proves constructive
  Osterwalder--Schrader positivity for that complete physical space.

`CompactDualSlabPhysicalData.lean` packages these existing objects as the
single corrected CD-2 datum.  Thus no bridge from the legacy box is needed,
and the finite reflection route is closed.

The next missing CD-2 object is now genuinely scale-to-scale:

```text
fine corrected-slab labelling
  -> positive/reflection-compatible coarse labelling kernel
  + exact retained remainder
```

It must be normalized, preserve the vacuum mass, intertwine the corrected
reflection, and expose its remainder in the same norm later consumed by
RG-I7.  Finite reflection positivity supplies the cone in which that kernel
must act; it does not supply the kernel or contraction estimate.

## Effect on the continuum route

This does not close RG-I7, RG-I8, RG-I9, or any uniform gap estimate.  It
does close the finite physical RP datum on which those estimates must be
built, removing a fatal mismatch before they are attempted.  A contraction
theorem on a non-reflection-closed finite carrier could not compose with the
OS limit; the corrected slab now provides the necessary finite cone.
