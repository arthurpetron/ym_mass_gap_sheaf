# OS/transfer-matrix research checkpoint

Date: 2026-09-27 UTC

This note records an independent literature check performed while the
dependency-heavy `Row64.lean` build was running.  It is guidance for the next
formal certificate boundary, not a new theorem or a claim about the Clay
target.

## Primary references checked

* K. Osterwalder and E. Seiler, “Gauge field theories on a lattice,”
  *Annals of Physics* 110 (1978), 440–471, DOI
  [10.1016/0003-4916(78)90039-8](https://www.sciencedirect.com/science/article/pii/0003491678900398).
  The paper establishes physical positivity for the Euclidean lattice
  Schwinger functions and derives a positive self-adjoint transfer matrix.
* M. Lüscher, “Construction of a selfadjoint, strictly positive transfer
  matrix for Euclidean lattice gauge theories,” *Communications in
  Mathematical Physics* 54 (1977), 283–292, DOI
  [10.1007/BF01614090](https://doi.org/10.1007/BF01614090).
* D. Schlingemann, “From euclidean field theory to quantum field theory,”
  [arXiv:hep-th/9802035](https://arxiv.org/abs/hep-th/9802035).  This gives a
  C*-algebraic presentation of the Osterwalder–Schrader reconstruction route,
  including gauge-theoretic observables.

The previously supplied link [arXiv:2608.19068](https://arxiv.org/abs/2608.19068)
is not relevant to this route: it is a differential-geometry paper on a
positively curved metric on `S^2 × S^2`, not a Yang–Mills, reflection-
positivity, or transfer-matrix result.

## Formalization consequence

The references support a strict separation of four certificates:

1. reflection positivity for the *same* finite lattice measure and action;
2. construction and positivity/self-adjointness of the transfer on the
   resulting OS quotient;
3. identification of that transfer with the operator used in the correlator
   estimate; and
4. only then, a uniform limit passage and a physical Hamiltonian statement.

The repository already reflects this separation.  `CompletedPhysicalSU2Sector`
in `lean/YMGap/Continuum/BF4WilsonSpatialUnionCurrentSector.lean:74` packages
the current-carrier transfer and positivity fields, while
`CurrentCarrierBridge` in
`lean/YMGap/Continuum/BF4WilsonSpatialUnionCanonicalGNSBridge.lean:933`
requires explicit map, form-preservation, vacuum, and two-step-intertwining
fields before any canonical GNS conclusion is used.  The pending
`CanonicalRangeSectionCertificate` in the same module is the explicit
surjectivity/range boundary; it cannot be replaced by decay or by a finite
volume gap.

## Next certificate boundary

The next useful producer should therefore be an inhabited, same-measure
OS/transfer identification (including the action/reflection data), not another
selected-vector estimate.  Until that producer and the canonical range
section are inhabited, the existing fixed-spacing response and form bounds
remain conditional image-level statements.  In particular, the literature
does not justify identifying the current-carrier `T` with a physical
Hamiltonian or inferring a continuum mass gap from the finite transfer rate.
