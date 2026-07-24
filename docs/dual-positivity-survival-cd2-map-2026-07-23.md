# Dual-positivity survival pins: exact CD-2 scope

## Result

The supplied exact-rational regression pins are strong evidence for a
**positive-channel route** to the reflection part of CD-2.  In particular,
the `(1,1,1,1)` rim channel has an exactly resummed activity

\[
  A_{\rm rim}(s)
    = \frac14 + \frac92 s^{16} + 6s^{24}
      + \frac{21}{4}s^{32},
\]

and its twelve-sector page-spin ledger is termwise positive and resums exactly
to that activity.  The sectors form four permutation orbits of sizes
`1,6,4,1`; the displayed polynomial is their four-**monomial**,
exponent-compressed sum, not a four-entry page-spin ledger.  This is the right
algebraic shape for one positive diagonal channel of a reflected boundary
Gram.

It is not yet a `SpinFoamRPBlockRemainder` certificate.  The executable
regression module, exact integrator, manifest exporter, and note,

```text
computations/dual_positivity_survival.py
computations/exact_haar_network.py
computations/dual_positivity_manifest.py
```

are present in the workspace.  What is missing is a Lean semantic theorem
identifying the scalar rim activity with a matrix element of the physical
finite-box spin-foam term,
and the remaining channels have not been shown to form a complete reflected
boundary decomposition.  The named Lean production interface
`SpinFoamRPBlockRemainder` is also still only a planned name: there is no
declaration with that name in `lean/YMGap`.

The route is now known to require a signed complete channel ledger.
Universal nonnegativity of resolved fixed-face amplitudes is false: a
cutoff-two labelling on the boundary of one four-cube has exact Haar
amplitude `-1/196608`.  Thus the positive rim channel may contribute one
Gram square, but it cannot be promoted to an entrywise-positive statement
about every resolved dual channel.  This does not refute (DP), which concerns
the complete physical-complex sum over every induced fusion channel and edge
intertwiner.

The negative fixed-face witness is not a counterexample to the complete
binary-surface-pair sum.  Retaining duplicate fundamental strands at a
crossing edge gives the full two-dimensional
`Inv((1/2)^(tensor 4))` projector.  All 100 four-cube symmetry orbits of
intersecting pairs have positive complete sums, even though six ledgers
contain negative resolved channels.  The regression pair
`(0x4ab33,0x6bc6ad)` contains four `-1/196608` channels but sums exactly to
`31/331776`.  This is the model CD-2 must follow: signed channel completeness
first, Gram positivity only after the intertwiner sum.

The signed four-cube ledgers now also have an exact structural resummation.
Their overlap graphs are `K_(2,2)`, `K_(2,4)`, and `K_(4,4)`, with local
two-channel weight

\[
 W=\begin{pmatrix}1&1\\1&-1/3\end{pmatrix}.
\]

The complete graph sum is

\[
 Z_{m,n}=\sum_{r=0}^m\binom mr
   \left(1+(-1/3)^r\right)^n>0.
\]

This proves the six cancellation-requiring ledgers after their finite
four-cube classification; the other 94 ledgers are termwise nonnegative.
It is not an all-complex or reflected-boundary theorem.

The complete exact `128 x 128` binary-surface Gram is also now executable.
All 8,256 unordered entries are positive, and strict row diagonal dominance
gives an explicit nonnegative-coordinate rank-one factorization.  This is a
finite positive-definite certificate for the one-four-cube binary sector.
It does not construct the CD-2 physical block kernel, prove its pushforward
identity, or supply a cutoff-independent norm.

The first higher-valence follow-up is also finite but positive.  On the
minimal `[0,1] x [0,2]^3` brick, a distinguished interior link is incident
to six plaquettes.  All 65 stabilizer orbits of pairs in the 66-surface
two-cube-composite family have positive complete duplicate-character
amplitudes.  Ten orbits activate all six central plaquettes.  This is not an
exhaustive survey of the brick's 44-dimensional binary-surface kernel and
does not yet provide the physical reflected-channel map required below.

The associated exact `66 x 66` Gram is strictly diagonally dominant:

\[
 \min_i G_{ii}-65\max_{i\ne j}G_{ij}
 =\frac{6562}{6561}-65\frac{31}{3888}
 =\frac{50587}{104976}>0.
\]

It therefore has an explicit nonnegative-coordinate rank-one
factorization.  This closes a finite six-valent Gram cone, but the uniform
bound first fails at 127 observables and cannot cover the 4,096-surface
closure of the 12 local generators.  A weighted/orbitwise gluing estimate is
still required before this can inform a cutoff-independent CD-2 norm.

The weight-three shell already contains 220 surfaces, nine surface orbits,
and 568 pair orbits.  Direct quaternion-polynomial contraction does not
finish its first duplicated diagonal at practical cost despite greedy link
elimination.  CD-2 exploration should therefore implement a local
fusion-tree projector block at the six-valent link and validate it against
the complete weight-two census before any weight-three sign claim.

## What each pin establishes

### P0 — single cube

The exact values `1`, `1/16`, and `1/81` for uniform spins `0`, `1`, and `2`
are normalization and Euler-power checks for a closed bivalent network.  They
test the integrator and show positivity on three closed-surface fibers.  They
do not test a block kernel, reflection boundary, or overlap remainder.

### P1 — two cubes

The small structured table gives five nonzero positive amplitudes and the
expected parity zero.  This is a useful shared-link sanity check, but it
enumerates only a structured slice.  It does not prove completeness of the
two-plaquette state list or nonnegativity of every boundary matrix entry.

### P1b — slab

The pinned slab values are positive at the displayed even walls and vanish at
one odd wall.  The test itself correctly labels this circuit
“not SOS-protected.”  These values therefore cannot be used as an RP
certificate without a separate reflected-Gram factorization.

### P2 — wheel

The hand-reduced and symmetric spin-two wheel values are positive, the
all-ones wheel vanishes by a genuine selection rule, and the cutoff-one sweep
has no negative entry.  The subsequent exact search found 1,213 nonzero
amplitudes through doubled spin three and no negative value.

More importantly, the search led to an all-label identity.  Expanding the
rim characters into matrix coefficients and applying the multiplicity-one
trivalent Haar projector gives

\[
 W(j;m)=\frac{1}{\prod_i(m_i+1)}
 \sum_{a_0,\ldots,a_3}
 \left|\sum_{b_0,\ldots,b_3}
 \prod_i C[j_i,a_i;m_i,b_i\mid m_{i-1},b_{i-1}]\right|^2 .
\]

Thus P2 wheel positivity is an all-label theorem, not merely a finite
falsification result.  The exact quaternion integrator and an independent
Clebsch--Gordan implementation agree on zero, nonzero, symmetric,
asymmetric, and spin-three witnesses.  This theorem is still about the
gauge-fixed wheel topology; it does not prove that the wheel channels exhaust
the physical block boundary.

### P3 — rim channel

This is the load-bearing new signal.  The exact polynomial is positive on the
unit interval, each reported ledger contribution is positive, and the ledger
resums exactly.  The P2 squared-norm identity strengthens this: for every
fixed rim labelling, every heat-kernel page coefficient is nonnegative at
arbitrary label, because the fusion sum is finite and its dimension and heat
weights are positive.  An exhaustive check of all 81 rim patterns through
label two independently found 590 positive resolved sectors, 354
nonnegative aggregate coefficients, and exact reconstruction in every case.

Conditional on the semantic bridges below, the displayed unit-rim ledger can
discharge one theorem of the form

```text
rimChannelGramContribution_nonnegative
```

for the `(1,1,1,1)` channel.  It cannot by itself discharge full block
pushforward exactness, row normalization, total remainder zero, or
reflection-cone preservation for arbitrary boundary data.

## Exact map required from Python to the physical Lean objects

The following bridges must be proved in this order.  Each equality should be
an exact `Q'.eqv`, not a floating-point comparison.

1. **Export the executable certificate boundary — DONE.**
   `computations/dual_positivity_manifest.py` recomputes the actual oriented
   wheel words, all twelve unit-rim sectors, their raw Haar amplitudes,
   dimension products, heat exponents, weighted coefficients, and the
   aggregated activity.  It independently checks the sector resummation
   against the direct heat-activity contraction and emits canonical JSON with
   SHA-256
   `f7ad2fd06add0c8e5bc51e4aa340bdb0e86687f52d664d3ce3397f21be5d2e52`.
   This is a stable translation boundary, not yet a Lean semantic theorem.

2. **Pin the geometry.** Identify the cube, double-cube, slab, wheel, and rim
   graph edges with explicit sublists of
   `CompactDualPhysicalData.faceEdges` and
   `CompactDualPhysicalData.enumeratedLinks`.  Orientation and reflection must
   agree with the finite-box `Z4HalfTimeReflection*` conventions.

3. **Prove integrator semantics.** For each graph, identify the Python
   integral with the corresponding finite fiber sum of
   `CompactDualPhysicalData.physicalTerm` over
   `explicitPhysicalLabellings D.cutoff D.boxExtent`.  This is the bridge that
   prevents a detached spin-network surrogate from being substituted for the
   physical packet-graph identity.

4. **Pin the coupling coordinate.** Prove what the polynomial variable `s`
   denotes and translate every exponent to the exact rational
   `D.reflectionWeightQ mode = D.coupling^(4*C₂(mode))`.  Positivity on an
   abstract interval is insufficient until the physical coupling lies in that
   interval and the exponent convention agrees.

5. **Pin the boundary channel.** Map the four rim labels to modes of
   `DualBoundaryState D`, with `(1,1,1,1)` represented in the actual boundary
   packet at `D.cutoff`.  State explicitly what happens when `D.cutoff < 1`.

6. **Reconstruct the scalar activity.** The current Lean door records the
   complete twelve-sector ledger as four exact permutation orbits:
   multiplicities `1,6,4,1`, representatives
   `(0000),(0022),(0222),(2222)`, exponents `0,16,24,32`, and per-sector
   coefficients `1/4,3/4,3/2,21/4`.  It proves every orbit contribution
   nonnegative and proves exact resummation to the displayed four-monomial
   polynomial.  Still needed is a semantic theorem deriving this orbit data
   from the exact-Haar program rather than restating its regression output.
   The regression rationals are expected theorem outputs, not axioms or
   fields of a certificate.

7. **Lift scalar positivity to a Gram channel.** Exhibit the actual boundary
   linear functional `L_rim` and prove

   \[
     Q_{\rm rim}(B)
       \simeq A_{\rm rim}(D.coupling)\,L_{\rm rim}(B)^2.
   \]

   Only this square factorization turns the scalar sign check into a
   reflection-positive quadratic contribution.

8. **Prove channel completeness.** Decompose the complete two-plaquette
   reflected boundary quadratic into the rim term plus every other channel.
   Every residual channel must either have its own nonnegative square ledger
   or be retained explicitly in the overlap remainder.  No omitted channel
   may be set to zero by definition.

9. **Construct the physical block kernel.** On the actual fine and coarse
   labelling lists, give a source-dependent kernel and prove pointwise
   nonnegativity, row normalization, target support, and exact compatibility
   with the packet-graph pushforward.

10. **Define rather than discard the remainder.** For each coarse
    configuration, define

    \[
      R_{\rm overlap}(y)
        := \sum_x \mu_{\rm fine}(x)K(x,y)-\mu_{\rm coarse}(y),
    \]

    then prove the pointwise decomposition and
    `listQSum R_overlap coarseStates ≈ 0`.  The existing `15/16`
    shared-link mismatch must appear in this ledger; a construction that
    makes it disappear fails the gate.

11. **Add the CD-3 norm only after exactness.** Equip the same explicit
    remainder with the proposed weighted norm and prove the
    cutoff/volume-uniform `c*(1-w)^2` estimate with `c` returned as
    Type-level data.

## Honest Lean production interface

The eventual interface should be indexed by *two actual*
`CompactDualPhysicalData` values, not by detached state spaces:

```text
SpinFoamRPBlockRemainder (fine coarse : CompactDualPhysicalData)

kernel :
  EdgeLabelling -> EdgeLabelling -> Q'
kernel_nonnegative
kernel_row_normalized_on_actual_lists
kernel_supported_on_actual_coarse_list

overlapRemainder : EdgeLabelling -> Q'
pushforward_decomposition :
  sum fine.physicalTerm * kernel
    ≈ coarse.physicalTerm + overlapRemainder
overlapRemainder_total_zero

boundaryChannelMap
boundaryChannelMap_eq_kernel_readout
reflected_quadratic_channel_decomposition
reflected_quadratic_nonnegative
```

The boundary-map equality is essential.  Merely returning
`ReflectionConeCertificate (boundaryChannelMap B)` would be vacuous here,
because CD-1 already proves the Schur self-Gram nonnegative for every packet;
it would not say that the map came from the physical block kernel.

The residual constructor theorem should therefore have the shape

```text
parametricSpinFoam_block_pushforward_decomposition
  (geometry : PhysicalTwoPlaquetteGeometry fine coarse)
  (integrator : ExactHaarNetworkSemantics geometry)
  (channels : CompletePositiveBoundaryChannelDecomposition integrator)
  (kernel : PhysicalNormalizedBlockKernel integrator)
  :
  SpinFoamRPBlockRemainder fine coarse
```

The supplied P3 ledger contributes to `channels`; it does not construct
`geometry`, `kernel`, or the complete channel decomposition.

Here `channels` can no longer mean that every fixed-face scalar is
nonnegative.  It must mean a complete **signed** decomposition together with
a proof that the assembled reflected boundary quadratic is positive
semidefinite.  The exact four-cube witness

```text
(2,1,1,1,1,2,0,1,1,0,1,1,0,1,1,0,1,1,1,1,0,1,1,0)
```

and its value `-1/196608` must be a regression/semantic pin: any proposed
physical bridge that makes it nonnegative has lost the actual recoupling
sign.

## Falsification gates before claiming CD-2 progress

1. The executable code must continue to reproduce every supplied rational
   exactly.
2. Permuting graph orientation or applying the repository reflection must
   preserve the claimed channel identification.
3. Exhaustive state enumeration must agree with the production finite lists;
   structured subsets are not completeness checks.
4. The polynomial sign routine must certify the closed physical coupling
   interval, including endpoints, with exact arithmetic.
5. The complete boundary matrix, not only its diagonal or one scalar channel,
   must admit a Gram/SOS decomposition.
6. Every cutoff-one boundary pattern must be checked before the cutoff is
   increased; then the same test must pass at cutoffs two and three.
7. The kernel must remain positive and row-normalized after the shared link is
   integrated.  Product rows are already known to fail in this geometry.
8. The exact `15/16` mismatch must be recovered in
   `R_overlap`, and the full remainder must sum to zero.
9. A negative wheel/rim channel at any cutoff, an incomplete signed
   recoupling ledger, or failure to reproduce the exact four-cube value
   `-1/196608` blocks the proposed bridge.  Negative fixed-face sectors must
   be retained and controlled in the assembled reflected Gram rather than
   being averaged away.
10. Growth of the weighted remainder constant with cutoff or box volume
    blocks CD-3 even if the finite CD-2 equality succeeds.

## Immediate next executable step

The manifest is exported and pinned, but the four-cube no-go result changes
the immediate priority.  First identify whether the negative cutoff-two
orbits occur in the actual two-plaquette reflected boundary fiber and define
the complete signed channel ledger.  In parallel, prove that the oriented
wheel is its claimed finite fiber and formalize the all-label
Clebsch--Gordan squared-norm identity for that positive subchannel.  The
assembled boundary quadratic—not each fixed-face entry—must then receive the
Gram proof, normalized block kernel, and explicit overlap remainder.
