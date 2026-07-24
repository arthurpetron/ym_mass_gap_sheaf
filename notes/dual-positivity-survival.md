# Dual positivity survival: exact first probes

**Date:** 2026-07-23
**Code:** `computations/exact_haar_network.py`,
`computations/dual_positivity_survival.py`,
`computations/dual_positivity_manifest.py`
**Regression/falsification gates:** `tests/test_exact_haar_network.py`,
`tests/test_dual_positivity_survival.py`,
`tests/test_dual_positivity_manifest.py`

## Question and normalization

The probes ask whether the coefficients of the SU(2) character-expanded
theory remain nonnegative on the first genuinely three-dimensional
incidence patterns.  This is different from pointwise positivity of the
original Boltzmann weight.

Labels are doubled spins `n = 2j`, dimensions are `d_n = n+1`, and
`4 C_2(n) = n(n+2)`.  The exact Haar engine represents links as unit
quaternions and integrates polynomial character networks with normalized
S3 moments.  The heat-kernel variable remains symbolic as
`s = exp(-t/4)`.  No floating-point arithmetic enters these results.

The network topologies are explicit:

1. `single_cube_table` assigns characters to the six oriented plaquette
   words of the boundary of a 1x1x1 brick.
2. `double_cube_structured_table` uses all eleven plaquette words of a
   1x1x2 brick: five exterior faces per cube and their shared face.
3. `slab_value` uses the twenty plaquettes of a 2x2x1 brick.  Four
   interior walls form the unanchored circuit around its central edge.
4. `wheel_value` contracts

       product_i chi_{j_i}(X_i)
                 chi_{m_i}(X_i X_{i+1}^{-1})

   over four independent Haar links.  This is the gauge-fixed star of an
   interior link with four pages and four rim readouts.
5. `rim_channel_activity` replaces every page character by its finite
   heat-kernel activity.  Fusion makes the sum exact:
   `j_i <= m_{i-1}+m_i`.

For the three brick probes, write `e(p,d)` for the positively oriented
edge from lattice vertex `p` in coordinate direction `d`.  Every face in
the evaluator is the four-edge word

    e(p,d1) e(p+d1,d2) e(p+d2,d1)^-1 e(p,d2)^-1,
    d1 < d2.

The allowed basepoints are exactly those for which all four vertices lie
in `[0,nx] x [0,ny] x [0,nz]`.  Hence this one formula produces the six
faces of the cube, the eleven faces (including the shared `z=1` face) of
the double cube, and the twenty plaquettes of the slab without an
orientation lookup table.  The four slab circuit faces are, cyclically,
the `x=1` walls at `y=0,1` and the `y=1` walls at `x=1,0`.

## All-label P2 theorem: the wheel is an exact squared norm

The wheel admits an analytic positivity proof for every choice of page
and rim labels.  This is stronger than the finite sweeps and depends on
the page-character trace wiring; it is not the false general assertion
that an arbitrary cyclic trace of orthogonal projectors is nonnegative.

For a doubled label `n`, let

    Mag(n) = {-n, -n+2, ..., n}

be its doubled magnetic indices.  Write
`C[j,p; m,q | r,u]` for a unitary Clebsch--Gordan coefficient coupling
`j tensor m` to `r`.  With all cyclic indices read modulo four, define

    A_{j,m}(a_0,...,a_3)
      = sum_{b_i in Mag(m_i)}
          product_i C[j_i,a_i; m_i,b_i | m_{i-1},b_{i-1}].

Then the exact Haar contraction used by `wheel_value` is

    W(j;m)
      = 1 / product_i (m_i+1)
          sum_{a_i in Mag(j_i)} |A_{j,m}(a_0,...,a_3)|^2.

In particular `W(j;m) >= 0` for all doubled-spin labels, with no cutoff.
If a local triple `(j_i,m_i,m_{i-1})` is inadmissible, its Clebsch--Gordan
coefficient vanishes and the whole wheel vanishes.

Here is the normalization derivation.  Expand one oriented rim character
as

    chi_m(X_i X_{i+1}^{-1})
      = sum_{b,c} D^m_{bc}(X_i) conjugate(D^m_{bc}(X_{i+1})).

At link `X_i`, the page trace and its two adjacent rims give

    integral D^j_{aa}(X)
             D^m_{bc}(X)
             conjugate(D^r_{de}(X)) dX
      = C[j,a; m,b | r,d]
          conjugate(C[j,a; m,c | r,e]) / (r+1).

This is Schur orthogonality after decomposing `D^j tensor D^m`; SU(2)
fusion is multiplicity-free.  Multiplying the four link identities
leaves one contraction over the `b` indices and an independent,
complex-conjugate contraction over the `c` indices.  The page trace
forces the same magnetic tuple `a` in both.  Their product is therefore
`|A_{j,m}(a)|^2`, and the four Schur factors multiply to the displayed
dimension denominator.  This matched the independent quaternion-moment
engine exactly on nonzero, zero, symmetric, asymmetric, and spin-three
cases.

Consequently the fixed-rim heat-kernel channel also has nonnegative
coefficients for **all** rim labels: it is the finite fusion sum

    sum_j [product_i (j_i+1)] s^{sum_i j_i(j_i+2)} W(j;m).

Different page tuples can merge at the same power of `s`, but no
cancellation is needed for positivity.

## Machine-readable unit-rim certificate

`computations/dual_positivity_manifest.py` is the executable boundary for a
future Lean semantic translation.  It recomputes the public oriented wheel
words, all twelve nonzero `(1,1,1,1)` page sectors, each raw Haar amplitude,
dimension product, heat exponent, and weighted coefficient.  The activity is
summed from that resolved ledger and checked against the independent direct
heat-activity contraction before serialization.

The canonical JSON certificate has SHA-256

    f7ad2fd06add0c8e5bc51e4aa340bdb0e86687f52d664d3ce3397f21be5d2e52.

This digest pins a translation boundary; it is not evidence that the wheel
has already been identified with a fiber of the physical finite-box
spin-foam term.

## Exact observations

- The single-cube nonzero assignments through label two are the uniform
  shells, with values `1`, `1/16`, and `1/81`.
- The double-cube corner `n_A,n_B <= 1`, `k <= 2` has five surviving
  assignments and no negative coefficient.  The parity-forbidden
  `(1,1,1)` sector vanishes.
- The unanchored slab values
  `Z(1;0,0,0,0)=1/16384`,
  `Z(1;2,2,2,2)=7/442368`, and
  `Z(2;2,2,2,2)=1/28697814` are positive, while
  `Z(1;1,1,1,1)=0`.
- Before the analytic identity was derived, exact wheel sweeps through
  labels two and three found respectively 187 and 1,213 nonzero
  amplitudes and no negatives.  At label three the minimum is `1/576`,
  attained eight times.  These are now regression evidence for the
  all-label formula rather than the basis of the positivity claim.
- For rim `(1,1,1,1)`, the physically summed channel is

      1/4 + (9/2)s^16 + 6s^24 + (21/4)s^32,

  and its page-spin decomposition is termwise positive.

The last four-monomial polynomial compresses an exact twelve-sector
ledger.  Grouping page tuples by heat-kernel exponent gives:

| exponent | page-spin sectors | contribution per sector | total |
|---:|---|---:|---:|
| 0 | `(0,0,0,0)` | `1/4` | `1/4` |
| 16 | six permutations of `(0,0,2,2)` | `3/4` | `9/2` |
| 24 | four permutations of `(0,2,2,2)` | `3/2` | `6` |
| 32 | `(2,2,2,2)` | `21/4` | `21/4` |

Thus a certificate phrased only in terms of the four powers forgets the
individual page sectors and their permutation-orbit provenance.  It does
not forget a cancellation in this example: all twelve resolved
contributions are strictly positive.

As an exploratory check, the complete structured slab grid with exterior
and wall labels at most two was also evaluated: 25 assignments survive,
none is negative, and the smallest positive value is `1/57395628`.
That 243-assignment run took about 16.6 seconds on the development
machine.  The automated gate keeps the lighter
`exterior <= 1, walls <= 2` grid (13 survivors, no negatives); the larger
grid remains a reproducible exploratory command rather than a global-suite
cost.

The exact squared-norm identity closes P2 for all labels.  It does not
apply to the slab: the slab has a closed, unanchored intertwiner circuit
and no page trace that separates its two rim-index contractions into
complex-conjugate factors.  Slab positivity therefore remains a finite
falsification finding.

## Four-cube falsification of entrywise fixed-face positivity

The positive wheel theorem does not extend to all physical cubical
fixed-face amplitudes.  The complete cutoff-two survey of the four-cube
boundary found the locally admissible labelling

    (2,1,1,1,1,2,0,1,1,0,1,1,0,1,1,0,1,1,1,1,0,1,1,0)

with exact Haar amplitude `-1/196608`.  Its 16 correctly wired tetrahedral
`6j` symbols have nine negative signs and no zeros.  Since every edge is
trivalent, there is no higher-dimensional intertwiner fiber left to sum.
Thus universal resolved fixed-face nonnegativity is false.  This is not a
counterexample to (DP): a physical intersecting-surface complex also sums
the induced face-fusion channels, and the negative sector is only one entry
in that complete ledger.

The positive subclass is nevertheless larger than the original probes.
All 128 binary surfaces obey the two-dimensional formula
`Z=2^(chi-F)`; the three 16-face, Euler-zero sectors are the coordinate
Clifford tori and have value `2^-16`.

There are two different pair statements.  The highest-channel projection,
which replaces each coincident fundamental pair by one spin-one face, is
positive for all 7,997 intersecting pairs by an even-sign parity proof.
The genuine pair instead retains duplicate fundamental characters and sums
the full `Inv((1/2)^(tensor 4))` crossing space.  Its 100 symmetry-orbit
values are also all strictly positive, with minimum `1/16384`.  Six orbits
contain negative resolved fixed-face terms; for masks `0x4ab33` and
`0x6bc6ad`, four terms equal the negative witness `-1/196608`, while the
complete pair is `31/331776`.  Thus the counterexample refutes universal
fixed-face positivity but not the complete binary-pair conjecture.  The
exact distinction and surviving cone are documented in
`notes/hypercube4d-dual-positivity-conjecture.md`.

The six signed four-cube ledgers now have a structural explanation.  Their
overlap graphs are `K_(2,2)`, `K_(2,4)`, or `K_(4,4)`, with local weight
`W=[[1,1],[1,-1/3]]`; the complete sum is the manifestly positive binomial
expression

    sum_r binom(m,r) * (1 + (-1/3)^r)^n.

The complete exact `128 x 128` binary-surface Gram is also entrywise positive
and strictly row-diagonally dominant, hence has an explicit
nonnegative-coordinate rank-one factorization.  These are finite theorems on
one four-cube, not cutoff-independent RG estimates.

A first higher-valent follow-up uses the minimal `[0,1] x [0,2]^3` brick.
Its distinguished interior link is incident to six plaquettes.  A complete
65-orbit census of the 66-surface two-cube-composite family is positive,
including ten orbits that activate all six incident plaquettes.  The full
44-dimensional binary-surface kernel of that brick has not been surveyed.
The exact `66 x 66` Gram is strictly diagonally dominant, with uniform
residual floor `50587/104976`, and hence has the same explicit
nonnegative-coordinate factorization as the four-cube Gram.  This uniform
ceiling argument first fails at 127 observables, so it does not scale by
itself to the 4,096-surface closure of the 12 elementary generators.

## Honest boundary

These computations do **not** establish positivity for arbitrary
three- or four-dimensional complexes.  In particular:

- the cube, double-cube, and slab sweeps are finite evidence, not
  all-spin theorems; P2 wheel positivity is the exception proved above;
- the unrestricted 2x2x2 core and full four-dimensional slab kernels remain
  untested wall candidates; only the restricted 66-surface six-valent brick
  family has now been evaluated;
- dual-coefficient positivity is not reflection positivity;
- positivity supplies no contraction constant `q < 1`;
- the symbolic channel calculation uses heat-kernel coefficients, not
  the Wilson-action coefficients;
- an independent recoupling/projector derivation of a nontrivial slab
  value remains desirable.

The implication is therefore narrow but important: the squared-norm wheel,
the binary surfaces, the complete four-strand pair census, and the enumerated
slab witnesses remain valid positive channels, but they cannot justify a
universal-sign block kernel.  CD-2 must assemble the complete reflected
quadratic as a Gram while retaining negative fixed-face sectors in an
explicit signed channel or overlap ledger.
