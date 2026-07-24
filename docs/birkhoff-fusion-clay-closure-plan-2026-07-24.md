# Birkhoff–fusion route to Clay closure

Date: 2026-07-24

## Terminal theorem

The program is complete only when it constructs, for every compact simple
gauge group \(G\), one nontrivial quantum Yang–Mills theory on
\(\mathbb R^4\), verifies axioms at least as strong as
Osterwalder–Schrader/Wightman for that same theory, and proves that its
Hamiltonian has no spectrum in \((0,\Delta_G)\) for explicit
\(\Delta_G>0\).

A lattice contraction, a continuum correlation rate, or an abstract
Hamiltonian model is not by itself the terminal theorem.

## Critical path

| Gate | Deliverable | Exit certificate | Hard failure signal |
|---|---|---|---|
| BF1. Physical carrier | Finite fusion-closed basis on corrected slabs | Direct Haar integral equals complete fusion ledger; actual heat activity is nonnegative | A negative complete-family heat polynomial, or failure of exact resummation |
| BF2. Dual positivity | General theorem (DP), or a precisely enlarged positive carrier | Nonnegative activity for every physical generator at every cutoff and coupling | Exact counterexample surviving the complete physical sum |
| BF3. Physical block map | Exact fine-to-coarse pushforward on the BF2 carrier | Mass preservation, reflection compatibility, and an explicit remainder identity | Coarse data leave the carrier or require signed cancellation not represented by it |
| BF4. Projective geometry | Birkhoff–Hopf estimate over a fixed physical block | Exact/projective diameter bound whose grouped rate is \(<1\), uniform in volume and cutoff | Infinite diameter or grouped rates with no positive physical decay exponent |
| BF5. Graded stability | Perturbative comparison for branched/intersection sectors | Explicit \(C\kappa^{64}\) bound and summable grouped distortion | Graded contribution is unsummable or changes the cone order |
| BF6. RG-I7–I9 | Contraction, landing, and summable distortion on the actual Yang–Mills trajectory | One witness-bearing RG certificate with volume/cutoff moduli | Any certificate applies only to a surrogate law or a fixed cutoff |
| BF7. Continuum theory | Infinite-volume and \(a\to0\) Schwinger functional/measure | Located convergence moduli, non-Gaussianity, locality, AF short-distance normalization | Limit is trivial, Gaussian, nonunique, or detached from the RG trajectory |
| BF8. OS reconstruction and gap | OS axioms and reconstruction on the BF7 object | Physical Hilbert space, vacuum, Hamiltonian, and \(\operatorname{spec}H\cap(0,\Delta)=\varnothing\) | Correlation decay cannot be identified with the reconstructed Hamiltonian |
| BF9. All compact simple groups | Uniform group-theoretic lift | Concrete per-group representation/heat-kernel data plus a proved worst-case reduction | An uninhabited representation-data interface remains |
| BF10. Clay assembly | Shared-object final theorem | `ClayTargetPinned`-strength inhabitant and independent assumption audit | Any clause refers to a different or surrogate object |

## BF1: current tranche

The carrier candidate is a multiset of closed labelled surface strands.
Overlap faces retain all irreducible channels and all fusion-path
multiplicities. The implementation must satisfy four checks:

1. every strand has zero mod-two edge boundary;
2. union stays in the carrier;
3. direct unfused Haar integration equals the complete channel ledger;
4. the label-dependent heat-weighted activity is tested exactly for sign.

Current exact certificate:

- corrected slab: extent one, 72 faces, 116 edges;
- complete family: two intersecting closed fundamental surfaces;
- fusion ledger: 16 channels, including four negative fixed channels;
- direct and resummed amplitude: \(31/331776\);
- physical heat activity:
  \(w^{48}(1+12w^8+6w^{16}+12w^{24}+w^{32})>0\).

BF1 is not closed by one example. The next BF1 work units are:

1. enumerate surface-family orbits at bounded strand count and cutoff;
2. compute exact heat polynomials and search for negative families;
3. add embedded fusion-tree/intertwiner data if surface masks alone
   overcount or fail closure;
4. state the minimal general positivity lemma surviving that falsification
   campaign.

## BF2–BF4: contraction engine

The Birkhoff map will not be the raw one-face fusion matrix: its support has
zero holes and infinite Hilbert diameter. The candidate is the reflected
physical block kernel on BF2-positive generators.

For lattice spacing \(a_n\), the target is scale-dependent:

\[
q_n=1-m a_n+o(a_n),
\qquad
\quad
\prod_{n\in I(L)}\left(q_n+C\kappa_n^{64}\right)
\le e^{-m_*L}<1
\]

for every group of steps spanning a fixed physical distance \(L\). Required
certificate data are the positive cone, an interior comparison point, lower
and upper cross-ratio bounds, the physical block length, and the graded
distortion budget.

## BF5–BF6: physical RG closure

The exact pushforward identity must split into:

- the unbranched positive carrier map;
- a \(\kappa\)-graded branched sector;
- an actual remainder measured in the same projective norm;
- scale-dependent contraction and summable distortion;
- landing in the domain where the estimates reproduce under iteration.

This package is RG-I7, RG-I8, and RG-I9 only when its measure is the exact
Haar-network Gibbs law, not the multiplicity-product surrogate.

## BF7–BF10: from RG to the Clay theorem

The RG certificate must construct located infinite-volume and continuum
Schwinger limits on a gauge-invariant local observable algebra. The same
object must carry reflection positivity, Euclidean covariance, symmetry,
regularity, clustering, locality, nontriviality, and asymptotic-freedom
normalization.

OS/GNS reconstruction must then identify the physical time translations and
show that the grouped correlation exponent supplies a spectral exclusion
\((0,\Delta_G)\) for the reconstructed Hamiltonian. Finally, every
representation-theoretic input must be constructed for each compact simple
group, and all fields must assemble on the one shared stack required by
`ClayTargetPinned`.

## Evidence and commit policy

Every completed gate requires:

- an exact computation or proof artifact;
- regression tests;
- a prose statement distinguishing proved results from open inputs;
- constructive Lean certificates for witness-bearing reductions where
  applicable;
- an assumption/axiom audit;
- a focused commit that does not absorb unrelated worktree changes.
