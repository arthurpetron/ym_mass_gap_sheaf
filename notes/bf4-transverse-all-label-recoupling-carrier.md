# BF4 transverse all-label recoupling carrier

## Result

The connected 15-face transverse core now has an explicit nested
finite-cutoff recoupling carrier.  At face-label cutoff \(N\), it retains:

- the ordered oriented legs at all five internal trivalent Haar links;
- every one-dimensional admissible \(SU(2)\) invariant channel there;
- the ordered legs at all nine corridor-protected bivalent links;
- every Clebsch--Gordan output, without truncating the boundary at \(N\).

Two face labels at most \(N\) can fuse through output label \(2N\).  Keeping
those outputs is essential: truncating them back to \(N\), or retaining only
parity, would destroy the physical carrier.

The implementation records the canonical local basis data rather than
materializing the enormous global boundary-profile table.  Successive
cutoffs embed literally by inclusion of representations and local channels.

## Exact factor-graph census

The five internal invariant constraints and nine boundary path
multiplicities form a small integer factor graph on the 15 face labels.
Deterministic variable elimination contracts this graph exactly.  It counts
internally admissible face assignments and the same assignments weighted by
all boundary fusion-output choices:

| cutoff \(N\) | internal channels per trivalent link | boundary channels per protected link | assignments | boundary-channel paths |
|---:|---:|---:|---:|---:|
| 0 | 1 | 1 | 1 | 1 |
| 1 | 4 | 5 | 1024 | 10673 |
| 2 | 11 | 14 | 184437 | 29647857 |
| 3 | 23 | 30 | 8114176 | 8982556738 |
| 4 | 42 | 55 | 179406250 | 1075792843993 |
| 5 | 69 | 91 | 2279938752 | 54549556261540 |

The \(N=1\) row exactly reproduces the independently constructed binary
fusion ledger.  The rapid growth explains why flat profile enumeration is
not a viable all-label representation; the factor graph and its nested local
bases are the reusable carrier.

The executable constructor is
`computations/transverse_all_label_recoupling.py`, with tests in
`tests/test_transverse_all_label_recoupling.py`.

## What remains open

This is an abstract orthonormal fusion-basis carrier, not yet the physical
operator.  It does not currently contain:

1. numerical magnetic-index Clebsch--Gordan coefficients in one fixed global
   convention;
2. global \(F/R\) recoupling transport between the internal and corridor
   boundary trees;
3. coherent Haar amplitudes on those open indices above cutoff one;
4. a carrier-norm cutoff modulus connecting the fixed-coupling uniform
   function tail to the source-indexed operator;
5. the physical all-label Choi/Kraus map or its CP-order comparison.

The next constructor must supply these amplitudes and transport before
seeking a positive domination coefficient.  The exact cutoff-one CP pilot
shows why this order is mandatory: the binary truncation is already
indefinite at a legitimate weak-coupling activity, so it cannot be inserted
as a separately positive seed and repaired afterward.
