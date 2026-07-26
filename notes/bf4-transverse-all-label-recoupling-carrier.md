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

This is an abstract orthonormal fusion-basis carrier, not itself the physical
operator.  In this coordinate presentation it does not currently contain:

1. numerical magnetic-index Clebsch--Gordan coefficients in one fixed global
   convention;
2. global \(F/R\) recoupling transport between the internal and corridor
   boundary trees;
3. coherent Haar amplitudes on those open indices above cutoff one;
4. a carrier-norm cutoff modulus connecting the fixed-coupling uniform
   function tail to the source-indexed operator;
5. an entrywise physical all-label Choi/Kraus contraction through that
   recoupling basis.

Subsequent work supplies the local magnetic tensors and a residual
full-measure Gram operator.  More importantly, direct all-label measure
regrouping now bypasses the missing entrywise \(F/R\) expansion and proves
the basis-free fixed-coupling comparison
\[
 J_{\rm phys}(s,u)\succeq
 \left(\frac{\ell_s}{H_s}\right)^{21}J_{\rm corr}(s,u).
\]
See `notes/bf4-physical-all-label-choi-domination.md`.  The coordinate-level
recoupling contraction above remains open, but it is no longer required for
that fixed-coupling theorem.

The exact cutoff-one CP pilot still rules out treating the binary
truncation as a separately positive seed and repairing it label by label.
The live obstruction is instead the collapse of the certified coefficient
toward weak coupling, together with the missing mass-preserving
consecutive-scale RG composition.
