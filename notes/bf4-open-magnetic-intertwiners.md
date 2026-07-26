# BF4 open magnetic-index intertwiners

## Result

The finite-cutoff transverse recoupling carrier now has explicit local
magnetic-index tensors.  All labels are doubled spins.  The implementation
uses the terminating Condon--Shortley factorial formula and stores every
coefficient as

\[
q\sqrt{r},\qquad q\in\mathbb Q,
\]

with exact rational square and explicit sign.  It is therefore independent
of floating-point or symbolic simplification.  The squarefree normalizer uses
total finite integer factorization rather than the bounded small-spin prime
table of the older \(6j\) pilot, so the formula is an arbitrary finite-label
algorithm rather than a cutoff-three special case.

At each of the five unprotected trivalent links, every admissible label
triple has its unique normalized invariant tensor.  At each of the nine
protected bivalent links, every untruncated Clebsch--Gordan output has its
complete open-output tensor.  Incoming legs are transported through the
standard self-duality map

\[
  |j,m\rangle^*\longmapsto (-1)^{j-m}|j,-m\rangle .
\]

This retains the oriented leg data already pinned by the recoupling carrier.

## Exact checks

The arbitrary-label formula was compared coefficient-by-coefficient with
SymPy's independent Wigner implementation for all input labels through
doubled label four.  Exact signs and squares agree.

The Clebsch--Gordan change of basis was then checked without SymPy:

| face cutoff | coupled/product vectors | Gram entries | completeness entries |
|---:|---:|---:|---:|
| 1 | 9 | 25 | 25 |
| 2 | 36 | 196 | 196 |
| 3 | 100 | 900 | 900 |

Every exact residual is zero.  The local transverse packets contain,
respectively,

| face cutoff | internal tensors | protected-boundary tensors |
|---:|---:|---:|
| 1 | 20 | 45 |
| 2 | 55 | 126 |
| 3 | 115 | 270 |

Each internal tensor has norm one.  Every magnetic column of every boundary
tensor is orthonormal, including after the orientation-dependent self-dual
transport.  The corresponding nonzero sparse component counts are
\((35,99)\), \((170,495)\), and \((560,1701)\).

The invariant designation is also checked directly rather than inferred
from nomenclature.  For cutoffs one, two, and three, the exact total
\(J_z,J_+,J_-\) actions vanish componentwise on all 4, 11, and 23 admissible
canonical trivalent tensors, covering 13, 103, and 439 magnetic components.

## Scope

This closes the missing *local magnetic-index data*, not the BF4 operator
comparison.  The tensors have not yet been contracted across the complete
transverse graph.  In particular, the following remain open:

1. all-label global signed \(F/R\) transport between the local fusion bases
   (the complete cutoff-one transport is now pinned separately);
2. coherent all-label Haar amplitudes on the global boundary carrier;
3. transport of the residual heat-tail modulus into that carrier norm;
4. CP-order domination of the physical grouped map by the corridor packet.

The executable sources are
`computations/su2_magnetic_intertwiners.py` and
`tests/test_su2_magnetic_intertwiners.py`.

The cutoff-one global convention and shared protected-link interfaces are
constructed in `computations/transverse_open_index_network.py`; see
`notes/bf4-transverse-open-index-network.md`.
