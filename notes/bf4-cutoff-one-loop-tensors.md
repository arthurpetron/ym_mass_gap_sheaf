# BF4 cutoff-one coherent loop tensors

## 1. Scope

This note records the exact coherent contraction of the connected transverse
core left by the BF4 corridor leaf reduction.  The core has:

- 15 transverse faces;
- five unprotected trivalent Haar links;
- nine corridor-protected bivalent boundary links.

The calculation is complete at representation cutoff one: every selected
face carries either the vacuum or the fundamental \(SU(2)\) character
\(\chi_1\).  It is not an all-label calculation and does not prove a
complete-positive domination of the interacting corrected-slab map.

## 2. Compact contraction

An internally admissible binary face assignment activates either zero or two
fundamental strands at each of the five internal links.  The incidence
constraints admit a simultaneous whole-face orientation choice for every one
of the 1024 assignments.  Since \(\chi_1(g)=\chi_1(g^{-1})\), these face flips
do not change the integrand, and the two active occurrences of each remaining
Haar variable can be made oppositely oriented.

For occurrences in two trace loops the contraction uses Schur orthogonality:
\[
 \int_{SU(2)}\chi_1(UA)\chi_1(U^{-1}B)\,dU
 = \frac12\chi_1(AB).
\]
If both occurrences lie in the same trace, the same matrix-coefficient
identity splits that trace into two.  Free reduction after every gluing
removes adjacent \(UU^{-1}\) pairs and replaces an empty fundamental trace by
\(\operatorname{Tr}(I)=2\).  Thus each assignment becomes exactly
\[
 c_\alpha\prod_j\chi_1(W_{\alpha,j}),
 \qquad c_\alpha\in\mathbb Q_{>0},
\]
where every \(W_{\alpha,j}\) is a cyclic word using only the nine protected
boundary links.

This loop-word representation avoids the coordinate-polynomial blow-up of a
simultaneous fifteen-factor expansion while preserving the coherent boundary
observable.  A prior gluing can free-reduce a later internal pair completely,
so the number of effective Haar integrations can be smaller than the number
of initially active internal pairs.

## 3. Exact census

All 1024 admissible assignments produce distinct canonical compact records
after free reduction, trace cyclicity and inversion, and factor permutation.
This does not assert functional independence modulo every \(SU(2)\) trace
identity.  Their face count census is

| active faces | number of tensors |
|---:|---:|
| 0 | 1 |
| 1 | 6 |
| 2 | 15 |
| 3 | 22 |
| 4 | 30 |
| 5 | 60 |
| 6 | 126 |
| 7 | 204 |
| 8 | 237 |
| 9 | 190 |
| 10 | 99 |
| 11 | 30 |
| 12 | 4 |

The coefficient census is

| coefficient \(c_\alpha\) | number of tensors |
|---:|---:|
| \(1/32\) | 192 |
| \(1/16\) | 448 |
| \(1/8\) | 192 |
| \(1/4\) | 128 |
| \(1\) | 64 |

The effective-integration census is
\[
 (0,64),\ (2,128),\ (3,192),\ (4,448),\ (5,192).
\]
The number of surviving boundary trace loops has the binomial row
\[
 (0,1),(1,20),(2,100),(3,236),(4,310),
 (5,236),(6,100),(7,20),(8,1).
\]
No boundary trace word has length greater than seven.

## 4. Independent exact checks

Five distinguished masks
\[
 0,\quad \mathtt{0x800},\quad \mathtt{0x1088},\quad
 \mathtt{0x7e00},\quad \mathtt{0x6cff}
\]
were also expanded and integrated directly in exact quaternion coordinates.
The compact loop tensors agree as functions on \(SU(2)^9\).  The last mask is
a maximal twelve-face filling with coefficient \(1/32\), seven boundary
loops, and maximum word length seven; its direct polynomial has 183976
monomials.  These checks are independent evaluations of representative
cases, while the complete 1024-entry census uses the exact trace-gluing
algorithm.

The executable source is
`computations/transverse_cutoff_one_loop_tensor.py`, with regression gates in
`tests/test_transverse_cutoff_one_loop_tensor.py`.

## 5. Remaining theorem

Positivity of the scalar coefficients in this fundamental trace basis is not
the required CP-order domination.  Wilson traces are not themselves positive
functions.  The six decorations, nested arbitrary-cutoff local fusion bases,
and a fixed-coupling all-label function tail have since been constructed.
The exact cutoff-one Schur pilot nevertheless becomes indefinite at
\(z=2s^3=3/2\), so the binary family cannot be used as a separately positive
weak-coupling seed.

The next BF4 obligation is therefore:

1. evaluate the open magnetic-index Haar amplitudes and global \(F/R\)
   transport on the nested fusion carrier;
2. lift the fixed-coupling function tail to that source-indexed operator;
3. reconstruct the all-label physical Choi/Kraus map;
4. compare it with the nine-corridor packet and extract a domination
   coefficient bounded below uniformly in spacing and ambient volume.

Until those steps are proved, the corrected slab has no certified physical
refresh packet, and no mass-gap consequence follows from this calculation.
