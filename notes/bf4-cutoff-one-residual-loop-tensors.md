# BF4 complete cutoff-one residual loop tensors

## 1. Scope

This note extends the coherent contraction of the connected 15-face
transverse component to the complete 21-face residual left by normalized-Haar
leaf elimination.  The additional six faces are isolated one-face
decorations.

The result is exact at representation cutoff one.  It does not prove an
all-label completion, complete-positive order domination, a physical
transfer identification, or a mass gap.

## 2. Exact decoration factorization

After maximal-tree gauge fixing, the six decoration faces
\[
 31,\ 32,\ 47,\ 50,\ 56,\ 58
\]
have the free-link words
\[
\begin{aligned}
 &(27,31^{-1}),\quad (32^{-1}),\quad
 (55,59^{-1}),\\
 &(61^{-1}),\quad (67,71^{-1}),\quad (72^{-1}).
\end{aligned}
\]
Thus three words have length one and three have length two.  Their nine link
sets are pairwise disjoint, every link is protected by a selected heat
corridor, and they are disjoint from the nine protected links of the
connected component.

No decoration therefore introduces another unprotected Haar integral.  If
\(T_\alpha\) is one of the 1024 coherent core tensors and
\(D\subseteq\{1,\ldots,6\}\), the full residual tensor is exactly
\[
 T_{\alpha,D}
 =
 T_\alpha\prod_{d\in D}\chi_1(W_d).
\]
The rational coefficient and the number of internal Haar integrations are
unchanged.  Every active decoration simply appends one independent boundary
trace.

## 3. Complete record census

There are \(2^6=64\) decoration profiles, hence
\[
 1024\cdot64=65536
\]
admissible residual assignments.  All 65536 produce distinct canonical
compact records \((c_{\alpha,D},\{W_{\alpha,D,j}\})\).  Distinctness is
checked after free reduction, trace cyclicity and inversion, and permutation
of trace factors.

These 65536 records are not the previously computed 683072 boundary fusion
paths.  A single trace-word record can expand into several singlet/triplet
outputs when products meeting a protected link are recoupled.  The present
calculation retains the coherent trace product before that output-channel
expansion.

The active-face census is
\[
\begin{array}{c|rrrrrrrrrr}
\text{faces}&0&1&2&3&4&5&6&7&8&9\\
\hline
\text{records}&1&12&66&222&522&966&1638&2886&5148&8294
\end{array}
\]
\[
\begin{array}{c|rrrrrrrrr}
\text{faces}&10&11&12&13&14&15&16&17&18\\
\hline
\text{records}&11154&12090&10374&6930&3522&1314&339&54&4.
\end{array}
\]
No admissible assignment activates more than 18 of the 21 residual faces,
because the 15-face component admits at most 12 active faces.

The coefficient census is

| coefficient | records |
|---:|---:|
| \(1/32\) | 12288 |
| \(1/16\) | 28672 |
| \(1/8\) | 12288 |
| \(1/4\) | 8192 |
| \(1\) | 4096 |

The effective-integration census is
\[
 (0,4096),\ (2,8192),\ (3,12288),\
 (4,28672),\ (5,12288).
\]
Both tables are the exact 64-fold lift of the connected-core tables.

The boundary-loop census is
\[
\begin{aligned}
 &(0,1),(1,26),(2,235),(3,1156),(4,3641),\\
 &(5,7942),(6,12507),(7,14520),(8,12507),\\
 &(9,7942),(10,3641),(11,1156),(12,235),(13,26),(14,1).
\end{aligned}
\]
It is the convolution of the core loop census with the six-decoration
binomial row.  A record contains at most 14 trace factors, no individual
trace word has length greater than seven, and the sum of all word lengths in
one record is at most 27.

The total-word-length census is
\[
\begin{aligned}
 &(0,1),(1,6),(2,22),(3,65),(4,162),(5,356),(6,708),\\
 &(7,1282),(8,2127),(9,3242),(10,4538),(11,5839),\\
 &(12,6908),(13,7512),(14,7512),(15,6908),(16,5839),\\
 &(17,4538),(18,3242),(19,2127),(20,1282),(21,708),\\
 &(22,356),(23,162),(24,65),(25,22),(26,6),(27,1).
\end{aligned}
\]

## 4. Independent exact checks

The compact construction was compared with direct quaternion-coordinate Haar
integration for the representative pairs
\[
 (0,0),\quad (0,\mathtt{0x3f}),\quad
 (\mathtt{0x800},\mathtt{0x15}),\quad
 (\mathtt{0x1088},\mathtt{0x3f}).
\]
These cover the vacuum, all decorations without the core, a mixed core and
decoration filling, and a nontrivial core with all decorations.  The
polynomials agree exactly as functions on the boundary copies of \(SU(2)\).

The maximally long compact record uses core mask \(\mathtt{0x1eff}\) and all
six decorations.  It has 18 active faces, 14 boundary traces, and 27 boundary
letters, while its longest individual word has length six.

The executable audit is
`computations/transverse_cutoff_one_residual_tensor.py`; its regression gates
are in `tests/test_transverse_cutoff_one_residual_tensor.py`.

## 5. Remaining theorem

The six decorations are now fully incorporated into the coherent cutoff-one
residual.  What remains is not further binary-face bookkeeping.  A nested
arbitrary-cutoff local recoupling carrier and a fixed-coupling uniform
all-label residual tail have since been constructed.  Direct all-label
measure regrouping now defines the basis-free physical Choi/Kraus Gram and
proves fixed-coupling corridor domination with coefficient
\((\ell_s/H_s)^{21}\).

The normalized difference now has a random-unitary CPTP residual-channel
promotion and abstract same-carrier convolution law.  The load-bearing step
is to identify that law with actual boundary-dependent corrected-slab
gluing and to replace the collapsing fixed-slab coefficient by a
spacing-uniform relative residual-order estimate applied directly to the
glued physical-distance block.

Positive rational coefficients multiplying Wilson traces do not establish
that order statement, because Wilson traces themselves need not be positive.
The next certificate must therefore be formulated in a positive
matrix-coefficient, Gram, or Choi carrier rather than inferred from the
compact trace-word census.
