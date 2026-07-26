# BF4 cutoff-one open-index transverse network

## 1. What is now constructed

The connected 15-face transverse component is now represented as an exact
magnetic-index tensor network at face-label cutoff \(N=1\).  It is not
flattened into its 10673 boundary-channel paths.

The structured carrier has:

- 15 discrete face-label variables \(j_f\in\{0,1\}\);
- 33 oriented matrix incidences arranged into 15 cyclic face wires;
- 33 magnetic corner indices, each used by exactly two local tensor ports;
- five internal trivalent Haar nodes;
- nine protected bivalent Clebsch--Gordan output nodes.

The five internal nodes each have the four admissible local label records
\[
 (0,0,0),\quad(0,1,1),\quad(1,0,1),\quad(1,1,0).
\]
For each record the invariant space is one-dimensional.  The Haar projector
is stored in Kraus form as the outer product of a normalized oriented
three-\(j\) ket with its bra.

Each protected residual pair has the complete five-record CG carrier
\[
 (0,0;0),\quad(0,1;1),\quad(1,0;1),\quad
 (1,1;0),\quad(1,1;2).
\]
Both output magnetic indices are left open.  The exact CG tables are
isometries, so these nodes are ready to be used as Choi/Kraus interfaces.
The finite factor graph recovers the known 1024 internally admissible face
assignments and 10673 complete boundary-channel paths without materializing
the global path table.

## 2. Orientation and duality

For a positive occurrence \(D^j(U)_{ab}\), the ket port uses \(a\) and the
bra port uses \(b\).  For a negative occurrence
\[
 D^j(U^{-1})_{ab}=\overline{D^j(U)_{ba}},
\]
the ket/bra ports are exchanged and the conjugate representation is
identified with \(V_j\) using
\[
 J|j,m\rangle^*
   =(-1)^{j-m}|j,-m\rangle.
\]
All 33 raw orientation signs remain attached to their incidences; they are
not erased by a whole-face parity reduction.

The fundamental representation is pseudoreal:
\[
 J^2=-I.
\]
This Frobenius--Schur sign is the principal duality warning.  A negative leg
cannot be turned around twice as though the pivotal map were literally the
identity.  The present module pins one Condon--Shortley/pivotal convention
locally.  The selected-corridor source tensors must use the same convention
before their contraction can be identified with the physical Choi operator.

The internal orientation signatures are
\[
\begin{gathered}
(-,-,-),\ (-,-,+),\ (+,-,-),\ (+,-,+),\ (+,+,-),
\end{gathered}
\]
once each.  The nine residual boundary-pair signatures have census
\[
 (--):3,\qquad(-+):4,\qquad(++):2.
\]

## 3. Shared protected-link channels

At each of the nine core protected links, two residual faces and two selected
corridor faces meet.  Fuse the residual pair to \(k\), fuse the selected pair
to the same \(k\), and close the two outputs with the normalized cap.  The
local projector weight is
\[
 \frac1{\dim(k)}=\frac1{k+1}.
\]

For labels in \(\{0,1\}\), eight of the sixteen four-leg assignments are
admissible in this pair basis.  They carry nine shared-channel records:

- four records with \(k=0\);
- four records with \(k=1\);
- one additional all-fundamental record with \(k=2\).

Across all nine interfaces this gives 36, 36 and 9 local shared-channel
records respectively.  This is a local carrier count, not a flattening of
the global paths.

The all-fundamental assignment is two-dimensional, with grouped channel
order \((0,2)\).  Transport from the grouping
\[
 (\text{residual pair})(\text{selected pair})
\]
to increasing face-id order is therefore a genuine signed Racah operation.
The nine-interface census is:

\[
 5\times
 \begin{pmatrix}
  \frac12&\frac{\sqrt3}{2}\\
  \frac{\sqrt3}{2}&-\frac12
 \end{pmatrix},
\qquad
 3\times
 \begin{pmatrix}
  -\frac12&-\frac{\sqrt3}{2}\\
  \frac{\sqrt3}{2}&-\frac12
 \end{pmatrix},
\qquad
 1\times I_2.
\]

All blocks were obtained as exact overlaps of normalized magnetic tensors,
and every block is orthogonal.  This is the required local \(F/R\) transport:
the two-channel packet cannot be replaced by a positive scalar or by parity
alone.

## 4. Decoration interfaces

The complete 21-face residual also has nine protected links belonging to the
six one-face decorations.  Each such link contains:

- two selected-corridor legs;
- one residual decoration leg.

The local invariant exists exactly when the selected pair fuses to the
residual label:
\[
 r\in a\otimes b.
\]
At cutoff one the four records are
\[
 (0,0;0),\quad(0,1;1),\quad(1,0;1),\quad(1,1;0).
\]
Their normalized projector weights are \(1/(r+1)\).  Transport from the
selected-pair-first order to increasing face-id order is an exact sign
\(\pm1\), computed from the ordered three-\(j\) tensors.  Thus all eighteen
protected residual interfaces now have an explicit shared-channel gluing
rule.

## 5. Independent checks

The executable coefficient tables were checked against SymPy's independent
exact implementations of the Condon--Shortley Clebsch--Gordan and Wigner
three-\(j\) coefficients.  Further gates verify:

- normalization of every oriented internal invariant;
- completeness of every oriented boundary CG transform;
- orthonormality of every pair-pair shared-channel basis;
- orthogonality of all protected-link Racah blocks;
- the fundamental identity \(J^2=-I\);
- exact corner-port degree two throughout the 15 face cycles.

The implementation is
`computations/transverse_open_index_network.py`, with regression tests in
`tests/test_transverse_open_index_network.py`.

## 6. Fail-closed boundary

This milestone supplies exact local magnetic tensors, orientation transport,
and a non-flattened contraction graph.  It does not yet contract the
selected-corridor source indices with the residual network into one physical
Choi matrix.  In particular, it does not prove CP-order domination.

The next obligation is:

> Contract the selected and residual open indices in the same pivotal
> convention, retaining the signed \(F/R\) blocks and the \(J^2=-1\) duality
> sign, and identify the resulting source-indexed tensor with the physical
> grouped corrected-slab Choi operator.

An entrywise recoupling proof would require that identification before
seeking a positive corridor subtraction and a uniform CP-order lower bound.

The fixed-coupling order theorem has since been obtained by a different,
basis-free route: group the full positive leaf-reduced measure first, define
the nine-slot source/target Choi Gram directly, and apply pointwise residual
measure order.  This does not materialize the entrywise all-label
contraction described above, but it proves the same fixed-coupling Choi
inequality invariantly under recoupling.  See
`notes/bf4-physical-all-label-choi-domination.md`.  Its coefficient is not
spacing-uniform.
