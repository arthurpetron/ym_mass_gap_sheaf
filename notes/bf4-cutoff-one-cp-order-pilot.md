# BF4 cutoff-one CP-order pilot and exact truncation obstruction

## 1. The finite operator question

The 1024 compact loop tensors determine a scalar transverse-core function
of the nine corridor-protected Haar variables.  They do not retain the open
magnetic and intertwiner indices needed to reconstruct the physical
corrected-slab Choi operator.  A finite question that uses exactly the
available data, without pretending those indices have already been built,
is nevertheless possible.

Write
\[
 z=2s^3
\]
for the coefficient of the fundamental character in the cutoff-one
plaquette factor, and let \(f_z\) be the transverse-core density after the
five internal Haar variables are integrated.  On product Haar space use the
orthonormal feature packet
\[
 \phi_0=1,\qquad
 \phi_i=\chi_1(U_i),\quad 1\le i\le9,
\]
where \(U_i\) are the nine protected boundary variables.  Define
\[
 G_{ij}(z)
 =
 \int f_z(U)\phi_i(U)\phi_j(U)\,dU.
\]

The matrix is exact and finite.  Associate to it the Schur multiplier
\[
 {\cal S}_{G(z)}(A)=G(z)\mathbin{\circ}A
\]
on \(M_{10}\).  Its Choi matrix is zero off the span of
\(\{|i\rangle\otimes|i\rangle\}\), and its restriction to that span is
exactly \(G(z)\).  Consequently
\[
 {\cal S}_{G(z)}-\eta{\cal S}_I
 \text{ is completely positive}
 \quad\Longleftrightarrow\quad
 G(z)-\eta I_{10}\succeq0.
\]
This is the precise bounded cutoff-one CP-order pilot.

It is not the physical corrected-slab CP map.  It is a finite Schur/Gram
compression determined by the scalar loop tensors.  Positivity of this
compression is necessary for the corresponding scalar multiplication
domination, but it is not sufficient to reconstruct or dominate the
all-label open-index physical map.

## 2. Exact moment matrix

Protected-link parity reduces the apparent calculation sharply.  Of the
100 matrix entries, only 28 are nonzero, and they take seven distinct
polynomial values.  The activity exponents are
\[
 0,1,2,4,5,6,7,8,9,10,11,12.
\]
Every coefficient is computed by exact fundamental-character Haar
contraction.

The two entries responsible for the first obstruction are
\[
\begin{aligned}
d(z)=G_{88}(z)=G_{99}(z)
 &=1+\frac14z^6+\frac5{256}z^{10}+\frac1{512}z^{12},\\
b(z)=G_{89}(z)=G_{98}(z)
 &=z^2+\frac1{16}z^4+\frac{17}{128}z^8
   +\frac1{1024}z^{10}+\frac1{256}z^{12}.
\end{aligned}
\]

## 3. A positive strong-coupling pilot

At
\[
 z=\frac12\qquad\left(s^3=\frac14\right),
\]
exact rational \(LDL^{\mathsf T}\) factorization proves
\[
 G\!\left(\frac12\right)-\frac13I_{10}\succ0.
\]
Thus the finite Schur multiplier has the literal CP-order decomposition
\[
 {\cal S}_{G(1/2)}
 =
 \frac13{\cal S}_I+\text{CP residual}.
\]
This establishes that the formulation is inhabited and that the compact
loop data can support a nonzero finite CP-order coefficient in a
strong-coupling regime.  It does not assert a pointwise lower bound for
\(f_{1/2}\), nor a physical corrected-slab refresh coefficient.

## 4. Exact weak-coupling obstruction

Take
\[
 z=\frac32,\qquad
 s=\left(\frac34\right)^{1/3}.
\]
This is strictly inside the physical heat-coordinate range \(0<s<1\), not
the endpoint \(s=1\).  The principal block on \(\phi_8,\phi_9\) is
\[
 \begin{pmatrix}
 10962521/2097152 & 3425373/524288\\
 3425373/524288 & 10962521/2097152
 \end{pmatrix}.
\]
Its determinant is
\[
 -\frac{67554016350623}{4398046511104}<0.
\]
Equivalently, for \(v=e_8-e_9\),
\[
 v^{\mathsf T}G(3/2)v
 =
 -\frac{2738971}{1048576}<0.
\]
Therefore \({\cal S}_{G(3/2)}\) is not completely positive.  Subtracting any
nonnegative corridor multiple only makes the same quadratic form smaller,
so no cutoff-one CP-order domination exists at this activity even in the
ten-feature pilot.

This obstruction has a narrow but decisive interpretation:

- the cutoff-one character truncation cannot be isolated as a positive
  Kraus/Schur component along the weak-coupling route;
- positive scalar coefficients of the individual loop-word records do not
  imply positivity after coherent boundary evaluation;
- a proof cannot obtain the physical corridor domination by monotonically
  adding the cutoff-one contribution as though it were already CP.

It is **not** an obstruction to the full heat-kernel theory.  The complete
all-label heat kernel is positive, and exact Haar blocking of the complete
open-index reflected carrier is CP.  Nor is this matrix the physical
corrected-slab Choi operator.  The negative certificate only rejects the
cutoff-one truncation/Schur compression as a positive weak-coupling
building block.

## 5. Revised next construction

The next CP-order object must therefore be all-label from the start:

1. retain open Peter--Weyl magnetic indices and every shared corridor
   intertwiner;
2. group enough representation labels before taking a positive summand;
3. construct the physical source-to-target Choi/Kraus operator rather than
   only its scalar Wilson-trace contraction;
4. compare that all-label Choi operator with the corridor Choi packet by an
   exact PSD difference and a summable heat-relative tail.

The executable certificate is
`computations/transverse_cutoff_one_cp_order.py`, with regression gates in
`tests/test_transverse_cutoff_one_cp_order.py`.
