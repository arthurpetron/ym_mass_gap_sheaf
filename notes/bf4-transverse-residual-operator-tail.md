# BF4 transverse residual operator/Choi tail

## 1. Result

The fixed-coupling uniform modulus for the 21-face transverse residual lifts
to an exact trace-norm modulus on finite heat-weighted Peter--Weyl
open-index compressions.  Independently, compressions of the full positive
residual measure converge in trace norm to its full positive Gram operator,
with explicit bounds on the retained/outside cross corners.

The construction deliberately separates two operations:

1. **Full-measure feature compression.** First construct the exact positive
   all-label residual measure, form its Gram operator, and then apply an
   orthogonal finite-carrier projection.  Every such compression is PSD; as
   a Choi matrix it defines a CP map.
2. **Character truncation.** Replace each heat kernel in the scalar density
   by a finite character sum.  This gives a computable approximation and a
   norm bound, but its density and Gram matrix are not thereby positive.

The second operation must not be substituted for the first.  The exact
cutoff-one obstruction at \(z=3/2\) in
`notes/bf4-cutoff-one-cp-order-pilot.md` shows that a finite character
truncation can already have a negative two-feature Gram minor.

This result is fixed-coupling and ambient-volume independent.  It is not
uniform as the heat coordinates tend to one, and it does not reconstruct
the physical source-to-target corrected-slab Choi operator.

## 2. Positive full-measure Gram

Let \(R_s(x)\) be the full all-label transverse residual on its 18 protected
boundary variables.  It is obtained by integrating the product of 21
positive heat kernels over the five internal normalized Haar variables, so
\[
 R_s(x)\ge0.
\]
If \(H_s\) is the rational one-plaquette character majorant from the
all-label tail certificate, then
\[
 0\le R_s(x)\le H_s^{21}.
\]

For an independent feature heat coordinate \(0<u<1\), use the complete
magnetic-index Peter--Weyl feature vector on one boundary slot,
\[
 v_u(g)_{nmk}
 =
 \sqrt{(n+1)u^{n(n+2)}}\,D^n_{mk}(g).
\]
Unitarity gives the pointwise identity
\[
 \lVert v_u(g)\rVert^2
 =
 \sum_{n\ge0}(n+1)^2u^{n(n+2)}.
\]
Tensoring over 18 protected slots gives \(V_u(x)\).  The full Gram operator
\[
 A_{s,u}
 =
 \int R_s(x)\,
   |V_u(x)\rangle\langle V_u(x)|\,dx
\]
is positive trace class.

If \(P_M\) retains every open magnetic component with label at most \(M\),
then
\[
 A^{(M)}_{s,u}=P_MA_{s,u}P_M\succeq0.
\]
Thus every established finite Choi indexing of this Gram compression is CP.
An orthogonal projection onto complete invariant/intertwiner packets
preserves positivity and cannot increase trace norm.  Signed orthonormal
recoupling is unitary congruence and preserves both positivity and norm.

This is an operator theorem about the full measure.  The repository still
lacks the physical source/target indexing and shared-intertwiner transport
which would identify this Gram with the corrected-slab block map.

## 3. Lifting the scalar density tail

Let \(R_{s,N}\) be the 21-factor character truncation and let
\[
 E_N(s)=21H_s^{20}T_N(s)
\]
be the exact boundary-uniform scalar error:
\[
 \lVert R_s-R_{s,N}\rVert_\infty\le E_N(s).
\]
For the full feature vector,
\[
\left\|
 \int (R_s-R_{s,N})|V_u\rangle\langle V_u|
\right\|_1
\le
 E_N(s)H_u^{18}.
\]
For the finite feature compression, write
\[
 B_M(u)=\sum_{n=0}^{M}(n+1)^2u^{n(n+2)}.
\]
The sharper compressed bound is
\[
\boxed{\quad
 \left\|
 P_M(A_{s,u}-A^{\rm char}_{s,N,u})P_M
 \right\|_1
 \le E_N(s)B_M(u)^{18}.
 \quad}
\]
The same quantity bounds the operator norm because
\(\lVert X\rVert_{\rm op}\le\lVert X\rVert_1\).

No positivity of \(A^{\rm char}_{s,N,u}\) is used or inferred.  The proof is
only the trace norm of a rank-one operator,
\(\lVert|v\rangle\langle v|\rVert_1=\lVert v\rVert^2\), followed by the
uniform scalar bound.

## 4. Feature-compression tail of the full positive Gram

Let \(T_M(u)\) be the one-slot feature tail and use the rational full
one-slot upper bound \(H_u=B_M+T_M\).  The squared norm outside the complete
18-slot cutoff obeys the tensor telescope
\[
 O_M(u)
 \le
 18H_u^{17}T_M(u).
\]
Writing \(Q_M=1-P_M\), the outside diagonal satisfies
\[
 \lVert Q_MA_{s,u}Q_M\rVert_1
 \le H_s^{21}O_M(u).
\]
The coherent cross corner is retained and bounded by
\[
 \lVert P_MA_{s,u}Q_M\rVert_1
 \le
 H_s^{21}\sqrt{H_u^{18}O_M(u)}.
\]
The executable certificate uses an exact rational upper enclosure of the
square root.  The opposite cross corner has the same bound.  Therefore
\[
\boxed{\quad
 \lVert A_{s,u}-P_MA_{s,u}P_M\rVert_1
 \le
 2H_s^{21}\sqrt{H_u^{18}O_M(u)}
 +H_s^{21}O_M(u).
 \quad}
\]
Unlike a diagonal-only truncation, this estimate explicitly controls
\(P_MAQ_M\), \(Q_MAP_M\), and \(Q_MAQ_M\).

Combining this with the compressed density bound gives a finite,
character-computable approximation:
\[
\begin{aligned}
\lVert A_{s,u}-P_MA^{\rm char}_{s,N,u}P_M\rVert_1
\le{}&
 E_N(s)B_M(u)^{18}\\
&+2H_s^{21}\sqrt{H_u^{18}O_M(u)}
 +H_s^{21}O_M(u).
\end{aligned}
\]
At fixed \(s,u<1\), both \(E_N(s)\) and \(O_M(u)\) vanish
super-geometrically.  This is a trace-class Cauchy name.

As an exact executable sample, \(s=u=1/2\) and \(N=M=8\) place the combined
bound below \(10^{-5}\) (the decimal guide is approximately
\(1.5845\times10^{-6}\)).

## 5. Scope and next obligation

The theorem supplies:

- a positive trace-class full residual Gram;
- CP/PSD finite compressions of that full Gram;
- an exact trace- and operator-norm lift of the scalar density modulus;
- a full feature-cutoff tail with both coherent cross corners;
- stability under complete intertwiner projection and unitary recoupling.

It does not supply:

- positivity of finite character-truncated densities;
- a spacing-uniform cutoff as \(s\) or \(u\) tends to one;
- the source-indexed physical corrected-slab Kraus/Choi operator;
- CP-order domination of that physical operator by the corridor packet.

The next operator construction must assemble the all-label source/target
Choi indices and shared corridor intertwiners, then apply the full-measure
compression theorem—not the signed character truncation—to an exact
CP-order difference.

The executable certificate is
`computations/transverse_residual_operator_tail.py`, with regression gates
in `tests/test_transverse_residual_operator_tail.py`.
