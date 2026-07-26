# BF4 boundary-message order on the enlarged carrier

## Status

This note closes the carrier choice and the order algebra for the
continuous boundary-message route. It does **not** prove the interacting
four-dimensional mass gap.

The nine retained coarse holonomies are not known to be Markov-lumpable.
Instead, retain the complete connected spatial boundary graph. It has

\[
E=48,\qquad V=26,\qquad c=1,
\]

so tree gauge leaves

\[
r=E-V+c=23
\]

independent cycle variables, with residual root conjugation on invariant
observables. On this enlarged carrier the retained projection is the
identity. The source and target carriers agree, the all-label fine-boundary
transfer acts on them, and Markov intertwining is exact. The nine coarse
spatial holonomies are recoverable functions of the carrier; temporal
coarse observables remain part of the one-step environment/instrument.

This executes the “enlarge the retained carrier” branch. It makes no claim
that the smaller nine-loop carrier is lumpable.

## Terminal-independent row-order theorem

Let \(G(x,z)>0\) be a grouped raw kernel, let \(h(z)>0\) be any terminal
message, and fix a reference source \(x_0\). Suppose

\[
\alpha\le {G(x,z)\over G(x_0,z)}\le\beta
\]

for all sources and targets. Define

\[
H(x)=\int G(x,z)h(z)\,dz,\qquad
P(x,dz)={G(x,z)h(z)\over H(x)}\,dz.
\]

Integration gives

\[
\alpha\le {H(x)\over H(x_0)}\le\beta,
\]

and therefore

\[
P(x,dz)\ge {\alpha\over\beta}P(x_0,dz).
\]

The coefficient is independent of the terminal boundary condition. Thus a
two-sided row-Harnack estimate for the raw grouped kernel simultaneously
orders every continuous backward message and gives the required Markov
minorization.

The exact finite version is implemented by
`finite_grouped_message_order()` in
`computations/boundary_message_uniform_order.py`.

## Endpoint weights cancel

If

\[
G(x,z)=a(x)Q(x,z)b(z),
\]

then Markovizing \(G\) with terminal message \(h\) is exactly the same as
Markovizing \(Q\) with terminal message \(bh\). The source factor \(a(x)\)
cancels.

For the symmetric physical slab transfer, the correct relative coordinate
is

\[
g_j={h_j\over\sqrt{W_{\rm spatial}}}.
\]

Consequently the endpoint square roots of the spatial density are not part
of the hard uniform estimate. The remaining object is the interior
spatially weighted Feynman--Kac kernel.

## Spacing-uniform kinetic benchmark

Group heat steps until the effective heat coordinate is at most \(1/2\).
The exact one-cycle all-label estimates are

\[
{1055\over2272}\le K\le {3489\over2272}.
\]

On the 23-cycle product carrier this gives

\[
\left({1055\over3489}\right)^{23}
\le {G_{\rm kin}(x,z)\over G_{\rm kin}(x_0,z)}
\le
\left({3489\over1055}\right)^{23}.
\]

The terminal-independent common Markov mass is therefore

\[
\boxed{\varepsilon_{\rm kin}
=\left({1055\over3489}\right)^{46}>0.}
\]

It is independent of the microscopic spacing once the grouped heat cap is
met. This is a genuine uniform theorem for the 23-cycle kinetic reference
kernel, not for the full physical slab: it omits the spatial weights at
intermediate time slices.

## Stable positive-limit route

There is also a clean sufficient criterion for the interacting kernel. If
grouped physical kernels \(G_a\) converge uniformly to a kernel \(G_*\)
with

\[
q_{\min}=\inf G_*>0,\qquad q_{\max}=\sup G_*<\infty,
\]

and

\[
\lVert G_a-G_*\rVert_\infty\le\delta<q_{\min},
\]

then

\[
q_{\min}-\delta\le G_a\le q_{\max}+\delta
\]

and every backward-message Markovization has common mass at least

\[
\left({q_{\min}-\delta\over q_{\max}+\delta}\right)^2.
\]

The finite exact certificate is
`uniform_kernel_limit_message_order()`.
This criterion remains valid, but it is not necessary: a spacing-dependent
rank-one profile may localize and destroy every absolute floor while
canceling exactly from the normalized channel.

## Why positivity of the interior weights is insufficient

There is an exact two-state obstruction to any generic argument. Put
\[
a={1\over n},\qquad
Q_a=\begin{pmatrix}1&a\\a&1\end{pmatrix},\qquad
D_n=\operatorname{diag}(1,n).
\]
Then the two-step Feynman--Kac kernel \(Q_aD_nQ_a\) has
terminal-independent row-order mass
\[
\varepsilon_n={n\over n^2-n+1}\le {2\over n}\longrightarrow0.
\]
Thus strict positivity of an intermediate potential, by itself, cannot
give spacing-uniform order. This finite countermodel does not refute the
physical Yang--Mills Harnack estimate; it proves that the estimate must use
specific structure of the spatial plaquette weight. The executable witness is
`intermediate_potential_harnack_obstruction()`.

## Projective refinement and remaining obstruction

The physical grouped kernel includes the intermediate spatial plaquette
weights. A global comparison by their pointwise floor and ceiling repeats
the known weak-coupling collapse and is not useful. The exact invariant
consumer is instead the four-boundary ratio
\[
\Theta(G)=
\sup_{x,x',z,z'}
{G(x,z)G(x',z')\over G(x,z')G(x',z)}.
\]
A bound \(\Theta(G_{a,L})\le\Theta_L\) gives common Markov mass
\(\Theta_L^{-1}\) for every terminal message. Equivalently, it is enough to
prove relative convergence to a spacing-dependent rank-one Perron profile.
The profiles themselves need no uniform lower bound.

At fixed coupling, compact positivity-improving Perron theory supplies that
relative convergence. The remaining theorem is the spacing-uniform
two-buffer budget
\[
C_{s(a)}^2q_{s(a)}^{m(a,L)-2}\le\delta_L<1,
\]
or the four-boundary cross-product estimate directly.

The Yang--Mills spatial carrier has one exact flat gauge orbit: its cell
complex collapses to a cube boundary, and the tree-gauge linearized
curvature Gram obeys \(B^\mathsf TB>(1/11)I\). The remaining bridge is
not topological multiwell degeneracy. A reverse-collapse reconstruction also
gives the global bound
\(\sum_e d(U_e,I)^2\le81\sum_p d(U_p,I)^2\).

The temporal Haar integral now reduces exactly further. Its 24 faces are
edge cylinders over a connected 20-vertex graph, so tree gauge leaves five
chord holonomies. A spanning tree of that graph extends to the full
boundary, and conditional integration over the 18 complementary Haar
coordinates gives
\[
T_s^m=M_{\sqrt W}R^\ast
k_s(M_{\overline W_s}k_s)^{m-1}R M_{\sqrt W}.
\]
Thus the physical cross-ratio is exactly that of a five-holonomy effective
Feynman--Kac kernel. The remaining work is the spacing-uniform
heat-kernel/Perron promotion for this reduced kernel.

The executable gates are
`computations/boundary_message_markovization.py`,
`computations/boundary_message_uniform_order.py`, and
`computations/boundary_message_projective_harnack.py`. See
`notes/bf4-physical-feynman-kac-projective-harnack.md`.
