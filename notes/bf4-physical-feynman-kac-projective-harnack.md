# BF4 physical Feynman--Kac projective Harnack route

## Status

The absolute positive-kernel limit proposed in the first boundary-message
reduction is stronger than the normalized physical channel needs. The exact
consumer is a four-boundary cross-ratio. This note proves the projective
reduction, derives a fixed-coupling two-buffer Perron estimate, and isolates
one spacing-uniform Yang--Mills estimate.

It does **not** prove that estimate or the Yang--Mills mass gap.

## Four-boundary order theorem

Let \(G(x,z)>0\) be the grouped physical Feynman--Kac kernel and let
\[
H_h(x)=\int G(x,z)h(z)\,dz,\qquad
P_h(x,dz)={G(x,z)h(z)\over H_h(x)}\,dz
\]
for an arbitrary positive terminal message \(h\).

Define
\[
\Theta(G)=
\sup_{x,x',z,z'}
{G(x,z)G(x',z')\over G(x,z')G(x',z)}.
\]

For fixed \(x,x'\), put \(r(z)=G(x,z)/G(x',z)\). Then
\[
{H_h(x)\over H_h(x')}
\]
is a weighted average of \(r\), with positive weights
\(G(x',z)h(z)\). It therefore lies between \(\inf r\) and \(\sup r\).
Consequently
\[
{P_h(x,dz)\over P_h(x',dz)}
=
{r(z)\over H_h(x)/H_h(x')}
\ge {\inf r\over\sup r}
\ge {1\over\Theta(G)}.
\]

Thus
\[
\boxed{
P_h(x,dz)\ge\Theta(G)^{-1}P_h(x',dz)
}
\]
for every source pair and every terminal message. The coefficient is
terminal-independent.

This is implemented in exact arithmetic by
`cross_ratio_backward_message_order()`. It reuses the repository's
`certify_positive_sector()` cross-ratio engine.

## Why absolute positive-kernel convergence is unnecessary

The cross-ratio is unchanged under arbitrary positive source and target
profiles:
\[
G(x,z)\longmapsto a(x)G(x,z)b(z).
\]
All four profile factors cancel.

Suppose, more generally, that
\[
G_a(x,z)=\alpha_a(x)\beta_a(z)(1+r_a(x,z)),
\qquad
|r_a(x,z)|\le\delta<1.
\]
The profiles may depend on the lattice spacing and may localize. Directly,
\[
\Theta(G_a)
\le
\left({1+\delta\over1-\delta}\right)^2,
\]
so every backward-message channel has common mass at least
\[
\boxed{
\varepsilon_L
\ge
\left({1-\delta\over1+\delta}\right)^2.
}
\]

The executable certificate is `relative_rank_one_projective_order()`.

There is also an exact family showing why this relaxation matters. Let
\[
\alpha_n={1\over n+1}(1,n),\qquad
\beta_n={1\over n+1}(n,1),\qquad
G_n=\alpha_n\otimes\beta_n.
\]
Then
\[
\inf G_n={1\over(n+1)^2}\longrightarrow0,
\]
so no spacing-independent absolute kernel floor survives. Nevertheless
\(\Theta(G_n)=1\), and every normalized row is identical. The common
Markov mass is exactly one.

This witness is `localized_rank_one_profile_witness()`.

## Fixed-coupling physical Perron convergence

For fixed \(0<s<1\), the physical boundary transfer \(T_s\) has a strictly
positive continuous symmetric kernel on the compact boundary quotient.
Hence its integral operator is compact and positivity improving. Standard
Jentzsch--Perron theory gives:

- a simple leading eigenvalue \(\lambda_s>0\);
- a continuous strictly positive eigenfunction \(\phi_s\);
- a strict fixed-coupling spectral ratio
  \[
  q_s={\sup_{\lambda\ne\lambda_s}|\lambda|\over\lambda_s}<1.
  \]

At fixed \(s\), compactness also gives
\(\inf\phi_s>0\). Two transfer factors turn the operator-norm Perron
remainder into a uniform kernel remainder.

More precisely, define
\[
C_s=
\sup_x{\lVert T_s(x,\cdot)\rVert_2\over
             \lambda_s\phi_s(x)}.
\]
Using
\[
T_s^m-\lambda_s^m\Pi_s
=
T_s\bigl(T_s^{m-2}-\lambda_s^{m-2}\Pi_s\bigr)T_s
\]
and the \(L^2\) spectral theorem gives
\[
\left|
{T_s^m(x,z)\over
 \lambda_s^m\phi_s(x)\phi_s(z)}
-1
\right|
\le
C_s^2q_s^{m-2}.
\tag{PH}
\]

This is the exact scalar interface recorded by
`intrinsic_perron_remainder_budget()`.

## Yang--Mills-specific single-flat-orbit coercivity

The spatial potential is the product of 24 plaquette heat kernels on the
48-link, 26-vertex retained boundary. The tempting claim that these faces
are already a quadrangulated sphere is false: their edge-face degree census
is
\[
(1:24),\qquad(2:6),\qquad(3:12),\qquad(4:6).
\]

The exact cell complex nevertheless has the required single-well topology.
Its boundary ranks over \(\mathbf F_2\) are
\[
\operatorname{rank}\partial_1=25,\qquad
\operatorname{rank}\partial_2=23,
\]
so its Betti numbers are \((1,0,1)\). More constructively:

1. eighteen face--free-edge elementary collapses leave six faces;
2. those six faces, twelve edges and eight vertices are the boundary of one
   cube;
3. eighteen graph leaf collapses remove the remaining attached forest.

Thus the full spatial complex deformation retracts onto \(S^2\). In
particular its fundamental group is trivial. Every flat \(SU(2)\)
connection is gauge equivalent to the trivial connection, and multiple
topological flat wells are excluded.

There is also an exact local coercivity estimate. Deterministic tree gauge
leaves 23 cycle variables. The linearized plaquette-curvature matrix
\[
B:\mathbf R^{23}\longrightarrow\mathbf R^{24}
\]
has full column rank. Its Gram matrix satisfies
\[
\operatorname{tr}(B^\mathsf TB)=47,\qquad
\det(B^\mathsf TB)=6.
\]
Every leading principal minor of
\[
11B^\mathsf TB-I
\]
is positive; the smallest of these integer minors is \(32\). Sylvester's
criterion therefore gives the exact bound
\[
\boxed{
\lVert B\xi\rVert_2^2>{1\over11}\lVert\xi\rVert_2^2.
}
\]

The executable certificate is
`boundary_spatial_flatness_coercivity()`.

The same collapse supplies a global nonlinear inequality. Omit one
redundant face. The remaining 23 faces collapse through 23 face--edge pairs
to a 25-edge spanning tree. In tree gauge, reversing the collapse
reconstructs every one of the 23 non-tree link variables from plaquette
holonomies. Bi-invariance and the triangle inequality give coefficient
vectors whose largest \(\ell^1\) weight is \(9\), largest coefficient is
\(2\), and total squared \(\ell^2\) weight is \(81\). Therefore
\[
\boxed{
\sum_{\text{23 cycles}}d(U_e,I)^2
\le
81\sum_{\text{24 faces}}d(U_p,I)^2.
}
\tag{GC}
\]

This proves uniqueness and both local and global metric coercivity of the
flat well. The remaining estimates can therefore be formulated around one
globally controlled well rather than a sum over topological sectors.

## Exact nonlinear five-holonomy reduction

The temporal kinetic kernel is not linearly elliptic on all 23 retained
cycles. After tree gauge on both boundaries, the temporal incidence matrix
has
\[
24\ \text{faces},\qquad
23+23\ \text{boundary cycle columns},\qquad
20\ \text{temporal-link columns}.
\]
Its full rank is \(24\), while the temporal-link submatrix has rank \(19\).
Eliminating the internal temporal directions leaves relative rank
\[
24-19=5.
\]

An explicit integral \(5\times24\) left annihilator of the temporal-link
columns gives the effective boundary matrix
\[
\bigl(e_i,-e_i\bigr),
\qquad i\in\{0,4,5,6,10\}.
\]
Thus the five linearized kinetic directions are literal differences between
the same five source and target cycle coordinates.

This rank is not only infinitesimal. The 24 temporal faces are exactly the
edge cylinders over a connected spatial graph \(\Gamma\) with
\[
|V(\Gamma)|=20,\qquad |E(\Gamma)|=24.
\]
The 20 temporal links are in bijection with its vertices. If \(A,B\) are
the restrictions of the source and target boundary connections to
\(\Gamma\), the temporal Haar integral has the form
\[
\kappa_s(A,B)
=
\int_{SU(2)^{V(\Gamma)}}
\prod_{e=(v,w)}
K_s\!\left(A_e g_w B_e^{-1}g_v^{-1}\right)
\prod_v dg_v,
\tag{TK}
\]
up to the harmless choice of edge orientation.

The kernel (TK) is invariant under independent vertex-gauge changes of
\(A\) and \(B\), by a Haar change of variables in \(g\). Choose a spanning
tree of \(\Gamma\) and pin its root gauge. Tree gauge sets its 19 tree
links to the identity and leaves
\[
|E|-|V|+1=5
\]
chord holonomies. Consequently there is an exact positive kernel \(k_s\)
on five source and five target holonomies such that
\[
\kappa_s(A,B)=k_s(\pi A,\pi B).
\tag{5H}
\]
The 19-edge tree of \(\Gamma\) extends to a 25-edge spanning tree of the
full 26-vertex boundary graph. In that adapted full-boundary tree gauge,
\(\pi\) is literally projection onto five of the 23 chord coordinates and
Haar measure is product Haar along the complementary 18 coordinates. For
the repository's original deterministic full-boundary tree, the matching
linearized indices are \(\{0,4,5,6,10\}\).

The executable certificate
`boundary_temporal_relative_coupling()` verifies the edge-cylinder
bijection, connectivity, cycle rank, the five exact chord indices and the
matching linear annihilator.

## Exact conditional-integration identity

Let \(X=SU(2)^{23}\) be the based-tree-gauge fine boundary carrier, let
\(Y=SU(2)^5\), and let \(\pi:X\to Y\) record the five temporal-graph chord
holonomies. It is a coordinate projection in the adapted gauge above and
generally nonlinear in another full-graph tree gauge. Write \(R\) for
conditional Haar integration over the 18-dimensional fibers of \(\pi\),
and let \(R^\ast f=f\circ\pi\). If \(W_s>0\) is the full 24-plaquette
spatial weight, define
\[
\overline W_s=R\,M_{W_s}\,R^\ast,\qquad
\overline W_s(y)
=\int_{\pi^{-1}(y)}W_s(x)\,d\mu_y(x).
\]
Thus \(\overline W_s\) is multiplication by a strictly positive continuous
five-holonomy weight.

The one-slab physical transfer is exactly
\[
T_s=M_{\sqrt{W_s}}R^\ast k_s R M_{\sqrt{W_s}}.
\]
Using \(R M_{W_s}R^\ast=M_{\overline W_s}\), induction gives
\[
\boxed{
T_s^m
=M_{\sqrt{W_s}}R^\ast
k_s\bigl(M_{\overline W_s}k_s\bigr)^{m-1}
R M_{\sqrt{W_s}}.
}
\tag{FR}
\]
This is the nonlinear conditional-lumpability identity sought in the
earlier carrier fork. The 18 complementary fine-boundary directions have
not been discarded or bounded by extrema: they are integrated exactly into
\(\overline W_s\).

In the four-boundary cross-ratio of the kernel of \(T_s^m\), both endpoint
\(\sqrt{W_s}\) profiles cancel. Hence its projective distortion is exactly
the distortion of the five-holonomy grouped kernel
\[
G^{(5)}_{s,m}
=k_s\bigl(M_{\overline W_s}k_s\bigr)^{m-1}.
\tag{5FK}
\]
No 23-dimensional temporal ellipticity or spatial--temporal
hypocoercivity hypothesis is needed.

## The spacing-uniform theorem now required

Let \(s=s(a)\), and let \(m(a,L)\) be the number of microscopic slabs in
fixed physical length \(L\). Apply fixed-coupling Perron theory to the
five-holonomy effective transfer (5FK). It is sufficient to prove
\[
\boxed{
C_{s(a)}^2q_{s(a)}^{m(a,L)-2}
\le\delta_L<1
}
\tag{UPH}
\]
uniformly in spacing and ambient volume, with \(C_s,q_s\) now belonging to
the five-holonomy effective operator.

Then (PH) and the relative rank-one theorem give
\[
\Theta(T_{s(a)}^{m(a,L)})
\le
\left({1+\delta_L\over1-\delta_L}\right)^2
\]
and hence a spacing-uniform order bound for every continuous backward
message.

The Perron profile \(\phi_{s(a)}\) is allowed to localize. Neither a uniform
lower bound on \(\phi_{s(a)}\) nor an absolute positive limit of the
normalized kernels is required; all profile factors cancel from the
four-boundary ratio.

## Direct Yang--Mills boundary-interaction form

The spectral quantities in (UPH) can be avoided by proving the equivalent
division-free estimate directly:
\[
G_{a,L}(x,z)G_{a,L}(x',z')
\le
\Theta_L
G_{a,L}(x,z')G_{a,L}(x',z),
\qquad \Theta_L<\infty.
\tag{CR}
\]

For the physical path integral, source-only and target-only free-energy
factors cancel from (CR). By (FR), the same is true before any estimate:
the 23-cycle problem reduces exactly to the five-holonomy effective kernel.
What remains is the connected interaction between its two time boundaries.
This makes a surface/polymer expansion a natural Yang--Mills-specific route:
after the four-term cancellation, only components that communicate between
the source and target can contribute to the projective distortion.

The unproved estimate is therefore no longer an absolute floor/ceiling
bound on all interior plaquette weights. It is a uniform bound on the
connected boundary-to-boundary distortion:
\[
\log\Theta(G_{a,L})
\]
or, without logarithms, the cross-product inequality (CR).

The physical options are now:

1. combine the exact fiber weight \(\overline W_s\), the global \(1/81\)
   curvature bound and uniform \(SU(2)\) heat-kernel estimates to prove the
   five-holonomy intrinsic Perron budget (UPH), including uniform control
   of \(C_{s(a)}\) and accumulated decay of \(q_{s(a)}\); or
2. prove (CR) directly on (5FK) by a connected surface/cluster
   reorganization of the grouped all-label integral.

The executable frontier is
`physical_feynman_kac_projective_route()`. It fails closed at precisely
this spacing-uniform five-holonomy four-boundary estimate.
