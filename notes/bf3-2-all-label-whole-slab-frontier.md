# BF3.2 — all-label whole-slab kernel frontier

Date: 2026-07-25

Status: **fixed-block all-label construction complete; full BF3.2 remains
open**.

## 1. Result

The exact BF3.1 Haar coefficient for every nine-word coarse Wilson insertion
now has a constructive all-label completion.  If \(0<s<1\) is the heat
coordinate and \(n\) is the doubled \(SU(2)\) label, then

\[
  (n+1)s^{n(n+2)}\lvert\chi_n(g)\rvert
  \le h_n(s):=(n+1)^2s^{n(n+2)}.
\]

The ratio after the first label omitted by cutoff \(N\) is

\[
  r_N(s)
  =
  \frac{(N+3)^2}{(N+2)^2}s^{2N+5}.
\]

It decreases thereafter.  Whenever \(r_N(s)<1\),

\[
  \sum_{n>N}h_n(s)
  \le
  T_N(s):=
  \frac{(N+2)^2s^{(N+1)(N+3)}}{1-r_N(s)}.
\]

For the corrected slab's 72 fine plaquettes, put

\[
  H_N(s)=\sum_{n=0}^{N}h_n(s)+T_N(s).
\]

The difference between the literal all-label Haar coefficient and the
finite \(72\)-label-cube sum is bounded by

\[
  D_{\mathrm{ext}}\,
  72H_N(s)^{71}T_N(s),
\]

where \(D_{\mathrm{ext}}\) is the product of the dimensions of the inserted
coarse Wilson representations.  Therefore the dimension-weighted
coefficient norm is uniform in every external label.

This is an actual Cauchy name, not a formal series label.  Its \(N\)-th
approximant enumerates the finite cube

\[
  \{0,\ldots,N\}^{72}
\]

and sends every term through the same exact Haar integrator used by BF3.1.
The literal evaluator is definition-level and exponential; BF3.1's affine
and incidence reductions remain the practical low-cutoff engine.

## 2. Normalized strong-coupling corridor

The same estimate controls the normalized Gibbs density where the elementary
character majorant supplies a positive pointwise floor.  If

\[
  E_N(s):=H_N(s)-1<1,
\]

then each plaquette heat kernel is at least \(1-E_N(s)\).  Consequently the
72-face partition function is at least

\[
  (1-E_N(s))^{72},
\]

and the normalized \(L^1\) difference is bounded by

\[
  \frac{2\cdot72H_N(s)^{71}T_N(s)}
       {(1-E_N(s))^{72}}.
\]

At \(s=\tfrac12\), the least cutoff certified by this elementary bound for
normalized error below \(10^{-2}\) is \(N=11\).  This is a bound on the
actual plaquette-coupled Haar density on the fixed corrected slab, not on
the older product-of-multiplicities surrogate.

The cutoff selection is constructive and coupling dependent.  In the raw
dimension-weighted coefficient norm, the least cutoffs for tolerance
\(10^{-2}\) increase strictly at the sample points
\(s=\tfrac12,\tfrac34,\tfrac9{10}\).  This directly implements the
coupling-dependence required by the BF3.3 near-continuum fence.

## 3. All-coupling Jacobi floor

The elementary floor \(1-E_N(s)\) is limited to strong coupling, but the
differentiated Jacobi triple product gives a rational pointwise floor for
every rational \(0<s<1\).  In the conjugacy coordinate
\(x=\cos\theta\),

\[
 K_s(x)=\frac{\vartheta_3(x)}{2s}S_s(x),
\]

where

\[
\begin{aligned}
\vartheta_3(x)
&=
\prod_{n\ge1}
  (1-s^{2n})
  (1+2s^{2n-1}x+s^{4n-2}),\\
S_s(x)
&=
\sum_{n\ge1}
\frac{2s^{2n-1}}
 {1+2s^{2n-1}x+s^{4n-2}}.
\end{aligned}
\]

For \(-1\le x\le1\),

\[
 1+2s^{2n-1}x+s^{4n-2}
 \ge (1-s^{2n-1})^2,
\]

and the first term of \(S_s\) is at least
\(2s/(1+s)^2\).  Define

\[
\begin{aligned}
P_M(s)
&=
\prod_{n=1}^{M}
(1-s^{2n})(1-s^{2n-1})^2,\\
\delta_M(s)
&=
\frac{s^{2M+2}+2s^{2M+1}}{1-s^2}.
\end{aligned}
\]

The elementary product inequality
\(\prod_i(1-x_i)\ge1-\sum_i x_i\) gives, whenever
\(\delta_M(s)<1\),

\[
  K_s(x)
  \ge
  L_{s,M}
  :=
  \frac{P_M(s)(1-\delta_M(s))}{(1+s)^2}
  >0
\]

uniformly on the complete conjugacy interval.  Increasing \(M\) eventually
makes \(\delta_M(s)<1\), so this is a terminating rational construction at
every rational coupling.

Combining \(L_{s,M}\) with the super-geometric character tail selects a
cutoff satisfying both

\[
  T_N(s)<L_{s,M}
\]

and

\[
 \frac{2\cdot72H_N(s)^{71}T_N(s)}
 {L_{s,M}^{72}}
 \le\varepsilon.
\]

The first inequality proves that the truncated plaquette kernel itself is
positive; the second bounds the normalized conditional law.  Sample exact
certificate sizes are:

| \(s\) | Jacobi product terms | rational floor (decimal guide) |
|---:|---:|---:|
| \(1/2\) | 1 | \(4.8611\times10^{-2}\) |
| \(3/4\) | 3 | \(1.5701\times10^{-4}\) |
| \(9/10\) | 13 | \(5.6593\times10^{-11}\) |

For \(s=3/4\) and normalized tolerance \(10^{-1}\), the least cutoff
certified by this deliberately crude floor is \(N=49\).

The rational inequalities and schedule are executable.  The analytic input
is the standard differentiated Jacobi triple-product identity.  The
repository's `HeatKernelPos*.lean` files explicitly leave that infinite
identity unformalized, so the frontier records the distinction: the
paper-level all-coupling floor is complete, while its axiom-clean Lean
transport remains open.

## 4. Why this does not close BF3.2

Three distinct norms must not be conflated.

1. The estimate above controls a dimension-weighted matrix coefficient and
   the \(L^1\) difference of two local conditional Gibbs densities.
2. BF2's carrier is the cone of positive trace-class kernels on the complete
   fusion/intertwiner boundary Hilbert space.
3. BF4 needs the Hilbert projective metric on a cone invariant under the
   normalized physical block map.

The first additional theorem—the trace-norm identification for
representation truncation—can now be proved.

For one boundary holonomy, use the heat-weighted Peter--Weyl feature vector

\[
 v_s(g)_{nmk}
 =
 \sqrt{(n+1)s^{n(n+2)}}D^n_{mk}(g).
\]

Unitarity gives

\[
 \lVert v_s(g)\rVert^2
 =
 \sum_n(n+1)^2s^{n(n+2)}
 \le H_N(s)
\]

uniformly in \(g\).  Tensoring over the nine coarse Wilson holonomies gives
evaluation norm at most \(H_N(s)^9\).  If \(\delta\mu\) is the normalized
local Gibbs truncation error, then the reflected Gram difference is a
Bochner integral of rank-one kernels,

\[
 \delta G
 =
 \int |v(U)\rangle\langle v(U)|\,d\delta\mu(U),
\]

and hence

\[
 \lVert\delta G\rVert_1
 \le
 H_N(s)^9\lVert\delta\mu\rVert_{L^1}.
\]

Resolving gauge invariance and intertwiners is an orthogonal projection and
cannot increase this norm.  For the finite boundary projection \(P\) and
\(Q=1-P\), the trace ideal property gives

\[
\begin{aligned}
\lVert P\delta GP\rVert_1&\le\lVert\delta G\rVert_1,\\
\lVert P\delta GQ\rVert_1&\le\lVert\delta G\rVert_1,\\
\lVert Q\delta GP\rVert_1&\le\lVert\delta G\rVert_1,\\
\lVert Q\delta GQ\rVert_1&\le\lVert\delta G\rVert_1.
\end{aligned}
\]

Signed orthonormal \(F/R\) recouplings are unitary and preserve trace norm.
This identifies the character/Gibbs tail with the BF2 trace-class
boundary-kernel norm and retains every coherent corner.  It also makes the
complete boundary Gram a trace-norm Cauchy object.

This theorem does not say the raw physical block is trace preserving, nor
does it make complete positivity a Hilbert-metric contraction.  It controls
only the representation truncation of a fixed exact conditional law.
Moreover, trace-norm convergence does not imply convergence in BF4's
relative heat order: an error supported on the smallest heat eigenvalue can
have vanishing trace norm and relative-order norm one.  That exact
counter-witness is recorded in
`computations/reference_order_birkhoff.py`.

The present product estimate also contains \(H_N^{F-1}\) and a factor \(F\)
for \(F\) active plaquettes.  It is therefore not a uniform estimate on a
single global density when \(F\) is the total lattice volume.  This agrees
with the axiom-free obstruction
`Z4FixedCutoffNaiveTailFence`: an independent first-omitted-label charge
summed over every plaquette is unbounded on cofinal boxes.  A valid
volume-uniform BF3.2 estimate must instead use a local conditional norm,
connected-cluster cancellation, or another localization mechanism.

For a conditional block kernel, all
plaquette factors disjoint from the corrected slab cancel between numerator
and normalizer.  Exactly 72 active plaquettes remain, and fixed exterior
links only change their holonomies.  Since both the character upper bound and
the Jacobi lower bound are pointwise and uniform in the holonomy,
the normalized conditional truncation estimate above is uniform in the
ambient finite volume and in the boundary condition at every rational
coupling.

Finally, representation truncation is not the RG remainder.  The actual
remainder compares the normalized fine Gibbs pushforward with the actual
coarse Gibbs law and retains

\[
  P\Phi Q,\qquad Q\Phi P,\qquad Q\Phi Q.
\]

`CompactDualPhysicalRemainderLocality` proves that every intertwined
fine/coarse cylinder mismatch lower-bounds its \(L^1\) norm.  Thus no global
refresh kernel can manufacture a zero remainder; the physical cylinder
mismatches still have to be bounded.

## 4. Gate ledger

| BF3.2 obligation | Result |
|---|---|
| all-label fusion/intertwiner field over every coarse word | coefficient-level exact Haar Cauchy name for all nine coarse Wilson labels |
| summable heat tail on one corrected slab | explicit super-geometric bound |
| external-label uniformity | complete after division by the product of representation dimensions |
| coupling-dependent cutoff schedule | constructive |
| normalized actual density tail | complete in the elementary strong-coupling corridor |
| rational all-coupling heat-kernel floor and positive truncated law | complete using the differentiated Jacobi identity; Lean transport open |
| identify the complete open-boundary tail with the BF2 trace-class kernel norm | complete for representation truncation |
| control all coherent \(P/Q\) truncation blocks in that norm | complete |
| boundary/ambient-volume-uniform conditional truncation tail | complete at every rational coupling |
| global additive volume tail | impossible by the naïve route; localization is mandatory |
| bound the actual fine/coarse RG remainder | open |
| pass a ready physical kernel to BF4 | not yet admissible |

The next theorem is therefore:

> Construct the actual local fine-to-coarse Haar pushforward and compare it
> with the actual coarse Gibbs conditional law in the same BF2 trace norm;
> bound every resulting cylinder mismatch and coherent remainder with
> constants independent of ambient volume.  Then strengthen the centered
> remainder to the relative heat-order inequality required by BF4.

Only after this theorem can the grouped physical map be tested against
BF4's nine-field handoff.

## 6. Reproduction

- `computations/all_label_whole_slab_tail.py`;
- `tests/test_all_label_whole_slab_tail.py`;
- `notes/bf2-1-general-reflection-positive-carrier.md`;
- `lean/YMGap/Continuum/Z4FixedCutoffNaiveTailFence.lean`;
- `lean/YMGap/Continuum/CompactDualPhysicalRemainderLocality.lean`.

The executable frontier is
`computations.all_label_whole_slab_tail.bf32_all_label_frontier()`.
