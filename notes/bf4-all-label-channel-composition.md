# BF4 all-label residual channel and fixed-distance composition obstruction

## Result

The direct physical/corridor measure order now has an exact
mass-preserving channel interpretation.  For the nine-slot Peter--Weyl
carrier let
\[
 U(g_1,\ldots,g_9)
 =
 \bigotimes_{j=1}^{9}\bigoplus_{n\ge0}D^n(g_j).
\]
This is unitary on the universal source/target Hilbert space
\[
 \mathcal H
 =
 \bigotimes_{j=1}^{9}\bigoplus_{n\ge0}V_n .
\]
For a probability law \(\alpha\) on the nine coarse holonomies define the
normal random-unitary channel
\[
 \Phi_\alpha(X)
 =
 \int U(g)XU(g)^*\,d\alpha(g).
\]

The fixed-coupling theorem supplies
\[
 \mu_{\rm phys}\ge\eta_s\mu_{\rm corr},
 \qquad
 \eta_s=\left(\frac{\ell_s}{H_s}\right)^{21}.
\]
Because both measures have mass one,
\[
 \omega_s
 =
 \frac{\mu_{\rm phys}-\eta_s\mu_{\rm corr}}{1-\eta_s}
\]
is again a probability measure.  Consequently
\[
 \boxed{\quad
 \Phi_{\rm phys}
 =
 \eta_s\Phi_{\rm corr}
 +(1-\eta_s)\Phi_{\omega_s}.
 \quad}
\]
Every term is normal, completely positive, trace preserving, and unital.
Thus the positive Choi difference does have a canonical mass-preserving
residual-channel promotion.

This is not yet the physical RG refresh decomposition.  In particular,
\(\Phi_{\rm corr}\) has not been proved to be the input-independent reset
map required by the constructive base-norm argument on the full carrier.
Nor has the channel obtained by abstract convolution been identified with
the conditional Haar-network channel obtained by gluing corrected slabs.

## Removing the trace-class feature weights

The trace-class Choi feature at heat coordinate \(u<1\) uses the positive
block weight
\[
 q_n(u)=(n+1)u^{n(n+2)}.
\]
At finite cutoff \(N\), the corresponding operator is
\[
 A_{u,N}(g)=U_N(g)Q_{u,N}^{1/2},
\]
where \(Q_{u,N}>0\) is block diagonal and commutes with \(U_N(g)\).
Congruence by \(Q_{u,N}^{-1/2}\) therefore converts the weighted Choi order
to the unweighted random-unitary Choi order.  Its source partial trace is
the identity, so the normalized residual is CPTP.

The cutoff restrictions are exact:
\[
 U_{N+1}|_{\mathcal H_N}=U_N.
\]
They define a projective family of finite CPTP channels and hence the
normal random-unitary channel on \(\mathcal H\).  The unweighted
infinite-dimensional Choi operator is not trace class; the channel is the
primary all-label object, while the \(u<1\) Choi operators remain its
trace-class probes.

## Abstract same-carrier composition

For probability laws \(\alpha,\beta\), with convolution convention
\((h,g)\mapsto hg\),
\[
 \Phi_\beta\circ\Phi_\alpha
 =
 \Phi_{\beta*\alpha}.
\]
This follows directly from \(U(h)U(g)=U(hg)\).  It proves an exact
same-carrier composition law for the abstract all-label channels and their
finite restrictions.

The missing identity is physical:
\[
 \Phi_{\text{Haar-network block glued over }[0,L]}
 \stackrel{?}{=}
 \Phi_{\mu_{a,m-1}}\circ\cdots\circ\Phi_{\mu_{a,0}} .
\]
The normalized one-slab laws can acquire boundary dependence when slabs are
glued, and shared Haar variables must be integrated only once.  Independence
or bare convolution cannot be assumed.  An executable gluing constructor
must pin those shared variables and prove the equality.

## Exact adjacent-slab fiber product

The gluing geometry is now pinned.  Translate a second 72-face corrected
slab by one unit in time and identify its lower spatial boundary with the
upper boundary of the first slab.  The census is:

| item | count |
|---|---:|
| faces in each slab | 72 |
| shared spatial interface faces | 24 |
| faces in the fixed-spatial union | 120 |
| links in each slab | 116 |
| shared interface links | 48 |
| links in the union | 184 |
| vertices in each slab | 52 |
| shared interface vertices | 26 |
| vertices in the union | 78 |

Every shared face and link is spatial and lies at time one.  The existing
`boundary_complete_slab_plaquettes(2)` is not this object: it enlarges all
three spatial directions together with time and contains 405 faces.

On the identified variables the one-slab density product obeys
\[
 W_{\rm lower}W_{\rm upper}
 =
 W_{\rm glued}W_{\rm interface},
\]
where \(W_{\rm interface}\) is the product of the 24 shared heat kernels.
Thus independent probability convolution both duplicates the shared
variables and counts their action twice.  Physical gluing is a boundary
fiber product, division by one interface factor, and a new partition
normalization.

A global floor/ceiling treatment of this correction also fails uniformly:
\[
 \eta_s^{\rm interface}
 =
 \left(\frac{\ell_s}{H_s}\right)^{24}
 \le
 \left(\frac{(1-s)^3}{1+s}\right)^{24}.
\]
On \(s=1-a\),
\[
 \eta_s^{\rm interface}\le a^{72}.
\]
The interface must therefore be integrated as part of the complete glued
block; it cannot be paid for afterward by another worst-holonomy ratio.

## Exact mass-preserving normalization by boundary messages

The fiber-product normalization algebra is also closed.  Assign the initial
spatial-slice weight to the incoming boundary law and, at each step, assign
the temporal plaquettes and target spatial-slice weight to one raw transfer
kernel \(T_j(x,y)\).  This counts every plaquette exactly once, and the raw
kernels compose to the glued density.

Independent row normalization of each \(T_j\) is not compatible with this
composition.  Instead choose a positive terminal boundary message \(h_m\)
and define backward
\[
 h_j(x)=\int T_j(x,y)h_{j+1}(y)\,dy.
\]
Then
\[
 P_j(x,dy)
 =
 \frac{T_j(x,y)h_{j+1}(y)}{h_j(x)}\,dy
\]
is mass preserving, and the message factors telescope:
\[
 (P_0\cdots P_{m-1})(x,dz)
 =
 \frac{(T_0\cdots T_{m-1})(x,z)h_m(z)}{h_0(x)}\,dz.
\]
Thus finite-horizon boundary-conditioned composition requires neither
independent convolution nor an infinite-volume Perron eigenfunction.

This theorem is implemented over exact nonnegative rational transfer
matrices in `computations/boundary_message_markovization.py`.  The continuous
all-label Yang--Mills transfer is now defined on the same geometry by
\[
 T_s(x,y)
 =
 W_{\rm sp}(x)^{1/2}
 \left[\int_{G^{20}}W_{\rm temp}(x,z,y)\,dz\right]
 W_{\rm sp}(y)^{1/2}.
\]
It acts between identical \(G^{48}\)-boundary carriers modulo boundary
gauge, is strictly positive, continuous, gauge invariant, and
time-reflection symmetric.  Its products reproduce the glued density with
the expected endpoint half-weights, and backward messages construct the
fine-boundary finite-horizon Markov channel.

What is not yet proved is a spacing-uniform relative bound on those
continuous messages or that the nine coarse holonomies form a Markov
intertwining/sufficient statistic for this fine-boundary channel.

There is already an exact obstruction to the simplest sufficiency claim.
In the pinned gauge, free link \(7\), geometrically
\[
 ((0,0,1,0),0),
\]
meets lower spatial faces \(1,9,10\) but none of the nine retained coarse
paths.  Changing only this link from \(I\) to the center element \(-I\)
leaves every retained coarse holonomy fixed, while the spatial density
changes because
\[
 K_s(I)-K_s(-I)
 =
 2\sum_{\substack{n\ge0\\n\ {\rm odd}}}
 (n+1)^2s^{n(n+2)}>0.
\]
Thus the raw transfer kernel does not factor through the nine coarse loops.
This does not by itself refute Markov lumpability after conditional
integration and backward-message normalization.  It proves that the next
step must either establish a genuine conditional-cancellation/lumpability
theorem or enlarge the retained carrier.

## Exact no-go for composing the current microscopic tags

Take the dyadic trajectory
\[
 a=2^{-k},\qquad s=1-a,\qquad m=a^{-1}=2^k .
\]
The current one-slab coefficient obeys
\[
 \eta_s
 \le
 \left(\frac{a^3}{2-a}\right)^{21}
 \le a^{63}.
\]
Expand a formal composition of \(m\) one-slab decompositions into corridor
and residual tags.  The total coefficient of every history containing at
least one certified corridor tag is
\[
 \varepsilon_{\rm tag}
 =
 1-(1-\eta_s)^m.
\]
Bernoulli's inequality gives the exact bound
\[
 \boxed{\quad
 \varepsilon_{\rm tag}
 \le m\eta_s
 \le a^{62}.
 \quad}
\]
It tends to zero over one fixed unit of physical distance.  This proves that
the present microscopic floor/ceiling certificate cannot be rescued merely
by composing its tagged corridor summands.

This does **not** prove that the physically glued block lacks a uniform
refresh.  It leaves two possibilities:

1. mixing contained in the residual histories supplies the missing mass;
2. a direct grouped relative-order estimate sees cancellations and Haar
   convolutions before the catastrophic microscopic minorization is taken.

## Remaining theorem

The next theorem starts from the now-constructed all-label boundary transfer
and must prove both:

1. despite the raw hidden-link witness, prove that conditional integration
   makes the nine-slot pushforward Markov-lumpable, or enlarge the retained
   carrier until an intertwining holds;
2. uniformly compare the boundary messages strongly enough that, before
   microscopic minorization,
   \[
   \Phi_{\mu_{a,L}^{\rm glue}}
   \succeq
   \varepsilon_L\Omega_{R_{a,L}},
   \qquad \varepsilon_L>0,
   \]
   uniformly in spacing, representation cutoff, and ambient volume.

The executable certificate is
`computations/physical_all_label_channel_composition.py`, with tests in
`tests/test_physical_all_label_channel_composition.py`.  The exact gluing
geometry and interface no-go are in
`computations/corrected_slab_physical_gluing.py`, tested by
`tests/test_corrected_slab_physical_gluing.py`.  Boundary-message
Markovization is tested by `tests/test_boundary_message_markovization.py`.
