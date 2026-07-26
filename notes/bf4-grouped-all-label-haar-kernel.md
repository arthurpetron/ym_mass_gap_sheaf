# BF4 grouped all-label Haar kernel: exact corridor result and physical frontier

Date: 2026-07-25  
Status: **all-label heat corridor positive; interacting corrected-slab
domination open**

## 1. Verdict

There are two mathematically distinct questions hidden in “construct the
grouped all-label Haar/fusion kernel.”

1. Does an actual all-label Haar-convolution corridor exhibit a common
   faithful packet with a spacing-uniform mass after fixed-distance grouping?
2. Does the complete interacting corrected-slab block contain that corridor
   in positive, preferably completely-positive, order?

The answer to the first question is **yes**, with an explicit rational
certificate.  The answer to the second is **not yet known** from the
repository's present BF3.2 construction.

The exact corridor constant is

\[
  \boxed{\varepsilon_0=\frac{1055}{2272}>0.}
\]

If \(r\) independent group coordinates are refreshed, the common product
packet has mass at least

\[
  \varepsilon_r=\left(\frac{1055}{2272}\right)^r.
\]

For the nine coarse Wilson holonomies used by BF3.2,

\[
  \varepsilon_9
  =
  \left(\frac{1055}{2272}\right)^9
  \approx 1.003789\times10^{-3}.
\]

This is many orders of magnitude stronger than the microscopic
72-plaquette pointwise floor.  More importantly, it is independent of the
representation cutoff.  It becomes a spacing-uniform physical BF4
certificate only after two further facts are proved:

- a corrected-slab CP-order domination/factorization through a finite
  corridor cover;
- the cumulative heat condition along the physical spacing trajectory.

BF4 therefore remains open, but its proposed grouped mechanism has passed
its first genuine all-label test.

## 2. Exact all-label corridor

Use the repository's doubled label \(n\) and rational heat coordinate
\(0<s<1\):

\[
  K_s(g)
  =
  \sum_{n\ge0}
    (n+1)s^{n(n+2)}\chi_n(g).
\]

Character orthogonality gives the exact central convolution law

\[
  K_s*K_t=K_{st}.
\]

Consequently a corridor of \(m\) Haar-integrated heat plaquettes has

\[
  K_s^{*m}=K_u,\qquad u=s^m,
\]

and every Peter--Weyl mode has the exact multiplier

\[
  u^{n(n+2)}=s^{m n(n+2)}.
\]

This is the all-label continuation of the cutoff-two disk calculation in
`notes/bf1-6-reflection-cut-half-surface.md`, where four fine plaquettes
produced the modes

\[
  1,\qquad2s^{12},\qquad3s^{32}.
\]

Those are exactly the \(n=0,1,2\) terms of \(K_{s^4}\).

## 3. A rational common Haar floor

Suppose

\[
  0<u\le\frac12.
\]

The character bound \(\lvert\chi_n(g)\rvert\le n+1\) gives

\[
 K_u(g)
 \ge
 1-\sum_{n\ge1}(n+1)^2u^{n(n+2)}.
\]

Every term is increasing in \(u\), so it is enough to use \(u=\tfrac12\).
The first excited term is

\[
 4\left(\frac12\right)^3=\frac12.
\]

For the remaining labels \(n\ge2\), the first term is \(9/256\), and the
successive-ratio majorant from BF3.2 is

\[
 \frac{16}{9}\left(\frac12\right)^7=\frac1{72}.
\]

Thus

\[
 \sum_{n\ge2}(n+1)^2
   \left(\frac12\right)^{n(n+2)}
 \le
 \frac{9/256}{1-1/72}
 =
 \frac{81}{2272}.
\]

It follows that, for every \(g\in SU(2)\),

\[
\begin{aligned}
 K_u(g)
 &\ge
 1-\frac12-\frac{81}{2272}\\
 &=\frac{1055}{2272}.
\end{aligned}
\]

Since normalized Haar measure \(\lambda\) has mass one and
\(\int K_u\,d\lambda=1\), the Markov kernel

\[
 P_u(g,dh)=K_u(gh^{-1})\,\lambda(dh)
\]

has the literal refresh decomposition

\[
 P_u
 =
 \varepsilon_0\Omega_\lambda
 +(1-\varepsilon_0)Q_u,
\qquad
 \varepsilon_0=\frac{1055}{2272},
\]

where \(Q_u\) is again a positive Markov kernel.  The constructive theorem
in `ConstructiveRefreshContraction.lean` therefore gives a base-norm rate

\[
 1-\varepsilon_0=\frac{1217}{2272}.
\]

No representation cutoff, logarithm, minimum over a continuum, or
compactness argument occurs in this certificate.

## 4. Why the packet is all-label and faithful

The packet is normalized Haar on the group-coordinate carrier, not a
vacuum-only representation packet.  For \(u>0\), every Peter--Weyl mode has
strictly positive heat weight

\[
 u^{n(n+2)}>0
 \qquad(n=0,1,2,\ldots).
\]

Hence the corresponding heat-weighted Peter--Weyl Gram has no missing
representation label.  Tensoring finitely many such coordinates retains
strictly positive weight in every finite tensor label.

There is an important scope qualification.  After the deterministic
coarse-holonomy pushforward, the Haar packet is faithful on the image
carrier.  Proving that this image is the whole quantitative BF2
reference-order component—or identifying the correct smaller component—is
part of the corrected-slab corridor-cover theorem still required below.

## 5. Fixed physical distance without logarithms

Let \(a>0\) be the spacing, \(L>0\) a fixed physical distance, and

\[
 m(a,L)=\left\lceil\frac{L}{a}\right\rceil.
\]

The exact constructive cumulative-heat condition is

\[
 \boxed{\quad
   s(a)^{m(a,L)}\le\frac12.
 \quad}
 \tag{CH}_{L}
\]

Whenever \((\mathrm{CH})_L\) holds, every grouped corridor has the same
rational common mass \(\varepsilon_0\), independent of \(a\).  A cover by
\(r\) corridor coordinates has mass at least \(\varepsilon_0^r\).

The executable dyadic model

\[
 a_N=\frac1N,\qquad s_N=1-\frac1N,\qquad m=N
\]

satisfies

\[
 s_N^N\le\frac12
\]

for every tested dyadic \(N\ge2\), and therefore carries one identical
rational packet at every spacing.  This is an exact model of the mechanism,
not a proof that the physical Yang--Mills trajectory has this particular
\(s(a)\).

The physical program must derive \((\mathrm{CH})_L\) from the actual
coupling/spacing relation.  Stating that relation is unavoidable: without
it one can choose \(s(a)\) so close to one that the fixed-distance grouped
coordinate remains above \(1/2\).

### The cumulative condition controls a bare heat mode, not yet the physical gap

The condition is not automatic from grouping, but its exact content must be
named correctly.
Let

\[
 \rho(a)=s(a)^3
\]

be the exact fundamental Fourier multiplier of the local heat kernel.  If
\(m=\lceil L/a\rceil\) and \(s(a)^m\le1/2\), then

\[
 \rho(a)^m=s(a)^{3m}\le\frac18.
\]

The exact Bernoulli bound

\[
 1-\rho^m\le m(1-\rho)
\]

therefore gives

\[
 1-\rho(a)\ge\frac{7}{8m}.
\]

Since \(ma\le L+a\), for \(a\le L\),

\[
 \boxed{\quad
 \frac{1-\rho(a)}{a}
 \ge
 \frac{7}{8ma}
 \ge
 \frac{7}{16L}.
 \quad}
\]

Thus \((\mathrm{CH})_L\) implies a spacing-uniform lower bound on the
rescaled **bare heat-kernel mode margin**.  Conversely, a suitable positive
lower bound on this bare quantity supplies a grouped subunit rate after
choosing \(L\) large enough.

This does not identify \(\rho(a)\) with the second eigenvalue of the
interacting four-dimensional, gauge-invariant transfer operator.  That
identification is the repository's separate open physical-margin bridge.  In
fact the usual bare asymptotic-freedom scaling can make
\((1-\rho(a))/a\) diverge, which is a diagnostic that this local multiplier
is not itself the finite continuum mass.

The corridor calculation therefore establishes a narrower equivalence:

> a cumulative bare heat estimate produces an explicit all-label refresh
> packet, while a uniform grouped-half condition bounds the same rescaled
> bare mode.

The BF4 work is to prove the interacting corrected-slab CP-domination and
derive the needed bare coupling/spacing estimate from the actual trajectory.
Promotion of the resulting grouped contraction to a physical mass gap still
requires the shared-object transfer/OS identification in BF6--BF8.

## 6. Audit of the current “actual” BF3.2 object

The current all-label construction in
`computations/all_label_whole_slab_tail.py` provides:

- a literal finite-cutoff Haar coefficient for each nine-word Wilson
  insertion;
- an all-label Cauchy modulus for that coefficient;
- a normalized local conditional-density tail;
- a trace-class Gram tail after the Peter--Weyl feature lift.

This is enough to define the complete local reflected Gram.  It is not yet a
composable source-indexed kernel

\[
  (b,A)\longmapsto\Phi_{a,k}(b,A)
\]

with compatible source and target carriers at consecutive scales.  In
particular, the current code does not provide:

1. a corridor cover of the corrected-slab independent Haar variables;
2. an identity or CP inequality placing the interacting block above the
   product corridor kernel;
3. the shared-intertwiner transport needed when corridors overlap;
4. a coupling update \(s_k\mapsto s_{k+1}\) tied to physical spacing;
5. a composable grouped map over \(\lceil L/a\rceil\) steps.

The existing fixed-coupling minorization instead bounds every one of the 72
plaquette factors by a global Jacobi floor and ceiling.  Its mass collapses
as \(s\to1\).  It cannot supply \((\mathrm{CH})_L\) or the corridor
factorization.

### Exact corrected-slab corridor geometry

The nine coarse loops do have canonical fine filling disks:

- six spatial \(2\times2\) disks, each containing four plaquettes;
- three temporal \(2\times1\) disks, each containing two plaquettes.

The executable incidence audit proves:

| field | exact result |
|---|---:|
| corridors | \(9\) |
| selected faces | \(30\) |
| face-set overlaps | \(0\) |
| disk-internal links | \(27\) |
| internal-link overlaps between disks | \(0\) |
| disks whose boundary equals the named coarse path | \(9\) |
| off-corridor plaquettes incident at each internal link | exactly \(2\) |

Thus the proposed corridor family is not a detached geometry: it is the
canonical filling of every BF3.2 coarse Wilson loop.  But the audit also
proves why the four-plaquette semigroup identity cannot simply be multiplied
nine times inside the full 72-face integrand.  Every one of the 27
disk-internal links is used by two transverse plaquettes among the remaining
42 faces.  The Haar variables needed for the corridor convolution are
therefore coupled to the off-corridor activity.

Literal factorization is ruled out.  A successful proof must instead sum
the transverse fusion families and establish a CP-order domination, or find
a change of variables or conditional expectation that isolates the same
positive corridor component.

The transverse problem can nevertheless be reduced exactly.  Repeatedly
choose an off-corridor plaquette containing a free Haar link that occurs in
no selected disk and in no other remaining off-corridor factor.  Haar
normalization integrates that plaquette to one.  This constructive leaf
elimination removes 21 of the 42 transverse plaquettes.

The maximal residual for this rule has:

- 21 transverse plaquettes;
- free-link degree census
  \(((1,9),(2,9),(3,5))\);
- 18 corridor-protected links;
- one connected 15-face component and six one-face decorations.

Every remaining degree-one link is corridor-protected, so the reduction
cannot continue without acting on the heat corridors themselves.  The
load-bearing CP-order comparison has therefore been cut in half: it is a
specific 21-face transverse core, not an undifferentiated 42-face remainder.

### Complete cutoff-one fusion expansion of the residual

The 21-face residual has now also been expanded without the mod-two boundary
simplification.  Its connected component contains 15 faces, five trivalent
internal Haar links, and nine bivalent corridor-protected links.  The six
remaining faces are disjoint one-face decorations attached through nine
additional protected links.

At representation cutoff one, the connected core has 1024 internally
admissible binary face assignments.  Mod-two boundary data collapse these to
128 signatures with eight fillings each.  That collapse is not physically
adequate: whenever two fundamental strands reach a protected link, both the
singlet output \(0\) and triplet output \(2\) must be retained.  Keeping those
outputs gives the exact complete ledger:

| field | exact result |
|---|---:|
| connected-core boundary label profiles | \(4761\) |
| connected-core fusion paths | \(10673\) |
| profile multiplicities \(1,2,4,8\) | \(1505,2184,944,128\) |
| decoration boundary profiles | \(64\) |
| full 21-face boundary label profiles | \(304704\) |
| full 21-face fusion paths | \(683072\) |

Every admissible internal trivalent packet has one-dimensional invariant
space, so the first multiplicity is entirely in the distinct core fillings
and boundary fusion outputs.  The vacuum boundary profile alone has eight
fillings, at face counts \(0,6,10,12\) with multiplicities \(1,3,3,1\).

This is a cutoff-one fusion ledger, not yet the CP-order certificate.  It
refutes use of the 128-state parity boundary as the source of truth and pins
the next object: evaluate the coherent partially contracted Haar tensor on
these complete boundary sectors, then prove an all-label positive lower
bound with a cutoff modulus.  The executable certificate is
`transverse_cutoff_one_fusion_audit()` in
`computations/grouped_all_label_haar_refresh.py`.

This corrects the interpretation of the BF3.2 handoff:

> BF3.2 supplies the all-label local Gram and its cutoff modulus.  The
> source-indexed composable grouped kernel needed to test the physical
> refresh packet is still a BF4 constructor, not already-existing data.

## 7. Exact theorem that would close BF4-C3/C4

Let \(\mathcal C_{a,L}\) be a product of \(r\) grouped heat corridors, let
\(\Pi\) be the deterministic coarse-holonomy/intertwiner pushforward, and
let \(\Phi_{a,L}\) be the actual normalized grouped corrected-slab map.

It is sufficient to construct

\[
 \Phi_{a,L}
 =
 \eta_{a,L}\,\Pi\mathcal C_{a,L}
 +(1-\eta_{a,L})\Theta_{a,L},
 \tag{PCD}_{a,L}
\]

where

- \(\Theta_{a,L}\) is completely positive and mass-preserving;
- \(\eta_{a,L}\ge\eta_L>0\);
- the corridor cover retains every shared coarse intertwiner;
- \(s(a)^{\lceil L/a\rceil}\le\tfrac12\).

Then

\[
 \Phi_{a,L}
 =
 \eta_{a,L}\varepsilon_0^r
   \Omega_{\Pi_*\lambda^{\otimes r}}
 +\text{positive residual},
\]

so the physical refresh mass satisfies

\[
 \boxed{\quad
 \varepsilon_{a,L}
 \ge
 \eta_L
 \left(\frac{1055}{2272}\right)^r
 >0.
 \quad}
\]

This is the desired spacing-, cutoff-, and volume-uniform BF4 witness.

The first open theorem is therefore no longer “find some positive packet.”
The packet and its all-label mass are explicit.  The first open theorem is:

> **Prove the corrected-slab CP-order corridor domination
> \((\mathrm{PCD})_{a,L}\), including a finite corridor cover and shared
> coarse-intertwiner transport.**

The geometry portion is now partly closed: the nine disks, their
boundaries, and their disjoint internal-link sets are pinned.  The open
portion is exactly the transverse-interaction/recoupling sum forced by the
two off-corridor incidences at every internal link.  Normalized Haar leaf
elimination reduces that sum to the pinned 21-face core above.

After that, prove the physical cumulative-heat condition
\((\mathrm{CH})_L\).

## 8. Executable artifacts

- `computations/grouped_all_label_haar_refresh.py`;
- `tests/test_grouped_all_label_haar_refresh.py`;
- `computations/all_label_whole_slab_tail.py`;
- `computations/constructive_refresh_contraction.py`;
- `lean/YMGap/Continuum/ConstructiveRefreshContraction.lean`.

The fail-closed status object is
`grouped_physical_packet_frontier()`.
