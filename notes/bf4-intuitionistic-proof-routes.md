# BF4: intuitionistic proof routes

Date: 2026-07-25  
Status: **constructive contraction algebra proved; physical BF4 witness open**

## 1. Result of the proof-design audit

BF4 does not intrinsically require a constructive version of the full
Birkhoff--Hopf theorem.  The theorem can be replaced by a stronger but much
more witness-bearing statement about the grouped physical block map.

Let \(\Phi\) be a positive mass-preserving block map, let \(R\) be an
explicit normalized positive reference, and define the reset map

\[
  \Omega_R(A)=\ell(A)R.
\]

The preferred constructive target is a literal decomposition

\[
  \boxed{\quad
  \Phi_{a,L}
  =
  \varepsilon_{a,L}\Omega_{R_{a,L}}
  +(1-\varepsilon_{a,L})\Psi_{a,L},
  \quad}
\]

where

- \(0<\varepsilon_{a,L}\le 1\) is explicit;
- \(\Psi_{a,L}\) is positive and mass-preserving on the same physical
  carrier;
- the equality is the equality of the actual grouped Haar-network map, not
  a surrogate;
- all data are uniform in the representation cutoff and ambient volume.

For normalized inputs \(A,B\), the reset portions cancel:

\[
 \Phi(A)-\Phi(B)
 =
 (1-\varepsilon)\bigl(\Psi(A)-\Psi(B)\bigr).
\]

Positivity and mass preservation make \(\Psi\) nonexpansive in the base
norm.  Therefore

\[
 \|\Phi(A)-\Phi(B)\|_{\mathrm{base}}
 \le
 (1-\varepsilon)\|A-B\|_{\mathrm{base}}.
\]

For finite probability kernels this is now proved over exact rationals in
`lean/YMGap/Continuum/ConstructiveRefreshContraction.lean`.  The proof uses
finite sums and explicit witnesses only.  It does not use logarithms,
suprema, eigenvectors, spectral decomposition, compactness, choice, or
excluded middle on arbitrary propositions.

For a square kernel,
`lean/YMGap/RG/ConstructiveRefreshStableDynamics.lean` also proves that the
finite probability simplex is invariant and exports the result as the
literal `UniformContractionCertificate` expected by the existing RG-I7
stable-dynamics interface.

This changes the logical shape of BF4:

> **The central missing object is a common physical refresh packet, not an
> abstract projective diameter.**

## 2. Relation to the current reference-order target

The present BF4 target centers normalized outputs at a reference \(R_a\):

\[
 E_A=\frac{\Phi(A)}{\ell(A)}-R_a,\qquad
 -\delta_aR_a\preceq E_A\preceq\delta_aR_a.
\]

Its lower half already gives

\[
 \Phi(A)\succeq (1-\delta_a)\ell(A)R_a.
\]

Set \(\varepsilon_a=1-\delta_a\).  If this inequality holds for every
positive input and \(\Phi\) is linear, the residual map

\[
 \Psi_a(A)
 =
 \frac{\Phi(A)-\varepsilon_a\ell(A)R_a}
      {1-\varepsilon_a}
\]

is positive and mass-preserving.  The constructive refresh theorem then
has rate

\[
 1-\varepsilon_a=\delta_a.
\]

Thus the one-sided lower minorization gives exactly the same rate as the
symmetric reference-order target \(\alpha=1-\delta\),
\(\beta=1+\delta\).  The upper Loewner bound is useful for Hilbert geometry
but is not required for the refresh/base-norm proof.

There is one operator-level qualification.  Pointwise positivity of the
residual is enough for the ordered base norm.  A **completely positive**
residual is preferable because BF4 must be stable under boundary ancillas,
tensoring, and coherent intertwiner transport.  The strongest physical
certificate should therefore be a CP-order decomposition of maps, not just
an output-by-output Loewner inequality.

## 3. Why the refresh should be proved after physical grouping

The current 72-plaquette Haar-reference minorization is exact but its
deficit is about \(10^{-216}\) already at \(s=1/2\), and becomes worse as
\(s\to1\).  That is not an accident.  A small-time heat kernel has a useful
spectral contraction of order \(1-ma\), while its global Haar minorization
can be exponentially smaller than any power of \(a\).  A microscopic
Doeblin argument generally cannot see the correct exponent.

The constructive route should therefore target the map already grouped
over a fixed physical distance:

\[
  \Phi_{a,L}
  =
  \Phi_{a,n_L-1}\circ\cdots\circ\Phi_{a,0}.
\]

The desired witness is

\[
  \varepsilon_{a,L}\ge\varepsilon_L>0
  \quad\text{for all sufficiently small }a,
\]

with one explicit rational \(\varepsilon_L\).  Then

\[
  q_L=1-\varepsilon_L<1
\]

is spacing-, cutoff-, and volume-uniform.  This is already in the exact
form consumed by
`lean/YMGap/RG/ScaleDependentGroupedContraction.lean`.

This direct grouped statement is more intuitionistic than first proving an
asymptotic formula \(q_a=1-ma+o(a)\): it asks for a finite witness
\((L,\varepsilon_L)\), and the proof checks a finite composition at every
spacing.  No logarithm is needed to establish geometric clustering.

## 4. Candidate physical constructions

### Route A — grouped common Haar/fusion packet

This is the preferred route.

1. Pick a fixed physical slab/corridor whose grouped map crosses every
   retained boundary cut signature.
2. Use exact Haar integration and heat-kernel convolution to integrate
   off-corridor plaquettes into the normalized reference rather than paying
   a worst-holonomy floor for all 72 plaquettes at every microscopic step.
3. Exhibit a complete family of fusion histories that lands in a common
   faithful packet \(R_{a,L}\).
4. Sum that family before expanding into signed \(F\)-channels.
5. Prove its total coefficient is at least an explicit
   \(\varepsilon_L>0\).
6. Define the residual by literal subtraction and prove positivity,
   normalization, reflection intertwining, and coherent \(P/Q\) transport.

The packet must mix the 32 cutoff-one rank-one components.  A packet
confined to one BF3.1 cut-signature block cannot work.

**Expected payoff.**  It proves BF4 with only one-sided order and feeds the
existing grouped-contraction and graded-Perron--Frobenius interfaces
directly.

**Main risk.**  A fixed low-spin packet may lose all mass as \(s\to1\).
The reference should therefore move with the heat distribution and retain
all labels; a vacuum-only packet is unlikely to have the required scale.

### Route B — a primitive fusion word plus a heat-relative tail

Find an explicit finite word of local recouplings/Haar integrations whose
kernel is positivity improving on a cutoff head.  Then split

\[
  \Phi=\Phi_{\le J(a)}+\Phi_{>J(a)}.
\]

The head supplies an exact common packet.  The BF3.2 heat-weighted coherent
tail supplies the error, but it must be upgraded from trace-smallness to a
**heat-relative** order estimate.  The cutoff \(J(a)\) is constructive data
with a modulus.

This route is useful if a single all-label packet is hard to see.  Its
danger is the already-proved fact that trace-smallness alone does not imply
relative-order smallness.

### Route C — located finite cross-ratio algebra

Keep the Birkhoff idea, but replace classical Hilbert-metric machinery by
finite rational witnesses:

- a finite source/target enumeration;
- strict positive entry witnesses;
- rational lower and upper likelihood-ratio bounds;
- decidable finite minima and maxima;
- the exact candidate
  \[
    q=(S-1)/(S+1).
  \]

`RationalCrossRatioDiameter.lean` already contains the certificate-shaped
cross-ratio half.  The remaining constructive theorem can be phrased as an
oscillation/Dobrushin inequality and proved by finite algebra, avoiding
\(\log\), \(\tanh\), and square roots.

For the all-label limit, the finite extrema must be replaced by supplied
located bounds with moduli.  One must not define an unlocated supremum and
then invoke compactness.

**Expected payoff.**  It can be sharper than a one-sided refresh constant.

**Main risk.**  It does not repair support holes or growing diameter; the
correct grouped physical kernel is still required first.

### Route D — constructive energy/coercivity inequality

If no useful grouped minorization exists, prove directly

\[
  \mathcal E_a(f,f)\ge m a\,\mathrm{Var}_a(f)
\]

or a fixed-\(L\) analogue on the physical fusion carrier.  This can be
intuitionistic if \(\mathcal E_a\), the variance, and \(m\) are explicit and
the inequality is proved by finite Haar/fusion identities plus a convergent
tail modulus.  No spectral theorem is needed: the coercive inequality is
itself the gap witness.

This route can see the linear small-\(a\) rate that microscopic global
minorization misses.

**Expected payoff.**  Correct scale and direct connection to the mass.

**Main risk.**  It gives up BF4's hoped-for “one diameter bound” simplicity
and reintroduces a substantial analytic estimate.

### Route E — explicit coupling of fusion histories

Construct, for every pair of boundary inputs, a common finite fusion-history
prefix of weight \(\varepsilon_L\), and use identical choices on that prefix.
The uncoupled residual histories carry the remaining mass.  Algebraically
this is Route A, but the witness is a pairing of histories rather than an
operator inequality.

This presentation may be the easiest executable search target: the exact
engine can enumerate candidate histories and certify their common weight.
The final theorem should then repackage the result as the map-level refresh
decomposition so that pair-dependent choices do not enter the proof.

## 5. Constructive obligations, in dependency order

### BF4-C1 — finite refresh algebra

**Closed.**

- finite pushforward defined over `Q'`;
- finite \(l^1\) distance defined over `Q'`;
- nonnegative row-stochastic residual proved nonexpansive;
- reference term proved to cancel for equal-mass inputs;
- exact contraction rate \(1-\varepsilon\) proved;
- \(0\le1-\varepsilon<1\) proved;
- load-bearing axiom print contains only the repository-accepted kernel
  infrastructure (`propext`, and `Quot.sound` through rational comparison).

Artifact:

- `lean/YMGap/Continuum/ConstructiveRefreshContraction.lean`;
- `lean/YMGap/RG/ConstructiveRefreshStableDynamics.lean`.

The finite search companion
`computations/constructive_refresh_contraction.py` computes the largest
entrywise common packet
\(\varepsilon=\sum_y\min_x K(x,y)\), reconstructs the exact residual, and
can census grouped powers.  Its regression suite includes exact support-hole,
rank-one-reset, and two-state grouped-contraction witnesses.  Applied to the
normalized cutoff-one raw local-face fusion kernel it returns
\(\varepsilon=0\) exactly: the support holes already rejected by BF3.3 also
reject the refresh route before physical grouping.

### BF4-C2 — noncommutative carrier lift

**Open.**

Define the ordered base norm on the BF2 trace-class carrier with
witness-bearing positive decompositions, and prove that a positive
mass-preserving residual is nonexpansive.  Prefer a completely positive
refresh decomposition so the theorem is stable under tensoring and
coherent boundary modules.

### BF4-C3 — exact physical grouped packet

**Open and load-bearing.**

Construct

\[
 \Phi_{a,L}
 =
 \varepsilon_{a,L}\Omega_{R_{a,L}}
 +(1-\varepsilon_{a,L})\Psi_{a,L}
\]

from the same all-label Haar-network map that exited BF3.2.  Prove all-label
positivity, mass preservation, reflection intertwining, cut-signature
mixing, and coherent \(P/Q\) compatibility.

**Corridor result (2026-07-25).**  The central all-label heat corridor is
now explicit.  Haar convolution gives \(K_s^{*m}=K_{s^m}\), and the complete
character tail proves
\[
 K_{s^m}(g)\ge\frac{1055}{2272}
 \qquad\text{whenever }s^m\le\frac12.
\]
This supplies a genuine all-label common Haar packet, with every
Peter--Weyl mode strictly present.  What remains open in C3 is the physical
promotion: pin a finite corrected-slab corridor cover and prove that the
actual interacting grouped map CP-dominates it with a coefficient bounded
away from zero.  BF3.2's current coefficientwise Cauchy Gram is not itself
the required composable source-indexed grouped kernel.

### BF4-C4 — spacing-uniform packet mass

**Open and load-bearing.**

Exhibit rational \(L>0\), \(\varepsilon_L>0\), and a spacing threshold such
that

\[
 \varepsilon_{a,L}\ge\varepsilon_L.
\]

This replaces the present catastrophic microscopic Haar floor by a grouped
heat-relative estimate.

For the corridor route the spacing obligation has the exact
logarithm-free form
\[
 s(a)^{\lceil L/a\rceil}\le\frac12.
\]
If the physical CP-domination coefficient is
\(\eta_{a,L}\ge\eta_L>0\) and the cover uses \(r\) independent corridors,
then
\[
 \varepsilon_{a,L}
 \ge
 \eta_L\left(\frac{1055}{2272}\right)^r.
\]
Thus the common packet no longer has to be discovered.  C4 must prove the
bare coupling/spacing inequality and the uniform CP-domination mass.  The
condition is not a free grouping convention: with \(\rho=s^3\), it implies
\[
 (1-\rho(a))/a\ge 7/(16L)
\]
for \(a\le L\).  Here \(\rho\) is the local bare heat-kernel Fourier
multiplier, not yet the separator of the interacting gauge-invariant transfer
operator.  The inequality may be derived from bare asymptotic freedom; it
becomes a physical gap statement only after the separate transfer
identification.  C4 must therefore derive the bare estimate on the actual
trajectory and must not silently promote it to the Clay gap.

### BF4-C5 — graded transport

**Open; shared with BF5.**

Prove that the coherent/branched sector contributes an actual base-norm
distortion bounded by \(C\kappa_a^{64}\), and that the grouped product of
the total rates is strictly subunit.  The algebraic consumer already exists
in `ScaleDependentGradedPerronFrobenius.lean`.

## 6. Recommended next experiment

Construct the open-index all-label Choi lift of the now-explicit heat packet
on the **smallest grouped corrected slab that mixes two distinct BF3.1 cut
signatures**.  Do not start from the cutoff-one truncation: its exact
ten-feature Schur symbol is indefinite at \(z=2s^3=3/2\), even though the
full heat kernel is positive.

For every candidate fusion-history family, record:

1. source boundary signature;
2. target reference packet;
3. exact heat coefficient;
4. exact Haar/fusion amplitude after summing the complete physical family;
5. whether the term survives at all representation cutoffs;
6. whether the same packet occurs for every source signature;
7. a heat-relative lower bound, not an absolute Haar floor.

Stop a candidate immediately if it fails cut-signature mixing or if its
common mass is a fixed low-spin probability vanishing at weak coupling.
Also stop any proposal that tries to add the cutoff-one family as an
independently CP summand; the exact negative direction \(e_8-e_9\) rules out
that promotion.  Candidate families must group the full label tower before
the CP-order comparison.
The corridor packet itself is already all-label and has the fixed mass
\(1055/2272\) once its grouped coordinate is at most \(1/2\).  The search
must now determine the finite corridor cover, its shared-intertwiner
transport, and the CP-domination coefficient \(\eta_{a,L}\).  The first
successful family becomes the constructor for BF4-C3; its uniform
\(\eta_L\), together with the cumulative-heat inequality, closes BF4-C4.

The executable finite screening interface is
`maximal_refresh_certificate` /
`grouped_refresh_certificates` in
`computations/constructive_refresh_contraction.py`.
The grouped all-label corridor certificate is in
`computations/grouped_all_label_haar_refresh.py`; see
`notes/bf4-grouped-all-label-haar-kernel.md`.

## 7. Literature coordinate

The classical source remains Garrett Birkhoff's
[“Extensions of Jentzsch's Theorem”](https://www.ams.org/journals/tran/1957-085-01/S0002-9947-1957-0087058-6/),
which formulates uniform positivity relative to a fixed order unit and uses
Hilbert's projective metric.  Dobrushin's 1956
[nonstationary Markov-chain work](https://www.mathnet.ru/eng/tvp4987)
is the historical coordinate for finite-kernel contraction coefficients.
The present route does not import their classical existence arguments: it
extracts the finite cancellation/nonexpansivity core as exact proof data.

## 8. Honest status

This investigation proves a new BF4 **engine theorem** and reduces the
intuitionistic physical gate to a concrete common-packet construction.  It
does not prove that the Yang--Mills grouped Haar block possesses such a
packet with spacing-uniform mass.  BF4, RG-I7--I9, and the mass-gap theorem
remain open.
