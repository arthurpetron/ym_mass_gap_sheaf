# Constructive Yang--Mills mass-gap formalization

> **Research status (2026-09-12): this repository does not prove the Clay
> Yang--Mills existence and mass-gap theorem.** It contains kernel-checked
> finite-lattice and strong-coupling results, explicit proof compilers, and an
> honest ledger of the bridges that remain open.

This project is a Mathlib-free Lean 4 formalization of a constructive route
from four-dimensional lattice gauge theory to continuum quantum Yang--Mills.
The active physical model is SU(2) BF4 lattice data. Existence statements are
required to carry witnesses and explicit moduli; numerical exploration is not
part of the trusted proof.

## Whole-project goal

The Clay target requires a non-trivial quantum Yang--Mills theory on
`R^4`, satisfying suitable QFT axioms, with an isolated vacuum and a uniform
mass gap `Delta > 0` for every compact simple gauge group. The repository is
currently pursuing SU(2) as the concrete non-abelian construction; a valid
all-group lift remains separate work.

```text
WHOLE-PROJECT GOAL / CLAY TARGET
Continuum 4D Yang--Mills exists + QFT axioms + isolated vacuum + Delta > 0
                                  |
                    EXPAND into causal obligations
                                  v
finite 4D SU(2) lattice measure and exact representation data       [PROVED]
  |                   FIX w=1/400 AND slab extent=1
  +-> OS Gram -> physical transfer -> exact vacuum component -----+
  |   and sector event contains the weight-one vacuum    [PROVED] |
  +-> complete-source conservation + target-weighted contraction -+
  |   internal bad mass <= (384/425) * sector mass       [PROVED] |
  `-> degree-13 Casimir majorant -> exact finite Fubini -----------+
      full partition <= 65/64, for every spin cutoff     [PROVED] |
                                                                 v
                     AND: all three inputs on the same ensemble
                                                                 |
       outside physical mass <= 1/64                             |
         -> escaping bad mass <= (6/425) * sector mass   [PROVED] <+
         -> successful mass >= (7/85) * sector mass      [PROVED]
         -> same normalized OS traffic >= 448/5525       [PROVED]
                                  |
                 + zero extension -> exact sector energy [PROVED]
                 + restricted move energy <= C * energy [PROVED]
                 -> positive sector-parity energy floor [PROVED]
                 original coverage route (not used below):
                 centered norm <= move energy / kappa     [OPEN]
                 (all-K exact cube/parity sector + positive
                  OS vacuum orbits: PROVED; weighted coverage: OPEN)
                 direct-mate probability floor alone: REFUTED
                 (explicit source family, each fixed 0<w<=1/2)
                 alternative direct tail branch, extent-one sector:
                   balanced Casimir drop + full boundary sum [PROVED]
                   -> Gaussian conditional self-return       [PROVED]
                   + injective six-label shell count          [PROVED]
                   -> actual high-label trace <= epsilon     [PROVED]
                   -> EVERY raw/centered tail form <= epsilon
                      times its own stationary norm          [PROVED]
                   -> raw tail rate 1/4, FIXED head B=1404    [PROVED]
                   -> centered norm <= original energy
                      + 3 * root-zero head norm               [PROVED]
                   AND fixed-head rooted energy control       [PROVED]
                   -> full centered N <= (1+3*C(w))*energy    [PROVED]
                                  v
  common strict centered form rate q(w)<1 for EVERY K>=K0(w)        [PROVED]
  (fixed extent one; explicit w-dependent rate/onset, 0<w<=1/2)
    -> cofinal sector-only certificate + same-object limit         [PROVED]
    -> completed marginal form gap and norm decay, SAME q(w)       [PROVED]
                                  | required together with:
  raw-entry saturation -> all-spin raw OS form -> completion         [PROVED]
    -> common physical normalization + signed-form cutoff identity [PROVED]
    -> raw/normalized reflected norm comparison, fixed w=1/400      [PROVED]
  finite marginal form D + actual conditional P, 0 <= P <= I
    -> E(a,b) = D(a,Pb) -> same P on E-completion + fixed unit vacuum [PROVED]
    -> exact centered macro moments via the comparison map          [PROVED]
                                  | required together with:
  source tails -> cutoff-removed marginal-norm conditional transfer  [PROVED]
    -> self-adjoint, 0 <= <Px,x> <= <x,x> on the completion          [PROVED]
    -> same P contracts E(x,y)=<x,Py>; unit vacuum and moments       [PROVED]
  complete E's root-sector image <-> normalized raw cube completion [PROVED]
    + marginal-sector completion -- E<=B --> this E completion      [PROVED]
    + every finite cube vector has a computed sector preimage      [PROVED]
    -> same physical pairing for EVERY completed sector vector     [PROVED]
    -> mapped sector action: positive, self-adjoint, E-contractive  [PROVED]
    + actual dense output Cauchy data + sharp difference contraction [PROVED]
    -> explicit map on ENTIRE raw/E completions, actual dense pin   [PROVED]
    + joint pairing limits -> full positive, rational-linear,
      self-adjoint contraction on BOTH entire completions          [PROVED]
    -> dense testing -> whole marginal-sector intertwining         [PROVED]
    -> same conditional-power moments, exact one-insertion shift   [PROVED]
    + exact sector indicator + unit-envelope prefixes + tail modulus [PROVED]
    -> completed stationary sector Omega, ||Omega||^2 >= 64/65      [PROVED]
    -> Omega-perp invariant under the SAME positive contraction    [PROVED]
    -> sector vacuum pairing = original stationary mean            [PROVED]
    + moving rational centering -> vectors in this complement      [PROVED]
    -> same-object connected conditional covariance, exact shift   [PROVED]
    + root-annihilating channel -> positive centered reflected norm [PROVED]
    + exact root correction + common denominator floor
      -> reflected centering error controlled by stationary mean   [PROVED]
    + Cauchy--Schwarz + fixed vacuum/root bounds + explicit tolerance [PROVED]
    -> centered-image density in the whole reflected complement     [PROVED]
       (rate from each supplied Cauchy representative; no choice)
    + same transfer contracts approximation errors + pairing limits [PROVED]
      -> common dense form bound IFF full complement bound, same q [PROVED]
         AND completed marginal positive-form Cauchy--Schwarz       [PROVED]
         -> ||P x||_M^2 <= q <P x,x>_M                              [PROVED]
         + exact pairing E(Rx,Ry)=<x,P y>_M + intertwining          [PROVED]
         -> SAME q bounds the dense reflected form                 [PROVED]
         -> <T x,x>_E <= q <x,x>_E on ENTIRE Omega-perp             [PROVED]
            (w=1/400, extent one, actual conditional operator)
    + two positive physical edges AND zero direct root/probe entry [PROVED]
      -> positive pairing through both original completion limits [PROVED]
      -> SAME completed transfer moves root; T is not identity     [PROVED]
      + stationarity AND completed-norm dissipation control
      -> d = T root - root lies in Omega-perp, with positive norm  [PROVED]
      -> <T d,d> + explicit positive floor <= <d,d>               [PROVED one vector]
    + original marginal Cauchy--Schwarz AND same-object pairing limits
      -> <x,test>_E^2 <= <T x,x>_E * ||test||_marginal^2           [PROVED all x]
      -> zero transfer response forces x=0                      [PROVED]
      + positive d/probe pairing AND d's strict deficit
      -> l*||d||^2 <= <T d,d> <= q*||d||^2, l>0, q<1             [PROVED one vector]
  identify that same action with geometric Euclidean time            [OPEN]
                                  v
                     same-object completed physical gap             [OPEN]
                                  | required together with:
  volume control + spacing control + QFT reconstruction              [OPEN]
  extension from SU(2) to every compact simple gauge group            [OPEN]
                                  |
                 CONTRACT only through checked bridges
                                  v
Continuum 4D Yang--Mills exists + QFT axioms + isolated vacuum + Delta > 0
WHOLE-PROJECT GOAL / CLAY TARGET
```

`PROVED` means kernel-checked at exactly the displayed scope. It does not mean
that downstream arrows have been proved. `PARTIAL` means concrete objects and
useful theorems exist but a required bridge is missing.

## Current frontier

The strict bound now reaches the **same completed reflected vacuum
complement**. Next: derive its fixed-space isolation and decay consequences
for that operator. The larger project still requires identification with
the exact YM action and geometric time, plus volume/spacing control and
continuum reconstruction. A gap for conditional dynamics is not by itself
a Yang--Mills mass gap.

**Latest result: the constructed rate survives both completions.**
`BF4PhysicalCubeCompletedMarginalGap.cofinalSectorGap` supplies the existing
sector-only limit interface on the explicit schedule `max(request,K0(w))`.
For every fixed `0<w<=1/2`, the resulting completed marginal form gap and
conditional-iterate norm decay use the original `q(w)`.

At `w=1/400`, extent one, positivity gives
`||P x||_M^2 <= q(w) <P x,x>_M`. The exact comparison identities identify
these quantities with the reflected transfer form and reflected norm.
`BF4PhysicalCubeCompletedReflectedGap.completed_reflected_form_bound`
therefore proves

```text
<T x,x>_E <= q <x,x>_E,   0 < q < 1,
for EVERY x in the completed reflected vacuum complement.
```

There is no supplied gap, vector-dependent prefactor, or rate loss. The
argument uses the actual vacuum sector, never the reducible full carrier;
it does not pretend the marginal and reflected norms are equal.
See [`BF4PhysicalCubeCompletedMarginalGap.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCompletedMarginalGap.lean)
and [`BF4PhysicalCubeCompletedReflectedGap.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCompletedReflectedGap.lean).
Both focused monitored checks passed all 13 printed axiom gates within
`{propext, Quot.sound}`. No new analytic premise or proof hole was added;
the full build/audit/guard was not run.

**Input: a constructed cutoff-uniform strict centered form bound.**
At extent one, for every fixed `0<w<=1/2`, Lean constructs a rational
`q(w)` and an explicit onset `K0(w)` such that

```text
0 < q(w) < 1
|P_K(f)| <= q(w) * N_K(f)
    for EVERY K >= K0(w) and EVERY stationary-mean-zero f.
```

`P_K` is the original physical matrix quadratic and `N_K` its original
stationary squared norm. For the fixed head B=1404, the existing persistent
edge floor F(w) and loop-free path scale S(w) give the computed constant
`C(w)=S(w)/F(w)`. The new proof controls the head by the original full
energy; summing costs only the stationary mass <=1. The previous tail
absorption then gives `N_K(f)<=(1+3*C(w))*E_K(f)`, and exact rational
algebra produces `q(w)=(1+6*C(w))/(2+6*C(w))`.

The rate and onset **depend on w**. This is not a coupling-, volume-, or
lattice-spacing-uniform physical gap. It supplies the completed result
above. Exact action/geometric time, vacuum uniqueness in the completed
theory, thermodynamic/continuum passage and Clay remain open.
See [`BF4PhysicalCubeAnchoredHeadBound.lean`](lean/YMGap/Continuum/BF4PhysicalCubeAnchoredHeadBound.lean)
and [`BF4PhysicalCubeCutoffUniformGap.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCutoffUniformGap.lean).
Both focused monitored checks passed all 20 printed axiom gates. The exact
untrusted path/algebra pilot passed 1,089 rooted bounds and four rate identities;
no numerical BF4 spectral oracle was used.

**Input: a fixed-head, root-anchored energy inequality.**
At extent one, for every `0<w<=1/2`, every spin cutoff `K>=1404`, and
every coefficient `f` of zero stationary mean, Lean proves

```text
N_K(f) <= E_K(f) + 3 * N_K(head_1404(f - f(vacuum)))
```

Here `N_K` is the original stationary squared norm and `E_K` is the
original directed physical Dirichlet energy, exactly twice `N_K-P_K`.
The proof establishes an **uncentered** tail rate `1/4`, absorbs the
mixed block by Gram positivity, and subtracts the root value without
changing the energy. Neither unit sector mass nor a strict head rate is
assumed. The head cutoff stays fixed while K grows.

The previously missing fixed-head constant is now supplied by the result
above. This absorption theorem alone does not supply it. See
[`BF4PhysicalCubeTailAbsorption.lean`](lean/YMGap/Continuum/BF4PhysicalCubeTailAbsorption.lean).
The focused monitored Lean check passed all 12 printed axiom gates;
the exact untrusted algebra pilot passed 29,141 positive-block checks.

**Input: the actual centered new-tail form is uniformly small.**
For any positive rational epsilon, take the explicit old cutoff
`B=1400+epsilon.den`. At extent one, for every `0<w<=1/2` and every later
cutoff K>=B, Lean proves

```text
exactCenteredNewTailTrace(B,K) <= epsilon
centeredGram_K(tail,tail) <= epsilon * stationaryNormSquared_K(tail)
```

The second bound holds for **every** literal new-tail coefficient vector,
not just a probe. The proof injects each radius-M shell into `(M+1)^6`
six-label codes and partitions the original conditional diagonal sum
exactly by radius. Genuinely new indices have radius greater than B,
so the Gaussian radial estimate below bounds the existing old/new-block
trace. Its centered stationary subtraction only decreases that trace.

This discharges the trace input of the existing head--tail compiler.
That earlier compiler still gives rate `q+epsilon` from a sufficient
centered head rate q. The newer anchored route above now proves a strict
full rate without needing that comparison.
Exact action/geometric time, vacuum uniqueness and
volume/spacing/continuum passage also remain open. See
[`BF4PhysicalCubeHighLabelTrace.lean`](lean/YMGap/Continuum/BF4PhysicalCubeHighLabelTrace.lean)
and [`BF4PhysicalCubeNewTailTraceBound.lean`](lean/YMGap/Continuum/BF4PhysicalCubeNewTailTraceBound.lean).
Both focused monitored checks passed, all 18 gates within
`{propext, Quot.sound}`; no new sorry or full-tree audit.

**Input: Gaussian suppression of actual high-label self-return.**
At extent one, every member of the original vacuum sector whose largest
cube label is M>=1400 satisfies, for every admitting cutoff and `0<w<=1/2`,

```text
P_K(source,source) <= 4096*(M+1)^6*w^floor(M^2/72)
```

The theorem concerns the existing `centralPhysicalConditionalKernel`;
cube support and parity are derived from canonical sector membership.
The proof combines the complete boundary comparison below with an exact
six-dimensional heat factorization and the quadratic Casimir decrease.

The degree-12 radial envelope
`R_w(M)=4096*(M+1)^12*w^floor(M^2/72)` also has a proved successor ratio at
most 1/2 beyond 1400. Every finite tail starting at N>=1400 is at most
`2*R_w(N)`. The explicit threshold `N(epsilon)=1401+epsilon.den` makes
every such tail at most epsilon, uniformly for `0<=w<=1/2`.
The six-label counting/trace connection is now proved above. Sufficient
head control remains open; scalar summability or a small tail alone is not
an all-vector spectral gap. See
[`BF4PhysicalCubeGaussianReturn.lean`](lean/YMGap/Continuum/BF4PhysicalCubeGaussianReturn.lean).
All 21 gates passed in its focused monitored check; the reused heat-product
module was also checked. No new sorry or full-tree audit.

**Input: full boundary summation and an actual diagonal/row
comparison.** At extent one, for every representation cutoff and explicitly
for `0 <= w <= 1/2`, Lean proves

```text
boundaryOverlap(source,target) <= 4096 * boundaryHeat(difference(source))
```

The proof factors an upper estimate over the original 24-coordinate
enumeration: twelve active heat tails each cost at most 2, and twelve
inactive labels are forced zero. Combining this with the balanced physical
move below gives, for every bounded common-parity cube source and K>=2,

```text
H(balanced(source)) * P_K(source,source) <= 4096 * H(source)
```

Here H is the actual half-state heat product, and P_K is the original
normalized reflected joint divided by its own stationary marginal; the
common partition cancels exactly. This is not a replacement dynamics or a
state-uniform transition floor. The Gaussian return bound and radial
summability are now proved above; the actual trace connection and sufficient
centered head--tail control or weighted norm coverage remain open. Neither an all-vector
strict rate nor a geometric-time identification follows yet. See
[`BF4PhysicalCubeBoundarySumBound.lean`](lean/YMGap/Continuum/BF4PhysicalCubeBoundarySumBound.lean).
The focused monitored check passed all 13 axiom gates within
`{propext, Quot.sound}`. No full-tree audit was run.

**Input: an all-state balanced physical move with quadratic Casimir
descent.** For a cube-supported common-parity state, let M be its largest
label. On each cube face replace s by
`2*(floor(2*floor(s/2)/3)+ceil(M/12))`. This computed target preserves every
minimal source difference-boundary channel, belongs to the actual vacuum
component, fits every original cutoff `K>=2`, and has a proved positive
entry in the original physical kernel. Its excess radius above 11 contracts
by `5/6`. Writing C for the sum of the six `c4(s)=s*(s+2)` values
(four times the SU(2) Casimir), Lean proves

```text
72*C(target) + M^2 <= 72*C(source)                 when M >= 1400
864*C(target) <= 863*C(source)                    when M >= 1400
```

The proof uses a sum-of-squares reserve at a maximal label to pay the
rounding and common offset. These are **label-energy rates, not operator
or mass-gap rates**. The boundary-sum and diagonal/row comparison is now
proved above; the resulting weighted norm or centered head--tail estimates
remain open. See
[`BF4PhysicalCubeBalancedDescent.lean`](lean/YMGap/Continuum/BF4PhysicalCubeBalancedDescent.lean)
and [`BF4PhysicalCubeBalancedCasimir.lean`](lean/YMGap/Continuum/BF4PhysicalCubeBalancedCasimir.lean).
Both modules passed focused monitored checks; all 46 printed axiom gates
are within `{propext, Quot.sound}`. No full-tree audit was run.

**Retained route correction:** a **cutoff-uniform direct inward-mate transition
floor is impossible** at each fixed `0 < w <= 1/2`, including `w=1/400`.
In six-face coordinates, take

```text
source       (2k+14, 0, 0, 0, 0, 0)
inward mate  (2k+13, 1, 1, 1, 1, 1)
competitor   (2k+12, 2, 2, 2, 2, 2)
```

Both targets have the same complete boundary mask against the source.
Their SU(2) dimension/Casimir comparison gives, for every `K >= 2k+14`,
`P_K(source,mate) <= w^(4k+2)` for the **original normalized physical
conditional kernel**. The sources belong to the actual vacuum component;
an explicit cofinal tolerance modulus proves the no-floor theorem. See
[`BF4PhysicalCubeInwardMateCompetitor.lean`](lean/YMGap/Continuum/BF4PhysicalCubeInwardMateCompetitor.lean)
and [`BF4PhysicalCubeInwardMateNoUniformFloor.lean`](lean/YMGap/Continuum/BF4PhysicalCubeInwardMateNoUniformFloor.lean).
This does **not** refute a full-operator gap or the proved averaged traffic
bounds. The analytic frontier remains weighted norm coverage/Poincare,
without assuming a uniform probability for the single selected mate edge.
Both modules passed targeted monitored checks; all 28 printed axiom gates
are within `{propext, Quot.sound}`. No full-tree audit was run.

**Previous positive result:** the constructed excitation has a **two-sided strict
relative response** for the SAME completed physical transfer:

```text
l * ||d||_E^2 <= <T d,d>_E <= q * ||d||_E^2,  l > 0, q < 1
```

The new full-space estimate is
`<x,test>_E^2 <= <T x,x>_E * ||test||_marginal^2` for every completed
reflected vector x and every finite cube test. It uses the original marginal
norm on the right, not the weaker reflected norm. Dense physical
Cauchy--Schwarz and the same-object pairing limits prove it without a gap
assumption. Dense tests then show that zero response forces x=0, so the
completed transfer kills no nonzero vector. These are not bounds away from
zero uniformly over vectors, nor bounds away from the vacuum eigenvalue one.

For `d = T root - root`, let delta be the existing positive probe-pairing
floor, C the computed marginal squared-norm ceiling of that probe, U the
existing squared-norm ceiling for d, and eta its proved positive deficit.
The displayed rates are explicit rational data:
`l = delta^2/(C*U)` and `q = 1 - eta/U`. They are proved for **this one
excitation**, not for every centered vector. See
[`BF4PhysicalCubeMixedTestBound.lean`](lean/YMGap/Continuum/BF4PhysicalCubeMixedTestBound.lean)
and [`BF4PhysicalCubeExcitationResponse.lean`](lean/YMGap/Continuum/BF4PhysicalCubeExcitationResponse.lean).
All 25 printed axiom gates passed in targeted monitored checks; no full-tree
audit was run. Scope is fixed `w=1/400`, extent one. A common dense q<1,
a unit-normalized canonical geometric-time probe, vacuum uniqueness, and
volume/spacing/continuum control remain open.

**Completion bridge:** the **common dense form bound and the bound on the entire
completed reflected vacuum complement are equivalent, with exactly the same
rate `q`**. The dense side uses the original centered physical presentations;
the completed side is not restricted to the older marginal-sector image.
The proof passes both the norm and transfer pairings through the constructed
approximants, using explicit moduli and no choice of quotient representatives.
See `dense_form_bound_iff_completed` in
[`BF4PhysicalCubeDenseFormClosure.lean`](lean/YMGap/Continuum/BF4PhysicalCubeDenseFormClosure.lean),
with represented pairing continuity in
[`GNSRepresentedApproximation.lean`](lean/YMGap/Continuum/GNSRepresentedApproximation.lean).
All 17 printed axiom gates passed in targeted monitored checks; no full-tree
audit was run. Scope is fixed `w=1/400`, extent one. **No common `q < 1` is
constructed:** that dense analytic estimate, geometric-time identification,
and the volume/spacing/continuum passage remain open.

**Previous result:** a **strict, quantitatively nonzero excitation in the actual
completed vacuum complement**. Define `d = T root - root`; stationarity gives
`<Omega,d>_E = 0` exactly. If `delta = twoStepFloor` is the physical positive
pairing floor below, and `P,R` are computed squared-norm ceilings for the
fixed probe and root representatives, Lean proves

```text
alpha = delta^2 / P > 0
eta   = alpha^2 / (2R) > 0
alpha <= <d,d>_E <= 2R
<T d,d>_E + eta <= <d,d>_E
```

The short argument is quantitative Cauchy--Schwarz, self-adjointness and
`||T x - x||_E^2 <= 2 * (<x,x>_E - <T x,x>_E)` on the full completed
carrier. See
[`BF4PhysicalCubeDissipation.lean`](lean/YMGap/Continuum/BF4PhysicalCubeDissipation.lean)
and [`BF4PhysicalCubeStrictExcitation.lean`](lean/YMGap/Continuum/BF4PhysicalCubeStrictExcitation.lean).
All 31 printed axiom gates passed in targeted monitored checks; no full-tree
audit was run. Scope is still fixed `w=1/400`, extent one. This is **one
vector's strict deficit**, not a uniform relative bound for every vector,
a normalized positive-response probe for the canonical geometric-time root,
vacuum uniqueness, or a continuum gap.

**Physical input:** the **actual completed physical transfer is not the
identity**. A three-state argument witnesses the movement:

```text
single-face twice-spin-two probe -> fundamental cube -> root
           positive edge floors at every cutoff K >= 2
direct probe--root entry = 0, by incompatible SU(2) triangles

<root, probe>_E = 0
<T root, probe>_E >= twoStepFloor > 0
therefore T root != root
```

The positive floor is an explicit product of heat weights and the actual
normalization floor, at fixed `w=1/400` and extent one. The proof retains
one source term in the marginal pairing of the two conditional images,
with independent action and pairing cutoffs, and passes through both
existing completion limits. The exact same-object moment identity then
gives the displayed reflected pairing. No new dynamics is introduced.
See [`BF4PhysicalCubeTransferNonidentity.lean`](lean/YMGap/Continuum/BF4PhysicalCubeTransferNonidentity.lean),
with its physical inputs in
[`BF4PhysicalCubeThreeStatePath.lean`](lean/YMGap/Continuum/BF4PhysicalCubeThreeStatePath.lean)
and [`BF4PhysicalCubeTwoStepPositivePairing.lean`](lean/YMGap/Continuum/BF4PhysicalCubeTwoStepPositivePairing.lean).
All 42 printed axiom gates passed in targeted checks; no full-tree audit
was run. Nonidentity is not a strict vacuum-complement bound, uniqueness
of the stationary vacuum, or geometric-time identification.

**Connected density result:** the actual centered physical images now approximate every
represented vector in the **whole completed reflected vacuum complement**,
with an explicit rate. This is at fixed `w=1/400` and extent one. The target
need not come from the old marginal-sector image: its only vector property
is orthogonality to the constructed stationary sector vacuum.

The proof combines the centering estimate below with Cauchy--Schwarz. Let
`U` and `R` be computed norm ceilings for the fixed vacuum and root, and set
`K = 2 * (1 + U*R/(64/65)^2)`. For any finite approximant `p` to `x`:

```text
||centered(p) - x||_E^2 <= K * ||p - x||_E^2
input tolerance = epsilon / K
output rate     = supplied Cauchy modulus(input tolerance)
```

[`BF4PhysicalCubeCenteredDensity.centeredDensity`](lean/YMGap/Continuum/BF4PhysicalCubeCenteredDensity.lean)
returns the presentations, modulus and error proof as data. Each approximant
also has its existing explicit centered Cauchy representative. There is no
choice of representatives from arbitrary quotient points. The generic
[`ScaledGNSCompletionEstimates.lean`](lean/YMGap/Continuum/ScaledGNSCompletionEstimates.lean)
preserves the actual normalized pairing and squared-distance modulus.
Both modules passed targeted checks and all 39 printed axiom gates; no full
repository build/audit was run. This is density, not a strict spectral gap.

**Connected centering estimate:** centering has a proved, base-independent error bound in
the **actual reflected norm**. For any finite sector presentation `p`, let
`r` be the root cylinder, `C(p)` its existing limiting correction, and `Omega`
the constructed stationary sector vacuum. The new full-space pairing identity
gives

```text
<centered(p), y> = <p, y> - C(p) <r, y>     for every completed y
||centered(p) - p||^2 = C(p)^2 ||r||^2
(64/65)^2 ||centered(p) - p||^2 <= <Omega,p>^2 ||r||^2
```

The denominator is the same physical root weight for every presentation
base. Thus this estimate has no coefficient-count or growing-cutoff factor.
It remains at fixed `w=1/400` and extent one. See
[`BF4PhysicalCubeCenteringPairing.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCenteringPairing.lean)
and [`BF4PhysicalCubeCenteringControl.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCenteringControl.lean).
The new density witness above supplies the explicit approximation assembly.

**Connected nonzero-vector result:** an explicitly centered single-face spin-two observable
has positive norm in the **actual reflected completion**. Its difference
boundary has zero root amplitude but positive probe amplitude, so one term
of the physical Gram sum-of-squares supplies a lower bound unchanged by
every rational root correction. The existing centered Cauchy sequence
passes that bound to the same completed vector. The witnessing rational is
`(64/65) * channelFloor(1/400) > 0`, where `channelFloor(w)` is an explicit
heat-weight product, not a coupling-uniform constant. This also proves
positivity of its connected conditional covariance at shifted index one
(reflected index zero). See
[`BF4PhysicalCubeSeparatedChannel.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSeparatedChannel.lean)
and [`BF4PhysicalCubeCenteredPositiveNorm.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCenteredPositiveNorm.lean).
A positive norm is not a strict transfer bound or a nonidentity theorem.

**Connected centering result:** the constructed sector vacuum's pairing equals the
original physical stationary mean on the **entire completed marginal
sector**. This identifies the existing moving rationally centered cylinders
with vectors in the new reflected vacuum complement. Their correlators are
proved equal to literal connected covariances under the original physical
law, using the same observable and conditional action, with the exact
one-insertion shift. See
[`BF4PhysicalCubeSectorCenteredRealization.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorCenteredRealization.lean).
This uses a rational head correction, not orthogonal projection along the
sector vacuum. Density now has the representative-supplied witness above;
the positive reflected norm is a separate physical-channel argument, not an
inference from a marginal lower bound.

**Connected vacuum result:** a stationary vector in the actual completed cube sector
is now constructed, with squared norm at least `64/65`. This is at fixed
`w=1/400` and extent one, not uniformly in the coupling. Finite component
indicators are zero/one observables with a common envelope; the original
physical tail modulus makes their prefixes Cauchy. Their global image is
exactly the cutoff-independent sector event, and finite stationarity passes
to the same completed transfer. The positive zero-labelled contribution and
partition ceiling supply the explicit norm floor. Self-adjointness then
makes this vector's orthogonal complement invariant, with the same positive
contractive operator. See
[`BF4PhysicalCubeSectorVacuum.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorVacuum.lean)
and [`BF4PhysicalCubeSectorVacuumNorm.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorVacuumNorm.lean).
This stationary vector is neither asserted to have unit norm nor proved to
be the unique fixed direction; a norm floor is not a spectral gap.

**Connected transfer result:** the actual transfer is proved positive, self-adjoint,
rational-linear and contractive on the **entire raw and reflected cube
completions**, at fixed `w=1/400` and extent one. Joint continuity of the
pairing passes the dense squared-distance bound to all vectors with constant
exactly `1`, without a normalization loss. Nondegeneracy and self-adjointness
give the vector-level linearity laws.

The same full-space map now **intertwines the entire existing completed
marginal sector**. The proof tests against dense cube vectors and moves the
transfer across the pairing; no new recoding producer or analytic premise is
assumed. All its natural-power moments on sector images equal the original
physical conditional moments, with the exact extra insertion from the
reflected form. See
[`BF4PhysicalCubeCompletedTransferLaws.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCompletedTransferLaws.lean).

**Boundary of this earlier transfer construction:** constant `1` gives
nonexpansiveness, not a strict gap. The head/tail estimate and same-rate
completion theorem reported above now supply strictness on the reflected
vacuum complement. The nonzero root cylinder is not the stationary sector
event; its movement under the transfer is proved above. Identifying
conditional iterations with geometric Euclidean time and controlling
volume and spacing limits remain open. A Cauchy diagonal modulus is not
a physical decay rate.

**Connected completed-pairing result:** the comparison preserves the actual physical pairing
for **every vector in the completed marginal sector**, not only finite
presentations. The proof slows the existing shared sampler to pay the finite
cube admission cutoff and normalization modulus. Its admissibility is
preserved, so it still constructs the same physical conditional operator.
The two aligned finite forms are eventually equal and have the constructed
completed pairings as limits.

Consequently the mapped sector action is positive, self-adjoint and
E-contractive; its iteration moments equal the original physical moments
with exactly one extra operator insertion. See
[`BF4PhysicalCubeSectorCompletedPairing.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorCompletedPairing.lean).
That earlier `mappedTransfer` has the completed marginal sector as its domain;
the new `cubeTransfer` above acts on the whole reflected completion. Its full
rational-linear operator laws and marginal-sector intertwining are now proved,
as is the positive-norm stationary sector vector above. Geometric time and
a strict gap remain open. The result is at fixed `w=1/400`
and extent one; no continuum or coupling-uniform claim follows.

**Connected comparison result:** the existing completed marginal root sector maps to
the reflected cube completion at `w=1/400`, extent one. The map preserves
each finite presentation's literal observable and contracts squared distance
by the proved `E <= B` estimate; its representative Cauchy modulus is unchanged.
Conversely, every finite signed cube vector has a computed marginal-sector
preimage. A common spin cutoff, faithful state-code lookup and finite summation
produce it, including negative coefficients and repeated states. The preimage
has the same observable values on every state, and its reflected image is
exactly the original cube vector. See
[`BF4PhysicalCubeSectorComparison.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorComparison.lean)
and [`BF4PhysicalCubeSectorDensePreimage.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorDensePreimage.lean).

The physical pairing pin now holds on the whole completed source as described
above. The completed transfer map with actual dense agreement and whole-source
intertwining are now proved. A dense preimage is not an inverse between
these two completed spaces.

**Connected completion result:** the literal cube-cylinder image has its reflected-norm
completion at the fixed anchor `w=1/400` and extent one. Two constructed maps
are inverses between this completion and the existing raw cube completion.
They keep the same finite-span sequences; the forward Cauchy modulus is
unchanged and the inverse uses the supplied modulus at `(64/65)*epsilon`.
The full completed pairing is proved to be the limit of the same dense
physical reflected pairings. See
[`BF4PhysicalCubeReflectedCompletion.lean`](lean/YMGap/Continuum/BF4PhysicalCubeReflectedCompletion.lean).

An elementary two-triangle argument also removes an unnecessary obstruction:
the two existing Cauchy moduli compute a null modulus directly, without choice.
The older claim that the legacy completion could not support this inverse
has been corrected.

**Connected dense realization:** the all-spin cube form is identified with the actual
completed physical pairing on its literal observable image. For arbitrary
finite signed lists `u,v`, the map `J` uses the existing exact state cylinders,
and the kernel-checked equality is
`E(Ju,Jv) = lambda * rawCubeForm(u,v)`.
At the fixed anchor `w=1/400`, its squared norm lies between `64/65` and `1`
times the raw reflected squared norm. The map neither creates nor removes
zero-norm vectors for these two reflected forms. See
[`BF4PhysicalCubeCompletedReflectedRealization.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCompletedReflectedRealization.lean).

**Connected operator result:** after the spin cutoff is removed, the actual conditional
operator `P` is self-adjoint and satisfies `0 <= <Px,x> <= <x,x>` on every
vector of the existing marginal-norm completion. The proof aligns both
insertions at the same finite cutoff using the existing adaptive sampler.

The constructive-real cubic identity now proves that this **same `P`** is
positive, self-adjoint and contractive for `E(x,y)=<x,Py>`. The same stationary
vacuum has E-norm one; its pairings, and the exact one-insertion-shifted
moments, are preserved. These are unconditional fixed-nome, finite-volume
results for `0<w<1`, using the constructed source-tail moduli. See
[`BF4PhysicalCutoffReflectedFormLaws.lean`](lean/YMGap/Continuum/BF4PhysicalCutoffReflectedFormLaws.lean).

The new completed root-sector map agrees with the conditional operator on
dense inputs; full intertwining remains open, as do geometric time and a strict gap. The construction
does not assume marginal completeness implies E-completeness; its scope is
the explicit-representative Cauchy quotient and the existing raw completion's
representative-family completeness.
No identification of the entire reducible carrier with the cube sector is
asserted; the vacuum-labelled root cylinder is not the constant stationary vacuum.

**Connected normalization result:** the all-spin raw cube form has its actual physical
cutoff-limit normalization. A single constructed `CReal` factor `lambda`
satisfies `normalized kernel = lambda * raw kernel`; its approximations are
exactly the reciprocals of the original finite partitions. The same identity
holds for every finite signed term list, including repeated states, after a
computed common cutoff. All limit constructions carry explicit moduli.

At the fixed anchor `w=1/400` and extent one, the checked partition ceiling
gives `64/65 <= lambda <= 1`, hence the corresponding two-sided comparison
of raw and normalized reflected squared norms. This is not a strict transfer
bound and is not a comparison with the marginal norm. See
[`BF4PhysicalCubeNormalizedKernelLimit.lean`](lean/YMGap/Continuum/BF4PhysicalCubeNormalizedKernelLimit.lean).

**Connected finite-transfer result:** the actual finite BF4 conditional operator acts on the
completion of its own reflected joint form, with a unit fixed stationary
vacuum. The proof uses the elementary identity
`P - P^3 = (I-P)P(I-P) + 2 P(I-P)P`: a positive contraction for the marginal
form `D` also contracts `E(a,b) = D(a,Pb)`. The latter is exactly the original
partition-normalized OS joint form; cancellation of the positive partition
also proves contraction of the full raw OS quadratic.

The canonical comparison `J` keeps the same Cauchy representatives and moduli,
decreases norms, intertwines the two completed actions, and preserves vacuum
orthogonality. Its exact moment identity is
`<Jx, P_E^n Jy>_E = <x, P_D^(n+1) y>_D`. This holds at each finite cutoff;
it neither asserts an inverse for `J` nor identifies macro iterations with
geometric time. See
[`BF4PhysicalJointFormTransfer.lean`](lean/YMGap/Continuum/BF4PhysicalJointFormTransfer.lean).

**Connected all-spin result:** the cube-sector raw reflected form has a
constructive GNS completion. Its states are exactly the union of the finite
canonical vacuum components for positive `w`; each state has a computed
admission cutoff. Explicit finite lists retain arbitrary signed rational
coefficients and repeated states. Their complete form is the original physical
boundary Gram at a computed common cutoff, not an assumed positive model.

The completed basis inner products equal the same raw physical kernel entries
at every cutoff beyond their saturation threshold. The vacuum-labelled root
has squared norm at least one and remains nonzero after completion. Finite
approximations and diagonal-limit representatives carry explicit moduli.
Completeness uses representative families with a supplied outer Cauchy modulus;
it does not select representatives from arbitrary quotient-valued sequences.
See [`BF4PhysicalCubeCompletion.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCompletion.lean).

The kernel underlying this construction, at slab extent one, has an exact
heat-weight/Boolean-overlap formula. For each half, its 48 production
links reduce to twelve SU(2) triangle tests and twelve boundary-zero tests;
the fixed part contributes eight corner triangles. The original weights and
boundary enumeration are retained, with no auxiliary multiplicity left.

If both endpoint label bounds are `R`, the raw kernel entry stops changing
exactly at every cutoff `K >= 2R`. A computed cutoff gives each pair an explicit
stable rational entry. Every finite quadratic form of this single stable
kernel is realized by the original physical OS Gram at a computed common
cutoff and is nonnegative for `w >= 0`.

The repository already constructs a cutoff-removed conditional transfer on
the **marginal-norm completion**, using explicit stationary-source-tail data;
see
[`BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer.lean`](lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer.lean).
It fixes that completion's stationary vacuum and preserves vacuum orthogonality.
The remaining operator bridge is to the **reflected cube completion** above,
not a missing conditional-transfer construction everywhere. The common
normalization identifies forms, and the new one-step laws control the existing
conditional action in E. They do not yet identify the two reflected carriers
or geometric time. A transfer-fixed vacuum on the raw cube completion,
a uniform strict gap,
thermodynamic/spacing limits and continuum reconstruction remain open. The
nonzero raw vacuum-labelled root alone does not prove vacuum isolation.

**Exact sector:** at slab extent one, every positive rational weight parameter
`w` and every spin cutoff `K >= 1`, the canonical vacuum sector is **exactly**
the bounded six-face cube labellings with common parity. The constructive
inward-mate orbit stays in that sector and reaches vacuum within `K + 1`
genuine positive OS moves.

The key construction puts `|a-b|` on the boundary face between cube labels
`a` and `b`. All source, mate and fixed-link multiplicities are exactly one;
the complete production summand becomes an explicit positive heat-coefficient
product below the original OS kernel. Together with the earlier singleton
pins and parity constraints, this proves both directions of the classification.
The sector sets are nested in `K` and unchanged by positive `w`; their weights
are not. Every mate-invariant observable on the sector is constant.

The edge weights depend explicitly on the state and `w`. Successful-source
traffic coverage and a cutoff-independent norm-to-move estimate remain open;
positive connectivity does not establish either. Sector-set nesting alone
also does not establish norm or operator compatibility across cutoffs; the
new raw-entry saturation theorem supplies a separate, strictly weaker result.

The preceding quantitative result remains: the normalized sector OS flow carries at
least `448/5525` total traffic. Exact source-block Fubini connects it to the
proved `7/85` raw sector-demand fraction. Together with the same-object sector
energy embedding, this gives the positive central-face-parity Dirichlet floor
`(448/5525)/(1 + globalInwardMateTransportCost)` on the exact vacuum component.
These estimates are uniform in spin cutoff `K >= 1` at fixed coupling `1/400`
and slab extent one.
The missing reverse estimate must control every centered sector norm by move
energy with a positive cutoff-independent floor.

The latest checked path is already on that actual OS object.  Every successful
six-face inward-mate source gives a supported two-edge path in the normalized
symmetric OS joint kernel.  Its selected source traffic has total mass at
least `41/425`; exact production-target fibers have congestion bounded by
`globalInwardMateTransportCost`; and all complete sources that forget to the
same first OS edge now inject into distinct literal boundary--intertwiner
summands of that edge.  Consequently their **aggregate** first-edge traffic is
at most the actual OS joint capacity, without a volume- or cutoff-cardinality
loss.  The second edge is now complete too: exact production-target classes
partition all selected source traffic, those classes partition again by their
actual second OS edge, and the resulting loads sum exactly to the original
traffic.  Each second-edge load is bounded by
`globalInwardMateTransportCost` times its OS capacity.

For one concrete observable the answer is now positive.  The parity of
central lower face zero is reversed by every selected inward mate, and because
the intermediate parity is also Boolean, exactly one of the two path edges
changes it.  Lean proves without a triangle-inequality loss that the two
selected parity-gradient energies sum to the selected traffic and are
therefore at least `41/425`.  The complete first-edge energy is now embedded
in the full physical OS Dirichlet form: exact first-edge fibers make the
parity gradient constant, their aggregate traffic is bounded by the matching
OS capacity, and distinct realized edges inject into the Cartesian half-state
square.  The second-edge energy is now embedded as well.  Its exact
production-target and OS-edge partitions contribute no loss; only the already
proved `globalInwardMateTransportCost` congestion factor remains.  The active
contraction is now complete: the explicit cutoff-independent positive floor

```text
(41/425) / (1 + globalInwardMateTransportCost)
```

is bounded by the full physical OS Dirichlet energy of central-face parity at
every cutoff `K >= 1`.  Lean now centers that same Boolean observable with its
exact stationary mean, proves that deleting zero-marginal rows and columns
does not change its Dirichlet energy, and applies the exact
Dirichlet/transfer identity.  The centered vector has a strictly positive
physical norm and obeys the explicit one-observable form estimate

```text
|<f,Tf>| <= q <f,f>,
q = 1 - (1/2) * (41/425) / (1 + globalInwardMateTransportCost),
0 <= q < 1.
```

This is a real cutoff-uniform strict channel of the actual finite physical
transfer, but it is not an all-vector Poincare inequality.  For arbitrary
observables, the selected source-to-target oscillation is at most
`2 * (1 + globalInwardMateTransportCost)` times the actual physical OS
Dirichlet energy.  The proposed Type-level full-carrier coverage input is now
proved impossible.  The XOR parity of central-cube faces `0` and `39` is
unchanged by every simultaneous six-face inward mate, but after exact
stationary centering it has strictly positive physical norm already at cutoff
one (vacuum value zero, proved transverse-face value one).  Its selected
endpoint energy is exactly zero.  Hence
`GlobalInwardMateUniformEndpointCoverage` has no inhabitant.

This obstruction cleanly repoints the proof.  The full positive-row carrier
is already known to be reducible at cutoff two.  Lean now proves the first
sector bridge: a positive raw OS edge cannot leave the exact finite vacuum
component, so whenever an inward-mate source endpoint is in that component,
its common hub and mate endpoint are there too.  A finite-support Boolean
classifier now filters the global source enumeration exactly to those paths;
the resulting Type-level list is duplicate-free and its membership theorem is
an iff, not an assumed selector.  Restricting the partition-normalized traffic
to this list preserves nonnegativity and both proved OS edge-capacity bounds,
including the second-edge congestion factor. The global `41/425` demand floor
does not follow merely by restriction; the new sector bound is `7/85`.
The branch decomposition has now been localized
at the right level: over the exact finite list of full physical fields whose
lower restriction is in the vacuum component, all-target mass plus
first-stretched mass equals the genuine BF4 physical mass exactly.  The
bad-target support argument now needs no equality of boundary labels: the raw
OS kernel sums over those labels, so each field supplies its own positive
boundary summand.  A target preserving the reflected upper state therefore
has a two-edge path from the source lower state.  A target preserving the
lower state stays in the sector directly.  The resulting exact decomposition is
`sector physical mass = successful mass + one-sided bad mass + two-sided bad mass`.
The two-sided residual changes both half-states and is contained in the older
boundary-or-upper crossing list; no strict positive mass reduction is claimed.
The weighted localization is now proved too: every nonnegative function of the
actual lowered target passes through the inverse-fiber and target/root/size
sums, preserving the factor `384/425`.  Taking the exact sector indicator
bounds all internal bad mass by `384/425` of sector physical mass.  Exact
branch conservation then proves
`(41/425) * sector mass <= successful mass + escaping bad mass`.
The escaping mass counts only sources in the sector whose lowered targets
leave it.  Every such source is proved two-sided; two-sided targets that
remain inside the sector are already covered by the contraction.
That escaping mass is now absorbed. The physical degree-thirteen face
majorant has successive ratio at most `2/15625` at the anchor, hence its
all-cutoff one-face sum is at most `15625/15623`. Exact finite Fubini and
the corrected slab's embedding in the 96-face ambient corner box give
`Z <= (15625/15623)^96 <= 65/64`. Since the weight-one vacuum lies in the
sector, outside physical mass is at most `1/64`. Applying the same weighted
contraction to the complementary target event gives
`escaping bad mass <= (6/425) * sector mass`. Subtracting this from the
previous demand bound proves
`successful mass >= (7/85) * sector mass > 0`.
This is a fixed-volume, fixed-coupling result, not uniformity in beta or
lattice spacing.

The sector Dirichlet embedding is now proved without recounting any fibers.
Zero extension of a sector observable adds no physical energy: the exact
component has no crossing OS kernel entries, and zero-marginal rows vanish.
The full half-state energy of this extension equals the already-defined
canonical indexed sector energy. On every restricted path, the extension
agrees with the original observable at all three vertices. Thus the first
edge, second edge, and endpoint estimates restrict with their original
factors `1`, `globalInwardMateTransportCost`, and
`2(1 + globalInwardMateTransportCost)`.

The exact normalization handoff is now proved as well. The sector test is
constant within each fixed-physical source block, so filtering commutes with
the complete-source Fubini sum. The existing production source weights agree
termwise with the raw source weights, yielding
`sector total traffic = successful sector mass / Z`. Thus the traffic is at
least `7/85` times the partition-normalized sector-event mass and, using
`sector mass >= 1` and `Z <= 65/64`, at least `448/5525` absolutely.
The Boolean parity identity says its two path-edge energies sum exactly to
this traffic, giving the sector Dirichlet floor
`(448/5525)/(1 + globalInwardMateTransportCost) > 0`, without a factor-two
triangle-inequality loss. No source list, physical kernel, or normalization
has been changed.

The geometric test now has a checked answer at cutoff two. In
[`BF4PhysicalVacuumSectorInwardMateOrbits.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateOrbits.lean),
`targetLower_eq_mate_sourceLower` identifies the literal source endpoint map;
`cubeInwardOrbit_even_eq_parityCore` proves its all-cutoff parity reduction;
`cubeInwardOrbit_rootTime_eq_zero` gives an explicit vacuum-hitting time for
cube-supported common-parity states. On the canonical cutoff-two sector at
coupling `1/2`, `canonicalCutoffTwo_mate_invariant_constant` proves every
potential-mate invariant is constant. This is a geometric statement, not a
new weighted OS estimate at the anchor coupling.

The all-cutoff physical support implication is now proved in
[`BF4PhysicalHalfCubeSupport.lean`](lean/YMGap/Continuum/BF4PhysicalHalfCubeSupport.lean)
and
[`BF4PhysicalVacuumSectorCubeContainment.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorCubeContainment.lean).
`sharedBoundaryOfKernelNeZero` returns a witnessing nonzero boundary as data.
`vacuumSector_cubeSupportedCommonParity` propagates the singleton pins and
relative parities along the actual canonical component.
`vacuumSector_inwardOrbit_reaches_zero` applies the existing orbit formula to
every sector state; `vacuumSector_cubePairParity_zero` eliminates the
pair-parity obstruction there for every cutoff. These are fixed-geometry
support statements for arbitrary nonnegative `w`, not uniform spectral bounds.

Next: establish physical support and successful-source traffic on the required
potential moves, then prove quantitative norm-to-move coverage at arbitrary
cutoff. The converse inclusion of the entire common-parity cube family in
the canonical sector is not proved here. The orbit formula alone does not
establish weighted coverage or congestion bounds.
The Poincare compiler's algebra remains useful: a correctly formulated
sector-local coverage theorem with floor `kappa > 0` produces the rate shape

```text
q_all = 4(1 + globalInwardMateTransportCost)
        / (4(1 + globalInwardMateTransportCost) + kappa) < 1
```

uniformly for every cutoff `K >= 1`.  No such sector-local uniform coverage
theorem is presently claimed.

See
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSFirstEdgeLoad.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSFirstEdgeLoad.lean).
The two-level second-edge partition is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSSecondEdgeLoad.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSSecondEdgeLoad.lean).
The exact Boolean observable identity is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityDemand.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityDemand.lean).
The checked first-edge Dirichlet embedding is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFirstEdgeEnergy.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFirstEdgeEnergy.lean).
The checked two-level second-edge embedding is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParitySecondEdgeEnergy.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParitySecondEdgeEnergy.lean).
The resulting explicit positive Dirichlet floor is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCoercivity.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCoercivity.lean).
The stationary centering, positive-norm certificate, exact transfer identity,
and strict one-observable form rate are in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFormGap.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFormGap.lean).
The arbitrary-observable two-edge estimate and exact all-vector coverage
frontier are in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSObservableEnergy.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSObservableEnergy.lean).
The conditional coverage-to-uniform-Poincare contraction is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSUniformPoincareCompiler.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSUniformPoincareCompiler.lean).
The exact XOR counterexample refuting its full-carrier coverage input is in
[`BF4PhysicalVacuumSectorInwardMateEndpointCoverageObstruction.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateEndpointCoverageObstruction.lean).
Positive raw-edge closure of the exact vacuum component and its application to
both inward-mate path edges are in
[`BF4PhysicalVacuumSectorInwardMateVacuumSectorRestriction.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateVacuumSectorRestriction.lean).
The exact finite-support classifier and duplicate-free sector-local source list
are in
[`BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier.lean).
The restricted partition-normalized traffic and its inherited first- and
second-edge capacity bounds are in
[`BF4PhysicalVacuumSectorInwardMateSectorLocalOSFlow.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorLocalOSFlow.lean).
The exact physical-field sector event and its localized good-plus-bad branch
conservation identity are in
[`BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation.lean).
The stronger support theorem, allowing arbitrary boundary changes whenever
either half-state is preserved, is in
[`BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.lean).
The exact three-way mass identity and residual containment are in
[`BF4PhysicalVacuumSectorInwardMateSectorLocalFirstStretchedSplit.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorLocalFirstStretchedSplit.lean).
The contraction against any nonnegative physical target function is in
[`BF4PhysicalVacuumSectorInwardMateTargetWeightedContraction.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateTargetWeightedContraction.lean).
Its sector specialization and exact escaping-mass demand bound are in
[`BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.lean).
The sharp physical partition ceiling is in
[`BF4PhysicalAnchorPartitionCeiling.lean`](lean/YMGap/Continuum/BF4PhysicalAnchorPartitionCeiling.lean).
The complementary-event comparison, leakage absorption, and positive `7/85`
sector demand are in
[`BF4PhysicalVacuumSectorInwardMateSectorDemand.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorDemand.lean).
The exact zero-extension identity for the canonical indexed sector is in
[`BF4PhysicalVacuumSectorZeroExtensionDirichlet.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorZeroExtensionDirichlet.lean).
The three unconditional restricted observable-energy comparisons are in
[`BF4PhysicalVacuumSectorInwardMateSectorObservableEnergy.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorObservableEnergy.lean).
The exact raw-to-normalized traffic identity, positive traffic floor, and
sector-parity Dirichlet consequence are in
[`BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.lean).

The current verified frontier joins a multiplicity-exact finite enumeration
of the root-first SU(2) cube source to a fixed-target contraction for every
certified first-stretched strand source.  Lean compiles the complete two-root
component union into three finite words:

- one connected rooted `Z^4` animal word in a carrier of size `625^n`;
- one exact physical strand-multiplicity word in a carrier of size `4^n`;
- one complete auxiliary-drop row word in a carrier of size at most `4096^n`.

At fixed root, peel size `n`, and lowered presented target, those words
reconstruct the source physical field and raw auxiliary assignment.  Thus any
explicit duplicate-free fixed-target source family has at most
`10240000^n` members.  Combining that injectivity with the exact per-source
anchor payment `anchorFaceCoefficient^n = (1/32000000)^n` gives the checked
finite-fiber estimate

```text
source fiber weight <= (8/25)^n * target weight.
```

See
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveEntropyCode.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveEntropyCode.lean),
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber.lean),
and
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveFiberWeight.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveFiberWeight.lean).

The classifier domain is now also a literal duplicate-free heterogeneous
product over the twelve cube incidences.  SU(2) fusion-path permutation
invariance proves that every root-first local fiber has the same cardinality
as its production-order fiber.  Hence the complete function-valued source
enumeration, and its injective target-or-first-stretched image, have exactly
`cubeInwardMateSourceBoundaryProduct K physical` members.

The target and first-stretched branches are now extracted as separate
duplicate-free lists whose lengths add back to the exact production
cube-boundary multiplicity.  The off-cube completion no longer starts from a
full background that would later discard twelve cube coordinates.  Instead,
it explicitly filters the complete slab-link list to the complement of the
twelve cube links, enumerates only those production fibers, and combines them
piecewise with the certified root-first cube data.  Cube and off-cube lookup
laws prove that every coordinate comes from exactly its intended source.

The remaining immediate bridge is to enumerate the Cartesian product of the
first-stretched list and this off-cube list injectively, partition the result
by common lowered target, root, and peel size, and sum those fibers.  The
Cartesian family itself is now explicit, duplicate-free, and has exact length

```text
first-stretched cube count * off-cube production multiplicity.
```

Every member canonically compiles to a complete presented source and its raw
auxiliary payload.  That compiler is now proved injective on the enumerated
family: equality on cube coordinates recovers the certified classifier input,
while equality off the cube reconstructs the complement assignment.  The
resulting physical/raw source list remains duplicate-free.  The active edge is
now to attach each member's deterministic lowered target, root, and peel size,
then partition this list into the fixed fibers consumed by the existing
`(8/25)^n` contraction theorem.  That attachment is now explicit and
duplicate-free: every entry retains its upstream source as an injective key,
projects the existing flat inverse record, and has peel size at least two.
Reapplying the older defensive cube override is also proved to leave the raw
complete source unchanged.  The live edge is the actual dependent target/root/
size partition and its fixed-fiber witness compiler.  The lossless decidable
partition key is now proved: it records the root, size, lowered physical word,
every local face-order word, and every local lowered-auxiliary word.  Equal
keys reconstruct literal equality of the lowered physical function and
heterogeneous equality of the dependent presented assignment.  The live edge
was therefore the realized representative fibers and their
`PresentedAdaptiveRemovalWitness` compiler.  That compiler is now checked as
well: each realized fiber is duplicate-free, has size at most
`10240000^n`, and its complete anchor weight is at most `(8/25)^n` times
the representative's lowered-target weight.  The live edge is the exact
representative-fiber Fubini sum followed by contraction of the resulting
distinct lowered-target weights against the pure mate product.  The exact
Fubini step is now checked and the full first-stretched source weight is
bounded by the strict-rate-weighted sum of its realized lowered targets.  The
live mathematical edge is the target-side congestion/injection that contracts
this distinct target sum against the pure mate product.
The theorem does **not** yet give a physical transfer minorization, a
posterior-variance fraction, an OS transfer gap, or a continuum result.

Earlier in the same causal chain, the Casimir/heat payment for an inward mate
at the physical nome `w = 1/2` established that a parity-uniform six-face cube
has a non-vacuum even source heat product at most `64` times its inward mate's
heat product, while an odd source is at most `1/4096` times its inward mate.

These are
`sixHeatProduct_evenInwardMate_le_sixtyFour` and
`sixHeatProduct_oddInwardMate_le_oneOver4096` in
[`BF4PhysicalVacuumSectorInwardMateHeatBound.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateHeatBound.lean).

The local SU(2) fusion debt is now also exact and kernel-checked. Lowering two
positive incident labels preserves their Clebsch--Gordan ladder except for
its stretched top channel. At the production link-multiplicity level, every
source path is bounded by the inward-mate path count plus one explicit
stretched-channel continuation. See
[`BF4PhysicalVacuumSectorInwardMateFusionSupport.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateFusionSupport.lean).

The local comparison now also transports across arbitrary physical incident
spin orderings, provided the two geometric permutation witnesses are supplied.
This is
`explicitValenceMultiplicity_physical_inwardMate_of_permutations` in
[`BF4PhysicalVacuumSectorInwardMateFusionReordering.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateFusionReordering.lean).
The generic finite-box incidence step is now closed as well:
`incidentPhysicalSpinsTwoFacePermutations` constructively moves any two
distinct incident plaquette IDs to the front of the source and mate words with
one shared residual word, and
`incidentPhysicalSpinsTwoFaceInwardMateLeAddStretched` immediately feeds
those witnesses into the production multiplicity inequality. See
[`BF4PhysicalVacuumSectorInwardMateIncidentOrder.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateIncidentOrder.lean).

The cube-specific geometry is now closed too.  The twelve-entry production
table is compiled into exact corrected-slab numerical incidence: at every
cube-boundary link the two recorded selected face IDs occur, are distinct, and
exhaust the selected six-face support.  Thus the global six-face mate restricts
to the proved local two-face mate, yielding the actual corrected-slab
multiplicity bound with one explicit stretched continuation.  See
[`BF4PhysicalVacuumSectorInwardMateCubeIncidence.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeIncidence.lean).

Those twelve local certificates now form one explicit global debt profile.
Lean proves that every link outside the cube boundary is unchanged and that
the boundary products obey
`product(source) <= product(mate + stretchedDebt)`.  See
[`BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile.lean).
This deliberately does not absorb the debts independently.

That finite product is now expanded exactly over Boolean words aligned with
the twelve attached links.  The all-target word is the pure mate product; all
nonempty stretched words sum to the named
`cubeInwardMateNonemptyStretchedRemainder`.  See
[`BF4PhysicalVacuumSectorInwardMateStretchedDebtExpansion.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateStretchedDebtExpansion.lean).

Every summand in that remainder now has a canonical constructive root.  Lean
computes the first stretched choice, proves its index lies in the attached
twelve-link incidence list, returns the corresponding geometric incidence as
data, and proves the root bit is `true`.  See
[`BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot.lean).

The natural-number remainder is no longer opaque cardinality either.  Each
stretched local factor is the length of a literal accepted SU(2) auxiliary
fiber; Boolean words choose target or stretched fibers link by link; and the
flattened finite carrier has length exactly
`cubeInwardMateNonemptyStretchedRemainder`.  See
[`BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber.lean).

The raw expansion has now been sharpened at its mathematical source.  The
SU(2) ladder proof shows that if either changed face label is zero, every
source channel survives and the additive debt is exactly zero.  The active
remainder therefore retains a stretched fiber only when both incident cube
faces are positive; it again has an exact finite-carrier cardinality theorem.
See
[`BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt.lean).

Every member of that active carrier now retains its assignment-membership
certificate, its first active position, the actual auxiliary labelling stored
there, and proofs that both incident physical face labels are positive.  Thus
the root required by the strand compiler is Type-level data rather than a
propositionally extracted witness.  See
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness.lean).
The two positive root faces are now also realized as distinct literal
slot-zero strand-copy vertices on their common recorded link; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies.lean).
For the stretched SU(2) vertex itself, the canonical resolution is now exact:
no strand joins the two input legs, while their strands occupy two disjoint
segments of the summed internal leg.  See
[`SU2StretchedTrivalentStrandContinuation.lean`](lean/YMGap/Continuum/SU2StretchedTrivalentStrandContinuation.lean).
The cube-root specialization now sends both literal face copies through those
canonical mates to distinct summed-channel ports and certifies the stored
auxiliary on the exact collapsed word; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation.lean).
The resulting collapsed auxiliary can now be lifted constructively back across
the stretched vertex.  For every source word of length at most six,
`stretchedFusionWitnessLift_mem` inserts the forced first channel, shifts the
remaining internal coordinates, and proves that the resulting auxiliary is
accepted on the ordered source word; see
[`SU2StretchedFusionWitnessLift.lean`](lean/YMGap/Continuum/SU2StretchedFusionWitnessLift.lean).
That compiler is now specialized to every active cube-root carrier:
`rootSourceAuxiliary_mem_orderedSourceSpins` provides the literal accepted
source auxiliary, and `rootProductionSpins_perm_orderedSourceSpins` retains
the exact permutation from the physical production order; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness.lean).
The corresponding root-first order of literal plaquette IDs is now retained
as data as well.  It is duplicate-free, permutes the production incidence
list, and maps exactly to the accepted ordered spin word; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder.lean).
The canonical ordered-chain termination and fixed-point-free terminal mate now
work for any such certified face presentation.  The generic compiler reindexes
every terminal to a literal incident plaquette and proves its mate lies on a
different face; see
[`CompactDualSlabOrderedLinkPhysicalStrandPairing.lean`](lean/YMGap/Continuum/CompactDualSlabOrderedLinkPhysicalStrandPairing.lean).
The one-element physical half-edge fiber now gives a constructive terminal at
any specified face position and strand slot.  At the active cube root this
produces two literal slot-zero terminals whose occurrences are exactly the two
previously named positive root copies; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals.lean).
Those selected terminals are now identified as full dependent ports at the
first canonical trivalent vertex, not merely by face ID.  The first channel is
proved to carry exactly the SU(2) stretched spin sum; its strand counts are
`ab = 0`, `bc = right`, and `ca = left`.  Consequently the two selected local
mates both land on the third leg but in distinct slots (`right` and `0`).  See
[`CanonicalLinkFirstVertexPorts.lean`](lean/YMGap/Continuum/CanonicalLinkFirstVertexPorts.lean)
and
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.lean).
The outgoing channel is now constructively classified as physical at valence
three or genuinely internal at valence four through six.  Both root strands
are fed to the exact stop-or-same-slot-advance compiler; their complete paths
to physical endpoints are retained as data, and those endpoints are proved
distinct.  See
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.lean).
Those endpoint terminals are now reindexed to the presentation-independent
global `(faceId, slot)` carrier.  Each root copy is proved to be the exact
source of a global strand edge, and the two retained path endpoints remain
distinct as literal global copies.  See
[`CompactDualSlabOrderedLinkGlobalFaceStrandEdge.lean`](lean/YMGap/Continuum/CompactDualSlabOrderedLinkGlobalFaceStrandEdge.lean)
and
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges.lean).
The global edge compiler now also accepts a different certified face order and
fusion witness at each link.  It enumerates every local physical terminal,
forgets every endpoint to the common global carrier, and concatenates the
result into one heterogeneous edge list.  Replacing the root entry of any
explicit complete background assignment by the actual root-first witness puts
both retained root edges literally in that list.  See
[`CompactDualSlabPresentedFusionGlobalFaceStrandEdges.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFusionGlobalFaceStrandEdges.lean).
An ordinary accepted source assignment now embeds canonically into this
presented interface.  More generally, a rooted component of any heterogeneous
presented graph pulls back to exact partner closure at each ordered link.  For
the active debt root, Lean constructs the two rooted components generated by
the left and right stretched-channel strands and takes their Boolean union.
That union contains both literal root copies and is closed across every edge,
without asserting that the two components coincide.  See
[`CompactDualSlabPresentedFaceStrandSeedComponent.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandSeedComponent.lean)
and
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.lean).
That ordered partner closure now compiles all the way through the existing
Kirchhoff strand-removal theorem.  At every link, the canonical edge drop is
proved equal to the global selected-copy count on the literal face occupying
that ordered position.  Consequently the two-root union constructs one common
lowered physical field and a complete accepted heterogeneous auxiliary
assignment over it; both distinct root-face labels decrease strictly.  See
[`CompactDualSlabPresentedFaceStrandComponentDrop.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentDrop.lean).

The source-side local decomposition is now witness-faithful rather than only
an inequality of natural-number dimensions.  For any root-first ordered word
through valence six, Lean reads the actual first SU(2) channel of an accepted
source witness.  If it survives the inward mate, the same auxiliary is
accepted in the mate fiber.  Otherwise Lean deletes the unique stretched
first vertex, retains the resulting accepted collapsed witness and both
positive-spin proofs, and proves that reinsertion recovers the source exactly.
The resulting `inwardMateFusionWitnessPartition` is injective.  See
[`SU2InwardMateFusionWitnessPartition.lean`](lean/YMGap/Continuum/SU2InwardMateFusionWitnessPartition.lean).

That abstract partition is now specialized to every literal cube-boundary
link.  One certified face order exposes the two incident cube faces first; its
residual literal faces are proved unchanged by the global six-face mate.  Lean
therefore maps the actual ordered source fiber injectively into either the
actual ordered mated fiber or an accepted collapsed stretched witness, and it
packages every surviving target as a presented mated-link witness.  Exact
recovery still returns the original auxiliary.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition.lean).

The dependent twelve-link product is now constructed too.  A complete source
is a function whose coordinate type is the accepted root-first fiber of that
literal incidence.  Lean classifies all coordinates, recovers all original
auxiliaries pointwise, proves the complete classifier injective, and packages
the original tuple as one accepted presented cube family.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition.lean).

That product now has a constructive global dichotomy.  A structural scan either
returns all twelve accepted mated witnesses or the first stretched incidence
with its actual positive two-face debt witness.  Forgetting the branch
reconstructs the complete classified assignment, so the source-to-branch map
remains injective.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched.lean).

The classifier's source-image invariant is now explicit rather than implicit
in its construction.  Every local output retains proof that its exact decoder
is accepted in the source fiber; the dependent product reconstructs a common
presented cube source.  The strengthened first-stretched branch keeps this
entire certified product and proves that its root output is exactly the stored
debt witness.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification.lean).

The certified cube family now extends to a complete slab presentation whenever
an explicit accepted full-slab background for the same physical field is
supplied.  A constructive finite lookup finds the unique recorded incidence
of each cube link, overwrites exactly those twelve entries with the certified
source witnesses, and leaves all off-cube entries unchanged.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation.lean).

At the certified first-stretched incidence, the retained positivity data now
constructs slot-zero terminals on the first two faces of that same root-first
witness.  Their terminal-pair edges have exactly the two literal cube-face
copies as sources, and both edges are proved members of the single completed
presented slab graph.  See
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges.lean).

Those two edges now seed a complete accepted peel.  Lean takes the Boolean
union of their constructive rooted components, proves it closed under the
actual partner at every independently presented link, and compiles the common
selection to a lowered physical field plus a complete accepted presented
assignment.  Both root-face labels decrease strictly; no connectivity claim
between the two roots is assumed.  See
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel.lean).

That accepted drop now has an exact physical serialization and pointwise
weight payment.  Every endpoint of the heterogeneous presented graph is
proved to lie on a displayed physical face; the selected-copy multiplicities
form a legal repeated-face peel with an exact physical left inverse; and the
certified two-root word has length at least two.  At the production anchor,
the actual completed source entry is bounded by one
`anchorFaceCoefficient` factor for every word letter.  See
[`CompactDualSlabPresentedFaceStrandComponentWeight.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentWeight.lean)
and
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight.lean).

The auxiliary drop is now serialized as well.  The lowered target retains each
certified face order, so the finite code pays no extra order coordinate.  Its
physical word plus link-local internal-drop words reconstruct the complete
source `(physical, raw auxiliary)` entry exactly, and every local word has
width at most three independently of cutoff.  See
[`CompactDualSlabPresentedFaceStrandComponentDropCode.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentDropCode.lean)
and
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedDropCode.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedDropCode.lean).

Zero internal-drop rows can now be erased and recovered exactly.  Every
retained row is charged injectively to a selected physical strand copy and one
of its four boundary links, so there are at most `4 * peelSize` nonzero rows.
More sharply, the complete volume-indexed row table inhabits a link-adaptive
Cartesian carrier: local conservation bounds every entry by the selected
physical mass incident on that link, all widths are at most three, and the
total incident mass is exactly `4 * peelSize`.  Consequently the auxiliary
carrier has size at most `4096^peelSize`, uniformly in slab volume and spin
cutoff.  See
[`CompactDualSlabPresentedFaceStrandComponentSparseDropCode.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentSparseDropCode.lean),
[`CompactDualSlabPresentedFaceStrandComponentAuxiliaryRowBound.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentAuxiliaryRowBound.lean),
and
[`CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction.lean).

The physical geometry, multiplicity, and auxiliary inverse are now joined in
one adaptive code.  Its fixed-target injectivity and weighted fiber contraction
are checked, including component overlap without double counting.  What is
still open is the global regrouping: construct the actual finite enumeration
of certified first-stretched routes, partition it by the common lowered target,
root, and peel size, and sum those fibers into a cutoff-independent multiple
of the pure mate product.  The older coarse mixed target/debt Cartesian carrier
still does not itself provide a common accepted source presentation and is not
used as one.  Closing this regrouping would feed a genuine physical
mate-transition floor and then a rooted-subtree Hardy--Poincare or posterior
conditional-variance estimate.

An earlier plan tried to bound the whole new-cutoff self-return trace by a
small constant. Exact exploratory computation found that plan false already
at cutoff four: a single state has self-return about `0.71428`, and six
symmetric copies make the positive trace exceed four. This computation is a
route-selection diagnostic only; no floating-point value enters a theorem.

For the detailed live dependency map, see [`work_plan.md`](work_plan.md).
For the source-based group audit, see
[`audits/AUDIT-GROUP-DEPENDENCE.md`](audits/AUDIT-GROUP-DEPENDENCE.md). That
audit found that the strand machinery is hard-coded to the SU(2)
Clebsch--Gordan rule and that no source dependency bridge currently connects
the component chain to the generic `singleStep` obligation. Accordingly, this
README makes no claim that group dependence is closed.

## Trust and constructivity rules

The Lean development is intentionally stricter than ordinary Lean code:

- no Mathlib dependencies;
- no `Classical.choice`, excluded-middle shortcut, or `native_decide` in
  load-bearing proofs;
- constructive reals carry explicit Cauchy moduli;
- witness-bearing existence claims use data-bearing structures or sigma
  types;
- load-bearing declarations are inspected with `#print axioms`; the permitted
  project gate is `propext` and `Quot.sound` only;
- unproved obligations and conditional interfaces are recorded in
  [`lean/SORRY_LEDGER.md`](lean/SORRY_LEDGER.md), rather than being described
  as completed physics.

Python and Rust may perform expensive searches or generate compact exact
certificates. They are **untrusted producers**: Lean must parse the resulting
finite data and independently check every semantic condition and inequality.

Read [`lean/AGENTS.md`](lean/AGENTS.md) before modifying any Lean file.

## Repository guide

| Path | Role |
| --- | --- |
| [`lean/`](lean/) | Lean 4 formalization and constructivity/axiom gates |
| [`lean/YMGap.lean`](lean/YMGap.lean) | Root import aggregator |
| [`lean/SORRY_LEDGER.md`](lean/SORRY_LEDGER.md) | Open obligations and milestone evidence |
| [`work_plan.md`](work_plan.md) | Current causal roadmap and status |
| [`docs/outline.md`](docs/outline.md) | Technical specification |
| [`docs/context.md`](docs/context.md) | Mathematical motivation and constructive rationale |
| [`audits/`](audits/) | Read-only source audits of important claim boundaries |
| [`computations/`](computations/) | Untrusted Python/Rust exploration and certificate generation |
| [`tests/`](tests/) | Tests for computational tooling |
| [`formal/`](formal/) | Human-readable LaTeX development |
| [`visualizations/`](visualizations/) | Generated diagrams and exploratory figures |

## Building safely

Lean is pinned by [`lean/lean-toolchain`](lean/lean-toolchain). Builds must use
the monitored launcher; bare `lake build` and bare `lake env lean` bypass the
repository's crash safeguards.

```bash
# Full monitored Lean build
make lean-build

# Narrow target (preferred while developing)
python3 scripts/safe_lean_build.py --jobs 1 -- +YMGap.Continuum.ModuleName:olean

# Check one source and emit only its importable olean (parent directory exists)
python3 scripts/safe_lean_build.py --check lean/YMGap/Continuum/ModuleName.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/ModuleName.olean

# Monitored axiom audit
make lean-audit
```

See [`docs/lean-build-safety.md`](docs/lean-build-safety.md) for memory and
worker limits.

The auxiliary Python tools require Python 3.11 or newer:

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -e ".[dev]"
make test
make lint
```

Other common targets are `make figures` and `make paper` (the latter requires
a working LaTeX installation with `latexmk`).

## How to evaluate a claim in this repository

Check all four of the following:

1. the exact theorem statement and its parameter range;
2. its printed axiom dependencies;
3. whether its hypotheses have concrete inhabitants, rather than only a
   conditional compiler;
4. whether the next bridge in [`lean/SORRY_LEDGER.md`](lean/SORRY_LEDGER.md)
   is still open.

A finite-cutoff theorem, a fixed-coupling clustering estimate, or a compiler
of the form “if certificate `C`, then gap” is valuable progress, but none is
by itself a continuum Yang--Mills mass-gap theorem.
