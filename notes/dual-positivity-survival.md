# Dual positivity survival: exact sign geography of the SU(2) character representation (first shaft)

**Date.** 2026-07-23 (first shaft); 4D extension same day.
**Code.** `computations/exact_haar_network.py` (exact integrator),
`computations/dual_positivity_survival.py` (probes),
`computations/hypercube4d_survey.py` (4D machinery),
`tests/test_exact_haar_network.py` (9 certification gates),
`tests/test_dual_positivity_survival.py`, `tests/test_hypercube_4d.py`
(pinned witnesses; 22 tests total, all exact).
**Arithmetic.** Everything below is exact: `Fraction` coefficients, the
heat-kernel coupling held symbolically as `s = e^{-t/4}`, sign verdicts on
`s ∈ (0,1)` decided by square-free factorization + Sturm counting.  No
floating point appears anywhere in the pipeline.

## 1. The question

The dual (character-expansion / spin-foam) representation of nonabelian
lattice gauge theory was historically abandoned because its amplitudes are
believed sign-indefinite ("the nonabelian dual sign problem": oscillating
6j-type weights).  If true where it matters, this blocks the strategy of
running an exact, never-linearized RG in the dual representation — the
representation in which compactness is native and the large-field problem
never gets created.  The question for this first shaft: **where, exactly,
does dual positivity first fail on minimal 3D complexes — and does the
physically forced channel summation restore it?**

Pointwise positivity of blocked weights is trivial (integrals of positive
integrands) and is *not* what is tested here.  What is tested is
positivity of the **dual coefficients**: exact Haar network values
attached to plaquette-spin assignments, the quantities an iterated dual
RG would propagate.

## 2. The instrument

`exact_haar_network.py` mirrors the Lean quaternion-block Haar calculus
(`finiteProductHaar`, the four-/six-valent projector files) in executable
form: links are unit quaternions, Haar = uniform measure on S³, monomial
moments are the exact rationals
`∏(2aᵢ−1)!! / (2^A (A+1)!)`, characters are Chebyshev polynomials in the
half-trace, and gauge invariance is exploited *exactly* via maximal-tree
gauge fixing (`GaugeFixedComplex`), which collapses the variable count of
every honest-geometry probe.

Nine certification gates pass, all as exact identities: Catalan trace
moments `∫(tr U)^{2k} = C_k`; odd-moment vanishing; character
orthogonality; the convolution identity `δ_{nm} χ_n(AB)/d_n` (verified
modulo the unit-norm ideal, which required implementing canonical
reduction `z² → 1−w²−x²−y²`); the fusion identity; the **honest-geometry
2D semigroup** (the 12-link 2×2 block reproduces `d_n s^{4n(n+2)}` on the
nose — the heat kernel is exactly self-similar under 2D blocking, our
Migdal fixed-point control); the K3 spin-model collapse `δδ/d`; K4
spin-model nonnegativity; and the Sturm sign-analyzer's edge cases.

## 3. Results (all exact)

### P0 — single cube (control): positive, as forced

Every edge of the closed surface is bivalent, so spins collapse to
all-equal: nonzero amplitudes are exactly
`Z(0)=1, Z(1)=1/16, Z(2)=1/81`.  Positive, 2D-like, no information about
the wall.  Control passes.

### P2 — the star of a link is *structurally* positive (a small theorem)

The folklore minimal sign-bearing object — one interior link with its
four surrounding plaquettes, read out through the four rim loops — was
swept over all page/rim spins ≤ 2: **187 nonzero values, zero
negatives**, and every one of the 81 rim channels' heat-kernel activities
is Sturm-certified positive on all of `s ∈ (0,1)` with a *termwise
positive* page ledger.

The reason is structural, and it is worth recording as a theorem-shaped
claim (Lean-ready):

> **Frozen-hub sum-of-squares.**  Gauge-fix the spine `e0 = 1`
> (conjugation invariance of class functions makes this exact).  Every
> loop of the star then has length ≤ 2 in free variables, i.e. every
> character argument has the spin-model form `g_u g_v^{-1}` on the graph
> "cycle C₄ + pendant edges to a frozen hub".  Integrating each vertex
> of a spin model inserts the projector onto invariants,
> `P = Σ_ι |ι⟩⟨ι|`, and the closed contraction pairs every bra with its
> own ket: the value is a sum of squared (real) network evaluations.
> Hence **every anchored star readout, in any dimension and for any
> compact group, is a sum of squares — nonnegative term by term.**

This explains, from one line, why the Lean spine's local four- and
six-valent "positive channel resolutions" kept succeeding: the star of a
link *cannot* go negative.  The 6j signs are invisible from any anchored
probe.  Corollary for experiment design: **tree-reducible and
spin-model-reducible probes are blind; the wall, if it exists, lives
strictly deeper.**

### P1 — double cube (first non-tree object): positive so far

Structured table `Z(n_A, n_B, k)` (outer shells forced uniform by
bivalent edges; interior face `k`; trivalent interior edges).  All values
computed so far are positive; parity kills `(1,1,1)` exactly:

```
Z(0,0,0) = 1        Z(0,1,1) = 1/16     Z(1,0,1) = 1/16
Z(1,1,0) = 1/256    Z(1,1,2) = 1/256    Z(0,2,2) = 1/81     ...
```

Completed table (guarded engine; two heaviest corners honestly
UNREACHED — resource verdicts):

```
Z(0,0,0) = 1
Z(0,1,1) = 1/16
Z(0,2,2) = 1/81
UNREACHED Z(0,2,4): link 3: merge cost 377804272 > 200000000
Z(1,0,1) = 1/16
Z(1,1,0) = 1/256
Z(1,1,2) = 1/256
Z(1,2,1) = 1/1296
Z(1,2,3) = 1/1296
UNREACHED Z(1,2,4): link 3: merge cost 377804272 > 200000000
Z(2,0,2) = 1/81
Z(2,1,1) = 1/1296
Z(2,1,3) = 1/1296
UNREACHED Z(2,1,4): product exceeded 2500000 monomials
Z(2,2,0) = 1/6561
Z(2,2,2) = 1/6561
UNREACHED Z(2,2,3): product exceeded 2500000 monomials
UNREACHED Z(2,2,4): link 3: merge cost 10452030080 > 200000000
```

All reached values positive.

### P1b — the 2×2×1 slab: positive, and *not* for structural reasons

The slab is the first probed complex with a **closed, unanchored
intertwiner circuit**: its four interior walls wind around the central
4-valent edge through four cubes, and after gauge fixing its plaquette
loops have length ≥ 3 in free variables — the sum-of-squares argument
does **not** apply.  Sweep over outer shell ≤ 2 × wall patterns ≤ 2
(243 assignments): **25 nonzero values, zero negatives**, e.g.

```
Z(outer=1, walls=(0,0,0,0)) = 1/16384
Z(outer=1, walls=(2,2,2,2)) = 7/442368
Z(outer=2, walls=(2,2,2,2)) = 1/28697814
```

This is the genuinely informative positive result of the shaft.

### P3 — the door test: exact positive channels

For every rim channel of the star, the heat-kernel-summed page activity
is an exact polynomial in `s` — exactly finite, because the fusion rule
kills page spins above `m_{i-1}+m_i` (no truncation debt).  Example:

```
rim (1,1,1,1):   1/4 + 9/2·s^16 + 6·s^24 + 21/4·s^32   — positive on (0,1)
```

All 81 channels: positive verdicts, termwise-positive ledgers.

### P4 — the 4D hypercube: surfaces, tori, and intersecting pairs

The 4-cube boundary (16 vertices, 32 edges, 24 plaquettes, **every edge
trivalent**) is the minimal closed genuinely 4D complex, and its dual
network is a closed trivalent web with tetrahedral sub-circuits — not
protected by any positivity argument we possess.  Three exact results:

**(a) Binary assignments are closed surfaces, and they evaluate by 2D
Yang–Mills.**  The parity-admissible spin-1 assignments form the F₂
kernel of the face–edge incidence: dimension 7 (the eight 3-cell
boundaries modulo the S³ fundamental relation), 128 surfaces.  Each has
bivalent edges *as a surface*, so it reduces exactly:

```
Z(Σ, uniform n) = d_n^{χ(Σ) − F(Σ)}
```

verified across the whole census — connected spheres at F = 6, 10, 12,
14 giving 2^{2−F}, disjoint sphere-pairs at F = 12 giving 2^{4−12}
(χ is additive; the vertex formula caught a hand-census error here,
and raw moments confirmed the formula), and three F = 16, χ = 0
surfaces at exactly 2^{−16}: the coordinate **Clifford tori** of the
boundary 3-sphere.  (Doubled
surfaces give d₂ = 3 in the same formula; spot-verified.)  Positive by
theorem; the census is pinned in `tests/test_hypercube_4d.py`.

**(b) Intersecting pairs are the genuine 4D interference test.**  Where
two surfaces cross without sharing a face, the crossing edges are
4-valent with four spin-1 faces; Inv(½⊗½⊗½⊗½) is 2-dimensional, and
the amplitude carries a closed chain of nontrivial 2×2 recouplings
around each intersection circle — every a-priori right to go negative.
The 8128 unordered pairs quotient under the hypercube's 384 symmetries
to **109 orbits**.  **Final ledger: 108/109 orbits evaluated (693 pair
evaluations), zero negatives, zero zeros-among-covered-orbits'
conflicts, zero inconsistencies.**  Covered-orbit values range from
1/16 (two 3-cells sharing a face is 1/256; the lightest crossings sit
higher) down to 1/2176782336 on the deepest crossings — every one
positive.

The single uncovered orbit is the extremal object: the **full
double-torus collision** (both Clifford tori simultaneously — all 24
faces occupied, the 8 shared faces at spin 2).  Its exact
χ₂ = χ₁² − 1 expansion into 256 terms was computed for 255 of them
(per-term symmetry-frame optimization; partial sums banked in a
checkpoint); the one extremal term (all eight intersection faces
doubled) exceeded the monomial engine under every strategy tried —
greedy frames, geometric slicing orders, torus-adapted incidence
orders, strict-memory retries — and is recorded as **UNREACHED: a
resource verdict, not a mathematical one**.  It is the inaugural
target for the TL-channel engine.

**(c) Orbit consistency is a free certification.**  Symmetric pairs are
evaluated through *different* gauge frames and contraction orders; every
coincidence across an orbit agreed exactly.  This cross-validates the
integrator far beyond the unit gates.

Two engine lessons worth recording: the amplitude is symmetry-invariant
but contraction *cost* is not — assignments unreachable in one frame
fall in another (`evaluate_in_best_frame`), which is how every formerly
OOM-fatal pair was recovered; and all resource limits now surface as
explicit `ContractionTooLarge`/UNREACHED verdicts (never silently as
zeros), with peak memory bounded by a result-size cap inside the
multiply itself.

### P5 — the vertex product formula, the closure of the survey, and THE WALL

**(a) The formula.**  Because every edge of the 4-cube boundary is
trivalent, SU(2) intertwiner spaces are multiplicity-free and the dual
amplitude factorizes completely:

```
Z(assignment) = ∏_{v ∈ 16 vertices} {6j}_v ,
{6j}_v = { j_xy j_xz j_xt ; j_zt j_yt j_yz }   (Wigner, j = n/2)
```

with no face, edge, theta, or phase corrections.  Fitted on three
surfaces, then over-verified: **949/949 exact matches** on the full
moment corpus (all binary and doubled surfaces + all 693 pair
evaluations, signs included), 20/20 on fresh cell-triples, and exact
n = 3 gates.  Where the formula disagreed with a hand census
(support-12 surfaces), direct moment integration sided with the
formula — those are disjoint unions of two spheres, χ = 4, Z = 1/256.
Amplitude evaluation drops from hours to sixteen memoized 6j lookups
(`computations/vertex_amplitude.py`).

**(b) Survey closed: 109/109.**  The formula evaluates the formerly
UNREACHED double-torus collision instantly: all sixteen vertices
contribute +1/6, so

```
Z(T1 ∪ T2) = 6^{−16} = 1/2821109907456  > 0.
```

Every orbit of the 4D pair survey is now evaluated, and every one is
positive.

**(c) THE WALL.**  With evaluation cheap, all C(128,3) = 341,376
triple-surface assignments (spins ≤ 3) were swept: **32,384 negative
amplitudes (9.5%) — and every single one requires a spin-3 face.**
Zero negatives occur at spins ≤ 2, anywhere, in anything this program
has ever computed.  The minimal negative exemplar (support 18, spin
profile {1:×9, 2:×6, 3:×3}):

```
Z(2707861, 3216742, 2201848) = −1/3981312
```

was **arbitrated against the raw moment engine**: the exact 512-term
χ-strand expansion (χ₂ = χ₁²−1, χ₃ = χ₁³−2χ₁, per-term symmetry-frame
optimization) completed in 17 seconds and returned **−1/3981312 — the
formula's value to the digit**, through an entirely independent
pipeline (quaternion moments; no representation theory).

**The wall's coordinate, exactly:** the sign problem of the SU(2) dual
representation switches on at **j = 3/2**, and geometrically it lives
on **triple-intersection curves** — spin-3 faces are faces shared by
all three surfaces, and no configuration lacking such a curve is
negative.  The conjecture (DP) as originally stated is **false**; what
survives, now supported by every computation to date, is:

> **(DP≤1)** Intertwiner-summed SU(2) dual amplitudes with all
> plaquette spins ≤ 2 (j ≤ 1) are nonnegative.

**(d) What the wall means physically.**  Heat-kernel activities weight
spin n by s^{n(n+2)}: the negative sector enters at s^{15} against the
positive sector's s^{3}.  The physical question is therefore no longer
"is the dual sign-free?" (it is not) but "**do the s-weighted channel
sums remain positive on s ∈ (0,1) despite the negative j ≥ 3/2
sector?**" — precisely the door-test question, now sharply posed with
the wall's location known.  This is DP.2/DP.3's question, and the
vertex formula makes the required sums computable.


### P6 — the sign is geometric: three falsifications and the framing hypothesis

With the vertex formula making million-configuration sweeps routine, the
day's second harvest was three *dead conjectures* — each killed by exact
data in minutes, each death narrowing what the sign can be:

1. **Not intersection-count parity.**  `sign(Z) = (−1)^{|a∩b∩c|}` fails
   on 160,128 of 341,376 triples; negatives occur at both parities of
   the triple overlap.
2. **Not a center artifact.**  The full quadruple sweep (all
   C(128,4) = 10,668,000 sums, spins ≤ 4): 2,423,296 negatives — census
   by max spin {3: 426,816; 4: 1,996,480} — including **18,176
   all-even-spin negatives**.  The SO(3) (integer-spin) dual is also
   sign-indefinite: the sign does not live in the Z₂ center, and the
   Frobenius–Schur (quaternionic-rep) story is at most partial —
   j = 2, a real representation, carries signs at four-fold overlap.
3. **Not any function of overlap sizes and component counts.**  A
   feature census (triple size, its connected components, pairwise
   overlap sizes, parities) yields 880 keys of which 836 are sign-pure —
   but 44 keys covering 55,248 triples are **mixed**: configurations
   with identical overlap combinatorics and opposite signs.

The surviving hypothesis is the one the falsifications converge on: the
sign depends on the **embedding** of the intersection locus — how the
surface sheets sit and twist through one another in the boundary
3-sphere — data invisible to counting, visible to linking and framing.
This is spin-*structure* behavior (Kasteleyn's discrete spin structures
absorbed exactly such loop signs in 2D; framings/twists play this role
for curves in 3-manifolds), as distinct from spin-*representation*
behavior, which item 2 kills.  Next microscope: matched-pair analysis —
take triples with identical feature keys and opposite signs, and diff
their geometry directly; then test linking-form invariants of the
intersection curves.  If the sign is a coboundary (gauge-absorbable à
la Kasteleyn), the dual becomes sign-free after a local twist and (DP)
resurrects in twisted form; if it is a genuine class, the RG must run
in the twisted/graded category.  Either way the sign sector becomes
*understood structure* rather than an obstruction — and the physical
door-test question (s-weighted channel sums, negative sector entering
at s¹⁵ vs s³) is unchanged by any of this.


### P16 — the imagination, checked: the Birkhoff mechanism is real

The imagined Layer-3 technology (mass gap as dimension-free cone
contraction, Birkhoff–Hopf) was tested against the smallest physical
channel-mixing kernel we possess — the wheel, heat-kernel weighted,
uniform sector (`scratch/birkhoff_check.py`).  Three findings, exact:

1. **The kernel is a strict Birkhoff contraction**: Hilbert projective
   diameter Δ ≈ 0.44–0.75 across cutoffs, contraction ratio
   q = tanh(Δ/4) ≈ 0.11–0.19.  Deeply inside the contractive regime.
2. **The diameter is exactly coupling-independent**: Δ identical at
   s = 1/4, 1/2, 3/4, 9/10 to all computed digits — structurally so,
   because activities enter as column scalings, which are Hilbert
   isometries.  The projective diameter is *pure group data*.  This is
   the imagined "constants from the group, not the volume" property,
   observed rather than hoped.
3. **One correction to the imagination**: on the naive positive
   orthant the diameter grows slowly with spin cutoff (0.44 → 0.75,
   cutoffs 2 → 5).  Cutoff-uniformity is therefore not free: the
   missing theorem must be formulated on a *weighted cone* (activity
   sequences inside a heat-kernel decay envelope), where the
   high-spin tail is cone-geometry, not diameter inflation.  The
   imagined object thus acquires its exact specification: **a
   Birkhoff contraction theorem for the dual blocking map on the
   heat-kernel-enveloped unbranched cone, with the κ-graded sector as
   an s⁶⁴-dominated perturbation.**

The imagined missing math, one check later: mechanism confirmed,
coupling-independence confirmed, and the remaining invention narrowed
from "a metric and a miracle" to "the right envelope on the cone."


### P17 — building the enveloped cone: the envelope must flow

First construction pass (`scratch/enveloped_cone.py`).  Clause 1
(envelope invariance) tested naively — corridor width of T(envelope)
against the *same-s* envelope — **fails, with a linear-in-Casimir
growth pattern** (log-widths 2.25, 6.24, 9.56, 16.64 at cutoffs
2–5).  That pattern is a diagnosis, not a defeat: it is precisely the
signature of comparing against an unrenormalized envelope.  The
blocking map does not preserve the heat-kernel envelope at coupling
s; it *transports* it (the exact 2D semigroup c_n → c_n⁴ is the clean
limit of this).  The corrected clause:

> **Envelope invariance (flowed form).**  T maps the corridor around
> envelope(s) into a *uniformly narrow* corridor around
> envelope(s′), where s′ is the renormalized coupling determined by
> the map itself.  Contraction then lives on the flowed family of
> cones — which is, of course, what an RG statement was always going
> to be: the cone is not fixed; the *pair* (cone, coupling) flows,
> and uniformity is claimed along the flow.

Build state: kernel machinery, corridor meter, and iterate-contraction
harness all standing (`computations/enveloped_cone.py`); next pass
fits s′ from the corridor's Casimir slope and re-measures width
against envelope(s′) — the number that decides whether the enveloped
Birkhoff theorem closes on this model kernel.


### P18 — the envelope flows: fit, collapse, and the right test object

Fitting the renormalized coupling from the Casimir slope
(`scratch/envelope_flow.py`) delivers the corrected clause's first
numbers: **the flowed corridor collapses** — log-widths drop from
{2.25, 6.24, 9.56, 16.64} (naive) to {0.90, 1.31, 1.86, 2.23}
(flowed) at cutoffs 2–5, an ~87% reduction at the deepest cutoff.
The envelope genuinely flows, and flowing it recovers most of the
corridor.

Two residual tells, with a structural diagnosis: the width still
creeps, and the fitted s′ drifts upward with cutoff (0.67 → 0.88,
versus the 2D semigroup's s⁴ = 0.0625) — i.e. the wheel
*anti-renormalizes*.  Rightly so: the wheel is a star **readout**,
not a scale map — its rim spins spread upward (m ≤ 2j), the opposite
of block-spin's downward concentration.  The model kernel was good
enough to confirm the Birkhoff mechanism (P16) and to force the
flowed-envelope formulation (P17); it is the wrong object for the
saturation test.  **The right object is the genuine one-step
blocking kernel** — the slab's 2×2 coarse-plaquette readout (DP.2),
whose 2D limit provably has s′ = s⁴ and corridor width zero (the
exact semigroup).  The 3D defect from that exact baseline is
precisely the quantity the enveloped Birkhoff theorem needs to be
small — and it is computable with the standing machinery.

Chain status after this push: mechanism confirmed → envelope must
flow → flow collapses the corridor → saturation test lands on DP.2's
blocking kernel, where the 2D fixed point provides the exact
zero-width baseline.  Each issue met so far has resolved into a
sharper formulation rather than an obstruction.

### P19 — DP.2 built: the slab blocking kernel exists and is positive

The genuine 2×2 blocking kernel demanded by P18 is now a computed
object (`computations/slab_blocking_kernel.py`).  Construction: the
2×2×1 slab block carries heat-kernel activities on all twenty faces;
coarse Wilson loops χ_n (top perimeter) and χ_m (bottom) read out the
two-sided blocked kernel T[n,m](s) — an exact s-polynomial.  An
adapted gauge tree (7 of 8 perimeter edges per layer in the tree)
makes each coarse loop a single free link; a per-link eliminator with
unit-sphere reduction of intermediates (integral-invariant, hence
exact) keeps contraction feasible; the transverse skeleton
(4 corner-linked perimeter classes q, 4 interior walls w — corner
bivalence forces the pairing) decomposes the sum into small certified
evaluations, cross-validated against the direct contraction at M=1
(exact equality, all entries).

Three structural findings:

1. **Univalence death (frozen-side scheme).**  If the block does NOT
   own its perimeter-wall fluctuations, every interior wall dies by
   univalence at slab thickness one, and the kernel collapses to the
   EXACT 2D rule c'_n = c_n^4/d_n^3 (gate-checked: N(n,m,0) =
   d_n^{-3} d_m^{-3}, all n,m ≤ 2).  Transverse physics enters
   entirely through the owned boundary.
2. **Entrywise positivity.**  Every computed entry of T at truncation
   M=1 (coarse spins ≤ 2 populated) is Sturm-certified positive on
   all of s ∈ (0,1).  The blocking kernel — unlike the raw dual
   amplitudes beyond the wall — shows no sign problem at this depth.
3. **The flow runs FASTER than 2D and the corridor narrows.**  Flow
   fits at M=1 (3-channel sector): s' = 0.0341 at s=1/2 (2D baseline
   s^4 = 0.0625), corridor log-width 1.82 (wheel readout at cutoff 5:
   2.23); at s=3/4: s' = 0.2495 vs 0.3164, width 0.79.  Transverse
   dressing accelerates the damping — and the corridor tightens with
   coupling.  The raw Birkhoff diameter of the full positive sector is
   HUGE and coupling-dependent (Δ ≈ 12–65): the projective contraction
   does NOT hold on the whole cone — confirming that the enveloped
   (corridor-restricted) cone is not a convenience but the mechanism.
   M=2 stability: UNREACHED at session resources — T[0,0] alone
   returned 18 terms with 25/47 skeleton classes over the 120 s
   per-class budget (partial checkpoint kept; needs a dedicated long
   run or the Mac).

### P20 — band geometry v2: hardened, voted, and honestly stuck at d2

The linking lift was rebuilt (`scratch/band_geometry2.py`) with four
fixes: F1 non-crossing chord traversal at revisited sheets (loud
failure on any leftover edge — the old walk silently truncated
composites); F2 cross-component linking terms; F3 per-component
orientability; F4 a push-scale stability vote (every q must agree at
two η/ε scales, else FAIL).  Pairs are now perfectly even
(polarization defined, 848–1209/case checks, zero odd defects).

The triple-consistency meter, however, saturates at ~70% (84/120 →
87/120 → 82/123 across three geometry revisions), with EVERY miss
exactly d2 — off by one linking unit, never by parity.  The stability
vote proves the misses are systematic, not metric accidents.  A
feature-correlation sweep (188 triples; connector antipodality,
perpendicularity, revisited sheets, components, clashes, seam counts,
and all their small F2-combinations vs the miss bit) found NOTHING
above the trivial baseline: the defect is not a countable connector
feature.

**Diagnosis (the sharpened missing math).**  The lift embeds the
CURVES but not the SURFACE: sheets push into their own 3-cells, so
the strand cover is torn at seams where glued sheets use different
push axes.  Band framings across tears pick up half-twist holonomy
that no curve-local bookkeeping can recover.  A coherent q needs an
embedded (or abstractly framed) Pin⁻ realization of the whole strand
cover — THE object the next shaft must build.

**Correlation-mode verdict (completed, 300-config sample,
vote-gated).**  52 configs completed the full pipeline (143 nonpin +
95 geometry failures — the vote fails loudly, as designed).  β
concentrates at 0 mod the d2 noise REGARDLESS of κ: κ=0 (n=35) has
β∈{0,2,6} for 30/35 with β=0 at 20; κ=1 (n=17) has β=0 at 8 and β=4
at only 2.  Exact β=4κ: 22/52 (42% vs 12.5% random — driven entirely
by the κ=0 sector; mirror convention identical).  Reading: the
torn-curve geometry is systematically BLIND to the κ-carrying twist —
the tears sit exactly at clashed seams, where the orientation-reversal
data lives.  The run neither confirms nor refutes β = 4κ; it sharpens
WHY the embedded-surface realization is non-negotiable.
(Checkpoint: computations/abk_verdict2_ckpt.json.)

### P21 — the Lean transport: three kernel-checked theorems

The session's structural results now live in the repo's Lean
discipline (`dual_kappa_spike/`, standalone, no Mathlib, kernel
`decide` only, {propext, Quot.sound} gate):

- `DualKappa.lean` — `no_local_gauge`: no face/edge-local sign gauge
  reproduces the 20-config anomaly certificate (832 key entries, all
  even multiplicity, one negative product): κ is a genuine global
  class.  Proof: strong-induction even-multiplicity lemma + kernel
  decide on the machine literals.
- `FrozenHub.lean` — the frozen-hub SOS theorem at certificate level:
  the exact ledgers of ALL 81 anchored rim channels (spins ≤ 2) have
  nonnegative integer coefficients (kernel-checked), and
  self-contained polynomial lemmas conclude `rim_readouts_pos`: every
  anchored star readout is strictly positive at every rational
  coupling s = num/den > 0.  (Strictly stronger than the per-channel
  Sturm certificates: all rational s > 0, not just (0,1).)
- `SupportLaw.lean` — the branch detector ({1,1,2} incident-spin
  pattern over the literal 4-cube edge-face table) as a Lean
  function; `kappa_odd_all_branched` kernel-checks it on 100 κ-odd
  samples.  The global census (all 6,704 κ-odd branched; all 8,128
  decomposables κ-even) was re-verified moment-side this session.

Status: UNBUILT in the cloud (no Lean toolchain); Mac-side
`lake build` next session (session lock per AGENTS.md).  Wiring TODO
unchanged: derive the sign/ledger literals inside Lean from the main
tree's quaternion Haar machinery.

## 4. Reading of the results

The sign problem of the nonabelian dual is now **located, not merely
bounded**: it does not exist at spins ≤ 2 anywhere this program has
reached (3D through the slab, 4D through the complete 109-orbit pair
survey and all sub-spin-3 triples), and it switches on exactly at
j = 3/2 on triple-intersection curves — with the minimal negative
amplitude arbitrated to the digit by two independent exact pipelines.  The emerging picture, consistent
with (and sharpening, by exactness) the numerical positivity observed in
the dual-simulation literature for 3D SU(2) (Cherrington et al.) and the
positivity theorems for related spin-foam amplitudes (Baez–Christensen):

> The oscillating 6j symbols live in the **intertwiner-resolved basis** —
> a basis chosen historically for *hand-computability*, not physics.  The
> Haar integral automatically performs the physical channel sum, and the
> physically-summed dual coefficients stay positive far beyond where the
> resolved basis oscillates.  At the scales probed, the "sign problem" is
> an artifact of a resolution the physics never asked for — detail thrown
> away *in reverse*: structure was added (a basis), and the added
> structure carried the signs.

For the program this connects both clones: it supplies executable,
exactly-witnessed instances for the Lean spine's positive-channel
factorization strategy, and it is the candidate **positivity cone** in
which the codex clone's `RG-I7 UniformContractionCertificate` wants to be
inhabited — a cone that empirically survives blocking at these scales.

## 5. Honest boundary of this shaft

1. **The 2×2×2 core is out of naive reach.**  The first complex where six
   walls meet at a central vertex OOM-killed the naive dict-polynomial
   engine.  This is the next wall-candidate scale.  The needed tool
   upgrade is exactly the executable mirror of the Lean TL₃/recoupling
   projectors: factored contraction through intertwiner channels instead
   of raw monomial expansion.  (Estimated: replaces 4^L monomial growth
   by channel-dimension growth.)
2. **4D: the single hypercube is now surveyed** (see P4); the next 4D
   scales are the double hypercube (two 4-cells sharing a cube, 29 free
   links) and the 2×2×1×1 brick around its central plaquette — both
   need the TL-channel engine.
3. **Positivity ≠ contraction.**  Nothing here estimates `q < 1`; this
   shaft only maps the cone in which such an estimate could be posed
   without leaving positive territory.
4. **Wilson action untested** (heat kernel only; Wilson coefficients are
   also positive, so P0–P2 conclusions transfer, but the exact
   `s`-polynomials of P3 do not).
5. **Reflection positivity of blocked duals untracked** — the
   load-bearing positivity for OS reconstruction is a separate (harder)
   cone; this shaft's positivity is the dual-coefficient cone only.
6. **Independent cross-check duty.**  All headline values are internally
   consistent (nine certified gates + hand-verified chain values +
   parity selections appearing where representation theory demands), but
   an independent rep-theoretic recomputation (invariant-subspace
   projectors over ℚ̄) of one slab value remains open as a duty.
7. **Double-cube high corner still running** (`n ≤ 2, k ≤ 4`); no
   negative so far.

## 6. Next shafts, in order of information per unit work

1. **TL-channel contraction engine** (unlocks 2×2×2 and 4D slab —
   the two live wall candidates).  This is also precisely the point
   where the Lean TL₃ six-valent projector work and this Python engine
   should merge into one bilingual artifact.
2. **The 4D slab analogue** — if positivity survives *there*, the
   conjecture "intertwiner-summed SU(2) dual amplitudes of physical
   complexes are nonnegative" deserves promotion to a target theorem
   (its truth would delete the historical reason the dual RG road was
   abandoned).
3. **One-step dual blocking map in the positive cone**: compute the
   exact blocked activities of the 2×2 coarse plaquette on the slab
   (readout characters against heat-kernel weights everywhere), i.e.
   the actual RG step this cone is supposed to carry — then compare
   `c'_n / c_n` against the 2D exact `c_n^4` to measure the first exact
   3D defect coefficient.
4. **RP tracking**: chessboard-reflect the slab and test whether the
   blocked dual coefficients remain in the RP cone — the positivity
   that OS reconstruction actually consumes.
