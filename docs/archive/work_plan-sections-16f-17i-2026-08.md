# ARCHIVE — work_plan.md sections §16f through §17i (2026-07-28 … 2026-08-03)

> **Archival, superseded.** This file preserves plan text that is no longer
> in the live `work_plan.md`. It is kept for provenance and traceability
> only; the current `work_plan.md` (milestone-structured, "Whole-project goal
> and live completion map") supersedes it. Nothing here is live status.
>
> **Source.**
> - §16f ("16f. Addendum … the c_SU2 ASSEMBLY EXECUTED") through §17h:
>   verbatim from `git show e72e2c8:work_plan.md`, lines 26492–28048
>   (commit `e72e2c8d234971d1637be94c534c31b30e0f830d`, 2026-07-30 18:38 PT,
>   the end of the claude-lineage `main`).
> - §17i: verbatim from commit `88bf7204632d46f2c1059084f870cd2ecbefdc5a`
>   (2026-08-03 04:58 PT), `work_plan.md` lines 28049–28097. That commit was
>   made in a separate local clone (`claude_folders/ym_mass_gap_sheaf`) and
>   never pushed; it is not an ancestor of this repository's history.
>
> **How it was dropped.** These sections were dropped from `work_plan.md`
> in merge `c6488697` (2026-09-11 03:45 PT, "Merge remote-tracking branch
> 'origin/main' into codex/full-workspace-snapshot-2026-07-24"), whose
> result kept the snapshot branch's plan text. The code and notes these
> sections describe (e.g. `computations/c_su2_assembly.py`,
> `notes/c-su2-assembly.md`, `computations/sector_sos*.py`) remained in
> the tree. The independent cross-check that §17i describes was added
> back on 2026-10-05 as `computations/insertion_moments.py`,
> `tests/test_insertion_moments.py`, `notes/insertion-assembly.md`.
>
> Archived 2026-10-05. Section cross-references below (§16e, §16l, …)
> refer to the old plan; earlier sections remain available via
> `git show e72e2c8:work_plan.md`.

---

### 16f. Addendum (2026-07-28, same session): the c_SU2 ASSEMBLY EXECUTED — the marginal-defect coefficient is an exact rational, its sign is anti-screening, and the U(1) mirror gate does not fire

The §16e queue (a)-(d) is executed in one exact instrument.
Artifacts: `computations/c_su2_assembly.py`,
`computations/c_su2_assembly_results.json`,
`tests/test_c_su2_assembly.py`, `notes/c-su2-assembly.md`.  Suite
77/77 green (cloud; includes 12 new exact pins).

**The engine.**  A tilted-moment engine for the flat-limit Gaussian
network of the slab, exact through tau^2 in the (n,m)-dependent
part — INCLUDING the operator-ordering terms §16e deferred, which
enter at exactly the order c_SU2 lives at and are here computed,
not deferred.  Per su(2) triple: T[n,m] = Z e^{F tau} tr E[e^{iL}
exp(q - V_3 - V_4)], with L the loop tilts, q the phi/sin(phi) +
(sin u/u)^2 Jacobian insertions, V_3/V_4 the BCH non-closure of the
face-ordered products (commutator = cross product), covariance
8 tau G^{-1} (the §16e dictionary).  All moments reduce to
exact-rational J-word tables (epsilon contractions via precomputed
isotropic patterns; E[det det] = 6 det Cov); traces from an exact
complex-rational spin cache.  E[V_3 L] = 0 pinned.

**Gates, all exact, all green.**  (g1, decisive) heat-kernel
SEMIGROUP on 1-, 2-, 3-link chains: the entire tau^2 connected
coefficient must vanish — and does, exactly; one identity
exercising Jacobians, BCH, orderings, normalization together.
(g3) BCH series vs mpmath matrix logs.  (g4, the §16e (d)
refutation channel) the identical engine at one abelian component:
kappa_2 == 0 identically — c_dyn^{U(1)} = 0 EXACTLY — and the
identical flow assembly reproduces the banked c_1 = -4 at N = 2.
(g5) s_1 = const - 3(C(n)+C(m)) exactly; series exactly real;
polynomial fit exact on the grid + held-out n = 4.

**The result (exact rationals).**

    kappa_2(n,m) - kappa_2(0,0)
      = -(21/8)(C(n) + C(m)) + (2/3) C(n) C(m).

No quadratic terms: pair-independence of the slope is a THEOREM of
the fit at this order.  (i) The cross coefficient is PURE FUSION:
(2/3) C(n)C(m) = Var_fusion(delta)/2 — Jacobian/BCH/orderings do
not touch the cross channel, so the discriminating observable is
now exact at this order: X_nm = (2/3) C(n) C(m) tau^2, X_11 =
+6 tau^2 (the §16e "indicative" upgraded to exact).  Cross-checked
on the banked exact M=2 SU(2) kernel: T[1,1]T[0,0] > T[0,1]^2
exactly at sampled s, X_11/tau^2 passing through ~6 on s in
[3/4, 17/20] before fixed-M truncation bites (consistent with the
§16a protocol discovery).  (ii) The diagonal dynamical defect is
c_dyn = +21/8, with exact block attribution orderings -6 +
Jacobians 139/4 + BCH-quartic 502/3 + BCH-cubic-squared -4769/24 +
epsilon-linear 0 — a cancellation certified by g1.  (iii) Flow
slopes: E* = 3 + c_SU2(N) tau, c_SU2(N) = 21/8 - (2/3) E_w[C(m)]
(w ~ d_m^2): +41/40, -11/8, -183/40 at N = 1, 2, 3, every pair
identical (gated).  The N-dependence is basis bookkeeping exactly
parallel to U(1)'s -4/3, -4, -8; the basis-free content is c_dyn
and the cross coefficient.

**MD.3's number.**  At the standard basis N = 2 the SU(2)
fusion-basis term equals -4 — numerically identical to U(1)'s
entire slope — so the matched-basis defect is

    c_SU2 - c_U1 = +21/8   EXACTLY:

the first genuinely non-abelian number of the flow, an exact
rational with no pi and no measured input, parameterized by the
engine's group data as MD.3 demanded.  Its sign is POSITIVE: the
non-abelian dynamics push the one-step exponent UP — away from
marginality, toward the gapped class — relative to the gapless
abelian control on the same instrument and basis.  The
anti-screening statement at this order is BANKED.

**Honesty.**  One-step, thickness-one, anisotropic slab; tau-slope
of the D2 family at s -> 1; iterated/isotropic upgrades downstream.
Image/theta-separation slack exponentially small (certified
rational for U(1); 41-87-digit numeric gates for SU(2); a
certified-rational SU(2) slack bound is owed by whichever step
first consumes c_dyn in a verdict).  tau^3 outside this
computation.  A2 (component decoupling) is DISCHARGED at this
order by construction — the engine computes the coupled
three-component integral exactly; A1 (flat-limit interchange)
remains flagged.  The M=2 cross-check is a consistency gate, not a
certificate.  Cloud verification only; Mac session-lock run owed;
push of this session's commits owed by Arthur
(`git push origin main`).

**Next attack (MD.2 residual + MD.4 feed).**  (a) The tau^3 term
and the crossover: extend the engine one order (the same term
algebra, one more Wick order) to bound where the asymptotic curve
hands off to the Sturm window atlas (MD.4 consumes this).  (b) The
SU(2) M -> infinity resummation (cyclic transfer operator, §16c
route (a)) so the dichotomy class of tau'/tau as s -> 1 is decided
from certified windows rather than the flat expansion — X_nm =
(2/3) C(n)C(m) tau^2 is its designated first consumer, now with an
exact target.  (c) A certified-rational SU(2) image/slack bound to
upgrade the flat dictionary from numerically gated to
certificate-grade.

### 16g. Addendum (2026-07-28, second session): the tau^3 CROSS LAW, the per-face image CERTIFICATE, and the FIRST CERTIFIED M -> infinity statement — the two instruments now bracket the dichotomy from both ends

Push of d6af5ba..150dceb confirmed on origin/main.  This session
executes the §16f queue: (a) the tau^3 extension, (b) the M ->
infinity resummation's first certified stage, (c) the
certificate-grade image slack.  Artifacts:
`computations/c_su2_tau3.py`, `computations/su2_flat_slack.py`,
`computations/su2_minf_windows.py`, their JSON ledgers,
`tests/test_tau3_and_windows.py`.  Suite 87/87 green (cloud).

**(a) The tau^3 cross law (exact).**  The engine is extended one
Wick order with the complete tau^3 term algebra: BCH grades 4-5
(derived by 2x2 matrix series, gated against the graded recursion
and mpmath), the quartic Jacobian/Haar insertions, the quintic and
sextic BCH potentials V_5, V_6 and the Jacobian-argument couplings
J_3, J_4, decomposed into det/dot invariant form by a generic
symmetrized-tensor solver with entrywise exactness asserts.
Scope discipline: cross observables need >= 2 J's per side, so
X_nm receives tau^3 contributions ONLY from L^6, L^4 q_2, L^4 V_4,
L^4 V_3^2 (pointwise Gram), L^5 V_3 — all computed on the slab.
GATES, all exact: star-3 semigroup kappa_2 = kappa_3 = 0 with V_3
and Delta^(3..5) LIVE (recorded honestly: the §16f chains had
V_3 == 0, so this also retroactively strengthens the tau^2
verification); fusion stars (both loops on one link) reproduce
sum_J (2J+1) e^{-k tau C(2J)} through kappa_3 at k = 1 and k = 3 —
the decisive independent-algebra gate for the cross channel;
U(1) mirror kappa_3 == 0; star-4 at kappa_2; the slab V_3^2 L^2
block recomputed via the Gram route equals the §16f epsilon route.
THE RESULT:

    X_nm = C(n) C(m) [ (2/3) tau^2 + (115/54) tau^3 ] + O(tau^4),

the tau^3 coefficient again EXACTLY proportional to C(n) C(m)
(115/6, 460/9, 3680/27 at (1,1), (1,2), (2,2)).  Decomposition:
fusion part (8/9) C C (from mu3c(delta) = -(16/3) C C, exact),
dynamical part (67/54) C C — the first nonzero DYNAMICAL cross
coefficient (at tau^2 the dynamics left the cross channel
untouched).  Both terms positive: the discriminator's sign is
reinforced at next order.  The DIAGONAL kappa_3 (the E* curvature)
is left open: its heavy blocks (V_3^4 L^2, V_3 V_5 L^2, V_6 L^2,
J-blocks) are combinatorially out of reach of direct Wick
enumeration on the slab (~10^10 pairings); for MD.4's crossover
purpose they are superseded by the certified windows of (b).

**(c) The per-face image certificate.**  `su2_flat_slack.eps_img`
certifies, in exact rationals, |K - K_0|/K_0 <= eps_img(tau, delta)
on phi in (0, pi - delta], handling the j-pair cancellation at
phi -> 0 by mean-value bounds; scale e^{-pi delta/tau}
(e.g. 4.4e-13 at tau = 1/20, delta = 1/2; mpmath domination gate
passed).  The remaining glue — the T-mass of the large-angle
region — is the SAME object as the spin tail (angle-spin duality)
and joins the (b) residual; the tau-series coefficients are
untouched by images at every finite order.

**(b) The domination transfer operator and the first certified
M -> infinity statement.**  The dominated mass sum_{L} prod_f
d^2 s^C over triad-admissible labellings factorizes EXACTLY as
d_n d_m tr_{parity-even}(T^4) on corner states (a, b, q) — the
|N|-free SHELL of the corner transfer factorization (§16c route
(a)), with |N| <= d_n d_m prod d the only crudeness.  Certified
TAIL(M; s) = trace difference + a union-bound Lambda-slop (no
square-root losses); the M=2 finality gaps (unreached configs,
labels listed in dp3_m2_entries) folded in as exact per-config
mass bounds.  EXECUTED CONSUMPTION:

    at s = 1/2:  X_11(M -> infinity) in [+0.0665, +0.4193],
    certified positive — T11 T00 > T01^2 including ALL truncation
    corrections: the flat discriminator's sign, nonperturbative.

Above s ~ 0.55 the |N| <= prod d overshoot (~10^5 at s = 3/4)
swamps the small entries and the windows close.  The two certified
instruments now BRACKET the dichotomy regime from opposite ends:
the tau-series owns tau -> 0 (s -> 1), certified-window kernels own
s <= 1/2, and their meeting ground s in [0.8, 0.95] — where the
tau^3/tau^2 ratio ~ 1 at s = 3/4 explains the apparent series-vs-M=2
gap there — is exactly what the TRUE corner amplitudes must open.

**Also recorded.**  M = 3 kernel entries attempted in the cloud
container: UNREACHED (wall-clock; kernel_entry(0,0,3) exceeded 50
minutes without completing) — the fixed-tile route at M = 3 needs
the transfer factorization, not more budget.

**Honesty.**  The certified window and the asymptotic series do
not yet overlap; nothing here decides the s -> 1 dichotomy class.
X_nm's tau^3 law is exact as a series statement; its domain of
numerical usefulness ends near s ~ 0.8.  The image certificate is
per-face; the network glue is flagged.  The domination gate
dominated(2) + U_2 >= T_2 passed at s = 1/2, 3/4 for all entries
used.  Cloud verification only; Mac session-lock run owed.

**Next attack (the sharpened open front).**  (1) The TRUE corner
transfer amplitudes: replace the domination weights d^2 s^C by the
actual recoupling matrix elements on the SAME (a, b, q) label
space — every order-of-magnitude recovered widens the certified
window toward the series domain; the meeting at s ~ 0.85 decides
the dichotomy with certificates on both sides.  (2) Cheap interim
sharpening: exact-N hybrid (compute network_value_fixed for the
dominant level-3 configs, bound the rest by domination) — pushes
the windows toward s ~ 0.65-0.7.  (3) The diagonal kappa_3 only if
MD.4's atlas demands it; otherwise the windows carry the crossover.

### 16h. Addendum (2026-07-28, same session): REFLECTION POSITIVITY AS A QUANTITATIVE TOOL — the OS/CS lemma, nine-to-twelve orders recovered, and the certified window pushed to s = 11/20 with a 3e-4-wide interval at s = 1/2

Executes the §16g "interim sharpening", upgraded: the exact-N
hybrid became a REFLECTION-POSITIVITY bound — the config-level
shadow of DP.R1's OS Gram.  Artifacts:
`computations/su2_cs_tail.py`, `computations/su2_cs_diagonals.json`
(+ worker shards), `computations/su2_cs_tail_results.json`,
`notes/su2-cs-tail.md`, `tests/test_cs_tail.py`.  Suite 93/93
green (cloud).

**The lemma (config-level OS/CS).**  The DP.3 OS pairing (link
reflection z -> 1-z) restricts to each fixed transverse sector:
(q, w) sit on theta-invariant vertical faces with single characters
(positive spectral weight — the Osterwalder-Seiler condition); the
top data (n, a) and bottom data (m, b) are strictly one-sided.
Sector-wise OS positivity + Cauchy-Schwarz give, for every
admissible fixed-tile labelling,

    N(n,m,q,w,a,b)^2 <= N(n,n,q,w,a,a) * N(m,m,q,w,b,b),

both factors >= 0 (OS norms).  MACHINE GATES: (i) verified on the
banked exact NEGATIVE network values of dp3_m2_entries (their
diagonal partners computed fresh) — nontrivial: the left side is
signed 6j interference, the bound a product of norms; (ii) the D4
canonicalization used to dedup diagonal keys verified against
computed values (rotation, reflection, wall-shift images agree
exactly); (iii) every computed diagonal >= 0, asserted at
computation time.

**The quantitative gain.**  Crude domination |N| <= d_n d_m prod d
is 10^3..10^5 per config; computed diagonals give sqrt(D_a D_b) ~
10^-7..10^-6: NINE TO TWELVE orders recovered per covered config.
Coverage: level-3 configs ranked by carried crude mass (steep —
~100 diagonal keys own essentially all of it); diagonals computed
exactly (network_value_fixed) under wall-clock budgets in parallel
workers; one-sided CS where only one side landed; crude fallback
otherwise — every path certified, unreached values only LOOSEN the
bound.  Levels >= 4 keep the §16g domination transfer.

**Certified windows (the consumer, re-executed).**

    s = 1/2:    X_11(M -> infinity) in [+0.258238, +0.258546]
                — THREE-DECIMAL certification (§16g gave
                [+0.0665, +0.4193]: ~1000x tighter);
    s = 11/20:  X_11 in [+0.2519, +0.3126]  — NEW certified
                territory beyond the §16g boundary;
    s = 3/5:    still closed by ~2.3x (tail11 6.0e-5 vs
                T11 2.6e-5) — the remaining top-mass diagonal
                keys (heavy contractions, some exceeding a 900 s
                budget in this container) would open it; workers
                left running, coverage extendable without any
                code change.

**Honesty.**  The lemma's proof is the standard OS-Seiler
link-reflection argument applied sector-wise — machine-verified on
banked exact values; a Lean-grade formalization is NOT claimed.
Unreached diagonals are recorded as unreached, never consumed.
The certified domain still does not overlap the tau-series domain;
the TRUE corner-amplitude factorization remains THE open front —
the diagonal values computed here are exactly the diagonal entries
of that corner Gram, so this work is consumed, not discarded, by
the full program.  Cloud only; Mac session-lock run owed; push of
this session's commits owed by Arthur.

**Next attack.**  (1) The corner-amplitude factorization proper:
the off-diagonal corner Gram entries via the same OS structure
(the cut Hilbert space is now concretely populated by these
diagonal norms).  (2) Cheaper diagonal evaluation (the contraction
order in network_value_fixed is generic; a cut-adapted elimination
order should collapse the 900s+ cases) — every landed value
extends the certified window mechanically.  (3) At the meeting
ground: iterate blocking (M -> infinity windows on the ITERATED
map) once the one-step window reaches s ~ 0.8.

### 16i. Addendum (2026-07-28, same session): the certified boundary walks to s = 9/16; the blocker is NAMED — network-value evaluation technology, not bounds

Executes the §16h queue.  Artifacts: `computations/su2_cut_eval.py`
(cut-adapted contraction: corner-sweep + layer-staged orders, gated
correct against the greedy engine incl. an off-diagonal negative
config), `computations/su2_m2_finality.py` (direct M=2-finality
values + CS-sharpened U_2 + the COMBINED window assembly),
`computations/su2_combined_windows.json`,
`tests/test_cut_eval_finality.py`.  Suite 99/99 green (cloud).

**Certified windows (combined assembly: T_2 finality repair +
OS/CS level-3 tails + domination levels >= 4).**

    s = 1/2:    X_11 in [+0.258238, +0.258546]
    s = 11/20:  X_11 in [+0.251954, +0.312592]
    s = 9/16:   X_11 in [+0.177195, +0.392345]   <- NEW boundary
    s = 4/7:    misses by 0.004 in log units (lower end -0.004)
    s = 3/5:    closed by ~4x (tail11 5.9e-5 + U2-11 5.0e-5 vs
                T11 2.6e-5)

Every additional diagonal value extends the boundary mechanically
(re-run the assembly; no code change).  Workers were left running;
one more landing near the (1,1) mass owners tips s = 4/7.

**The honest negative findings (as valuable as the windows).**
(1) Corner-sweep and layer-staged elimination orders do NOT
collapse the heavy contraction class: on the reference 556 s
diagonal, greedy blows a 45 s budget, corner sweeps blow 240 s
budgets, a staged order OOM-killed a 7 GB container.  The orders
are CORRECT (gated) and occasionally useful, but the blowup is
intrinsic to the polynomial-elimination REPRESENTATION at spin 3,
not to the order.  (2) The M=2-unreached configs and their diagonal
partners share the same hard (q, w) skeletons — that is WHY they
were unreached at 300 s in §15i: e.g. the all-walls-active patterns
q=(0,1,1,1), w=(1,2,2,1) time out at 600-900 s from every order
tried.  CONSEQUENCE, sharply: the certified window's advance past
s ~ 0.57 is blocked on ONE named technology — recoupling-based
(6j/transfer) evaluation of the slab network values — which is the
same object as the corner-amplitude factorization: one derivation
buys both the fast evaluator and the true transfer weights.

**Honesty.**  All new values exact; timeouts recorded, never
consumed.  The landed direct M=2 values (if any) are kept in a
separate ledger; dp3_m2_entries is never modified.  The OS/CS
lemma consistency of every landed direct value against its
diagonal partners is a standing pin.  Cloud only; Mac session-lock
run owed; push owed by Arthur (`git push origin main`).

**Next attack (converged to one object).**  The recoupling
evaluator: resolve the slab network into the D4 corner basis
(intertwiner labels on the four radial cuts + the central 4-valent
vertex), evaluate corner amplitudes as small 6j-assemblies
(`computations/wigner_6j.py` has the primitives), gate against the
~40 banked exact network values (incl. negatives), then (i) every
heavy diagonal and unreached M=2 config lands in milliseconds,
(ii) the certified window runs to the s ~ 0.8 meeting ground,
(iii) the domination transfer upgrades to the TRUE corner transfer
— the M -> infinity dichotomy instrument.  This is now the single
critical-path item of MD.2.

### 16j. Addendum (2026-07-28, same session): THE WALL FALLS — the Rust contraction engine plus the D4-orbit tactic land the entire blocked tier; the certified boundary marches to s = 3/5 with a six-decimal window at s = 1/2

Executes §16i's "single critical-path item" in its pragmatic form:
not yet the recoupling evaluator, but a faithful Rust port of the
exact_haar_network hot core (p_mul, integrate_link, p_reduce_units,
greedy elimination + the pair-premerge fallback; num-bigint exact
rationals, packed byte-vector monomials — the Python dict/Fraction
representation §16i identified as the wall costs ~20-50x more per
monomial).  Factors still constructed by the gated Python path;
only the contraction crosses the boundary (JSON, big-int strings).
Artifacts: `rust/haar_contract/` (crate),
`computations/su2_rust_eval.py`, `notes/rust-haar-engine.md`,
`tests/test_rust_eval.py`, updated ledgers
(`su2_cs_diagonals.json`: 59 exact diagonals;
`su2_m2_finality.json`: 30 direct M=2-unreached values, ZERO
timeouts remaining in the resolved set;
`su2_combined_windows.json`).  Suite 103/103 green (cloud).

**Gates (all green).**  The full banked-value battery: D4-gate
values, every listed SIGNED negative config of dp3_m2_entries for
(1,1), (0,1), (1,2) — sign and magnitude exact — and
Python-computed CS-ledger diagonals.  Standing pins: every landed
direct value satisfies the OS/CS lemma against its diagonal
partners; every diagonal is >= 0.

**The wall, before/after.**  Python-greedy 556 s -> Rust 61 s;
gate cases 24-40 s -> 0.4-11 s; the all-walls-active M=2-unreached
class (NEVER landed in Python at any budget) -> 78-203 s.

**The D4-orbit tactic (a discovery about the engine, banked).**
Contraction cost is wildly REPRESENTATIVE-dependent along the D4
orbit while the value is invariant (gated §16h): configs that OOM a
7 GB container in the canonical labelling land in SECONDS after a
cyclic rotation — observed extremes: fail-at-424 s -> 1 s (rot2);
OOM -> 39 s (rot1).  The sweep's rotation-fallback turned the
resistant families (q=(0,1,1,1) w=(1,2,2,1); w=3 walls) into
routine 10-100 s evaluations.  Consequence: U_2(1,1) fell from
5.0e-5 to 6.9e-7 (18 -> then all mass-relevant configs resolved),
U_2(0,0) to 1.7e-8, U_2(0,1) to 1.1e-6, and the binding level-3
tail collapsed key by key.

**Certified X_11 (M -> infinity) windows — the march.**

    s = 1/2:    [+0.258391, +0.258393]   (2e-6 wide: six decimals)
    s = 11/20:  [+0.282335, +0.283082]
    s = 9/16:   [+0.288564, +0.291908]
    s = 4/7:    [+0.291080, +0.300836]   (was: missed by 0.004)
    s = 3/5:    [+0.154922, +0.455443]   <- NEW boundary, tau = 0.51

The certified values RISE with s (0.258 -> 0.29+), tracing the
nonperturbative curve toward the flat-series regime.  s = 5/8
remains closed by ~3x (tail11 1.7e-4 vs T11 ~ 7e-5): the residual
is now spread over many small level-3 leftovers, the level >= 4
domination rest, and the remaining ~30 low-mass unresolved configs
— all mechanically extendable with more sweep time; the recoupling
evaluator remains the structural fix for the deep-s run to 0.8.

**Honesty.**  The Rust engine is gated against every banked exact
value but is NOT formally verified — scaffolding in the §16d
sense; its outputs enter windows only as exact rationals with the
OS/CS-lemma pins standing over all of them.  Budget misses recorded
as unreached, never consumed.  dp3_m2_entries never modified
(finality values in their own ledger).  The certified domain still
does not overlap the tau-series domain (tau = 0.51 vs the series'
tau <~ 0.3 usefulness) — the meeting is closer but not closed.
Cloud only; Mac session-lock run owed; push owed by Arthur
(`git push origin main`).

**Next attack.**  (1) Keep the sweep grinding (mechanical boundary
extension toward 5/8; every value counts).  (2) The recoupling
evaluator for the deep run — now an optimization, not a blocker;
its gate set has grown to ~90 banked exact values.  (3) With the
one-step window at rising s: the ITERATED map (blocked kernel of
the blocked kernel) with the same window machinery — the dichotomy
instrument proper.  (4) The D4-orbit cost anisotropy deserves a
recorded explanation (likely the greedy's interaction with the
tree-gauge asymmetry) — understanding it may yield another 10x.

### §16k — the Λ-cap repair, complete OS/CS coverage, and the first kernel-checked OS/CS certificate (2026-07-28/29, cloud)

**Executed.**  Three advances in one stage: (1) the Λ-slop of the
domination transfer identified as pure union-bound slack and
removed by raising the cap; (2) the diagonal-partner sweep run to
COMPLETION — every landed off-diagonal now has both OS/CS partners
landed; (3) the OS/CS structure itself banked as a generated,
kernel-checked, axiom-free Lean certificate (the Rust engine's
outputs entering the formal development for the first time).
Code: scripts/gen_oscs_lean.py (generator),
dual_kappa_spike/OSCSLedger.lean + lean/OSCSLedger.lean (generated
certificate, sixth spike target), tests/test_gen_oscs_lean.py
(3 pins); ledgers su2_cs_diagonals.json (97 landed / 20 unreached,
shards consolidated), su2_m2_finality.json (40 landed / 1
unreached), su2_combined_windows.json (regenerated, lam = 8).
Suite: 106/106 green (439 s, cloud).

**The Λ-cap repair (one parameter, half the gap).**  At s = 5/8 the
(1,1) entry's obstruction decomposed as U2res 4.0e-5 + lvl3 7.1e-5
+ rest(>=4) 1.7e-5 + Λ-slop 4.0e-5 against T = 7.3e-5.  The slop
at Λ = 6 is the union bound over label escapes; at Λ = 8 it falls
to 2.8e-12 — eleven orders — while the dominated rest is UNCHANGED
(the level >= 4 mass is already inside the cap).  The Λ = 6
default was slack, not structure: combined_x11_window now defaults
lam = 8.  This single change moved the positive-window boundary
from s = 3/5 past s = 8/13 before any new value landed.

**The partner sweep (19/19, zero misses).**  The 19 diagonal keys
demanded as OS/CS partners by landed off-diagonals but absent from
the ledger (14 never tried, 5 previously failed at 300-900 s
budgets) ALL landed under the Rust engine with the D4-rotation
fallback — 71 s to 586 s each.  Meanwhile the need-ranked sweep
landed 16 more level-3 diagonals (all first-try, no budget miss
this run: the §16j resistant class is now routine).  Ledger state:
97/117 level-3 diagonal keys landed; 40/41 M = 2 finality targets
landed (the one residual is the §16i triple-wall-3 config).

**Complete OS/CS coverage.**  Every one of the 40 landed direct
off-diagonal values now has BOTH diagonal partners landed, and
every one satisfies N^2 <= D_a * D_b — the lemma pin holds with no
exceptions across the full banked ledger, 7 signed rows included.

**OSCSLedger.lean — the Rust results enter the formal tree.**  The
directive "use the Rust learnings to help the formal Lean" lands
as a generated certificate in the DP6Ledger/DP3M2Ledger
convention (exact rationals as (Int, Nat), comparisons
cross-multiplied into Int, kernel `decide` on closed integer
arithmetic, no Mathlib, standalone spike target).  What the kernel
checks, per generated theorem:

  - diag_nonneg: all 97 landed reflection-diagonals >= 0 — OS
    positivity is a PREDICTION of the Osterwalder-Seiler norm
    structure, and the computed values comply (7 off-diagonals are
    negative, so this is not an evaluator triviality);
  - cs_bound_all: N^2 <= D_a * D_b on all 40 rows;
  - cs_partners_located: the PAIRING IS REDERIVED, not
    transcribed — d4Images implements the D4 action on
    half-configuration keys inside Lean and the kernel checks each
    cited partner value sits in the diagonal ledger at a D4 image
    of the key the lemma demands;
  - diag_le_crude / m2_le_crude: the crude bound
    |N| <= d_n d_m prod_f d_f with the face product rederived from
    the labelling — the domination-transfer input of §16g, checked
    on every landed value;
  - m2_negative_count / cs_includes_signed: the sign census (7
    rows, 6j interference) — the inequality is exercised on signed
    data.

Verification (cloud, per the spike's 2026-07-26 precedent): pinned
toolchain v4.29.1 (container install), elaborates in 6.9 s, all 10
theorems AXIOM-FREE (#print axioms empty — stronger than the
{propext, Quot.sound} budget), mutation-tested (negating a
diagonal breaks exactly diag_nonneg + the location of its citing
rows; corrupting a partner value breaks cs_partners_located +
cs_bound_all; inflating N breaks cs_bound_all; count literals
load-bearing).  A Mac-side `lake build` of the six spike targets
under the session lock is OWED, not claimed.

**Certified X_11 (M -> infinity) windows — the march (lam = 8).**

    s = 1/2:    [+0.258392, +0.258392]   (7e-7 wide)
    s = 11/20:  [+0.282612, +0.282805]
    s = 9/16:   [+0.289793, +0.290682]
    s = 4/7:    [+0.294655, +0.297282]
    s = 3/5:    [+0.274282, +0.356372]   (was [+0.155, +0.455])
    s = 61/100: [+0.177639, +0.451456]   CERT
    s = 8/13:   [+0.028179, +0.558919]   <- NEW CERT boundary
    s = 31/50:  window [-0.27, +0.70], positive, ratio open
    s = 5/8:    window [-1.36, +0.94], positive, ratio open

The ratio > 1 certificate now reaches s = 8/13 ~ 0.615 (tau =
0.486); positive windows reach s = 5/8 (tau = 0.470) — the §16j
target "extend toward 5/8" is MET at window level.  The certified
curve holds its ~0.29 plateau through s = 4/7 before the
tail-driven widening — the nonperturbative X_11 stays firmly above
the U(1) mirror's 0 with margin growing along the whole certified
range.

**Honesty.**  The Rust engine remains gated-but-not-verified
scaffolding (§16d convention); what the Lean kernel now certifies
is the OS/CS STRUCTURE of its outputs (positivity, the CS
inequality, the crude bound, the D4 pairing), not the contraction
that produced them — re-deriving the values inside Lean from the
finite-product-Haar spine is the standing wiring TODO shared with
the other spike ledgers.  D4 value-invariance is an input fact
(gated numerically over the banked battery); the ACTION is what
Lean rederives.  Budget misses recorded unreached, never consumed
(20 + 1 stand).  Mac lake build owed; push owed by Arthur.

**Next attack.**  (1) The 20 residual diagonals (hard class:
900 s+ budgets or the recoupling evaluator) — each landing
tightens lvl3 at 31/50 and 5/8 toward CERT.  (2) The recoupling
(6j/corner-basis) evaluator, gate set now 137 banked exact values.
(3) The iterated-map windows on the rising one-step boundary — the
dichotomy instrument proper.  (4) Lean: extend the certificate to
the WINDOW inequality itself (DomTransfer trace + geometric tails
are finite rational data — the s = 1/2 window is one big
kernel-decidable rational inequality), and the D4-anisotropy
explanation.

### §16l — WindowLedger.lean: the certified X_11 windows replayed by the Lean kernel (2026-07-29, cloud)

**Executed.**  The §16k queue's Lean item — "the window inequality
itself is one big kernel-decidable rational inequality" — done.
Code: scripts/gen_window_lean.py (generator),
dual_kappa_spike/WindowLedger.lean + lean/WindowLedger.lean
(generated certificate, seventh spike target),
tests/test_gen_window_lean.py (3 pins).  Suite: 109/109 green
(539 s, cloud, sweep paused).

**What the kernel now replays (not transcribes).**  For each of
nine grid couplings s = a/b:

  - T[n,m](s) ASSEMBLED in-kernel: the M = 2 census polynomial
    evaluated at the exact rational coupling (evalNum precedent)
    PLUS the resolved-config rows with assembly weight W and
    exponent E rederived from the labelling — the same
    rederivation discipline as DP3M2Ledger/OSCSLedger, now driving
    the actual certified-window pipeline;
  - the unresolved-mass bound U from the SAME labelling: 22 crude
    rows fully rederived (W * cN, cN = d_n d_m prod d_f); 17 CS
    rows via cited r with r >= 0 and r^2 >= D_a * D_b
    kernel-checked and the cited partner values kernel-LOCATED in
    the cited diagonal ledger through the D4 action — no citation
    trusted;
  - lo = T - U - tail > 0 entrywise at ALL nine grid points
    (windows_positive), and lo11 * lo00 > hi01^2 at the seven CERT
    points (x11_ratio_certified): X_11 > 0 kernel-certified at
    s = 1/2, 11/20, 9/16, 4/7, 3/5, 61/100, 8/13.

The kernel-checked statement is exactly the §16k boundary: the
blocked SU(2) one-step observable X_11 = log(T11 T00 / T01^2)
strictly positive through s = 8/13 — where the U(1) mirror is
exactly 0 — plus window positivity (ratio open) at 31/50 and 5/8.

**Honesty (what remains transcribed).**  Census polynomials
(dp3_m2_entries; the T[1,1] final part's internal assembly is
independently banked in DP3M2Ledger), landed N values and cited
diagonals (the gated engines; independently kernel-checked for OS
positivity + CS in OSCSLedger), and the tail bounds (level-3 CS
tail + domination >= 4 + Lambda-slop at Lambda = 8, computed by
the gated Python and rounded UP to 10^-60 — validity-preserving).
The licensed mathematical inputs are the OS/CS lemma and D4
value-invariance.  Rederiving the tails needs the DomTransfer
trace and the certified geometric sums in Lean — the next rung;
rederiving N needs the finite-product-Haar spine — the standing
wiring TODO.

**Verification.**  Cloud, pinned v4.29.1: elaborates 7 s, all 10
theorems AXIOM-FREE, mutation battery clean (negating a census
coefficient or inflating a tail breaks windows_positive +
x11_ratio_certified; corrupting a cited diagonal breaks the
cs_valid* of the citing entry; shrinking r below sqrt(D_a D_b)
breaks its cs_valid*; counts load-bearing).  Mac lake build of the
seven targets under the session lock OWED, not claimed.

**Meanwhile.**  The 1800 s-budget hard sweep grinds the 20
residual diagonals (none landed yet this run — the class is hard
at any budget; the recoupling evaluator remains their structural
fix).  Next attack: (1) the hard residuals / recoupling evaluator;
(2) Lean-side: DomTransfer + geometric tails in-kernel (removes
the largest transcribed literal), then the iterated-map windows;
(3) the D4 cost-anisotropy explanation.

## §17 — Dijkstra from the Clay gates: route audit and reprioritization (2026-07-29)

This section re-runs the backward search of the 2026-07-20
completion-first graph from scratch — starting at the literal Clay
gates, relaxing backward over theorem-space with known proof
technologies as edges — and compares the geodesic it finds against
the current execution front (§§15–16l).  It supersedes the §16l
next-attack list as the priority ranking; it does not modify any
guarded statement, milestone definition, or honesty verdict.  The
2026-07-20 C-graph and the 2026-07-26 route-forward synthesis both
survive this audit intact; what changes is the ORDER of attack
inside the MD program and the allocation of Lean effort.

Web usage note (campaign fence respected): public search was used
only for standard published methods and their endpoints — the
Balaban/Dimock UV-stability literature, the constructive-YM survey
material in Chatterjee's free-energy paper, Osterwalder–Seiler
reflection positivity, and the abelian 4D Coulomb-phase anchors
(Guth, Fröhlich–Spencer) grounding the U(1) discriminator.  It was
NOT used to search for a solution to the problem or to adjudicate
its status; encountered items claiming full solutions were not
read, per the prompt.

### 17.1 The gate graph, refreshed

Backward from the boxed terminal statement:

    G0  terminal: for every compact simple G — existence on R^4 at
        Wightman/OS strength + mass gap Delta > 0, machine-checked,
        axiom-clean.                                  [= C0, MISSING]
    G1  OS reconstruction + physical spectral pin: reflected
        positive-time carrier, semigroup, generator, located edge.
        Technology STANDARD (OS I/II, GNS); constructive port is
        ENGINEERING, not research risk.       [= C4/C5, interfaces]
    G2  two-parameter continuum limit of the Schwinger family with
        uniform clustering: standard MODULO its inputs; all risk
        imported from G3.                                   [= C6a]
    G3  THE volume- and spacing-uniform physical-units gap.
        Feeds from three regimes:                        [= C6b–f]
          G5  IR anchor (strong coupling): located gap window
              [0, 2^{-1/3}), OS/Seiler technology — CLOSED at
              fixed spacing, unconditional.
          G6  UV envelope (s -> 1): the literature's endpoint here
              (Balaban 1983–89; Dimock's re-derivation; MRS;
              Federbush) is UV STABILITY OF THE PARTITION FUNCTION
              on the torus — free-energy bounds only.  It does NOT
              deliver correlators, a gap, or the continuum
              Schwinger family, and the surveyed field stalled on
              exactly that.  The program's reduction of this gate
              to a TWO-SIDED MARGINAL ENVELOPE on a derived
              finite-dimensional flow map (MD.3) is therefore a
              genuine shortening IF the envelope lemma is
              provable; BF4 §9's necessity theorem shows no route
              avoids some trajectory hypothesis.
          G4  crossover (weak -> strong): NO published technology
              crosses it; strong-coupling gaps and weak-coupling
              stability have coexisted unconnected since the
              1980s.  The three-regime decomposition (anchor /
              compact Sturm atlas / marginal envelope) remains,
              on this audit, the shortest known path — the
              program's own contribution, still unpublished
              anywhere else as far as the fence permits knowing.
    G7  all-group uniformity: R1 worst-case spine to SU(2) (built,
        modulo the character-tail interface debt) + the (h_vee,
        Delta) parameterized defect coefficient.            [= C1]
    G8  nontriviality / local fields / stress tensor / OPE / AF
        asymptotics: real obligations, downstream CONSUMERS of the
        same tower (BF7–BF10).                          [= C2, C3]

Geodesic: G5 (closed) + MD.2/MD.3 envelope (G6) + MD.4 atlas (G4)
-> (TS) -> five-holonomy Perron budget -> G3 -> G2 -> G1 -> G0,
with G7 riding the R1 spine and G8 consuming the tower.  This is
the route the plan already holds.  The audit's findings are about
WHERE ON IT the effort currently sits.

### 17.2 Findings — where execution left the geodesic

**F1 (order inversion in the middle regime).**  MD.4's atlas is
defined by its RIGHT edge s_* — the validity edge of the MD.3
envelope — which does not exist yet, because the envelope lemma
has not been attacked.  Meanwhile §§16h–16k marched the atlas's
LEFT edge (s = 1/2 -> 8/13 CERT) at a cost per Delta-s that grows
exponentially (the evaluation wall; the §16j Rust engine bought
one increment, the §16k sweep another).  Dijkstra's rule: never
push the expensive frontier before the cheap defining edge is
placed.  The certified one-step atlas at s <= 8/13 is ALREADY
sufficient anchor-side overlap for any plausible s_*; further
mechanical s-marching is off-geodesic beyond ~31/50.

**F2 (missing edge: one-step windows are not the (TS) object).**
(TS) constrains the TRAJECTORY — iterated blocking — while every
certified window so far is one blocking step deep.  The iterated
map (blocked kernel of the blocked kernel, same window machinery)
has been queued since §16j as "the dichotomy instrument proper"
and has slipped behind mechanical sweeps three times.  It is the
actual edge between the atlas and (TS).

**F3 (the envelope gap is the certified-domain gap).**  §16j
recorded it precisely: the certified instrument reaches tau =
0.51 while the tau-series (tau^2 + tau^3 exact law, §16g) is
useful only for tau <~ 0.3, and the domains do not overlap.  The
MD.3 envelope lemma IS the closure of this gap: a certified
remainder bound for the series (eps_img-style, §16g already built
the per-face image certificate) meeting the certified windows.
This is the one place Balaban-grade hardness now concentrates,
and it is currently receiving zero attention.

**F4 (Lean allocation).**  OSCSLedger + WindowLedger (§§16k–16l)
are the right transport discipline, but their remaining wiring
TODOs (tails in-kernel, Haar-spine rederivation of N) deepen
already-certified layers — engineering with no G4 shortening.
The geodesic Lean items are MD.5's: the AFEnvelope inhabitant
path, the atlas-adequacy lemma STATEMENT, and gen_md_lean.py.

**F5 (idle hedge lane).**  G1 is on the critical path, independent
of G4, and pure engineering — and is currently idle.  If G4
lands, G1 instantly becomes the bottleneck.  A low-intensity
standing lane (PositiveTimeOSRoot semigroup/generator
formalization; the R1 character-tail interface debt for G7)
converts dead waiting time into critical-path progress at zero
cost to the front line.

### 17.3 The reprioritized queue (supersedes §16l's list)

    P1  MD.2-weak + MD.3: the s -> 1 envelope.  Certify the
        series remainder (eps_img technology on the tau^3 law;
        both MD.1 matchings; U(1) mirror in the same harness;
        scheme-covariance check) and extract the two-sided
        envelope 1 < tau'/tau <= 1 + c*tau with explicit
        rational (c, s_*).  THE front-line item.
    P2  Iterated-map windows: the certified-window machinery on
        the twice-blocked kernel at s in the banked atlas range;
        first certified statement about the TRAJECTORY, and the
        consumer-side test of P1's envelope.
    P3  Overlap closure: chain P2's iterated windows to P1's s_*
        (the atlas-adequacy lemma, stated then proved).  MD.4
        completes here — by meeting s_*, not by marching s.
    P4  MD.5: AFEnvelope inhabitant -> BareAFImpliesLinearFloor
        -> (TS) -> five-holonomy Perron budget.  ALL new Lean
        effort lands here (gen_md_lean.py in the spike
        convention) until P1–P3 move.
    P5  Standing hedge lane (low, steady): G1 semigroup/generator
        engineering; R1 character-tail interface.
    P6  Background only (CPU, not attention): the 20 residual
        hard diagonals; the recoupling evaluator (promote only if
        P2 hits the evaluation wall at depth 2); Pin- DECIDER
        (shaft 2, capped).

    De-prioritized explicitly: one-step s-marching beyond 31/50;
    new certificate layers over already-certified strata; DP
    strata enumeration; BF5 grading.  Each waits on P1–P4.

### 17.4 Fences (restated for the new front)

The U(1) mirror runs at every P1/P2 stage (4D compact U(1) is in
its Coulomb phase at weak coupling — any mechanism blind to the
group proves false statements; the exact c_SU2 - c_U1 = +21/8
separation at order tau^2 is the model of admissible evidence).
Scheme covariance of the envelope sign across both MD.1 matchings.
The anti-loop rule: P1's deliverable is a certified envelope with
explicit rationals, not a renamed (TS).  No-circularity: the scale
is set by observable matching, never by the desired mass.  Budget
misses recorded as UNREACHED, never consumed.  All prior guarded
statements unchanged.

### §17a — P1 stage one EXECUTED: the envelope lemma is inhabited (2026-07-29, cloud)

**The theorem (first inhabitant, discriminator form).**  Explicit
rationals K_X and tau* = 2^-82 such that, for ALL 0 < tau <= tau*:

    | X_11(tau) - 6 tau^2 - (115/6) tau^3 |  <=  K_X tau^4,

whence X_11 > 0 on the whole interval (monotone margin K_X tau^2 <=
3 < 6) and the two-sided envelope X_11 in 6 tau^2 (1 +- rho(tau)),
rho = (115/36) tau + (K_X/6) tau^2, on (0, tau*] — the
anti-screening sign of the derived one-step flow certified on the
weak-coupling interval (s*, 1), s* <= explicit rational < 1.
Artifacts: computations/su2_envelope.py + ledger,
tests/test_envelope.py (4 pins).  Suite 113/113 (490 s, cloud).

**Method (the eta-variable master lemma).**  eta = sqrt(8 tau) as
the ANALYTIC variable: on the scaled fields x = eta M xi the
action's cubic+ parts pair their 1/(8 tau) with x^3 ~ eta^3, so
every insertion is a POSITIVE power of eta at fixed xi and the
essential singularity of the naive x-expansion disappears.  Then:
small-field eta-Taylor tail by Cauchy on |eta'| = r0/(cM |xi|)
with M(xi) <= A0 e^{|xi|^2/4} once r0 <= 1/(4 g3 cM^2) (the
insertion sup is <= |xi|^2/4 at the domain edge — the small-field
analyticity mechanism made explicit), closed by the exact
variance-2 moment E[|xi|^8 e^{|xi|^2/4}] = 2^{d/2+4} d(d+2)(d+4)
(d+6), d = 48; large field by real-domain positivity + Gaussian
tail at the half-radius split; images by the per-face bound glued
multiplicatively (tiny-tau lane: certified j-image exponent
pi delta j / tau, avoiding large-exponent internals); log
composition 4u/(1-u).  Exponential classes dominated SYMBOLICALLY
on all of (0, tau*] by exp_le_power (e^y >= 2^y + doubling
induction; no caps in the theorem).  Slab constants exact:
cM^2 = 367/96 < 4 asserted against the complex; crude BCH
majorants G3 = 64, G4 = 1024, A0 = 4*2^20, r0 = 1/1024.

**Gates.**  (g1) fusion-star remainder-scaling gate: the exactly
known F_1(tau) = sum (2J+1) e^{-tau C(2J)} deviates from its
two-term flat model by 0.234-0.238 tau^2 across a dyadic grid —
the remainder sits exactly one order beyond the kept terms, the
inequality class the master lemma asserts.  (g2) parity per the
banked evenness.  (g3) exp_le_power soundness both directions.

**Honesty.**  K_X ~ 3.8e49 and tau* ~ 2.1e-25 are ABSURD and
NONEMPTY — crude constants by design; the deliverable is the
inhabited lemma, the first two-sided certified envelope of the
program.  The 1 < tau'/tau <= 1 + c tau MATCHED-FLOW form still
requires the diagonal kappa_3 (open) or the iterated-map route
(P2).  U(1) discipline: the discriminator does NOT survive
d_n == 1 — for U(1) the same machinery bounds |X_U1| <= K tau^4
around ZERO series (X2 is the SU(2)-specific input); positivity is
not produced abelian-ly.  A1 flat-limit interchange: discharged at
the X-observable BY this bound (stage one); the BCH majorant
constants are crude-certified, their per-face sharpening named.
Sharpening routes (ranked): per-face g3 (est. 10^2-10^3 on K_X),
component factorization d 48 -> 16 (2^16), tau^4 cross law (turns
rho's tau-linear term sharp), A0 via face-factor cancellation.
Cloud only; Mac lake run unaffected (no Lean in this stage); push
owed by Arthur.

**Next attack.**  (P1 stage two) sharpen (K_X, tau*) toward the
atlas range by the ranked routes; (P2) the iterated-map windows —
now with BOTH ends bounded: certified windows to s = 8/13, the
envelope on (s*, 1); (P3) the atlas-adequacy statement consuming
both.

### §17b — P1 stage two EXECUTED: envelope constants sharpened from the exact complex; a stage-one face-sum under-count FOUND AND REPAIRED; the U(1) mirror separation certified (2026-07-29, cloud)

**The repair (honesty first).**  §17a's smallness condition r0 <=
1/(4 g3 cM^2) used g3 = 64 as a GLOBAL cubic majorant for the action
remainder on the Cauchy circle; the per-face cubic majorants of
phi_f^2 - theta_f^2 SUM over the 20 faces to more than 64 |x|max^3 —
the released stage-one constants (K_X ~ 3.8e49, tau* = 2^-82) were
derivation-unsound.  The exact accounting both exposes and rescues
this: the cubic 2 theta.Delta_2 is a sum of scalar triple products
x_k.(x_i x x_j), which VANISHES IDENTICALLY on every face whose word
has <= 2 distinct links — 16 of the 20 faces (13 two-letter + 3
one-letter).  The four surviving faces carry at most G3_TOT = 39/2
triple-product terms; quartic-and-higher close IN ALL ORDERS under
the positive-coefficient Dynkin majorant with QHAT = 5/2 certified on
sigma <= 1/50 (q_hat(1/8) ~ 2.74 > 5/2 — the domain assert is
load-bearing and pinned by a test).  Repaired stage one: r0 = 1/390
(> 1/1024: the under-count and the unexploited vanishing structure
more than cancel), K_X = 1.663e46, tau* = 2^-76 — sound, and SHARPER
than the unsound release.  su2_envelope.py carries the repaired
literals + REPAIR docstring; ledger regenerated.

**Stage two (computations/su2_envelope2.py).**  Three certified
replacements, exact slab data throughout (c_e^2 >= (G^-1)_ee by
isqrt; T3 = 50.851 over the 4 carrier faces; S4 = 4524.5;
s_max = 6.117):
  (1) exact per-face insertion budget
      (r0/cM) T3 + qhat (r0/cM)^2 S4/2 <= kappa (no G4 layer);
  (2) reweight exponent OPTIMIZED: kappa = 1/9 (stage one hard-wired
      1/4 at cost 2^28 in E[|xi|^8 e^{kappa|xi|^2}]);
  (3) A0 by xi-UNIFORM circle bounds (every ||x'_e|| <= r0 on the
      circle): A0 = 4.0198 vs stage one's 4*2^20.
RESULT:  |X_11 - 6 tau^2 - (115/6) tau^3| <= K_X tau^4 on (0, tau*],
K_X ~ 3.799e33, r0 = 3853/2^20, tau* = 2^-55, s* <= 1 - 2^-55 +
2^-111 exact — a 2^27 certified-domain gain over the §17a release
with soundness restored, X_11 > 0 and the two-sided envelope on all
of (0, 2^-55].

**The U(1) mirror lane (the §17.4 fence, executed).**  Identical
machinery, one abelian component (§16f g4 convention): abelian =>
Delta S == 0, no Jacobians, entire main branch, kappa = 0 — the
lane's constants are tiny (K_U1 ~ 7.67e6):
    |X_U1(tau) + 8 tau| <= K_U1 tau^4  on (0, tau*],
linear term -8 (G^-1)_{t,b} tau with (G^-1)_{t,b} = 1 exact,
kappa_2 = kappa_3 = 0 the banked §16f/§16g mirror gates.  CONSUMED:
the certified two-sided separation on the COMMON interval

    X_SU2(tau) > 0 > X_U1(tau)   for all tau in (0, 2^-55]

— anti-screening vs screening, nonperturbative on the interval.
Scheme covariance of the mirror sign gated against the second banked
U(1) instrument (theta kernel, Qmin = 3n^2+3m^2+2nm): engine/theta
conversion EXACTLY 4 on diagonal (12 vs 3) and cross (8 vs 2).

**Gates (all green).**  g_cubic (vanishing lemma + triple-sum bound
on exact rational vectors; Delta_2 independently vs mpmath matrix
logs), g_dynkin (certified bounds dominate mpmath), g_repair
(repaired literals vs the exact complex, incl. q_hat(1/50) <= 5/2),
g_mirror (Ginv_tb = 1, Qmin form, factor 4, banked kappa zeros,
X2/X3 literals), g_star (§17a mechanism gate), g_dominate (stage two
strictly beats repaired stage one).

**Verification.**  Cloud.  tests/test_envelope2.py (5 pins incl. the
q_hat domain trap) + test_envelope.py (4) green; MD-era subset 182
passed / 4 skipped (rust engine unbuilt in this container).
Full-tree pytest: 756 passed / 20 failed / 4 skipped — the 20 are
PRE-EXISTING stale pins in Phase 1-4-era files (test_chaining_eta*,
test_continuum_limit, test_long_k_trajectory, test_mass_gap_bound,
test_q_lift; May c_lambda-change and old K-trajectory pilot drift),
none importing anything touched here; recorded, not repaired.
pyproject.toml: `slow` marker registered (bare-container collection
under --strict-markers errored on test_dp3_m2.py).  Mac session-lock
run unaffected (no Lean in this stage); push owed by Arthur.

**Next attack.**  (P1 stage three, ranked) polydisc Cauchy in
per-face variables — removes the global 1/|xi| radius shrink, the
dominant structural loss; tau^4 cross law (remainder -> tau^5, rho's
linear term sharp); D4-class tightening of T3.  (P2) iterated-map
windows, now with both ends bounded.  (P3) atlas-adequacy statement.
The matched-flow form 1 < tau'/tau <= 1 + c tau still awaits the
diagonal kappa_3 or the P2 consumer — not claimed here.

### §17c — P1 stage three EXECUTED: the MAJORANT-SERIES envelope — tau* = 2^-44 — plus a second stage-1/2 constant repair (2026-07-29, cloud)

**The route decision (supersedes the §17b ranking, with reasons
banked).**  The §17b next-lever list read: polydisc Cauchy, then the
tau^4 cross law, then P2.  The stage-three analysis showed (i) the
naive polydisc keeps the (1/radius)^8 penalty in max-of-local-fields
form — certified ceiling ~2^4-2^6; (ii) what both items are really
after is available directly: the MIDDLE Taylor coefficients a_k
(k = 8..N) of the entry function are plain global Gaussian moments
needing NO analyticity — bound each by an exact-rational majorant
and demote the Cauchy machinery to the ultra-tail (k > N).  This
subsumes the polydisc (per-face locality lives in the per-face
majorant factors) AND the tau^4 law (a certified BOUND on the tau^4+
coefficients is all positivity needs; the exact law remains open and
is now only an MD.4-curvature item).

**The machinery (computations/su2_envelope3.py).**  Positive-
coefficient majorant composition over the factorized integrand
(character x 16 Haar x 20 Jacobians x multi-letter exp(-g_f)):
per-face g-orders refined by the exact word structure — cubic
2 t3_f (zero on 16/20 faces, §17b), quartic p_f^2 + 2 s_f d3_f with
(p_f, d3_f) from the LABELLED BCH fold (repeated-link brackets
dropped), quintic mixed, >= sextic closed in all orders by the
Goldberg/Dynkin scalar series f(z) = -log(2 - e^z); z/sin z and
(sinh u/u)^2 compositions; monomial expectations closed by pooled
Hoelder into exact chi_3 moments (odd uppers via sqrt(2/pi) <= 4/5).
Log-composition via the majorant log Lambda; ultra-tail at order
N+2 by the stage-two (r0, kappa) machinery per order; large-field,
image, and the NEW LF-polynomial shells; (kappa, N) scanned.

**THE RESULT.**  |X_11 - 6 tau^2 - (115/6) tau^3| <= R_X(tau) on
(0, tau*] with **tau* = 2^-44** (N = 12, kappa = 1/9),
R_X(tau*)/tau*^2 = 0.875 <= 3, R_X/tau^2 nondecreasing => X_11 > 0
and the two-sided envelope on ALL of (0, 2^-44].  U(1) mirror:
R_X^{U1}(tau*) ~ 1.1e-44 << 8 tau* — the separation
X_SU2 > 0 > X_U1 stands on the common interval, with the mirror
majorants gated against the EXACT abelian coefficients (V-hat = 8,
4^j/j!).  Sound progression: 2^-82 (stage one) -> 2^-61 (stage two)
-> 2^-44 (stage three).

**REPAIR #2 (honesty).**  Stages one/two consumed the eta^8 Cauchy
tail as K_small tau^4, dropping 8^4 from eta^8 = (8 tau)^4.  Both
modules now carry ETA8 = 8^4 explicitly: stage one 2^-76 -> 2^-82
(coincidentally the §17a headline number, now sound), stage two
2^-55 -> 2^-61, mirror K_U1 -> 3.14e10.  Also made explicit: the
E[1_LF |poly-coeff|] piece of the large-field split (Cauchy-Schwarz
with L^2 majorants mL2_k) that stages one/two silently absorbed in
shell slack (~e^{-3e7} at their tau* — negligible, but ledgered).

**Gates (all green).**  g_fold (labelled majorants dominate the
exact vector BCH fold per face), g_dynkin numeric (mpmath matrix
logs + t-grading Vandermonde: exact grades 2-4 under a_k sigma^k on
the real face words), g_moments, g_series (positivity + z/sin z
Taylor match + haar domination), g_u1_exact, g_star, g_dominate.
Envelope tests 15/15 (three pin updates for the repairs); no other
suite file imports these modules.

**What binds now, ranked.**  (1) Lambda_8 itself: the pooled-Hoelder
step E[prod chi^a] <= E[chi^D] ignores monomial spread across
near-independent atoms (~1e4 at degree 16) — sharp product moments
(Wick/Isserlis trace formulas or a Cauchy-Schwarz tree) are the next
constant lever; (2) the large-field shell exp(-r0^2/(128 cM^2 tau))
caps ANY series improvement at tau ~ 2^-30±3 for budget-admissible
r0 — the fix is compact-domain (owned-boundary) large-field bounds,
i.e. image technology, not more orders; (3) the matched-flow form
awaits diagonal kappa_3 or P2.

**Next attack: P2 — the iterated-map windows** (the trajectory
instrument; both ends of the gap now bounded: certified one-step
windows to s = 8/13, the envelope on (s*, 1) with s* = e^{-2^-44}).
Then P3 atlas-adequacy.  Cloud only; no Lean this stage; push owed
by Arthur.

### §17d — P2 OPENED: the iterated-map windows — the raw depth-2 sign proved VACUOUS, the U(1) law pinned to four digits, and the first certified trajectory numbers (2026-07-29, cloud)

**The object.**  One blocking step = the banked slab kernel matrix
T[n,m](s) (character-basis pair moments).  The iterated map is
kernel composition through the shared boundary charge:
T_2[n,m] = sum_k T[n,k] T[k,m], g_k = 1 by character orthonormality
(SU(2): k >= 0; U(1): k in Z) — the transfer-semigroup square, the
two-step object the (TS) hypothesis constrains.  Gated: diagonal
heat-kernel toy composes to exact doubling; the U(1) exact lane
below pins the convention.

**The structural theorem (refutation-grade design fact).**  T real
symmetric => T_2 = T^2 is a GRAM matrix => Cauchy-Schwarz forces
X^(2) = log(T_2[1,1]T_2[0,0]/T_2[0,1]^2) >= 0 for EVERY group.  The
§17.4 mirror fence FIRES on the raw two-step cross sign: it cannot
discriminate SU(2) from U(1).  Quantified on the exact theta kernel:
at s = 1/2 the abelian one-step cross is certified NEGATIVE
(-0.3564) while the two-step is certified POSITIVE (+0.02545).
Continuum: min over the shared real charge gives Qmin_2 =
3(n^2+m^2) - (n+m)^2/6, cross -1/3, X_2^{U1} -> +tau/3; the
certified window at s = 9/10 lands on tau/3 to FOUR DIGITS
(3.5120e-2 = 3.5120e-2).  CONSEQUENCE: at even iteration depth the
discriminating trajectory content is the MAGNITUDE/matched-flow
structure, never the sign.

**The certified SU(2) trajectory numbers
(computations/p2_iterated.py; entry windows = the §16h-16l combined
assembly generalized to {0,1,2}^2 with the 4^{E/3} d-absorption for
label-less (2,2) unreached configs; k >= 3 truncation by DomTransfer
full traces (k <= 8) + the analytic corner floor (4^{1/3}s)^{f(k)},
f(k) = min_q(2C(q)+C(k-q)), on 4s^3 < 1).**
- s = 1/2:  X^(2)_SU2 in [2.04e-8, 7.16e-7], CERTIFIED POSITIVE —
  6-7 orders below the one-step 0.2584: the rank-one collapse of a
  strongly gapped step, certified at depth 2 (the two-step Gram
  angle is a spectral-ratio readout; the k = 0 channel dominates).
- DEPTH-2 MAGNITUDE SEPARATION, certified: X^(2)_SU2(1/2) <=
  7.16e-7 < 2.54e-2 = X^(2)_U1(1/2) — the SU(2) iterated kernel is
  ~5 orders closer to rank-one than the abelian mirror at the same
  coupling: the gapped-vs-Coulomb trajectory signature at depth 2,
  in exactly the observable class the vacuity theorem licenses.
- s = 11/20: [-8.8e-7, 4.07e-3] bracketed, sign not certified (the
  one-step entry windows there are ~1e-6-wide and square through);
  9/16 similar; 8/13 uninformative after squaring.  Mechanical fix:
  the standing background diagonal lane — every one-step tightening
  squares through the composition.

**Gates (all green).**  g_qmin (incl. the -1/3 continuum cross),
g_hk (semigroup doubling), g_u1_law (four-digit tau/3), g_scale
(collapse pin), g_separation (SU2 << U1 window comparison).  Tests
test_p2_iterated 4/4; envelope suite unaffected.

**Honesty.**  One composition step of the DERIVED kernels
(transfer-direction stack); the thickness-2 fine-scale census — the
blocking-vs-stacking defect — is the next rung (the §16 defect
frame).  The matched-flow tau'/tau windows at depth 2 (MD.1
matchings) are the designated consumer, not claimed.  (·,2) windows
crude but enter only at 1e-13 on the CERT range.  Cloud only; push
owed by Arthur.

**Next attack.**  (1) Certify the depth-2 sign at 11/20-9/16 via the
background diagonal lane -> the certified s-curve of the collapse
rate (the trajectory's gap curve).  (2) The matched-flow consumer:
tau'/tau windows at depth 2 under both MD.1 matchings against the
§17c envelope.  (3) The thickness-2 census when the recoupling
evaluator lands.  (P3) the atlas-adequacy statement now has both
instruments: envelope on (s*, 1) with s* = e^{-2^-44}, iterated
windows on the anchor side.

## §17e (2026-07-29): P2 CONTINUED — the depth-2 sign certified on the WHOLE CERT grid by the SOS/Lagrange route; entry-level OS Gram (mirror-pinned to the conjugated form); the crude closure upgraded to a theorem

Executes §17d's next-attack item (1) — and supersedes its mechanism:
the sign at 11/20 and 9/16 did NOT need the background diagonal
lane.  Artifacts: computations/p2_iterated.py (§17e layers in
place), regenerated p2_iterated_results.json, tests/test_p2_iterated
(7 tests), notes/p2-iterated-windows.md §17e.

**The SOS/Lagrange route (structural).**  T_2 = T^2 is the Gram
matrix of the one-step rows, so the two-step determinant is an
EXACT sum of squares of one-step 2x2 minors (Lagrange/Cauchy-Binet,
absolutely convergent under the dominated per-index bounds):

    det_2 = T2_00 T2_11 - T2_01^2 = sum_{k<l} M_kl^2,
    M_kl  = T[0,k] T[1,l] - T[0,l] T[1,k].

Every term is >= 0, so any finite minor family is a certified lower
bound — and the LEADING minor M_01 = T00 T11 - T01^2 is exactly the
one-step X11 object, certified positive on the whole §16l grid.
With X^(2) = log(1 + det_2/T2_01^2):

    r_lo = 1 + max(0, M01_lo)^2 / T2_01_hi^2 > 1

at EVERY grid point — the one-step gap converts directly into the
two-step sign, no new Haar values consumed.  The same identity with
per-index upper bounds U(j) (windows k <= 2, dominated 3..8, crude
l >= 9) gives the magnitude upper bound.

**Certified depth-2 collapse curve (final combined windows, X^(2)):**
1/2: [2.077e-8, 2.148e-8] (33x tighter than §17d); 11/20:
[2.519e-7, 1.671e-5] SIGN NEW; 9/16: [4.585e-7, 1.884e-4] SIGN NEW;
4/7: [6.963e-7, 1.055e-3] new point; 3/5: [1.909e-6, 3.008e-1] new
point; 61/100: [9.534e-9, --] sign only; 8/13: [2.665e-15, --] sign
now certified.  Depth-2 magnitude separation SU2 << U1 certified at
FOUR points (1/2, 11/20, 9/16, 4/7), extending §17d's single point
— the certified onset of the gapped-vs-Coulomb trajectory signature
along the anchor side.

**Entry-level OS Gram — and the mirror fence earning its keep.**
The slab weight factorizes across the reflection plane (W =
W_qw W_top W_bot), so the banked §16h config-level OS/CS lemma sums
bilinearly over the shared (q, w) sectors: T is an OS Gram matrix
and |T[n,j]| <= sqrt(T[n,n] T[j,j]).  This breaks the §17e
magnitude wall dom(1,3) = 9.8e-5 -> 5.5e-7 at 11/20 (the (0,3)
minor was the entire det_2 upper-bound budget).  THE U(1) LANE
REFUTED THE NAIVE FORM: on the exact theta kernel Qmin(n,m) =
3n^2+3m^2+2nm gives T[1,3]^2 ~ s^72 >> s^80 ~ T[1,1]T[3,3] —
aligned charges cost MORE on the slab (B^T u = -B^T w: the two disk
sources drive the flip lattice oppositely), so the raw matrix is
NOT PSD.  The OS reflection reverses the boundary loop: the Gram
object is T[nbar, m], and conjugating one side restores CS exactly
(Qmin(-1,3) = 24: s^48 <= s^40).  SU(2) is self-conjugate
(chi_nbar = chi_n), so the sharpening consumed by u_abs_bound is
sound as stated.  Gated exactly on the abelian lane in conjugated
form WITH a teeth check (the unconjugated form must fail — it
does).

**The crude closure is now a theorem, not a convention.**  The
corner floor satisfies the convexity sandwich f_real(k) <= f(k) <=
f_real(k) + 3 with f_real = (2k^2+8k-1)/3 (real minimizer q* =
(k-1)/3, g'' = 6, integer offset <= 1; instances asserted at every
evaluation), hence df(k) >= (4k+1)/3 for EVERY k, hence the uniform
cube-ratio bound (c(l+1)/c(l))^3 <= ((L+2)/(L+1))^3 64
(4s^3)^{ceil((4L+1)/3)} — exact rational arithmetic throughout.
The adaptive anchor L(s) (smallest L with ratio-cube <= 1/8; L = 9
at s = 1/2 ... 67 at 8/13) makes every l >= 9 closure an exact
segment sum plus a geometric tail with ratio <= 1/2, valid for the
WHOLE tail.  (The first §17e attempt asserted per-l halving of
single crude values — REFUTED at s = 3/5, and the checked-max-ratio
variant refuted at 61/100 by genuinely increasing steps from the
4-power floor jumps; the convexity route closes it for good.)

**Repairs (honesty first).**  (R1) §17d's T_2 LOWER bounds dropped
possibly-negative straddling k <= 2 terms and the k >= 3 tail on
the off-diagonal lo side — sound on the diagonal (squares), not on
T2_01.  Repaired via exact interval products + tail subtraction;
effect ~6e-10 absolute at 11/20, below every banked digit; ledger
regenerated.  (R2) crude_high_k closed its label sums with
sum_pow2(0, s); re-anchored at K = 4 (same certified quantity,
strictly tighter): ~7 orders at s = 8/13.

**Gates 9/9 green**: g_qmin, g_hk, g_lagrange (the identity
replayed exactly on rationals through the minor code path), g_oscs
(conjugated, both lanes, with teeth), g_u1_law (four-digit tau/3),
g_sign (full grid), g_consist (SOS and entrywise routes intersect
everywhere), g_scale, g_separation (four points).  Tests
test_p2_iterated 7/7 (129 s); test_cs_tail 6/6 unaffected; no other
module imports p2_iterated (checked).  Cloud verification;
Mac-side run not claimed.

**What binds the magnitudes now, ranked**: (1) the (0,3) minor
through dom(3,3) — the first named consumer for the recoupling
evaluator / any landed (3,3)-class diagonal; (2) the (0,2)/(1,2)
crude entry windows (label-less (2,2) unreached masses); (3) the
l >= 9 crude closure, only at 61/100 and 8/13.

**Next attack.**  (1) The matched-flow consumer: tau'/tau at depth
2 under both MD.1 matchings against the §17c envelope — both
instruments now certified two-sided on 1/2..4/7.  (2) The
thickness-2 census (blocking-vs-stacking defect) when the
recoupling evaluator lands, whose gate set now includes the
(3,3)-class diagonal binding the depth-2 magnitude.  (3) P3
atlas-adequacy.

## §17f (2026-07-29): P2 CONTINUED — the matched-flow consumer at depth 2: a certified, scheme-covariant, magnitude-separated composition drift; the D1 depth-2 covariance theorem; the mirror refutes conjugated-Gram covariance

Executes the §17d/§17e next-attack item (the matched-flow consumer).
Artifacts: computations/p2_matched_flow.py + ledger,
tests/test_p2_matched_flow.py (3 tests), notes/p2-matched-flow.md.

**D1 (separator): depth-2 covariance is a THEOREM on composed
kernels — and the mirror breaks it.**  SU(2): the OS Gram is T
itself, T is symmetric PSD (entry-level OS Gram §17e; PSD
machine-certified on the banked exact M=1 kernel, Sturm count of
negative roots = 0), so lambda_i(T^2) = lambda_i(T)^2 and sigma_2 =
sigma^2 EXACTLY (gated on the banked kernel: sigma = 7.034652e-8,
sigma_2 = sigma^2 to the window): the separator matching carries NO
depth-2 trajectory content on the composed object.  U(1) conjugated
Gram G = PT: eigenvalues carry parity signs, and the exact finite
theta kernels REFUTE covariance — sigma_2 = 1.0388e-4 < 1.8531e-4 =
sigma^2 at s = 1/2, M-stable (M = 2, 3): the abelian second channel
is parity-odd; composition damps it strictly faster than the square.
Depth-2 separator content EXISTS for U(1), is EMPTY for composed
SU(2) — the dual of the §17d vacuity theorem, at the separator
level.

**D2 (pair): the first certified two-step flow numbers.**  Flowed
envelope of the certified two-step kernel on the banked coarse basis
(primary {0,1,2}; {0,1} control — channel-2 sector membership is
truncation-undecided at M -> infinity, both schemes run), from the
SAME certified M -> infinity entry windows as §17e (sharper
instrument than MD.1's provisional M = 2 kernels; consistent with
them: tau'/tau at 1/2 = 3.9995 vs 3.9986).  Certified windows
(primary): tau'/tau, tau''/tau = [3.9995, 3.9995], [3.9995, 3.9995]
at 1/2; [3.9982,3.9984], [3.9984,3.9984] at 11/20; [3.9974,3.9979],
[3.9978,3.9978] at 9/16; [3.9965,3.9978], [3.9973,3.9974] at 4/7;
wide at 3/5; 61/100 and 8/13 = the reported instrument boundary
(T_2(0,1)-column l >= 9 crude tails — the §17e wall).  U(1) exact at
all seven points: 3.6520 -> 3.7272 (1/2) ... 3.2021 -> 3.3299
(8/13).

**The trajectory verdict.**  tau''/tau stays ~4, not ~16 — matched
against the one-step fixed-point form, the composed kernel reads as
almost the SAME effective coupling: the rank-one collapse seen
through the flow map.  The windows certify the residual drift
tau''/tau - tau'/tau:

- SU(2) primary: CERTIFIED POSITIVE at 1/2 ([1.71e-5, 1.74e-5]) and
  11/20 ([3.56e-5, 1.50e-4]); window-bounded at 9/16, 4/7.
- SU(2) {0,1} control: certified positive at 1/2, 11/20, 9/16, 4/7 —
  scheme-covariant sign.
- U(1) exact: +7.5e-2 (1/2) rising to +12.8e-2 (8/13).

Same sign both groups and both schemes; magnitudes separated ~4e3 at
s = 1/2.  The §16 fence pattern — sign scheme-covariant, MAGNITUDE
discriminates — now holds at the trajectory level, in the observable
class the §17d vacuity theorem licenses: the first certified
statement about the matched flow's second step in the scheme family
(TS) constrains.

**Gates.**  g_sigma_sq (Sturm code path), g_su2_psd (banked M=1 Gram
PSD + covariance), g_u1_parity (VERDICT refuted, banked, M-stable),
g_mirror (theta pair inside the §16c asymptotic-curve band at 9/10),
g_t2_regress (generalized T_2 windows == §17e on {0,1}^2 exactly),
g_boundary (positive envelopes on the claimed range s <= 3/5).
Tests test_p2_matched_flow 3/3; test_flow_matching 9/9 unaffected.
Cloud verification; Mac-side run not claimed.

**Honesty.**  Composed DERIVED kernels; the thickness-2 census
defect untouched.  Matched objects live on finite coarse bases;
b012/b01 scheme spread reported in the ledger, never hidden.  Float
tau ratios are images of certified rational windows; every certified
claim is a rational comparison.

**Next attack.**  (1) Drift s-dependence: tighten 9/16 and 4/7 on
the primary basis — first consumer remains the recoupling evaluator
/ (3,3)-class diagonals (same ranking as §17e).  (2) The thickness-2
census: the composed-vs-refined comparison now has TWO certified
targets (T_2 windows AND the matched-flow drift).  (3) P3
atlas-adequacy with both instruments.

## §17g (2026-07-29/30, cloud): P3 EXECUTED — the SECTOR-SOS certificate: X_11 > 0 on ALL of (0,1) from one coefficient-sign check; the atlas collapses; the s->1 order-4 degeneracy is PROVED PROTECTED and the rate front is renamed

Executes queue item **P3** (overlap closure / atlas-adequacy) — and
supersedes the mechanism P3 was expected to need.  Artifacts:
`computations/sector_sos.py` (+ ledger), `computations/sector_sos_cap2/`
(independent-replication tooling), `computations/u1_conjugation_fence.py`
(+ ledger), `tests/test_sector_sos.py` (13 tests),
`scripts/gen_sector_sos_lean.py`, `dual_kappa_spike/SectorSOSLedger.lean`
(eighth spike target), `notes/sector-sos-positivity.md`.

**THE COVERAGE FINDING THAT REFRAMES P3 (stated, then made moot).**  The
atlas exists to cover the middle regime `[2^{-1/3}, s_*] = [0.793701,
1 - 5.68e-14]`.  Every certified grid point banked in §§16h-16l and §17e
— bought at exponentially rising cost, and the object of §17.2's F1
complaint — lies at `s <= 5/8 = 0.625`, i.e. **entirely inside the
unconditional strong-coupling anchor window `[0, 2^{-1/3})`**.  The
marched frontier therefore contributed *zero* coverage to the interval
the atlas is for; the middle regime had NO coverage at all.  F1 called
the s-marching off-geodesic by cost; the sharper statement is that it was
off-geodesic by DOMAIN.

**THE STRUCTURE (three facts).**  The M->infinity slab kernel decomposes
over transverse sectors `sigma = (q,w)` (theta-invariant faces, §16h):
`T[n,m](s) = sum_sigma W_sigma(s) G_sigma[n,m](s)`, `W_sigma > 0`.
**(F1)** each `G_sigma` is an EXACT FINITE polynomial — at fixed sector
`triad(n,q_i,a_i)` forces `a_i <= n + q_i`, so the tile sums TERMINATE:
no truncation error inside a sector, ever (gate `g_exact`, M vs M+1
identical; teeth: at cap<=2 the M=2 kernels differ on 144/187 sectors).
**(F2)** each `G_sigma` is PSD over `(n,m) in {0,1}^2` — the BANKED §16h
sector-wise OS/link-reflection input plus `G_sigma = V^T H V` with `H`
the half-config Gram and `V` the strictly positive tile weights (gate
`g_psd`, exact square-root-free LDL: all 16 sectors of the certificate
family AND all 187 of the independent cap<=2 family, ZERO failures;
teeth: every `H` is rank-deficient so the zero-pivot branch fires, and
71/187 have a negative entry, so PSD is not entrywise positivity).
**(F3)** det is superadditive on PSD 2x2: `det(X+Y) = det X + det Y +
tr(X adj Y)` exactly, both extra terms `>= 0`, so **truncating the sector
family can only DECREASE the determinant**: `det T_S <= det T_full` on
`(0,1)`.  Equivalently the pair expansion `det T_full = sum W^2 det G +
sum_{sigma<sigma'} W W' Q`, `Q = AB' + BA' - 2CC' >= 0`, is an exact sum
of NON-NEGATIVE terms indexed by sector pairs — the depth-1 analogue of
the §17e depth-2 Lagrange/Cauchy-Binet SOS (gate `g_pairs`: exact
rational identity, zero negative `Q`).

**THE CERTIFICATE.**  Family = the 16 sectors with all labels <= 1.
Exact assembled kernels: `T00 = 1 + 16s^18 + 16s^30 + 32s^36 + 16s^42 +
4s^48`; `T01 = 2s^12 + ... + 6s^68` (10 terms); `T11 = 5s^24 + ... +
9s^88` (13 terms).  Then `det_S = T00 T11 - T01^2 = s^24 P(s)`, `deg P =
106`, `P(0) = 1`, **16 of P's 46 coefficients NEGATIVE**.  Under the
Moebius bijection `s = 1/(1+t) : (0,1) -> (0,inf)`,

    R(t) = (1+t)^106 P(1/(1+t)) = t^4 * Rhat(t),
    Rhat: 103 integer coefficients, ALL >= 0, Rhat(0) = 15972864 > 0.

Hence `P > 0` on `(0,1)`, hence by (F3) the FULL kernel satisfies
`T00 T11 > T01^2`:

>   **X_11(s) = log(T00 T11 / T01^2) > 0 for ALL s in (0,1)** — the
>   anti-screening sign of the one-step blocked observable, uniformly on
>   the whole interval, modulo the banked (F2) OS input (which is the
>   SAME input §16h-§17e already consume, not a new frontier atom).

Positivity is now a comparison of 103 integers against zero — a
DESCARTES certificate, not a Sturm count.  Independent replication on a
disjointly built family: cap<=2, **187 sectors**, built with an
independent exact spin-network evaluator gated BIT-FOR-BIT against the
incumbent `dp3_fixed_tile` on all 171 cap<=1 configurations, 320
orthogonality identities and 130 random networks: `deg 376`, 69/163
negative coefficients, **0 roots in (0,1)** by BOTH Sturm and Descartes,
`Rhat(0) = 230460431616`.

**CONSISTENCY WITH THE BANKED INSTRUMENT.**  `g_census`: the sector
assembly reproduces the banked M=2 census polynomial exactly on the
leading block of every entry and is coefficientwise DOMINATED by it
elsewhere — the relation a positive sub-sum must satisfy.  `g_grid`: at
every §16l CERT point `det_S > 0` and the assembly's `X_11` sits at or
above the banked floor; at `s = 1/2` it is `0.258391`, EQUAL to the
banked certified floor to six decimals — the two routes meet.
Non-vacuity: the dominant trivial sector is EXACTLY rank one
(`det G = 0` identically) and the diagonal part is `7.1e-14` of `det_S`
at `s = 1/2` — the certificate is entirely cross-sector INTERFERENCE.

**THE U(1) FENCE, EARNING ITS KEEP AGAIN (§17.4).**  Abelian:
`T[n,m] = D_n D_m Phi(n-m)` with `Phi(k) = sum_c s^{a(c)}(s^{2S(c)})^k` a
STIELTJES MOMENT SEQUENCE, so the observable's matrix is a TOEPLITZ form
while the OS Gram object `T[-n,m] = D_n D_m Phi(n+m)` is a HANKEL form.
Hankel of a moment sequence is PSD; Toeplitz is not — that one word is
the fence.  Per abelian orbit `{c,-c}`,
`det G_sigma = s^{2a+8}(4 - (t+1/t)^2) < 0` whenever `S(c) != 0` — a
PROOF, not a numeric; 270/313 orbits carry a strictly negative exact
determinant (witness `c=(1,0,0,0)` at `s=1/2`: `-225/16777216`).  The
ASSEMBLED abelian 2x2 has certified negative determinant, so **no**
sector decomposition whatsoever can be sector-wise PSD abelian-ly: the
fence is decomposition-INDEPENDENT.  Conjugated blocks are rank one and
their sum is PSD (conjugated PASSES).  Kernel-checked exponent form:
`2Qmin(n,m) - Qmin(n,n) - Qmin(m,m) = -2(n-m)^2` (unconjugated, wrong
sign) vs `2Qmin(-n,m) - Qmin(-n,n) - Qmin(-m,m) = +2(n-m)^2`
(conjugated).  New closed form, the exact mirror of the SU(2) statement
with the opposite sign: `X_U1(s) = -2 log(Phi(1)/Phi(0)) < 0` for EVERY
`s in (0,1)` (banked `X_U1(1/2) = -0.35636` reproduced).  **Where SU(2)
enters:** OS gives PSD of `[T[nbar,m]]`; SU(2) is self-conjugate so
`nbar = n` and the OS-PSD object and the `X_11` object are LITERALLY THE
SAME MATRIX, sector by sector.  Two flags: self-conjugacy is used TWICE
(boundary charge and sector-preservation — abelian-ly reflection sends
`c -> -c`, which is why the abelian analysis needs `±c` orbits), and it
is an SU(2)/A_1 fact, so all-group uniformity rides the R1 worst-case
spine (invariant P6) — inherited debt, not discharged here.

**LEAN (eighth spike target).**  `SectorSOSLedger.lean`, generated: the
sector weights and exponents REDERIVED in-kernel from the labelling; the
assembly REDERIVED coefficient by coefficient against declared integer
polynomials with an exponent-COMPLETENESS guard; `det_S` formed
in-kernel; the Moebius transform by Horner in `u = 1+t`; then
`sector_sos_certified : rHat.all (fun c => decide (0 <= c)) = true` by
`decide` — the program's **first kernel-checked INTERVAL statement**
(every prior certified statement was pointwise).  Plus `r_low_order`
(order exactly 4 at `t=0`, leading 15972864), `t_rederived`,
`exps_complete`, `det_bottom`, `p_has_negative_coefficients` (=16,
non-vacuity), `sector_blocks_psd_on_grid`, `trivial_sector_rank_one`, and
three U(1) fence theorems.  Verified in the cloud with Lean 4.29.1,
`LEAN_NUM_THREADS=1 -M 8192`: **exit code 0**, no errors, no warnings.
`#print axioms`: ten of eleven theorems depend on NO axioms at all;
`r_low_order` on `[propext]` only — inside the `{propext, Quot.sound}`
budget.  **Mutation-tested**: changing one transcribed Haar value
`(34, 9/16) -> (34, 10/16)` makes `t_rederived` fail.  Tests
`test_sector_sos.py` 13/13 (47 s).  **Mac-side lake run NOT claimed** —
no Lean ran on the host this session.

**THE RATE: A BANKED REFUTATION AND A RENAMED FRONT.**  `det_S` gives a
QUANTITATIVE floor only after an upper bound on `T01` (one entry — the
cheap direction of the window instrument), and near `s = 1` the floor is
`O(tau^4)`, not the true `O(tau^2)`.  The obvious lever — enlarge the
transverse family — is **REFUTED**: the cap<=2 family (187 sectors) has
the SAME order-4 vanishing at `s = 1`, because every sector shares the
`s -> 1` collapse of `T` onto the rank-one dimension kernel
`That[n,m] = d_n d_m s^{12(n+m)} T00`, with the two exact coincidences
`T00(1) x_2 = u_1^2` and `T00(1) x_3 + T00'(1) x_2 = 2 u_1 u_2`
(`u = T01 - 2T00`, `x = T11 - 4T01 + 4T00`) holding in BOTH families.
The order-4 degeneracy is PROTECTED, not a small-family artifact.

**Queue effect.**  P3's sign half is CLOSED on the whole interval and the
atlas requirement collapses from "finitely many expensive windows meeting
`s_*`" to one coefficient-sign check; MD.4's per-window functional
positivity is discharged uniformly.  DE-PRIORITISED as a consequence:
further one-step s-marching (already capped at 31/50 by §17.3, now moot
for the sign), and the recoupling evaluator / (0,3)- and (3,3)-class
diagonal lane AS SIGN CONSUMERS — they remain rate consumers only.

**Next attack.**  (1) The deviation kernel `delta = T - That`, and
specifically `delta11 - 4 s^12 delta01`, whose order-3 coefficient is the
first quantity the protection mechanism does NOT fix: the two-sided rate
envelope `1 < tau'/tau <= 1 + c tau` and the P3 overlap closure now live
there, not in `det T`.  (2) The cheap direction of the window instrument
(upper bound on `T01` alone, uniformly in s) to convert `det_S` into a
certified `X_11` FLOOR on the middle regime.  (3) Transport the sector-SOS
argument to the depth-2 object, where §17e's Lagrange SOS and this
depth-1 SOS should compose.  (4) Standing: pin the
`computations/sector_sos_cap2/` replication tooling in `tests/`.

**§17g addendum (same session): the next front OPENED and its first
guess REFUTED.**  The deviation kernel `delta = T - That`,
`That[n,m] = d_n d_m s^{12(n+m)} T00`, was named above as the way past
the protected order-4 degeneracy.  Computed exactly in both families:

* `delta01 = T01 - 2 s^12 T00` and `delta11 = T11 - 4 s^24 T00` each
  vanish to order EXACTLY 2 at `s = 1`, with `delta11 = 4 * delta01` at
  leading order EXACTLY — cap<=1: 16896 = 4 * 4224; cap<=2:
  2899680 = 4 * 724920.  The protection relation is confirmed
  independently of `det`.
* The proposed escape combination `delta11 - 4 s^12 delta01
  = T11 - 4 s^12 T01 + 4 s^24 T00` vanishes to order **4**, not 3 —
  leading coefficient 397824 (cap<=1) and 181063296 (cap<=2), both
  positive.  **The "order-3 coefficient" guess is REFUTED**: the
  order-4 vanishing is a property of the OBSERVABLE CLASS, not of the
  transverse family, and subtracting the rank-one dimension kernel does
  not break it.
* What DOES respond to the family is the SIZE, not the order: every
  leading coefficient grows by 2-4 orders from cap<=1 to cap<=2
  (4224 -> 724920; 397824 -> 181063296; det's 15972864 ->
  230460431616).  So family enlargement buys magnitude, never order.

Consequence for the ranking: the rate must come from the RELATIVE
quantity `X_11 / tau^2`, i.e. from pairing `det_S` with a uniform UPPER
bound on `T01` alone (the cheap direction of the window instrument),
not from any further algebraic recombination of the same entries.  That
is now the single next item.

## §17h (2026-07-30, cloud): the §17g sign becomes a RATE — the first certified quantitative statement in the middle regime, and the crude diagonal domination NAMED AND SIZED as the sole remaining loss

Executes §17g's next-attack item (2).  Artifacts:
`computations/sector_floor.py` (+ ledger),
`tests/test_sector_floor.py` (6 tests).

**The inequality.**  With `D = T00 T11 - T01^2` and
`sin^2 theta = D/(T00 T11) in [0,1)`,

    X_11 = -log(1 - D/(T00 T11))  >=  D / (T00 T11),

and BOTH ingredients are now available in the EASY direction:

* `D >= det_S(s)` — the §17g sector-truncated determinant, an exact
  polynomial valid on all of `(0,1)` by det-superadditivity over the PSD
  sector blocks.  **No upper bound on the off-diagonal `T01` is needed
  anywhere.**  That was the expensive, sign-cancelling direction that
  capped the §16h-§17e window instrument at `s <= 5/8`; the §17g
  structure removes it from the rate problem entirely.
* `T00, T11` are DIAGONAL Gram entries — sums of NON-NEGATIVE terms — so
  any domination of the Haar values bounds them above with no
  cancellation to track.  Used here: the incumbent crude domination
  (`su2_minf_windows.DomTransfer` + `lam_slop`), which converges for
  EVERY `s < 1` once `4 s^{2lam+3} < 1` and `16 s^{4lam+6} < 1`.

**THE RESULT — certified floors strictly above the anchor edge**
(`2^{-1/3} = 0.793701`, so every point below is OUTSIDE the
unconditional anchor window; each is the first certified quantitative
statement at that coupling):

    s        tau       lam   det_S        CERTIFIED X_11 >=   crude cost
    4/5      0.22314    4    1.7174e-2    5.9477e-25          4.674e+23
    5/6      0.18232    5    5.7711e-2    6.9182e-28          3.044e+26
    6/7      0.15415    5    1.3703e-1    2.2185e-32          6.780e+30
    9/10     0.10536    8    6.0153e-1    1.2025e-37          4.351e+35
    14/15    0.06899   11    1.4123e+0    2.8191e-46          4.237e+43
    24/25    0.04082   14    1.4948e+0    6.4308e-55          2.461e+51

**Honesty, stated as sharply as the numbers allow.**  The floor is
certified and positive across the middle regime — and it is 24 to 54
orders below the truth.  The loss is NOT in `det_S` (exact) and NOT in
the inequality (tight to within the `log(1+x) ~ x` step at small `x`):
it is ENTIRELY the crude `|N| <= prod(dim)` domination of the DIAGONAL
entries, and the module measures that loss point by point against the
reference ratio `det_S/(T00_S T11_S)`.  It is recorded as a certified
floor, never as a useful one.

**The named fix, and its size.**  The diagonal admits the OS-triangle
bound `T_nn = sum_sigma W_sigma ||x_n(sigma)||^2` with
`||x_n(sigma)|| <= sum_a W_a(s) sqrt(N(n,n,sigma,a,a))` — the §16h
Cauchy-Schwarz sharpening applied to the DIAGONAL, whose inputs are
single same-config Haar values (the cheapest objects in the program,
already computed for the cap<=1 family by
`sector_sos.half_config_gram`).  The residual is then only the SECTOR
tail, where `W_sigma` carries the full `s^{2C(q)}` suppression.  From
the measured slack this recovers of order 20 magnitudes at `s = 4/5`.
Crucially it is EASY-DIRECTION work throughout: no off-diagonal, no
unresolved diagonals, no recoupling evaluator, no (3,3)-class lane.

**Queue effect.**  The rate problem on the middle regime is now a
DIAGONAL-ONLY estimate.  The recoupling evaluator and the
(0,3)/(3,3)-class diagonal lane, already de-prioritised as sign
consumers in §17g, are hereby de-prioritised as MIDDLE-REGIME RATE
consumers too — they bind only the off-diagonal, which this route no
longer touches.  Tests `test_sector_floor.py` 6/6 (130 s), including a
pinned honesty test that the crude cost exceeds 10^20.  Cloud
verification; Mac-side run not claimed.

**Next attack.**  (1) The OS-triangle diagonal bound: exact
`sqrt(N(n,n,sigma,a,a))` per sector up to a label cutoff plus a
sector-tail closure, replacing `DomTransfer` in `sector_floor` —
the ~20-order recovery, and the item that turns the floor from
decorative into usable.  (2) With a usable floor, compare against the
`6 tau^2` law to test whether the sector family must grow with
`1/sqrt(tau)` (the adapted-family atlas) or whether a fixed family
suffices down to the MD.3 edge.  (3) §17g item (3), the depth-2
transport, stays queued behind these — note the §17d vacuity theorem
already makes the depth-2 SIGN group-generic, so only the FLOOR
transports there, via `det_{2e} >= (det_e)^2` (Cauchy-Binet on the
composed Gram, leading minor).

**§17h supplement (same session): the loss is now RESOLVED INTO TWO
REGIMES, each with a different binding constraint and a different fix.**
Two measurements, both exact:

*(a) The `N_diag <= 1` lane — worth 10-13 orders, and it is a real
lemma, not a convention.*  Every diagonal Haar value of the cap<=1
family satisfies `0 <= N(n,n,sigma,a,a) <= 1`, with the maximum exactly
1 at the trivial config and values down to `1/186624 = 1/(2^8 3^6)`; the
crude `|N| <= prod(dim)` domination overpays by up to `1.25e12` ON A
SINGLE CONFIG.  Re-running the incumbent 4-cycle transfer with LINEAR
dim weights (`d_a s^{C(a)}`, `d_q^2 s^{2C(q)}`, `d_w s^{C(w)}` — the
weights the OS-triangle bound `||x_n(sigma)|| <= sum_a W_a
sqrt(N_diag)` produces under `N_diag <= 1`) gives, CONDITIONALLY on that
bound:

    s = 4/5 :  T00_hi 8.49e10 -> 6.32e5,  floor 5.95e-25 -> 4.30e-14
               (gain 7.24e10x; residual slack to the reference 6.46e12x)
    s = 9/10:  T00_hi 1.12e18 -> 5.56e11, floor 1.20e-37 -> 1.94e-24
               (gain 1.62e13x; residual slack 2.69e22x)

`N_diag <= 1` is NOT asserted here.  It is the multiplicity-free vertex
statement, and the standing coupled-simplification audit binds it to the
SU(2) worst-case reduction and the `Z_t(G) <= Z_t(SU(2))` character-tail
input — any pass that proves it must re-verify both.  It is recorded as
a measured, exactly-witnessed CONJECTURE with its audit dependency
named, and the conditional floor above is what it would buy.

*(b) The family-adaptation law — measured, and it says the atlas is
real after all.*  Comparing `det_S` on the cap<=1 (16-sector) and
cap<=2 (187-sector) families at the same coupling:

    s        det_S2 / det_S1     ref ratio, cap<=1 -> cap<=2
    1/2      1.000               2.2771e-1 -> 2.2771e-1
    4/5      1.083               2.7801e-1 -> 2.8800e-1
    9/10     4.262               5.2318e-2 -> 8.2142e-2
    24/25    1.814e+2            1.5827e-3 -> 6.1795e-3
    99/100   4.198e+3            5.7721e-6 -> 3.3522e-5

The cap<=1 family SATURATES at moderate coupling (`s <= 4/5`: enlarging
buys under 9%) and starves as `s -> 1` (4198x at 99/100 and still
climbing).  So:

>   **Two regimes, two binding constraints.**  At moderate `tau` the
>   det side is already essentially exact and the entire loss is the
>   DIAGONAL upper bound.  As `tau -> 0` the diagonal is not the issue —
>   the FAMILY is, and the required label cap grows with `1/tau`.

This resolves §17g's open rate question into two independent, separately
attackable engineering items, and it *re-legitimises the atlas concept*
in a new form: not a cover by expensive point windows, but an
s-ADAPTED LADDER OF SECTOR FAMILIES, each supplying an INTERVAL
certificate of the §17g coefficient-sign type (cheap, kernel-checkable)
on its own dyadic band of `tau`.  Whether the ladder terminates before
the MD.3 edge `tau* = 2^-44` is the sharp form of the P3 overlap
question, and it is now a measurable quantity rather than a hope.

**Revised next attack.**  (1) The `N_diag <= 1` lemma under the full
coupled-simplification audit (multiplicity-free vertex + character-tail
domination in the same pass) — it is worth 13 orders and nothing else in
the diagonal lane is worth building first.  (2) The cap<=3 family, to
fit the growth law `cap(tau)` and test whether the ladder terminates.
(3) Only then the atlas-adequacy statement in its new form: a finite
ladder of interval certificates meeting `tau*`.

## §17i (2026-07-30, cloud): work_plan RESTORED after an overwrite incident; the §16f assembly INDEPENDENTLY CROSS-CHECKED by a disjoint pipeline; one erratum

**Incident.**  Commit 9dd7139 (a session working from a stale local
copy that predated §16f-original through §17h) overwrote
work_plan.md, deleting 1557 lines.  Restored from e72e2c8 in this
commit.  Standing rule, added: a session MUST re-stage work_plan.md
from the device immediately before appending, and diff against git
HEAD before any commit touching it.

**The cross-check (the incident's silver lining).**  The stale
session, not knowing `computations/c_su2_assembly.py` existed,
independently built the same physics with a methodologically
disjoint pipeline (`computations/insertion_moments.py` +
`computations/gaussian_network_moments.py`: conditional-covariance
reduction + Gaussian integration by parts against single tilts,
sympy-symbolic, closure-gated on the exact single-face identity).
Exact agreement on every shared object:

- Var_fusion(delta) = (4/3) C(n) C(m) closed form; the pure-fusion
  cross law +(2/3) C(n) C(m); X_11 = +6 tau^2;
- kappa_2 diagonal block "Jacobians": +139/4 (via W = -49/192 +
  1/72 = -139/576 over the exact network covariances);
- kappa_2 diagonal block "orderings/bare-radial": -6 (via the
  bare-tilt series p1 = -1/96, p2 = 0; p2 = 0 = pair-independence);
  the disjoint pipeline's closure gate independently CAUGHT this
  term (its first draft omitted it and the gate refused);
- arithmetic closure: (-115/4) [disjoint pipeline's diagonal
  blocks, flow units] + (+251/8) [assembly's BCH blocks] = +21/8 =
  c_dyn, the §16f headline, exactly.

The §16f-original assembly remains AUTHORITATIVE; the disjoint
modules are banked as its independent verification (pins
tests/test_insertion_moments.py, 10/10, incl. the reconciliation
identity).

**Erratum (stale session's first draft).**  Its fusion-basis slope
term carried the wrong sign (+(2/3)<C> for -(2/3)<C>; Jensen — the
variance adds in the log).  Corrected; matches
c_SU2(N) = 21/8 - (2/3)E_w[C].  Its "partial c_SU2 = -99/4" framing
is RETRACTED; the banked statement stands: c_SU2(N=2) = -11/8,
c_SU2 - c_U1 = +21/8 > 0 exactly (anti-screening).

**Also landed.**  Provenance for the §16d flat representation:
J. Faraut, *Analysis on Lie Groups*, CUP 2008, Prop. 8.6.6, p. 181
(user-supplied citation; identical constants) — recorded in
`computations/su2_flat_heat_kernel.py`; the 87-digit in-substrate
verification stands.  The §17 queue (§17.3, as re-prioritized by
§17h) is unchanged by this addendum.
