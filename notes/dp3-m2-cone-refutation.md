# DP.3-(i) at M = 2 — the coefficient cone is REFUTED at both granularities; the functional cone survives

**Date.** 2026-07-26.
**Milestone.** Queue item (a) of work_plan §15f: "DP.2/DP.3 M=2 — saturation
+ ε_slab(M) + cone preservation where 6j interference first enters + RP at
M=2."
**Predecessors.** DP.2 (`computations/slab_blocking_kernel.py`); DP.6
(profile granularity fails, exponent granularity holds); DP.6-U1
(discriminator rule); `docs/dp3-exponent-cone-statement.md` (the statement
this note amends).

All arithmetic exact (`Fraction` / integer s-polynomials; Sturm sign
certification on (0,1); no floats in any verdict path).

---

## 0. Headline

`docs/dp3-exponent-cone-statement.md` §2(i)(a) named the open content of
claim (i) precisely:

> "at M = 1 the computed entries happen to be coefficientwise nonnegative,
> so preservation holds trivially at this truncation — the open content of
> (i) lives at larger M, where signed 6j interference can in principle put
> negative coefficients into an entry while leaving it positive as a
> function.  If that occurs, claim (i) must be proved at the aggregated
> level (cancellation across m at fixed output exponent), exactly the DP.6
> pattern."

Both halves of that sentence are now settled, and the second one
negatively:

1. **Entry level — REFUTED.**  `T[1,1]` carries the coefficient
   **−32/3 at s⁷⁶**, exact and final (§2).
2. **Aggregated level — ALSO REFUTED.**  The blocked image `(Bv)_1`
   carries **−64/3 at s⁷⁹**, exact and final: the other channels
   contribute *exactly zero* at that exponent, so there is nothing to
   cancel against (§3).  The DP.6-style repair is therefore **not
   available** — cancellation across m does not happen here.
3. **Functional positivity SURVIVES.**  `T[1,1]` is positive as a
   function on all of (0,1), Sturm-certified, negative coefficient and
   all (§4).  The property DP.2's Birkhoff/Hilbert measurements actually
   consume is intact everywhere computed.

The conclusion is a change of cone, not a repair of the proof: see §6.
Nothing in the repo's numeric state changes; no constant is invented.

## 1. Method

### 1.1 Fixed-tile decomposition (why M = 2 became reachable)

The polynomial-valued route (`kernel_entry_skeleton`, tiles carrying
truncated heat activities) does not reach M = 2 on this host: direct
contraction passed 3.3 GB before being killed, and the skeleton route
exceeded a 240 s per-class budget on 17 of 46 classes.

Since `heat_activity(U, M) = Σ_{a≤M} d_a s^{C(a)} χ_a(U)`,

    skeleton_value(n, m, q, w, M)
      = Σ_{top, bot}  Π_i d_{a_i} s^{C(a_i)} d_{b_i} s^{C(b_i)}
                      · N(n, m, q, w, top, bot),

with `N` the Haar value of a network all of whose factors are single
characters — an exact rational, and a much smaller contraction.  It
reaches classes the polynomial route could not: the lowest-exponent
blocker `q=(0,0,1,1) w=(0,1,2,1)` computes in 91 s with N = 1/256.

**Gated, not assumed.**  `dp3_fixed_tile.gate()` rebuilds
`skeleton_value` from the fixed-tile sum and demands exact polynomial
equality: 14/14 classes matched, including spin-2 classes.  Separately
`dp3_m2_driver.gate_M1()` reproduces `kernel_entry_skeleton` exactly for
all ten entries n, m ≤ 3 at M = 1.

### 1.2 Why this granularity answers claim (i)

Every weight in the assembly (dimensions, Casimir powers, D4 orbit
multiplicities) is strictly positive.  A negative coefficient in
`T[n,m]` can therefore only originate in a negative `N` — in signed 6j
recoupling interference.  Auditing the `N`'s is the sharp test, and each
`N` is rigorous on its own, independent of any other configuration.

### 1.3 Per-exponent finality (the rigor device)

A configuration contributes to **exactly one** exponent, `E(config)`.
So a computed coefficient at exponent E is FINAL as soon as no UNREACHED
configuration sits at that same E.  This is sharper than a global
"exact below the smallest unreached E" window: a coefficient can be
final far above that window.  It lifts to the blocked image — the
`(Bv)_n` coefficient at E is final iff, for every m, no unreached
configuration of `T[n,m]` sits at `E − C(m)`.  `dp3_m2_analysis.final_at`
/ `blocked_final_at` implement the predicate; every verdict below is
tagged by it.

### 1.4 Process isolation

Two runs died on memory — one OOM-killed at 4 GB, one in a cascade of
`MemoryError`s raised *inside* its own exception handler (at that point
even `import gc` could not allocate).  Each configuration is now
evaluated in a subprocess worker with its own address-space cap
(`worker_fixed.py`, `run_iso.py`); a worker that overruns memory or
wall-clock is killed and replaced and its configuration recorded
UNREACHED.  Isolation, not a larger try/except.

## 2. The entry-level fence: T[1,1] at s⁷⁶

Eight configurations carry E = 76 in `T[1,1]`; **all eight are
computed**, four contribute 0 and four contribute −8/3 each:

| q | w | top | bot | N | weight | contribution |
|---|---|---|---|---|---|---|
| (0,1,2,1) | (1,1,1,1) | (1,0,1,2) | (1,2,1,2) | −1/1492992 | 3981312 | −8/3 |
| (0,1,2,1) | (1,1,1,1) | (1,2,1,0) | (1,2,1,2) | −1/1492992 | 3981312 | −8/3 |
| (0,1,2,1) | (1,1,1,1) | (1,2,1,2) | (1,0,1,2) | −1/1492992 | 3981312 | −8/3 |
| (0,1,2,1) | (1,1,1,1) | (1,2,1,2) | (1,2,1,0) | −1/1492992 | 3981312 | −8/3 |
| (1,2,1,2) | (1,1,1,1) | (4 labellings) | | 0 | 1990656 | 0 |

**Coefficient at E = 76 = −32/3, FINAL.**

The four negative configurations are D4/reflection images of one.  Every
negative `N` found anywhere in the census requires a **spin-2 face** —
the same signature as the (DP) refutation of §15a (every negative
amplitude required a spin-3 face), now one level up: inside the blocking
kernel rather than the bare dual amplitude.

## 3. The aggregated fence: (Bv)_1 at s⁷⁹

For the heat-kernel envelope `v_m = d_m s^{C(m)}`:

| m | needs T[1,m] at | coefficient | × d_m s^{C(m)} | contribution |
|---|---|---|---|---|
| 0 | s⁷⁹ | 0 | 1·s⁰ | 0 |
| 1 | s⁷⁶ | −32/3 | 2·s³ | **−64/3** |
| 2 | s⁷¹ | 0 | 3·s⁸ | 0 |

**Coefficient at E = 79 = −64/3, FINAL** (no unreached configuration of
`T[1,0]`, `T[1,1]`, `T[1,2]` sits at 79, 76, 71 respectively).

This is the decisive point.  The DP.6 precedent was that positivity
lost at fine granularity is *restored* by aggregation, with margins of
50–500×.  Here the two sibling channels contribute **exactly zero** at
the offending exponent: there is no cancellation to appeal to, and the
aggregated repair route named in the DP.3 statement is closed.

## 4. Functional positivity survives

`T[1,1]`, final part (E < 78):

    5s²⁴ + 12s³⁰ + 2s³⁶ + 24s³⁸ + 72s⁴⁶ + 48s⁵² + 144s⁵⁴ + 34s⁵⁶
      + 48s⁶⁰ + 232s⁶² + 84s⁶⁸ + 848/3·s⁷⁰ + 64s⁷² − 32/3·s⁷⁶

one negative coefficient; **Sturm on (0,1): positive**.

All three blocked channels, final parts: coefficientwise positive AND
Sturm positive on (0,1).  `T[0,0]`: 27 terms, zero negative network
values.

Completed entry table (`T[2,2]` closed 2026-07-26, after the first
draft of this note):

| entry | terms | negative N | unreached | FINAL below E | negative coefficients |
|---|---|---|---|---|---|
| T[0,0] | 27 | 0 | 13 | 58 | none |
| T[0,1] | 30 | 3 | 21 | 68 | 102, 112 (provisional) |
| T[0,2] | 36 | 2 | 28 | 66 | none |
| T[1,1] | 26 | 24 | 45 | 78 | **76 (FINAL)**, 102 |
| T[1,2] | 29 | 30 | 26 | 76 | 112 (provisional) |
| T[2,2] | 31 | 12 | 89 | 72 | 102 (provisional) |

| channel | FINAL below E | (i) coefficientwise | (i') Sturm on (0,1) | negatives above window |
|---|---|---|---|---|
| (Bv)_0 | 58 | YES | positive | 105, 115 |
| (Bv)_1 | 68 | YES | positive | **79 (FINAL by the per-exponent predicate)**, 105, 120 |
| (Bv)_2 | 66 | YES | positive | 110, 115 |

Note the pattern: negative coefficients are common in the provisional
tails of every entry and every channel, but only two are final under
the §1.3 predicate — and those two are the fences of §2 and §3.

So the negativity is a property of the **character/exponent basis**, not
of the kernel.  The same object in the configuration basis — a
symmetric-half-weight boundary kernel `W^{1/2}[∫W_temp]W^{1/2}` — is
manifestly strictly positive pointwise, precisely because it is never
expanded in dual coefficients.

## 5. Discriminator (audit rule ii)

| step | tag | evidence |
|---|---|---|
| negative coefficients in blocked kernel entries and in the blocked image | **non-abelian liability** | SU(2): −32/3 at s⁷⁶ (T[1,1]), −64/3 at s⁷⁹ ((Bv)_1); every negative N requires a spin-2 face.  U(1) control at M = 1, 2, 3: **zero** negative coefficients in any entry (entries are certified lattice-point counts) |
| functional positivity of entries on (0,1) | **group-generic** | holds for both groups; carries no gap weight |

Unchanged: the only gap-carrying step remains the sign of the one-step
coupling defect (SU(2) s′ < s⁴ vs abelian s′ > s⁴, §15e).

## 6. What replaces claim (i)

`C_exp` was defined coefficientwise (`a_E ≥ 0`) as a convenience.  DP.2's
contraction measurements never consumed it: they evaluate entries at each
s and compute Hilbert projective diameters from the resulting numbers.
The restatement:

> **Claim DP.3-(i′) (functional cone preservation).**  For dual data
> admitted at exponent granularity, every coarse channel `(Bv)_n` is
> positive as a function on (0,1).

`(i′)` is what the Birkhoff argument needs, is strictly weaker than
`(i)`, and is not contradicted by anything computed here.  Two
consequences worth recording:

* **Positive diagonal conjugation is Birkhoff-neutral.**  The Hilbert
  projective metric satisfies `d(Df, Dg) = d(f, g)` for positive diagonal
  `D`, so a Doob/`h`-transform `P = D_{1/h} T D_{h′}` has the same
  projective diameter and the same contraction coefficient as `T`.  A
  contraction rate may be computed on the unnormalized composed kernel
  and transported to a Markovized channel with no re-estimation.
* The half-weight symmetrization that makes a slab kernel manifestly a
  Gram is the same device as the OS pairing of DP.3-(ii), corroborating
  that the RP data point is structural — consistent with its group-blind
  tag.

## 7. ε_slab(M) — certified, and far stronger than the naive bound

`eps_slab.py` computes, by pure combinatorial enumeration over
triad-admissible labellings (no Haar contraction, no wall-clock budget,
no dependence on which classes were reached),

    E*(n, m, M) := min { E(config) : admissible, max spin = M+1 },

so that `min-deg( T_{M+1}[n,m] − T_M[n,m] ) ≥ E*`, and

    eps_slab(M) := s^{E*(M)} .

At M = 1 (naive single-face bound C(2) = **8**):

| entry | 0,0 | 0,1 | 0,2 | 0,3 | 1,1 | 1,2 | 1,3 | 2,2 | 2,3 | 3,3 |
|---|---|---|---|---|---|---|---|---|---|---|
| E* | 38 | 32 | 32 | 68 | 38 | 44 | 56 | 56 | 68 | 88 |

**Global E\* = 32 versus the naive 8.**  A spin-2 face cannot appear in
isolation: the triads at the 4-valent interior edge and at the
corner-linked perimeter-wall classes force companion faces up with it.
At s = 1/2 the suppression factor alone is 2⁻³² ≈ 2.3 × 10⁻¹⁰.

Measured corroboration: computed `T_{M=2}[0,0]` and `T_{M=1}[0,0]` agree
on every coefficient through s⁴⁷, first differing at s⁴⁸ (4 → 40),
against the certified bound of 38.

## 8. Lean transport (2026-07-26)

`dual_kappa_spike/DP3M2Ledger.lean`, generated by
`scripts/gen_dp3m2_lean.py`, banks both fences as kernel-checked
statements in the DP6Ledger convention (rationals as (Int, Nat),
comparisons cross-multiplied into Int, closed-integer `decide`, no
Mathlib).

| theorem | content |
|---|---|
| `e76_weights_positive` | every assembly weight > 0 — hence a negative coefficient can only come from a negative N |
| `e76_exponents_are_76` | the exponent of each listed configuration, rederived in Lean from its labelling |
| `t11_coeff_76_value`, `t11_coeff_76_negative` | the entry-level fence: −32/3 |
| `blocked_79_no_cancellation` | both sibling channels vanish at their feeding exponents |
| `blocked_79_value`, `blocked_79_negative` | the aggregated fence: −64/3 |
| `t11_final_unique_negative` | it is the only negative coefficient in the final part |
| `t11_scaled_matches`, `t11_final_positive_at` | evaluation witnesses at s = 1/4, 1/2, 3/4 |
| `eps_star_beats_naive`, `eps_star_min` | ε_slab(1) exponents vs the naive C(2) = 8 |

**21 theorems, every one axiom-free** (`#print axioms` reports "does not
depend on any axioms"), all five spike targets build green under Lean
v4.29.1.  Non-vacuity is checked, not assumed: count pins rule out
trivially-true `List.all`, and a mutation test (fence coefficient
flipped to +32/3, a sibling channel given a nonzero value) breaks
exactly the three theorems that assert those literals.

Following the DP6Ledger precedent, "positive polynomial on all of
(0,1)" is **not** formalized — the evaluation pins are witnesses at
three rational couplings and nothing more; the all-s statement stays
Sturm-certified in `computations/`.

Verification was run in the cloud container with the pinned toolchain,
not on the Mac.  That is sound here because the package has zero
dependencies, and it leaves the machine-safety contract untouched — but
per AGENTS.md it is not a Mac-side verification, and none has been run.

## 9. Honesty box

* The refutations rest on ONE coefficient each, but both are exact and
  final under the §1.3 predicate, with every contributing configuration
  computed.  One counterexample is all a refutation needs.
* Claim `(i′)` is **verified, not proved**: it holds at every entry and
  final window computed here, and the functional verdicts on the
  *provisional* parts of the polynomials are not claimed at all.
* UNREACHED sets are wall-clock and memory dependent, hence not
  reproducible run to run.  Only per-exponent-final statements are
  claimed; those are schedule-independent.
* `E*` bounds the truncation *exponent*, not the truncation
  *magnitude*: the tail-mass prefactor of ε_slab is not computed here.
* `T[2,2]` is now complete (225 of 314 configurations, 89 unreached,
  final below E = 72), so all three blocked channels are computed.
  **RP at M = 2 (claim ii) has still NOT been re-run** — the M = 1 data
  point stands unamended, and the 3×3 Gram at M = 2 is untested.
* The three T[0,1] configurations that bound its global window
  (E = 68, 76, 76) remain unreached: they exceed a 5 GB address-space
  cap, not merely a time budget.  They do not affect any verdict above,
  by the per-exponent predicate.
