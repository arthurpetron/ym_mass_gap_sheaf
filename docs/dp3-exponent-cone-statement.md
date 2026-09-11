# DP.3 at exponent granularity — formal re-statement, and the first RP data point

> **AMENDED 2026-07-26 (M = 2 round).  Claim (i) as stated below is
> REFUTED, at BOTH granularities.**  The coefficient cone `C_exp`
> (§1, `a_E >= 0`) is not preserved by one blocking step at activity
> truncation M = 2:
>
> * entry level — `T[1,1]` carries the coefficient **-32/3 at s^76**
>   (all eight configurations at that exponent computed; final);
> * aggregated level — the blocked image `(Bv)_1` carries **-64/3 at
>   s^79**, with the sibling channels contributing *exactly zero*
>   there, so the repair route named in §2(i)(a) below ("prove (i) at
>   the aggregated level ... exactly the DP.6 pattern") is **closed**.
>
> What survives is positivity as a FUNCTION: `T[1,1]` and the blocked
> images are Sturm-positive on all of (0,1) despite the negative
> coefficients.  The cone is therefore restated functionally —
> **claim (i')**, §2(i') — which is what the Birkhoff/Hilbert
> machinery of DP.2 actually consumes; the coefficientwise version was
> a convenience that no measurement in this program ever used.
> Details, method, and the eps_slab(M) certificate:
> `notes/dp3-m2-cone-refutation.md`; data
> `computations/dp3_m2_entries.json`; pins `tests/test_dp3_m2.py`.
> Claim (ii) (RP) is untouched by this round and has NOT been re-run
> at M = 2.

**Date.** 2026-07-25.
**Predecessors.** DP.2 (exact blocked kernel `T[n,m](s)` on the 2x2x1 slab,
`ym_dp6/computations/slab_blocking_kernel.py`, Sturm-positive entries on (0,1));
DP.6 (signed-sector survival: per-PROFILE channels fail, per-EXPONENT aggregation
succeeds, `ym_dp6/computations/dp6_signed_survival.py`); DP.6-U1 (discriminator
tags, standing audit rule: no group-blind step may carry gap weight).
**Code for the data point.** `/home/claude/dp3/dp3_rp_check.py`,
results `/home/claude/dp3/dp3_rp_results.json`, pins `/home/claude/dp3/test_dp3_rp.py`
(7 tests, all green). All arithmetic exact (Fraction / integer s-polynomials;
Sturm sign certification on (0,1); no floats in any verdict path).

---

## 0. Why the granularity had to be corrected

DP.6 proved that the dual cone **cannot** be built on profile channels: of the
260 spin-profile classes of the triple corpus on the 4-cube boundary, 4 have
negative s-weighted channel sums

| profile | E | class channel sign |
|---|---|---|
| 1^11 2^11 3^1 | 136 | negative |
| 1^9 2^12 3^1  | 138 | negative |
| 1^10 2^11 3^2 | 148 | negative |
| 1^8 2^11 3^4  | 172 | negative |

and the sign is **s-independent**, because a class channel is the exact monomial
`c_class · (ΣZ)_class · s^E` (both `c` and `E` are functions of the profile
alone) — no weighting in s can ever rescue a profile channel. Positivity *is*
restored one level up: summing all classes sharing an s-exponent E gives a
positive coefficient at **every** occurring E (cancellation margins ~50–500x at
E ∈ {136, 138, 148, 172}), and the global sum is an 80-monomial polynomial with
all coefficients positive. The dual cone of this program therefore lives at
**exponent granularity**, and every downstream milestone must be restated there.

## 1. The exponent-aggregated channel space and the cone C_exp

Fix a finite dual corpus K (a set of admissible spin/charge assignments on a
complex, e.g. the DP.6 triple corpus, or the image of a blocking step). Each
assignment κ carries the exact amplitude `Z(κ)` (certified vertex product
formula) and the heat-kernel weight `w(κ) = c(κ) s^{E(κ)}` with
`c(κ) = Π_{faces, n>0} d_n ∈ Z_{>0}` and `E(κ) = Σ_faces C(n_f)` (4x Casimir
`C(n) = n(n+2)` for SU(2), `C(m) = m²` for U(1)).

**Definition (exponent channel).** For each occurring exponent E,

    v_E(s)  :=  ( Σ_{κ ∈ K : E(κ) = E}  c(κ) Z(κ) )  ·  s^E
             =   a_E · s^E,        a_E ∈ Q.

The **exponent-aggregated channel space** is the finite-dimensional space
spanned by the monomials {v_E}; the **dual cone at exponent granularity** is

    C_exp  :=  { Σ_E λ_E v_E  :  λ_E ≥ 0 }        (nonnegative combinations),

and the corpus K is **admitted** to C_exp iff every aggregated coefficient
`a_E ≥ 0` — equivalently iff its total dual polynomial has nonnegative
coefficients. (Profile channels are strictly finer: DP.6 shows admission FAILS
at profile granularity and HOLDS at exponent granularity for the triple corpus;
aggregating further — to the single global value — would discard the channel
structure the contraction machinery needs.)

## 2. The three claims DP.3 must establish

### (i) Cone preservation under one blocking step

Let `B` denote the one-step blocking map realized by the DP.2 slab kernel: a
coarse observable in channel n receives from the fine layer

    (B v)_n (s)  =  Σ_m  T[n,m](s) · v_m(s),

`T[n,m](s)` the exact owned-boundary slab kernel (an s-polynomial whose
coefficients are themselves exponent-aggregated: one exact rational per
s-exponent, summed over all interior dressings reaching that exponent — the
kernel entry IS an exponent-granularity object by construction).

**Claim DP.3-(i) (cone preservation).** For dual data admitted at exponent
granularity (all input `a_E ≥ 0`), the blocked data is again admitted: every
s-exponent coefficient of every coarse channel `(B v)_n` is nonnegative.

Two precisions. (a) Sufficient condition actually available: if every kernel
entry `T[n,m]` is coefficientwise nonnegative, preservation is immediate
(products and sums of nonneg-coefficient polynomials). DP.2's Sturm result
("entries positive as functions on (0,1)") is weaker than coefficientwise
positivity; at M = 1 the computed entries happen to be coefficientwise
nonnegative, so preservation holds trivially at this truncation — the open
content of (i) lives at larger M, where signed 6j interference can in principle
put negative coefficients into an entry while leaving it positive as a
function. If that occurs, claim (i) must be proved at the aggregated level
(cancellation across m at fixed output exponent), exactly the DP.6 pattern.

> **2026-07-26: this is exactly what happened, and the aggregated repair
> FAILED.**  At M = 2 signed 6j interference does put a negative
> coefficient into an entry (`T[1,1]`, -32/3 at s^76), the entry does
> remain positive as a function, and aggregation across m does NOT
> rescue coefficientwise positivity: `(Bv)_1` has -64/3 at s^79 with
> both sibling channels vanishing at that exponent.  See claim (i')
> below.
(b) The cone on which contraction will eventually be run is the **enveloped**
(corridor-restricted) cone of DP.2/P19, since the Birkhoff diameter of the full
positive cone is huge (Δ ≈ 12–65); claim (i) is stated for the full C_exp, and
its enveloped refinement (blocked image lands in the corridor) is part of the
contraction milestone, not of DP.3.

### (i') Functional cone preservation — the replacement for (i) (added 2026-07-26)

Let `C_fun` be the cone of dual data whose channels are positive as
*functions* on (0,1) (Sturm-certifiable), rather than coefficientwise.

**Claim DP.3-(i') (functional cone preservation).**  For dual data
admitted at exponent granularity, the blocked data has every coarse
channel `(Bv)_n` positive as a function on (0,1).

This is strictly weaker than (i), is what DP.2's Birkhoff/Hilbert
diameter measurements consume (they evaluate entries at each s), and is
contradicted by nothing computed in the M = 2 round: every entry and
every blocked image checked there is Sturm-positive on its final part.
Status: **verified, not proved.**

Recorded with it, because it governs how (i') feeds the contraction
milestone: **positive diagonal conjugation is Birkhoff-neutral.**  The
Hilbert projective metric satisfies `d(Df, Dg) = d(f, g)` for positive
diagonal `D`, so an h-transform `P = D_{1/h} T D_{h'}` has the same
projective diameter, hence the same contraction coefficient, as `T`.  A
contraction rate may be computed on an unnormalized composed kernel and
transported to the normalized/Markovized channel with no re-estimation.

### (ii) Reflection positivity of the blocked dual coefficients

**Claim DP.3-(ii) (RP at exponent granularity).** Let θ be the chessboard
(link) reflection across the blocking plane of the slab (the plane z = 1/2:
contains no vertices, bisects the vertical links). For half-configuration
observables `f = Σ_n λ_n f_n`, `f_n = χ_n(coarse perimeter loop of the upper
half)`, supported strictly above the plane, the OS Gram built from the blocked
dual coefficients,

    G[n,m](s)  :=  ⟨ θ(f_n) · f_m ⟩_slab  =  T[n,m](s)      (SU(2), real χ)
    G[n,m](s)  :=  T_U1[-n, m](s)                            (U(1), θ antilinear)

is positive semidefinite for every s ∈ (0,1), at every truncation M and coarse
cutoff N. Each Gram entry is an exponent-aggregated polynomial; PSD-ness of
the matrix of aggregated coefficients (as functions of s) is the precise
"RP survives in the dual coefficients" statement. RP is what makes the blocked
dual data *quantum-mechanically meaningful* (an inner product on half-space
states, hence a transfer operator and a spectrum for the gap to live in);
without (ii), cone preservation (i) would be positivity of bookkeeping numbers
with no Hilbert space behind them.

### (iii) What DP.6 already gives; what remains

Given: **admission**. The fine corpus is in C_exp (all aggregated coefficients
positive; global 80-monomial polynomial positive; margins 50–500x at the four
negative-class exponents). Also given by DP.2: existence and exactness of the
blocking kernel, entrywise Sturm positivity, and the flow measurement
s' = 0.0341 < s⁴ = 0.0625 at s = 1/2 with corridor narrowing.

Remaining for DP.3 proper: (a) claim (i) at truncations where entries are not
trivially coefficientwise positive (M ≥ 2), (b) claim (ii) — of which THIS
deliverable banks the first exact data point (§4), at M = 1, N = 3, s ∈
{1/4, 1/2, 3/4}, plus a stronger all-s Sturm certificate on every leading
principal minor, (c) iteration stability: both claims under repeated blocking
(the one-step kernel composed with itself in the coarse channel space).

### (iv) Discriminator tags (audit rule: no group-blind step carries gap weight)

| step | tag | evidence |
|---|---|---|
| Duality transform, definition of C_exp, exponent aggregation | **group-blind** (scaffolding) | identical construction for U(1); abelian admission is free (amplitudes ∈ {0,1}) |
| Entrywise kernel positivity of T[n,m] on (0,1) | **group-generic** | U(1) entries are literal lattice-point counts (positive integers by construction); SU(2) positivity is measured, and 4D U(1) is gapless — so entry positivity cannot be the mechanism |
| RP / PSD of the OS Gram (claim ii) | **group-blind** (scaffolding) | verified PSD for BOTH SU(2) and U(1) below; structurally expected for any compact group: the truncated heat kernel has positive character coefficients `d_n s^{C(n)}`, which is exactly the Osterwalder–Seiler condition for link RP, and truncation in n preserves it. RP must never be cited as gap-producing |
| Cone preservation (claim i) at M ≥ 2 | **mixed** | the liability (negative coefficients from signed 6j interference) exists only non-abelianly; controlling it restores what U(1) has for free — tag: *liability control / admission*, not mechanism |
| Contraction acceleration s' < s⁴ and corridor narrowing | **non-abelian — the only gap-carrying step** | SU(2): s' = 0.0341 < 0.0625; U(1) control tracks the 2D rule exactly (ρ ratios ≡ 1). Named non-abelian ingredients: univalence failure d_n = n+1 > 1 feeding c' = c⁴/d³, and transverse interference channels absent abelianly |

The eventual chain must read: admission (DP.6, scaffolding) → RP (DP.3-ii,
scaffolding) → cone preservation (DP.3-i, liability control) → contraction on
the enveloped cone (non-abelian, the gap) → spectral gap (abstract Birkhoff,
scaffolding).

## 3. The reflection pairing used, and why it is the OS one

The slab is the 2x2x1 brick, vertices (x,y,z), x,y ∈ {0,1,2}, z ∈ {0,1}. The
reflection is θ: (x,y,z) ↦ (x,y,1−z), the plane **z = 1/2**, which contains no
vertices and bisects the nine vertical links: this is **link reflection**
(chessboard reflection through a half-integer plane), the reflection adapted to
the blocking plane. Under θ the four top tiles swap with the four bottom
tiles, the twelve vertical faces map to themselves orientation-reversed, and
the coarse top perimeter loop maps to the bottom loop with the same in-plane
orientation. The owned-boundary measure Π_f K_M(U_f; s) is θ-invariant
(K_M is a real class function, K_M(U⁻¹) = K_M(U)).

The OS observables must live strictly above the plane: `f_n = χ_n(L_top)`
depends only on the four z = 1 perimeter links — entirely inside z > 1/2 (the
vertical links, which cross the plane, are not used). The OS map is
**antilinear**: (θf)(U) = conj(f(θU)). Hence

* SU(2): θf_n = χ_n(L_bot) (characters real, reps self-conjugate), so
  `G[n,m] = ⟨θ(f_n) f_m⟩ = T[n,m](s)` — the DP.2 kernel entry read directly as
  ⟨reflected half | slab | half⟩. No symmetrization was applied or needed:
  T[0,1] = T[1,0] was verified as an exact polynomial identity (z-flip
  symmetry of the geometry), so the extracted matrix is symmetric.
* U(1): θf_n = conj(χ_n(L_bot)) = χ_{-n}(L_bot), so
  `G[n,m] = T_U1[-n, m]` (module convention T[top, bottom]; equal to
  T_U1[m, -n] by the verified z-flip identity). **The conjugation is
  material**: the exact check `T_U1[1,1] ≠ T_U1[-1,1]` passes
  (T_U1[1,1] = s^8, one configuration; T_U1[-1,1] = 2s^8 + 12s^10 + 2s^12,
  the charge-neutral channel with its full dressing), so the conjugated and
  unconjugated pairings are genuinely different matrices. Both were computed;
  only the conjugated one is the OS form.

Normalization: ⟨·⟩ is the unnormalized slab integral; dividing by
Z = T[0,0] > 0 rescales G by a positive constant and cannot change PSD-ness.
Gauge fixing by the adapted spanning tree (which includes one crossing
vertical edge) is value-preserving for gauge-invariant integrands, so the
reflection argument applies to the ungauged form of the same numbers.

## 4. The first RP data point (banked)

Scheme: owned-boundary slab, activity truncation **M = 1**, coarse cutoff
**N = 3**. At M = 1 the SU(2) spin-3 row and the U(1) charge-±3 rows are
identically zero (the coarse loop cannot be dressed into the trivial channel
by spin/charge ≤ 1 activities); they are kept as exact zero rows (PSD-neutral:
zero pivot with zero column) and reported, not hidden.

**Verdict: PSD holds — SU(2) and U(1) — at s = 1/4, 1/2, 3/4, and moreover on
ALL of (0,1) by Sturm certification of every leading principal minor.**

SU(2) OS Gram (basis order 0,1,2,3; entries at M = 1):

    T[0,0] = 1 + 16s^18 + 16s^30 + 32s^36 + 16s^42 + 4s^48
    T[0,1] = 2s^12 + 8s^24 + 8s^30 + 14s^36        T[1,1] = 5s^24 + 12s^30 + 2s^36
    T[0,2] = 4s^48      T[1,2] = 2s^36      T[2,2] = 4s^48      T[·,3] = 0

    minor 1x1 = T[0,0]                                    Sturm: positive on (0,1)
    minor 2x2 = s^24 + 12s^30 − 30s^36 + 48s^42 + 72s^48 − 16s^54
                + 64s^60 + 272s^66 + 80s^72 + 80s^78 + 8s^84      Sturm: positive
    minor 3x3 = 48s^78 − 120s^84 + 128s^90 + 320s^96 − 128s^102
                + 256s^108 + 1152s^114 + 448s^120 + 128s^126      Sturm: positive
    minor 4x4 = 0 (exact zero row, spin 3)                        Sturm: zero

    s = 1/2: pivots [70373040226561/70368744177664,
                     170108259427459713/2417999250345375404392448,
                     33833778425931/15586334101769027236107649024, 0] — PSD
    (minors and pivots at s = 1/4, 3/4 equally exact: dp3_rp_results.json)

U(1) OS Gram (basis order 0, 1, −1, 2, −2, 3, −3; G[n,m] = T_U1[−n,m]):
all five nontrivial leading minors Sturm-positive on (0,1), minors 6,7 exactly
zero (charge-±3 rows); PSD at all three s values, e.g. s = 1/2 pivots
[37201/32768, 1054645/76187648, 29094681/2159912960, 41494529/3813498028032,
921075/84980795392, 0, 0].

**Control (pairing falsification).** The unconjugated U(1) matrix T_U1[n,m] —
the plausible-looking wrong pairing — is **not** PSD: its 2x2 leading minor is
`−8s^12 − 30s^16 − 24s^18 − 64s^20 − 48s^22 − 47s^24`, negative on all of
(0,1), and LDLᵀ fails with a negative second pivot at every probed s
(−43247/19046912 at s = 1/2). Had the antilinearity of θ been dropped, DP.3
would have announced a spurious RP violation. For SU(2) this ambiguity does
not exist (real characters); for every group with complex representations the
conjugation is load-bearing. This is itself a small group-structure lesson:
*which* matrix is the Gram depends on the reality of the representation ring.

**An exponent-granularity echo inside the minors.** The SU(2) 2x2 and 3x3
minors are NOT coefficientwise positive (−30s^36, −16s^54; −120s^84, −128s^102)
yet are positive as functions on (0,1): positivity of the RP minors is again a
cancellation phenomenon across s-exponents — the same granularity lesson DP.6
taught for the channel sums, now appearing one level up in the Gram algebra.

## 5. Honesty box

* This is ONE data point: one blocking step, one truncation (M = 1), small
  coarse basis (effective rank 3 for SU(2), 5 for U(1)). It verifies; it does
  not prove claim (ii).
* PSD success here was structurally *expected* (truncated heat kernel has
  positive character coefficients ⇒ Osterwalder–Seiler link RP survives
  truncation), which is precisely why the result is tagged group-blind
  scaffolding. The decisive follow-ups are: M = 2 (where signed interference
  can enter kernel coefficients), the iterated kernel (does RP survive
  *composition* in the coarse channels), and RP of the blocked measure tested
  against a *larger* half-space observable algebra than the perimeter-loop
  characters (e.g. products of tile characters), where failure is not
  structurally excluded.
* The spin-3 / charge-±3 zero rows mean N = 3 adds no information beyond
  N = 2 at this truncation; quoted "effective" Gram sizes are 3 and 5.
* The Gram uses the unnormalized slab integral; all PSD statements are
  normalization-independent, but any future comparison of Gram *magnitudes*
  across schemes must divide by T[0,0].

## 6. Reproduction

    cd /home/claude/dp3
    python dp3_rp_check.py              # full rebuild (~2 min), writes JSON
    python dp3_rp_check.py --from-json  # re-verify Gram algebra from saved kernels
    python -m pytest test_dp3_rp.py -v  # 7 pins, all green (~3 s)

Kernel engines reused unmodified from `/home/claude/ym_dp6/computations/`:
`slab_blocking_kernel.py` (SU(2), exact Haar contraction),
`dp6_u1_slab_blocking.py` (U(1), certified lattice-point count),
`exact_haar_network.py` (Sturm sign certification on (0,1)).
