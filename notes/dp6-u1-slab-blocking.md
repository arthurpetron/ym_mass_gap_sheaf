# DP.6-U1 — the abelian contraction-step discriminator: verdict on the U(1) slab blocking

**Date.** 2026-07-24.
**Code.** `computations/dp6_u1_slab_blocking.py` (exact abelian kernel +
DP.2 measurement protocol), `tests/test_dp6_u1_slab_blocking.py`
(9 pinned exact witnesses), `dp6_u1_results.json` (full exact ledger).
**Arithmetic.** Exact throughout: every kernel entry is an s-polynomial
with positive-integer-count coefficients (`Fraction`); floats appear only
in the log-space flow fit, exactly as in the SU(2) protocol.

## 1. The banked prediction

> U(1) slab blocking should track its 2D rule s' = s^4 exactly with
> corridor NON-narrowing (univalence d_m = 1 kills the d^3 denominator),
> vs the measured SU(2) s' = 0.0341 < s^4 = 0.0625 at s = 1/2 with
> corridor narrowing (flowed 1.82 vs wheel 2.23 at s = 1/2; 0.79 at
> s = 3/4).

## 2. Protocol and fairness of comparison

Same object, same instrument, abelian group data. The complex, the
adapted spanning tree, the twenty faces (4 top tiles, 4 bottom tiles,
4 interior walls, 8 perimeter walls), both coarse perimeter loops, and
the Hilbert-diameter meter are **imported from
`computations.slab_blocking_kernel`** — the U(1) run reuses the SU(2)
slab's ∂-data verbatim (∂-consistency by construction, plus an
independent full-33-edge conservation check in gate 3).

U(1) group data: charges m ∈ ℤ, d_m = 1, χ_m = e^{imθ}, fusion
m ⊗ n = m + n (single path — no recoupling, no 6j), Casimir m², activity
s^{m²}.

**Normalization mapping.** SU(2) uses s = e^{−t/4} so the activity
exponent is the integer Casimir polynomial n(n+2) = 4j(j+1); the U(1)
analogue takes s = e^{−t} so the exponent is the integer Casimir m².
In *both* parametrizations the exact 2D blocking rule c'_n = c_n⁴/d_n³
reads **s' = s⁴** (SU(2): d_n s^{4n(n+2)}; U(1): s^{4m²}), so the
"measured s' vs s⁴" comparison is parametrization-fair group by group —
the fair statement is the 2D-rule form, and that is what was measured.

Because Haar integration of e^{ikθ} is δ_{k,0}, the abelian
owned-boundary kernel is an exact lattice-point count: face charges
k ∈ ℤ²⁰, |k_f| ≤ M, with winding conservation on every free edge. The
constraint system has rank 16 (= #free edges) and its saturated integer
kernel is exactly the four cube-boundary 2-cycles (Smith invariants
1,1,1,1 — certified, gate 0), so

  T_U1[n,m](s) = Σ over (uniform charged tiles) + (cube-flip lattice ℤ⁴)
                 of s^{Σ k_f²},

a finite exact enumeration at each truncation M, cross-validated by an
independent tile-sweep parametrization with full-boundary constraint
checking (gate 3).

**SU(2) pin check (driving proof).** Re-running the mirrored DP.2
machinery (kernel_entry_skeleton, N = 2, M = 1, dp2_measure protocol)
reproduced the banked numbers to the digit: s' = 0.034121 (s⁴ = 0.0625),
corridor 1.816737, whole-cone Δ = 31.88 at s = 1/2; s' = 0.249521
(s⁴ = 0.316406), corridor 0.792869, Δ = 12.51 at s = 3/4. All five
mirrored `tests/test_slab_blocking.py` pins pass.

## 3. Non-degeneracy (the honest caveat, resolved)

The feared degeneracy — a diagonal U(1) kernel with nothing for the
projective machinery to measure — **does not occur**. Charge
conservation does *not* force n = m: each coarse loop bounds its own
disk of tiles, so T_U1[n,m] ≠ 0 for every (n,m), and the transverse
sector is a genuine 4-parameter family of charge-conserving **cube
flips** (the abelian remnant of transverse fluctuation). All entries are
positive integer counts — the abelian dual has no sign structure and no
multiplicity: nothing exists to interfere. Symmetries verified exactly:
T[n,m] = T[−n,−m] (conjugation) and T[n,m] = T[m,n] (z-flip). One real
abelian rigidity was found: at M = 1 the charge-2 channels are empty
(T[2,±2] = 0) because the SU(2) triad (1,1,2) has no abelian counterpart
— fusion is a single path — so the charge-2 sector opens only at M ≥ 2.

## 4. Results (truncation-converged; sector = {−2..2} throughout for M ≥ 2)

Where the prediction is exactly right — and where it fails:

- **Frozen-side scheme: exact 2D, both groups.** With perimeter walls
  frozen, every cube flip dies (univalence at thickness one) and
  T = s^{4n²+4m²} exactly: c' = c⁴, corridor exactly zero (gate 2).
  Identical structure to SU(2)'s gate 3. The open-disk gate likewise:
  c'_n = s^{4n²} exactly (gate 1).
- **Owned-boundary scheme: U(1) does NOT track s' = s⁴.**

| quantity (owned-boundary, one step) | SU(2) (M=1, pinned) | U(1) (M=5, converged) |
|---|---|---|
| s' at s = 1/2 (2D rule: 0.0625) | **0.034121** (< s⁴) | **0.126197** (> s⁴) |
| s' at s = 3/4 (2D rule: 0.316406) | **0.249521** (< s⁴) | **0.451794** (> s⁴) |
| corridor log-width, s = 1/2 | 1.8167 (wheel: 2.23) | 0.4614 |
| corridor log-width, s = 3/4 | 0.7929 | 0.0119 |
| whole-cone Birkhoff Δ, s = 1/2 | 31.88 | 22.18 |
| whole-cone Birkhoff Δ, s = 3/4 | 12.51 | 9.21 |

Exact witness that the U(1) deviation is real (not fit noise), at M = 2,
s = 1/2:  ρ₁ = (v₁/v₀)/s⁴ = 14330603980276662272/11258810062447479809 ≠ 1
(≈ 1.2728), ρ₂ = 148520413760355041280/11258810062447479809 (≈ 13.19).

**Truncation stability.** Exact statement, certified for M = 1..5: every
configuration first admitted at truncation M+1 charges some face to
|k| = M+1, so T_{M+1} − T_M has minimal degree ≥ (M+1)² (measured gaps
12, 26, 48, 80, ...). Measured quantities: at s = 1/2 all reported
digits are stable from M = 3 on (M = 4, 5, 6 agree to 10 digits); at
s = 3/4 from M = 5 on (M = 5 vs 6 agree to 9 digits). M = 5 is reported.
At M = 1 the charge-2 channels are empty (sector {−1,0,1}) — the
same-truncation comparison with SU(2)'s M = 1 numbers is therefore made
at the U(1)-converged values, which the exact min-degree bound shows are
the M → ∞ answers to far beyond the quoted precision.

## 5. Verdict and interpretation for the discriminator audit rule

**The banked prediction is REFUTED in its strong form — and the
discriminator comes out sharpened, not weakened.**

The reasoning error in the banked form: univalence (d = 1) does kill the
d³ denominator, but it does not kill the *transverse charge sector* of
the owned-boundary block — the cube-flip lattice survives abelianization
and dresses the kernel. Exact 2D tracking holds precisely where it also
holds for SU(2) (frozen-side scheme, open-disk gate), so it cannot
discriminate.

What does discriminate is the **sign of the one-step coupling defect**:

- **U(1) anti-renormalizes:** s' = 0.126 > s⁴ = 0.0625 (s = 1/2);
  0.452 > 0.316 (s = 3/4). Abelian transverse flips *slow* the damping —
  the blocked activities are fatter than the 2D rule.
- **SU(2) super-renormalizes:** s' = 0.0341 < 0.0625; 0.2495 < 0.3164.
  Non-abelian transverse dressing *accelerates* the damping.

Since the abelian kernel contains everything except recoupling — same
geometry, same envelope, same charge-conserving transverse excitations,
all-positive weights — the SU(2) acceleration (s' < s⁴, the
contraction-friendly direction the mass-gap chain needs) is produced by
the only structure the abelian theory lacks: **off-diagonal non-abelian
recoupling at the 4-valent interior edge**. That is the correct
one-paragraph audit rule going forward: *the discriminator for "the
contraction step is genuinely non-abelian" is s' < s⁴ at one blocking
step, not exactness of the 2D rule; U(1) sits provably on the other side
(s' > s⁴, exact-witness ρ₁ > 1).* Consistently, U(1) reproduces the
qualitative corridor phenomenology (corridor ≪ whole-cone diameter, and
narrowing with coupling: 0.46 → 0.012) — the enveloped-cone *mechanism*
is group-generic — while the *direction of the flow defect* is the
group-sensitive number. This also matches physics: 3D U(1) is confining
but gapless-photon-like at weak coupling (Polyakov's mechanism is
instanton-driven, not blocking-contraction-driven), whereas the SU(2)
one-step map is already contraction-accelerating at these couplings.

## 6. Files

- `computations/dp6_u1_slab_blocking.py` — module (gates + kernel +
  measurements; `python -m computations.dp6_u1_slab_blocking 2 5`).
- `tests/test_dp6_u1_slab_blocking.py` — 9 pins (all pass; the 5
  mirrored SU(2) slab pins also pass in the same session).
- `dp6_u1_results.json` — exact kernel entries (M = 1, 2), exact v/ρ
  ledgers, per-M stability table (M = 1..6), gates, verdict.
