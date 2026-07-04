# Coulomb-gas duality (C1) and graded reflection positivity (C2) for R1

**Residual R1.** `Δ²_t V(t) ≥ −2` for all `t`, `w∈[0,1)`, where `V(t)=⟨D²⟩_t` is the
variance of the flux `D=t−2p` under `μ_t(p) ∝ coeffW(w,p)·coeffW(w,t−p)`,
`coeffW w s=(s+1)w^{s(s+2)}`.  Equivalently `U(t):=V(t)+t²` is discretely convex.
The wall is the coupled even/odd (integer/half-integer SU(2) spin = SO(3) vs spinor)
parity structure; the parity is the center-`Z₂` / `(−1)^F` / spin structure.

This memo tests the two dual handles **C1 (Poisson/Villain–Coulomb-gas duality)** and
**C2 (transfer-matrix RP graded by `(−1)^F`)**.  All numbers below come from
`computations/coulomb_rp_analysis.py` and `.../quantify.py` (exact `Fraction`-in-`w`
Lean mirror objects + `mpmath` D-lattice theta objects).  This mirrors, it does not
prove.

---

## Bottom line

| Handle | Does it make R1 a *manifest* positivity? | What it *does* deliver |
|---|---|---|
| **C1 Coulomb-gas / Poisson duality** | **No.** | Confirms the sector-flip is exactly `ϑ₄(w²)⁴`, electric-even ↔ magnetic-odd, Jacobi `ϑ₃⁴=ϑ₂⁴+ϑ₄⁴` (to 1e-61). But duality does not decouple the coupling into a free Gaussian, and it maps the tight `w→0` corner the **wrong way**. |
| **C2 graded RP** | **No** (as a clean split). | Correctly identifies the wall as the `(−1)^F` sector-flip and **exactly reproduces the existing two-piece Lean reduction** (`ContinuumFloor` + `FiniteCorrectionBound`). The negative finite correction is intrinsic; no free-lunch SOS. |

**New forward progress (the useful by-product).** Two quantitative reductions fell out:

1. **A scale-matched uniform bound with a clean rational constant:**
   ```
   Δ²V(s) + 2  ≥  (3/8)·[ 2(1 − (G_odd − G_even)) ]  =  (3/4)·(1 − ϑ₄(w²)⁴)     ∀ s, w,
   ```
   manifestly `≥ 0` (since `ϑ₄⁴ ≤ 1`). `inf_{s,w} slack/sectorflip = 3/8` **exactly**,
   attained at the corner `(s=0, w→0)` where `slack ~ 6w²` and `sectorflip ~ 16w²`.
   This is a *stronger, better-conditioned* target than the razor-thin
   `FiniteCorrectionBound`: it has a **finite 3/8 margin** and ties `slack` directly to
   the already-PROVED sector-flip object.
2. **The mass factor is inessential.** The bare truncated-theta variance
   `G(t)=ξ_t/θ_t` (drop the `(M²−D²)` envelope) already satisfies `Δ²G + 2 ≥ 0`
   for all tested `(s,w)`. So the floor is driven by the parity coupling, not the
   envelope — attack the simpler `G`-floor first.

---

## C1 — Coulomb-gas / Poisson–Villain duality

**Setup.** The tilted measure is a (truncated) Villain / periodic-Gaussian partition
sum. On the D-lattice, `θ_t = Σ_D w^{D²/2}`; the even/odd completions are
`θ₃(w²)` (electric, integer spin) and `θ₂(w²)` (magnetic center-vortex, half-integer
spin). Poisson summation is the Kramers–Wannier / electric–magnetic dual:
`θ₃(q=e^{−πα}) = α^{−1/2} θ₃(e^{−π/α})`, `α = −log(w²)/π`.

**Result C1.1 — the sector-flip is an exact modular object (verified).**
The continuum shadow gives `V(t)→G_parity`, `Δ²V(even, t→∞) → −2(G_odd−G_even)`.
Numerically, to full precision:
```
G_odd(w) − G_even(w)  =  ϑ₄(w²)⁴  =  dlog k / dlog w        (k = (ϑ₂/ϑ₃)² elliptic modulus)
ϑ₃⁴ = ϑ₂⁴ + ϑ₄⁴   (Jacobi)   verified to 1e-61.
```
So the sector-flip `2(1−(G_odd−G_even)) = 2(1 − ϑ₄(w²)⁴) ≥ 0` is precisely the PROVED
`ContinuumShadowFloor.ContinuumFloor (a)` object, and it *is* the electric-even ↔
magnetic-odd coupling. This much of the duality picture is real and exact.

**Result C1.2 — duality does NOT decouple the parity (the obstruction).**
For a "free-fermion / bosonization" decoupling we would need `Δ²V+2` to become a single
Gaussian in a dual variable with no even/odd coupling. It does not: the coupling term
`ϑ₄(w²)⁴` ranges over the *whole* interval `(0,1)` as `w:1→0` and is exactly the
irreducible piece. It is a clean modular function, but it is the coupling, not its
removal.

**Result C1.3 — Poisson maps the tight corner the wrong way.**
Self-dual point `α=1` at `w=e^{−π/2}=0.2079`. The binding regime is the deep few-mode
corner `w→0` (`α→∞`, `q→0`), where the floor is razor-tight. Reflection sends this to
its many-mode dual `w→1` (`q→1`) — the opposite side of the operating window. Measured:

| w | α=−log(w²)/π | q=w² | q_dual=e^{−π/α} | regime |
|---|---|---|---|---|
| 0.02 | 2.49 | 4e-4 | 0.283 | **few-mode, TIGHT** |
| 0.2079 | 1.00 | 0.043 | 0.043 | self-dual |
| 0.7071 | 0.22 | 0.5 | 7e-7 | many-mode |

**Result C1.4 — the true extremiser is invisible to any dual free field.**
`inf_w slack/(w²(1−w²))` is `144/25 = 5.76` at **finite `s=0`** (`w²=1/6`), rising
monotonically in `s` to the continuum value `8`. The binding case is the smallest
finite window, not the `t→∞` / dual / free-field limit. A Coulomb-gas free energy is a
`t→∞` object; it cannot see the `s=0` extremiser.

> **C1 verdict.** The duality is exact and it *names* the coupling (`ϑ₄⁴`), but it does
> not turn the floor into a manifest positivity: it neither decouples the parity into a
> free Gaussian nor addresses the finite `s=0` extremiser, and it maps the tight corner
> away from itself. Negative for closure; useful only as the (already-known)
> identification of the sector-flip.

---

## C2 — reflection positivity of the transfer matrix, graded by `(−1)^F`

The proposal: `Δ²(V+t²)≥0` is a midpoint-vs-endpoints log-convexity; the midpoint `t+1`
flips center sector (even↔odd = NS↔R), so apply RP *within* each `(−1)^F` sector and
treat the flip as the separate bounded `ϑ₄⁴` term.

**Result C2.1 — within-sector convexity of `U=V+t²` is TRUE and clean.**
Restricting to a single parity (step 2): `V(t)+V(t+4)−2V(t+2)+8 ≥ 0` holds for **both**
parities, all `w`, with a comfortable minimum `≈ 6.95` (at `w=1/√2`). So each
`(−1)^F` block, on its own, is convex. **But this is the wrong second difference:** R1
is the *cross-sector step-1* second difference, which mixes the two blocks and cannot be
bounded by within-sector convexity alone.

**Result C2.2 — there is NO RP transfer operator (the log-concavity obstruction).**
If `V(t)` were `⟨v, T^t v⟩` for a reflection-positive `T`, the partition functions would
be log-*convex* (`Z_{t+2}Z_{t−2} ≥ Z_t²`). Measured, `θ_t` and `den_t` are log-*concave*
(`Z_{t+2}Z_{t−2} − Z_t² < 0` at every `t`, both parities, every `w`). So the naive
"`V` = matrix element, RP ⇒ convexity" route has no operator behind it.

**Result C2.3 — the exact sector-flip split reproduces the existing Lean reduction.**
Definitional exact identity (`G_e,G_o` = infinite even/odd theta variances):
```
Δ²V(s) + 2  =  [ 2(1 − (G_o − G_e)) ]  +  [ corr(s,w) ],
corr(s,w) = (V(s) − G_e) + (V(s+2) − G_e) − 2(V(s+1) − G_o).
```
- The bracket `2(1−(G_o−G_e)) = 2(1−ϑ₄⁴) ≥ 0` is **`ContinuumFloor (a)`** (PROVED-open).
- `corr(s,w)` is **NEGATIVE generically** (down to `−0.78` on the grid). It is exactly
  the open **`FiniteCorrectionBound (b)`** ("`Δ²V` dips a hair below its asymptote").

So C2 does **not** split into `[≥0] + [≥0]`. The negative finite correction is intrinsic;
the total stays `≥0` only because the sector-flip carries enough slack to absorb it. This
is a faithful re-derivation of why the two open Lean pieces exist — not a way around them.

**Result C2.4 — the absorption is quantified: a clean 3/8 floor.**
`inf_{s,w} slack / sectorflip = 3/8` **exactly** (corner `s=0, w→0`), i.e. the finite
correction never eats more than `5/8` of the sector-flip slack. Hence the manifestly
non-negative uniform bound
```
Δ²V(s) + 2  ≥  (3/8)·2(1 − (G_o − G_e))  =  (3/4)(1 − ϑ₄(w²)⁴).
```
Away from the corner the ratio rises (`0.40, 0.50, 0.86, 0.91, → 1` as `w→1`).

> **C2 verdict.** The `(−1)^F` grading is the *correct* diagnosis of the wall, and
> within-*sector* convexity genuinely holds — but it addresses the wrong (step-2) second
> difference. The physical (step-1) floor keeps an irreducible negative finite
> correction, so C2 yields **no manifest-positive split**. Its concrete payoff is the
> *scale-matched* reduction R1 ⇐ `[slack ≥ (3/4)(1−ϑ₄⁴)]`, which has a finite `3/8`
> margin and rides on the already-proved sector-flip object.

---

## Reconciliation with the proved continuum shadow

All three continuum facts are reproduced by the RP/duality bookkeeping as the
sector-graded partition functions:

- `V(t) → G_parity`, `Δ²V(even,∞) → −2(G_odd−G_even)`  — the sector-flip limit.
- `G_odd − G_even = ϑ₄(w²)⁴ ∈ (0,1)`  — the magnetic-charge (odd/spinor) excess, `→1` as
  `w→0`, `→0` as `w→1` (verified as `dlog k/dlog w`).
- `ϑ₃⁴ = ϑ₂⁴ + ϑ₄⁴`  — Jacobi; ties the electric (`ϑ₃`), magnetic (`ϑ₂`) and flip
  (`ϑ₄`) sectors (verified to 1e-61).

The floor `−2` is `2(1 − (G_o−G_e)) ≥ 0 ⇔ ϑ₄⁴ ≤ 1`, plus the finite-size correction.

---

## Reuse assessment for the existing RP / Krein / GNS Lean machinery

- **`ReflectionPositivity.lean` (`diagReflForm_nonneg`).** The right primitive — a
  diagonal weighted sum-of-squares `Σ c_s² w_s ≥ 0` for nonneg weights, all real `c` —
  *if* R1 could be written as such a Gram/SOS form. It cannot, two ways: (i) the
  three-body kernel `D0²+D2²−2D1²+2` is **separable/additive** in the D-lattice, so it
  collapses to the moment second-difference (no cross-terms, no Gram matrix in D-space);
  (ii) the transfer (`t`) direction has **no RP operator** (partition functions are
  log-concave, C2.2). Reusable only after a genuine Gram reformulation is found — none
  here.
- **`KreinOS.lean` (indefinite-metric / `Θκ`-positivity / physical quotient).** The
  `(−1)^F` parity grading *is* structurally a Krein involution `κ`, and this template is
  the natural home for a graded RP. But `KreinOS` *consumes* a `Θκ`-positivity input and
  packages the conclusion; our finding (C2.3) is precisely that the graded form is **not**
  `Θκ`-positive without the finite correction. So it hosts the conclusion, it does not
  supply the missing positivity.
- **GNS machinery (`GNS*`, `WilsonGNS`, `CompactTransferGNS`).** Reconstruction
  scaffolding downstream of positivity; nothing to consume until a positive form exists.

**Net.** Neither C1 nor C2 converts R1 into a manifest positivity. C1 is exact but
structurally orthogonal to the binding finite corner. C2 correctly grades the wall by
`(−1)^F` and faithfully reproduces the existing `ContinuumFloor + FiniteCorrectionBound`
two-piece reduction, with the negative finite correction shown to be intrinsic (no
free-lunch SOS). The tangible advances are the new scale-matched bound
`Δ²V+2 ≥ (3/4)(1−ϑ₄(w²)⁴)` (finite `3/8` margin, rides the proved sector-flip) and the
observation that the `(M²−D²)` envelope is inessential (the bare theta-variance already
obeys the floor).

*Scripts:* `computations/coulomb_rp_analysis.py`, `computations/quantify_coulomb_rp.py`.
Mirrors only; no Lean touched.
