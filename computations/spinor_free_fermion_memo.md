# "These are just spinors": refermionizing the R1 variance residual

**Question tested.** Residual R1 is `Δ²_t V(t) ≥ −2` for all integer `t ≥ 0` and `w ∈ [0,1)`,
where `V(t) = ⟨D²⟩` is the variance of the flux `D = t − 2p` under
`μ_t(p) ∝ coeffW(w,p)·coeffW(w,t−p)`, `coeffW(w,s) = (s+1) w^{s(s+2)}`.
Does refermionization (SU(2)₁ = free Dirac fermion, even/odd t = NS/R spin structure) turn the
coupled even/odd "parity wall" into a manifest free-fermion positivity?

**One-line verdict.** *Partially, and it is genuinely illuminating.* The object **is** an exact free
fermion — `V(t) = 4·Σₖ pₖ(1−pₖ)`, a sum of independent Bernoulli occupation-number variances —
throughout the entire strong-coupling regime `w ≲ 0.82`, which is exactly where R1 is tight.
But this Wick/determinant structure lives **at fixed fermion number**, and R1 is a **cross-sector
second difference in fermion number** (the even↔odd flip is `(−1)^F`, i.e. adding one fermion mode,
R↔NS). Fixed-number free-fermion positivity does **not** control cross-number differences. So the
picture explains *why* the wall exists (it is the `(−1)^F` alternation of `V`) and makes every
*fixed-t* slice a manifest sum-of-squares, but it does **not** dissolve the *uniform-in-t* wall,
which remains the theta cross-sector (log-concavity) statement already known to the project.

All numbers below are high-precision (mpmath dps 50–80, mpmath.polyroots with extraprec 400–800);
scripts: `computations/spinor_{explore,symbolic,roothp,rootlocus,fermionform,structure,corner}.py`.

---

## 1. The dictionary (exact, confirmed)

Write `s(s+2) = (s+1)²−1` and set `n = p+1`, `m = (t−p)+1`. Dropping constants that cancel in the
normalized measure,

```
μ_t(p) ∝ coeffW(w,p)·coeffW(w,t−p) ∝ n·m·w^{n²+m²},   n + m = N := t + 2,  n,m ≥ 1,   D = m − n.
```

So the fusion measure is **two identical independent particles** `n, m` on `ℤ_{≥1}` each with
single-particle weight

```
g(k) = k · w^{k²}        (k = 1, 2, 3, …),
```

**conditioned on the total `n + m = N`**. The flux is the *relative coordinate* `D = m − n`, and
`V(t) = Var(D | n+m=N) = 4·Var(n | n+m=N)`. Verified: `V(0)=0, V(1)=1, V(2)=12w²/(2+3w²)`, and the
full symbolic list `V(3)=3(6w⁴+1)/(2w⁴+3)`, `V(4)=w²(160w⁶+64)/(10w⁸+16w²+9)`, … (script `spinor_symbolic.py`).

- `g(k)=k w^{k²}` is a single Jacobi-theta building block: `Σ_{k∈ℤ} w^{k²} = ϑ₃(w)`,
  `Σ_{k≥1} k w^{k²}` is its "level-one" (charge-weighted) piece. `w^{k²}` = free-fermion mode energies,
  the `k = d_s` = dimension = fermion-number weight. So `μ_t` = **two free fermions with fixed total
  fermion number `N`**. This is the correct object; the parity of `N` (= parity of `t`) is the
  spin structure.

**Spin-structure / theta grounding (confirmed exactly, `spinor_structure.py`).**
Split the single-particle sum by parity: `A = Σ_{k odd} k w^{k²}`, `B = Σ_{k even} k w^{k²}`. Then

```
G_even (n,m same parity)     = A² + B²        (NS-like: even lattice)
G_odd  (n,m opposite parity) = 2AB            (R-like)
G_odd − G_even = −(A − B)²                    ← a perfect (negative) square.
```

`(A−B) = Σ_{k≥1}(−1)^{k−1} k w^{k²}` is a theta **derivative at the half-period** (a Dirac zero-mode /
Pfaffian of the two-particle problem). The perfect-square form is the two-fermion shadow of the
project's proved four-fermion identity `G_odd − G_even = ϑ₄(w²)⁴` and the abstruse identity
`ϑ₃⁴ = ϑ₂⁴ + ϑ₄⁴`: the project's `G` is the 4-copy (SO(8)-triality) object; the clean two-particle
core here is its square root. **The spin-structure decomposition is real and the difference is a
fermionic determinant — this part of "just spinors" is fully vindicated.**

---

## 2. It IS a free fermion (independent Bernoulli occupations) — but only for `w ≲ 0.82`

`n` is a **sum of independent Bernoullis** iff the fixed-`N` generating polynomial
`P_N(z) = Σ_{n=1}^{N−1} n(N−n) w^{n²+(N−n)²} z^n` is **real-rooted** (Newton). High-precision roots
(`spinor_roothp.py`, `spinor_rootlocus.py`):

| regime | root locus | fermion meaning |
|---|---|---|
| `w < w* ≈ 0.82` | all roots on the **negative real axis** | `n = 1 + Σₖ Bₖ`, independent Bernoulli(pₖ) — *classical/log-concave fermion* |
| `w = w*` | transition | — |
| `w → 1` | roots migrate to the **unit circle** `|z|=1` | Lee–Yang / physical-momentum fermion `e^{iθ}` |

The threshold `w*(N)` is remarkably flat: `w*(4) = √(2/3) = 0.816497` (exact, from
`disc = 4w¹⁶(4−9w⁴) ≥ 0`), rising to `w*(∞) ≈ 0.8226`. Above `w*` the naive occupation numbers become
complex; the roots only *reach* the unit circle cleanly as `w → 1` (at `w=0.99` they are on it to 1e-81).

**Free-fermion form of the variance (confirmed to 25+ digits for `w ≤ 0.8`, `spinor_fermionform.py`):**
with the roots giving `pₖ = 1/(1+ρₖ)`, `ρₖ = −(root)ₖ > 0`,

```
V(t) = 4 · Σₖ pₖ(1 − pₖ).      (n has N−2 Bernoulli modes)
```

Example (`w=0.7`): `V(t=6)` direct `= 2.54646062900358` vs fermion `= 2.54646062900358`. This is the
target free-fermion form `⟨D²⟩ = Σ f(1−f)` — a sum of **independent** occupation fluctuations, with
manifest positivity, log-concavity, and Wick structure.

**Why this matters for R1.** The R1 danger zone is exactly here. `min_t Δ²(V+t²)`:
`0.059 (w=0.1) → 0.48 (0.3) → 1.09 (0.5) → 1.69 (0.7) → 1.81 (0.9)`. The bound is **tight (→0) at
small `w`** and has huge slack (≈1.8) at `w→1`. So the free-fermion (real-rooted) regime
**covers the entire hard corner**; the break at `w > w*` is in the *easy* regime and is harmless.

---

## 3. The mechanism: R1 is the `(−1)^F` alternation of the variance

Small-`w` limits (`spinor_corner.py`):

```
V(t) → 0   for t even   (integer spin: SO(3)/adjoint, screenable — 0 fermion modes)
V(t) → 1   for t odd    (half-integer spin: one genuine spinor, D = ±1 minimal vortex)
leading corrections:  V(even t) = c_t·w² + …   (c_2=6, c_4=64/9, c_6=15/2, …),  V(odd t) = 1 + O(w⁴).
```

So as `w→0`, `V = [0,1,0,1,…]` — **exactly the fermion-number `(−1)^F` oscillation.** Its second
difference alternates `∓2`:

```
Δ²V(t even) → −2   (saturates R1!)      Δ²V(t odd) → +2.
```

The `+t²` that turns R1 into convexity of `V+t²` is precisely `Δ²(t²) = +2 = D_max²` — the geometric
maximum flux. Thus **R1 saturates at `(t even, w→0)` with margin `Δ²(V+t²) = c_{t+2} w² + O(w⁴) → 0⁺`**
(e.g. `t=0`: `Δ²(V+t²) = 6w² → 0⁺`). This is the project's "corner-tight `Δ²⟨D²⟩ ≥ −2`."

The reframing is exact: the `−2` floor is nothing but the pure fermion-number oscillation, and R1 =
"the `(−1)^F` alternation of the flux variance, plus `D_max²`, is convex in fermion number."
The parity coupling the combinatorial attacks kept hitting **is** `(−1)^F` / the R↔NS sector flip.

---

## 4. The crux: does free-fermion positivity make Δ²(V+t²) manifest?

Two distinct answers, depending on what you fix.

**(a) Fixed t — YES, manifestly SOS (constructive, Lean-able).**
Each `Δ²(V(t)+t²)` is a single rational function of `w`; its numerator is a univariate polynomial in
`u = w²` that is **nonnegative on `u ≥ 0`** (verified `t=0..4`, degrees up to 38, `spinor_corner.py`;
even-`t` numerators touch 0 at `w=0`, odd-`t` strictly positive). A univariate polynomial nonnegative
on `[0,∞)` always admits a finite **`σ₀(u) + u·σ₁(u)` sum-of-squares certificate**
(Pólya–Positivstellensatz) — directly `nlinarith`/`polyrith`-formalizable in Lean, per fixed `t`. The
leading term is literally a square: `Δ²(V(0)+t²) = 6w² = (√6 w)²`.

**(b) Uniform in t — NO, not from fixed-number Wick.** R1 is `∀t`. The fermion positivity of §2 is a
statement **at fixed particle number N**. R1 is `Δ²_N` **across** `N = t, t+1, t+2` — three different
fermion-number sectors, i.e. an even/odd (R/NS) comparison where the *number of fermion modes changes
by one*. Two concrete obstructions:

  - The transverse susceptibility `V = Var(D | N)` is **not** the curvature of the free energy.
    We checked `V(t)` vs `−Δ²_N log Z_N` (`Z_N = Σ g(n)g(N−n)`, itself manifestly log-concave —
    convolution of the log-concave `g`): the ratio drifts with both `N` and `w`
    (`0.14 → 1.9 → 17 → 190`), so `V ≠ const·(−Δ²log Z)`. Log-concavity of `Z_N` is the *longitudinal*
    (particle-number) fluctuation and is manifestly fermionic; R1 is the *transverse* (flux-`D`) one and
    is a genuinely different object.
  - Between `N` and `N+1` the occupation set `{pₖ^{(N)}}` reshuffles (one mode added). There is no
    Wick/Pfaffian identity relating `Σ pₖ^{(N)}(1−pₖ^{(N)})` across `N` — that is exactly the theta /
    `LineSumLogConcaveCR` cross-sector statement the project already isolated as Core B.

So refermionization **reproduces** the known reduction rather than removing it: it identifies the
irreducible residual as *the `(−1)^F`-graded, cross-fermion-number second difference of the flux
variance*, and confirms it is not a free (Wick) quantity.

---

## 5. Where the free-fermion picture breaks (quantified)

1. **Independent-Bernoulli form breaks at `w > w* ≈ 0.82`** (roots leave the real axis). *Harmless*:
   R1 is loose (margin ≈1.8) there.
2. **The true break is `(−1)^F` cross-sector coupling.** R1 couples `N` and `N±1`; fixed-`N` freeness
   cannot see it. Quantitatively, the residual after the leading Gaussian term is the sign of the
   *second difference in `N`* of the `O(w²)` (and higher) theta corrections `c_N w² + …` — precisely
   the theta log-concavity / abstruse-identity content, not a Wick contraction.
3. **The mass envelope `(M²−D²)` is a genuine interaction**, not part of this free two-fermion problem
   (the free object here is just the fusion measure `μ_t`); it would be a quartic (four-fermion) vertex
   on top and does not appear in R1 itself.

---

## 6. Verdict and formalization assessment

- **"These are just spinors" is TRUE and useful, with a precise domain.** `μ_t` is exactly two free
  fermions at fixed total number; `V(t) = 4Σ pₖ(1−pₖ)` (independent Bernoulli occupations) for the
  whole strong-coupling danger zone `w ≲ 0.82`; the even/odd wall is literally `(−1)^F` (R↔NS); the
  `−2` floor is the pure fermion-number oscillation and the `+t²` rescue is `D_max²`.
- **The wall does NOT fully dissolve.** The manifest free-fermion positivity is *within a
  fermion-number sector*; R1 is a *cross-sector* second difference. The smallest irreducible residual
  is: **`Σₖ pₖ(1−pₖ)` (flux-variance) is `(N−2)²`-convex across fermion-number sectors `N`** — i.e. the
  theta / `LineSumLogConcaveCR` cross-sector log-concavity, which refermionization *explains* but does
  not *prove*.
- **Formalization payoff, concrete:** every *fixed* `t` is a finite univariate `σ₀ + u σ₁` SOS
  certificate (`nlinarith`-able); the leading corner is the literal square `6w²`. If the project can
  supply a *`t`-uniform* SOS/Pfaffian bound for the cross-sector difference — the natural candidate is
  a Gram/Pfaffian built from the `(A−B)²` fermion-determinant of §1 — R1 closes constructively.
  That uniform Pfaffian is the honest remaining target; this analysis did not produce it.

**Bottom line:** clean "it's a free fermion" for the physics and the tight regime (with the exact
`V = Σ f(1−f)` and the `(−1)^F` mechanism), and an honest "it's NOT free where it hurts" for the
proof: R1's residual is the cross-fermion-number (`(−1)^F`) second difference, which is not a
fixed-sector Wick identity and coincides with the already-known theta log-concavity wall.
