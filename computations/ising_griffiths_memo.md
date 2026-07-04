# Ising / free-fermion reframing of the R1 residual `Δ²V(t) ≥ −2`

**Question tested.** The open residual R1 asks: for `V(t)=⟨D²⟩`, the variance of `D=t−2p`
under the fusion measure `μ_t(p) ∝ coeffW(w,p)·coeffW(w,t−p)`,
`coeffW(w,s)=(s+1)w^{s(s+2)}`, is the cross-parity second difference bounded,
`Δ²V(t) = V(t+2)−2V(t+1)+V(t) ≥ −2`, equivalently `V(t)+t²` convex in `t`.
The hypothesis under test: this is the 2D-Ising / free-Majorana structure (two spin-structure
sectors = the two parities), and the bound is a **standard correlation inequality**
(Griffiths/GKS-II, FKG, or Lebowitz/GHS `u₄≤0`), hence constructive and Lean-friendly.

All numbers below are `mpmath` at 60–80 digits; scripts in `computations/ising_griffiths_verify.py`.

---

## 1. The exact ensemble dictionary (numerically confirmed to 60 digits)

Write `s(s+2)=(s+1)²−1`, `dim = s+1`. With `a=p+1`, `b=(t−p)+1`, `N=t+2`, `q=w`, the
weight factorizes cleanly (constants cancel in `μ_t`):

```
μ_t(p) ∝ coeffW(w,p)coeffW(w,t−p) ∝ a·b·q^{a²+b²},   a+b = N,  a,b ≥ 1,
D = t−2p = a−b,   a²+b² = ½((a+b)² + (a−b)²),   ab = ¼(N²−D²).
```

Three equivalent forms of `V(t)=⟨D²⟩`, each verified `|diff| < 1e-59` against the direct sum
over `w∈{0.3,0.7,0.9,0.99}`, `t≤16`:

1. **Single-variable "confined lattice-Gaussian":**
   `V(t) = ⟨D²⟩` under `π_N(D) ∝ (N²−D²)·q^{D²/2}`, support `|D|≤N−2`, `D≡N (mod 2)`.
2. **Two-particle canonical ensemble:** `a,b` i.i.d. with single-particle law
   `p₁(n) ∝ n·q^{n²}` (`n≥1`), conditioned on `a+b=N`; then `V(t)=4·Var(a | a+b=N)`.
3. **Convexity form (the residual restated):**
   `V(t)+t² = 4⟨a²⟩_N − 4N + 4`  ⟹  `Δ²(V+t²)≥0 ⟺ N↦⟨a²⟩_N convex`.

**Free-fermion / spin-structure content.** The single-particle generating sum
`Σ_{n≥1} n q^{n²}` is a theta-derivative; `Σ_n q^{n²}=ϑ₃` is the free-Majorana (NS) partition
sum. The two parities of `D` are the two spin structures exactly as hypothesized:
`D` even ⇒ `ϑ₃`-lattice (NS / disorder sector), `D` odd ⇒ `ϑ₂`-lattice (R / spin sector).
So the even/odd `V`-chains genuinely are the two `Z₂` / spin-structure sectors of the Ising
free fermion. **This part of the hypothesis is correct.**

---

## 2. The bound holds, and `−2` is SHARP — but it is a Casimir floor, not a bulk fluctuation

Grid scan (log-spaced `w∈[1e-6,1)`, `t≤80`): `min(Δ²V+2) = 1.3e-11 > 0`, attained as
`w→0` at `t=2`. The constant `−2` is **sharp**: `Δ²V(2) → −2` as `w→0`
(`Δ²V(2)+2 ≈ 13.11·w³ → 0`).

The saturating configuration is the **minimal-Casimir fusion channel** (`w→0` = vacuum
dominance): the measure concentrates on the single `p` minimizing the total Casimir
`p(p+2)+(t−p)(t−p+2)`, giving
- even `t`: `D=0` channel ⇒ `V→0`;
- odd  `t`: `D=±1` channel ⇒ `V→1`.

Hence `Δ²V = 0 − 2·1 + 0 = −2`. Because `C₄(s)=s(s+2)` has `Δ²C₄ = 2`, the floor is
**`−2 = −Δ²(Casimir)`** — the identical `Δ²C₄=2` / `d2x≤1` pinning already in the project's
Tier-0 note, now derived as the sharp extremal channel. This means the bound cannot come from
a "fluctuations are positive" argument that would give a slack; it is saturated.

---

## 3. VERDICT on the correlation-inequality routes

### Lebowitz / GHS `u₄ ≤ 0` (the flagged front-runner): **REFUTED for this ensemble.**
The natural 4-point Ursell here is the 4th cumulant of the spin sum `D`,
`κ₄(D)=⟨D⁴⟩−3⟨D²⟩²`. Over a `200×50` `(w,t)` grid, `κ₄` is **positive on 3438/9751 points**
(max `+1.37`); it does **not** have a definite sign. The sign is **parity-locked**:
at moderate `w` (e.g. `w=0.4`) `κ₄ ≈ +1.24` in the even (`ϑ₃`) sector but `κ₄ ≈ −1.33` in the
odd (`ϑ₂`) sector. So `u₄≤0` is simply false, and the "`Δ²(variance)~u₄≤0`" mechanism does not
close the bound. (It becomes uniformly negative only in the strong-Gaussian `w→1` regime.)

### Griffiths / GKS-II and FKG: **inapplicable — the ensemble is not ferromagnetic.**
The interaction in `π_N(D) ∝ (N²−D²)q^{D²/2}` is `q^{D²/2}=exp(−½β D²)` with `β=|ln w|>0`:
a **confining / antiferromagnetic-sign** quadratic (Curie–Weiss with the *wrong* sign, penalizing
large magnetization `D`), not the `e^{+βD²/2}` of a ferromagnet. GKS-II and FKG require
ferromagnetic couplings `J_ij≥0`; that hypothesis is violated, so these inequalities do not
apply and the expected `u₄≤0` sign is (consistently) reversed in the even sector.

### What actually controls the bound: **log-concavity / Brascamp–Lieb (Gaussian domination).**
The genuine structure is one-dimensional **log-concavity**, verified two ways:
- `coeffW` is **strictly PF₂ / log-concave, unconditionally**:
  `coeffW(s)²/(coeffW(s−1)coeffW(s+1)) = (1+1/[s(s+2)])·w^{−2} > 1` (exact, all `w<1`).
- the assembled weight `ρ(D)=(N²−D²)q^{D²/2}` is discretely log-concave in `D`
  (`ρ(D)² ≥ ρ(D−2)ρ(D+2)`, min ratio `1.046` over the grid).

This is the **Brascamp–Lieb / Prékopa / Gaussian-domination** family (variance bounds for
log-concave measures), **not** the Ising ferromagnetic-correlation family. It is exactly the
project's existing `LineSumLogConcave` / `coeffW_rect` PF₂ core.

**Bottom line.** The Ising = free-Majorana reframing is *structurally real and correct* (the
two parities are the two spin structures; `V` is a genuine `ϑ`-sector susceptibility), but it
does **not** hand over a shortcut correlation inequality. The specific bound is **not** a
ferromagnetic Griffiths/FKG statement, and the flagged Lebowitz `u₄≤0` route is **refuted**
(parity-dependent kurtosis sign). The reframing instead lands on — and clarifies — the *same*
log-concavity wall the project already has, recasting it as a Brascamp–Lieb / Gaussian-domination
variance-convexity statement, and it pins the sharp constant `−2` to `−Δ²C₄` (the Casimir
second difference), saturated by the vacuum-dominated minimal-Casimir channel.

---

## 4. Constructive / Lean-formalizability assessment

- The refuted routes (Griffiths, FKG, Lebowitz) are moot here.
- The operative route — **log-concavity of `coeffW` (PF₂)** — is *fully constructive and already
  Lean-proved unconditionally*: the ratio identity `(1+1/[s(s+2)])w^{−2}>1` is elementary
  algebra, no probabilistic limit. This is genuinely Lean-friendly (it is `coeffW_rect` /
  `FusionCoreStepRoundC.coeffW_superLogConcave`).
- The **residual gap** is unchanged: single-factor log-concavity of `coeffW` does **not** by
  itself give convexity of the *conditioned second moment* `⟨a²⟩_N` (= the cross-parity
  `Δ²V≥−2`). That step is the Brascamp–Lieb / line-sum-log-concavity statement
  `LineSumLogConcaveCR`, which remains the irreducible core. The Ising reframing does not remove
  it; it reframes it as "the conditional variance of a log-concave i.i.d. pair is convex in the
  sum, up to the `−Δ²C₄` Casimir offset."

**Recommendation.** Do not pursue Griffiths/FKG/Lebowitz for this node — they are inapplicable
(non-ferromagnetic) or false (indefinite `u₄`). Keep the log-concavity / Brascamp–Lieb framing;
the useful new facts extracted are (i) the sharp constant `−2 = −Δ²C₄` with its explicit
`w→0` extremal channel, giving a concrete saturation certificate, and (ii) the reduction
`Δ²V≥−2 ⟺ ⟨a²⟩_N convex in N` for the i.i.d. law `n q^{n²}`, which is a cleaner target for a
Brascamp–Lieb / discrete-log-concave variance-convexity lemma than the raw theta line-sum.
