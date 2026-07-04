# Convexity of the conditional second moment `N ↦ E[X²|X+Y=N]` (residual R1)

**Statement.** `g(k)=k·w^{k²}` (`k≥1`, `w∈(0,1)` fixed), `X,Y` iid `∝ g`. With
`P_N=Σ_j g(j)g(N−j)`, `R_N=Σ_j j²g(j)g(N−j)`, `m(N)=R_N/P_N=E[X²|X+Y=N]`, prove
`Δ²m(N):=m(N−1)−2m(N)+m(N+1) ≥ 0` for integer `N≥2`.

**Bottom line.** The theorem is **NEW** (Efron-type results in the literature give only *first-order*
monotonicity; a general *convexity* statement is provably **FALSE**). I establish two rigorous new
structural facts — (i) a hard impossibility that pins down exactly what any proof must use, and (ii)
a clean exact reformulation (a "tilted / theta-center-shifted partition function" whose
log-concavity in `N`, evaluated as a field-curvature, *is* the residual) that reduces R1 to a single
sharp scalar inequality `G_N''(0) ≥ −2` and explains why the extremal constant is exactly `−2`. The
uniform-in-`N` inequality itself is **not fully closed**; the smallest rigorous gap is stated
precisely and coincides with the project's independently-found sharp envelope. Numerics (mpmath,
dps 40–50) back every claim.

---

## 0. Dictionary to the R1 residual (exact)

`g(k)g(N−k)=k(N−k)w^{k²+(N−k)²}∝ (N²−D²)w^{D²/2}`, `D=2k−N`. So the conditional law of `X` is, in the
flux variable `D`, `π_N(D)∝(N²−D²)w^{D²/2}` (support `|D|≤N−2`, `D≡N (mod 2)`). Writing
`V(N):=⟨D²⟩_{π_N}=4Var(X|N)` and `t=N−2`:

- `E[X²|N]=N²/4+Var(X|N)=(N²+V)/4`, so `Δ²m=½+¼Δ²V`.
- **`Δ²m≥0 ⟺ Δ²V≥−2 ⟺ F(N):=N²+V(N)=4E[X²|N]` is (discretely) convex.** This is exactly R1
  (`Δ²V(t)≥−2`), verified symbolically against the project's `coeffW` three-body form.

Numerics (mpmath, dps 40): `min_N Δ²m` = `1.50e−4 (w=.01)`, `.0148 (.1)`, `.273 (.5)`, `.453 (.9)`;
strictly positive, tight as `w→0` at small `N` of the parity `N≡1(2)` (i.e. even `t`). Confirmed for
every rapidly-decaying weight tested (theta `w^{k²}`, Poisson `1/k!`→bulk value `½`, geometric
`x^k`→bulk value `⅔`).

---

## 1. KNOWN vs NEW — the theorem is new, and a general form is false

**Literature gives only first order.** Efron (1965, *Increasing properties of Pólya frequency
functions*, Ann. Math. Statist.) proves: for `X,Y` iid with a **log-concave (PF₂)** law and `Φ`
monotone, `N↦E[Φ(X)|X+Y=N]` is **monotone**. All descendants stay first-order:
Saumard–Wellner (2014, *Log-concavity and strong log-concavity: a review*, Statist. Surv. 8) §on
Efron; the Efron-monotonicity failure/asymptotics for heavy tails (Denuit–Robert 2021, *Efron's
asymptotic monotonicity property in the Gaussian stable domain*, J. Multivariate Anal. 186; ASTIN
2023, *Conditional expectations given the sum … regularly varying densities*). **No convexity
("second-order Efron") result exists** in this line, and — see §2 — a general one cannot: convexity
is *false* for general PF laws. So R1's convexity is a genuinely new inequality specific to
strongly-log-concave / theta weights.

`Φ=X²` is nondecreasing on the support `k≥1`, so Efron already gives `m(N)` **nondecreasing**
(numerically confirmed). The open content of R1 is strictly the *second-order* refinement.

**A clean rigorous proof of Efron's first-order step (PF₂ ⇒ monotone), for the record.** Clearing,
`R_{N+1}P_N−R_NP_{N+1}=½Σ_{a,b}(a²−b²)g(a)g(b)·B(a,b)`,
`B(a,b)=g(N+1−a)g(N−b)−g(N−a)g(N+1−b)=g(N−a)g(N−b)[φ(N−a)−φ(N−b)]`, `φ(k):=g(k+1)/g(k)`.
Log-concavity ⇔ `φ` nonincreasing, so for `a<b`: `φ(N−a)≤φ(N−b)⇒B≤0`, and `(a²−b²)<0`, so every term
`≥0`. Hence `m` nondecreasing. Uses **only PF₂**; it is a sum of 2×2 minors (discrete Wronskians) of
the Toeplitz matrix `[g(·)]` with a sign-matched Vandermonde coefficient — fully Lean-friendly.

---

## 2. Impossibility: no pure total-positivity / SOS certificate can prove convexity

The natural second-order generalization of §1 would express the cleared second difference `S_N` as a
sign-matched sum of **3×3** minors of `[g(·)]`, provable from `g` being PF₃. **This cannot work**,
by a decisive counterexample:

> **Uniform on `{0,…,n}`** (`g≡1` on the support) is **PF of every order** (its Toeplitz matrix is
> totally positive), yet `Δ²E[X²|X+Y=N]` is **negative**: `= −4/3` at `N=n=5`, `−3` at `n=10`,
> `−19/3` at `n=20` (exact; mpmath-verified). The failure is a *hard-support-boundary* kink: for
> `N≤n` the conditional law is uniform on `{0,…,N}` giving `m(N)=N(2N+1)/6` (convex, `Δ²=⅔`); the
> clipping at `N>n` breaks convexity at the edge.

Consequence, sharp: **any certificate that uses only the PF/TP (total-positivity) property of `g`
would also apply to the uniform law and hence prove a false statement.** Therefore **every valid
proof of R1 must quantitatively use the tail decay of `g`** (equivalently, must exploit that `g` has
*no hard support boundary*). This rules out, as stated, the "3×3 minor-sum" (strategy 1), the pure
"MLR/coupling" (strategy 3), and any `w`-uniform SOS that ignores the tail. It is fully consistent
with the project's independent findings (Lebowitz `u₄≤0` refuted; FKG/Griffiths inapplicable; the
`w→0` corner is the extremiser). This is the single most useful orientation fact: **R1 is not a
total-positivity theorem; it is a strong-log-concavity/tail theorem.** The relevant strength of `g`
is `−Δ²log g(k)=−log(1−1/k²)+2|log w| ≥ 2|log w|>0` (uniform strong log-concavity), which the flat
uniform law lacks.

---

## 3. New exact reformulation: field-tilted partition function (the `−2` explained)

Introduce a field `h` conjugate to the flux `D=2a−N`:
```
Z_N(h) := Σ_{a} g(a)g(N−a) e^{h(2a−N)} = e^{−hN}·(g_h ∗ g)(N),   g_h(a):=g(a)e^{2ha}.
```
Two elementary, **rigorous** facts:

**(R1) `Z_N(h)` is log-concave in `N` for every real `h`.** `g` is PF (Jacobi triple product ⇒
Laguerre–Pólya ⇒ PF; closed under `z d/dz`). Geometric tilt preserves PF (`[g_h(i−j)]=Δ[g(i−j)]Δ⁻¹`,
`Δ=diag(e^{2hi})`, same minors up to positive factors), so `g_h` is PF; convolution of PF sequences
is PF (Karlin), so `g_h∗g` is PF, in particular log-concave in `N`; the factor `e^{−hN}` is
log-linear and does not affect `Δ_N²log`. Hence
```
G_N(h) := Δ_N² log Z_N(h) = log( Z_{N−1}(h)Z_{N+1}(h) / Z_N(h)² ) ≤ 0    ∀h∈ℝ.
```
**(R2) `Z_N(h)` is even in `h`** (substitute `a↦N−a`), and
`∂_h log Z_N(0)=⟨2a−N⟩=0`, `∂_h² log Z_N(0)=Var(2a−N)=V(N)`. Therefore, differentiating (R1) twice
in `h` at `h=0`,
```
Δ_N² V(N) = ∂_h² G_N(h)|_{h=0} = G_N''(0).
```
Both verified numerically to 8 digits (`G_N` exactly even; `G_N''(0)=Δ²V` to 1e−8).

**So R1 ⟺ `G_N''(0) ≥ −2`, where `G_N(h)≤0` is even.** The field is geometrically a **shift of the
theta center**: `g_h(a)=a·w^{(a−a₀)²}·const` with `a₀=h/|log w|`, so `G_N(h)` is the
log-concavity-defect of a convolution of two theta sequences as a function of the *relative shift* of
their centers.

**Why the sharp constant is exactly `−2`.** Split `F=N²+V`. The mean part is *rigid*: by the
`a↔N−a` symmetry, `⟨2a⟩=N` **exactly for every `N`** (mpmath: `9.000000000`), so `(mean)²=N²` with
**zero slack**, contributing `Δ²(N²)=+2`. All flexibility is in the variance `V=G-curvature`. Hence
the floor `Δ²V≥−2` is precisely "the variance concavity cannot exceed the rigid `+2` of the pinned
mean," and it is saturated (`Δ²V→−2`) in the vacuum-dominated corner `w→0`, even `t`. This is the
same `−2=−Δ²(Casimir)` the project found, now derived from the exact `⟨2a⟩=N` identity.

**Asymptotics of the reduced object.** `G_N(0)=log(P_{N−1}P_{N+1}/P_N²)` (pair-log-concavity gap);
`G_N(±∞)=log(g(N−2)g(N)/g(N−1)²)=2log w+log[N(N−2)/(N−1)²]` (single-particle gap; exponent
identity `(N−2)²+N²−2(N−1)²=2`). So `G_N` is an even, nonpositive profile interpolating a
pair-gap at the center and a single-particle-gap plateau at `|h|→∞`; `R1` is the assertion that the
curvature of this profile at its center is `≥−2`.

---

## 4. What remains open, and the smallest rigorous gap

`G_N''(0)≥−2` does **not** follow from `G_N≤0` + evenness alone (an even nonpositive function can
have an arbitrarily sharp central spike). The missing ingredient is exactly the §2 tail control: a
lower bound on the *width/shape* of the central bump of `G_N(h)`, or equivalently a bound on how fast
the tilted log-concavity ratio can dip. This is the honest irreducible residual and it matches, term
for term, the two equivalent walls the project's direct route already isolated:

- **(A) sharp minorant** `Δ²V(N)+2 ≥ (144/25)·w²(1−w²)` for all `N` (extremiser `(t=0,w²=1/6)`,
  constant `144/25=5.76` exact), or
- **(B) monotone ratio** `g_s:=inf_w (Δ²V+2)/(w²(1−w²))` nondecreasing in `s` (`g_0=144/25`,
  `g_1=48/7`, … ↗ 8), base cases exact rationals.

Both are strictly sharper than R1 with a known extremiser at *small* `N` — consistent with §2 (the
tight case is finite, discrete, number-theoretic, not the continuum `s→∞` face `G_odd−G_even≤1`,
which is `8>144/25` and hence *not* the extremiser). A complete proof therefore factors as
**[finitely many exact-rational small-`N` base cases] + [one uniform monotonicity / large-`N` theta
bound]**; the latter is the continuum/theta face handled by the parallel elliptic-modulus route,
the former are decidable in ℚ.

The §3 reformulation contributes a concrete new attack surface for the uniform step: prove that the
even profile `G_N(h)` satisfies `G_N(h)−G_N(0) ≥ −h²+o(h²)` uniformly — a *width* lower bound on the
central bump — which is a statement purely about log-concavity of a two-theta convolution under
center-shift, and is where the strong-log-concavity of `w^{k²}` (§2) enters. I did **not** close this
uniform bound; it is the same wall, now expressed as a single scalar curvature inequality with an
explicit meaning.

---

## 5. Cleanest sufficient hypothesis / key lemma

- `g` is **PF** (Jacobi triple product ⇒ LP ⇒ PF); this yields §1 (monotonicity) and §3-(R1)
  (log-concavity of the tilted `Z`) rigorously. But **PF is not sufficient** for the convexity
  (§2, uniform counterexample).
- The correct sufficient strength is **uniform strong log-concavity with a hard-boundary-free tail**:
  `−Δ²log g(k) ≥ 2|log w| > 0`, which `w^{k²}` has and the uniform law does not. The operative
  key lemma is the **§3 reduction** `Δ²V=G_N''(0)`, `G_N≤0` even, plus a *quantitative* central-bump
  width bound (the still-open piece), NOT a total-positivity minor identity.

## 6. Constructive / Lean-formalizability assessment

- §1 (Efron monotonicity) and §3 (R1)–(R2): **constructive, finite, Lean-friendly.** (R1) is
  "convolution of PF is PF ⇒ log-concave"; (R2) is the `a↔N−a` symmetry. The reduction
  `Δ²V=G_N''(0)` is an exact identity.
- §2 impossibility: a *finite exact* computation (uniform gives `−4/3` at `n=5`) — trivially
  formalizable, and valuable as it **prevents wasting effort** on a nonexistent SOS/minor certificate.
- The **uniform-in-`N` closing step is NOT a finite minor-sum / single SOS** (that is impossible by
  §2). The realistic formalization is: **finitely many exact-ℚ base cases** (each an
  `nlinarith`/`polyrith` `σ₀(w²)+w²σ₁(w²)` certificate — every fixed `N` slice is such an SOS, per
  the project's `spinor_corner` finding) **+ one analytic monotonicity lemma** (the theta/large-`N`
  face). There is no shortcut around the tail analysis.

## 7. Numerical ledger (mpmath, dps 40–50)

- `Δ²m>0` across `w∈{.01,.1,.5,.9}`, `N≤120`; min `1.5e−4` at `(w=.01,N=3)`; tight corner `w→0`.
- Uniform `{0,…,n}`: `Δ²m=−4/3 (n=5), −3 (n=10), −19/3 (n=20)` — convexity **fails** (PF∞).
- Poisson `1/k!`→ bulk `½`; geometric `x^k`→ bulk `⅔` (conditional-uniform, exact `Δ²=⅔`); theta →
  positive throughout — only hard-cutoff uniform fails.
- `G_N(h)≤0` on grid `N≤24`, `|h|≤3` (max `−0.51<0`); `G_N` exactly even; `G_N''(0)=Δ²V` to 1e−8.
- `⟨2a⟩=N` exactly (`9.000000000`), pinning the rigid `+2` and the sharp floor `−2`.
- `Δ²V→+2` (loose parity, even `N`) and `→−2` (tight parity, odd `N`) as `w→0`, confirming the
  `(−1)^F`/Casimir saturation.

**Sources.** Efron 1965 Ann. Math. Statist.; Saumard–Wellner 2014 Statist. Surv. 8 (Efron review);
Denuit–Robert 2021 J. Multivariate Anal. 186; ASTIN Bull. 2023 (regularly-varying conditional
expectations). Total positivity / PF-convolution semigroup: Karlin, *Total Positivity* (1968).
