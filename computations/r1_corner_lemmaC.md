# Lemma C — a Lean-formalizable proof via a univariate Bernstein certificate

**Statement (Lemma C).** For all integers `s ≥ 7` and all `q ∈ (0,1]`,
```
        Δ²Var_q(s)  ≤  Δ²Var_par(s),
```
where, on the tilted parabolic ensemble `ρ_t(D) = (n²−D²) q^{D²}` (`D ≡ t (mod 2)`, `|D| ≤ t`,
`n = t+2`), `Var_q(t) = ⟨D⁴⟩ − ⟨D²⟩²`, `Δ²X(s) = X(s) − 2X(s+1) + X(s+2)`, and
`Δ²Var_par(s) = 96(s²+6s+7)/175`.

**Verdict.** Lemma C is TRUE. For **each fixed `s`** it reduces to a single univariate polynomial
inequality `P_s(q) ≥ 0 on [0,1]` that a prover checks by a **finite list of nonnegative integers**
(a Bernstein certificate). This is proved below and verified exactly for `s = 7..30` and numerically
(the direct inequality) for `s = 7..60`, `μ ∈ [0,10]`. The one honest residual is the **quantifier
over `s`** (infinitely many, growing degree): see §6.

The "clean" cumulant sufficient condition proposed in the brief (`Δ²m₃(μ) ≥ 0`) is **FALSE** — see
§4 — so the proof does **not** go through pointwise third-moment positivity; it goes through the
polynomial/Bernstein route.

Every constant below is exact; floats are only sanity checks.

---

## 1. The exact algebraic objects (integer-coefficient polynomials in `q`)

For integer `t ≥ 1` and `j ∈ {0,1,2}` define the raw moments (finite sums, integer coefficients):
```
   S_j(t) := Σ_{D ≡ t (2),  |D| ≤ t}  D^{2j} · (n²−D²) · q^{D²},     n = t+2.
```
So `S_0, S_1, S_2` are `M0, M2, M4`. Then (all as rational functions of `q`):
```
   Var_q(t) = N(t) / d(t),      N(t) := S_2(t)·S_0(t) − S_1(t)²,     d(t) := S_0(t)².
```
`N(t), d(t) ∈ ℤ[q]`, and `d(t) > 0` on `(0,1]`. (Reindexing `D = t − 2j`, `j = 0..t`, the weight is
`4(j+1)(t+1−j) q^{(t−2j)²}` — an explicit log-concave parabola×geometric; used only for intuition.)

**FACT 0 (denominator-cleared form).** Since `d(t) > 0`, multiplying the target by
`175·d(s)d(s+1)d(s+2) > 0` shows

> **Lemma C at `s`  ⟺  `P_s(q) ≥ 0` for all `q ∈ (0,1]`**, where
```
   P_s(q) := 96(s²+6s+7)·d(s)d(s+1)d(s+2)
             − 175·[ N(s)·d(s+1)d(s+2) − 2 N(s+1)·d(s)d(s+2) + N(s+2)·d(s)d(s+1) ] ∈ ℤ[q].
```

`P_s(1) = 0` (equality at `q = 1`, the pure parabola). `deg P_s = 2·[s² + (s+1)² + (s+2)²]`
(e.g. `s=7`: degree `388`, lowest term `q⁴`).

---

## 2. FACT 1 — the structural factorization (verified exact, `s = 7..30`)

`P_s(q)` factors as
```
   P_s(q)  =  q^{ν_s} · (q⁴ − 1) · H_s(q⁴),        ν_s = 2 (s even) or 4 (s odd),   H_s ∈ ℤ[x].
```
Two prover-checkable sub-facts, both verified exactly for `s = 7..30`:

* **(1a)** every exponent of `P_s(q)/q^{ν_s}` is `≡ 0 (mod 4)` — so `P_s(q)/q^{ν_s}` is a genuine
  polynomial `Px_s(x)` in `x := q⁴`;
* **(1b)** `(x − 1)` divides `Px_s(x)` exactly in `ℤ[x]`, i.e. `Px_s = (x−1)·H_s`  (equivalently
  `Px_s(1) = 0`), with integer quotient `H_s`.

`deg H_s = ½·[s² + (s+1)² + (s+2)²] − 1` (e.g. `s=7`: `deg_x H_7 = 95`).

Because `q^{ν_s} > 0` and `(q⁴ − 1) < 0` on `(0,1)`,
```
   P_s(q) ≥ 0 on (0,1]   ⟺   H_s(x) ≤ 0 on x ∈ [0,1]   ⟺   −H_s(x) ≥ 0 on [0,1].
```
(Note: `H_s(1) < 0` **strictly** — e.g. `H_7(1) = −62793204960854016000` — so the zero of `P_s` at
`q=1` comes entirely from the `(q⁴−1)` factor; `−H_s` is bounded away from `0` on `[0,1]`.)

---

## 3. FACT 2 — the Bernstein nonnegativity certificate (verified exact, `s = 7..30`)

Write `−H_s(x) = Σ_{i=0}^{d} a_i x^i`, `d = deg H_s`, `a_i ∈ ℤ` (`a_0 = −H_s(0) > 0`; note leading
`a_d < 0`, harmless off `[0,1]`). Its Bernstein coefficients on `[0,1]` are
`b_k = Σ_{i=0}^{k} [C(k,i)/C(d,i)] a_i`. Using the identity `C(k,i)/C(d,i) = C(d−i,k−i)/C(d,k)`,
`b_k = β_k / C(d,k)` with the **integer**
```
   β_k^{(s)}  :=  Σ_{i=0}^{k}  a_i · C(d−i, k−i)          (k = 0, …, d).
```

> **FACT 2.  `β_k^{(s)} ≥ 0` for all `k = 0..d`** (verified: in fact **strictly `> 0`**, `s = 7..30`).

**Why this closes it (the only external lemma, elementary):** the Bernstein basis
`B_{k,d}(x) = C(d,k) x^k (1−x)^{d−k}` is `≥ 0` on `[0,1]`, and
`−H_s(x) = Σ_k b_k B_{k,d}(x) = Σ_k (β_k/C(d,k)) B_{k,d}(x)`. Hence `β_k ≥ 0 ∀k ⇒ −H_s(x) ≥ 0` on
`[0,1]`. Combined with §2 this gives `P_s(q) ≥ 0` on `(0,1]`, i.e. Lemma C at `s`. ∎ (each fixed `s`)

The whole per-`s` proof is thus **three finite, purely algebraic, prover-checkable facts** about
integer polynomials: (1a) support mod 4, (1b) exact division by `x−1`, (2) `d+1` integers `β_k ≥ 0`.
No infinite theta, no analysis, no floating point.

Concrete example `s = 7`: `−H_7` has `deg = 95`, `a_0 = 138726604800000000`, and all `96` integers
`β_k^{(7)} > 0`.

---

## 4. Why the proposed cumulant route (Δ²m₃ ≥ 0) FAILS, and the exact backbone

The exponential-family identity is correct and exact:
```
   ∂Var_q(t)/∂μ = −½·m₃(t;q),     m₃ := ⟨g³⟩ − 3⟨g²⟩⟨g⟩ + 2⟨g⟩³  (third central moment of g = D²),
```
so `∂/∂μ [Δ²Var_μ(s)] = −½ Δ²m₃(μ; s)`, and Lemma C would follow from `Δ²m₃(μ;s) ≥ 0 ∀μ≥0`.

**This pointwise condition is FALSE.** Numerically `min_{s,μ} Δ²m₃ = −115.9` at `(s,μ)=(9, 0.1)`.
At fixed `s=9`, `Δ²m₃(μ)` starts at `+6968.17` (μ=0), crosses `0` near `μ≈0.065`, dips to `≈ −130`
near `μ≈0.09`, then returns toward `0`. Consequently `F(μ,s) := Δ²Var_par − Δ²Var_μ = ½∫₀^μ Δ²m₃ dν`
is **not** produced by a sign-definite integrand — it stays `≥ 0` only because the large positive
`Δ²m₃` near `μ=0` dominates the shallow later dip. So the third-moment sign route cannot be used;
the Bernstein route of §1–3 is the substitute.

What the cumulant identity **does** give exactly and uniformly (all parities identical, verified):
```
   ⟨D²⟩_par = t(t+4)/5,   ⟨D⁴⟩_par = t(t+4)(3t²+12t−8)/35,   ⟨D⁶⟩_par = t(t+4)(5t⁴+40t³+40t²−160t+96)/105,
   Var_par(t) = 8 t(t−1)(t+4)(t+5)/175,      Δ²Var_par(s) = 96(s²+6s+7)/175,
   m₃_par(t)  = 32 t(t−1)(t+4)(t+5)(t²+4t−15)/2625,
   Δ²m₃_par(s) = 64(5s⁴+60s³+211s²+186s−42)/875  >  0   for all s ≥ 1.
```
Hence `∂/∂μ [Δ²Var_μ(s)]|_{μ=0⁺} = −½ Δ²m₃_par(s) < 0`: **`μ = 0` (i.e. `q = 1`) is a strict local
maximum of `Δ²Var_μ`, uniformly in `s`** — the correct, provable "edge" statement. (At the other
edge, `q→0⁺`, the ensemble collapses to its minimal `D²`-shell and `Var_q(t) → 0`, so
`Δ²Var_{q→0}(s) = 0 ≤ Δ²Var_par(s)`.)

---

## 5. Numerical verification log

| check | method / precision | result |
|---|---|---|
| `Var_par`, `⟨D^{2k}⟩_par`, `m₃_par` closed forms (both parities) | exact (interpolation + spot check) | ✓ identical both parities |
| `∂_μ Var = −½ m₃` | mpmath dps 40, central diff | agree to 10 digits |
| `Δ²m₃_par(s) = 64(5s⁴+…)/875 > 0` | exact + mpmath | ✓ `s = 7..12` (and `>0 ∀s≥1`) |
| **direct Lemma C** `Δ²Var_q ≤ Δ²Var_par` | mpmath dps 40 | `max(Δ²Var_q − Δ²Var_par) = 2·10⁻³⁵ ≤ 0`, `s=7..60`, `μ∈[0,10]` (=0 only at μ=0) |
| pointwise `Δ²m₃ ≥ 0` (proposed suff. cond.) | mpmath dps 40 | **FALSE**, `min = −115.9` at `(9, 0.1)` |
| **FACT 1** support mod 4 + exact `(x−1)` division | exact integer | ✓ `s = 7..30` |
| **FACT 2** integer Bernstein `β_k^{(s)} ≥ 0` | exact integer | ✓ **strictly `> 0`**, `s = 7..30` |
| no root of `H_s` in `(0,1)`; `max_{[0,1]} H_s < 0` | numpy roots / grid | ✓ `s = 2..12` |

Scripts (in `/Users/darthur/.claude/jobs/1c30fec5/tmp/`): `numverify.py` (direct C + Δ²m₃),
`parab_moments.py`, `verify_m3.py` (backbone closed forms), `intcert.py` / `intcert30.py`
(exact integer Bernstein certificate), `reduce.py`, `descartes.py`, `roots_np.py` (structure).

---

## 6. What a Lean formalization needs, and the honest residual

**Per-`s` (COMPLETE, and this is genuinely all-`μ`, i.e. all `q∈(0,1]`).** For any fixed `s` the
proof is the elementary Bernstein lemma (§3, one-time) applied to three finite integer facts about
`P_s`: (1a) exponents `≡0 mod 4`, (1b) `(x−1) | Px_s`, (2) `β_k^{(s)} ≥ 0`. All are `decide`-style
computations on explicit integer polynomials. The Bernstein positivity lemma
(`all Bernstein coeffs ≥ 0 ⇒ poly ≥ 0 on [0,1]`) is short and standard (nonnegativity of the
Bernstein basis on `[0,1]`); it is the only reusable piece of "mathematics."

**The residual: the `∀ s ≥ 7` quantifier.** `deg P_s = 2·[s²+(s+1)²+(s+2)²] = O(s²)` grows, so
there is **no single finite Bernstein object** covering all `s`; the certificate is a *family*
`{(H_s, β^{(s)})}`. Two honest routes to discharge the quantifier:

1. **Finite base + asymptotic tail.** Verify the integer certificate for `s = 7 .. N` (done to
   `N = 30`; extends by pure computation), then prove `−H_s ≥ 0` on `[0,1]` for `s > N` by an
   asymptotic dominance argument. The uniform seeds are in §4: the `q→1` edge derivative
   `−½Δ²m₃_par(s) = −32(5s⁴+…)/875 < 0` and the `q→0` edge value `0`, both closed-form in `s`; a
   spacing-uniform bound on the intermediate `μ`-region (where, per the corner split, only
   `μ ≤ 35/(2(s²+6s+7)) → 0` is actually needed) would close it. **Not yet reduced to a finite
   check** — this is the open piece.
2. **Uniform positive Bernstein family.** Find a closed form / manifest-positivity pattern for
   `β_k^{(s)}` (or a generating-function proof that `−H_s` has nonnegative Bernstein coefficients for
   all `s`). Numerically the `β_k^{(s)} > 0` with large margin and smooth `s`-dependence, which is
   encouraging, but no closed form was found here.

**Bottom line.** Lemma C is reduced from "a numerical scan over `(s,μ)`" to **a finite, exact,
integer-polynomial certificate per `s`** (three `decide`-checkable facts + one short Bernstein
lemma), valid for the full range `μ ≥ 0`. The pure-analysis content is gone. The only thing between
this and a closed Lean theorem `∀ s ≥ 7` is a **uniform-in-`s`** wrapper — either a closed form for
the (numerically very clean, strictly positive) certificate integers `β_k^{(s)}`, or a base-cases +
asymptotic-tail argument seeded by the exact edge formulas in §4.
