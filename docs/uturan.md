# The w-FREE coupling Turán `(‡)` — a UNIFORM-IN-s proof

**Date:** 2026-07-06 · **Job:** 1c30fec5 · Working tree MAIN, no worktree.
**Status headline:** the sole open residual of the SU(2) fusion log-concavity core —
Round M's w-free coupling Turán `(‡)` — is proved **UNIFORM IN s, for all `Q ≥ 4`**, by a
**fully elementary, fully rational** argument (term-keeping lower bound + geometric-tail upper
bound + exact antidiagonal exponent identities). No saddle/theta transcendence is needed. The
Round-M verdict that this residual is "a genuine heat-kernel local-CLT (saddle-WIDTH) statement,
NOT a finite rational inequality, not recoverable by dominant-term/geometric-tail bounds" is
**REFUTED**: it IS so recoverable, once `w` is gone and the numerator's square is used.

Numerics below are `mpmath` dps 50–60 and exact `sympy`.

---

## 0. The exact target (extracted from `FusionCoreStepRoundM.lean`)

Round M reduced the whole fusion box node to the truncated-block reserve `(†)` and, via the exact
Gaussian factorization `coeffW_antidiag_gaussian`
(`c_a·c_b·w^{2ab} ≃ (dimQ a·dimQ b)·w^{c4(a+b)}`, `c4 S = S(S+2)`), stripped the common Gaussian to
leave the **w-free coupling Turán**

> **(‡)**   `U(s+3)² ≥ (256/(225·Q))·U(s+2)·U(s+4)` for all `s ≥ 0`, where `Q = 1/w² ≥ 4` and
>
> **`U(m) := Σ_{i+j=m, i,j≥1} i·j·Q^{ij} = Σ_{i=1}^{m-1} i(m−i) Q^{i(m−i)}`.**

Equivalently (clearing the denominator, `Q>0`):

> **(‡′)**   `225·Q·U(s+3)² ≥ 256·U(s+2)·U(s+4)`.

`256/225 = (16/15)²`. The physical fusion core is at `w = wH = 1/2`, i.e. `Q = 4`, at which `(‡)`
is a pure **integer** inequality; but the proof below is uniform for **all `Q ≥ 4`** (all `w ≤ 1/2`),
covering the general-`w` structures `SymMinorGershgorin (w)` / `FiniteSMargin (w)`.

---

## 1. The structural anatomy of `U(m)`

Let `M(m) := ⌊m²/4⌋ = max_i i(m−i)` (the peak product on the antidiagonal). Write the terms by
distance from the centre.

**Even `m = 2n`** (`M = n²`): `i = n±t`, product `= n²−t²`, exponent `n²−t²`, `t = 0..n−1`:
```
U(2n) = n²Q^{n²} + 2 Σ_{t=1}^{n−1} (n²−t²) Q^{n²−t²}
      = M·Q^M · [ 1 + 2 Σ_{t=1}^{n−1} (1 − t²/n²) Q^{−t²} ]  =:  M·Q^M · ψ_E(m).
```
`ψ_E(m) ↗ θ_E(Q) := Σ_{t∈ℤ} Q^{−t²} = 1 + 2Σ_{t≥1}Q^{−t²}` (Jacobi ϑ₃), monotonically in `n`
(each coefficient `1−t²/n²` increases and new positive terms appear).

**Odd `m = 2n+1`** (`M = n(n+1) = (m²−1)/4`, two central terms): `i = (m±1)/2 ± t`, product
`= M − t(t+1)`, exponent `M − t(t+1)`, `t = 0..n−1`, each doubled:
```
U(2n+1) = 2 Σ_{t=0}^{n−1} (M − t(t+1)) Q^{M−t(t+1)}
        = M·Q^M · [ 2 Σ_{t=0}^{n−1} (1 − t(t+1)/M) Q^{−t(t+1)} ]  =:  M·Q^M · ψ_O(m).
```
`ψ_O(m) ↗ θ_O(Q) := 2 Σ_{t≥0} Q^{−t(t+1)} = 2(1 + Q^{−2} + Q^{−6} + …)`, monotone in `n`.

**Numeric limits (dps 60).** `Q=4`: `θ_E = 1.5078201…`, `θ_O = 2.1254884…`, `θ_O/θ_E = 1.40964`.
As `Q→∞`, `θ_E→1`, `θ_O→2`, `θ_O/θ_E→2`. Monotonicity of `ψ_E, ψ_O` in `n` verified for
`n = 1..19` (strictly UP), and is structural (term-by-term).

**Key observation the earlier rounds missed:** `θ_O ≈ 2` is *dominated by its leading (doubled
central) term* `= 2`. So an **odd-index** `U` is captured to `≈94%` by its two central terms alone
— **no saddle-width is lost** in a central-term lower bound of an odd index. Symmetrically `θ_E`'s
leading two shells (`1 + (3/2)/Q ≈ 1.375` at `Q=4`, i.e. `91%` of `θ_E`) capture the even index
cheaply. The `w`-free `×1.75` slack absorbs the remaining `~6–9%`. This is exactly the content the
Round-M "dominant-term fails" analysis dropped: it lower-bounded the numerator by a *single* central
term (losing the doubling `2`), which is why it fell short.

---

## 2. The four elementary envelope bounds (all TRUE, verified `s=0..79`, `Q∈{4,…,64}`)

Because the NUMERATOR of `(‡)` is `U(s+3)²` (a square) and the exponent second-difference is exactly
`±1/0` (Gaussian gap already paid by `Q`), the theta factors **cancel**; we only need a crude
capture. Two lower bounds (numerator) and two upper bounds (denominators):

**(L)  Term-keeping LOWER bounds on the numerator `U(s+3)`:**
- If `s` is **even** (`s+3` odd, `M₃ = (s+2)(s+4)/4`): keep the **two central terms** →
  `U(s+3) ≥ 2·M₃·Q^{M₃}`.  (`ψ_O(s+3) ≥ 2`.)
- If `s` is **odd** (`s+3` even, `M₃ = (s+3)²/4`, `n = (s+3)/2 ≥ 2`): keep **central + first pair** →
  `U(s+3) ≥ (1 + (3/2)/Q)·M₃·Q^{M₃}`.  (`ψ_E(s+3) ≥ 1 + 2(1−1/n²)/Q ≥ 1 + (3/2)/Q` since `n≥2`.)

**(U)  Geometric-tail UPPER bounds on the denominators:**  Using `i(m−i) ≤ M(m)` per term and
`Q^{−t²} ≤ Q^{−t}`, `Q^{−t(t+1)} ≤ Q^{−2t}` for `t ≥ 1`, and the finite geometric sum
`Σ_{t≥1}Q^{−kt} ≤ Q^{−k}/(1−Q^{−k})`:
- **Even** index `m`: `U(m) ≤ M(m)·Q^{M(m)}·(1 + 2/(Q−1))`.   (`ψ_E ≤ θ_E ≤ 1 + 2/(Q−1)`.)
- **Odd** index `m`:  `U(m) ≤ M(m)·Q^{M(m)}·(2Q²/(Q²−1))`.    (`ψ_O ≤ θ_O ≤ 2/(1−Q^{−2})`.)

All four validated against exact `U` for `s = 0..79`, `Q ∈ {4, 4.5, 5, 8, 16, 64}` (bounds hold and
clear the target, `u7.py`).

---

## 3. The exact antidiagonal exponent identities (pure `Nat`)

With `M(m) = ⌊m²/4⌋`:

**Even `s`:** `M(s+3) = (s+2)(s+4)/4`, `M(s+2) = (s+2)²/4`, `M(s+4) = (s+4)²/4`, and
- `M(s+3)² = M(s+2)·M(s+4)`   (exactly, since `(s+2)(s+4)/4` squared `= (s+2)²(s+4)²/16`),
- `2·M(s+3) + 1 = M(s+2) + M(s+4)`   (`(s+4−(s+2))² = 4`).

**Odd `s`:** `M(s+3) = (s+3)²/4`, `M(s+2) = (s+1)(s+3)/4`, `M(s+4) = (s+3)(s+5)/4`, and
- `2·M(s+3) = M(s+2) + M(s+4)`   (exponent gap `0`),
- `M(s+3)² ≥ M(s+2)·M(s+4)`   (ratio `(s+3)²/((s+1)(s+5)) = 1 + 4/((s+1)(s+5)) ≥ 1`).

---

## 4. The reduction — `(‡′)` collapses to two rational Q-inequalities (no `s` left)

**Even `s`.** Substitute (L)+(U); write `e₂=M(s+2), e₃=M(s+3), e₄=M(s+4)`, `T = 1+2/(Q−1)`.
```
LHS = 225·Q·U(s+3)²  ≥  225·Q·(2 e₃ Q^{e₃})²      = 900·e₃²·Q^{2e₃+1} = 900·e₃²·Q^{e₂+e₄}
RHS = 256·U(s+2)U(s+4) ≤ 256·(e₂Q^{e₂}T)(e₄Q^{e₄}T) = 256·e₂e₄·T²·Q^{e₂+e₄}.
```
`Q^{e₂+e₄}` cancels; `e₃² = e₂e₄` cancels the polynomial part. **Remaining:**
`900 ≥ 256·T²  ⟺  T ≤ 15/8  ⟺  1+2/(Q−1) ≤ 15/8  ⟺  Q ≥ 23/7 ≈ 3.286.`  **True for `Q ≥ 4`.**
(At `Q=4`: `T=5/3`, `256·T² = 6400/9 ≈ 711.1 ≤ 900`; margin `900/711 = 1.266`.)

**Odd `s`.** With `L = 1+3/(2Q)`, `T_O = 2Q²/(Q²−1)`, and `2e₃ = e₂+e₄`, `e₃² ≥ e₂e₄`:
```
LHS = 225·Q·U(s+3)²  ≥  225·L²·e₃²·Q^{2e₃+1}
RHS = 256·U(s+2)U(s+4) ≤ 256·e₂e₄·T_O²·Q^{e₂+e₄} = 256·e₂e₄·T_O²·Q^{2e₃}.
```
`Q^{2e₃}` cancels, one `Q` survives on the left; `e₃² ≥ e₂e₄` drops the polynomial in our favour.
**Remaining:**  `225·L²·Q ≥ 256·T_O²`, i.e.
```
225·(1 + 3/(2Q))²·Q  ≥  256·(2Q²/(Q²−1))².
```
Clearing denominators, this is `P(Q) ≥ 0` with
```
P(Q) = 900Q⁶ − 1396Q⁵ + 225Q⁴ − 5400Q³ − 3150Q² + 2700Q + 2025.
```
Its only real roots are `≈ 0.7413` and `≈ 2.5194` (`sympy nroots`), both `< 4`; leading coeff `> 0`,
so `P(Q) > 0` for all `Q ≥ 4`. **Machine-checkable certificate:** the shift `Q = 4 + x` gives
```
P(4+x) = 900x⁶ + 20204x⁵ + 188305x⁴ + 926840x³ + 2516210x² + 3518620x + 1931321,
```
**all coefficients strictly positive** ⟹ `P(Q) > 0` for all `Q ≥ 4` (i.e. `x ≥ 0`). (At `Q=4`:
`P(4) = 1931321 > 0`; margin of the odd inequality `≈ 1.46`.)

**Both parities close for `Q ≥ 4` with worst case `Q = 4`.** No `s`-dependence survives the
reduction — this is a genuinely uniform-in-`s` proof, not a finite-`s` decide.

---

## 5. Why this beats the Round-M "transcendental" verdict

Round M argued the residual is an irreducible saddle-WIDTH (local-CLT) statement because:
(a) `U` is not log-concave (`U(m+1)²/(U(m)U(m+2)) ≈ 0.5 < 1`); (b) dominant-term/geometric-tail
"loses the saddle-width `θ(Q)²` and fails". Both are about the *sharp* ratio `→ 1/√Q`.

The point: **`(‡)` does not ask for the sharp ratio.** It asks for `≥ 256/(225Q) = 0.284·(1/Q)·Q`
= a `×1.75`-relaxed target. The `θ²` factor that "dominant-term loses" appears **identically** in
numerator (`U(s+3)²`, giving `θ²`) and denominator (`U(s+2)U(s+4)`, giving `θ·θ`); with `w` gone
they are the *same* `Q`-theta and **cancel**. What remains is the leading-shell capture ratio, and
the leading shell of an odd theta is the doubled central term `= 2` — captured exactly by keeping two
terms. So the "saddle width" is never actually needed; the crude bound suffices **because the slack
is `×1.75` and the numerator is squared.** The earlier failure was a *single*-central-term lower
bound (dropping the factor `2`), not the strongest crude bound.

---

## 6. Honest status — Lean vs paper

**Paper (this document): `(‡)` is PROVED uniform in `s`, all `Q ≥ 4`.** Airtight; all sub-facts are
elementary and independently verified (dps 50–60 + exact sympy). This mathematically discharges the
sole open residual `(†)` of the SU(2) fusion log-concavity core.

**Lean file `FusionUTuranWFree.lean` (this session):** proves, axiom-clean (`propext`/`Quot.sound`
only; `decide` facts axiom-free), the **decidable/algebraic HEART**:
- the `Nat` antidiagonal exponent identities (§3),
- the two rational `Q`-closures (§4): the even scalar `T ≤ 15/8 ⟸ Q ≥ 23/7`, and the odd
  polynomial `P(Q) ≥ 0` via the all-nonneg-coefficient shift `P(4+x)` (both as `Q'`/`decide`
  at `Q=4`, and the even closure for general `Q ≥ 4`),
- the **reduction interface** `UTuranEnvelope Q`: a structure carrying the four §2 envelope bounds
  as hypotheses, and `uturan_of_envelope` deriving `(‡′)` for all `s` from it,
- the clean `w`-free definition `Ucoup Q m` and its nonnegativity.

The four §2 envelope bounds (elementary term-keeping / finite-geometric) are carried as the interface
fields — each has a complete paper proof above; formalizing the finite-geometric tail sum over `Q'`
and the acN↔`Ucoup` reindexing (Round-M's factorization supplies the per-term identity) is the
**only remaining formalization work**, and it is *bookkeeping, not mathematics*.

**⚠️ COORDINATOR FLAG (honesty rule ii).** This result, if the four envelope bounds + acN reindexing
are formalized, closes `(‡) ⟹ SymMinorGershgorin/FiniteSMargin ⟹ FusionConvLogConcaveCore` and the
SU(2) fusion core, which cascades toward the continuum floor. **Per the mandate, NO guarded
Clay-frontier bundle has been inhabited; `YMGapGuard` remains untouched.** The mathematical wall is
down; what remains is Lean bookkeeping. This is flagged LOUDLY for coordinator review before any
downstream bundle is touched — do NOT let a "bookkeeping-only" framing wave the last mile through
without an independent audit of (a) the acN→Ucoup truncation-safety direction and (b) the
finite-geometric tail constant, which are the two places a sign/direction error could hide.
