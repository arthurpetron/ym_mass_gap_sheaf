# Core B — dedicated attack on the fusion log-concavity reserve `(†)`

**Date:** 2026-07-06 · **Tree:** MAIN, `.../ym_mass_gap_sheaf/lean` (no worktree)
**New file:** `YMGap/Continuum/FusionCoreStepRoundM.lean` (imported in `YMGap.lean`)
**Build:** full `lake build` GREEN = **670 jobs**. `YMGapGuard` **OK** (5 Clay-frontier
types unconditionally uninhabited). No `sorry`/`Classical`/`native_decide`/custom `axiom`.
All new decls axiom-gated (`propext`/`Quot.sound` only; the `decide` fact is axiom-free).

---

## 0. The exact target `(†)`, extracted and quoted

The whole node reduces (Rounds A–L, in-tree) to one residual. From
`AutoconvGershgorin.lean` + `LeakGeoDecay.lean` + `AcNReserveAnalytic.lean`, with

- `coeffW w s = c_s = dimQ s · qpow w (c4 s) = (s+1)·w^{s(s+2)}`  (heat-kernel weight; `wH=1/2`),
- `acN w n S = Σ_{p<n} c_p·c_{S−p}`  (range-`n` **central autoconvolution**),

the sole open content is the truncated-block reserve on the **line-sum** `acN`:

> **(†)**  `(256/225)·acN(s+1,s)·acN(s+1,s+2) ≤ acN(s+1,s+1)²`,  for all `s`, at `w ≤ 1/2`.

`256/225 = (16/15)² = 1 + 31/225`. The line-sum is over `p ∈ [0,s]`; all three factors use the
**same** range `n = s+1`, so `acN(s+1,s)` is the full antidiagonal sum at total degree `s` while
`acN(s+1,s+1)`, `acN(s+1,s+2)` are truncated (missing the smallest 1 resp. 2 tail terms).

**Numeric confirmation (sympy exact, `w=1/2`):** `(†)` holds with a comfortable margin. The
worst `B/A = acN(s+1,s+1)²/(acN(s+1,s)acN(s+1,s+2))` over `s∈[0,40)` is **1.9893 at s=38**
(need `256/225 ≈ 1.1378`) — margin **×1.75**, and it does **not** drift toward `256/225`: even-`s`
decreases to the limit from above (`5.33, 2.48, 2.08, 2.04, 2.02, 2.01, …`), odd-`s` sits slightly
higher. The limit is `1/w = 2` (see §2). So the margin is uniform (`B/A → 2`), never approaching
the needed constant — the constant `256/225` is a *chosen sufficient slack*, not the sharp value.

`(†)` is genuinely a **strong-coupling** fact: at `w=63/64, s=4` it is FALSE (`B/A≈1.123<1.138`);
`B/A → 1` as `w→1`. Any proof must consume `w ≤ 1/2` (in-tree `reserve_fails_near_one`).

---

## 1. THE STRUCTURAL RESULT — exact Gaussian factorization (new, proved in Lean)

Writing `c_p = (p+1)w^{p(p+2)} = (p+1)w^{(p+1)²−1}`, the product of two weights on the
antidiagonal `a+b = S` factorizes **exactly**:

    c_a · c_b · w^{2ab}  =  (dimQ a · dimQ b) · w^{c4(a+b)},          (★)

proved in Lean as **`coeffW_antidiag_gaussian`** (axiom-clean), via the pure-`Nat` identity
**`c4_antidiag`**: `c4 a + c4 b + 2ab = c4(a+b)`  (i.e. `(a+1)²+(b+1)²+2(a+1)(b+1) = (a+b+2)²`).

(★) says: on `a+b = S` the weight product is a **single Gaussian** `w^{c4 S}` times a `w`-free
**coupling** `dimQ a·dimQ b` carried by the (cleared) negative power `w^{−2ab} = Q^{ab}`,
`Q = 1/w²`. Consequently

    acN(s+1,S) = w^{c4(S+2)−2} · U_trunc(S+2),   U(m) := Σ_{i+j=m, i,j≥1} i·j·Q^{ij}.

**Where the reserve comes from.** The Gaussian prefactors across the three modes of `(†)` have
**second difference exactly 2** (in-tree `c4_sum_symm`: `c4 S + c4(S+2) = 2 c4(S+1) + 2`, i.e.
`(s+2)²+(s+4)² = 2(s+3)²+2`, verified symbolically). Dividing `(†)` by the common Gaussian factor
**cancels it exactly** and leaves

    (256/225)·w² · U(s+2)·U(s+4)  ≤  U(s+3)²,   i.e.  U(s+3)² ≥ (256/(225·Q))·U(s+2)·U(s+4).   (‡)

So the **entire** reserve `256/225` is paid by the Gaussian gap `w^{−2} = Q ≥ 4`, and — since
`w² ≤ 1/4` — the coupling `U` need only supply the residual budget `(256/225)·w² ≤ 64/225 ≈ 0.284`
(proved in Lean as **`gaussianReserveBudget`**). The true coupling margin is
`U(s+3)²/(U(s+2)U(s+4)) → 1/√Q` (`= 0.5` at `Q=4`; **worst 0.4970 at s=58**, mpmath dps 60), giving
a **uniform ×1.75 cushion** over the needed `64/225`. Confirmed for `Q∈{4,5,8,16,64}` with margin
**growing** as `Q` grows (worst case is `Q=4`, i.e. `w=1/2`).

**Truncation is safe:** the truncated `(†)` margin is always `≥` the full-autoconvolution margin
(`= 2.0768 ≥ 2.0729` at `s=4`; diff `< 10⁻¹⁵` for `s ≥ 10`) — the dropped tail terms only *help*.

This is a genuine restructuring: it replaces the crude in-tree theta-floor residual
`FiniteSMargin` (`40000/22801`) and the not-PSD reserve matrix (`FusionCoreStepRoundL`) with the
**transparent** statement (‡): *all reserve is the Gaussian gap; `U` need only be not-too-anti-
log-concave.* At `w=1/2` (`Q=4`) the residual is a **pure integer inequality** `U(m)=Σ ij·4^{ij}`.

---

## 2. Why it is TRANSCENDENTAL (uniform-in-s), adversarially verified

`(‡)` is NOT closable by any elementary uniform bound:

- **`U` is not log-concave.** `U(m+1)²/(U(m)U(m+2)) ≈ 0.5 < 1` (so no reserve-1 semigroup/Hoggar
  argument gives it; the value needed is `< 1`, but only the *saddle width* delivers it).
- **Dominant-term / geometric-tail fails at EVERY physical `w`.** Bounding
  `U(m) ≤ central(m)·θ(Q)` (θ = theta-tail, `1+2Σ_{k≥1}Q^{−k²}`) and `U(s+3) ≥ central(s+3)` gives a
  crude ratio `central-ratio / θ(Q)²`. This under-shoots the need `256/(225Q)` for all tested
  `Q` up to `4096` (crude/need `= 0.39, 0.83, 0.88, …` — creeps toward 1 but never reaches it, and
  only at `w→0`). It loses **exactly the numerator's own saddle-width factor θ(Q)²** — the discrete
  local-CLT content. The central-term log-concavity gives `Q^{−1}`, the truth is `Q^{−1/2}`; the
  `√` is the saddle width and is irreducible to dominant-term estimates.
- **Not a matrix-positivity fact** (Round L): the reserve quadratic form is not PSD (negative
  `2×2` principal minor at `w=1/2`), so Gershgorin/diagonal-dominance/absolute-value bounds cannot
  close it.
- `U(m)=Σ_{i+j=m} ij Q^{ij}` has a **quadratic** exponent `ij`, so it is theta-like, **not
  holonomic** — no finite linear recurrence in `m`; an induction-in-`s` carry does not exist.

**Verdict on the uniform-in-`s` route:** it is a genuine **heat-kernel local-CLT (saddle-WIDTH)**
statement. `(†)` is NOT proved uniform-in-`s` in this session, and none of the reductions dissolve
that wall — they *localize and explain* it. Small-`s` `decide` (now through `s=4`, Round L through
`s=3`) is **not** `∀s`; the `∀s` cancellation is the transcendental content and is not claimed.

---

## 3. What is PROVED in Lean (`FusionCoreStepRoundM.lean`, all axiom-clean)

| decl | content | axioms |
|---|---|---|
| `c4_antidiag` | `c4 a + c4 b + 2ab = c4(a+b)` (antidiagonal Casimir identity, Nat) | `[propext, Quot.sound]` |
| `coeffW_antidiag_gaussian` | **(★)** `c_a·c_b·w^{2ab} ≃ (dimQ a·dimQ b)·w^{c4(a+b)}` — the exact Gaussian factorization | `[propext, Quot.sound]` |
| `gaussianReserveBudget` | `reserveC·w² ≤ 64/225` for `w ≤ 1/2` — the reserve is `≤ 64/225` of the coupling margin; the rest is the Gaussian gap | `[propext]` |
| `reserve_holds_at_half_4` | `(†)` holds at `w=1/2, s=4` (`B/A≈2.077`), extending Round L's `s=0..3` | none |

`#print axioms` for all four: `propext`/`Quot.sound` only (the `decide` fact axiom-free). Full
`lake build` 670 jobs GREEN; `YMGapGuard` **OK**.

---

## 4. HONEST verdict

- **`(†)` is NOT closed uniform-in-`s`; nothing downstream is closed; no guarded Clay-frontier
  bundle is inhabited (`YMGapGuard` OK).** This is NOT a 4D Yang–Mills mass gap.
- **Genuine advance:** the exact Gaussian factorization `(★)` (proved) pins the reserve's source —
  the *entire* `256/225` is paid by the Gaussian second-difference `w^{−2} ≥ 4` (`c4_sum_symm`) —
  and reduces `(†)` to the clean `w`-free coupling log-concavity `(‡)`
  `U(s+3)² ≥ (256/(225Q))·U(s+2)U(s+4)`, `U(m)=Σ ij Q^{ij}`, with a uniform ×1.75 cushion (worst
  `Q=4`). At `w=1/2` this is a pure **integer** inequality on `U(m)=Σ ij·4^{ij}`.
- **The residual is confirmed transcendental** (saddle-WIDTH local-CLT): not log-concave, not PSD,
  not dominant-term-closable at any physical `w`, not holonomic (no induction carry). The exact
  transcendental residual is: *the discrete theta autoconvolution `U(m)=Σ ij Q^{ij}` (`Q=1/w²≥4`)
  has log-concavity margin `U(m+1)²/(U(m)U(m+2)) ≥ 256/(225Q)` uniformly in `m`* — a
  `θ`-ratio / Tate–Zelditch saddle-remainder bound.

**Sharpest reducible piece delivered:** the exact factorization + reserve accounting (Lean-proved),
which cleanly separates the *provable* Gaussian gap (`w^{−2} ≥ 4 > 256/225`, all reserve) from the
*transcendental* coupling width (`U`-margin `→ 1/√Q`, the local-CLT), in its most transparent
`w`-free form to date.
