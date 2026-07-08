# θ-inversion for M1/M2 — consumer schema (exact vs bounds), sum-level bracket, honest verdict

**Date:** 2026-07-08. Lean-core (`Q'`/`CReal`), axiom gate `propext`/`Quot.sound`, guard 5.
Owner files: `JacobiModularCReal.lean`, `AbelianMomentEnvelope.lean` (+ read of the consumer
`R1CurvatureEnvelope.lean`). No `EnterWorktree`; edits in the main tree.

---

## 1. CONSUMER-SCHEMA EXTRACTION (task step 1) — the headline

**Question:** does the M1/M2 envelope need the EXACT modular identity `ϑ(1/t)=√t·ϑ(t)`, or only
TWO-SIDED bounds `c₁√t·ϑ(t) ≤ ϑ(1/t) ≤ c₂√t·ϑ(t)`?

**Answer: BOUNDS, not the exact identity.** Traced through the actual Lean consumer.

The object M1/M2 feed is NOT literally `V·(1−w)≤2` / `Var·(1−w)²≤8`. Those are the *route*
`poisson_M1M2.md` uses. The genuine consumer is the **curvature envelope**
`R1CurvatureEnvelope.CurvatureEnvelope` (= the abelian shadow `AbelianMomentEnvelope.AbelFullRangeFloor`):

    Δ²V(s) + 2  ≥  (144/25)·w²·(1−w²)      for all windows s,   V(t)=dmomNfull/acNfull.

Its constant `144/25 = 5.76` is **strictly below the s→∞ asymptotic**. I verified numerically
(`cs_probe.py`, mpmath dps 50; the SU(2) moments with `coeffW w s = (s+1)w^{s(s+2)}` exactly matching
the Lean defs) the infimum over `w∈(0,1)` of `(Δ²V(s)+2)/(w²(1−w²))`:

| s | inf ratio | argmin w |   | s | inf ratio |
|---|-----------|----------|---|---|-----------|
| 0 | 5.7600 (=144/25, tight) | 0.408≈1/√6 | | 7 | 7.957 |
| 1 | 6.8571 (=48/7) | 0.707 | | 8 | 7.967 |
| 2 | 7.208 | 0.731 | | 20 | 7.9966 |
| 3 | 7.560 | 0.735 | | ∞ | → 8 (plateau) |

The envelope is **tight only at s=0** (proved exactly there as a perfect square, `curvatureEnvelope_zero`;
windows s=0..6 all proved by Bernstein certificates). On the open **tail s ≥ 7** the true infimum ratio
is `≥ 7.957`, while only `5.76` is required — a **uniform multiplicative margin ≈ 7.96/5.76 = 1.38×**.

**Consequence:** the tail does not need a sharp modular *equality*. Two-sided bounds
`ϑ(1/t) ≍ √t·ϑ(t)` with looseness under the `1.38×` budget suffice. This is the cheaper schema the
task predicted, and it is now grounded in the actual consumer, not asserted.

*(Rigor note: the `1.38×` margin is an exact numeric fact about the consumer `(Δ²V+2)/(w²(1−w²))`.
The further step "M1 constant may be loose up to 1.38" is the natural but heuristic V-level reading;
the load-bearing, machine-relevant statement is the envelope-ratio margin itself.)*

---

## 2. THE θ-INVERSION BOUND, SUM-LEVEL, NO INTEGRATION (task step 2) — built in Lean

`JacobiModularCReal §3b` (new, axiom-clean, `#print axioms ⊆ {propext, Quot.sound}`, no `sorryAx`):

| decl | statement | role |
|---|---|---|
| `thetaPartial_mono` | `θ_N ≤ θ_{N+d}` | partial sums monotone |
| `thetaS_geRat_partial` | `ϑ₃(q) ≥ θ_N` for every N | monotone lower-bound family |
| `fsum_const_val` | `Σ_{i<N} c ≃ N·c` | helper |
| `thetaHalf_ge_count` | `N·q^{N²} ≤ Σ_{n=1}^N q^{n²}` | counting kernel of the √-rate |
| **`thetaS_geRat_count`** | **`ϑ₃(q) ≥ 1 + 2N·q^{N²}`, every N** | **the DIVERGENCE lower bound** |
| `thetaHalf_le_geom` | `Σ q^{n²} ≤ Σ_{i<N} q^{2i+1}` | upper leg (→ `q/(1−q²)`) |

Everything is derived at the **sum level** from the counting / `pow_base_antitone` domination
already in the file (the same super-geometric `q^{(l+1)²} ≤ q^{2l+1}` used for the convergence
modulus). **No Poisson summation, no contour/Fourier integral, no multivariate integration** — exactly
the BK-lesson constraint. The triple product `ThetaConv.thetaConvCReal` was inspected but only realises
`ϑ₃` for `q ≤ 1/16` (small-nome regime), so it does not reach the binding `q → 1` regime; the
counting/geometric route is what applies there.

**Why `thetaS_geRat_count` is the load-bearing one.** For fixed `q<1`, `ϑ₃(q)` is finite; the crux is
its DIVERGENCE as `q → 1` (`ε = −ln q → 0`), which is what stops the moment ratio
`V = (Σ_D D²q^{D²})/(Σ_D q^{D²})` from blowing up. Choosing `N ∼ 1/√ε` in `1 + 2N·q^{N²}` makes the
right side `∼ (2/e)/√ε ∼ 1/√(1−q) → ∞`. Verified (`cs_probe3.py`): the family reproduces the true
`√(π/ε)` growth rate, with best value `≈ 0.50–0.70 ×` the truth.

---

## 3. HOW FAR M1/M2 (and hlocalize) CLOSE — honest verdict

**They do NOT close this session; the residual is SHARPENED, not discharged.**

- The margin budget is `1.38×`. The elementary sum-level lower bound `thetaS_geRat_count` has constant
  `2/e ≈ 0.74` of the sharp `√(π/ε)` — a factor `≈ 2` loose (`cs_probe3.py`: ratio → ~0.5 as q→1),
  i.e. **outside** the `1.38` window. Single-scale counting/geometric domination is provably too loose.
- The near-sharp two-sided bound (constant within `1.38`) requires the `√(π/ε)` scale. That is
  obtainable either via the 1-D integral test with the Gaussian value `∫e^{−εx²}=½√(π/ε)` (the
  integration the task steers away from), or a `q → 1` triple-product estimate the codebase does not
  yet carry. That single near-sharp constant is the genuine remaining input.

So the route the user specified genuinely **reduces the target**:

    OLD residual: prove the EXACT modular identity ϑ₃(1/τ)=√τ·ϑ₃(τ)  (irrational dual nome, Poisson).
    NEW residual: prove a TWO-SIDED sum-level theta bound ϑ₃(q) ≍ √(π/ε)·(…) tight to within 1.38×
                  in the q→1 regime  (constant only; sign/rate already built here).

The exact-identity obligation (irrational nome `e^{−π²/ε}`, `CReal`-exp-of-`CReal`, term-by-term
Poisson) is **eliminated** as unnecessary. What remains is a scalar-constant tightening, strictly
smaller and better-posed. `MomentEnvelopePoissonDual` and `hlocalize` stay OPEN; the Clay YM mass gap
stays OPEN.

**SU(2) lift (task step 4):** unchanged and already exact — `coeffW_prod_eq_weyl_abel`
(`w²·coeffW·coeffW ≃ (dimQ·dimQ)·abelCoeff·abelCoeff`) carries any abelian bracket to the SU(2)
moments up to the Weyl `1/(s+2)²` perturbation; no new obstruction there.

---

## 4. VERIFICATION (re-run this session)

- `lake build` (full): **exit 0, 784 jobs**, `Build completed successfully`.
- Frontier **guard 5**: `frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited`.
  M1/M2/hlocalize did **not** react (correct — not discharged).
- `#print axioms` on all 7 new decls: `[propext]` / `[propext, Quot.sound]` only; no `sorryAx`.
  `thetaPartial_nonconstant` depends on no axioms.
- `python3 scripts/lean_axiom_audit.py`: **PASS** (7521 theorems observed, +28 tracked).
- Banned tokens (`native_decide`, `sorry`, `Classical`, `:= True`) in code: **NONE** (only the
  honest-scope docstring names them as absent).
- Route audit: no integration/Fourier used; the bracket is pure sum-level counting + `pow_base_antitone`.

---

## 5. HONEST VERDICT

- **Exact vs bounds:** BOUNDS suffice — the consumer (`CurvatureEnvelope`, const `144/25`) carries a
  `≈1.38×` uniform tail margin over the s→∞ plateau `8`. The exact modular identity is NOT required.
- **Triple-product not integration:** the two-sided theta bracket is built at the sum/product level
  (counting + geometric domination), no Poisson, no integration — as instructed.
- **Did it close M1/M2 / hlocalize?** No. The elementary bracket is `≈2×` loose, outside the `1.38`
  window. The sharp residual is now precisely **a near-sharp (`<1.38`) two-sided theta bound in the
  q→1 regime**, i.e. the `√(π/ε)` scale constant — strictly smaller than the exact-identity wall it
  replaces. Not faked: no `Prop:=True`, no assumed hypothesis passed as proof, no vacuous inhabitant.
