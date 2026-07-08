# Multi-scale / dyadic chord tightening of the sum-level θ lower bound — 2026-07-08

**Owner files:** `JacobiModularCReal.lean` §3c (new).  Lean-core (`Q'`/`CReal`), axiom gate
`propext`/`Quot.sound`, guard 5.  No `EnterWorktree`; edits in the main tree.  Coordinated:
did NOT touch Penrose/ReachTransport.

---

## 1. What was built (Lean, axiom-clean, non-vacuous)

New subsection `JacobiModularCReal §3c`, all `#print axioms ⊆ {propext, Quot.sound}`, no
`sorry`/`native_decide`/`Classical`/`:= True`:

| decl | statement | constant vs sharp `½√(π/ε)` |
|---|---|---|
| `chord_nat` | `n² ≤ N_lo² + (N_hi+N_lo)(n−N_lo)` (convexity chord, `Nat`) | — |
| `pow_chord_block` | `q^{N_lo²+(N_hi+N_lo)(n−N_lo)} ≤ q^{n²}` (reusable per-block minorant) | — |
| **`thetaHalf_ge_geomChord`** | **`Σ_{i<N} q^{(i+1)N} ≤ Σ_{n≤N} q^{n²}`** (single geometric block) | **`≈ 0.720`** |
| `geomChord_ge_count` | `N·q^{N²} ≤ Σ_{i<N} q^{(i+1)N}` (chord beats count term-by-term) | proves genuine tightening |
| `thetaPartial_ge_geomChord` | `1 + 2·Σ q^{(i+1)N} ≤ θ_N` | lift to symmetric partial sum |
| `thetaS_geRat_geomChord` | `ϑ₃(q) ≥ 1 + 2·Σ_{i<N} q^{(i+1)N}` | the tightened divergence bound |
| `fsum_splitM` | `Σ_{k<a+b} f = Σ_{k<a} f + Σ_{r<b} f(a+r)` (local split) | — |
| **`thetaHalf_ge_twoBlock`** | **`Σ_{n≤M} q^{nM} + Σ_{n≤M} q^{M²+3Mn} ≤ Σ_{n≤2M} q^{n²}`** | **`≈ 0.880`** |

**Method = CONVEXITY / chord domination, purely sum-level.** On a block `[N_lo,N_hi]` the
parabola `n²` lies below its own chord, so `q^{n²} ≥ q^{N_lo²}·(q^{N_hi+N_lo})^{n−N_lo}` — a finite
GEOMETRIC series, summable in closed form. This is a Riemann-lower-sum of the Gaussian evaluated
as a geometric sum, **NOT** the integral. **No Poisson, no integration, no exact modular identity**
(all forbidden/eliminated). Everything routes through the existing `pow_base_antitone` +
`fsum_mono_lt` machinery.

## 2. Did multi-scale counting reach the 1.38× window?

**YES — the two-block minorant clears it; the single block narrowly misses.** The consumer margin
is `1/1.38 = 0.7246` (the `s≥7` envelope tail infimum `≥7.96` vs required `144/25=5.76`).

Verified numerically (`mpmath` dps 30, the EXACT integer chord exponents used in Lean, optimising
the block width `M`):

| bound | constant (÷ sharp `½√(π/ε)`) | vs window `0.7246` |
|---|---|---|
| single-scale count `thetaHalf_ge_count` (prior) | `0.484` | far outside (`≈2×` loose) |
| **single-block chord `thetaHalf_ge_geomChord`** | **`0.720`** | misses by `0.6%` |
| **two-block dyadic `thetaHalf_ge_twoBlock`** | **`0.880`** | **INSIDE (`0.880 > 0.7246`)** |
| K=3 blocks | `0.933` | inside |
| K=4 blocks | `0.957` | inside |

(`a=10⁻³`: half=27.525, single=0.720, two=0.880, clears; `a=10⁻⁴`: half=88.123, same ratios.)
Stacking dyadic blocks drives the constant `→1`; two blocks already clear the margin with room
(`0.880/0.7246 = 1.21×` inside). The single geometric block is a genuine `1.5×` improvement over
the count (`0.484 → 0.720`), proved term-by-term in Lean by `geomChord_ge_count`.

## 3. Did M1/M2 / hlocalize close? — HONEST verdict: NO.

**The constant was tightened INTO the window, but M1/M2/hlocalize do NOT close, because the
constant was never the sole gate.** Traced through the actual Lean:

- `thetaS_geRat_count` / `thetaHalf_le_geom` / the new chord bounds have **NO downstream consumer**
  anywhere in `lean/` (grep-verified). They are standalone sum-level θ objects.
- `MomentEnvelopePoissonDual w` requires `∀ s, AbelFullRangeFloor w s` (the `−2` curvature floor);
  the SHARPER `R1CurvatureEnvelope.CurvatureEnvelope` tail `∀ s≥7` (`Δ²V+2 ≥ (144/25)w²(1−w²)`)
  is the genuine open core. **Neither is wired to any θ bound.** The reduction chain
  `θ two-sided bound ⟹ V=2/ε−4R₁/(ε²R₀) ⟹ Δ²V+2 ≥ (144/25)w²(1−w²) for s≥7 ⟹ M1/M2 ⟹ hlocalize`
  is **not built** in the codebase — it is the large remaining analytic content (second-difference
  of the theta-ratio moment `V(t)`), of which the θ-constant is one input.
- Guard reaction: `frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited` —
  unchanged. M1/M2/hlocalize did **not** discharge (correct).

**One further honesty caveat on the constant itself.** The Lean object is the term-domination
INEQUALITY (`thetaHalf_ge_twoBlock`), fully machine-checked. Its optimised constant `0.880` is
verified NUMERICALLY, **not** in Lean: extracting the constant requires the transcendental scale
`M ∼ 0.75/√(−ln q)` and the closed-form geometric evaluation against the `√(π/ε)` asymptotic —
i.e. choosing `N`/`M` as functions of `q` via `√(−ln q)`, which is outside the `Q'`/`CReal` core.
So the machine-checked statement is "`ϑ₃ ≥` this geometric minorant"; the "constant is `0.880`,
inside `1.38×`" is a real-analysis fact verified numerically (as the prior `cs_probe3.py` was).

## 4. Verification (re-run this session)

- `lake build` (full): **exit 0, 785 jobs**, `Build completed successfully`.
- Frontier **guard 5**: `frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited`.
  M1/M2/hlocalize did **not** react.
- `#print axioms` on all 9 new decls: `[propext]` / `[propext, Quot.sound]` only; no `sorryAx`.
- `python3 scripts/lean_axiom_audit.py`: **PASS** (7542 theorems observed).
- Banned tokens (`native_decide`, `sorry`, `Classical`, `:= True`, `nlinarith`, `ring`) in code:
  **NONE** (only the honest-scope docstring names them as absent).
- Route audit: no integration / Poisson / exact-modular; pure sum-level chord + `pow_base_antitone`.

## 5. Verdict

- **Multi-scale reached the window.** The user's dyadic-counting route works: two chord blocks give
  a sum-level minorant with constant `0.880 > 0.7246 = 1/1.38`, inside the envelope margin — where
  the prior single-scale count (`0.484`) and even the single geometric block (`0.720`) fell short.
  Genuine, axiom-clean, no integration.
- **But it does NOT close M1/M2 or hlocalize.** The θ constant is one input to an UNBUILT analytic
  chain (θ two-sided bound ⟹ `Δ²V+2 ≥ (144/25)w²(1−w²)` on `s≥7`). That second-difference moment
  reduction — not the constant — is the sharp residual. The best `c` achieved in-window is `0.880`
  (two-block); the sharp residual is now the **moment-ratio second-difference bound** wiring the
  in-window θ bracket to `CurvatureEnvelope`'s `s≥7` tail. The Clay YM mass gap remains OPEN.
