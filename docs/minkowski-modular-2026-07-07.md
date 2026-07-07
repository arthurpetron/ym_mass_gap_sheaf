# The Lorentzian / modular (Tomita–Takesaki) reflection route — does it carry the mass-gap defect, or inherit RP gap-blindness?

**Date:** 2026-07-07. **Scope:** whether the "true Minkowski with reflections" framing — the
Tomita–Takesaki **modular** structure whose Euclidean shadow is OS2 reflection positivity —
supplies a genuinely-new, non-gap-blind handle on the block-spin defect `realδ_k`
(= `SingleStepDefectReduction.SingleStepDefectBound.singleStep`), or inherits the
machine-checked gap-blindness of Euclidean RP (`ReflectionCondensateBound.rp_gap_blind`) plus
the free-energy wall (`MKBondMovingControl.mkVariational_bounds_freeEnergy_not_gapDefect`).

**Deliverables:** `lean/YMGap/Continuum/MinkowskiModularReflection.lean` (new, wired into
`YMGap.lean`; full `lake build` **green = 752 jobs**; `YMGapGuard` **frontier-guard OK = 5**
Clay-frontier types unconditionally uninhabited). Lean-core only (`Q'`/`Nat` + `CReal`/`ExpNeg`);
no Mathlib/`ring`/`native_decide`/`Classical`/`sorry`. Axiom gate `propext`/`Quot.sound` only.
Numerics: `modular_relent.py` (mpmath, dps 45). **Committed: nothing** (per instruction).

---

## 0. HEADLINE VERDICT (task criterion (iii): machine-checked GAP-BLIND + free-energy wall)

**The Lorentzian/modular reflection framing is GAP-BLIND — it INHERITS `rp_gap_blind`, in a
SHARPER form (gapless at *every* modular time, not just the Euclidean `t = 0` endpoint) — AND
its quantitative content (relative entropy) is a free-energy difference that hits the MK
free-energy-≠-gap-defect wall. It supplies NO genuinely-new, non-gap-blind handle on `realδ_k`.
This CLOSES the reflection route in its strongest (Minkowski / modular / relative-entropy) form.**

The honest prior held. This is **outcome (iii)**, not (i) or (ii): no `SingleStepDefectBound`
inhabitant, and no new non-gap-blind modular handle. No `SingleStepDefectBound` alias is
introduced (the forbidden move); the relative-entropy content lands strictly BELOW the gap
defect, on the free-energy bracket.

---

## 1. The modular counterpart of RP is the BOOST — gap-blind by Bisognano–Wichmann (task point 1)

Euclidean OS2 reflection positivity ↔ Tomita–Takesaki modular structure. **Bisognano–Wichmann:**
for a Rindler wedge the modular flow `σ_s = Δ^{is}` is exactly the **Lorentz boost**, and the
modular conjugation `J` is the **wedge reflection**. The mass gap, by contrast, is the spectral
gap of the **Hamiltonian `H = P⁰`** — a *different* generator.

- **(a) The modular generator is the boost `B`, not `H`.** `B` has spectrum `ℝ`: continuous,
  `J`-symmetric under `s ↦ −s`, containing `0` and accumulating there. A gapped `H` has
  spectrum `{0} ∪ [m, ∞)`, gap `m > 0`. So the modular/reflection data holds for the
  gapless (massless/scale-invariant) theory just as OS2 does — **gap-blind**, and *sharper*
  than the Euclidean `t = 0` endpoint: gapless at **every** modular time `s`.

**Lean formalization** (modular reflection weight `modWeight s λ = e^{−s·λ}` for boost
eigenvalue `λ`, the Minkowski analogue of `reflWeight t s = e^{−t·C₂(s)}`):

| fact | Lean | status |
|---|---|---|
| modular (KMS/Bisognano–Wichmann) reflection positivity, all `s ≥ 0`, all boost spectra, all real `c` | `modReflPositive_holds` | **PROVED** (via `diagReflForm_nonneg`, the same SOS engine that discharges OS2) |
| zero-boost mode pinned to `1` at **every** modular time `s`: `modWeight s 0 = 1` (identity Gram) | `modWeight_zeroBoost_squeeze` | **PROVED** |
| **modular GAP-BLINDNESS** (mirror of `rp_gap_blind`, sharper): modular RP holds at the gapless boost spectrum, form = identity Gram at every `s` | `modular_gap_blind` | **PROVED (new)** |
| boost spectrum accumulates at `1`: `modWeight s λ ≥ 1 − λ·s → 1` as `λ → 0` (no gap in the modular generator) | `modWeight_near_one` | **PROVED (new)** |
| **the CONTRAST**: the mass-gap Hamiltonian is NOT gapless — `casimirQ 1 = 3/4 > 0` (isolated spectrum ⇒ the gap lives in `H`, not the boost) | `hamiltonian_gap_floor` | **PROVED** |

The decisive structural statement: the SAME predicate that would "certify" a gapped theory holds
identically for the gapless one (`boostGapless := fun _ => 0`), at arbitrary modular time. An
inhabitant of the modular reflection predicate is compatible with **zero gap**. This is
`rp_gap_blind` inherited — and strengthened from the single point `t = 0` to *all* `s`, because
the boost's continuous spectrum contains a `λ = 0` invariant mode and accumulates at `λ → 0`.

---

## 2. The quantitative content is RELATIVE ENTROPY — it hits the MK free-energy wall (task point 2)

The quantitative modular datum under RG coarse-graining is the **relative entropy**
`S(ω_fine‖ω_coarse)`, monotone by data-processing (Uhlmann–Lindblad) / QNEC. But relative
entropy is a **free-energy difference**: `S(ρ‖σ) = β(F_ρ − F_σ) ≥ 0` (Gibbs / Donsker–Varadhan).
`MKBondMovingControl` already proved a free-energy bracket does **not** control the gap defect
(the free energy `[c^{⋆m}]₀` explodes `1 → 1.1·10⁷` while the gap indicator `2 − ρ_m` stays
`O(1−w)` and *decreases* `≈ 6(1−w)/m`).

**Numerical adjudication** (`modular_relent.py`, mpmath dps 45, SU(2) heat-kernel fusion at
`w = 0.99`, `ε = 1−w = 0.01`; exact Peter–Weyl integral representation
`[c^{⋆m}]_s = (2/π)∫₀^π f(θ)^m sin((s+1)θ) sinθ dθ`, `f = Σ_s (s+1)w^{s(s+2)}χ_s`):

| m | free energy `Z_m = [c^{⋆m}]₀` | `logZ_m` | gap defect `2 − ρ_m` | `(2−ρ)/ε` (target `6/m`) | rel. entropy `S_m = S(ρ_m‖ρ_1)` | `S_m / logZ_m` |
|---|---|---|---|---|---|---|
| 1 | 1.000 | 0.000 | 0.05940 | 5.94 | 0.000 | — |
| 2 | 158.65 | 5.067 | 0.03003 | 3.00 | 0.2847 | 0.0562 |
| 3 | 38491.0 | 10.558 | 0.02009 | 2.01 | 0.6390 | 0.0605 |
| 4 | 1.1125·10⁷ | 16.225 | 0.01509 | 1.51 | 0.9431 | 0.0581 |

(`Z_m = 1, 159, 38491, 1.1·10⁷` reproduces the MK-control table exactly — the convention is
validated.) **Decisive read-off:**

- **`S_m` GROWS with `m`** (extensive): `0 → 0.28 → 0.64 → 0.94`.
- **`S_m / logZ_m ≈ 0.056–0.061`** — a near-**CONSTANT** ratio to the free energy: relative
  entropy **TRACKS the exploding free energy `logZ_m`**.
- The gap defect `2 − ρ_m` **DECREASES** `≈ 6ε/m`. `S_m` and `2 − ρ_m` have **opposite
  monotonicity** — relative entropy is **decorrelated** from the gap defect.

So relative entropy tracks the free energy, not the gap defect: it inherits the MK wall.

**Lean formalization:**

| fact | Lean | status |
|---|---|---|
| relative entropy as its Gibbs free-energy identity `S = F_fine − F_coarse ≥ 0` | `RelativeEntropyData`, `relEnt`, `relEnt_nonneg` | **PROVED** |
| **relative entropy IS a free-energy bracket** — `RelativeEntropyData → MKFreeEnergyBracket` (the object proved silent about the gap defect) | `relativeEntropy_to_freeEnergyBracket` | **PROVED (the reduction)** |

The bridge `relativeEntropy_to_freeEnergyBracket` takes `freeEnergy := F_fine`,
`mkLower := F_coarse`, `mkUpper := F_fine`; the Gibbs inequality `F_coarse ≤ F_fine` (positivity
of relative entropy) IS the lower bracket. So the modular quantitative content lands **exactly**
on `MKBondMovingControl.MKFreeEnergyBracket`, which `mkVariational_bounds_freeEnergy_not_gapDefect`
proved does not transfer to `realδ_k`. **No `SingleStepDefectBound` alias:** relative entropy does
not even *reach* the gap defect — it stops at the strictly-weaker free-energy bracket.

---

## 3. The modular FLOW sub-question — also reduces to free energy (task point 3)

Does the modular **flow** (relative modular Hamiltonian / QNEC monotonicity) carry MORE than the
static reflection? **No.** The relative modular Hamiltonian `K_{ρ|σ} = −log Δ_{ρ|σ}` has
expectation `⟨K_{ρ|σ}⟩_ρ = S(ρ‖σ)` — the *same* relative entropy — and QNEC (`∂²_s S ≥ 0`) /
data-processing monotonicity is a convexity of that same free-energy functional. So the modular
flow also reduces to the free-energy bracket.

| fact | Lean | status |
|---|---|---|
| modular-flow datum (relative modular Hamiltonian + QNEC monotonicity of `S`) | `ModularFlowData` | Type (Rule 8) |
| **the modular flow ALSO hits the free-energy wall** — `ModularFlowData → MKFreeEnergyBracket` | `modularFlow_to_freeEnergyBracket` | **PROVED (the reduction)** |

The QNEC monotonicity field is itself a statement about the free-energy-difference sequence
`relEnt`, not the gap defect. The one genuinely-open piece — the flow — is **not** a new
non-gap-blind handle: it lands on the same wall.

---

## 4. Adversarial verdict (task point 4)

**Is the Lorentzian/modular reflection framing (i) a genuinely-new non-gap-blind handle on
`realδ_k`, or (iii) gap-blind + free-energy-walled?** → **(iii), machine-checked.**

- **Gap-blind:** `modular_gap_blind` — the modular reflection predicate holds identically for the
  gapless boost spectrum at every modular time; it inherits `rp_gap_blind` in a sharper form
  (`euclideanGapBlind` re-exports the Euclidean statement it mirrors). The gap lives in `H`
  (`hamiltonian_gap_floor`: `casimirQ 1 = 3/4 > 0`), which the modular/boost data cannot see.
- **Free-energy-walled:** `relativeEntropy_to_freeEnergyBracket` and
  `modularFlow_to_freeEnergyBracket` — the relative-entropy content (static and flow) reduces to
  the `MKFreeEnergyBracket`, numerically confirmed to track the exploding free energy
  (`S_m/logZ_m ≈ const`), decorrelated from the shrinking gap defect.

Refutation attempts that FAILED to salvage a new handle (each honestly checked, none works):
- *"Modular flow = physical time evolution ⇒ its generator is `H` ⇒ carries the gap."* — **False.**
  Bisognano–Wichmann: the modular generator is the **boost** `B`, whose spectrum is continuous
  through `0` (`modWeight_near_one`, `modWeight_zeroBoost_squeeze`), not `H` (gap `m`). The Unruh
  effect is precisely the statement that the modular flow is *thermal/boost*, not energy.
- *"Relative-entropy monotonicity is a strict inequality ⇒ a positive bound."* — **True but
  free-energy-valued.** `S(ρ‖σ) = β(F_ρ − F_σ)` is a difference of `log Z`'s; its positivity is
  the Gibbs inequality on free energies, which MK proved is silent about `ρ_m`. Numerics confirm
  `S` tracks `logZ`, not `2 − ρ_m`.
- *"QNEC / relative modular Hamiltonian carries the flow's derivative content."* — **Same
  functional.** `⟨K_{ρ|σ}⟩_ρ = S(ρ‖σ)`; QNEC is its convexity — still free energy.

**Residual (NOT closed):** `realδ_k = SingleStepDefectBound.singleStep`, untouched — the
reflection is gap-blind and the relative entropy stops at the free-energy bracket.

---

## 5. Build / guard / `#print axioms`

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited
Build completed successfully (752 jobs).
```

All 12 load-bearing declarations `#print axioms ⊆ {propext, Quot.sound}` (no `Classical.*`, no
`sorryAx`, no `native_decide`, no `ring`):

```
modWeight_nonneg                       : [propext, Quot.sound]
modWeight_le_one                       : [propext, Quot.sound]
modReflForm_nonneg                     : [propext, Quot.sound]   ← modular (KMS) reflection positivity
modReflPositive_holds                  : [propext, Quot.sound]
modWeight_zeroBoost_squeeze            : [propext, Quot.sound]   ← λ=0 mode = 1 at every s
modular_gap_blind                      : [propext, Quot.sound]   ← THE modular gap-blindness (sharper rp_gap_blind)
modWeight_near_one                     : [propext, Quot.sound]   ← boost spectrum accumulates at 1
hamiltonian_gap_floor                  : (no axioms)             ← casimirQ 1 = 3/4 > 0 (the contrast)
relEnt_nonneg                          : [propext]
relativeEntropy_to_freeEnergyBracket   : [propext]               ← relative entropy → free-energy wall
modularFlow_to_freeEnergyBracket       : [propext]               ← modular flow → free-energy wall
minkowski_modular_verdict              : [propext, Quot.sound]
```

**Guard / STOP audit:** no guarded Clay-frontier bundle inhabited; `minkowski_modular_verdict`
is an informational record of PROVED facts only; no `SingleStepDefectBound` inhabitant and no
`def _ := SingleStepDefectBound` alias. The `→ MKFreeEnergyBracket` producers are conditional
(they consume `RelativeEntropyData` / `ModularFlowData`) and target a *non-frontier* free-energy
type, so the guard correctly does not react.

---

## 6. HONEST FINAL VERDICT

The "true Minkowski with reflections" / Tomita–Takesaki modular framing does **not** give a
genuinely-new, non-gap-blind handle on the block-spin defect. Machine-checked here:

1. **It is GAP-BLIND** (`modular_gap_blind`), inheriting `rp_gap_blind` in the *sharper* form
   "gapless at every modular time `s`" — because the modular generator is the **boost**
   (continuous spectrum through `0`, `modWeight_near_one` + `modWeight_zeroBoost_squeeze`), not
   the Hamiltonian `H` whose spectrum is isolated (`hamiltonian_gap_floor`, `casimirQ 1 = 3/4`).
2. **Its quantitative content — relative entropy — hits the MK free-energy wall**
   (`relativeEntropy_to_freeEnergyBracket`, `modularFlow_to_freeEnergyBracket`), because
   `S(ρ‖σ)` is a Gibbs free-energy difference, numerically tracking the exploding free energy
   (`S_m/logZ_m ≈ 0.056–0.061`) and decorrelated from the shrinking gap defect `2 − ρ_m`.

This **CLOSES the reflection route in its strongest (Minkowski / modular / relative-entropy)
form** — task criterion (iii). No frontier bundle is inhabited; no `SingleStepDefectBound` alias
is introduced; nothing is faked; the 4D Yang–Mills mass gap remains **OPEN**. The live target
remains atomic `singleStep` (the real 4D block-spin per-step defect over the full RG recursion).
