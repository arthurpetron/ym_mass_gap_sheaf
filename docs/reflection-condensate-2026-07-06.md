# The reflection-positivity / correlation-inequality bound on the spacing-uniform condensate

**Deliverable Lean file:** `lean/YMGap/Continuum/ReflectionCondensateBound.lean` (wired into
`YMGap.lean`; full `lake build` **green = 725 jobs** (724 → 725); `YMGapGuard`
**frontier-guard OK = 5** Clay-frontier types unconditionally uninhabited). MAIN tree, NEW
file, Lean-core only (`Q'`/`Nat` + the `CReal`/`ExpNeg` backbone), no
Mathlib/`ring`/`native_decide`/`Classical`/`sorry`. Axiom gate `propext`/`Quot.sound` only
on all 11 load-bearing decls (several just `[propext]`). **Committed: nothing** (per instruction).

---

## 0. HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

**The reflection-positivity / correlation-inequality tool gives the FIXED-SPACING condensate
lower bound (the PROVED anchor) but NOT the spacing-uniform (a→0) bound. It is an EIGHTH
independent confirmation that the a→0 uniformity = `singleStep`.** The decisive new content —
machine-checked here for the first time — is that **reflection positivity is GAP-BLIND**: OS2
holds identically at `t = 0`, where the reflection form degenerates to the identity Gram
(a massless, zero-gap, scale-invariant theory), so an inhabitant of OS2 cannot distinguish a
gapped from a gapless theory and cannot furnish a positive spacing-uniform floor.

This is NOT the genuine new construction the task hoped for; it is the same irreducible core
seen through a genuinely different, and provably insufficient, tool.

---

## 1. THE OS2 REFLECTION-POSITIVITY SCHWARZ (task point 1) — fixed-spacing, does NOT lower-bound the condensate

OS2 is `0 ≤ E(θ(a)*·a)`, a Gram/PSD form. After Schur diagonalization it is the diagonal
sum of squares `R_t(c) = Σ_s e^{−t·C₂(s)}·c_s² ≥ 0` for **every** real `c`
(`ReflectionPositivity.reflSchwinger_nonneg`, PROVED unconditionally). The associated
**Cauchy–Schwarz `|E(θ(a)*·b)|² ≤ E(θ(a)*·a)·E(θ(b)*·b)` already exists and is PROVED**
in the repo as `WilsonGNS.cauchy_schwarz` (on the actual finite-volume expectation `E`) — a
bona-fide reflection-positivity Schwarz bound at fixed spacing.

**Direction check (decisive).** The Schwarz inequality is an **UPPER** bound on the
off-diagonal (cross-separation) correlator `E(θW_p · W_{p'})`. That is exactly the input that
proves **clustering / spectral decay** — the fixed-spacing `wilsonG_decay`, already PROVED. It
is **not** a lower bound on the one-point condensate `⟨G²⟩`. A lower bound on `⟨G²⟩` is not a
Schwarz consequence at all. So the RP-Schwarz supplies the fixed-spacing decay direction, not a
condensate floor, and not the a→0 uniformity.

Lean (this module, re-exports of PROVED facts):
- `rp_schwinger_holds t ht : ReflectionPositiveSchwinger t ht` — OS2 PSD, all `t ≥ 0`, all real `c`.
- `reflWeight_le_one t ht s : reflWeight t ht s ≤ 1` — diagonal entries `e^{−t·C₂(s)} ∈ [0,1]`.

---

## 2. THE CORRELATION (Griffiths-type) INEQUALITY (task point 2) — fixed-spacing floor, wrong sign for a→0

The character expansion has **nonnegative coefficients** (`coeffW ≥ 0`) — the positive-type /
"ferromagnetic" structure a correlation inequality needs. This gives a genuine first-Griffiths-type
positivity of the vacuum condensate: `⟨1−χ⟩ = plaqActivity ≥` its leading mode
`coeffW w 1 = 2w³ > 0`, a strictly positive rational floor `1/4` at the strong-coupling anchor
`w = 1/2` (PROVED, re-exported):
- `condensate_correlationLower : coeffW w 1 ≤ plaqActivity w (M+1)` (∀ M, `0 ≤ w`).
- `condensate_correlationFloor : 1/4 ≤ plaqActivity anchorW (M+1)`.

**Direction check (decisive).** The second Griffiths inequality
`⟨G²(x)G²(y)⟩ ≥ ⟨G²⟩⟨G²⟩` bounds the **connected** two-point function **below** (`≥ 0`) — the
**wrong sign for clustering** (clustering needs an upper bound on the connected correlator), and it
says nothing forcing the one-point `⟨G²⟩` to stay bounded away from `0` as the coupling flows
`g→0` (`a→0`). The first Griffiths gives `⟨G²⟩ ≥ 0` — nonneg, not a strict spacing-uniform floor.
**Both are perfectly compatible with a massless continuum limit.** (Numerics: `coeffW(1/2,1) =
2·(1/2)³ = 1/4`, `4w³ = 1/2`; exact `sympy`.)

---

## 3. THE DECISIVE CHECK (task point 3) — reflection positivity is GAP-BLIND (the new content)

**Does a reflection-positive quantity that IS spacing-uniform give the continuum condensate?
NO — and the reason is sharp and machine-checked: reflection positivity carries no gap magnitude.**

The OS2 predicate `ReflectionPositiveSchwinger t ht` holds for **every** `t ≥ 0`, including
`t = 0`. At `t = 0` every reflection weight is `e^{−0·C₂(s)} = 1`
(`reflWeight_zero_squeeze`: both `≤ 1` and `≥ 1`), so the reflection form degenerates to the
**identity Gram** `Σ_s c_s²` — a **massless, zero-gap, scale-invariant** theory. A critical /
massless theory is perfectly reflection-positive. Hence:

- `rp_holds_gapless : ReflectionPositiveSchwinger 0 (le 0 0)` — OS2 holds at the gapless point.
- `rp_gap_blind` — packages it: OS2 holds at `t = 0` **and** the form there is the identity Gram.

Therefore an inhabitant of OS2 is **compatible with zero gap**; it cannot distinguish gapped
from gapless, so it cannot yield a positive spacing-uniform floor. That floor is **extra data**.
(mpmath, dps 50: `reflWeight t 1 = e^{−(3/4)t}` runs monotonically `0.223 → 1` as `t: 2 → 0`, i.e.
the leading decay → no decay; the "gap" `1 − reflWeight → 0`.)

Any RP-derived quantity that carries the mass gap (transfer-operator spectral gap, Schwarz
correlation-length ratio) is precisely the reconstructed decay rate, whose a→0 uniformity is the
already-named `UniformPhysicalCorrelationDecay ⟹ singleStep`. There is **no** scale-invariant
reflection-positive quantity that fixes the continuum condensate: scale-invariance is exactly the
gapless point RP also satisfies.

---

## 4. HONEST ASSESSMENT (task point 4) — 8th confirmation, NOT a new construction

**Continuum condensate positivity via RP = `singleStep`.** The continuum `⟨G²⟩ ~ Λ⁴` is
DEFINITIONALLY the same essential singularity `exp(−c/β₀g²) = condensateCReal`
(`continuumCondensate_is_essential_singularity`, `rfl`); its nonzero a→0 generation is
`ContinuumReflectionCondensate = SingleStepDefectBound.singleStep`
(`continuumReflection_is_singleStep`, `rfl`) — the **identical** residual as the OPE / RG / OS
routes (not a parallel object; proved by defeq, Rule 9.8). UNINHABITED.

| object | status | Lean |
|---|---|---|
| OS2 reflection-positivity Schwarz/Gram (all `t ≥ 0`, all real `c`) | **PROVED** (re-export) | `rp_schwinger_holds` ⟵ `reflectionPositiveSchwinger_holds` |
| RP Cauchy–Schwarz `|E(θa·b)|² ≤ E(θa·a)E(θb·b)` | **PROVED** (upstream) | `WilsonGNS.cauchy_schwarz` |
| correlation-inequality (Griffiths-type) **fixed-spacing** condensate floor `1/4` | **PROVED** | `condensate_correlationLower`, `condensate_correlationFloor` |
| **reflection positivity is GAP-BLIND** (OS2 holds at massless `t=0`) | **PROVED (new)** | `rp_gap_blind`, `reflWeight_zero_squeeze` |
| continuum condensate = essential singularity `exp(−c/β₀g²)` | **PROVED identification** (`rfl`) | `continuumCondensate_is_essential_singularity` |
| **spacing-uniform (a→0) condensate positivity** | **OPEN = `singleStep`** | `ContinuumReflectionCondensate := SingleStepDefectBound` (uninhabited) |

**Is the continuum bound constructible from RP + correlation inequalities? NO.** The RP-Schwarz
gives the fixed-spacing clustering (upper bound on cross-correlators, the proved `wilsonG_decay`
direction); the Griffiths-type inequality gives the fixed-spacing condensate floor `1/4`. Neither
survives a→0: RP is gap-blind (holds at the massless point), and the correlation inequalities are
compatible with a massless limit. The spacing-uniform lower bound is the residual `singleStep`.

**Is the tool genuinely different? Yes — genuinely different (OS2 Gram/Schwarz + Griffiths
positivity, distinct from fluctuation defect / string tension / curvature / OPE). Is it more
tractable? No** — and this route adds the *sharpest* insufficiency statement of the eight:
reflection positivity is *provably* gap-blind, so unlike the other framings it cannot even in
principle distinguish the gapped continuum theory it is meant to certify.

---

## 5. Cascade / STOP audit (MANDATORY — this is the mass gap) — NOT tripped

No STOP condition tripped; no guarded bundle inhabited; no cascade. `ContinuumReflectionCondensate`
is a `def` alias of `SingleStepDefectBound`; **no inhabitant is produced.** The module re-exports
PROVED OS2 / condensate facts, PROVES the gap-blindness (`rp_gap_blind`), RESTATES the continuum
condensate positivity as `Type` WITHOUT inhabiting it, and produces
`reflection_condensate_verdict : ReflectionCondensateVerdict` (an informational bundle of PROVED
facts only). It inhabits NONE of the 5 guarded Clay-frontier types (`Tier0Scorecard`,
`UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`) and no unconditional
`SingleStepDefectBound`. STOP-and-exhaustively-audit (triggered only on a cascade to a guarded
bundle) is **not met**.

---

## 6. Build / guard / `#print axioms`

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited
Build completed successfully (725 jobs).
```

All 11 load-bearing decls `#print axioms ⊆ {propext, Quot.sound}` (no `Classical.*`, no `sorryAx`,
no `native_decide`, no `ring`):

```
rp_schwinger_holds                            : [propext, Quot.sound]
reflWeight_le_one                             : [propext, Quot.sound]
condensate_correlationLower                   : [propext, Quot.sound]   ← Griffiths-type fixed-spacing floor
condensate_correlationFloor                   : [propext, Quot.sound]   ← 1/4 at w=1/2
reflWeight_zero_ge_one                        : [propext]               ← reflWeight 0 s ≥ 1
reflWeight_zero_squeeze                        : [propext, Quot.sound]   ← reflWeight 0 s = 1 (identity Gram)
rp_holds_gapless                              : [propext, Quot.sound]   ← OS2 at massless t=0
rp_gap_blind                                  : [propext, Quot.sound]   ← THE decisive insufficiency
continuumReflection_is_singleStep             : [propext, Quot.sound]   ← 8th-confirmation identity (rfl)
continuumCondensate_is_essential_singularity  : [propext, Quot.sound]
reflection_condensate_verdict                 : [propext, Quot.sound]
```

---

## 7. HONEST FINAL VERDICT

**CONSTRUCTED (genuine content):** (i) the OS2 reflection-positivity Schwarz/Gram structure at
every `t ≥ 0` (with the Cauchy–Schwarz already PROVED as `WilsonGNS.cauchy_schwarz`); (ii) the
correlation-inequality (Griffiths-type) FIXED-SPACING condensate lower bound
`⟨1−χ⟩ ≥ coeffW w 1 = 2w³`, floor `1/4`; (iii) **the decisive new INSUFFICIENCY — reflection
positivity is GAP-BLIND** (`rp_gap_blind`): OS2 holds identically at the massless `t = 0` where the
reflection form is the identity Gram, so OS2 cannot furnish a positive spacing-uniform floor.

**RESIDUAL (NOT closed):** the CONTINUUM (a→0) condensate positivity — the same essential
singularity `exp(−c/β₀g²)`, its nonzero generation `= SingleStepDefectBound.singleStep`, the
identical core as the OPE / RG / OS routes.

**So the reflection-positivity / correlation-inequality tool is an EIGHTH independent confirmation
of the same irreducible core `singleStep`** — a genuinely different tool that supplies the
fixed-spacing anchor but is *provably* gap-blind (its own decisive feature), hence does NOT derive
the spacing-uniform continuum condensate. It does **not** give the continuum condensate (no new
construction); it confirms `singleStep`. No guarded frontier bundle is inhabited; nothing is faked;
the 4D Yang–Mills mass gap remains **OPEN**.
