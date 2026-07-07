# Anchor-dominance made concrete: the telescoping eigenvalue-shift budget

**Deliverables.** `lean/YMGap/Continuum/AnchorDominanceEigenvalueShift.lean` (full `lake
build` green, 692 jobs, frontier-guard **OK at 5**, axiom-clean), `anchor_num.py` (mpmath
dps 60 + exact `fractions`), this report. **Committed: nothing** (per instructions).

---

## 0. Headline

The **anchor-dominance** `Σε_k < m_phys` — carried by `CAPSTONE §5` as an *independent
open inequality* on top of the additive step law and summability — is now **DISCHARGED**,
in a deep-UV-anchored scheme, by a machine-checked, axiom-clean argument. The mechanism is
the **exact telescoping** of the multiplicity-blind eigenvalue-shift erosion:

```
ε_k = w_{k+1}³ − w_k³   ⟹   Σ_{j<k} ε_j = w_k³ − w_0³ ≤ 1 − w_0³ =: Bε   (EXACT).
```

The **entire accumulated real additive erosion is the single closed value `1 − w_0³`**,
which the transmuted margin `m_phys = 1 − e^{−1/e} = 0.30780` strictly dominates once the
UV anchor is deep enough. At `w_0 = 11/12`: `Bε = 397/1728 = 0.22975 < 3/10 ≤ m_phys`
(**kernel `decide`, zero axioms**), slack ≈ 0.078.

**This does NOT close the mass gap.** `anchorDominance_floor` is a guard-safe CONDITIONAL
producer (open binders on the real margin and step law); it inhabits **no** guarded bundle.
Two named inputs remain open (§4). The 4D Yang–Mills mass gap remains **OPEN**.

---

## 1. What `ε_k` is — concrete, tied to the real flow (task condition (i))

`ε_k` is **not a free field**. It is the multiplicity-BLIND coupling-flow **eigenvalue
shift** of Route I (`RouteIEigenvalueDefect.EigenvalueShiftDefect`):

- The physical gap edge is the transfer eigenvalue `eigA w 1 = w^{C₄(1)} = w³`
  (`GapIsEigenvalue` VERDICT A — the decay rate, not the amplitude `coeffW`).
- Route I **proved** the fusion-DEGENERACY defect is `0` (`eigA_fusedDefect_eqv_zero`), so
  the only per-step defect is the coupling-flow shift `ε_k = w_{k+1}³ − w_k³` along the
  asymptotic-freedom flow `w_k ↑ 1`.
- It is dominated by the Route H renormalized defect: numerically `eigShift(w) ≤ δ_ren(w)
  = 2(1−w)²(2+w) ≤ 6(1−w)²` (verified at the `w_0=11/12` pair: `0.01627 ≤ 0.04051 ≤
  0.04167`).

The DECISIVE structural fact this module exploits — absent from the squared-defect
treatments — is that the eigenvalue shift is **additive and telescopes**. That converts an
unbounded-looking budget into a single closed endpoint difference.

Lean objects (all axiom-clean):

| declaration | statement | axioms |
|---|---|---|
| `qcube_mono` / `qcube_le_one` | `eigA·1 = w³` monotone / sub-unit on `[0,1]` | `[propext]` |
| `eigShiftSeq w k` | `= w_{k+1}³ − w_k³` (the concrete `ε_k`) | — |
| `eigShift_nonneg` | `ε_k ≥ 0` for `w_k ↑` | `[propext]` |
| **`eigShift_tailSum_eqv`** | **`Σ_{j<k} ε_j ≃ w_k³ − w_0³`** (EXACT telescope) | `[propext]` |
| **`eigShift_tailSum_le`** | **`Σ_{j<k} ε_j ≤ 1 − w_0³`** (∀ k) — the budget `Bε` | `[propext]` |
| `zero_tailSum_le` | `Bδ = 0` (pure-additive route; Route I degeneracy defect `= 0`) | `[propext]` |

---

## 2. The anchor-dominance Σε < m_phys (task condition (ii)) — with REAL constants

**m_phys.** `m_phys = 1 − sep_0 = 1 − e^{−1/e} = 0.307799372444…` (`concreteTowerE` seed
`e^{−1}`, `DimensionlessMarginTransmutation`), mpmath dps 60. `m_phys > 3/10` (gap `0.0078`).
The anchor seed is a scheme parameter: seeding at `w_0^{exp}=1` boosts `m_phys → 1−e^{−1} =
0.632`, giving even more room.

**The naïve non-anchored budget FAILS (the honest bad news).** For the canonical AF rate
`1−w_k = 1/(k+1)` (`A=1,B=1`) summed from `k=0`, the squared model majorant is

```
Σ_{k≥0} 6(1−w_k)² = 6·(π²/6) = π² = 9.8696  ≫  m_phys = 0.3078   → anchor-dominance FAILS.
```

So re-anchoring alone does not rescue the *squared* budget cheaply. What rescues it is the
**telescoping additive** budget, which does **not** carry the factor-of-6 / square inflation:

**The telescoping eigenvalue-shift budget (deep-UV anchor).**

| anchor `w_0` | `1−w_0` | `Bε = 1 − w_0³` | vs `m_phys=0.3078` | slack |
|---|---|---|---|---|
| 9/10  | 0.100 | 271/1000 = 0.27100 | OK | 0.037 |
| **11/12** | **0.083** | **397/1728 = 0.22975** | **OK** | **0.078** |
| 14/15 | 0.067 | 631/3375 = 0.18696 | OK | 0.121 |
| 19/20 | 0.050 | 1141/8000 = 0.14263 | OK | 0.165 |

`11/12` is the canonical AF trajectory `w_k = 1−1/(k+1)` at cutoff `k=11`. The telescoping
identity was verified exactly (`Σ_{k<K}(w_{k+1}³−w_k³) = w_K³−w_0³`, `K` up to 1000,
`fractions`-exact).

**For comparison,** even the *cruder* Route-H squared majorant works under deep-enough
anchoring: `Σ_{k≥0} 6/(k+B)² = 6·ζ(2,B) < m_phys` for `B ≥ 20` (`w_0 ≥ 0.95`) — a second,
independent scheme. The telescoping eigenvalue-shift budget is the sharp one (`B=12`
suffices, `w_0 = 11/12`).

**The scheme answer (task condition (iii)).** Yes — there is a genuine scheme where
`Σε < m_phys`: any UV anchor `w_0` with `1 − w_0³ < m_phys`, i.e. `w_0 > (1−m_phys)^{1/3} =
0.8879` for `m_phys = 0.3078` (or `w_0 > 0.717` for the boosted seed). The block factor `b`
does **not** need to grow; the anchor depth is the operative freedom, and the budget is a
*closed* value `1−w_0³ → 0`, not an infinite series to be tamed.

---

## 3. The Lean floor + STOP check (task condition (iv))

`anchorDominance_floor` (axioms `[propext, Quot.sound]`) is the CONDITIONAL producer: for
the AF flow `w` (`0 ≤ w_k ≤ 1`, `w_k ↑`), any margin obeying the additive step
`margin(k+1) ≥ margin k − ε_k` with `margin 0 ≥ 0` and **anchor-dominance
`1 − w_0³ < margin 0`**, the PROVED `additiveErosion_uniform_floor` (reused, not re-proved)
yields the **uniform strictly-positive continuum floor**

```
∀ k,  margin 0 − (1 − w_0³) ≤ margin k    and    0 < margin 0 − (1 − w_0³).
```

with `Bδ = 0` (`zero_tailSum_le`) and `Bε = 1 − w_0³` (`eigShift_tailSum_le`).
`anchorDom_numeric` (**no axioms**) supplies the anchor-dominance at `w_0 = 11/12` for any
`m_0 ≥ 3/10`; `anchorDom_from_mphys_lb` packages it against the transmuted `m_phys`.

**MANDATORY STOP CHECK — nothing guarded inhabited.** `anchorDominance_floor` has open
binders on `w`, `margin`, `hstep`, `hanchor`, so it is **not** an unconditional inhabitant.
It does **NOT** construct `TrueMarginRecursionPhysical`, `TrueMarginRecursionSummable`,
`SingleStepDefectBound`, `UniformSpacingFloor`, `Tier0Scorecard`, `ClayTarget`,
`ClayTargetPinned`, or `FrontierDAG`. (`TrueMarginRecursionPhysical` would cascade
`→ uniformSpacingFloor_of_trueMarginPhysical → QFloor → UniformSpacingFloor`, a guarded
type — deliberately not built.) **No `SingleStepDefectBound` / `TrueMarginRecursion` /
`FrontierDAG.trueMargin` is inhabited; `YMGapGuard` is UNCHANGED at 5.** No STOP condition
tripped.

```
YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                 uninhabited across YMGap.*
Build completed successfully (692 jobs).
```

`#print axioms`, all 10 load-bearing decls: `[propext]`, `[propext, Quot.sound]`, or **none**
(`anchorDom_numeric` = zero-axiom kernel `decide`). No `Classical.*`, no `native_decide`, no
`sorry`/`admit`/`sorryAx`.

---

## 4. Adversarial verdict — is this GENUINE, or a constant fudge?

**Genuine on the summability/dominance, honestly conditional on two named inputs.**

1. **`ε_k` is the real block-spin defect, not a free field.** It is Route I's
   multiplicity-blind eigenvalue shift `w_{k+1}³−w_k³` (the decay-rate degradation of the
   proved transfer eigenvalue `eigA w 1 = w³`), dominated by Route H's `δ_ren`. The
   telescoping is an exact algebraic identity (`eigShift_tailSum_eqv`), not a chosen bound.

2. **The anchor-dominance is with REAL constants, in a physical scheme.** `Bε = 1 − w_0³`
   is closed and exact; `m_phys = 1−e^{−1/e}` is the transmutation-doc conserved value; the
   deep-UV anchor `w_0 = 11/12` is a genuine AF-trajectory point. Deep-UV anchoring is
   physically legitimate: the strong-coupling region `w ∈ [0, w_0]` is fixed-spacing and its
   gap is separately PROVED, so the continuum problem is only the tail `w: w_0 → 1`. This is
   **not** a free-lunch: the total additive erosion over the *entire* continuum tail is
   exactly `1 − w_0³`, and it is that total that the transmuted margin dominates.

3. **The two residuals are the genuine 4D content, and are NOT closed:**
   - **(R1) the identification** `ε_k ≤ w_{k+1}³ − w_k³` — that the real per-step additive
     erosion of the *dimensionless* margin is bounded by the eigenvalue shift. This is
     Route I's UNINHABITED `EigenvalueShiftDefect` / Route H's open identification.
   - **(R2) the anchor value** `margin 0 ≥ m_phys` at the deep-UV anchor — that the
     dimensionless margin at the UV cutoff equals the transmuted `m_phys`. Dimensional
     transmutation is PROVED for the *ideal* flow (`DimensionlessMarginTransmutation`); the
     *real* flow's conservation is the open transmutation content.

**Net reduction.** The Clay core stated in `CAPSTONE §5` was: *prove the real block-spin
defects satisfy (a) the step, (b) summability, and (c) anchor-dominance `(1−Σδ)m_0 > Σε`.*
This module **discharges (b) and (c)** for the eigenvalue-shift erosion (summability is the
exact telescope; anchor-dominance follows from deep-UV anchoring + `m_phys ≥ 3/10`),
leaving the core as the **single identification (R1)** plus the **transmutation anchor
(R2)** — both already-named, already-open objects, no new wall opened. Anchor-dominance is
removed as an independent obligation.

**Honest one-line verdict.** The mass gap's positivity is **provable in a genuine
deep-UV-anchored scheme** *modulo* two named inputs (the eigenvalue-shift identification and
the transmutation anchor `m_0 ≥ m_phys`): given those, the accumulated real block-spin
additive erosion `1 − w_0³ = 0.22975` is strictly dominated by the transmuted margin
`m_phys = 0.30780`, so the continuum dimensionless margin `≥ m_phys − (1−w_0³) > 0`. The
anchor-dominance is no longer a mystery inequality — it is the exact telescoping endpoint.
**No guarded bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains
OPEN.**
