# The FIELD-SPACE renormalized construction at w→1 — the physical single-step contraction ρ_phys, and whether ρ_phys<1 is constructible or the residual is the foundational Bałaban RG

**Deliverable.** `lean/YMGap/Continuum/FieldSpaceRenormalized.lean` (wired into `YMGap.lean`).
Full `lake build` green = **727 jobs**; `YMGapGuard` **frontier-guard OK = 5** Clay-frontier
types still unconditionally uninhabited; all 10 load-bearing declarations axiom-clean
(`[propext, Quot.sound]`); no `sorry`/`native_decide`/`Classical`. Numerics `num.py`
(mpmath dps 50, sympy exact). Commits: none (per instruction).

---

## 0. The obligation (the genuine continuum frontier)

The mass gap lives at `w → 1` (`a → 0`), OUTSIDE the character radius `w* = 2^{−1/3}`.
The nine confirmation routes pinpoint the dichotomy:

- the **character basis** (`SimonLiebCorrelation`) controls STRONG coupling `w ≤ w*` and
  DIVERGES at `w → 1`: single-step correlation `ρ = 2w³ → 2 > 1`, radius `w* = 2^{−1/3}`;
- the **field-space basis** (`FieldSpaceCluster`, `g² ∼ (1−w) → 0`) CONVERGES there but is
  UNDERDETERMINED (`field_beats_char_at_weak`).

The continuum construction MUST use the field-space/renormalized description. Build the
field-space physical single-step contraction `ρ_phys` at `w → 1` and decide EXACTLY: is
`ρ_phys < 1` (the mass gap) constructible, or is the determination the open `singleStep`?

---

## 1. Numeric validation (`num.py`, mpmath dps 50, sympy exact)

- **Crossover** `w* = 2^{−1/3} = 0.7937005259840997…`, and `2·(w*)³ = 1.0` exactly (sympy):
  the character single-step correlation crosses 1 precisely at `w*`.
- **`g²` bracket** `(1−w) ≤ −log w ≤ (1−w)/w` for all `w∈(0,1)`, e.g. `w=0.99`:
  `0.0100 ≤ 0.010050 ≤ 0.010101`. So `g² ∼ (1−w)` as `w→1`.
- **Inversion** at `w=9/10`: field activity `1−w = 0.1`, character activity `2w³ = 1.458`.
- **UV summability** `Σ_k 6(1−w_k)²` with `w_k = 1−1/(k+1)` → `6ζ(2) = π² = 9.8696…`
  (200k-term partial sum `9.86957…`).
- **Dimensional transmutation (scalar)**: with per-step model defect `δ_k ≤ 6/(k+B)² → 0`,
  the accumulated product `∏_{k}(1 − 6/(k+B)²)` (B=4, 500k terms) = `0.15398… > 0` — a
  vanishing per-step contraction WITH a strictly positive accumulated floor.
- **Field=char crossover** (real root of `2w³+w−1`) at `w = 0.589754…` (sympy `nroots`),
  matching the doc.

---

## 2. The physics, made precise (dimensional transmutation at the scalar level)

The AF makes `g² ∼ (1−w_k) → 0` in the deep UV (`k→∞`). The field-space per-step defect
(renormalized transverse second cumulant) VANISHES: `δ_model,k ≤ 6(1−w_k)² → 0`. So the
per-step physical contraction vanishes at the UV fixed point — NO gap per lattice step in
lattice units (correlation length diverges in lattice units, as it must at a UV FP).

The mass gap is an IR property. The physical contraction over one PHYSICAL correlation
length is the ACCUMULATED product `∏_{i<k}(1 − δ_model,i)`. Dimensional transmutation is
the statement that although each factor `→ 1`, the accumulated product stays BOUNDED AWAY
FROM ZERO: `≥ ε > 0` uniformly in `k`. Vanishing per-step contraction + positive
accumulated floor = the physical gap the flow generates.

---

## 3. What is PROVED in Lean-core (`FieldSpaceRenormalized.lean`, all axiom-clean)

| declaration | content | axioms |
|---|---|---|
| `physDefect`, `physSurvival`, `accumContraction` | field-space per-step objects (`δ_model`, `1−δ_model`, `∏(1−δ_model)`) | — |
| `physDefect_le_gFourth` | per-step contraction `O(g⁴)`: `δ_model,k ≤ 6(1−w_k)²` (→0 in UV) | propext, Quot.sound |
| `physSurvival_nonneg` / `physSurvival_le_one` | survival factor `1−δ_model,k ∈ [0,1]` | propext, Quot.sound |
| **`model_physContraction_floor`** | **MODEL physical contraction UNIFORM**: `0 < afFloorEps ∧ ∀k, afFloorEps ≤ ∏(1−δ_model,i)` — `ρ_phys(model) < 1` uniformly | propext, Quot.sound |
| **`dimensional_transmutation_scalar`** | vanishing per-step contraction (`≤6(1−w_k)²`) + positive accumulated floor (`≥ε>0`), PROVED for the model | propext, Quot.sound |
| `fieldSpace_model_certificate` | from convergent field-space scalar data alone: cluster convergence AND model floor (no physical input) | propext, Quot.sound |
| `physContraction_is_singleStep` | `FieldSpacePhysicalContraction = SingleStepDefectBound` (`rfl`, Rule 9.8) | propext, Quot.sound |
| `physFloor_of_physContraction` | GIVEN the physical contraction (=singleStep), the true margin has the positive continuum floor | propext, Quot.sound |
| `physFloor_of_convergence_and_physContraction` | convergence + physical contraction ⟹ true-margin floor + cluster bound (P load-bearing) | propext, Quot.sound |
| `fieldSpace_renormalized_verdict` | informational bundle of PROVED facts; inhabits no frontier bundle | propext, Quot.sound |

Reuses PROVED `afEffect_le_gFourth`, `afFloorEps_pos`, `afFloorEps_le_afPhysGapSeq`,
`afDefectSeq_nonneg/le_one`, `fieldConvergence_sum_bounded`, `fullFloor_of_singleStep`.

---

## 4. THE DECISIVE CHECK — is ρ_phys<1 constructible, or is it singleStep?

**The MODEL contraction IS constructible and uniform (genuine new piece).**
`model_physContraction_floor` proves UNCONDITIONALLY that the accumulated field-space MODEL
contraction complement `∏_{i<k}(1 − δ_model,i)` stays `≥ afFloorEps > 0` for all `k`. So the
field-space renormalized flow DOES generate a uniform physical contraction `ρ_phys < 1` —
**for the MODEL transverse defect `δ_model`.** This is the constructive scalar core of
dimensional transmutation: the per-step contraction vanishes in the UV (`O(g⁴)`) yet the
accumulated product has a positive floor.

**The REAL physical contraction is NOT constructible from the convergent scalar series —
it IS `singleStep`.** The model floor bounds `∏(1−δ_model)`, the product of the MODEL
survival factors. The PHYSICAL mass gap is a floor on the TRUE dimensionless margin
`trueMargin k = m_lat(a_k)/a_k`, and the true margin tracks the model ONLY IF

    (1 − δ_model,k)·trueMargin_k ≤ trueMargin_{k+1}     (realδ_k ≤ δ_model,k),

which is EXACTLY `SingleStepDefectBound.singleStep`. Formalized:
`FieldSpacePhysicalContraction := SingleStepDefectBound` (PROVED identity `rfl`, Rule 9.8),
UNINHABITED; `physFloor_of_physContraction` shows it WOULD give the full continuum floor.

**The underdetermination, machine-precise.** `fieldSpace_model_certificate` produces — from
`FieldClusterConvergence afr` ALONE — BOTH the cluster-sum convergence AND the model
contraction floor, with NO input about the real interacting flow ("the field-space
converges"). The physical floor needs the STRICTLY LARGER input
`FieldSpacePhysicalContraction = singleStep`
(`physFloor_of_convergence_and_physContraction`, where `P` is load-bearing). The convergent
scalar series fixes the MODEL contraction but NOT the real one — "but underdetermined." The
determination `realδ ≤ δ_model` is the open Bałaban RG datum.

---

## 5. HONEST FOUNDATIONAL ASSESSMENT

- **Is the field-space basis the genuine continuum? YES (proved).** Character diverges at
  `w→1` (`ρ=2w³→2`, radius `w*=2^{−1/3}`); field-space converges there (`g²∼(1−w)→0`). The
  mass gap lives outside the character radius, so the renormalized/field-space description
  is mandatory.

- **What genuine NEW piece is built?** The uniform MODEL physical contraction floor
  `∏(1−δ_model,i) ≥ ε > 0` (`ρ_phys(model)<1` uniformly), plus the machine-checked scalar
  dimensional-transmutation signature (per-step contraction `→0` in the UV yet a positive
  accumulated floor). Previously the field-space work (`FieldSpaceCluster`) proved the
  scalar cluster CONVERGENCE and the `O(g⁴)` effect; this module builds the physical
  CONTRACTION object `ρ_phys` on top of it and proves the model contraction is uniform, and
  identifies the real contraction with `singleStep` by `rfl`.

- **Is `S_eff` (the renormalized effective action with `ρ_phys<1`) constructible from the
  proved pieces, or the foundational input?** **Foundational input.** The field-space
  scalar series converges (proved) but is underdetermined (proved): it determines the MODEL
  contraction, not the real one. The real renormalized effective action requires the
  configuration-space Gaussian measure and the connected Ursell amplitudes
  `|z_n(w)| ≤ (μg²)^n` (a NEW SUBSTRATE the character-basis library lacks — the honest
  residual already named `FieldClusterConvergence.inducedBound`), and the per-step
  determination `realδ_k ≤ δ_model,k` (`singleStep`). Neither is constructible from the
  convergent scalar series; both are the decades-of-work non-perturbative Bałaban RG.

---

## 6. Build / guard / axioms (honesty gate)

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (727 jobs).
```

- `#print axioms` on all 10 load-bearing declarations: `[propext, Quot.sound]`. No
  `Classical.*`, no `sorryAx`, no `native_decide`, no `sorry`/`admit` (banned tokens appear
  only in prose docstrings).
- Frontier guard count UNCHANGED at 5. `FieldSpacePhysicalContraction := SingleStepDefectBound`
  is a def-alias (exactly as `SimonLiebCorrelation.ContinuumSimonLieb`), NOT one of the 5
  guarded frontier types; it is UNINHABITED. All producers take `P` / `singleStep` as an
  open hypothesis — no unconditional inhabitant, no cascade to a guarded bundle.

**No STOP condition tripped.** ρ_phys<1 is NOT constructed for the real flow; only the
MODEL contraction floor is proved (unconditional), and the real physical contraction is
identified with the open `singleStep`.

---

## 7. HONEST VERDICT — feasible or the foundational Clay input?

**The field-space continuum construction gives ρ_phys<1 for the MODEL flow (constructible,
PROVED uniform), NOT for the real flow. The determination of the real physical contraction
is the residual = `singleStep` = the foundational Bałaban RG.**

- The field-space renormalized flow genuinely produces a uniform physical contraction
  `ρ_phys(model) < 1` (positive accumulated floor `∏(1−δ_model)≥ε>0`) with the vanishing-
  per-step / positive-accumulated dimensional-transmutation signature — a genuine new
  machine-checked piece.
- The field-space scalar series CONVERGES at `w→1` (proved) but is UNDERDETERMINED (proved):
  it fixes the model contraction, not the real one. A convergent-but-underdetermined
  field-space measure is NOT the gap.
- The real physical contraction `ρ_phys<1` (⟹ the mass gap) IS `singleStep`
  (`realδ_k ≤ δ_model,k`), the foundational non-perturbative Bałaban RG input — not
  constructible from the convergent scalar series, and requiring the configuration-space
  Gaussian measure the library lacks.

This is the TENTH independent confirmation of the same irreducible core `singleStep`, in
field-space renormalized form. No guarded frontier bundle is inhabited; nothing is faked; no
free-field `δ:=0` dodge is used; the 4D Yang–Mills mass gap remains **OPEN**. The single open
front is the physical contraction `ρ_phys<1` = `SingleStepDefectBound.singleStep` = the
field-space renormalized effective action, the foundational Bałaban RG.
```
