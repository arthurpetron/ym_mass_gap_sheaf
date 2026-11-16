# SCOPE: stating `hspacing` for the window j6–8 directly on the heat-kernel string tension a(w) (2026-11-16)

Docs only. No implementation. The repo was read at b69d27d9.

## 1. Where hspacing enters today
Finding: in Lean, hspacing is **not** routed through a coupling map. It is a hypothesis on an abstract,
unconstrained sequence `a : Nat → Q'`:
- `RG/UndershootPhysicalUnits.lean:92` `spacing_bound (a rho om) … (hspacing : ∀ i, 2·a(i+1) ≤ rho i · a i)` and
  `:110` `floor_physical`. These are the generic reductions.
- `RG/Robust3UndershootPhysicalUnits.lean:60–61` `robust3_spacing_bound (a) (ha) (hspacing_OPEN : ∀ i,
  Q'.ofNat 2 * a (i+1) ≤ r3Rho i * a i)`, giving 2ⁿ·a_n ≤ P₃·a_0.
  - `r3Rho := r2Rho` (:38).
  - `r3P` (:50) and `r3P_value` (:53) depend only on ρ/ω.
- `RG/Robust3UndershootCrossoverInstance.lean:137` `robust3_physical_floor`, binder `_hspacing_OPEN` at :156.
- `RG/Robust3MarginDischarge.lean:99` `robust3_physical_floor_noMargin`, binder at :118.
- ρ values: `RG/Robust2UndershootPhysicalUnits.lean:40–51` `r2RhoTab`.
  - 6 ↦ 36/25 (:47), 7 ↦ 33/25 (:48), 8 ↦ 63/50 (:49), 9 ↦ 61/50 (:50).
  - Tail `r2RhoTail` at :70; dispatch `r2Rho` at :77.
- Nomes: `RG/Robust3UndershootAfSchedule.lean:43` `r3Tab` (6 ↦ 779/1000, 7 ↦ 794701/1e6, 8 ↦ 808737/1e6,
  9 ↦ 32873/40000 = 0.821825) and `:201` `r3Nome`.
- **The map appears only in prose and in how ρ was chosen.**
  - The `Robust3UndershootPhysicalUnits.lean:18–21` docstring cites the naive 3L(−q) model for the tail spacing ratio.
  - The head ρ6/ρ7 were set from map-based ℓ estimates (task2g/task2i numerics).
- **Gap in the current interface.** Nothing ties `a` to the nome schedule or to a string tension. The theorems hold for
  every `a` satisfying the hypothesis; for example `a ≡ 0` satisfies it trivially, given `ha`. So what "a is the
  physical lattice spacing" means is purely documentary.

## 2. A possible new interface (additive)
A new file, for example `RG/Robust3SpacingHeatKernel.lean`, importing `Robust3MarginDischarge` and nothing more:
```lean
/-- Abstract heat-kernel string tension a(w) (lattice units, a√σ at nome w). OPEN physics object. -/
-- parameter `aHK : Q' → Q'`, with `haHK : ∀ i, 0 ≤ aHK (r3Nome i)`
def hspacingHK_window (aHK : Q' → Q') : Prop :=
  ∀ j, 6 ≤ j → j ≤ 8 → Q'.ofNat 2 * aHK (r3Nome (j+1)) ≤ r3Rho j * aHK (r3Nome j)
def hspacingHK_offWindow (aHK : Q' → Q') : Prop :=
  ∀ i, (i < 6 ∨ 8 < i) → Q'.ofNat 2 * aHK (r3Nome (i+1)) ≤ r3Rho i * aHK (r3Nome i)
theorem hspacing_of_HK : hspacingHK_window aHK → hspacingHK_offWindow aHK →
    ∀ i, Q'.ofNat 2 * (fun i => aHK (r3Nome i)) (i+1) ≤ r3Rho i * (fun i => aHK (r3Nome i)) i
theorem robust3_spacing_bound_HK … := robust3_spacing_bound (fun i => aHK (r3Nome i)) … (hspacing_of_HK …)
theorem robust3_physical_floor_noMargin_HK … -- same binders as :99, with a := aHK ∘ r3Nome
```
- **Proof content:** a case split on i (window or not) plus instantiation. No new analysis is needed.
- **What it gains:** the window hypothesis is stated at the actual Lean nomes w6…w9 for one function a(w). That is
  exactly what task2k measures (ℓ_j = log2(a(w_j)/a(w_{j+1})) ≥ 1 − log2 ρ_j). The off-window part stays a separate
  named OPEN hypothesis (strong coupling for i < 6; AF tail for i ≥ 9, or i ≥ 11 for the analytic tail).
- **Optional refinement:** split off-window into head (i < 6), the data window (9 ≤ i ≤ 10) and the tail (i ≥ 11), to
  match the numerics' evidence classes.

## 3. Additivity
Yes. The new theorems are specialisations (a := aHK ∘ r3Nome) of the existing ones, so no existing statement changes,
and r3Rho, r3P and r3Nome are reused unchanged. Compatibility with the existing generic statements is immediate,
since they quantify over all `a`.

## 4. Estimated size
About 80–140 Lean lines plus an audit:
- definitions: ~15;
- the case split: ~25;
- two or three instantiations: ~40–80, mostly restating the long `robust3_physical_floor` binders.

This is a single commit, well under 400 lines.

## 5. Interaction with P′ and physical units
- **Physical units.** P₃ = ω_0 ≈ 81.92 depends only on ρ, so it is unchanged. The conclusion becomes
  2ⁿ·aHK(r3Nome n) ≤ P₃·aHK(r3Nome 0), which is the physical-units statement with a now explicitly a(w) on the schedule.
- **P′.** P′ is a numerics-side path quantity (P′ minimum slack = min_j (ℓ_j − ℓ_min,j) along the schedule); it is not a Lean
  object. Under the HK interface, the window part of P′ is exactly the slack of `hspacingHK_window`.
  - task2k gives +0.204 (j6) and +0.077 (j7) for the primary estimator.
  - Because ρ is unchanged, P′'s ℓ_min thresholds (0.4739, 0.5995, 0.667) are unchanged.

## 6. Blockers and open points
- **No Lean blocker** for the interface itself.
- **j8 evidence.** j8 is in the window but has no direct heat-kernel measurement (w9 at L12 is unreliable; L ≥ 20–24 is
  pending). Until that run exists, the j8 clause rests on literature Wilson-map models, so it is map-based again.
  Option: state the window as j6–7 only and leave j8 in off-window, until Numerics reports.
- **aHK stays abstract.** There is no Lean definition of the heat-kernel string tension, or of its link to the transfer
  matrix or measure. Defining it is a large new analysis interface and out of scope; the new hypothesis is OPEN
  physics input, like `hspacing_OPEN`.
- **Interpretation risk.** Because the existing theorems quantify over arbitrary `a`, the HK version adds meaning
  (documented binding to nomes), not mathematical strength. Audits must say so.

Caveats: MC support for the window is evidence, not proof. δ_min = 0 is only necessary. No chart closure is claimed.
Any future Lean work: direct lean against copied oleans, not lake-verified.
