# Audit: Robust3SpacingHeatKernel, hspacing on the heat-kernel a(w) at the Lean nomes (window j6–7) (2026-11-16)

File: `lean/YMGap/RG/Robust3SpacingHeatKernel.lean` (156 lines, new; additive). It implements
SCOPE-HSPACING-HEAT-KERNEL-WINDOW-2026-11-16.md.
- Budget: about 80–140 lines, with a stop at about 250. The definitions and HK theorems take 104 lines; the non-vacuity part takes about 50.
- No existing statement was changed.

## Definitions
- `hspacingHK_win aHK lo hi` (:39): for every j with lo ≤ j ≤ hi, 2·aHK(r3Nome(j+1)) ≤ r3Rho j · aHK(r3Nome j).
- `hspacingHK_off aHK lo hi` (:43): the same inequality for j < lo ∨ hi < j. **OPEN.**
- `hposHK aHK` (:47): 0 < aHK(r3Nome j) for every j. This rules out the vacuous a ≡ 0.
- `hspacingHK_window aHK := hspacingHK_win aHK 6 7` (:50): the current MC-supported window.
- **Extension point for j8.** Every theorem is generic in `lo hi`. Once Numerics reports w9, use `lo hi = 6 8`; no new
  theorem is needed. The note is in the module docstring.

## PROVED (reductions; the hypotheses stay OPEN)
- `hspacing_of_HK` (:53): window + off-window imply the existing `hspacing_OPEN` for a := aHK ∘ r3Nome.
- `robust3_spacing_bound_HK` (:68): 2ⁿ·aHK(w_n) ≤ P₃·aHK(w_0), with P₃ ≈ 81.92 unchanged.
- `robust3_physical_floor_noMargin_HK` (:75): `robust3_physical_floor_noMargin` (MarginDischarge:99) with a := aHK ∘ r3Nome.
  - Binders: `_hpos`, `_hwin_MC` and `_hoff_OPEN`, with ha derived from positivity.
  - Still OPEN and unchanged: `hcross_OPEN`, `hafδ_OPEN`, `hupper_OPEN` and `hschur_OPEN`, plus the `Phi`/`D`/`width`/`delta` data.
- `rho_ge_one` (:105): 1 ≤ ρ_i for all i. The head is checked by `decide` over i < 11; the tail uses
  (k+4)(k+18) ≤ (k+17)(k+5).

## Non-vacuity: exactly what is covered
- `spacing_nonvacuous` (:129): the concrete sequence a_j = 2^{-j} (`aSeq`, :125) satisfies 0 < a_j and
  2·a_{j+1} ≤ ρ_j·a_j for **every** j, window and off-window.
- `HK_hyps_of_seq` (:149): any aHK with aHK(r3Nome j) = 2^{-j} satisfies `hposHK`, `hspacingHK_win` and `hspacingHK_off`,
  for every lo and hi.
- **Covered:** the spacing and positivity hypotheses (window, off-window and positivity, plus the derived nonnegativity).
- **Not covered:**
  - The existence of a function aHK : Q' → Q' with aHK ∘ r3Nome = 2^{-j}. That needs r3Nome injective, which is not proved
    here. The witness is at the sequence level, which is the level the reductions use.
  - `hcross_OPEN`, `hafδ_OPEN`, `hupper_OPEN`, `hschur_OPEN` and the Phi/D/width/delta data are not witnessed.
- So `robust3_physical_floor_noMargin_HK` is NOT shown non-vacuous as a whole.
- The witness 2^{-j} (ℓ = 1 everywhere) is a toy sequence, not the physical heat-kernel string tension.

## What is weaker or unchanged
- aHK is an abstract function, an OPEN physics object; there is no Lean definition of the heat-kernel string tension.
- The window clause is supported only by Monte Carlo: Numerics task2k gives ℓ6 = 0.678±0.018 and ℓ7 = 0.676±0.018
  directly at the Lean nomes. **MC is evidence, not proof.**
- j8 is in the off-window hypothesis for now, pending w9 at L ≥ 20–24.
- The HK theorems are specialisations of the existing ones. They add the binding of a to the nome schedule and a
  positivity requirement, not new mathematical strength.

## Checks
- Build: direct `lean -M 6144`, rc 0, zero warnings. 1.0 s wall, 0.8 s user CPU, 0.2 s sys, peak RSS 1701 MiB, min MemAvailable 12741 MiB.
- Axiom check: 1.1 s, 0.8 s user CPU, peak RSS 1668 MiB. Temp file, deleted.
  - `hspacing_of_HK` and `rho_ge_one`: [propext].
  - `robust3_spacing_bound_HK`, `robust3_physical_floor_noMargin_HK`, `spacing_nonvacuous` and `HK_hyps_of_seq`: [propext, Quot.sound].
- None of sorry, admit, Classical, native_decide, omega, simpa or grind appear. One Nat side goal uses `simp +arith`.

**δ_min = 0 is only a necessary condition: it removes the obstruction but does not prove hafδ.**

**Build caveat:** direct lean against copied oleans, not lake-verified (stale-trace caveat). No chart closure is claimed.

U(1) note: the window w ≈ 0.78–0.80 lies far above 1/8. Per the standing note, a uniform gap there would NOT hold for
U(1), so it is genuine non-abelian content (not proved).
