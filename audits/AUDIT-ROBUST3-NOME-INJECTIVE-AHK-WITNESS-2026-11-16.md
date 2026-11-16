# Audit: Robust3NomeInjective, r3Nome strictly increasing and a genuine aHK witness (2026-11-16)

File: `lean/YMGap/RG/Robust3NomeInjective.lean` (211 lines, new; additive). Budget: stop at about 250 lines.
No classical choice is used; no existing statement was changed.

## PROVED
- `ecomp_strict` (:69): E_k < E_{k+1} for every k.
  - `D_step` (:60): D_k + 1/4 ≤ D_{k+1}. This reuses `core` with e3 → e3 + 1/4 (1/100 + 31/100 + 4/17 + 1/4 ≤ 1).
  - `B_low` (:47): B_k ≥ 11/30.
  - `B_mono`.
  - `lt_add_pos` (:35).
  - This strengthens the earlier non-strict `ecomp_mono`, which is left unchanged.
- `r3E_strict` (:83), `r3Gap_strict` (:86) and `one_sub_lt` (:93).
- `r3Nome_step` (:116): the head j < 11 is checked by `decide` (`head_strict`, :114); the tail goes through 1 − r3Gap.
- `r3Nome_strict` (:124): i < j → r3Nome i < r3Nome j.
- `r3Nome_inj` (:138): (r3Nome i).eqv (r3Nome j) → i = j. This is semantic equality; structural equality implies it.

## Constructing aHK without classical choice
- `firstHit w n` (:148) is a fuelled linear search for the first j < n with `(r3Nome j).eqv w`. `Q'.eqv` is decidable
  through `decEq` on Int, so no choice is needed.
- `aHKw w` (:196) runs the search with fuel `4·w.den + 12` and returns 2^{-j} for the hit j, or 1 if there is none.
- `firstHit_nome` (:154): firstHit (r3Nome j) n = if j < n then some j else none. It uses injectivity.
- `bound_ok` (:174): j < 4·(r3Nome j).den + 12 for every j.
  - For j < 11 this is trivial.
  - For the tail, den(1 − r3Gap k) = (r3E k).num, and the existing floor (k+1)/4 ≤ E_k (`r3Floor_le`) gives k+1 ≤ 4·num.
- `aHKw_nome` (:201): aHKw (r3Nome j) = 2^{-j}.
- `aHKw_hyps` (:207): `hposHK aHKw ∧ hspacingHK_win aHKw lo hi ∧ hspacingHK_off aHKw lo hi`, for all lo and hi.

## What the witness covers
- Covered: only the spacing and positivity hypotheses of `robust3_spacing_bound_HK` and
  `robust3_physical_floor_noMargin_HK` (SpacingHeatKernel:68/:75).
- Not covered: hcross, hafδ, hupper, hschur and the Phi/D/width/delta data stay OPEN and unwitnessed.
- aHKw is a toy function (ℓ = 1 at every step), not the heat-kernel string tension. The window clause for the
  physical a(w) is supported only by Monte Carlo (task2k), which is not proof.

## Checks
- Build: direct `lean -M 6144`, rc 0, zero warnings. 1.0 s wall, 1.0 s user CPU, 0.3 s sys, peak RSS 1711 MiB, min MemAvailable 12661 MiB.
- Axiom check: 0.8 s, 0.5 s user CPU, peak RSS 1665 MiB. Temp file, deleted.
  - `bound_ok`: [propext].
  - `ecomp_strict`, `r3Nome_strict`, `r3Nome_inj`, `firstHit_nome`, `aHKw_nome` and `aHKw_hyps`: [propext, Quot.sound].
- None of sorry, admit, Classical, native_decide, omega, simpa or grind appear.

**δ_min = 0 is only a necessary condition.** Build caveat: direct lean against copied oleans, not lake-verified
(stale-trace caveat). No chart closure is claimed.
