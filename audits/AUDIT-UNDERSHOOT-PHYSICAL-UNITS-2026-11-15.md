# AUDIT: physical units for the undershooting schedule (`lean/YMGap/RG/UndershootPhysicalUnits.lean`), 2026-11-15

**Compiled with direct `lean -M 6144` against the overlay**: rc 0, zero warnings, peak Lean RSS 1,758 MiB,
min free RAM 13,361 MiB. **Stale-trace caveat:** this is direct lean against copied oleans (Mac scratch build,
same base e57df53c with source sha1s matched, plus the box partial build), NOT lake-verified.
Axioms (temp file, deleted): all within `[propext, Quot.sound]`; `usP_value` has none. New file only, 225 lines.
**δ_min = 0 is only a NECESSARY condition: it removes the obstruction but does not prove `hafδ`.**

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence. Any uniform
gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β; YM Numerics interim report
(numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content
(hcross_OPEN beyond 1/8, AF-regime inputs). Per the numerics, the U(1) transition lies between 1/8 and 1/2,
inside the crossover.

## PROVED (rational, no reals)
* `spacing_weighted` (:58): if `2·a_{i+1} ≤ ρ_i·a_i` and `ρ_i·ω_{i+1} ≤ ω_i`, then `2ⁿ·a_n·ω_n ≤ a_0·ω_0`.
* `spacing_bound` (:92): if also `ω ≥ 1`, then `2ⁿ·a_n ≤ ω_0·a_0`.
* `floor_physical` (:110): from `floor ≤ 2ⁿ·M_n` and `M_n ≥ 0`, `floor·a_n ≤ (ω_0·a_0)·M_n`.
* The schedule's weights:
  * `usRho` (:165): head table, then tail `(m+10)(m+1)/(m(m+11))` with `m = i − 4`;
  * `usOmega` (:166): tail `(m+10)/m`;
  * `tail_weight` (:168): the weight step, with equality via an `ac_rfl` Nat identity;
  * `us_weight` (:191) and `us_omega_ge_one` (:200).
* `usP_value` (:208): `ω_0 = P = 96256076646951/2500000000000`, and `38 < P < 39`.
* `undershoot_spacing_bound` (:218): `2ⁿ·a_n ≤ P·a_0` for all n, under `hspacing_OPEN`.

## Real-analysis link (NOT formalised)
* `2^u ≤ 1 + u` for `0 ≤ u ≤ 1` because `2^u` is **convex**, so it lies below its chord. The 4:49 PM brief said
  "concave"; that was a slip.
* Hence `ℓ_i = log₂(a_i/a_{i+1}) ≥ 1 − u_i` implies `a_i/a_{i+1} ≥ 2/(1+u_i)`, which is `hspacing_OPEN`.
* With `U = log₂ P ≈ 5.267`, the exact real bound is `2ⁿ a_n/a_0 ≤ 2^{Σu}`. The rational `P` is used here; it
  dominates `∏ 2^{u_i}`, which is all that is needed.

## Where P comes from (numerical inputs)
* Crossover: 5.590 (2.48 doublings), with u = 1/100, 1/40, 1/5, 1/2, 2/3, 4/5 from the TM ℓ in Numerics §7
  (finite-cube TM, the least physical part).
* Data window: 2.836, with u = 1 − ℓ_min rounded up to 0.01.
* Tail: 17/7, with u = 10/(m(m+11)) ≈ 0.041–0.044·g⁴ ≥ the design undershoot (0.03 g⁴) + 0.0077 g⁴
  (three-loop of either sign) + slack.
* Measured from a_6 instead, the factor is ≈ 6.89.
* `hspacing_OPEN` is a physics input. It is supported numerically only by the bands in
  `DESIGN-UNDERSHOOT-SCHEDULE-2026-11-15.md`.
