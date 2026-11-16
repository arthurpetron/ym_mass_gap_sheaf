# AUDIT: undershooting AF nome schedule (`lean/YMGap/RG/UndershootAfSchedule.lean`), 2026-11-15

**Compiled with direct `lean -M 6144` against the overlay** (`direct_build2.py`): rc 0, zero warnings,
peak Lean RSS 1,766 MiB, min free RAM 13,525 MiB. **Stale-trace caveat:** after the box restore (~16:51 PST)
the dependency oleans come from two places, so this is direct lean against copied oleans, NOT lake-verified:
* 1,876 modules copied read-only from the Mac scratch build (`~/ymlean_prover_scratch/wt`, same base e57df53c;
  every source sha1 matched);
* 1,485 modules from the earlier box partial build.

The recompile of the existing `TwoLoopAfSchedule.lean` passed as a check (rc 0, 1,783 MiB).
Axioms (temp file, deleted): `undershootSchedule`, `undershoot_join` and `undershoot_steps` use
`[propext, Quot.sound]`; `usGap_le_of_modulus` uses `[propext]`. New file only (178 lines). No
sorry/admit/Classical/native_decide/omega/simpa.

**δ_min = 0 for ℓ ≤ 1 is only a NECESSARY condition: it removes the obstruction from README §8 but does
NOT prove `hafδ`.**

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence. Any uniform
gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β; YM Numerics interim report
(numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content
(hcross_OPEN beyond 1/8, AF-regime inputs). Per the numerics, the U(1) transition lies between 1/8 and 1/2,
inside the crossover.

## PROVED
* `undershootSchedule : NomeSchedule` (:135). Head j < 11 by bounded decide. Tail
  `w_j = 1 − 1941658544/usF(j−11)`, where `usF` is a Nat recursion with increment `usInc` (:47, :52);
  monotone because the increments are Nat additions. Modulus `11 + 1941658544·ε.den`, from
  `usF_ge` (:58), `usF i ≥ 12577219337 + i`.
* `undershoot_join` (:160): w₀ = 1/64 ≤ 1/55, `w_j = dyTable j` for j < 6, w₆ = 779/1000 (no offset).
* `undershoot_steps` (:174): `DyadicRGStep` holds for every n < 45. `DyadicRGStep` only bounds a step from
  above, so it accepts ℓ < 1; no variant is needed.

## NUMERICAL design (not a theorem)
See `audits/DESIGN-UNDERSHOOT-SCHEDULE-2026-11-15.md` for the full table (j ≤ 41) and the choice of c.
* Data window j = 6..10: steps are sized so that ℓ_max = 1 − 0.03·g⁴ under the §8 slope bands.
* Tail: the two-loop step is `1 − 7/((i+8)(i+16))`, with c_eff ∈ [0.0290, 0.0304].
* (1 − ℓ_max)/g⁴ ≥ 0.0081 on the tail up to j = 1009, against the worst known residual of +0.021 g⁴.
