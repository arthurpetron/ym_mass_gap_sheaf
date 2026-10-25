# Audit — `SU2HeatKernelTorusClusteringBridge` (2026-10-25)

## Classification
- **U(1)-true, fixed-coupling heat-kernel action (`BondMovingStep.coeffW`).**
- **Conditional on the explicit observable-to-semigroup hypothesis `hcov` (`HeatKernelTorusSemigroupBridge`).**
- **NOT evidence for a non-abelian mass gap.**

## Scope & Hygiene
- File: `lean/YMGap/Continuum/SU2HeatKernelTorusClusteringBridge.lean` (250 lines).
- Connects `BF4StrongCouplingClusteringBridge` to `SU2TruncRatio`'s same-action heat-kernel torus (`ZObs w0 S_trunc` on `torusLinks (2M)`, `torusPlaquettes (2M)`), avoiding the `WilsonHeatCoeffDominationNoGo` coefficient mismatch between Taylor-Wilson `T_K` and `coeffW`.
- Proves `ZHK_pos` (`0 < ZHK S_trunc`), `covHK_decay` (`|covHK n| ≤ Ctr · λ^(n+1)`), and `ehatHK_polymer_decay` (`Rq (EhatHK m) ≤ Rq ((Ctr · λ) · (λ²)^m)` for `2m + 1 ≤ M`, uniform in `M` and `S_trunc`).
- Isolates the explicit observable-to-semigroup hypothesis `HeatKernelTorusSemigroupBridge` (`hcov`) and proves `ehatHK_semigroup_decay_of_bridge`, `pilot_ehatHK_semigroup_decay_of_bridge` (`timeRate = 1/4` at `existingPilotNome`), and `pilot_ehatHK_two_rate_envelope`.
- Axioms (`#print axioms`): `[propext, Quot.sound]` only on every declaration.
- Banned-token scan (`sorry`, `admit`, `Classical`, `native_decide`, `omega`, `simpa`, `Mathlib`): 0 matches.
