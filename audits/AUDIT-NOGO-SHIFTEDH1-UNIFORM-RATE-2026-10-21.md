# AUDIT: NO-GO, uniform contraction rate vs shifted H1 (2026-10-21 PT)

**Label: NO-GO.** File `lean/YMGap/Continuum/BF4WilsonAllNomeShiftedH1UniformRateNoGo.lean`.

## Statement
`shiftedH1_uniformRate_noGo tr c0 r rj fl hfl H1s Hnd Hr hunif hr1 : False` with
`H1s : PathShiftedEpsBound tr c0`, `Hnd : PathShiftedNondegenerate tr fl` (positive
floors), `Hr : ∀ j, WilsonVacuumRayleighRate … (rj j)`, `hunif : ∀ j, rj j ≤ r`,
`hr1 : r < 1`. Contrapositive: `shiftedH1_forbids_uniformRate`.

## Proof
`path_shiftedEps_forces_rate` gives `side_j (1 - r_j) ≤ c0` (j ≥ 1). Monotonicity gives
`(1-r) side_j ≤ c0`. `exists_side_mul_gt` (witness `j = (c0·(1-r)⁻¹).num.toNat + 1`,
`n ≤ 2^n`) gives `c0 < (1-r) side_j`. Contradiction.

## Scope
* Hypotheses added: none beyond those `path_shiftedEps_forces_rate` already consumes.
* Meaning: under shifted H1, lattice-unit rates must degrade like `1 - c0/side_j`
  (fixed physical gap at best); a scale-uniform lattice-unit gap is excluded.
* Not a mass-gap statement; H1 itself remains OPEN.

## Gates
Focused capped `lake env lean` check (`-j1`, `LEAN_NUM_THREADS=2`, 3.4 GiB worker cap), no
diagnostics. `#print axioms`: main theorems {propext, Quot.sound}; helpers ⊆ {propext}.
Banned-token scan clean.
