# boundedH @ finite volume — CLOSE of the two analytic monotonicity residuals

Date: 2026-07-08. Reconstruction/spectral side. LEAN-CORE only, axiom gate
`{propext, Quot.sound}`. Build green, guard green (5 frontier types uninhabited).

New file: `lean/YMGap/Continuum/BoundedHFiniteVolClosed.lean` (wired into `YMGap.lean`).

---

## STEP 1 — AUDIT (proved-vs-open, before this work)

### `BoundedHamiltonianFiniteVol.lean` (`FiniteVolumeBoundedH`)
The milestone-(a) bounded-Hamiltonian mass gap, carried by the bounded transfer
carrier `op := G.op.T` + located `−log` energies (NOT a literal unbounded `H`).
Six field-groups:

- CLOSED outright: `op`, `selfAdjoint` (`= G.op.T`, genuine bounded), `vacuum_zero`
  (`hamiltonian_vacuum_energy_zero`), `Δ / hΔ` (`hamiltonianGapReal`), `Δ_pos`
  (`hamiltonianGapReal_pos` via `isPositive_neg_logRat`), `spectrum_nonneg`
  (`isPositive_neg_logRat ∘ leEv_czero_of_isPositive`).
- REDUCED: the `noSpectrumIn` FLOOR `Δ = −log sep ≤ E_i = −log λ_i`, assembled by
  `HamiltonianSpectrumInf.hamiltonianGap_le_energy` from **two `Type`-level analytic
  residuals** carried as hypotheses of `mkFiniteVolumeBoundedH`:
  - `YOfMonotone` — `a ≤ b ⟹ yOf a ≤ yOf b` (`yOf m = (m−1)/(m+1)`);
  - `ArtanhMonotoneWindow` — `y ≤ y' ⟹ leEv (artanh y) (artanh y')` on `|y|≤1/3`.
  **VERDICT: these two were OPEN** (structures taken as arguments, never inhabited).
  Everything downstream (`hamiltonianGap_le_energy`, `neg_logRat_antitone`,
  `logRat_leEv_of_le`) was proved *conditionally on* `Y, A`.

### `HaddDischarge.lean` (`hadd`)
**DISCHARGED**, confirmed. `spectralMarginInput_of_edgeLocalization` installs the
PROVED `EdgeLocalizationResidual.hadd` (`= hadd_from_edge_residual`, a real
`Q'`/`Nat` theorem) into the `SpectralMarginInput.hadd` field definitionally
(`hadd_is_installed : … .hadd = R.hadd` by `rfl`). `hEdge` / `hFR` are STRUCTURE
FIELDS of `EdgeLocalizationResidual` (model hookups), and `hadd_from_edge_residual`
proves `hadd` from them + `hlat_margin`. So `hadd` is a theorem of
`{hEdge, hFR, node ①}`; its only genuinely-open dependency is node ① `bulk_shift`
(inside `L k`). Sub-wall B dropped `{hadd, hbridge, sl.hlocalize} → {hbridge,
sl.hlocalize}`. Not touched by this work.

### `SelfAdjointHamiltonian.lean` (`BoundedFunctionalCalculusResidual`)
The LITERAL bounded operator `H` with `e^{−H}=T`. **Genuinely UNSATISFIABLE** over
the spin tower (`−log w^{C₄(s)} → +∞`, `−log` unbounded at 0). The module documents
this and quarantines it as a named residual. **NOT forced** — the mass gap uses the
`FiniteVolumeBoundedH` reframing (bounded carrier + located energies), which is
STRONGER than needed only in the literal-operator direction and WEAKER (correct)
here. Honesty guardrail respected.

---

## STEP 2 — CLOSE (this work)

`BoundedHFiniteVolClosed.lean` PROVES both analytic residuals with shelf tools:

1. `recipPos_antitone` — `0<x≤y ⟹ 1/y ≤ 1/x`, one line off `recipPos_num/_den`.
2. `yOf_eqv_form` — `yOf m ≃ 1 − 2·(1/(m+1))` (since `m−1 = (m+1)−2` and
   `(m+1)·recipPos(m+1) ≃ 1`).
3. **`yOfMonotone_proof : YOfMonotone`** — from (1)+(2): `a≤b ⟹ a+1≤b+1 ⟹
   1/(b+1)≤1/(a+1) ⟹ 1−2/(a+1) ≤ 1−2/(b+1)`.
4. `neg_mul_neg_eqv`, `neg_even_pow_eqv`, `neg_odd_pow_eqv` — power-of-negation
   identities (`(−a)^{2k} ≃ a^{2k}`, `(−a)^{2k+1} ≃ −(a^{2k+1})`).
5. **`odd_pow_mono`** (the genuine new lemma) — `a≤b ⟹ a^{2k+1} ≤ b^{2k+1}` for
   ARBITRARY rationals (no sign hypothesis), by a three-way sign split off the
   existing one-sided `pow_le_pow_base` (nonneg base), `odd_pow_nonpos`, `pow_nonneg`
   plus (4). This is exactly "−log antitone over the located spectrum" content:
   odd powers are monotone across all signs, so each artanh term is monotone.
6. `term_mono`, `partialSum_mono` — termwise/pointwise partial-sum monotonicity.
7. **`artanhMonotoneWindow_proof : ArtanhMonotoneWindow`** — pointwise
   `partialSum y n ≤ partialSum y' n ⟹ leEv` (N=0).

Both structures are now INHABITED (proved), axiom-clean `{propext, Quot.sound}`.

8. **`mkFiniteVolumeBoundedH_uncond`** — `mkFiniteVolumeBoundedH` with `Y, A`
   ELIMINATED (installed from 3 & 7). The `noSpectrumIn` floor no longer depends on
   any unproved monotonicity input.

9. **`concreteBoundedH` — NON-VACUOUS `FiniteVolumeBoundedH`** over a REAL finite
   `SpectralModel`: the excited character tower at `w = 9/10`, `N = 1`. Single mode
   `λ₀ = qpow(9/10)(c4 1) = (9/10)³ = 729/1000 = sep ∈ [2/3,1)`. In-window
   certificates (`concWin_val : |yOf(729/1000)| = 271/1729 ≤ 1/3`) hold by `decide`
   on a CLOSED term, transported to the `op`-indexed fields by proof-irrelevance of
   the positivity argument. Located gap `Δ = −log(729/1000) > 0` is genuine
   (`isPositive_neg_logRat` supplies an explicit positive rational witness — NOT a
   zero/shape witness). `concreteBoundedH_mass_gap` reads off the three predicates
   `H ≥ 0`, `H ψ_vac = 0`, `Δ > 0`.

### Verdict on `FiniteVolumeBoundedH` at finite volume
The STANDARD operator mass gap (`H ≥ 0`, `vacuum_zero`, no spectrum in `(0,Δ)`,
carried by the bounded transfer op + located `−log` energies) is **CLOSED with shelf
tools** — non-vacuously inhabited by a real finite spectral model with a genuine
located gap. The only remaining hypotheses of the constructor are the in-window
certificates `hwin`/`win` (`|yOf λ_i| ≤ 1/3`, i.e. `λ_i ≥ 1/2`) — the honest
energy-image scope caveat that the direct artanh construction (`m ∈ [2/3,2]`) always
carried, discharged concretely for the single-mode witness. The two ANALYTIC
monotonicity residuals are gone. The literal unbounded `H` is correctly NOT forced.

---

## STEP 3 — HONEST Sub-wall B state after boundedH/hadd

Shelf tools (finite-dim operator theory) closed:
- the operator-theory dictionary (`hadd` = located-2nd-eigenvalue ↔ physical margin),
- the bounded finite-vol Hamiltonian mass gap (`FiniteVolumeBoundedH`, above).

**Remaining Sub-wall B residual = node ① only**, which is NOT finite-dim operator
theory but the RG-defect / spectral-localization atoms:
- `hbridge` / `bulk_shift` — the Bałaban-RG spectral localization
  (`shift_k ≤ δ_k · g_k`), and
- `sl.hlocalize` — the graded bond-moving localization (Core B).

These are the genuine RG-localization frontier; `hadd` and the reconstruction-side
bounded-H gap no longer sit in front of them.

---

## VERIFY (re-run)

- `lake build` exit **0** (774 jobs); `lake build YMGapGuard` exit **0**.
- Guard: all **5** frontier types (`Tier0Scorecard`, `UniformSpacingFloor`,
  `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`) remain UNINHABITED — no
  reconstruction/Sub-wall-B atom reacted (`FiniteVolumeBoundedH` is not a frontier
  scorecard type). Guard stays 5.
- `#print axioms` on every new decl (`recipPos_antitone`, `yOf_eqv_form`,
  `yOfMonotone_proof`, `odd_pow_mono`, `artanhMonotoneWindow_proof`,
  `mkFiniteVolumeBoundedH_uncond`, `concreteBoundedH`, `concreteBoundedH_mass_gap`):
  `[propext, Quot.sound]` — clean.
- No `native_decide` / `sorry` / `Prop := True` (only in the doc comment stating we
  avoid them). `decide` = kernel decision on closed rational arithmetic (allowed).
- Non-vacuity genuine: real single-mode `SpectralModel` (`k=1`), `sep = 729/1000`,
  window bound `271/1729 ≤ 1/3` decided true, `Δ = −log(729/1000) > 0` with explicit
  positive witness. Not a shape/zero term.

**Bottom line:** boundedH is CLOSED at finite volume on the reconstruction side (a
real D-move: the two analytic monotonicity residuals `YOfMonotone` /
`ArtanhMonotoneWindow` are now proved; `FiniteVolumeBoundedH` non-vacuously
inhabited with shelf tools). What remains in Sub-wall B is node ① (RG spectral
localization `hbridge`/`bulk_shift` + `sl.hlocalize`), which is RG-defect
mathematics, not finite-dim operator theory.
