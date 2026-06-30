/-
Track B / R2 — **UNIFYING the continuum-gap walls: one canonical spacing-uniform
floor interface that every independent reduction bottoms out at.**

# Why this module exists (read first — and the HONEST scope)

The continuum frontier of this development has been attacked from several
independent directions, and each one was honestly reduced to a single named
OPEN field.  Those fields look superficially different, but they have ONE shape:

  * `CodynamicPhysFloor.UniformPhysGapFloor` — a positive rational `floor` with
    `∀ N, ofQ' floor ≤ physGapC N` (CReal per-scale physical gap), consumed by
    `CRealContinuumGapResidual`;
  * `SpacingUniformProgress.ModeEnergyFloor.energy_floor` — a positive `K` with
    `∀ k i, K ≤ eigval k i` (the generator spectral energies), the scalar core of
    the Bakry–Émery curvature route;
  * `ContinuumGapLimit.ContinuumGapPersistence.uniform_floor` — a positive
    `floorRate` with `∀ Λ, floorRate ≤ gapMargin Λ` (finite-volume gap margins);
  * `ContinuumGapModulus.UniformRatioVariation.floor_le` — a positive `floor`
    with `∀ d, floor ≤ ratio d` (the dimensionless `Δ/√σ̂` ratio along the AF
    schedule);
  * `CodynamicHierarchical.DimensionalTransmutation.rate_matched` — a positive
    `physFloor` with `∀ N, physFloor · aScaling N ≤ (1 − sep N)·∏ρ_dec`
    (the margin, rescaled and matched against the spacing).

In every case the genuinely-open content is the SAME assertion: *a single
strictly-positive rational floor sits below a per-scale gap quantity, UNIFORMLY in
the scale.*  (The sibling `RGGapPersistence.RegScalingBand` carries the same shape
with `physGapMin`.)

This module names that shared shape ONCE, as the polymorphic Type-level interface
`UniformSpacingFloor le g`, and proves the reductions both ways:

  * **extraction** (each wall's open field IS a `UniformSpacingFloor`) — so the
    walls are genuinely the same interface, not merely analogous;
  * **discharge** (a `UniformSpacingFloor` instance FEEDS each wall's consumer) —
    proved in full for the codynamic `UniformPhysGapFloor`/`CRealContinuumGapResidual`
    and the curvature `ModeEnergyFloor` (the two reductions the round targets);
  * **capstone** `unified_continuum_gap` — ONE shared positive scalar floor
    `cur.floor`, instantiated against the codynamic CReal gap quantity AND the
    curvature `Q'` spectral quantity, produces the positive-gap conclusion of BOTH
    routes simultaneously.

# HONESTY — this is CONSOLIDATION, not closure

`UniformSpacingFloor` is itself **UNINHABITED** for the genuine continuum
(`a → 0`): it IS the open dimensional-transmutation / spacing-uniform spectral-gap
physics (Bałaban / Shen–Zhu–Zhu class).  Nothing here inhabits it for 4D
Yang–Mills.  What this round proves is that the several independent continuum walls
**COINCIDE** — they are one and the same open input wearing different units — so
the project has a SINGLE continuum frontier rather than several.  No wall is
removed; they are shown identical.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure repackaging over the five reduction backbones; every carrier is `Type`-level
data (the per-scale `bound` field is a `Pi` of the order relation, never a
`Prop`-∃ existential witness).  Each load-bearing declaration is gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).  No `Classical.*`, no
`native_decide`, no `sorry`.
-/

import YMGap.Continuum.CodynamicPhysFloor
import YMGap.Continuum.SpacingUniformProgress
import YMGap.Continuum.CodynamicHierarchical
import YMGap.Continuum.ContinuumGapLimit
import YMGap.Continuum.ContinuumGapModulus

namespace YMGap.Continuum.UnifiedContinuumFloor

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.CodynamicCRealFlow
open YMGap.Continuum.CodynamicPhysFloor
open YMGap.Continuum.SpacingUniformProgress

/-! ## 1. The canonical interface — one spacing-uniform positive floor

`UniformSpacingFloor le g` is the single shape every continuum wall reduces to: a
strictly-positive rational `floor`, together with the assertion that it lies below
the per-scale gap quantity `g i` (via the order relation `le`) at EVERY scale `i`
simultaneously.  Polymorphic in the index type `ι` (scale / volume / mode), the
carrier `α` (`Q'` or `CReal`), and the order relation `le : Q' → α → Prop` (plain
`≤` for the `Q'` walls, `leEv ∘ ofQ'` for the CReal wall, the spacing-matched
product for dimensional transmutation).  All data is `Type`-level (Rule 8); the
`bound` field is a `Pi`, never a `Prop`-∃. -/

/-- **THE CANONICAL SPACING-UNIFORM FLOOR INTERFACE.**  A single strictly-positive
rational `floor` lying — via the order relation `le` — below the per-scale gap
quantity `g i` for EVERY scale `i` at once.  This is the one shared open input the
continuum walls coincide at; it is UNINHABITED for the genuine `a → 0` limit. -/
structure UniformSpacingFloor {ι : Type} {α : Type} (le : Q' → α → Prop)
    (g : ι → α) : Type where
  /-- The uniform positive floor. -/
  floor : Q'
  /-- The floor is strictly positive. -/
  floor_pos : (0 : Q') < floor
  /-- The floor lies below the per-scale gap quantity at every scale at once. -/
  bound : ∀ i, le floor (g i)

/-- The `Q'`-valued specialization: a positive floor below a `Q'` per-scale
quantity under the plain rational order (`floor ≤ g i`). -/
abbrev QFloor {ι : Type} (g : ι → Q') : Type :=
  UniformSpacingFloor (fun (q x : Q') => q ≤ x) g

/-- The `CReal`-valued specialization: a positive rational floor below a `CReal`
per-scale quantity under the eventual order (`ofQ' floor ≤ g i` via `leEv`). -/
abbrev CRealFloor {ι : Type} (g : ι → CReal) : Type :=
  UniformSpacingFloor (fun (q : Q') (x : CReal) => CReal.leEv (CReal.ofQ' q) x) g

/-! ## 2. EXTRACTION — each named wall's open field IS a `UniformSpacingFloor`

The forward direction of coincidence: every wall's open field repackages, with no
loss, into the canonical interface.  These witness that the walls are literally the
same structure (different `le`/`g`), not merely similar. -/

/-- **Codynamic wall ⊆ canonical (CReal).**  `UniformPhysGapFloor` is a
`CRealFloor` on the per-scale physical gap `physGapC b (sep T) A`. -/
def ofUniformPhysGapFloor {b : Nat} (T : SelfSimilarTower b) (A : SpacingSchedule)
    (U : UniformPhysGapFloor T A) : CRealFloor (physGapC b (sep T) A) where
  floor := U.floor
  floor_pos := U.floor_pos
  bound := U.bound

/-- **Curvature wall ⊆ canonical (`Q'`).**  `ModeEnergyFloor.energy_floor` is a
`QFloor` on the (uncurried) generator spectral energies, with floor `K`. -/
def ofModeEnergyFloor (F : ModeEnergyFloor) :
    QFloor (fun p : Nat × Nat => F.eigval p.1 p.2) where
  floor := F.K
  floor_pos := F.K_pos
  bound := fun p => F.energy_floor p.1 p.2

/-- **Persistence wall ⊆ canonical (`Q'`).**  `ContinuumGapPersistence.uniform_floor`
is a `QFloor` on the per-volume gap margins, with floor `floorRate`. -/
def ofContinuumGapPersistence (P : ContinuumGapLimit.ContinuumGapPersistence) :
    QFloor (fun Λ : Nat => (P.located Λ).gapMargin) where
  floor := P.floorRate
  floor_pos := P.floorRate_pos
  bound := P.uniform_floor

/-- **Modulus wall ⊆ canonical (`Q'`).**  `UniformRatioVariation.floor_le` is a
`QFloor` on the dimensionless ratio along the AF schedule, with floor `floor`. -/
def ofUniformRatioVariation {C : AFTrajectoryCertificate.AFTrajectoryCertificate}
    (V : ContinuumGapModulus.UniformRatioVariation C) :
    QFloor V.ratio where
  floor := V.floor
  floor_pos := V.floor_pos
  bound := V.floor_le

/-- **Dimensional-transmutation wall ⊆ canonical (spacing-matched).**
`DimensionalTransmutation.rate_matched` is a `UniformSpacingFloor` whose order
relation is the spacing-matched product `q · a ≤ rhs`, with floor `physFloor`.
Even this units-rescaled wall is the same canonical interface. -/
def ofDimensionalTransmutation
    (D : CodynamicHierarchical.DimensionalTransmutation) :
    UniformSpacingFloor (fun (q : Q') (p : Q' × Q') => q * p.1 ≤ p.2)
      (fun N : Nat => (D.aScaling N,
        ((1 : Q') - D.sep N)
          * CodynamicHierarchical.physMultiplierProduct D.bb D.sep N)) where
  floor := D.physFloor
  floor_pos := D.physFloor_pos
  bound := D.rate_matched

/-! ## 3. DISCHARGE (codynamic) — canonical ⇒ `UniformPhysGapFloor` ⇒ residual

The reverse direction for the codynamic route: a canonical `CRealFloor` on the
physical gap rebuilds the named wall `UniformPhysGapFloor`, and — together with the
already-proved self-similar flow data (`T`, `uvSeed`, spacing `A`) — assembles the
full `CRealContinuumGapResidual`.  The per-scale positivity half is supplied by the
flow (`CRealContinuumGapResidual.physGap_pos`); the canonical floor discharges
exactly the open uniform half. -/

/-- **Canonical ⇒ codynamic wall.**  A `CRealFloor` on the per-scale physical gap
is exactly the named `UniformPhysGapFloor`. -/
def toUniformPhysGapFloor {b : Nat} (T : SelfSimilarTower b) (A : SpacingSchedule)
    (F : CRealFloor (physGapC b (sep T) A)) : UniformPhysGapFloor T A where
  floor := F.floor
  floor_pos := F.floor_pos
  bound := F.bound

/-- **Canonical ⇒ codynamic continuum residual.**  The single canonical floor,
combined with the already-proved self-similar flow data, assembles the full
`CRealContinuumGapResidual`: the open `uniform` field is discharged by the
canonical interface. -/
def toCRealContinuumGapResidual {b : Nat} (T : SelfSimilarTower b)
    (uvSeed : PosEv (T.w 0)) (A : SpacingSchedule)
    (F : CRealFloor (physGapC b (sep T) A)) : CRealContinuumGapResidual b where
  T := T
  uvSeed := uvSeed
  spacing := A
  uniform := toUniformPhysGapFloor T A F

/-! ## 4. DISCHARGE (curvature) — canonical ⇒ `ModeEnergyFloor`

A canonical `QFloor` on the generator energies of a spectral template `M`
discharges `M`'s open `energy_floor` field, with the curvature constant `K` taken
to be the canonical `floor`.  All other (proved) spectral data of `M` is reused via
record update; only the smallness side-condition `s · K < 1` for the new `K` is
required (it is structural — a positive rescaling constraint, not analytic
content). -/

/-- **Canonical ⇒ curvature wall.**  Given a spectral template `M` (carrying the
proved generator/transfer data) and a canonical `QFloor` on its generator energies,
produce a `ModeEnergyFloor` whose curvature constant is the canonical `floor` and
whose open `energy_floor` is discharged by the canonical `bound`.  `hstep` is the
structural smallness constraint `s · floor < 1`. -/
def toModeEnergyFloor (M : ModeEnergyFloor)
    (F : QFloor (fun p : Nat × Nat => M.eigval p.1 p.2))
    (hstep : M.s * F.floor < (1 : Q')) : ModeEnergyFloor :=
  { M with
    K := F.floor
    K_pos := F.floor_pos
    step_small := hstep
    energy_floor := fun k i => F.bound (k, i) }

/-- **Canonical ⇒ positive curvature continuum mass.**  The curvature route's
strictly-positive continuum mass follows from the canonical floor alone (through
`toModeEnergyFloor` and the proved mode-curvature ⇒ positivity pipeline). -/
theorem curvature_continuum_mass_isPositive (M : ModeEnergyFloor)
    (F : QFloor (fun p : Nat × Nat => M.eigval p.1 p.2))
    (hstep : M.s * F.floor < (1 : Q')) :
    CReal.IsPositive (toModeEnergyFloor M F hstep).toModeCurvatureBound.continuumRate :=
  (toModeEnergyFloor M F hstep).energy_floor_continuum_mass_isPositive

/-! ## 5. CAPSTONE — one shared floor drives BOTH continuum routes

`unified_continuum_gap` takes the already-proved data of both routes (the
self-similar flow `T`/`uvSeed`/`A`; the curvature spectral template `M`) and a
SINGLE shared positive scalar floor — presented as the canonical interface against
each route's per-scale quantity, the two instances tied to the SAME scalar by
`hshared` — and produces the positive-gap conclusion of BOTH the codynamic and the
curvature routes.  This is the demonstration that the two routes share one open
input: the same scalar `cur.floor`, below the codynamic CReal gap and below the
curvature `Q'` spectral energies, is all that is missing from either. -/

/-- **THE UNIFICATION CAPSTONE.**  ONE shared positive scalar floor `cur.floor`
(instantiated codynamically as `cod` against the per-scale physical gap, and
curvature-wise as `cur` against the generator energies, tied together by
`hshared`) yields:

  * the codynamic continuum-floor conclusion — `0 < cur.floor` and the per-scale
    physical-gap bound `∀ N, ofQ' (cur.floor) ≤ physGapC N`, extracted through the
    assembled `CRealContinuumGapResidual`; AND
  * the curvature route's strictly-positive continuum mass.

Both conclusions are produced from the SAME scalar floor, exhibiting that the
codynamic and curvature continuum walls are one and the same open input.  This is
CONSOLIDATION: `cod`/`cur` are uninhabited for the genuine `a → 0` limit. -/
theorem unified_continuum_gap {b : Nat}
    (T : SelfSimilarTower b) (uvSeed : PosEv (T.w 0)) (A : SpacingSchedule)
    (M : ModeEnergyFloor)
    (cod : CRealFloor (physGapC b (sep T) A))
    (cur : QFloor (fun p : Nat × Nat => M.eigval p.1 p.2))
    (hshared : cod.floor = cur.floor)
    (hstep : M.s * cur.floor < (1 : Q')) :
    ( (0 : Q') < cur.floor
        ∧ (∀ N, CReal.leEv (CReal.ofQ' cur.floor) (physGapC b (sep T) A N)) )
    ∧ CReal.IsPositive (toModeEnergyFloor M cur hstep).toModeCurvatureBound.continuumRate := by
  -- Codynamic side: assemble the residual and read off its continuum floor data,
  -- then transport along the shared-scalar equation.
  let R := toCRealContinuumGapResidual T uvSeed A cod
  have hcod_pos : (0 : Q') < cur.floor := hshared ▸ R.continuumFloor_pos
  have hcod_bound : ∀ N, CReal.leEv (CReal.ofQ' cur.floor) (physGapC b (sep T) A N) :=
    hshared ▸ R.continuumFloor_bound
  -- Curvature side: the same shared floor discharges the mode-energy wall.
  have hcurv := curvature_continuum_mass_isPositive M cur hstep
  exact ⟨⟨hcod_pos, hcod_bound⟩, hcurv⟩

end YMGap.Continuum.UnifiedContinuumFloor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.UnifiedContinuumFloor.ofUniformPhysGapFloor
#print axioms YMGap.Continuum.UnifiedContinuumFloor.ofModeEnergyFloor
#print axioms YMGap.Continuum.UnifiedContinuumFloor.ofContinuumGapPersistence
#print axioms YMGap.Continuum.UnifiedContinuumFloor.ofUniformRatioVariation
#print axioms YMGap.Continuum.UnifiedContinuumFloor.ofDimensionalTransmutation
#print axioms YMGap.Continuum.UnifiedContinuumFloor.toUniformPhysGapFloor
#print axioms YMGap.Continuum.UnifiedContinuumFloor.toCRealContinuumGapResidual
#print axioms YMGap.Continuum.UnifiedContinuumFloor.toModeEnergyFloor
#print axioms YMGap.Continuum.UnifiedContinuumFloor.curvature_continuum_mass_isPositive
#print axioms YMGap.Continuum.UnifiedContinuumFloor.unified_continuum_gap
