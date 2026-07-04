/-
The CURVATURE FLOOR ROUTE — connecting the already-proved links
`UniformCurvatureBound ⟹ ModeEnergyFloor ⟹ UniformSpacingFloor` into ONE named
reduction `CurvatureFloorInput ⟹ QFloor`, landing at the SAME canonical `QFloor`
interface as the DefectGapRecursion-family supplier
(`uniformSpacingFloor_of_trueMarginPhysical`), hence interchangeable with it.

# What this module is

The a→0 continuum frontier has two parallel suppliers of the ONE canonical
spacing-uniform floor (`UnifiedContinuumFloor.QFloor`):

  * the DEFECT route — `uniformSpacingFloor_of_trueMarginPhysical`, feeding the
    per-scale physical `margin`;
  * the CURVATURE route — assembled HERE, feeding the per-mode generator energies
    `eigval` through the Bakry–Émery template.

This module supplies the single MISSING arrow of the curvature chain (the
`UniformCurvatureBound → ModeEnergyFloor` bridge, `toModeEnergyFloor`) and
composes it with the already-proved terminal link
`UnifiedContinuumFloor.ofModeEnergyFloor` to obtain
`curvatureFloor : CurvatureFloorInput → QFloor _`.

# What is PROVED vs the NAMED open input

PROVED (genuine, no new analytic content — pure record assembly over proved
templates):
  * `toModeEnergyFloor` — the missing `UniformCurvatureBound ⟹ ModeEnergyFloor`
    arrow: copies the shared spectral data and DISCHARGES `energy_floor` per mode
    via the proved template `RevGen.eigenvalue_ge_of_CD` fed `uniform_CD`.
  * `curvatureFloor` — the full chain `UCB ⟹ MEF ⟹ USF`, i.e.
    `CurvatureFloorInput → QFloor (fun p => B.eigval p.1 p.2)`, by composing
    `toModeEnergyFloor` with `UnifiedContinuumFloor.ofModeEnergyFloor`.

NAMED (the geometric continuum wall, `Type`-level, Rule 8, UNINHABITED for the
genuine a→0 limit): `UniformCurvatureBound.uniform_CD` — a SINGLE curvature
constant `K > 0` with `CD(K)` at EVERY spacing.  This is the Bałaban- /
Shen–Zhu–Zhu-class interacting uniform-curvature estimate; it is NOT inhabited
here and NOT faked.  This milestone only CONNECTS the proved links.

# Interchangeability with the defect route

`curvatureFloor B` and `uniformSpacingFloor_of_trueMarginPhysical T` both inhabit
`QFloor _ = UniformSpacingFloor (fun q x => q ≤ x) _` — the SAME canonical
interface, differing only in the per-scale quantity (`eigval` vs `margin`).  Any
consumer of a `QFloor` accepts either supplier; `atCanonicalInterface` (an
identity at the canonical type) records this shared shape and is applied to each.

# Axiom-gate (AGENTS.md Rules 1, 6, 8)

Pure `Q'` record assembly over the proved `eigenvalue_ge_of_CD` and
`ofModeEnergyFloor`; no new `axiom`, no `sorry`/`admit`, no `Classical.*`/
`native_decide`/`decide`-on-nondecidable, no `Prop := True` stub.  `uniform_CD`
stays the named open input carried as `Type`-level data.  Permitted axiom output:
`propext` / `Quot.sound` only.
-/

import YMGap.Continuum.UniformCurvatureBound
import YMGap.Continuum.SpacingUniformProgress
import YMGap.Continuum.UnifiedContinuumFloor
import YMGap.Continuum.TrueMarginRecursionPhysical

namespace YMGap.Continuum.CurvatureFloorStatement

open YMGap.Constructive
open YMGap.Continuum.SpacingUniformProgress
open YMGap.Continuum.UnifiedContinuumFloor
open YMGap.Continuum.UniformCurvatureBound

/-! ## 1. The curvature-floor input — the NAMED residual as data

`CurvatureFloorInput` IS the `UniformCurvatureBound`: the uniform curvature
constant `K > 0` plus the eigen-link, carrying the named open field `uniform_CD`.
The curvature-floor data — "curvature constant + per-scale mode-energy floor" — is
exactly `K` (with `K_pos`) together with the `energy_floor` this input DERIVES
below. -/

/-- **The curvature-floor input** — the single geometric residual of the a→0
limit, carried as `Type`-level data.  Its open field `uniform_CD` (a single
`CD(K)`, `K > 0`, at every spacing) is the NAMED research core; it is NOT
inhabited here. -/
abbrev CurvatureFloorInput : Type := UniformCurvatureBound

/-! ## 2. The MISSING arrow — `UniformCurvatureBound ⟹ ModeEnergyFloor`

The only unconnected link of the curvature chain.  Copies the shared spectral
data verbatim and discharges the scalar energy floor per mode from the curvature
bound, via the proved Bakry–Émery template `RevGen.eigenvalue_ge_of_CD`. -/

/-- **The curvature ⇒ mode-energy-floor bridge.**  A `CurvatureFloorInput` yields
a `ModeEnergyFloor`: all spectral fields are copied, and the open `energy_floor`
(`∀ k i, K ≤ eigval k i`) is DISCHARGED per mode by the proved template
`eigenvalue_ge_of_CD` fed the uniform curvature bound `uniform_CD k` and the
genuine excited mode `(eigf k i, eigval k i)`.  No new analytic content. -/
def toModeEnergyFloor (B : CurvatureFloorInput) : ModeEnergyFloor where
  gen        := B.gen
  spec       := B.spec
  K          := B.K
  K_pos      := B.K_pos
  s          := B.s
  s_pos      := B.s_pos
  step_small := B.step_small
  eigf       := B.eigf
  eigval     := B.eigval
  eigen      := B.eigen
  eigval_pos := B.eigval_pos
  var_pos    := B.var_pos
  energy_floor := fun k i =>
    (B.gen k).eigenvalue_ge_of_CD (B.uniform_CD k) (B.eigf k i) (B.eigen k i)
      (B.eigval_pos k i) (B.var_pos k i)
  spec_lam_eq := B.spec_lam_eq

/-! ## 3. The full chain `UCB ⟹ MEF ⟹ USF` — landing at the canonical floor -/

/-- **THE CURVATURE FLOOR REDUCTION.**  A `CurvatureFloorInput` supplies the
canonical spacing-uniform floor on the generator spectral energies:
`CurvatureFloorInput → QFloor (fun p => B.eigval p.1 p.2)`, with floor `K`.
Proof: the missing arrow `toModeEnergyFloor` composed with the proved terminal
link `ofModeEnergyFloor`.  Same canonical `QFloor` target as the defect route. -/
def curvatureFloor (B : CurvatureFloorInput) :
    QFloor (fun p : Nat × Nat => B.eigval p.1 p.2) :=
  ofModeEnergyFloor (toModeEnergyFloor B)

/-- The reduced floor is exactly the uniform curvature constant `K`. -/
theorem curvatureFloor_floor (B : CurvatureFloorInput) :
    (curvatureFloor B).floor = B.K := rfl

/-! ## 4. Interchangeability with the DefectGapRecursion route

`curvatureFloor B` and the defect supplier
`uniformSpacingFloor_of_trueMarginPhysical T` both inhabit `QFloor _`, i.e. the
SAME `UniformSpacingFloor (fun q x => q ≤ x) _`.  Any `QFloor`-consumer accepts
either; the routes differ only in the per-scale quantity (`eigval` vs `margin`).
Interchangeability is a TYPE-LEVEL shape fact, not a proposition to discharge, so
we record it as the identity `def` at the canonical type and apply it to each
supplier. -/

/-- **The canonical interface as an identity.**  A generic consumer of the
canonical floor is its shared shape `QFloor g`; the identity at that type accepts
any supplier.  Applying it to each route below witnesses that they are drop-in
replacements at the SAME interface. -/
def atCanonicalInterface {ι : Type} {g : ι → Q'} (F : QFloor g) : QFloor g := F

/-- The CURVATURE supplier at the canonical interface. -/
def curvatureAtInterface (B : CurvatureFloorInput) :
    QFloor (fun p : Nat × Nat => B.eigval p.1 p.2) :=
  atCanonicalInterface (curvatureFloor B)

/-- The DEFECT supplier at the SAME canonical interface. -/
def defectAtInterface (T : YMGap.Continuum.TrueMarginRecursionPhysical) :
    QFloor T.margin :=
  atCanonicalInterface (YMGap.Continuum.uniformSpacingFloor_of_trueMarginPhysical T)

/-- The curvature supplier at the canonical interface is unchanged (identity). -/
theorem curvatureAtInterface_eq (B : CurvatureFloorInput) :
    curvatureAtInterface B = curvatureFloor B := rfl

/-- The defect supplier at the canonical interface is unchanged (identity). -/
theorem defectAtInterface_eq (T : YMGap.Continuum.TrueMarginRecursionPhysical) :
    defectAtInterface T
      = YMGap.Continuum.uniformSpacingFloor_of_trueMarginPhysical T := rfl

/-- The curvature supplier at the canonical interface. -/
example (B : CurvatureFloorInput) :
    QFloor (fun p : Nat × Nat => B.eigval p.1 p.2) := curvatureFloor B

/-- The defect supplier at the SAME canonical interface. -/
example (T : YMGap.Continuum.TrueMarginRecursionPhysical) :
    QFloor T.margin :=
  YMGap.Continuum.uniformSpacingFloor_of_trueMarginPhysical T

end YMGap.Continuum.CurvatureFloorStatement

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CurvatureFloorStatement.toModeEnergyFloor
#print axioms YMGap.Continuum.CurvatureFloorStatement.curvatureFloor
#print axioms YMGap.Continuum.CurvatureFloorStatement.curvatureFloor_floor
#print axioms YMGap.Continuum.CurvatureFloorStatement.curvatureAtInterface
#print axioms YMGap.Continuum.CurvatureFloorStatement.defectAtInterface
