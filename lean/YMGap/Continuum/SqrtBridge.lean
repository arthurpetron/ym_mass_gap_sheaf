/-
The √-bridge: `m_0 = √σ̂_∞` as a genuine constructive real (Milestone F.5,
`docs/uniform-parametric-bound-plan.md` Part II.4).

# Why this module exists

The SU(2) mass bound was carried as a `Q'`-rational threshold `m_0² ≤ σ̂_∞`
(decidable), and the dimensional identification `m ≥ √σ̂_∞` was paper-only.
`Constructive/Sqrt.lean` now provides a genuine constructive square root
`CReal.sqrtFrom` (Heron iteration, explicit Type-level modulus, axiom-clean),
proving it is positive for positive input and satisfies `(√a)² ≃ a`.

This module plugs that into the σ̂_∞ application: it defines the mass

    m_0 := √σ̂_∞    (a `CReal`),

with witnessed positivity inherited from the proved `σ̂_∞ > 0`, and the proved
square identity `m_0² ≃ σ̂_∞` (`CReal.Equiv`).  The √-content is now a Lean
theorem, not an assumption; only the dimensional (mass-units) interpretation
remains the paper's province.

For the UV-direction pilot, `σ̂_∞ = ofQ' 1` (the σ̂_N trajectory is the constant
`σ̂_0 = 1`), so `m_0 = √1` and the conservative O(1) area-law constant is `1`
explicitly.  The construction is fully general in the square-root value: any
positive rational `a` with a positive rational lower-bound witness `L` (`L² ≤ a`)
gives `√a` via `CReal.sqrtFrom`.

# Axiom-gate (AGENTS.md Rule 1)

Every theorem reports `[propext, Quot.sound]` only (the `Quot.sound` from
`omega`/`Nat` in the underlying Heron analysis).  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Constructive.Sqrt
import YMGap.Constructive.Reals

namespace YMGap.Continuum.SqrtBridge

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.RG.SigmaHatPilotUV

/-! ## The rational value of σ̂_∞ and its lower-bound witness

`σ̂_∞ = ofQ' 1` for the UV pilot.  We expose the rational value `sigmaHatVal = 1`
and its lower-bound witness `L = 1` (`1·1 ≤ 1`), the inputs `sqrtFrom` consumes. -/

/-- The rational value of σ̂_∞ for the UV pilot: `1`. -/
def sigmaHatVal : Q' := sigma_hat_0_pilot_uv

theorem sigmaHatVal_pos : (0 : Q') < sigmaHatVal := by decide

/-- A positive rational lower-bound witness: `L = 1`, with `L² ≤ σ̂_∞`. -/
def sqrtL : Q' := 1

theorem sqrtL_pos : (0 : Q') < sqrtL := by decide

theorem sqrtL_sq_le : sqrtL * sqrtL ≤ sigmaHatVal := by decide

/-- `sigma_hat_inf_creal` is definitionally `ofQ' sigmaHatVal`. -/
theorem sigma_hat_inf_creal_eq_ofQ' :
    sigma_hat_inf_creal = CReal.ofQ' sigmaHatVal := rfl

/-! ## The mass `m_0 = √σ̂_∞` -/

/-- **The mass `m_0 = √σ̂_∞`** as a genuine constructive real. -/
def m_0 : CReal := CReal.sqrtFrom sigmaHatVal sqrtL sigmaHatVal_pos sqrtL_pos sqrtL_sq_le

/-- **`m_0 > 0`** — the dimensional positivity of the mass, witnessed by the
rational lower bound `L`, ultimately from `σ̂_∞ > 0`. -/
theorem m_0_isPositive : CReal.IsPositive m_0 :=
  CReal.sqrtFrom_isPositive sigmaHatVal sqrtL sigmaHatVal_pos sqrtL_pos sqrtL_sq_le

/-- **`m_0² ≃ σ̂_∞`** — the defining square identity of the √-bridge:
the square of the mass is `CReal.Equiv` to σ̂_∞. -/
theorem m_0_sq_equiv_sigma_hat :
    CReal.Equiv (CReal.mul m_0 m_0) sigma_hat_inf_creal := by
  -- (√a)² ≃ ofQ' a = σ̂_∞
  rw [sigma_hat_inf_creal_eq_ofQ']
  exact CReal.sqrtFrom_sq_equiv sigmaHatVal sqrtL sigmaHatVal_pos sqrtL_pos sqrtL_sq_le

/-- **The √-bridge, packaged.**  There is a constructive real `m_0` that is
strictly positive and whose square is `σ̂_∞`: the genuine Lean form of
`m_0 = √σ̂_∞`, `m_0 > 0`, `m_0² ≃ σ̂_∞`. -/
def sqrt_bridge :
    Σ' m : CReal, CReal.IsPositive m ∧ CReal.Equiv (CReal.mul m m) sigma_hat_inf_creal :=
  ⟨m_0, m_0_isPositive, m_0_sq_equiv_sigma_hat⟩

/-! ## The dimensionless gap ratio `Δ/√σ̂` (the Buckingham-Π invariant)

Dimensional analysis (Buckingham-Π) on the data `{Δ, √σ̂}` — one mass dimension
shared by both — leaves **exactly one** dimensionless invariant, the pure number

    gapRatio  :=  Δ / √σ̂  =  Δ / m_0 .

That pure number is the physically meaningful content of the mass gap: rescaling
the mass unit rescales `Δ` and `m_0 = √σ̂` *together*, leaving `gapRatio` fixed.
The choice `σ̂ = 1` (hence `m_0 = √σ̂ = 1`) in this development is precisely such a
unit choice (a √σ̂-as-unit-of-mass convention); it cancels in `gapRatio`.

There is no division on `CReal`, so we carry the ratio **multiplicatively**: the
defining relation is `gapRatio · m_0 ≃ Δ` (i.e. `Δ = gapRatio · √σ̂`), never a
division operator.  The constructor below is parametric in the dimensionless
number `r`: supplying `r` *defines* the dimensionful gap `Δ := r · m_0`, so the
multiplicative defining relation holds by reflexivity and `IsPositive gapRatio`
is exactly `IsPositive r`.  This is the reusable `Δ/√σ̂` constructor. -/

/-- `Equiv` is reflexive (the `ε`-slack absorbs the `0` difference). -/
theorem Equiv.refl (x : CReal) : CReal.Equiv x x :=
  fun ε hε => ⟨0, fun n _ =>
    ⟨Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε),
     Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε)⟩⟩

/-- **The dimensionful gap from a dimensionless ratio.**  Given the dimensionless
number `r` (the pure `Δ/√σ̂`), the dimensionful gap is `Δ := r · m_0 = r · √σ̂`. -/
def dimensionfulGapOf (r : CReal) : CReal := CReal.mul r m_0

/-- **The dimensionless gap ratio `Δ/√σ̂`, carried multiplicatively.**  For the
dimensionless number `r`, `gapRatioOf r := r` is the Buckingham-Π invariant; its
defining relation `gapRatioOf r · m_0 ≃ dimensionfulGapOf r` (`= Δ`) and its
positivity are immediate.  This is the reusable `Δ/√σ̂` constructor. -/
def gapRatioOf (r : CReal) : CReal := r

/-- **Multiplicative defining relation of the gap ratio:** `gapRatioOf r · m_0 ≃
Δ`, i.e. `Δ = (Δ/√σ̂) · √σ̂`, with no division.  Holds by reflexivity because
`dimensionfulGapOf r` is *defined* as `r · m_0`. -/
theorem gapRatioOf_mul_m_0_equiv (r : CReal) :
    CReal.Equiv (CReal.mul (gapRatioOf r) m_0) (dimensionfulGapOf r) :=
  Equiv.refl _

/-- **Positivity of the gap ratio.**  The dimensionless `Δ/√σ̂` is strictly
positive whenever `Δ` is — here directly, since `gapRatioOf r = r` and `Δ =
r · m_0` with `m_0 > 0`, so a positive `r` gives both a positive ratio and a
positive `Δ`. -/
theorem gapRatioOf_isPositive {r : CReal} (hr : CReal.IsPositive r) :
    CReal.IsPositive (gapRatioOf r) := hr

/-- **The dimensionless-ratio bridge, packaged.**  From a positive dimensionless
number `r`, the data: the gap ratio (positive) and the multiplicative defining
relation `gapRatio · m_0 ≃ Δ`.  Reusable Buckingham-Π `Δ/√σ̂` constructor. -/
def gapRatio_bridge {r : CReal} (hr : CReal.IsPositive r) :
    Σ' g : CReal, CReal.IsPositive g
      ∧ CReal.Equiv (CReal.mul g m_0) (dimensionfulGapOf r) :=
  ⟨gapRatioOf r, gapRatioOf_isPositive hr, gapRatioOf_mul_m_0_equiv r⟩

/-! ### A concrete, non-vacuous instance: the saturated ratio `Δ/√σ̂ = 1`

Taking `r := ofQ' 1` (so `Δ := 1 · m_0 = √σ̂`) gives a genuine, non-vacuous
inhabitant: `gapRatio ≃ 1`, the marginal `Δ = √σ̂` case (gap equal to the string
scale).  It witnesses the constructor on actual data, not vacuously. -/

/-- The dimensionless number `1` as a `CReal`. -/
def oneRatio : CReal := CReal.ofQ' 1

/-- `oneRatio` is strictly positive (`ε = 1`). -/
theorem oneRatio_isPositive : CReal.IsPositive oneRatio :=
  CReal.isPositive_of_approx_ge (by decide) (fun _ => Q'.le_refl' 1)

/-- **Concrete gap ratio `Δ/√σ̂ = 1`** (the `Δ = √σ̂` marginal case), with its
multiplicative defining relation `gapRatio · m_0 ≃ Δ` and positivity — a genuine
non-vacuous inhabitant of the Buckingham-Π constructor. -/
def gapRatio_one_bridge :
    Σ' g : CReal, CReal.IsPositive g
      ∧ CReal.Equiv (CReal.mul g m_0) (dimensionfulGapOf oneRatio) :=
  gapRatio_bridge oneRatio_isPositive

/-! ## Quarantine: unit choices vs numeric witnesses (honesty split)

The constants in this development fall into two strictly different kinds, and the
Buckingham-Π analysis makes the distinction precise.  This namespace re-exposes
them (as ADDITIVE aliases — the originals are untouched) tagged by kind. -/

namespace unitScale

/-- UNIT CHOICE (cancels).  `sigmaHatVal = σ̂ = 1` is the arbitrary mass-unit
convention — taking `√σ̂` as the unit of mass.  It is *not* a physical claim: it
drops out of every dimensionless ratio (Buckingham-Π).  Alias of `sigmaHatVal`. -/
def sigmaHatUnit : Q' := sigmaHatVal

/-- UNIT CHOICE (cancels).  `sqrtL = 1` is the rational lower-bound witness used
to build `√σ̂` under the same `σ̂ = 1` unit convention; a unit choice, not a
physical claim.  Alias of `sqrtL`. -/
def sqrtLUnit : Q' := sqrtL

theorem sigmaHatUnit_eq : sigmaHatUnit = sigmaHatVal := rfl
theorem sqrtLUnit_eq : sqrtLUnit = sqrtL := rfl

end unitScale

end YMGap.Continuum.SqrtBridge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SqrtBridge.sigmaHatVal_pos
#print axioms YMGap.Continuum.SqrtBridge.sqrtL_sq_le
#print axioms YMGap.Continuum.SqrtBridge.m_0
#print axioms YMGap.Continuum.SqrtBridge.m_0_isPositive
#print axioms YMGap.Continuum.SqrtBridge.m_0_sq_equiv_sigma_hat
#print axioms YMGap.Continuum.SqrtBridge.sqrt_bridge
#print axioms YMGap.Continuum.SqrtBridge.Equiv.refl
#print axioms YMGap.Continuum.SqrtBridge.dimensionfulGapOf
#print axioms YMGap.Continuum.SqrtBridge.gapRatioOf
#print axioms YMGap.Continuum.SqrtBridge.gapRatioOf_mul_m_0_equiv
#print axioms YMGap.Continuum.SqrtBridge.gapRatioOf_isPositive
#print axioms YMGap.Continuum.SqrtBridge.gapRatio_bridge
#print axioms YMGap.Continuum.SqrtBridge.oneRatio_isPositive
#print axioms YMGap.Continuum.SqrtBridge.gapRatio_one_bridge
#print axioms YMGap.Continuum.SqrtBridge.unitScale.sigmaHatUnit_eq
#print axioms YMGap.Continuum.SqrtBridge.unitScale.sqrtLUnit_eq
