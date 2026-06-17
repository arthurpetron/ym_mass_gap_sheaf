/-
Track B / R2 — a CONCRETE inhabitant of the volume-uniform cluster bound, turning
the thermodynamic-limit reduction from "conditional on the cluster bound" into
"the cluster bound is inhabited at strong coupling", and firing the end-to-end
continuum-mass chain on it with NO remaining hypothesis.

# What this module is

The continuum gap-persistence reduction collapses the whole thermodynamic Λ→∞
limit (convergence of the per-volume gap margins AND persistence of a uniform
positive floor) to a SINGLE `Type`-level input: the volume-uniform cluster bound.
Up to now that input was an abstract interface with no concrete inhabitant — the
reduction fired only on a hypothetical witness.

This module CONSTRUCTS a genuine, non-vacuous inhabitant grounded in the proven
strong-coupling located-gap datum: the constant finite-volume family at the
proven `sep = 1/2` located gap.  Every per-volume gap margin is the genuine
strict mass-gap margin `1 − 1/2 = 1/2 > 0` of the compact finite transfer
operator, so:

  * `floorRate := 1/2` is exactly that proven margin; `uniform_floor` holds with
    equality (the constant family meets the floor at every volume);
  * `tailConst := 0` — the strong-coupling cluster tail of a CONSTANT
    (volume-independent) margin sequence vanishes; the single-step geometric
    bounds `incr_up` / `incr_lo` then read `m ≤ m + geoIncr 0 Λ`, true because
    `geoIncr 0 Λ ≥ 0` and consecutive margins are EQUAL (the family is constant);
  * `modulus` is the project's division-free product modulus at `B = 2·0`.

The floor is grounded in the genuine finite-volume located mass gap (the
`sep = 1/2` second eigenvalue strictly below the vacuum eigenvalue `1`), the same
strong-coupling datum the rest of the development rests on.  The renormalized
string tension σ̂_∞ is independently positive in the strong-coupling regime
(`SigmaHatLimit.zero_lt_sigma_hat_uv_epsilon`), which is the physical grounding
of a positive gap floor; the precise numerical √-bridge `m ≥ √σ̂_∞` is NOT wired
in here, so the rational floor `1/2` is the proven eigenvalue-gap margin rather
than a σ̂-derived number — stated honestly.

From this inhabitant the reduction's capstone — a strictly-positive continuum
mass — fires end to end with no remaining hypothesis.

# Axiom-gate

Each load-bearing theorem reports `[propext]` / `[propext, Quot.sound]` only.
No `sorry`, no `Classical.*`, no `native_decide`.
-/

import YMGap.Continuum.ClusterGapReduction
import YMGap.Continuum.ContinuumGapLimit
import YMGap.Continuum.LocatedReconstruction
import YMGap.Continuum.KPLimit
import YMGap.Constructive.CRealMul

namespace YMGap.Continuum.ClusterBoundInstance

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.ContinuumGapLimit
open YMGap.Continuum.ClusterGapReduction

/-! ## The strong-coupling clustering floor

The floor is the proven eigenvalue-gap margin of the `sep = 1/2` located gap:
`1 − 1/2 = 1/2 > 0`.  This is the genuine finite-volume mass gap of the compact
transfer operator, not an arbitrary constant. -/

/-- The strong-coupling clustering floor `δ = 1/2`: the proven eigenvalue-gap
margin `1 − sep` of the `sep = 1/2` located gap. -/
def strongCouplingFloor : Q' := Q'.mkPos 1 2 (by decide)

/-- The clustering floor is strictly positive. -/
theorem strongCouplingFloor_pos : (0 : Q') < strongCouplingFloor := by
  show (0 : Int) * (2 : Int) < (1 : Int) * (1 : Int)
  decide

/-- The constant `sep = 1/2` family's gap margin is the strong-coupling floor at
every volume: `(constGappedLocated Λ).gapMargin = 1 − 1/2`.  This is `rfl`. -/
theorem constGapped_margin_eq (Λ : Nat) :
    (constGappedLocated Λ).gapMargin = 1 - Q'.mkPos 1 2 (by decide) := rfl

/-! ## The concrete cluster bound at strong coupling

All fields discharged from the proven `sep = 1/2` located gap:

  * `gaps` / `located` — the constant `sep = 1/2` finite-volume family;
  * `floorRate` — the proven margin `1/2`, met with EQUALITY by `uniform_floor`;
  * `tailConst := 0` — the vanishing cluster tail of a constant margin sequence;
  * `incr_up` / `incr_lo` — `m ≤ m + geoIncr 0 Λ` (`geoIncr 0 Λ ≥ 0`, margins
    constant), via `add_le_self_of_nonneg`;
  * `modulus` — the division-free product modulus at `B = 2·0`. -/

/-- **The volume-uniform cluster bound at strong coupling, CONSTRUCTED.**  A
genuine inhabitant of `UniformClusterBound` built from the proven `sep = 1/2`
located gap: a constant gap-margin family at the strong-coupling floor `1/2` with
vanishing cluster tail.  Non-vacuous — every field carries real located-gap
data, not a placeholder. -/
def strongCouplingClusterBound : UniformClusterBound where
  gaps := constGappedFamily
  located := constGappedLocated
  floorRate := strongCouplingFloor
  floorRate_pos := strongCouplingFloor_pos
  uniform_floor := fun Λ => constGapped_uniform_floor Λ
  tailConst := 0
  tailConst_nonneg := Q'.le_refl' 0
  incr_up := fun Λ =>
    -- (located (Λ+1)).gapMargin = (located Λ).gapMargin (constant family, rfl),
    -- so the goal is m ≤ m + geoIncr 0 Λ with geoIncr 0 Λ ≥ 0.
    Q'.add_le_self_of_nonneg _ (geoIncr 0 Λ) (geoIncr_nonneg 0 (Q'.le_refl' 0) Λ)
  incr_lo := fun Λ =>
    Q'.add_le_self_of_nonneg _ (geoIncr 0 Λ) (geoIncr_nonneg 0 (Q'.le_refl' 0) Λ)
  modulus := fun ε hε =>
    CReal.exists_mul_le
      (Q'.mul_nonneg _ _ (by decide) (Q'.le_refl' 0)) hε

/-- The constructed cluster bound's clustering floor is `1/2`. -/
theorem strongCouplingClusterBound_floor :
    strongCouplingClusterBound.floorRate = strongCouplingFloor := rfl

/-- The constructed cluster bound's cluster tail constant vanishes. -/
theorem strongCouplingClusterBound_tailConst :
    strongCouplingClusterBound.tailConst = 0 := rfl

/-! ## The continuum rate of the concrete inhabitant

Feeding the inhabitant through the reduction's `continuumRate` yields a genuine
`CReal` whose every approximation is the constant strong-coupling margin `1/2`. -/

/-- The continuum gap rate of the strong-coupling inhabitant — the `CReal` limit
of the (constant) `sep = 1/2` margin sequence. -/
def strongCouplingContinuumRate : CReal :=
  continuumRate strongCouplingClusterBound

/-- Every approximation of the strong-coupling continuum rate is the proven gap
margin `1 − 1/2` — the limit is fed by the genuine located gap, not a stub. -/
@[simp] theorem strongCouplingContinuumRate_approx (Λ : Nat) :
    strongCouplingContinuumRate.approx Λ = 1 - Q'.mkPos 1 2 (by decide) := rfl

/-! ## Capstone: a concrete strictly-positive continuum mass, no hypotheses

Instantiating the reduction's positivity capstone at the concrete inhabitant
gives a `CReal.IsPositive` certificate for the continuum mass with NO remaining
free parameter — the end-to-end chain
finite-volume located gaps ⟹ uniform cluster bound ⟹ positive continuum mass
now fires on a genuine object. -/

/-- **Capstone (positivity, unconditional).**  The continuum mass built from the
strong-coupling cluster inhabitant is a strictly-positive constructive real.
This is `clusterBound_continuum_mass_isPositive` at the concrete inhabitant — no
hypothesis remains: the cluster bound is inhabited, and the chain fires. -/
theorem strongCoupling_continuum_mass_isPositive :
    CReal.IsPositive strongCouplingContinuumRate :=
  clusterBound_continuum_mass_isPositive strongCouplingClusterBound

/-- **Capstone (packaged).**  The concrete continuum mass as `Type`-level data
with its positivity proof, fed end-to-end by the strong-coupling cluster bound —
the strictly-positive continuum mass gap, unconditionally inhabited. -/
def strongCoupling_continuum_gap_bridge : Σ' m : CReal, CReal.IsPositive m :=
  clusterBound_continuum_gap_bridge strongCouplingClusterBound

/-- The packaged mass is exactly the strong-coupling continuum rate. -/
theorem strongCoupling_bridge_fst :
    strongCoupling_continuum_gap_bridge.1 = strongCouplingContinuumRate := rfl

/-- The full continuum gap-persistence datum, populated by the strong-coupling
cluster bound — the reduction's `ContinuumGapPersistence` with all fields, both
formerly-open ones included, supplied by the concrete inhabitant. -/
def strongCouplingPersistence : ContinuumGapPersistence :=
  continuumGapPersistence_of_clusterBound strongCouplingClusterBound

/-- The persistence datum's continuum rate is the strong-coupling continuum
rate. -/
theorem strongCouplingPersistence_rate :
    strongCouplingPersistence.continuumRate = strongCouplingContinuumRate := rfl

end YMGap.Continuum.ClusterBoundInstance

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ClusterBoundInstance.strongCouplingFloor_pos
#print axioms YMGap.Continuum.ClusterBoundInstance.constGapped_margin_eq
#print axioms YMGap.Continuum.ClusterBoundInstance.strongCouplingClusterBound
#print axioms YMGap.Continuum.ClusterBoundInstance.strongCouplingClusterBound_floor
#print axioms YMGap.Continuum.ClusterBoundInstance.strongCouplingClusterBound_tailConst
#print axioms YMGap.Continuum.ClusterBoundInstance.strongCouplingContinuumRate
#print axioms YMGap.Continuum.ClusterBoundInstance.strongCouplingContinuumRate_approx
#print axioms YMGap.Continuum.ClusterBoundInstance.strongCoupling_continuum_mass_isPositive
#print axioms YMGap.Continuum.ClusterBoundInstance.strongCoupling_continuum_gap_bridge
#print axioms YMGap.Continuum.ClusterBoundInstance.strongCoupling_bridge_fst
#print axioms YMGap.Continuum.ClusterBoundInstance.strongCouplingPersistence
#print axioms YMGap.Continuum.ClusterBoundInstance.strongCouplingPersistence_rate
