/-
# Scale-dependent microscopic contraction and uniform physical grouping

A positive block map near the continuum limit need not have a contraction
rate bounded away from one per microscopic lattice step.  For a physical mass
gap one instead expects

    q_a = 1 - a m + o(a),

so `q_a -> 1` while the product over a fixed physical distance remains
strictly subunit.

This module gives that distinction an exact constructive interface.
`ScaleDependentContractionCertificate` permits a different rational rate at
every microscopic scale.  Its finite evolution contracts by the literal
product of those rates.  `GroupedContractionDoor` then asks for one exact
bound on each consecutive group product and exports the grouped evolution as
the existing `UniformContractionCertificate` consumed by RG-I7--I9.

Thus a Birkhoff diameter certificate may deteriorate microscopically without
invalidating the route.  The load-bearing physical obligation is the grouped
product estimate.  This file proves only the composition algebra; it does not
construct that estimate for Yang--Mills.

## Axiom gate

Constructive exact-rational algebra only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, quotient, or noncomputable declaration is used.
-/

import YMGap.RG.StableDynamics

namespace YMGap.RG.ScaleDependentGroupedContraction

open YMGap.Constructive
open YMGap.RG.StableDynamics

universe u v

/-- Microscopic contraction data with a scale-dependent exact rate. -/
structure ScaleDependentContractionCertificate (X : Type u) where
  distance : X → X → Q'
  Admissible : X → Type v
  step : Nat → X → X
  rate : Nat → Q'
  rateNonnegative : ∀ n, (0 : Q') ≤ rate n
  rateBelowOne : ∀ n, rate n < (1 : Q')
  distanceNonnegative : ∀ x y, (0 : Q') ≤ distance x y
  stepAdmissible :
    ∀ n x, Admissible x → Admissible (step n x)
  contracts :
    ∀ n x y, Admissible x → Admissible y →
      distance (step n x) (step n y) ≤ rate n * distance x y

namespace ScaleDependentContractionCertificate

/-- Consecutive microscopic evolution beginning at `start`. -/
def evolveFrom {X : Type u}
    (certificate : ScaleDependentContractionCertificate.{u, v} X)
    (start : Nat) (x : X) : Nat → X
  | 0 => x
  | length + 1 =>
      certificate.step (start + length)
        (certificate.evolveFrom start x length)

/-- The exact product of the consecutive microscopic rates. -/
def rateProduct {X : Type u}
    (certificate : ScaleDependentContractionCertificate.{u, v} X)
    (start : Nat) : Nat → Q'
  | 0 => 1
  | length + 1 =>
      certificate.rate (start + length) *
        certificate.rateProduct start length

def evolveAdmissible {X : Type u}
    (certificate : ScaleDependentContractionCertificate.{u, v} X)
    (start : Nat) {x : X} (hx : certificate.Admissible x) :
    (length : Nat) →
      certificate.Admissible
        (certificate.evolveFrom start x length)
  | 0 => hx
  | length + 1 =>
      certificate.stepAdmissible (start + length) _
        (certificate.evolveAdmissible start hx length)

theorem rateProduct_nonnegative {X : Type u}
  (certificate : ScaleDependentContractionCertificate.{u, v} X)
    (start : Nat) :
    ∀ length, (0 : Q') ≤ certificate.rateProduct start length
  | 0 => by
      change (0 : Q') ≤ 1
      decide
  | length + 1 =>
      Q'.mul_nonneg _ _
        (certificate.rateNonnegative (start + length))
        (certificate.rateProduct_nonnegative start length)

/-- The scale-dependent microscopic evolution contracts by the literal
ordered product of its rates. -/
theorem evolve_pair_contracts {X : Type u}
    (certificate : ScaleDependentContractionCertificate.{u, v} X)
    (start : Nat) {x y : X}
    (hx : certificate.Admissible x)
    (hy : certificate.Admissible y) :
    ∀ length,
      certificate.distance
          (certificate.evolveFrom start x length)
          (certificate.evolveFrom start y length) ≤
        certificate.rateProduct start length *
          certificate.distance x y
  | 0 => by
      exact Q'.ge_of_eqv
        (Q'.one_mul_eqv (certificate.distance x y))
  | length + 1 => by
      have hstep :=
        certificate.contracts (start + length)
          (certificate.evolveFrom start x length)
          (certificate.evolveFrom start y length)
          (certificate.evolveAdmissible start hx length)
          (certificate.evolveAdmissible start hy length)
      have hind :=
        certificate.evolve_pair_contracts start hx hy length
      have hscaled :
          certificate.rate (start + length) *
              certificate.distance
                (certificate.evolveFrom start x length)
                (certificate.evolveFrom start y length) ≤
            certificate.rate (start + length) *
              (certificate.rateProduct start length *
                certificate.distance x y) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _
          hind (certificate.rateNonnegative (start + length))
      exact Q'.le_trans' _ _ _ hstep
        (Q'.le_trans' _ _ _ hscaled
          (Q'.ge_of_eqv
            (Q'.mul_assoc_eqv
              (certificate.rate (start + length))
              (certificate.rateProduct start length)
              (certificate.distance x y))))

end ScaleDependentContractionCertificate

/-- Starting microscopic index of group `group`, for consecutive group
lengths beginning at index zero. -/
def groupStart (groupLength : Nat → Nat) : Nat → Nat
  | 0 => 0
  | group + 1 => groupStart groupLength group + groupLength group

/-- A uniform contraction door over fixed-physical-distance groups.

The group lengths may grow as the lattice spacing decreases.  The only
uniform datum is the upper bound on each exact product of microscopic rates.
-/
structure GroupedContractionDoor
    {X : Type u}
    (microscopic : ScaleDependentContractionCertificate.{u, v} X) where
  groupLength : Nat → Nat
  macroRate : Q'
  macroRateNonnegative : (0 : Q') ≤ macroRate
  macroRateBelowOne : macroRate < (1 : Q')
  groupRateBound :
    ∀ group,
      microscopic.rateProduct
          (groupStart groupLength group)
          (groupLength group) ≤ macroRate

namespace GroupedContractionDoor

/-- One grouped step is a consecutive block of microscopic steps. -/
def groupedStep
    {X : Type u}
    {microscopic : ScaleDependentContractionCertificate.{u, v} X}
    (door : GroupedContractionDoor microscopic)
    (group : Nat) (x : X) : X :=
  microscopic.evolveFrom
    (groupStart door.groupLength group) x (door.groupLength group)

def groupedStepAdmissible
    {X : Type u}
    {microscopic : ScaleDependentContractionCertificate.{u, v} X}
    (door : GroupedContractionDoor microscopic)
    (group : Nat) (x : X)
    (hx : microscopic.Admissible x) :
    microscopic.Admissible (door.groupedStep group x) :=
  microscopic.evolveAdmissible
    (groupStart door.groupLength group) hx (door.groupLength group)

theorem groupedStep_contracts
    {X : Type u}
    {microscopic : ScaleDependentContractionCertificate.{u, v} X}
    (door : GroupedContractionDoor microscopic)
    (group : Nat) (x y : X)
    (hx : microscopic.Admissible x)
    (hy : microscopic.Admissible y) :
    microscopic.distance
        (door.groupedStep group x)
        (door.groupedStep group y) ≤
      door.macroRate * microscopic.distance x y := by
  have hproduct :=
    microscopic.evolve_pair_contracts
      (groupStart door.groupLength group) hx hy (door.groupLength group)
  have hrate :
      microscopic.rateProduct
            (groupStart door.groupLength group)
            (door.groupLength group) *
          microscopic.distance x y ≤
        door.macroRate * microscopic.distance x y :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (door.groupRateBound group)
      (microscopic.distanceNonnegative x y)
  exact Q'.le_trans' _ _ _ hproduct hrate

/-- Export the fixed-physical-distance grouping as the literal uniform
contraction certificate already consumed by the RG-I7--I9 layer. -/
def toUniformContractionCertificate
    {X : Type u}
    {microscopic : ScaleDependentContractionCertificate.{u, v} X}
    (door : GroupedContractionDoor microscopic) :
    UniformContractionCertificate.{u, v} X where
  distance := microscopic.distance
  Admissible := microscopic.Admissible
  step := door.groupedStep
  q := door.macroRate
  qNonnegative := door.macroRateNonnegative
  qBelowOne := door.macroRateBelowOne
  distanceNonnegative := microscopic.distanceNonnegative
  stepAdmissible := door.groupedStepAdmissible
  contracts := door.groupedStep_contracts

theorem exported_rate_eq
    {X : Type u}
    {microscopic : ScaleDependentContractionCertificate.{u, v} X}
    (door : GroupedContractionDoor microscopic) :
    door.toUniformContractionCertificate.q = door.macroRate :=
  rfl

theorem exported_step_eq
    {X : Type u}
    {microscopic : ScaleDependentContractionCertificate.{u, v} X}
    (door : GroupedContractionDoor microscopic)
    (group : Nat) (x : X) :
    door.toUniformContractionCertificate.step group x =
      microscopic.evolveFrom
        (groupStart door.groupLength group) x (door.groupLength group) :=
  rfl

end GroupedContractionDoor

#print axioms ScaleDependentContractionCertificate.rateProduct_nonnegative
#print axioms ScaleDependentContractionCertificate.evolve_pair_contracts
#print axioms GroupedContractionDoor.groupedStep_contracts
#print axioms GroupedContractionDoor.toUniformContractionCertificate
#print axioms GroupedContractionDoor.exported_rate_eq
#print axioms GroupedContractionDoor.exported_step_eq

end YMGap.RG.ScaleDependentGroupedContraction
