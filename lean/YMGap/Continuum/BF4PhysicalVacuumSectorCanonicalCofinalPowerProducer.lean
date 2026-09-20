/-
# Canonical density certificates to the cofinal completed-gap producer

The canonical finite density certificate supplies exact indexed row/column
laws and component closure.  Its remaining multi-slab identity is an explicit
`CanonicalFullDensityPowerDebt`.  This module wires a cofinal collection of
those certificates, together with one strict rate envelope, into the existing
compatible-factorization producer.

The construction is deliberately an adapter: every factorization field is
filled from the same canonical density and the supplied power debt at the same
anchor and depth.  It does not construct the power debt, a cofinal schedule,
the spacing modulus, a thermodynamic/continuum limit, or the Clay theorem.

The continuum certificate principle is therefore visible in the type: the
finite witness is retained at each scheduled cutoff, while uniformity is an
explicit `localRate_le_rate` field.  Comparison and limit moduli remain later
inputs rather than hidden choices.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate
import YMGap.Continuum.BF4PhysicalVacuumSectorDirectPowerBudgetGap

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalCofinalPowerProducer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate
open YMGap.Continuum.BF4PhysicalVacuumSectorDirectPowerBudgetGap
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4PhysicalVacuumSectorTimeFactorizationAdapter
open YMGap.Continuum.BF4StationaryDensityBufferSplit

/-! ## 1. The cofinal producer input -/

/-- A cofinal family of the canonical finite density certificates.

The `powerDebt` field is the same-carrier multi-slab identity at every
scheduled cutoff.  `sector_centered_bound` is the strict one-step estimate on
that same canonical carrier.  The single `rate` is the uniform envelope that
survives this finite cofinal compilation; no pointwise rate is silently
promoted to it.
-/
structure CanonicalCofinalCompatibleTimeFactorizationRateEnvelope
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (rate : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  depth : Nat → Nat → Nat
  localRate : Nat → Nat → Q'
  localRate_nonnegative : ∀ base threshold,
    (0 : Q') ≤ localRate base threshold
  localRate_le_rate : ∀ base threshold,
    localRate base threshold ≤ rate
  powerDebt : ∀ base threshold,
    CanonicalFullDensityPowerDebt
      w hw (anchor base threshold) half (depth base threshold)
  sector_centered_bound : ∀ base threshold source,
    source ∈ centralPhysicalFiniteVacuumSectorIndices
        w hw (anchor base threshold) half →
      finiteWeightedCenteredRowMass
          (centralPhysicalFiniteVacuumSectorIndices
            w hw (anchor base threshold) half)
          (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
            w hw (anchor base threshold) half)
          (centralPhysicalFiniteVacuumSectorConditionedTimeStep
            w hw (anchor base threshold) half
            (canonicalFullDensityOneStepIndex
              w hw (anchor base threshold) half))
          source ≤ localRate base threshold

/-! ## 2. Exact wiring into the existing compatible-factorization compiler -/

/-- The canonical one-step density and each supplied power debt fill the
existing full-factorization interface without changing the carrier. -/
def CanonicalCofinalCompatibleTimeFactorizationRateEnvelope.toRateEnvelope
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : CanonicalCofinalCompatibleTimeFactorizationRateEnvelope
      w hw half rate) :
    FixedNomeCofinalVacuumCompatibleTimeFactorizationRateEnvelope
      w hw half rate where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  depth := family.depth
  localRate := family.localRate
  fullOneStep := fun base threshold source target =>
    canonicalFullDensityOneStepIndex
      w hw (family.anchor base threshold) half source target
  factorization := by
    intro base threshold
    exact canonicalFullDensityCompatibleTimeFactorization
      (family.powerDebt base threshold)
  localRate_nonnegative := family.localRate_nonnegative
  sector_centered_bound := by
    intro base threshold source hsource
    exact family.sector_centered_bound base threshold source hsource
  localRate_le_rate := family.localRate_le_rate

/-- The canonical cofinal family reaches the explicit power-budget compiler.
The depth-amplified bound is derived constructively from the one uniform rate
envelope, rather than added as a duplicate hypothesis. -/
def CanonicalCofinalCompatibleTimeFactorizationRateEnvelope.toPowerBudget
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : CanonicalCofinalCompatibleTimeFactorizationRateEnvelope
      w hw half rate) :
    FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget
      w hw half rate :=
  family.toRateEnvelope.toPowerBudget

/-- The canonical cofinal family reaches the completed same-object
vacuum-sector strict-gap interface at the supplied uniform rate. -/
def CanonicalCofinalCompatibleTimeFactorizationRateEnvelope.toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : CanonicalCofinalCompatibleTimeFactorizationRateEnvelope
      w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half rate :=
  family.toPowerBudget.toVacuumSectorCenteredStrictGap

end YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalCofinalPowerProducer

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalCofinalPowerProducer.CanonicalCofinalCompatibleTimeFactorizationRateEnvelope.toRateEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalCofinalPowerProducer.CanonicalCofinalCompatibleTimeFactorizationRateEnvelope.toPowerBudget
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalCofinalPowerProducer.CanonicalCofinalCompatibleTimeFactorizationRateEnvelope.toVacuumSectorCenteredStrictGap
