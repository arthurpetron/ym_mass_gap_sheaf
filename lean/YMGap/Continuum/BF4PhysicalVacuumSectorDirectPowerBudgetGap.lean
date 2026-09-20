/-
# Cofinal direct density-power compiler for the BF4 vacuum sector

The natural output of an exact time factorization is

    conditionedPhysicalDensity = conditionedOneStep^[depth - 1],

where the power contains exactly `depth` one-step factors.  The preceding
adapter proves that a two-sided closed non-strict full factorization has this
form on the canonical vacuum component, and that a sector-local centered
one-step rate `qS` gives the complete row rate `qS^depth`.

This file compiles a constructively cofinal family of those direct powers,
with one uniform strict power budget, into the corrected mass-normalized row
certificate and the existing completed same-object vacuum-sector gap.  It
also packages the full-factorization producer route as one explicit cofinal
certificate.

No such cofinal family is constructed here.  No thermodynamic or continuum
limit is constructed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorTimeFactorizationAdapter

namespace YMGap.Continuum.BF4PhysicalVacuumSectorDirectPowerBudgetGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.BF4PhysicalVacuumSectorTimeFactorizationAdapter
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.FiniteSignedKernelL1
open YMGap.Continuum.FiniteWeightedGramSOS

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Cofinal direct sector-power budget -/

/-- A constructively cofinal family of exact conditioned density powers whose
complete depth-amplified centered rate is bounded by one fixed strict rate. -/
structure FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (rate : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  depth : Nat → Nat → Nat
  localRate : Nat → Nat → Q'
  oneStep : Nat → Nat → Nat → Nat → Q'
  densityPower : ∀ base threshold,
    PhysicalBF4VacuumSectorDensityPowerGluing
      w hw (anchor base threshold) half
      (depth base threshold) (oneStep base threshold)
      (localRate base threshold)
  powerBudget : ∀ base threshold,
    localRate base threshold ^ depth base threshold ≤ rate

namespace FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing

/-- Compile the direct depth-power budget to the corrected mass-normalized
row-distance interface. -/
def toMassNormalizedRowDistance
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing
      w hw half rate) :
    FixedNomeCofinalVacuumSectorMassNormalizedRowDistance
      w hw half rate where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  rowDistance := by
    intro base threshold source hsource
    let cutoff := family.anchor base threshold
    have hsourcePos : (0 : Q') <
        centralPhysicalFiniteWeight w hw cutoff half source :=
      centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
    have hdensityPower :=
      (family.densityPower base threshold).conditionedDensityCenteredRow_le_pow
        source hsource
    have hdensity :
        finiteWeightedCenteredRowMass
            (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
            (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
              w hw cutoff half)
            (centralPhysicalFiniteVacuumSectorMassNormalizedDensity
              w hw cutoff half)
            source ≤ rate :=
      Q'.le_trans' _ _ _ hdensityPower (family.powerBudget base threshold)
    have hidentity :=
      finiteCarrierMassNormalizedRowDistance_eqv_densityCenteredRowMass
        (states := centralPhysicalFiniteVacuumSectorIndices
          w hw cutoff half)
        (mass := centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
        (mass_pos := centralPhysicalFiniteVacuumSectorWeightSum_pos
          w hw cutoff half)
        (weight := centralPhysicalFiniteWeight w hw cutoff half)
        (joint := centralPhysicalFiniteKernel w hw cutoff half)
        hsourcePos
        (fun target htarget =>
          centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex htarget)
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hdensity
      (Q'.le_of_lt hsourcePos)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hidentity) ?_
    refine Q'.le_trans' _ _ _ hscaled ?_
    exact Q'.le_of_eqv
      (Q'.mul_comm_eqv
        (centralPhysicalFiniteWeight w hw cutoff half source) rate)

/-- Compile the same cofinal direct powers to the completed same-object
vacuum-sector strict gap. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing
      w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half rate :=
  family.toMassNormalizedRowDistance.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing

/-! ## 2. Cofinal compatible full-factorization producer -/

/-- The precise remaining cofinal producer on the full-factorization route.
The full one-step density is only required to be normalized and component-
preserving; the strict centered estimate is required solely after
conditioning on the canonical vacuum component. -/
structure FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (rate : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  depth : Nat → Nat → Nat
  localRate : Nat → Nat → Q'
  fullOneStep : Nat → Nat → Nat → Nat → Q'
  factorization : ∀ base threshold,
    PhysicalBF4FiniteVacuumCompatibleTimeFactorization
      w hw (anchor base threshold) half (depth base threshold)
      (fullOneStep base threshold)
  localRate_nonnegative : ∀ base threshold,
    (0 : Q') ≤ localRate base threshold
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
            (fullOneStep base threshold))
          source ≤ localRate base threshold
  powerBudget : ∀ base threshold,
    localRate base threshold ^ depth base threshold ≤ rate

/-! ## 3. Factorization envelope reduction -/

/-- A compatible full-factorization producer with the power-budget field
factored into the simpler uniform local-rate envelope.  This is the minimal
honest input shape for the factorization route: the factorization itself,
sector-centered one-step estimate, and `localRate ≤ rate < 1` remain explicit;
the depth-amplified budget is derived below. -/
structure FixedNomeCofinalVacuumCompatibleTimeFactorizationRateEnvelope
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (rate : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  depth : Nat → Nat → Nat
  localRate : Nat → Nat → Q'
  fullOneStep : Nat → Nat → Nat → Nat → Q'
  factorization : ∀ base threshold,
    PhysicalBF4FiniteVacuumCompatibleTimeFactorization
      w hw (anchor base threshold) half (depth base threshold)
      (fullOneStep base threshold)
  localRate_nonnegative : ∀ base threshold,
    (0 : Q') ≤ localRate base threshold
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
            (fullOneStep base threshold)) source ≤
        localRate base threshold
  localRate_le_rate : ∀ base threshold,
    localRate base threshold ≤ rate

namespace FixedNomeCofinalVacuumCompatibleTimeFactorizationRateEnvelope

/-- The envelope's strict local rate automatically supplies the power budget
required by the existing compatible-factorization compiler. -/
def toPowerBudget
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumCompatibleTimeFactorizationRateEnvelope
      w hw half rate) :
    FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget
      w hw half rate where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  depth := family.depth
  localRate := family.localRate
  fullOneStep := family.fullOneStep
  factorization := family.factorization
  localRate_nonnegative := family.localRate_nonnegative
  sector_centered_bound := family.sector_centered_bound
  powerBudget := by
    intro base threshold
    have hlocal0 := family.localRate_nonnegative base threshold
    have hlocal1 : family.localRate base threshold ≤ (1 : Q') :=
      Q'.le_trans' _ _ _ (family.localRate_le_rate base threshold)
        (Q'.le_of_lt family.rate_lt_one)
    have hdepth : 1 ≤ family.depth base threshold := by
      have hfactor := family.factorization base threshold
      exact Nat.le_trans (by decide : 1 ≤ 3) hfactor.depth_at_least_three
    have hdepth_eq : family.depth base threshold =
        (family.depth base threshold - 1) + 1 := by
      omega
    have hpow :
        family.localRate base threshold ^ family.depth base threshold ≤
          family.localRate base threshold := by
      rw [hdepth_eq]
      exact YMGap.Continuum.HKPos.pow_succ_le_self
        hlocal0 hlocal1 (family.depth base threshold - 1)
    exact Q'.le_trans' _ _ _ hpow
      (family.localRate_le_rate base threshold)

end FixedNomeCofinalVacuumCompatibleTimeFactorizationRateEnvelope

namespace FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget

/-- Restrict every compatible full factorization to the canonical component,
retaining the supplied sector-only strict rate. -/
def toDensityPowerBudgetGluing
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget
      w hw half rate) :
    FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing
      w hw half rate where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  depth := family.depth
  localRate := family.localRate
  oneStep := fun base threshold =>
    centralPhysicalFiniteVacuumSectorConditionedTimeStep
      w hw (family.anchor base threshold) half
      (family.fullOneStep base threshold)
  densityPower := by
    intro base threshold
    exact
      (family.factorization base threshold).toVacuumSectorDensityPowerGluing
        (family.localRate_nonnegative base threshold)
        (family.sector_centered_bound base threshold)
  powerBudget := family.powerBudget

/-- The full-factorization producer compiles to the corrected
mass-normalized cofinal row-distance certificate. -/
def toMassNormalizedRowDistance
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget
      w hw half rate) :
    FixedNomeCofinalVacuumSectorMassNormalizedRowDistance
      w hw half rate :=
  family.toDensityPowerBudgetGluing.toMassNormalizedRowDistance

/-- The same precise producer reaches the completed same-object
vacuum-sector strict gap at its supplied uniform rate. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget
      w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half rate :=
  family.toDensityPowerBudgetGluing.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget

end YMGap.Continuum.BF4PhysicalVacuumSectorDirectPowerBudgetGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDirectPowerBudgetGap.FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing.toMassNormalizedRowDistance
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDirectPowerBudgetGap.FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDirectPowerBudgetGap.FixedNomeCofinalVacuumCompatibleTimeFactorizationRateEnvelope.toPowerBudget
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDirectPowerBudgetGap.FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget.toDensityPowerBudgetGluing
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDirectPowerBudgetGap.FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget.toMassNormalizedRowDistance
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDirectPowerBudgetGap.FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget.toVacuumSectorCenteredStrictGap
