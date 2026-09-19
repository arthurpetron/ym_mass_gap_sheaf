/-
# Exact direct-power to local-slice adapter

The compatible-factorization route naturally supplies a direct conditioned
density power with index `depth - 1`.  The local contraction compiler expects
the same finite density written as two endpoint one-step compositions around
the middle power of index `depth - 3`.  The finite algebra identity is proved
in `BF4PhysicalVacuumSectorDensityPowerDecomposition`; this file only applies
that identity to the concrete sector interfaces.

No cofinal family, analytic estimate, thermodynamic limit, or continuum claim
is constructed here.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorTimeFactorizationAdapter
import YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing
import YMGap.Continuum.BF4PhysicalVacuumSectorLocalPowerBudgetGap
import YMGap.Continuum.BF4PhysicalVacuumSectorDensityPowerDecomposition
import YMGap.Continuum.BF4PhysicalVacuumSectorDirectPowerBudgetGap

namespace YMGap.Continuum.BF4PhysicalVacuumSectorDensityPowerToLocalSlice

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4PhysicalVacuumSectorTimeFactorizationAdapter
open YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing
open YMGap.Continuum.BF4PhysicalVacuumSectorLocalPowerBudgetGap
open YMGap.Continuum.BF4PhysicalVacuumSectorDensityPowerDecomposition
open YMGap.Continuum.BF4PhysicalVacuumSectorDirectPowerBudgetGap

local infix:50 " ≈ " => Q'.eqv

/-! ## Exact finite interface join -/

/-- A direct sector density-power gluing is the local endpoint/middle slice
required by the centered contraction compiler. -/
def PhysicalBF4VacuumSectorDensityPowerGluing.toLocalSliceGluing
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half depth : Nat}
    {oneStep : Nat → Nat → Q'} {qS : Q'}
    (data : PhysicalBF4VacuumSectorDensityPowerGluing
      w hw cutoff half depth oneStep qS) :
    PhysicalBF4VacuumSectorLocalSliceGluing
      w hw cutoff half depth oneStep qS where
  depth_at_least_three := data.depth_at_least_three
  qS_nonnegative := data.qS_nonnegative
  oneStep_row := data.oneStep_row
  oneStep_column := data.oneStep_column
  density_gluing := by
    intro source target hsource htarget
    refine Q'.eqv_trans _ _ _
      (data.density_power source target hsource htarget) ?_
    exact finiteWeightedDensityPower_depth_decomposition
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
        w hw cutoff half)
      oneStep depth data.depth_at_least_three source target
  one_step_centered_bound := data.one_step_centered_bound

/-- A direct-power cofinal family becomes a genuine sector-local family when
the same supplied local rates are known to lie below the quarter threshold.
The quarter premise is kept explicit; the direct power budget alone does not
manufacture it. -/
def FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing.toLocalSliceGluing
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing
      w hw half rate)
    (localRate_le_quarter : ∀ base threshold,
      family.localRate base threshold ≤ quarter) :
    FixedNomeCofinalVacuumSectorLocalSliceGluing w hw half where
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  depth := family.depth
  localRate := family.localRate
  localRate_le_quarter := localRate_le_quarter
  oneStep := family.oneStep
  localSlice := fun base threshold =>
    PhysicalBF4VacuumSectorDensityPowerGluing.toLocalSliceGluing
      (family.densityPower base threshold)

/-- The direct-power family also inhabits the exact depth-amplified local
power-budget interface, retaining its supplied uniform rate without imposing
the stronger one-step quarter cap. -/
def FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing.toLocalPowerBudgetGluing
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing
      w hw half rate) :
    FixedNomeCofinalVacuumSectorLocalPowerBudgetGluing
      w hw half rate where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  depth := family.depth
  localRate := family.localRate
  oneStep := family.oneStep
  localSlice := fun base threshold =>
    PhysicalBF4VacuumSectorDensityPowerGluing.toLocalSliceGluing
      (family.densityPower base threshold)
  powerBudget := family.powerBudget

/-- The direct-power family reaches the existing completed sector gap through
the local depth-amplified compiler as well as through its direct compiler. -/
def FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing.toLocalPowerBudgetVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing
      w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half rate :=
  FixedNomeCofinalVacuumSectorLocalPowerBudgetGluing.toVacuumSectorCenteredStrictGap
    (FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing.toLocalPowerBudgetGluing
      family)

/-- The compatible full-factorization route has the same exact local-slice
join once its explicit sector quarter bound is supplied. -/
def FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget.toLocalSliceGluing
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget
      w hw half rate)
    (localRate_le_quarter : ∀ base threshold,
      family.localRate base threshold ≤ quarter) :
    FixedNomeCofinalVacuumSectorLocalSliceGluing w hw half :=
  FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing.toLocalSliceGluing
    family.toDensityPowerBudgetGluing localRate_le_quarter

/-- The compatible full-factorization route reaches the exact local
power-budget compiler without requiring a one-step quarter cap. -/
def FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget.toLocalPowerBudgetGluing
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget
      w hw half rate) :
    FixedNomeCofinalVacuumSectorLocalPowerBudgetGluing
      w hw half rate :=
  FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing.toLocalPowerBudgetGluing
    family.toDensityPowerBudgetGluing

/-- The compatible full-factorization producer reaches the same completed
sector gap through the exact local power-budget compiler. -/
def FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget.toLocalPowerBudgetVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget
      w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half rate :=
  FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing.toLocalPowerBudgetVacuumSectorCenteredStrictGap
    family.toDensityPowerBudgetGluing

end YMGap.Continuum.BF4PhysicalVacuumSectorDensityPowerToLocalSlice

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityPowerToLocalSlice.PhysicalBF4VacuumSectorDensityPowerGluing.toLocalSliceGluing
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityPowerToLocalSlice.FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing.toLocalSliceGluing
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityPowerToLocalSlice.FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget.toLocalSliceGluing
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityPowerToLocalSlice.FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing.toLocalPowerBudgetGluing
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityPowerToLocalSlice.FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget.toLocalPowerBudgetGluing
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityPowerToLocalSlice.FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing.toLocalPowerBudgetVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityPowerToLocalSlice.FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget.toLocalPowerBudgetVacuumSectorCenteredStrictGap
