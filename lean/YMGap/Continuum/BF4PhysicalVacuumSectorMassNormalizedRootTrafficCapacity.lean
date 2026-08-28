/-
# Mass-normalized full-sector root-traffic capacity

The existing full-sector root flow routes twice the stationary demand from
every canonical-component state to the vacuum.  Its unnormalized capacity
condition compares `delta * flowLoad` directly with the physical kernel and
therefore produces a posterior fraction containing the component mass.

The normalized local condition is instead

    fraction * flowLoad(source,target)
      <= componentMass * physicalKernel(source,target).

It implies

    fraction * pairwiseVariance
      <= componentMass * physicalDirichlet,

so the mass-normalized pairwise bridge cancels the component mass and keeps
the same `fraction`.  This turns the global normalized Poincare frontier into
a pointwise congestion estimate on the already-constructed physical flow.

Every finite cutoff has a non-vacuous instance obtained from the old finite
capacity, with fraction `min 1 (componentMass * delta)`.  Avoiding that mass
loss cofinally requires proving the new normalized edge comparison directly;
no such cofinal witness or continuum conclusion is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCapacity
import YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedPairwiseGapBridge

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRootTrafficCapacity

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTraffic
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCapacity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedPairwiseGapBridge
open YMGap.Continuum.FiniteWeightedGramSOS

local infix:50 " ≈ " => Q'.eqv

private theorem q_min_pos_local {left right : Q'}
    (hleft : (0 : Q') < left) (hright : (0 : Q') < right) :
    (0 : Q') < Q'.min' left right := by
  unfold Q'.min'
  by_cases horder : left ≤ right
  · rw [if_pos horder]
    exact hleft
  · rw [if_neg horder]
    exact hright

/-- Multiplying a positive quotient by its denominator cancels before any
further right factor. -/
private theorem mass_mul_divPos_mul_eqv_local
    (mass fraction value : Q') (hmass : (0 : Q') < mass) :
    mass * (Q'.divPos fraction mass hmass * value) ≈
      fraction * value := by
  let reciprocal := Q'.recipPos mass hmass
  have hinner : mass * (fraction * reciprocal) ≈ fraction := by
    refine Q'.eqv_trans _ ((mass * fraction) * reciprocal) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv mass fraction reciprocal)) ?_
    refine Q'.eqv_trans _ ((fraction * mass) * reciprocal) _
      (Q'.mul_eqv_congr_right _ _ reciprocal
        (Q'.mul_comm_eqv mass fraction)) ?_
    refine Q'.eqv_trans _ (fraction * (mass * reciprocal)) _
      (Q'.mul_assoc_eqv fraction mass reciprocal) ?_
    refine Q'.eqv_trans _ (fraction * 1) _
      (Q'.mul_eqv_congr_left fraction _ _
        (Q'.mul_recipPos_eqv mass hmass)) ?_
    exact Q'.mul_one_eqv fraction
  unfold Q'.divPos
  change mass * ((fraction * reciprocal) * value) ≈ fraction * value
  refine Q'.eqv_trans _ ((mass * (fraction * reciprocal)) * value) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv mass (fraction * reciprocal) value)) ?_
  exact Q'.mul_eqv_congr_right _ _ value hinner

/-! ## 1. Finite normalized pointwise capacity -/

/-- A pointwise capacity for the existing full canonical-sector root flow,
normalized by the actual component mass. -/
structure CentralPhysicalFiniteVacuumSectorMassNormalizedRootTrafficCapacityAt
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) : Type 1 where
  fraction : Q'
  fraction_pos : (0 : Q') < fraction
  fraction_le_one : fraction ≤ (1 : Q')
  edge_capacity : ∀ source,
    source ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K half →
    ∀ target,
    target ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K half →
      fraction * centralPhysicalFiniteVacuumSectorRootFlowLoad
          w (Q'.le_of_lt hw) K half source target ≤
        centralPhysicalFiniteVacuumSectorMass
            w (Q'.le_of_lt hw) K half *
          centralPhysicalFiniteKernel
            w (Q'.le_of_lt hw) K half source target

namespace CentralPhysicalFiniteVacuumSectorMassNormalizedRootTrafficCapacityAt

/-- Divide the normalized fraction by the positive component mass to recover
the old unnormalized pointwise capacity at this one cutoff. -/
def toRootTrafficCapacityAt
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    (capacity :
      CentralPhysicalFiniteVacuumSectorMassNormalizedRootTrafficCapacityAt
        hw K half) :
    CentralPhysicalFiniteVacuumSectorRootTrafficCapacityAt hw K half where
  delta := Q'.divPos capacity.fraction
    (centralPhysicalFiniteVacuumSectorMass
      w (Q'.le_of_lt hw) K half)
    (centralPhysicalFiniteVacuumSectorWeightSum_pos
      w (Q'.le_of_lt hw) K half)
  delta_pos := Q'.divPos_pos _ _
    (centralPhysicalFiniteVacuumSectorWeightSum_pos
      w (Q'.le_of_lt hw) K half)
    capacity.fraction_pos
  edge_capacity := by
    intro source hsource target htarget
    let mass := centralPhysicalFiniteVacuumSectorMass
      w (Q'.le_of_lt hw) K half
    let load := centralPhysicalFiniteVacuumSectorRootFlowLoad
      w (Q'.le_of_lt hw) K half source target
    let kernel := centralPhysicalFiniteKernel
      w (Q'.le_of_lt hw) K half source target
    have hmass : (0 : Q') < mass := by
      unfold mass
      exact centralPhysicalFiniteVacuumSectorWeightSum_pos
        w (Q'.le_of_lt hw) K half
    apply Q'.le_of_mul_le_mul_left (c := mass)
    · exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (mass_mul_divPos_mul_eqv_local
            mass capacity.fraction load hmass))
        (capacity.edge_capacity source hsource target htarget)
    · exact hmass

/-- The normalized local congestion comparison implies the exact global
mass-normalized pairwise Poincare inequality. -/
def toMassNormalizedPairwiseCoercivityData
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    (capacity :
      CentralPhysicalFiniteVacuumSectorMassNormalizedRootTrafficCapacityAt
        hw K half) :
    CentralPhysicalFiniteMassNormalizedPairwiseCoercivityData
      w (Q'.le_of_lt hw) K half where
  fraction := capacity.fraction
  fraction_pos := capacity.fraction_pos
  fraction_le_one := capacity.fraction_le_one
  coercivity := by
    intro coefficient
    let mass := centralPhysicalFiniteVacuumSectorMass
      w (Q'.le_of_lt hw) K half
    let pairwise := centralPhysicalFiniteVacuumSectorPairwiseVariance
      w (Q'.le_of_lt hw) K half coefficient
    let dirichlet := finiteJointDirichletEnergy
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K half)
      coefficient
      (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K half)
    have hmass : (0 : Q') < mass := by
      unfold mass
      exact centralPhysicalFiniteVacuumSectorWeightSum_pos
        w (Q'.le_of_lt hw) K half
    have hold :
        (capacity.toRootTrafficCapacityAt.delta * pairwise) ≤
          dirichlet := by
      unfold pairwise dirichlet
      exact capacity.toRootTrafficCapacityAt
        |>.delta_mul_pairwiseVariance_le_physicalDirichlet coefficient
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ mass hold
      (Q'.le_of_lt hmass)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (mass_mul_divPos_mul_eqv_local
            mass capacity.fraction pairwise hmass)))
      hscaled

/-- Therefore the normalized local edge comparison already gives the exact
finite posterior-variance gap. -/
def toConditionalVarianceGapData
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    (capacity :
      CentralPhysicalFiniteVacuumSectorMassNormalizedRootTrafficCapacityAt
        hw K half) :=
  capacity.toMassNormalizedPairwiseCoercivityData
    |>.toConditionalVarianceGapData

end CentralPhysicalFiniteVacuumSectorMassNormalizedRootTrafficCapacityAt

/-! ## 2. Every finite cutoff is non-vacuous -/

/-- Any old finite root capacity gives a normalized one with the exact
mass-paying fraction `min 1 (componentMass * delta)`. -/
def CentralPhysicalFiniteVacuumSectorRootTrafficCapacityAt.toMassNormalized
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    (capacity : CentralPhysicalFiniteVacuumSectorRootTrafficCapacityAt
      hw K half) :
    CentralPhysicalFiniteVacuumSectorMassNormalizedRootTrafficCapacityAt
      hw K half where
  fraction := Q'.min' 1
    (centralPhysicalFiniteVacuumSectorMass
      w (Q'.le_of_lt hw) K half * capacity.delta)
  fraction_pos := q_min_pos_local (by decide)
    (Q'.mul_pos
      (centralPhysicalFiniteVacuumSectorWeightSum_pos
        w (Q'.le_of_lt hw) K half)
      capacity.delta_pos)
  fraction_le_one := Q'.min_le_left' _ _
  edge_capacity := by
    intro source hsource target htarget
    let mass := centralPhysicalFiniteVacuumSectorMass
      w (Q'.le_of_lt hw) K half
    let load := centralPhysicalFiniteVacuumSectorRootFlowLoad
      w (Q'.le_of_lt hw) K half source target
    let kernel := centralPhysicalFiniteKernel
      w (Q'.le_of_lt hw) K half source target
    have hload0 : (0 : Q') ≤ load := by
      unfold load
      exact centralPhysicalFiniteVacuumSectorRootFlowLoad_nonnegative
        w (Q'.le_of_lt hw) K half source target
    have hfirst : Q'.min' 1 (mass * capacity.delta) * load ≤
        (mass * capacity.delta) * load :=
      Q'.mul_le_mul_of_nonneg_right _ _ load
        (Q'.min_le_right' 1 (mass * capacity.delta)) hload0
    have hold := capacity.edge_capacity source hsource target htarget
    have hmass0 : (0 : Q') ≤ mass :=
      Q'.le_of_lt
        (centralPhysicalFiniteVacuumSectorWeightSum_pos
          w (Q'.le_of_lt hw) K half)
    have hsecond : mass * (capacity.delta * load) ≤
        mass * kernel :=
      Q'.mul_le_mul_of_nonneg_left _ _ mass hold hmass0
    exact Q'.le_trans' _ _ _ hfirst
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_assoc_eqv mass capacity.delta load))
        hsecond)

/-- A concrete positive mass-normalized root-traffic certificate at every
finite cutoff.  Its displayed fraction records the old route's mass loss. -/
def centralPhysicalFiniteVacuumSectorMassNormalizedRootFiniteCapacityAt
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) :
    CentralPhysicalFiniteVacuumSectorMassNormalizedRootTrafficCapacityAt
      hw K half :=
  CentralPhysicalFiniteVacuumSectorRootTrafficCapacityAt.toMassNormalized
    (centralPhysicalFiniteVacuumSectorRootFiniteCapacityAt hw K half)

/-! ## 3. The direct cofinal normalized congestion frontier -/

/-- One positive normalized pointwise root-flow capacity at every later
cutoff.  This is a concrete local sufficient theorem for the cofinal
mass-normalized Poincare gap. -/
structure FixedNomeCofinalVacuumSectorMassNormalizedRootTrafficCapacity
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  fraction : Q'
  fraction_pos : (0 : Q') < fraction
  fraction_le_one : fraction ≤ (1 : Q')
  edge_capacity : ∀ K, start ≤ K → ∀ source,
    source ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0 →
    ∀ target,
    target ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0 →
      fraction * centralPhysicalFiniteVacuumSectorRootFlowLoad
          w (Q'.le_of_lt hw) K 0 source target ≤
        centralPhysicalFiniteVacuumSectorMass
            w (Q'.le_of_lt hw) K 0 *
          centralPhysicalFiniteKernel
            w (Q'.le_of_lt hw) K 0 source target

namespace FixedNomeCofinalVacuumSectorMassNormalizedRootTrafficCapacity

def finiteCapacityAt
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassNormalizedRootTrafficCapacity hw)
    {K : Nat} (hK : family.start ≤ K) :
    CentralPhysicalFiniteVacuumSectorMassNormalizedRootTrafficCapacityAt
      hw K 0 where
  fraction := family.fraction
  fraction_pos := family.fraction_pos
  fraction_le_one := family.fraction_le_one
  edge_capacity := family.edge_capacity K hK

def toCofinalMassNormalizedPairwiseCoercivity
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassNormalizedRootTrafficCapacity hw) :
    FixedNomeCofinalMassNormalizedPairwiseCoercivity hw where
  start := family.start
  fraction := family.fraction
  fraction_pos := family.fraction_pos
  fraction_le_one := family.fraction_le_one
  coercivity := by
    intro K hK coefficient
    exact (family.finiteCapacityAt hK)
      |>.toMassNormalizedPairwiseCoercivityData
      |>.coercivity coefficient

/-- The normalized pointwise root-traffic estimate compiles to the exact
cofinal posterior fraction with no separate component-mass floor. -/
def toCofinalConditionalVarianceFraction
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassNormalizedRootTrafficCapacity hw) :=
  family.toCofinalMassNormalizedPairwiseCoercivity
    |>.toCofinalConditionalVarianceFraction

end FixedNomeCofinalVacuumSectorMassNormalizedRootTrafficCapacity

end YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRootTrafficCapacity

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRootTrafficCapacity.CentralPhysicalFiniteVacuumSectorMassNormalizedRootTrafficCapacityAt.toConditionalVarianceGapData
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRootTrafficCapacity.centralPhysicalFiniteVacuumSectorMassNormalizedRootFiniteCapacityAt
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRootTrafficCapacity.FixedNomeCofinalVacuumSectorMassNormalizedRootTrafficCapacity.toCofinalConditionalVarianceFraction
