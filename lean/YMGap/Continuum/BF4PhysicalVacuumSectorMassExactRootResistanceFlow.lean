/-
# Exact-mass resistance flow for the full BF4 vacuum sector

The generic pairwise-to-root identity contains the component mass exactly:

    pairwiseVariance <=
      componentMass * rootVariance + componentMass * rootVariance.

The earlier full-sector root compilers used the weaker consequence obtained
from `componentMass <= 1`, and subsequently had to divide aggregate traffic
by the component mass to recover a normalized Poincare estimate.  This module
retains the exact mass before applying the already-constructed resistance
flow.  The mass then appears on both sides of normalized Poincare coercivity,
so the sufficient edge condition becomes simply

    fraction * resistanceFlowLoad(source,target) <= 1.

No division by component mass and no global minimum physical edge remains.
Every finite cutoff has an explicit positive fraction.  The sole cofinal
frontier exposed here is a uniform bound on the raw dimensionless resistance
congestion itself.

No cofinal congestion bound, thermodynamic or continuum limit, continuum
QFT, or Clay conclusion is asserted.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRootResistanceFlow

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassExactRootResistanceFlow

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedPairwiseGapBridge
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRootResistanceFlow
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem centralPhysicalFiniteWeight_nonnegative_local
    (w : Q') (hw : (0 : Q') ≤ w) (K half state : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteWeight w hw K half state := by
  exact centralPhysicalRowMarginal_nonnegative hw K half
    (centralPhysicalFiniteStateAt w hw K half state)

private theorem q_min_pos_local {left right : Q'}
    (hleft : (0 : Q') < left) (hright : (0 : Q') < right) :
    (0 : Q') < Q'.min' left right := by
  unfold Q'.min'
  by_cases horder : left ≤ right
  · rw [if_pos horder]
    exact hleft
  · rw [if_neg horder]
    exact hright

private theorem recipPos_mul_eqv_one_local
    (value : Q') (hvalue : (0 : Q') < value) :
    Q'.recipPos value hvalue * value ≈ 1 := by
  exact Q'.eqv_trans _ (value * Q'.recipPos value hvalue) _
    (Q'.mul_comm_eqv _ _)
    (Q'.mul_recipPos_eqv value hvalue)

private theorem fraction_mul_mass_mul_eqv_mass_mul_fraction_mul_local
    (fraction mass value : Q') :
    fraction * (mass * value) ≈ mass * (fraction * value) := by
  refine Q'.eqv_trans _ ((fraction * mass) * value) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv fraction mass value)) ?_
  refine Q'.eqv_trans _ ((mass * fraction) * value) _
    (Q'.mul_eqv_congr_right _ _ value
      (Q'.mul_comm_eqv fraction mass)) ?_
  exact Q'.mul_assoc_eqv mass fraction value

/-! ## 1. Preserve the exact component mass through resistance routing -/

theorem centralPhysicalFiniteVacuumSectorRootVariance_le_rootResistanceSingleRawBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorRootVariance
        w hw K half coefficient ≤
      centralPhysicalFiniteVacuumSectorRootResistanceSingleRawBudget
        w hw K half coefficient := by
  unfold centralPhysicalFiniteVacuumSectorRootVariance
    finiteWeightedRootVariance
    centralPhysicalFiniteVacuumSectorRootResistanceSingleRawBudget
  apply listQSum_mono
  intro state hstate
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (centralPhysicalFiniteVacuumSector_root_sq_le_resistancePathBudget
      w hw K half coefficient state hstate)
    (centralPhysicalFiniteWeight_nonnegative_local w hw K half state)

theorem centralPhysicalFiniteVacuumSectorPairwiseVariance_le_mass_mul_rootResistanceRawBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorPairwiseVariance
        w hw K half coefficient ≤
      centralPhysicalFiniteVacuumSectorMass w hw K half *
        centralPhysicalFiniteVacuumSectorRootResistanceRawBudget
          w hw K half coefficient := by
  let states := centralPhysicalFiniteVacuumSectorIndices w hw K half
  let weight := centralPhysicalFiniteWeight w hw K half
  let mass := centralPhysicalFiniteVacuumSectorMass w hw K half
  let root := centralPhysicalFiniteVacuumSectorRootVariance
    w hw K half coefficient
  let single :=
    centralPhysicalFiniteVacuumSectorRootResistanceSingleRawBudget
      w hw K half coefficient
  have hexact :=
    finiteWeightedPairwiseVariance_le_twice_mass_rootVariance
      states weight coefficient 0
  have hroot : root ≤ single := by
    unfold root single
    exact
      centralPhysicalFiniteVacuumSectorRootVariance_le_rootResistanceSingleRawBudget
        w hw K half coefficient
  have hmass0 : (0 : Q') ≤ mass := by
    exact Q'.le_of_lt
      (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw K half)
  have hscaled : mass * root ≤ mass * single :=
    Q'.mul_le_mul_of_nonneg_left _ _ mass hroot hmass0
  refine Q'.le_trans' _ (mass * root + mass * root) _ ?_ ?_
  · simpa only [states, weight, mass, root,
      centralPhysicalFiniteVacuumSectorPairwiseVariance,
      centralPhysicalFiniteVacuumSectorMass] using hexact
  · refine Q'.le_trans' _ (mass * single + mass * single) _
      (Q'.add_le_add hscaled hscaled) ?_
    unfold centralPhysicalFiniteVacuumSectorRootResistanceRawBudget
      single
    exact Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.mul_add_eqv mass
          (centralPhysicalFiniteVacuumSectorRootResistanceSingleRawBudget
            w hw K half coefficient)
          (centralPhysicalFiniteVacuumSectorRootResistanceSingleRawBudget
            w hw K half coefficient)))

/-- This is the load-bearing strengthening: the full pairwise variance is
bounded by the component mass times the already-constructed resistance-loaded
Dirichlet form. -/
theorem centralPhysicalFiniteVacuumSectorPairwiseVariance_le_mass_mul_rootResistanceRawLoadedDirichlet
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorPairwiseVariance
        w hw K half coefficient ≤
      centralPhysicalFiniteVacuumSectorMass w hw K half *
        centralPhysicalFiniteVacuumSectorRootResistanceRawLoadedDirichlet
          w hw K half coefficient := by
  let mass := centralPhysicalFiniteVacuumSectorMass w hw K half
  have hraw :=
    centralPhysicalFiniteVacuumSectorPairwiseVariance_le_mass_mul_rootResistanceRawBudget
      w hw K half coefficient
  have hbudget :
      centralPhysicalFiniteVacuumSectorRootResistanceRawBudget
          w hw K half coefficient ≈
        centralPhysicalFiniteVacuumSectorRootResistanceRawLoadedDirichlet
          w hw K half coefficient := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (centralPhysicalFiniteVacuumSectorRootResistanceRawOccurrenceEnergy_eqv_rawBudget
          w hw K half coefficient))
      (Q'.eqv_symm
        (centralPhysicalFiniteVacuumSectorRootResistanceRawLoadedDirichlet_eqv_occurrenceEnergy
          w hw K half coefficient))
  exact Q'.le_trans' _
    (mass *
      centralPhysicalFiniteVacuumSectorRootResistanceRawBudget
        w hw K half coefficient) _ hraw
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left mass _ _ hbudget))

/-! ## 2. Raw resistance capacity gives mass-normalized Poincare -/

structure CentralPhysicalFiniteVacuumSectorMassExactRootResistanceFlowCapacityAt
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) : Type 1 where
  fraction : Q'
  fraction_pos : (0 : Q') < fraction
  fraction_le_one : fraction ≤ (1 : Q')
  edge_capacity : ∀ source target,
    fraction *
        centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
          w (Q'.le_of_lt hw) K half source target ≤
      1

private theorem finiteJointDirichletBlock_scale_joint_local
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (scale : Q') (joint : State → State → Q') :
    finiteJointDirichletBlock leftStates rightStates coefficient
        (fun left right => scale * joint left right) ≈
      scale * finiteJointDirichletBlock
        leftStates rightStates coefficient joint := by
  unfold finiteJointDirichletBlock
  refine Q'.eqv_trans _
    (listQSum
      (fun left => scale * listQSum
        (fun right =>
          joint left right *
            ((coefficient left + -coefficient right) *
              (coefficient left + -coefficient right)))
        rightStates)
      leftStates) _ ?_ ?_
  · apply listQSum_congr
    intro left
    refine Q'.eqv_trans _
      (listQSum
        (fun right => scale *
          (joint left right *
            ((coefficient left + -coefficient right) *
              (coefficient left + -coefficient right))))
        rightStates) _ ?_ ?_
    · apply listQSum_congr
      intro right
      exact Q'.mul_assoc_eqv _ _ _
    · exact listQSum_mul_left scale _ rightStates
  · exact listQSum_mul_left scale _ leftStates

namespace CentralPhysicalFiniteVacuumSectorMassExactRootResistanceFlowCapacityAt

private theorem fraction_mul_loadedDirichlet_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    (capacity :
      CentralPhysicalFiniteVacuumSectorMassExactRootResistanceFlowCapacityAt
        hw K half)
    (coefficient : Nat → Q') :
    capacity.fraction *
        centralPhysicalFiniteVacuumSectorRootResistanceRawLoadedDirichlet
          w (Q'.le_of_lt hw) K half coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K half)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K half) := by
  let states := centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw) K half
  let load := centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
    w (Q'.le_of_lt hw) K half
  let kernel := centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K half
  unfold centralPhysicalFiniteVacuumSectorRootResistanceRawLoadedDirichlet
    finiteWeightedOccurrenceLoadedDirichlet
  change capacity.fraction *
      finiteJointDirichletBlock states states coefficient
        (fun source target => load source target * kernel source target) ≤
    finiteJointDirichletBlock states states coefficient kernel
  refine Q'.le_trans' _
    (finiteJointDirichletBlock states states coefficient
      (fun source target =>
        capacity.fraction *
          (load source target * kernel source target))) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.eqv_symm
        (finiteJointDirichletBlock_scale_joint_local
          states states coefficient capacity.fraction
          (fun source target => load source target * kernel source target)))
  · unfold finiteJointDirichletBlock
    apply listQSum_mono
    intro source _hsource
    apply listQSum_mono
    intro target _htarget
    have hkernel0 : (0 : Q') ≤ kernel source target := by
      unfold kernel centralPhysicalFiniteKernel
      exact centralNormalizedPhysicalReflectedKernel_nonnegative
        (Q'.le_of_lt hw) K half _ _
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
      (kernel source target)
      (capacity.edge_capacity source target) hkernel0
    have hjoint :
        capacity.fraction *
            (load source target * kernel source target) ≤
          kernel source target := by
      exact Q'.le_trans' _
        ((capacity.fraction * load source target) * kernel source target) _
        (Q'.le_of_eqv
          (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
        (Q'.le_trans' _ (1 * kernel source target) _ hscaled
          (Q'.le_of_eqv (Q'.one_mul_eqv _)))
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hjoint
      (SumOfSquares.q_mul_self_nonneg
        (coefficient source + -coefficient target))

def toMassNormalizedPairwiseCoercivityData
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    (capacity :
      CentralPhysicalFiniteVacuumSectorMassExactRootResistanceFlowCapacityAt
        hw K half) :
    CentralPhysicalFiniteMassNormalizedPairwiseCoercivityData
      w (Q'.le_of_lt hw) K half where
  fraction := capacity.fraction
  fraction_pos := capacity.fraction_pos
  fraction_le_one := capacity.fraction_le_one
  coercivity := fun coefficient => by
    let mass := centralPhysicalFiniteVacuumSectorMass
      w (Q'.le_of_lt hw) K half
    let loaded :=
      centralPhysicalFiniteVacuumSectorRootResistanceRawLoadedDirichlet
        w (Q'.le_of_lt hw) K half coefficient
    let dirichlet := finiteJointDirichletEnergy
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K half)
      coefficient
      (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K half)
    have hpairwise :
        centralPhysicalFiniteVacuumSectorPairwiseVariance
            w (Q'.le_of_lt hw) K half coefficient ≤
          mass * loaded := by
      unfold mass loaded
      exact
        centralPhysicalFiniteVacuumSectorPairwiseVariance_le_mass_mul_rootResistanceRawLoadedDirichlet
          w (Q'.le_of_lt hw) K half coefficient
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ capacity.fraction
      hpairwise (Q'.le_of_lt capacity.fraction_pos)
    have hlocal : capacity.fraction * loaded ≤ dirichlet := by
      unfold loaded dirichlet
      exact capacity.fraction_mul_loadedDirichlet_le_physicalDirichlet
        coefficient
    have hmass0 : (0 : Q') ≤ mass := by
      unfold mass
      exact Q'.le_of_lt
        (centralPhysicalFiniteVacuumSectorWeightSum_pos
          w (Q'.le_of_lt hw) K half)
    have hmassScaled := Q'.mul_le_mul_of_nonneg_left _ _ mass
      hlocal hmass0
    exact Q'.le_trans' _ (capacity.fraction * (mass * loaded)) _
      hscaled
      (Q'.le_trans' _ (mass * (capacity.fraction * loaded)) _
        (Q'.le_of_eqv
          (fraction_mul_mass_mul_eqv_mass_mul_fraction_mul_local
            capacity.fraction mass loaded))
        hmassScaled)

def toConditionalVarianceGapData
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    (capacity :
      CentralPhysicalFiniteVacuumSectorMassExactRootResistanceFlowCapacityAt
        hw K half) :=
  capacity.toMassNormalizedPairwiseCoercivityData
    |>.toConditionalVarianceGapData

end CentralPhysicalFiniteVacuumSectorMassExactRootResistanceFlowCapacityAt

/-! ## 3. Finite and cofinal raw-congestion certificates -/

def centralPhysicalFiniteVacuumSectorRootResistanceRawTrafficCost
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : Q' :=
  1 + centralPhysicalFiniteVacuumSectorRootResistanceTotalTraffic
    w hw K half

theorem centralPhysicalFiniteVacuumSectorRootResistanceRawTrafficCost_pos
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorRootResistanceRawTrafficCost
        w hw K half := by
  unfold centralPhysicalFiniteVacuumSectorRootResistanceRawTrafficCost
  exact Q'.pos_add_nonneg (by decide)
    (centralPhysicalFiniteVacuumSectorRootResistanceTotalTraffic_nonnegative
      w hw K half)

def centralPhysicalFiniteVacuumSectorRootResistanceMassExactFiniteFraction
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) : Q' :=
  let cost := centralPhysicalFiniteVacuumSectorRootResistanceRawTrafficCost
    w (Q'.le_of_lt hw) K half
  Q'.min' 1
    (Q'.recipPos cost
      (centralPhysicalFiniteVacuumSectorRootResistanceRawTrafficCost_pos
        w (Q'.le_of_lt hw) K half))

theorem centralPhysicalFiniteVacuumSectorRootResistanceMassExactFiniteFraction_pos
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorRootResistanceMassExactFiniteFraction
        hw K half := by
  unfold
    centralPhysicalFiniteVacuumSectorRootResistanceMassExactFiniteFraction
  exact q_min_pos_local (by decide) (Q'.recipPos_pos _ _)

theorem centralPhysicalFiniteVacuumSectorRootResistanceMassExactFiniteFraction_le_one
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) :
    centralPhysicalFiniteVacuumSectorRootResistanceMassExactFiniteFraction
        hw K half ≤ 1 := by
  unfold
    centralPhysicalFiniteVacuumSectorRootResistanceMassExactFiniteFraction
  exact Q'.min_le_left' _ _

theorem centralPhysicalFiniteVacuumSectorRootResistanceMassExactFiniteFraction_mul_flowLoad_le_one
    {w : Q'} (hw : (0 : Q') < w) (K half source target : Nat) :
    centralPhysicalFiniteVacuumSectorRootResistanceMassExactFiniteFraction
          hw K half *
        centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
          w (Q'.le_of_lt hw) K half source target ≤
      1 := by
  let total := centralPhysicalFiniteVacuumSectorRootResistanceTotalTraffic
    w (Q'.le_of_lt hw) K half
  let cost := centralPhysicalFiniteVacuumSectorRootResistanceRawTrafficCost
    w (Q'.le_of_lt hw) K half
  let reciprocal := Q'.recipPos cost
    (centralPhysicalFiniteVacuumSectorRootResistanceRawTrafficCost_pos
      w (Q'.le_of_lt hw) K half)
  let fraction :=
    centralPhysicalFiniteVacuumSectorRootResistanceMassExactFiniteFraction
      hw K half
  let load := centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
    w (Q'.le_of_lt hw) K half source target
  have hloadTotal : load ≤ total := by
    unfold load total
    exact centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad_le_totalTraffic
      w (Q'.le_of_lt hw) K half source target
  have htotalCost : total ≤ cost := by
    unfold cost centralPhysicalFiniteVacuumSectorRootResistanceRawTrafficCost
    have hadd := Q'.add_le_add_right (0 : Q') 1 total
      (by decide : (0 : Q') ≤ 1)
    rwa [Q'.zero_add'] at hadd
  have hfraction : fraction ≤ reciprocal := by
    unfold fraction
      centralPhysicalFiniteVacuumSectorRootResistanceMassExactFiniteFraction
      reciprocal cost
    exact Q'.min_le_right' _ _
  have hload0 : (0 : Q') ≤ load := by
    unfold load
    exact centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad_nonnegative
      w (Q'.le_of_lt hw) K half source target
  have hreciprocal0 : (0 : Q') ≤ reciprocal := by
    unfold reciprocal
    exact Q'.le_of_lt (Q'.recipPos_pos _ _)
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ load
    hfraction hload0
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ reciprocal
    (Q'.le_trans' _ _ _ hloadTotal htotalCost) hreciprocal0
  exact Q'.le_trans' _ (reciprocal * load) _ hfirst
    (Q'.le_trans' _ (reciprocal * cost) _ hsecond
      (Q'.le_of_eqv
        (recipPos_mul_eqv_one_local cost
          (centralPhysicalFiniteVacuumSectorRootResistanceRawTrafficCost_pos
            w (Q'.le_of_lt hw) K half))))

def centralPhysicalFiniteVacuumSectorMassExactRootResistanceFiniteCapacityAt
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) :
    CentralPhysicalFiniteVacuumSectorMassExactRootResistanceFlowCapacityAt
      hw K half where
  fraction :=
    centralPhysicalFiniteVacuumSectorRootResistanceMassExactFiniteFraction
      hw K half
  fraction_pos :=
    centralPhysicalFiniteVacuumSectorRootResistanceMassExactFiniteFraction_pos
      hw K half
  fraction_le_one :=
    centralPhysicalFiniteVacuumSectorRootResistanceMassExactFiniteFraction_le_one
      hw K half
  edge_capacity := fun source target =>
    centralPhysicalFiniteVacuumSectorRootResistanceMassExactFiniteFraction_mul_flowLoad_le_one
      hw K half source target

structure FixedNomeCofinalVacuumSectorMassExactRootResistanceCongestionBound
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  bound : Q'
  bound_nonnegative : (0 : Q') ≤ bound
  flowLoad_le : ∀ K, start ≤ K → ∀ source target,
    centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
        w (Q'.le_of_lt hw) K 0 source target ≤
      bound

namespace FixedNomeCofinalVacuumSectorMassExactRootResistanceCongestionBound

def cost
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactRootResistanceCongestionBound hw) :
    Q' :=
  1 + family.bound

theorem cost_pos
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactRootResistanceCongestionBound hw) :
    (0 : Q') < family.cost := by
  unfold cost
  exact Q'.pos_add_nonneg (by decide) family.bound_nonnegative

def fraction
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactRootResistanceCongestionBound hw) :
    Q' :=
  Q'.min' 1 (Q'.recipPos family.cost family.cost_pos)

theorem fraction_pos
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactRootResistanceCongestionBound hw) :
    (0 : Q') < family.fraction := by
  unfold fraction
  exact q_min_pos_local (by decide) (Q'.recipPos_pos _ _)

theorem fraction_le_one
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactRootResistanceCongestionBound hw) :
    family.fraction ≤ (1 : Q') := by
  unfold fraction
  exact Q'.min_le_left' _ _

theorem flowLoad_le_cost
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactRootResistanceCongestionBound hw)
    {K : Nat} (hK : family.start ≤ K) (source target : Nat) :
    centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
        w (Q'.le_of_lt hw) K 0 source target ≤
      family.cost := by
  have hbound := family.flowLoad_le K hK source target
  have hadd := Q'.add_le_add_right (0 : Q') 1 family.bound
    (by decide : (0 : Q') ≤ 1)
  have hboundCost : family.bound ≤ family.cost := by
    unfold cost
    rwa [Q'.zero_add'] at hadd
  exact Q'.le_trans' _ _ _ hbound hboundCost

theorem fraction_mul_flowLoad_le_one
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactRootResistanceCongestionBound hw)
    {K : Nat} (hK : family.start ≤ K) (source target : Nat) :
    family.fraction *
        centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
          w (Q'.le_of_lt hw) K 0 source target ≤
      1 := by
  let reciprocal := Q'.recipPos family.cost family.cost_pos
  let load := centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
    w (Q'.le_of_lt hw) K 0 source target
  have hfraction : family.fraction ≤ reciprocal := by
    unfold fraction reciprocal
    exact Q'.min_le_right' _ _
  have hload0 : (0 : Q') ≤ load := by
    unfold load
    exact centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad_nonnegative
      w (Q'.le_of_lt hw) K 0 source target
  have hreciprocal0 : (0 : Q') ≤ reciprocal := by
    unfold reciprocal
    exact Q'.le_of_lt (Q'.recipPos_pos _ _)
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ load
    hfraction hload0
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ reciprocal
    (family.flowLoad_le_cost hK source target) hreciprocal0
  exact Q'.le_trans' _ (reciprocal * load) _ hfirst
    (Q'.le_trans' _ (reciprocal * family.cost) _ hsecond
      (Q'.le_of_eqv
        (recipPos_mul_eqv_one_local family.cost family.cost_pos)))

def finiteCapacityAt
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactRootResistanceCongestionBound hw)
    (K : Nat) (hK : family.start ≤ K) :
    CentralPhysicalFiniteVacuumSectorMassExactRootResistanceFlowCapacityAt
      hw K 0 where
  fraction := family.fraction
  fraction_pos := family.fraction_pos
  fraction_le_one := family.fraction_le_one
  edge_capacity := fun source target =>
    family.fraction_mul_flowLoad_le_one hK source target

def toCofinalMassNormalizedPairwiseCoercivity
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactRootResistanceCongestionBound hw) :
    FixedNomeCofinalMassNormalizedPairwiseCoercivity hw where
  start := family.start
  fraction := family.fraction
  fraction_pos := family.fraction_pos
  fraction_le_one := family.fraction_le_one
  coercivity := fun K hK coefficient =>
    (family.finiteCapacityAt K hK).toMassNormalizedPairwiseCoercivityData
      |>.coercivity coefficient

def toCofinalConditionalVarianceFraction
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactRootResistanceCongestionBound hw) :=
  family.toCofinalMassNormalizedPairwiseCoercivity
    |>.toCofinalConditionalVarianceFraction

end FixedNomeCofinalVacuumSectorMassExactRootResistanceCongestionBound

end YMGap.Continuum.BF4PhysicalVacuumSectorMassExactRootResistanceFlow

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactRootResistanceFlow.centralPhysicalFiniteVacuumSectorPairwiseVariance_le_mass_mul_rootResistanceRawLoadedDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactRootResistanceFlow.CentralPhysicalFiniteVacuumSectorMassExactRootResistanceFlowCapacityAt.toMassNormalizedPairwiseCoercivityData
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactRootResistanceFlow.centralPhysicalFiniteVacuumSectorMassExactRootResistanceFiniteCapacityAt
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactRootResistanceFlow.FixedNomeCofinalVacuumSectorMassExactRootResistanceCongestionBound.toCofinalConditionalVarianceFraction
