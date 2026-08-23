/-
# A uniform positive mass floor for the cutoff-two vacuum sector

The canonical vacuum sector always contains finite index zero, and finite
index zero is literally the all-zero lower boundary state.  The existing
uniform positive-row theorem supplies one fixed positive stationary weight
for that state at every sufficiently large representation cutoff.  Since the
sector mass is a sum of nonnegative weights containing index zero, the same
constant is a uniform positive sector-mass floor.

This closes the mass-floor input of the degree-24 simple-path congestion
compiler.  The cost-scaled positive-edge floor remains open.  No completed
gap inhabitant, thermodynamic/continuum limit, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad
import YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A nonnegative member lies below the full finite sum -/

private theorem listQSum_member_le_nonnegative_local
    {State : Type} (value : State → Q')
    (hvalue : ∀ state, (0 : Q') ≤ value state) :
    ∀ (states : List State) {selected : State},
      selected ∈ states → value selected ≤ listQSum value states
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | first :: rest, selected, hmem => by
      rcases List.mem_cons.mp hmem with hfirst | hrest
      · subst selected
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on value rest
            (fun state _ => hvalue state))
      · have htail := listQSum_member_le_nonnegative_local
          value hvalue rest hrest
        have hpad : listQSum value rest ≤
            value first + listQSum value rest := by
          have hadd := Q'.add_le_add_right
            (0 : Q') (value first) (listQSum value rest)
            (hvalue first)
          rwa [Q'.zero_add'] at hadd
        exact Q'.le_trans' _ _ _ htail hpad

/-! ## 2. The all-zero row supplies a uniform sector-mass floor -/

def cutoffTwoUniformVacuumSectorMassFloor : Q' :=
  centralPhysicalUniformPositiveRowFloor
    cutoffTwoHalfCoupling (by decide) 0

theorem cutoffTwoUniformVacuumSectorMassFloor_pos :
    (0 : Q') < cutoffTwoUniformVacuumSectorMassFloor :=
  centralPhysicalUniformPositiveRowFloor_pos
    cutoffTwoHalfCoupling (by decide) 0

def cutoffTwoUniformVacuumSectorMassFloorAnchor : Nat :=
  max 2 (centralPhysicalUniformRowFloorCutoff
    cutoffTwoHalfCoupling 0)

theorem cutoffTwoUniformVacuumSectorMassFloorAnchor_ge_two :
    2 ≤ cutoffTwoUniformVacuumSectorMassFloorAnchor := by
  unfold cutoffTwoUniformVacuumSectorMassFloorAnchor
  exact Nat.le_max_left _ _

theorem cutoffTwoUniformRowFloorCutoff_le_massFloorAnchor :
    centralPhysicalUniformRowFloorCutoff cutoffTwoHalfCoupling 0 ≤
      cutoffTwoUniformVacuumSectorMassFloorAnchor := by
  unfold cutoffTwoUniformVacuumSectorMassFloorAnchor
  exact Nat.le_max_right _ _

private theorem zero_mem_uniformAnchorPositiveCarrier :
    zeroEdgeLabelling ∈ centralPositiveHalfStates
      cutoffTwoHalfCoupling (by decide)
      (centralPhysicalUniformRowFloorCutoff
        cutoffTwoHalfCoupling 0) 0 := by
  obtain ⟨tail, hstates⟩ :=
    centralPositiveHalfStates_starts_vacuum
      cutoffTwoHalfCoupling (by decide)
      (centralPhysicalUniformRowFloorCutoff
        cutoffTwoHalfCoupling 0) 0
  rw [hstates]
  exact List.mem_cons_self

theorem cutoffTwoUniformVacuumSectorMassFloor_le
    {later : Nat}
    (hlater : cutoffTwoUniformVacuumSectorMassFloorAnchor ≤ later) :
    cutoffTwoUniformVacuumSectorMassFloor ≤
      centralPhysicalFiniteVacuumSectorMass
        cutoffTwoHalfCoupling (by decide) later 0 := by
  have hrowCutoff :
      centralPhysicalUniformRowFloorCutoff cutoffTwoHalfCoupling 0 ≤ later :=
    Nat.le_trans cutoffTwoUniformRowFloorCutoff_le_massFloorAnchor hlater
  have hrow := centralPhysicalUniformPositiveRowFloor_le
    (w := cutoffTwoHalfCoupling)
    (by decide : (0 : Q') < cutoffTwoHalfCoupling)
    (by decide : cutoffTwoHalfCoupling < (1 : Q'))
    0 hrowCutoff zero_mem_uniformAnchorPositiveCarrier
  have hzeroWeight : cutoffTwoUniformVacuumSectorMassFloor ≤
      centralPhysicalFiniteWeight
        cutoffTwoHalfCoupling (by decide) later 0 0 := by
    unfold cutoffTwoUniformVacuumSectorMassFloor
      centralPhysicalFiniteWeight
    rw [centralPhysicalFiniteStateAt_zero_eq_vacuum]
    exact hrow
  have hmember := listQSum_member_le_nonnegative_local
    (centralPhysicalFiniteWeight
      cutoffTwoHalfCoupling (by decide) later 0)
    (fun index => by
      unfold centralPhysicalFiniteWeight
      exact centralPhysicalRowMarginal_nonnegative
        (by decide) later 0 _)
    (centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) later 0)
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) later 0)
  unfold centralPhysicalFiniteVacuumSectorMass finiteWeightedMass
  exact Q'.le_trans' _ _ _ hzeroWeight hmember

/-! ## 3. Remove the mass-floor hypothesis from the degree-24 compiler -/

structure CutoffTwoCofinalAmbientLinearEdgeRatio
    (effectiveFloor : Q') : Type 1 where
  effective_floor_pos : (0 : Q') < effectiveFloor
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max cutoffTwoUniformVacuumSectorMassFloorAnchor request ≤
      anchor request
  ratio_bound : ∀ request,
    effectiveFloor *
        cutoffTwoAmbientLinearFullSectorCost (anchor request) ≤
      centralPhysicalFiniteVacuumSectorEdgeFloor
        cutoffTwoHalfCoupling (by decide) (anchor request) 0

namespace CutoffTwoCofinalAmbientLinearEdgeRatio

def toAmbientLinearFullSectorRatio
    {effectiveFloor : Q'}
    (family : CutoffTwoCofinalAmbientLinearEdgeRatio effectiveFloor) :
    CutoffTwoCofinalAmbientLinearFullSectorRatio
      effectiveFloor cutoffTwoUniformVacuumSectorMassFloor where
  effective_floor_pos := family.effective_floor_pos
  mass_floor_pos := cutoffTwoUniformVacuumSectorMassFloor_pos
  anchor := family.anchor
  anchor_ge := fun request => by
    have hfamily := family.anchor_ge request
    have htwo := cutoffTwoUniformVacuumSectorMassFloorAnchor_ge_two
    omega
  mass_floor_le := fun request =>
    cutoffTwoUniformVacuumSectorMassFloor_le
      (Nat.le_trans
        (Nat.le_max_left
          cutoffTwoUniformVacuumSectorMassFloorAnchor request)
        (family.anchor_ge request))
  ratio_bound := family.ratio_bound

def toCompletedStrictContractionData
    {effectiveFloor : Q'}
    (family : CutoffTwoCofinalAmbientLinearEdgeRatio effectiveFloor) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  family.toAmbientLinearFullSectorRatio
    |>.toCompletedStrictContractionData

end CutoffTwoCofinalAmbientLinearEdgeRatio

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor.cutoffTwoUniformVacuumSectorMassFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor.cutoffTwoUniformVacuumSectorMassFloor_le
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor.CutoffTwoCofinalAmbientLinearEdgeRatio.toCompletedStrictContractionData
