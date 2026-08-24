/-
# A uniform positive mass floor for every fixed physical BF4 vacuum sector

For any fixed nome `0 < w < 1` and half-extent, finite index zero is the
all-zero lower state and belongs to the canonical vacuum sector at every
representation cutoff.  The generic uniform positive-row theorem supplies
one fixed positive stationary weight for that state beyond an explicit
cutoff.  Nonnegativity of all other sector weights makes the same number a
uniform lower bound for the complete vacuum-sector mass.

The result is specialized to the strong-coupling spin-cube anchor
`w = 1/400`.  This closes the mass-floor lane at that fixed coupling; the
cutoff-uniform full-sector root-traffic capacity remains the analytic gap
frontier.  No continuum limit, continuum QFT, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
import YMGap.Continuum.Z4StrongCouplingParametricAnchor

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

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

/-! ## 1. Generic fixed-nome sector-mass floor -/

def centralPhysicalFiniteVacuumSectorUniformMassFloor
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Q' :=
  centralPhysicalUniformPositiveRowFloor w hw half

def centralPhysicalFiniteVacuumSectorUniformMassFloorAnchor
    (w : Q') (half : Nat) : Nat :=
  centralPhysicalUniformRowFloorCutoff w half

theorem centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorUniformMassFloor w hw half := by
  unfold centralPhysicalFiniteVacuumSectorUniformMassFloor
  exact centralPhysicalUniformPositiveRowFloor_pos w hw half

private theorem zero_mem_uniformAnchorPositiveCarrier
    {w : Q'} (hw0 : (0 : Q') < w) (half : Nat) :
    zeroEdgeLabelling ∈ centralPositiveHalfStates
      w (Q'.le_of_lt hw0)
      (centralPhysicalFiniteVacuumSectorUniformMassFloorAnchor w half)
      half := by
  obtain ⟨tail, hstates⟩ :=
    centralPositiveHalfStates_starts_vacuum
      w (Q'.le_of_lt hw0)
      (centralPhysicalFiniteVacuumSectorUniformMassFloorAnchor w half)
      half
  rw [hstates]
  exact List.mem_cons_self

/-- One explicit positive number lies below the complete canonical
vacuum-sector mass at every later representation cutoff. -/
theorem centralPhysicalFiniteVacuumSectorUniformMassFloor_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {K : Nat}
    (hK : centralPhysicalFiniteVacuumSectorUniformMassFloorAnchor
      w half ≤ K) :
    centralPhysicalFiniteVacuumSectorUniformMassFloor
        w (Q'.le_of_lt hw0) half ≤
      centralPhysicalFiniteVacuumSectorMass
        w (Q'.le_of_lt hw0) K half := by
  have hrow := centralPhysicalUniformPositiveRowFloor_le
    hw0 hw1 half hK
    (zero_mem_uniformAnchorPositiveCarrier hw0 half)
  have hzeroWeight :
      centralPhysicalFiniteVacuumSectorUniformMassFloor
          w (Q'.le_of_lt hw0) half ≤
        centralPhysicalFiniteWeight
          w (Q'.le_of_lt hw0) K half 0 := by
    unfold centralPhysicalFiniteVacuumSectorUniformMassFloor
      centralPhysicalFiniteWeight
    rw [centralPhysicalFiniteStateAt_zero_eq_vacuum]
    exact hrow
  have hmember := listQSum_member_le_nonnegative_local
    (centralPhysicalFiniteWeight w (Q'.le_of_lt hw0) K half)
    (fun index => by
      unfold centralPhysicalFiniteWeight
      exact centralPhysicalRowMarginal_nonnegative
        (Q'.le_of_lt hw0) K half _)
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) K half)
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) K half)
  unfold centralPhysicalFiniteVacuumSectorMass finiteWeightedMass
  exact Q'.le_trans' _ _ _ hzeroWeight hmember

/-! ## 2. Strong-coupling spin-cube anchor -/

def anchorCentralPhysicalFiniteVacuumSectorUniformMassFloor : Q' :=
  centralPhysicalFiniteVacuumSectorUniformMassFloor
    anchorCoupling (by decide) 0

def anchorCentralPhysicalFiniteVacuumSectorUniformMassFloorAnchor : Nat :=
  centralPhysicalFiniteVacuumSectorUniformMassFloorAnchor anchorCoupling 0

theorem anchorCentralPhysicalFiniteVacuumSectorUniformMassFloor_pos :
    (0 : Q') <
      anchorCentralPhysicalFiniteVacuumSectorUniformMassFloor := by
  exact centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
    anchorCoupling (by decide) 0

theorem anchorCentralPhysicalFiniteVacuumSectorUniformMassFloor_le
    {K : Nat}
    (hK : anchorCentralPhysicalFiniteVacuumSectorUniformMassFloorAnchor ≤ K) :
    anchorCentralPhysicalFiniteVacuumSectorUniformMassFloor ≤
      centralPhysicalFiniteVacuumSectorMass
        anchorCoupling (by decide) K 0 := by
  exact centralPhysicalFiniteVacuumSectorUniformMassFloor_le
    (w := anchorCoupling) (by decide) (by decide) 0 hK

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor.centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor.centralPhysicalFiniteVacuumSectorUniformMassFloor_le
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor.anchorCentralPhysicalFiniteVacuumSectorUniformMassFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor.anchorCentralPhysicalFiniteVacuumSectorUniformMassFloor_le
