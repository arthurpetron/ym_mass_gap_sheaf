/-
# Fixed-nome rooted coercivity gives a cofinal posterior gap

At one fixed nome `0 < w < 1`, combine three exact inputs:

* a cutoff-uniform off-ray rooted coercivity strength;
* a cutoff-uniform ray capacity;
* the already-proved positive mass floor for the canonical component.

The resulting cofinal posterior-variance fraction is

    min 1 (massFloor * rootedStrength).

Thus the rooted resistance route really reaches the completed-transfer gap
compiler at fixed nome.  The mass floor is load-bearing.  This file makes no
claim that this fraction has the required asymptotically-free scaling as the
nome approaches one; that comparison remains open.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor
import YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath
import YMGap.Continuum.BF4PhysicalVacuumSectorPairwiseCoercivityGapBridge

namespace YMGap.Continuum.BF4PhysicalVacuumSectorRootCoercivityCofinalGapBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor
open YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVariance
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVarianceGapBridge
open YMGap.Continuum.BF4PhysicalVacuumSectorPairwiseCoercivityGapBridge

private theorem q_min_pos_local {left right : Q'}
    (hleft : (0 : Q') < left) (hright : (0 : Q') < right) :
    (0 : Q') < Q'.min' left right := by
  unfold Q'.min'
  by_cases horder : left ≤ right
  · rw [if_pos horder]
    exact hleft
  · rw [if_neg horder]
    exact hright

/-- One schedule beyond all three cutoff anchors. -/
def rootedCofinalGapAnchor
    {w : Q'} {hw : (0 : Q') < w}
    (offRay : FixedNomeCofinalSpinCubeOffRayRootCoercivity hw)
    (ray : FixedNomeCofinalSpinCubeRayCapacity hw)
    (request : Nat) : Nat :=
  Nat.max request
    (Nat.max (Nat.max offRay.start ray.start)
      (centralPhysicalFiniteVacuumSectorUniformMassFloorAnchor w 0))

/-- The explicit fixed-nome posterior fraction supplied by the rooted route. -/
def rootedCofinalGapFraction
    {w : Q'} {hw : (0 : Q') < w}
    (offRay : FixedNomeCofinalSpinCubeOffRayRootCoercivity hw)
    (ray : FixedNomeCofinalSpinCubeRayCapacity hw) : Q' :=
  Q'.min' 1
    (centralPhysicalFiniteVacuumSectorUniformMassFloor
        w (Q'.le_of_lt hw) 0 *
      offRay.compiledStrength ray)

theorem rootedCofinalGapFraction_pos
    {w : Q'} {hw : (0 : Q') < w}
    (offRay : FixedNomeCofinalSpinCubeOffRayRootCoercivity hw)
    (ray : FixedNomeCofinalSpinCubeRayCapacity hw) :
    (0 : Q') < rootedCofinalGapFraction offRay ray := by
  unfold rootedCofinalGapFraction
  apply q_min_pos_local (by decide)
  exact Q'.mul_pos
    (centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
      w (Q'.le_of_lt hw) 0)
    (offRay.compiledStrength_pos ray)

theorem rootedCofinalGapFraction_le_one
    {w : Q'} {hw : (0 : Q') < w}
    (offRay : FixedNomeCofinalSpinCubeOffRayRootCoercivity hw)
    (ray : FixedNomeCofinalSpinCubeRayCapacity hw) :
    rootedCofinalGapFraction offRay ray ≤ (1 : Q') := by
  unfold rootedCofinalGapFraction
  exact Q'.min_le_left' _ _

/-! ## Finite comparison at a scheduled cutoff -/

/-- The cofinal rooted certificates specialize to the generic finite
pairwise-coercivity interface without changing their strength. -/
def rootedFinitePairwiseCoercivityData
    {w : Q'} {hw : (0 : Q') < w}
    (offRay : FixedNomeCofinalSpinCubeOffRayRootCoercivity hw)
    (ray : FixedNomeCofinalSpinCubeRayCapacity hw)
    {K : Nat} (hroot : Nat.max offRay.start ray.start ≤ K) :
    CentralPhysicalFinitePairwiseCoercivityData
      w (Q'.le_of_lt hw) K 0 where
  strength := offRay.compiledStrength ray
  strength_pos := offRay.compiledStrength_pos ray
  coercivity :=
    offRay.compiledStrength_mul_fullPairwiseVariance_le_physicalDirichlet
      ray hroot

/-- At any cutoff beyond the rooted and mass-floor anchors, the fixed
mass-floor fraction is a literal finite posterior-variance gap. -/
def rootedFiniteConditionalVarianceGapData
    {w : Q'} (hw : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (offRay : FixedNomeCofinalSpinCubeOffRayRootCoercivity hw)
    (ray : FixedNomeCofinalSpinCubeRayCapacity hw)
    {K : Nat}
    (hroot : Nat.max offRay.start ray.start ≤ K)
    (hmassAnchor :
      centralPhysicalFiniteVacuumSectorUniformMassFloorAnchor w 0 ≤ K) :
    CentralPhysicalFiniteConditionalVarianceGapData
      w (Q'.le_of_lt hw) K 0 := by
  let finitePairwise := rootedFinitePairwiseCoercivityData offRay ray hroot
  let finiteGap := finitePairwise.toConditionalVarianceGapData
  let massFloor :=
    centralPhysicalFiniteVacuumSectorUniformMassFloor
      w (Q'.le_of_lt hw) 0
  let strength := offRay.compiledStrength ray
  have hmassFloor : massFloor ≤
      centralPhysicalFiniteVacuumSectorMass
        w (Q'.le_of_lt hw) K 0 := by
    unfold massFloor
    exact centralPhysicalFiniteVacuumSectorUniformMassFloor_le
      hw hw1 0 hmassAnchor
  have hstrength0 : (0 : Q') ≤ strength := by
    exact Q'.le_of_lt (offRay.compiledStrength_pos ray)
  have hproduct : massFloor * strength ≤
      centralPhysicalFiniteVacuumSectorMass
          w (Q'.le_of_lt hw) K 0 * strength :=
    Q'.mul_le_mul_of_nonneg_right _ _ strength hmassFloor hstrength0
  have hfraction : rootedCofinalGapFraction offRay ray ≤
      finiteGap.fraction := by
    apply (Q'.le_min'_iff _ _ _).mpr
    constructor
    · exact rootedCofinalGapFraction_le_one offRay ray
    · exact Q'.le_trans' _ _ _
        (Q'.min_le_right' (1 : Q') (massFloor * strength))
        hproduct
  exact
    BF4PhysicalVacuumSectorPairwiseCoercivityGapBridge.CentralPhysicalFiniteConditionalVarianceGapData.lowerFraction
    finiteGap
    (rootedCofinalGapFraction offRay ray)
    (rootedCofinalGapFraction_pos offRay ray)
    (rootedCofinalGapFraction_le_one offRay ray)
    hfraction

/-- At fixed nome the current rooted resistance compiler reaches the exact
cofinal posterior-variance interface.  Its fraction visibly pays the
canonical-component mass floor. -/
def toFixedNomeCofinalConditionalVarianceFraction
    {w : Q'} (hw : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (offRay : FixedNomeCofinalSpinCubeOffRayRootCoercivity hw)
    (ray : FixedNomeCofinalSpinCubeRayCapacity hw) :
    FixedNomeCofinalVacuumSectorConditionalVarianceFraction
      w (Q'.le_of_lt hw) 0 where
  fraction := rootedCofinalGapFraction offRay ray
  fraction_pos := rootedCofinalGapFraction_pos offRay ray
  fraction_le_one := rootedCofinalGapFraction_le_one offRay ray
  anchor := rootedCofinalGapAnchor offRay ray
  anchor_ge := by
    intro request
    unfold rootedCofinalGapAnchor
    exact Nat.le_max_left _ _
  conditionalVarianceMargin := by
    intro request coefficient hcenter
    let K := rootedCofinalGapAnchor offRay ray request
    have hbase :
        Nat.max (Nat.max offRay.start ray.start)
            (centralPhysicalFiniteVacuumSectorUniformMassFloorAnchor w 0) ≤
          K := by
      unfold K rootedCofinalGapAnchor
      exact Nat.le_max_right _ _
    have hroot : Nat.max offRay.start ray.start ≤ K :=
      Nat.le_trans (Nat.le_max_left _ _) hbase
    have hmassAnchor :
        centralPhysicalFiniteVacuumSectorUniformMassFloorAnchor w 0 ≤ K :=
      Nat.le_trans (Nat.le_max_right _ _) hbase
    exact (rootedFiniteConditionalVarianceGapData
      hw hw1 offRay ray hroot hmassAnchor)
      |>.conditionalVarianceMargin coefficient hcenter

end YMGap.Continuum.BF4PhysicalVacuumSectorRootCoercivityCofinalGapBridge

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootCoercivityCofinalGapBridge.toFixedNomeCofinalConditionalVarianceFraction
