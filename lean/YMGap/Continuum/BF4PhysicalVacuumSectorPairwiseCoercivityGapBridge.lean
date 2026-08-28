/-
# Pairwise coercivity gives a posterior-variance gap

Suppose one finite canonical BF4 component satisfies

    strength * pairwiseVariance <= physicalDirichlet.

For a centered coefficient, pairwise variance is exactly twice the component
mass times the stationary diagonal.  Hence the posterior-variance fraction is

    min 1 (componentMass * strength).

This module proves that conversion and specializes it to the existing
spin-cube rooted coercivity certificate.  The component-mass factor is
load-bearing: no cutoff- or AF-uniform lower bound is inferred here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootCoercivity
import YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVarianceGapBridge

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPairwiseCoercivityGapBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVariance
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVarianceGapBridge
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

/-- Structural cancellation of the two copies of the stationary diagonal.
This avoids expanding rational representatives and uses only the semantic
ring laws already proved for `Q'`. -/
private theorem mass_strength_diagonal_eqv_half_twice_local
    (mass strength diagonal : Q') :
    (mass * strength) * diagonal ≈
      HalfPow.half *
        (strength * (mass * diagonal + mass * diagonal)) := by
  apply Q'.eqv_symm
  refine Q'.eqv_trans _
    (HalfPow.half *
      (strength * (mass * diagonal) + strength * (mass * diagonal))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left HalfPow.half _ _
      (Q'.mul_add_eqv strength (mass * diagonal) (mass * diagonal))
  refine Q'.eqv_trans _
    (HalfPow.half * (strength * (mass * diagonal)) +
      HalfPow.half * (strength * (mass * diagonal))) _
    (Q'.mul_add_eqv HalfPow.half
      (strength * (mass * diagonal)) (strength * (mass * diagonal))) ?_
  refine Q'.eqv_trans _ (strength * (mass * diagonal)) _
    (ExpNeg.two_halves (strength * (mass * diagonal))) ?_
  refine Q'.eqv_trans _ ((strength * mass) * diagonal) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv strength mass diagonal)) ?_
  exact Q'.mul_eqv_congr_right (strength * mass) (mass * strength) diagonal
    (Q'.mul_comm_eqv strength mass)

/-! ## 1. Generic finite pairwise-coercivity certificate -/

/-- A positive coefficient paying the full unnormalized stationary pairwise
variance by the literal physical Dirichlet energy. -/
structure CentralPhysicalFinitePairwiseCoercivityData
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) where
  strength : Q'
  strength_pos : (0 : Q') < strength
  coercivity : ∀ coefficient : Nat → Q',
    strength *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w hw cutoff half coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        coefficient
        (centralPhysicalFiniteKernel w hw cutoff half)

namespace CentralPhysicalFinitePairwiseCoercivityData

/-- The exact posterior fraction produced by unnormalized pairwise
coercivity.  The minimum only enforces the fraction convention `<= 1`. -/
def fraction
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (data : CentralPhysicalFinitePairwiseCoercivityData
      w hw cutoff half) : Q' :=
  Q'.min' 1
    (centralPhysicalFiniteVacuumSectorMass w hw cutoff half *
      data.strength)

theorem fraction_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (data : CentralPhysicalFinitePairwiseCoercivityData
      w hw cutoff half) :
    (0 : Q') < data.fraction := by
  unfold fraction
  apply q_min_pos_local (by decide)
  exact Q'.mul_pos
    (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
    data.strength_pos

theorem fraction_le_one
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (data : CentralPhysicalFinitePairwiseCoercivityData
      w hw cutoff half) :
    data.fraction ≤ (1 : Q') := by
  unfold fraction
  exact Q'.min_le_left' _ _

/-- Unnormalized pairwise coercivity gives the exact finite posterior-
variance gap, and exposes the unavoidable component-mass factor. -/
def toConditionalVarianceGapData
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (data : CentralPhysicalFinitePairwiseCoercivityData
      w hw cutoff half) :
    CentralPhysicalFiniteConditionalVarianceGapData w hw cutoff half where
  fraction := data.fraction
  fraction_pos := data.fraction_pos
  fraction_le_one := data.fraction_le_one
  conditionalVarianceMargin := by
    intro coefficient hcenter
    let mass := centralPhysicalFiniteVacuumSectorMass w hw cutoff half
    let diagonal :=
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half coefficient
    let dirichlet := finiteJointDirichletEnergy
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      coefficient
      (centralPhysicalFiniteKernel w hw cutoff half)
    let conditional :=
      centralPhysicalFiniteVacuumSectorConditionalPairwiseVariance
        w hw cutoff half coefficient
    let halfQ := Q'.mkPos 1 2 (by decide)
    have hdiagonal : (0 : Q') ≤ diagonal := by
      unfold diagonal
      exact centralPhysicalFiniteVacuumSectorDiagonalQuadratic_nonnegative
        w hw cutoff half coefficient
    have hfractionRaw : data.fraction ≤ mass * data.strength := by
      unfold fraction mass
      exact Q'.min_le_right' _ _
    have hfirst : data.fraction * diagonal ≤
        (mass * data.strength) * diagonal :=
      Q'.mul_le_mul_of_nonneg_right _ _ diagonal
        hfractionRaw hdiagonal
    have hpairwise :
        centralPhysicalFiniteVacuumSectorPairwiseVariance
            w hw cutoff half coefficient ≈
          mass * diagonal + mass * diagonal := by
      unfold mass diagonal
      exact centralPhysicalFiniteVacuumSectorPairwiseVariance_centered_eqv
        w hw cutoff half coefficient hcenter
    have hcoercivity :
        data.strength * (mass * diagonal + mass * diagonal) ≤
          dirichlet := by
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left data.strength _ _
            (Q'.eqv_symm hpairwise)))
        (data.coercivity coefficient)
    have hhalf :
        halfQ * (data.strength *
            (mass * diagonal + mass * diagonal)) ≤
          halfQ * dirichlet :=
      Q'.mul_le_mul_of_nonneg_left _ _ halfQ hcoercivity (by decide)
    have halgebra :
        (mass * data.strength) * diagonal ≈
          halfQ * (data.strength *
            (mass * diagonal + mass * diagonal)) := by
      change (mass * data.strength) * diagonal ≈
        HalfPow.half * (data.strength *
          (mass * diagonal + mass * diagonal))
      exact mass_strength_diagonal_eqv_half_twice_local
        mass data.strength diagonal
    have hconditional :
        halfQ * dirichlet ≈ halfQ * conditional := by
      unfold dirichlet conditional
      exact Q'.mul_eqv_congr_left halfQ _ _
        (centralPhysicalFiniteVacuumSectorDirichlet_eqv_conditionalPairwiseVariance
          w hw cutoff half coefficient)
    exact Q'.le_trans' _ _ _ hfirst
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv halgebra)
        (Q'.le_trans' _ _ _ hhalf (Q'.le_of_eqv hconditional)))

end CentralPhysicalFinitePairwiseCoercivityData

namespace CentralPhysicalFiniteConditionalVarianceGapData

/-- Posterior-variance gaps are downward closed in their fraction. -/
def lowerFraction
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (data : CentralPhysicalFiniteConditionalVarianceGapData
      w hw cutoff half)
    (fraction : Q')
    (fraction_pos : (0 : Q') < fraction)
    (fraction_le_one : fraction ≤ (1 : Q'))
    (hle : fraction ≤ data.fraction) :
    CentralPhysicalFiniteConditionalVarianceGapData
      w hw cutoff half where
  fraction := fraction
  fraction_pos := fraction_pos
  fraction_le_one := fraction_le_one
  conditionalVarianceMargin := by
    intro coefficient hcenter
    have hdiagonal : (0 : Q') ≤
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw cutoff half coefficient :=
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic_nonnegative
        w hw cutoff half coefficient
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
      (centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half coefficient)
      hle hdiagonal
    exact Q'.le_trans' _ _ _ hscaled
      (data.conditionalVarianceMargin coefficient hcenter)

end CentralPhysicalFiniteConditionalVarianceGapData

/-! ## 2. Existing rooted spin-cube coercivity enters the bridge -/

/-- The existing finite rooted ray/off-ray compiler is an unnormalized
pairwise-coercivity certificate with its literal compiled strength. -/
def CentralLowerExcitedSpinCubeOffRayRootCoercivityAt.toPairwiseCoercivityData
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {eta : Q'}
    (certificate :
      CentralLowerExcitedSpinCubeOffRayRootCoercivityAt hw K eta)
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    CentralPhysicalFinitePairwiseCoercivityData
      w (Q'.le_of_lt hw) K 0 where
  strength :=
    centralLowerExcitedSpinCubeRootCompiledStrength rayCapacity eta
  strength_pos :=
    centralLowerExcitedSpinCubeRootCompiledStrength_pos
      rayCapacity certificate.eta_pos
  coercivity :=
    certificate.compiledStrength_mul_fullPairwiseVariance_le_physicalDirichlet
      rayCapacity

/-- Consequently, the rooted finite compiler produces a posterior-variance
fraction equal to the minimum of one and component mass times its strength. -/
def CentralLowerExcitedSpinCubeOffRayRootCoercivityAt.toConditionalVarianceGapData
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {eta : Q'}
    (certificate :
      CentralLowerExcitedSpinCubeOffRayRootCoercivityAt hw K eta)
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    CentralPhysicalFiniteConditionalVarianceGapData
      w (Q'.le_of_lt hw) K 0 :=
  (CentralLowerExcitedSpinCubeOffRayRootCoercivityAt.toPairwiseCoercivityData
      certificate rayCapacity)
    |>.toConditionalVarianceGapData

end YMGap.Continuum.BF4PhysicalVacuumSectorPairwiseCoercivityGapBridge

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPairwiseCoercivityGapBridge.CentralPhysicalFinitePairwiseCoercivityData.toConditionalVarianceGapData
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPairwiseCoercivityGapBridge.CentralLowerExcitedSpinCubeOffRayRootCoercivityAt.toConditionalVarianceGapData
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPairwiseCoercivityGapBridge.CentralPhysicalFiniteConditionalVarianceGapData.lowerFraction
