/-
# Mass-normalized pairwise coercivity removes the component-mass loss

For a centered coefficient on one finite canonical BF4 component,

    pairwiseVariance = 2 * componentMass * diagonal.

Consequently the normalized Poincare inequality

    fraction * pairwiseVariance
      <= componentMass * physicalDirichlet

allows the positive component mass to cancel and gives exactly

    fraction * diagonal
      <= (1/2) * posteriorConditionalPairwiseVariance.

This is the mass-normalized alternative to the rooted unnormalized route.  It
produces the same posterior fraction without multiplying it by a separate
component-mass floor.  A cofinal version enters the existing completed
OS-transfer compiler directly.

No finite or cofinal normalized coercivity witness is inhabited here.  No
continuum or Clay conclusion is asserted.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath
import YMGap.Continuum.BF4PhysicalVacuumSectorPairwiseCoercivityGapBridge

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedPairwiseGapBridge

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
open YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVariance
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVarianceGapBridge
open YMGap.Continuum.FiniteWeightedGramSOS

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Structural rational identities -/

private theorem mass_fraction_diagonal_eqv_half_twice_local
    (mass fraction diagonal : Q') :
    mass * (fraction * diagonal) ≈
      HalfPow.half *
        (fraction * (mass * diagonal + mass * diagonal)) := by
  refine Q'.eqv_trans _ ((mass * fraction) * diagonal) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv mass fraction diagonal)) ?_
  apply Q'.eqv_symm
  refine Q'.eqv_trans _
    (HalfPow.half *
      (fraction * (mass * diagonal) + fraction * (mass * diagonal))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left HalfPow.half _ _
      (Q'.mul_add_eqv fraction (mass * diagonal) (mass * diagonal))
  refine Q'.eqv_trans _
    (HalfPow.half * (fraction * (mass * diagonal)) +
      HalfPow.half * (fraction * (mass * diagonal))) _
    (Q'.mul_add_eqv HalfPow.half
      (fraction * (mass * diagonal)) (fraction * (mass * diagonal))) ?_
  refine Q'.eqv_trans _ (fraction * (mass * diagonal)) _
    (ExpNeg.two_halves (fraction * (mass * diagonal))) ?_
  refine Q'.eqv_trans _ ((fraction * mass) * diagonal) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv fraction mass diagonal)) ?_
  exact Q'.mul_eqv_congr_right
    (fraction * mass) (mass * fraction) diagonal
    (Q'.mul_comm_eqv fraction mass)

private theorem half_mass_value_eqv_mass_half_value_local
    (mass value : Q') :
    HalfPow.half * (mass * value) ≈
      mass * (HalfPow.half * value) := by
  refine Q'.eqv_trans _ ((HalfPow.half * mass) * value) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv HalfPow.half mass value)) ?_
  refine Q'.eqv_trans _ ((mass * HalfPow.half) * value) _
    (Q'.mul_eqv_congr_right _ _ value
      (Q'.mul_comm_eqv HalfPow.half mass)) ?_
  exact Q'.mul_assoc_eqv mass HalfPow.half value

/-! ## 2. Exact finite cancellation -/

/-- A normalized Poincare fraction for the literal finite physical
Dirichlet energy.  The component mass is on the energy side of the estimate,
so it will cancel rather than enter the output fraction. -/
structure CentralPhysicalFiniteMassNormalizedPairwiseCoercivityData
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) where
  fraction : Q'
  fraction_pos : (0 : Q') < fraction
  fraction_le_one : fraction ≤ (1 : Q')
  coercivity : ∀ coefficient : Nat → Q',
    fraction *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w hw cutoff half coefficient ≤
      centralPhysicalFiniteVacuumSectorMass w hw cutoff half *
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
          coefficient
          (centralPhysicalFiniteKernel w hw cutoff half)

namespace CentralPhysicalFiniteMassNormalizedPairwiseCoercivityData

/-- Positive-mass cancellation converts normalized pairwise coercivity into
the exact posterior-variance gap with no component-mass loss. -/
def toConditionalVarianceGapData
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (data : CentralPhysicalFiniteMassNormalizedPairwiseCoercivityData
      w hw cutoff half) :
    CentralPhysicalFiniteConditionalVarianceGapData w hw cutoff half where
  fraction := data.fraction
  fraction_pos := data.fraction_pos
  fraction_le_one := data.fraction_le_one
  conditionalVarianceMargin := by
    intro coefficient hcenter
    let mass := centralPhysicalFiniteVacuumSectorMass w hw cutoff half
    let diagonal := centralPhysicalFiniteVacuumSectorDiagonalQuadratic
      w hw cutoff half coefficient
    let dirichlet := finiteJointDirichletEnergy
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      coefficient
      (centralPhysicalFiniteKernel w hw cutoff half)
    let conditional :=
      centralPhysicalFiniteVacuumSectorConditionalPairwiseVariance
        w hw cutoff half coefficient
    have hmass : (0 : Q') < mass := by
      unfold mass
      exact centralPhysicalFiniteVacuumSectorWeightSum_pos
        w hw cutoff half
    have hpairwise :
        centralPhysicalFiniteVacuumSectorPairwiseVariance
            w hw cutoff half coefficient ≈
          mass * diagonal + mass * diagonal := by
      unfold mass diagonal
      exact centralPhysicalFiniteVacuumSectorPairwiseVariance_centered_eqv
        w hw cutoff half coefficient hcenter
    have hcoercivity :
        data.fraction * (mass * diagonal + mass * diagonal) ≤
          mass * dirichlet := by
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left data.fraction _ _
            (Q'.eqv_symm hpairwise)))
        (data.coercivity coefficient)
    have hhalf := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      hcoercivity HalfPow.half_nonneg
    have hmassScaled :
        mass * (data.fraction * diagonal) ≤
          mass * (HalfPow.half * dirichlet) := by
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (mass_fraction_diagonal_eqv_half_twice_local
            mass data.fraction diagonal))
        (Q'.le_trans' _ _ _ hhalf
          (Q'.le_of_eqv
            (half_mass_value_eqv_mass_half_value_local mass dirichlet)))
    have hcancel : data.fraction * diagonal ≤
        HalfPow.half * dirichlet :=
      Q'.le_of_mul_le_mul_left hmassScaled hmass
    have hconditional :
        HalfPow.half * dirichlet ≈ HalfPow.half * conditional := by
      unfold dirichlet conditional
      exact Q'.mul_eqv_congr_left HalfPow.half _ _
        (centralPhysicalFiniteVacuumSectorDirichlet_eqv_conditionalPairwiseVariance
          w hw cutoff half coefficient)
    exact Q'.le_trans' _ _ _ hcancel (Q'.le_of_eqv hconditional)

end CentralPhysicalFiniteMassNormalizedPairwiseCoercivityData

/-! ## 3. Cofinal normalized Poincare family -/

/-- A single normalized Poincare fraction valid beyond a constructive
representation-cutoff anchor.  Unlike the unnormalized rooted interface,
this record contains no separate component-mass floor. -/
structure FixedNomeCofinalMassNormalizedPairwiseCoercivity
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  fraction : Q'
  fraction_pos : (0 : Q') < fraction
  fraction_le_one : fraction ≤ (1 : Q')
  coercivity : ∀ K, start ≤ K → ∀ coefficient : Nat → Q',
    fraction *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w (Q'.le_of_lt hw) K 0 coefficient ≤
      centralPhysicalFiniteVacuumSectorMass
          w (Q'.le_of_lt hw) K 0 *
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices
            w (Q'.le_of_lt hw) K 0)
          coefficient
          (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)

namespace FixedNomeCofinalMassNormalizedPairwiseCoercivity

def finiteData
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalMassNormalizedPairwiseCoercivity hw)
    {K : Nat} (hK : family.start ≤ K) :
    CentralPhysicalFiniteMassNormalizedPairwiseCoercivityData
      w (Q'.le_of_lt hw) K 0 where
  fraction := family.fraction
  fraction_pos := family.fraction_pos
  fraction_le_one := family.fraction_le_one
  coercivity := family.coercivity K hK

/-- A cofinal mass-normalized Poincare estimate enters the exact cofinal
posterior-gap interface without any unconditioned mass-floor factor. -/
def toCofinalConditionalVarianceFraction
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalMassNormalizedPairwiseCoercivity hw) :
    FixedNomeCofinalVacuumSectorConditionalVarianceFraction
      w (Q'.le_of_lt hw) 0 where
  fraction := family.fraction
  fraction_pos := family.fraction_pos
  fraction_le_one := family.fraction_le_one
  anchor := fun request => Nat.max request family.start
  anchor_ge := fun request => Nat.le_max_left request family.start
  conditionalVarianceMargin := by
    intro request coefficient hcenter
    have hstart : family.start ≤ Nat.max request family.start :=
      Nat.le_max_right request family.start
    exact (family.finiteData hstart).toConditionalVarianceGapData
      |>.conditionalVarianceMargin coefficient hcenter

end FixedNomeCofinalMassNormalizedPairwiseCoercivity

end YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedPairwiseGapBridge

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedPairwiseGapBridge.CentralPhysicalFiniteMassNormalizedPairwiseCoercivityData.toConditionalVarianceGapData
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedPairwiseGapBridge.FixedNomeCofinalMassNormalizedPairwiseCoercivity.toCofinalConditionalVarianceFraction

