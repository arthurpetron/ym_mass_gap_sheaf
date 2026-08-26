/-
# Compile one off-ray root estimate to full finite-sector coercivity

The preceding root decomposition reduces the unresolved spin-cube geometry
to one-body distances from the physical vacuum.  This module records the
minimal remaining analytic datum and proves that it is sufficient.

If `eta` pays the off-ray rooted variance and the verified ray capacity pays
the ray-root variance at strength `2 * delta`, their minimum pays both rooted
pieces.  The only loss is the explicit factor `1/4`: one factor `1/2` comes
from rooting the full pairwise variance, and one from adding two estimates
which each use the full Dirichlet energy.

Thus the compiler is mathematically causal and coefficient-uniform.  It does
not construct the missing cutoff-uniform `eta`; that is the next analytic
frontier.  No completed gap, thermodynamic or continuum limit, continuum QFT,
or Clay conclusion is asserted.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootVariance

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootCoercivity

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootVariance
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

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

private theorem centralPhysicalFiniteWeight_nonnegative_local
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteWeight w hw K 0 state := by
  exact centralPhysicalRowMarginal_nonnegative hw K 0
    (centralPhysicalFiniteStateAt w hw K 0 state)

private theorem half_half_mul_twice_eqv_local
    (strength value : Q') :
    (HalfPow.half * (HalfPow.half * strength)) * (value + value) ≈
      HalfPow.half * (strength * value) := by
  refine Q'.eqv_trans _
    (HalfPow.half *
      ((HalfPow.half * strength) * (value + value))) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  apply Q'.mul_eqv_congr_left
  refine Q'.eqv_trans _
    ((HalfPow.half * strength) * value +
      (HalfPow.half * strength) * value) _
    (Q'.mul_add_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (HalfPow.half * (strength * value) +
      HalfPow.half * (strength * value)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_assoc_eqv _ _ _) (Q'.mul_assoc_eqv _ _ _)
  · exact ExpNeg.two_halves (strength * value)

private theorem half_mul_twice_eqv_local (value : Q') :
    HalfPow.half * (value + value) ≈ value := by
  exact Q'.eqv_trans _
    (HalfPow.half * value + HalfPow.half * value) _
    (Q'.mul_add_eqv _ _ _) (ExpNeg.two_halves value)

/-! ## 1. The single remaining finite analytic datum -/

/-- At one cutoff, `eta` pays exactly the one-body off-ray distance from the
vacuum.  Unlike the older residual certificate, this contains no ray--off,
off--ray, or off--off pair matrix. -/
structure CentralLowerExcitedSpinCubeOffRayRootCoercivityAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) (eta : Q') : Type 1 where
  eta_pos : (0 : Q') < eta
  offRayRoot_coercivity : ∀ coefficient : Nat → Q',
    eta * centralLowerExcitedSpinCubeOffRayRootVariance
        w (Q'.le_of_lt hw) K coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)

/-! ## 2. Exact finite compiler -/

/-- The explicit full-sector strength compiled from the two rooted estimates:
`(1/4) * min (2 * rayDelta) eta`. -/
def centralLowerExcitedSpinCubeRootCompiledStrength
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (eta : Q') : Q' :=
  HalfPow.half *
    (HalfPow.half * Q'.min' (2 * rayCapacity.delta) eta)

theorem centralLowerExcitedSpinCubeRootCompiledStrength_pos
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    {eta : Q'} (heta : (0 : Q') < eta) :
    (0 : Q') <
      centralLowerExcitedSpinCubeRootCompiledStrength rayCapacity eta := by
  unfold centralLowerExcitedSpinCubeRootCompiledStrength
  apply ExpNeg.half_mul_pos
  apply ExpNeg.half_mul_pos
  exact q_min_pos_local
    (Q'.mul_pos (by decide) rayCapacity.delta_pos) heta

namespace CentralLowerExcitedSpinCubeOffRayRootCoercivityAt

/-- The single off-ray root estimate and the already-proved ray return imply
full pairwise Dirichlet coercivity, with no endpoint-pair residual left in the
interface. -/
theorem compiledStrength_mul_fullPairwiseVariance_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {eta : Q'}
    (certificate :
      CentralLowerExcitedSpinCubeOffRayRootCoercivityAt hw K eta)
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeRootCompiledStrength rayCapacity eta *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w (Q'.le_of_lt hw) K 0 coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  let rayRoot := centralLowerExcitedSpinCubeFilteredRayRootVariance
    w (Q'.le_of_lt hw) K coefficient
  let offRayRoot := centralLowerExcitedSpinCubeOffRayRootVariance
    w (Q'.le_of_lt hw) K coefficient
  let energy := finiteJointDirichletEnergy
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    coefficient
    (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)
  let common := Q'.min' (2 * rayCapacity.delta) eta
  let strength := HalfPow.half * (HalfPow.half * common)
  have hrayRoot0 : (0 : Q') ≤ rayRoot := by
    unfold rayRoot centralLowerExcitedSpinCubeFilteredRayRootVariance
    exact finiteWeightedRootVariance_nonnegative _ _ coefficient 0
      (fun state _ =>
        centralPhysicalFiniteWeight_nonnegative_local
          w (Q'.le_of_lt hw) K state)
  have hoffRayRoot0 : (0 : Q') ≤ offRayRoot := by
    unfold offRayRoot centralLowerExcitedSpinCubeOffRayRootVariance
    exact finiteWeightedRootVariance_nonnegative _ _ coefficient 0
      (fun state _ =>
        centralPhysicalFiniteWeight_nonnegative_local
          w (Q'.le_of_lt hw) K state)
  have hcommonRay : common * rayRoot ≤ energy := by
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ rayRoot
      (Q'.min_le_left' (2 * rayCapacity.delta) eta) hrayRoot0
    exact Q'.le_trans' _ _ _ hscaled
      (two_delta_mul_filteredRayRootVariance_le_physicalDirichlet
        hw rayCapacity coefficient)
  have hcommonOffRay : common * offRayRoot ≤ energy := by
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ offRayRoot
      (Q'.min_le_right' (2 * rayCapacity.delta) eta) hoffRayRoot0
    exact Q'.le_trans' _ _ _ hscaled
      (certificate.offRayRoot_coercivity coefficient)
  have hcommonSum : common * (rayRoot + offRayRoot) ≤ energy + energy := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_add_eqv common rayRoot offRayRoot))
      (Q'.add_le_add hcommonRay hcommonOffRay)
  have hhalfSum :
      HalfPow.half * (common * (rayRoot + offRayRoot)) ≤ energy := by
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      hcommonSum HalfPow.half_nonneg
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (half_mul_twice_eqv_local energy))
  have hpairwise :=
    centralPhysicalFiniteVacuumSectorPairwiseVariance_le_twice_rayRoot_add_offRayRoot
      w (Q'.le_of_lt hw) K coefficient
  have hstrength0 : (0 : Q') ≤ strength :=
    Q'.le_of_lt
      (centralLowerExcitedSpinCubeRootCompiledStrength_pos
        rayCapacity certificate.eta_pos)
  have hscaledPairwise := Q'.mul_le_mul_of_nonneg_left _ _ strength
    hpairwise hstrength0
  change strength *
      centralPhysicalFiniteVacuumSectorPairwiseVariance
        w (Q'.le_of_lt hw) K 0 coefficient ≤ energy
  exact Q'.le_trans' _
    (strength *
      ((rayRoot + offRayRoot) + (rayRoot + offRayRoot))) _
    hscaledPairwise
    (Q'.le_trans' _
      (HalfPow.half * (common * (rayRoot + offRayRoot))) _
      (Q'.le_of_eqv
        (half_half_mul_twice_eqv_local common (rayRoot + offRayRoot)))
      hhalfSum)

end CentralLowerExcitedSpinCubeOffRayRootCoercivityAt

/-! ## 3. The precise cofinal frontier -/

/-- A cutoff-independent `eta` paying every later off-ray rooted variance.
This is the sole new cofinal analytic family required by the rooted compiler;
no inhabitant is asserted here. -/
structure FixedNomeCofinalSpinCubeOffRayRootCoercivity
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  eta : Q'
  eta_pos : (0 : Q') < eta
  finite : ∀ K, start ≤ K →
    CentralLowerExcitedSpinCubeOffRayRootCoercivityAt hw K eta

namespace FixedNomeCofinalSpinCubeOffRayRootCoercivity

/-- The coefficient-independent strength that would survive the cutoff once
the off-ray root family is constructed. -/
def compiledStrength
    {w : Q'} {hw : (0 : Q') < w}
    (offRay : FixedNomeCofinalSpinCubeOffRayRootCoercivity hw)
    (ray : FixedNomeCofinalSpinCubeRayCapacity hw) : Q' :=
  HalfPow.half *
    (HalfPow.half * Q'.min' (2 * ray.delta) offRay.eta)

theorem compiledStrength_pos
    {w : Q'} {hw : (0 : Q') < w}
    (offRay : FixedNomeCofinalSpinCubeOffRayRootCoercivity hw)
    (ray : FixedNomeCofinalSpinCubeRayCapacity hw) :
    (0 : Q') < offRay.compiledStrength ray := by
  unfold compiledStrength
  apply ExpNeg.half_mul_pos
  apply ExpNeg.half_mul_pos
  exact q_min_pos_local
    (Q'.mul_pos (by decide) ray.delta_pos) offRay.eta_pos

/-- Beyond the maximum of the two starts, the two cofinal rooted estimates
compile to one uniform full-sector finite coercivity theorem. -/
theorem compiledStrength_mul_fullPairwiseVariance_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w}
    (offRay : FixedNomeCofinalSpinCubeOffRayRootCoercivity hw)
    (ray : FixedNomeCofinalSpinCubeRayCapacity hw)
    {K : Nat} (hK : Nat.max offRay.start ray.start ≤ K)
    (coefficient : Nat → Q') :
    offRay.compiledStrength ray *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w (Q'.le_of_lt hw) K 0 coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  have hoff : offRay.start ≤ K :=
    Nat.le_trans (Nat.le_max_left _ _) hK
  have hray : ray.start ≤ K :=
    Nat.le_trans (Nat.le_max_right _ _) hK
  exact
    (offRay.finite K hoff)
      |>.compiledStrength_mul_fullPairwiseVariance_le_physicalDirichlet
        (BF4PhysicalSpinCubeRayDirichletCoercivity.FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
          ray K hray) coefficient

end FixedNomeCofinalSpinCubeOffRayRootCoercivity

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootCoercivity

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootCoercivity.centralLowerExcitedSpinCubeRootCompiledStrength_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootCoercivity.CentralLowerExcitedSpinCubeOffRayRootCoercivityAt.compiledStrength_mul_fullPairwiseVariance_le_physicalDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootCoercivity.FixedNomeCofinalSpinCubeOffRayRootCoercivity.compiledStrength_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootCoercivity.FixedNomeCofinalSpinCubeOffRayRootCoercivity.compiledStrength_mul_fullPairwiseVariance_le_physicalDirichlet
