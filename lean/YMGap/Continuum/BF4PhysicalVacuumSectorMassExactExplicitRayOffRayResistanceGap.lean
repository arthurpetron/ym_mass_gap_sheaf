/-
# Exact-mass BF4 gap from the explicit spin ray and off-ray resistance

The arbitrary-spin vacuum ray is already controlled at every positive
subunit nome: the explicit selected-term row ceiling gives one positive
cutoff-independent return floor.  The unresolved part of the rooted vacuum
variance is therefore only the complement of that ray.

This module preserves the exact component mass while making that split.  If
`delta` pays the explicit ray-root variance and `eta` pays the off-ray root
variance, then

    min 1 ((1/4) * min (2*delta) eta) * pairwiseVariance
      <= componentMass * physicalDirichlet.

Thus an off-ray resistance-congestion bound alone compiles to the normalized
posterior-variance fraction.  The ray datum is inhabited here for every
`0 < w < 1`; it is no longer part of the open fixed-nome frontier.

No cofinal off-ray resistance-congestion bound is inhabited.  No comparison
with physical lattice spacing, thermodynamic or continuum limit, continuum
QFT, or Clay conclusion is asserted.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeExplicitSubunitSelectedTermRowCeiling
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
import YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedPairwiseGapBridge

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassExactExplicitRayOffRayResistanceGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalSpinCubeExplicitSubunitSelectedTermRowCeiling
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootVariance
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedPairwiseGapBridge
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem centralPhysicalFiniteWeight_nonnegative_local
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteWeight w hw K 0 state := by
  exact centralPhysicalRowMarginal_nonnegative hw K 0
    (centralPhysicalFiniteStateAt w hw K 0 state)

private theorem q_min_pos_local {left right : Q'}
    (hleft : (0 : Q') < left) (hright : (0 : Q') < right) :
    (0 : Q') < Q'.min' left right := by
  unfold Q'.min'
  by_cases horder : left ≤ right
  · rw [if_pos horder]
    exact hleft
  · rw [if_neg horder]
    exact hright

private theorem half_mul_twice_eqv_local (value : Q') :
    HalfPow.half * (value + value) ≈ value := by
  exact Q'.eqv_trans _
    (HalfPow.half * value + HalfPow.half * value) _
    (Q'.mul_add_eqv _ _ _) (ExpNeg.two_halves value)

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

private theorem scale_mul_mass_mul_eqv_mass_mul_scale_mul_local
    (scale mass value : Q') :
    scale * (mass * value) ≈ mass * (scale * value) := by
  refine Q'.eqv_trans _ ((scale * mass) * value) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv scale mass value)) ?_
  refine Q'.eqv_trans _ ((mass * scale) * value) _
    (Q'.mul_eqv_congr_right _ _ value
      (Q'.mul_comm_eqv scale mass)) ?_
  exact Q'.mul_assoc_eqv mass scale value

/-! ## 1. Exact-mass ray/off-ray rooting -/

/-- Unlike the older rooted split, this theorem retains the literal sector
mass from the exact pairwise-to-root identity. -/
theorem centralPhysicalFiniteVacuumSectorPairwiseVariance_le_mass_mul_twice_rayRoot_add_offRayRoot
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorPairwiseVariance
        w hw K 0 coefficient ≤
      centralPhysicalFiniteVacuumSectorMass w hw K 0 *
        ((centralLowerExcitedSpinCubeFilteredRayRootVariance
            w hw K coefficient +
          centralLowerExcitedSpinCubeOffRayRootVariance
            w hw K coefficient) +
        (centralLowerExcitedSpinCubeFilteredRayRootVariance
            w hw K coefficient +
          centralLowerExcitedSpinCubeOffRayRootVariance
            w hw K coefficient)) := by
  let states := centralPhysicalFiniteVacuumSectorIndices w hw K 0
  let weight := centralPhysicalFiniteWeight w hw K 0
  let mass := centralPhysicalFiniteVacuumSectorMass w hw K 0
  let root := centralPhysicalFiniteVacuumSectorRootVariance
    w hw K 0 coefficient
  let split :=
    centralLowerExcitedSpinCubeFilteredRayRootVariance w hw K coefficient +
      centralLowerExcitedSpinCubeOffRayRootVariance w hw K coefficient
  have hexact :=
    finiteWeightedPairwiseVariance_le_twice_mass_rootVariance
      states weight coefficient 0
  have hsplit : root ≈ split := by
    unfold root split
    exact
      centralPhysicalFiniteVacuumSectorRootVariance_eqv_rayRoot_add_offRayRoot
        w hw K coefficient
  refine Q'.le_trans' _ (mass * root + mass * root) _ ?_ ?_
  · simpa only [states, weight, mass, root,
      centralPhysicalFiniteVacuumSectorPairwiseVariance,
      centralPhysicalFiniteVacuumSectorMass] using hexact
  · exact Q'.le_of_eqv
      (Q'.eqv_trans _ (mass * split + mass * split) _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left mass _ _ hsplit)
          (Q'.mul_eqv_congr_left mass _ _ hsplit))
        (Q'.eqv_symm (Q'.mul_add_eqv mass split split)))

theorem centralPhysicalFiniteVacuumSectorPairwiseVariance_nonnegative_local
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorPairwiseVariance
        w hw K 0 coefficient := by
  unfold centralPhysicalFiniteVacuumSectorPairwiseVariance
    finiteWeightedPairwiseVariance finiteJointDirichletEnergy
    finiteStationaryProductJoint
  apply listQSum_nonnegative_on
  intro left _hleft
  apply listQSum_nonnegative_on
  intro right _hright
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (centralPhysicalFiniteWeight_nonnegative_local w hw K left)
      (centralPhysicalFiniteWeight_nonnegative_local w hw K right))
    (SumOfSquares.q_mul_self_nonneg
      (coefficient left + -coefficient right))

/-! ## 2. The exact-mass finite compiler -/

/-- The old numerical strength remains valid, but now with the component mass
on the energy side where the posterior bridge can cancel it. -/
theorem centralLowerExcitedSpinCubeRootCompiledStrength_mul_fullPairwiseVariance_le_mass_mul_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {eta : Q'}
    (certificate :
      CentralLowerExcitedSpinCubeOffRayRootCoercivityAt hw K eta)
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeRootCompiledStrength rayCapacity eta *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w (Q'.le_of_lt hw) K 0 coefficient ≤
      centralPhysicalFiniteVacuumSectorMass w (Q'.le_of_lt hw) K 0 *
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices
            w (Q'.le_of_lt hw) K 0)
          coefficient
          (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  let rayRoot := centralLowerExcitedSpinCubeFilteredRayRootVariance
    w (Q'.le_of_lt hw) K coefficient
  let offRayRoot := centralLowerExcitedSpinCubeOffRayRootVariance
    w (Q'.le_of_lt hw) K coefficient
  let rootSplit := rayRoot + offRayRoot
  let energy := finiteJointDirichletEnergy
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    coefficient
    (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)
  let mass := centralPhysicalFiniteVacuumSectorMass
    w (Q'.le_of_lt hw) K 0
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
  have hcommonSum : common * rootSplit ≤ energy + energy := by
    unfold rootSplit
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_add_eqv common rayRoot offRayRoot))
      (Q'.add_le_add hcommonRay hcommonOffRay)
  have hhalfSum : HalfPow.half * (common * rootSplit) ≤ energy := by
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      hcommonSum HalfPow.half_nonneg
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (half_mul_twice_eqv_local energy))
  have hstrengthTwice : strength * (rootSplit + rootSplit) ≤ energy := by
    exact Q'.le_trans' _
      (HalfPow.half * (common * rootSplit)) _
      (Q'.le_of_eqv
        (half_half_mul_twice_eqv_local common rootSplit))
      hhalfSum
  have hpairwise :=
    centralPhysicalFiniteVacuumSectorPairwiseVariance_le_mass_mul_twice_rayRoot_add_offRayRoot
      w (Q'.le_of_lt hw) K coefficient
  have hstrength0 : (0 : Q') ≤ strength :=
    Q'.le_of_lt
      (centralLowerExcitedSpinCubeRootCompiledStrength_pos
        rayCapacity certificate.eta_pos)
  have hscaledPairwise := Q'.mul_le_mul_of_nonneg_left _ _ strength
    hpairwise hstrength0
  have hmass0 : (0 : Q') ≤ mass := by
    unfold mass
    exact Q'.le_of_lt
      (centralPhysicalFiniteVacuumSectorWeightSum_pos
        w (Q'.le_of_lt hw) K 0)
  have hmassScaled := Q'.mul_le_mul_of_nonneg_left _ _ mass
    hstrengthTwice hmass0
  change strength *
      centralPhysicalFiniteVacuumSectorPairwiseVariance
        w (Q'.le_of_lt hw) K 0 coefficient ≤ mass * energy
  exact Q'.le_trans' _ (strength * (mass * (rootSplit + rootSplit))) _
    hscaledPairwise
    (Q'.le_trans' _ (mass * (strength * (rootSplit + rootSplit))) _
      (Q'.le_of_eqv
        (scale_mul_mass_mul_eqv_mass_mul_scale_mul_local
          strength mass (rootSplit + rootSplit)))
      hmassScaled)

def centralLowerExcitedSpinCubeMassExactNormalizedRootCompiledStrength
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (eta : Q') : Q' :=
  Q'.min' 1
    (centralLowerExcitedSpinCubeRootCompiledStrength rayCapacity eta)

theorem centralLowerExcitedSpinCubeMassExactNormalizedRootCompiledStrength_pos
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    {eta : Q'} (heta : (0 : Q') < eta) :
    (0 : Q') <
      centralLowerExcitedSpinCubeMassExactNormalizedRootCompiledStrength
        rayCapacity eta := by
  unfold centralLowerExcitedSpinCubeMassExactNormalizedRootCompiledStrength
  exact q_min_pos_local (by decide)
    (centralLowerExcitedSpinCubeRootCompiledStrength_pos rayCapacity heta)

theorem centralLowerExcitedSpinCubeMassExactNormalizedRootCompiledStrength_le_one
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (eta : Q') :
    centralLowerExcitedSpinCubeMassExactNormalizedRootCompiledStrength
        rayCapacity eta ≤ 1 := by
  unfold centralLowerExcitedSpinCubeMassExactNormalizedRootCompiledStrength
  exact Q'.min_le_left' _ _

def centralLowerExcitedSpinCubeMassExactRootCoercivityData
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {eta : Q'}
    (certificate :
      CentralLowerExcitedSpinCubeOffRayRootCoercivityAt hw K eta)
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    CentralPhysicalFiniteMassNormalizedPairwiseCoercivityData
      w (Q'.le_of_lt hw) K 0 where
  fraction :=
    centralLowerExcitedSpinCubeMassExactNormalizedRootCompiledStrength
      rayCapacity eta
  fraction_pos :=
    centralLowerExcitedSpinCubeMassExactNormalizedRootCompiledStrength_pos
      rayCapacity certificate.eta_pos
  fraction_le_one :=
    centralLowerExcitedSpinCubeMassExactNormalizedRootCompiledStrength_le_one
      rayCapacity eta
  coercivity := fun coefficient => by
    let pairwise := centralPhysicalFiniteVacuumSectorPairwiseVariance
      w (Q'.le_of_lt hw) K 0 coefficient
    let raw := centralLowerExcitedSpinCubeRootCompiledStrength
      rayCapacity eta
    let normalized :=
      centralLowerExcitedSpinCubeMassExactNormalizedRootCompiledStrength
        rayCapacity eta
    have hpairwise0 : (0 : Q') ≤ pairwise := by
      unfold pairwise
      exact centralPhysicalFiniteVacuumSectorPairwiseVariance_nonnegative_local
        w (Q'.le_of_lt hw) K coefficient
    have hnormalizedRaw : normalized ≤ raw := by
      unfold normalized
        centralLowerExcitedSpinCubeMassExactNormalizedRootCompiledStrength
      exact Q'.min_le_right' _ _
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ pairwise
      hnormalizedRaw hpairwise0
    exact Q'.le_trans' _ (raw * pairwise) _ hscaled
      (centralLowerExcitedSpinCubeRootCompiledStrength_mul_fullPairwiseVariance_le_mass_mul_physicalDirichlet
        certificate rayCapacity coefficient)

/-! ## 3. The explicit ray removes itself from the cofinal frontier -/

def explicitSubunitCentralSpinCubeCofinalRayCapacity
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    FixedNomeCofinalSpinCubeRayCapacity hw0 :=
  (explicitSubunitCentralSpinCubeSelectedTermRowCeiling
    w hw0 hw1).toCofinalRayCapacity

def fixedNomeMassExactExplicitRayOffRayResistanceFraction
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (offRay :
      FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw0) : Q' :=
  Q'.min' 1
    (HalfPow.half *
      (HalfPow.half * Q'.min'
        (2 * (explicitSubunitCentralSpinCubeCofinalRayCapacity
          w hw0 hw1).delta)
        offRay.eta))

theorem fixedNomeMassExactExplicitRayOffRayResistanceFraction_pos
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (offRay :
      FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw0) :
    (0 : Q') <
      fixedNomeMassExactExplicitRayOffRayResistanceFraction
        hw0 hw1 offRay := by
  unfold fixedNomeMassExactExplicitRayOffRayResistanceFraction
  exact q_min_pos_local (by decide)
    (by
      apply ExpNeg.half_mul_pos
      apply ExpNeg.half_mul_pos
      exact q_min_pos_local
        (Q'.mul_pos (by decide)
          (explicitSubunitCentralSpinCubeCofinalRayCapacity
            w hw0 hw1).delta_pos)
        offRay.eta_pos)

theorem fixedNomeMassExactExplicitRayOffRayResistanceFraction_le_one
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (offRay :
      FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw0) :
    fixedNomeMassExactExplicitRayOffRayResistanceFraction
        hw0 hw1 offRay ≤ 1 := by
  unfold fixedNomeMassExactExplicitRayOffRayResistanceFraction
  exact Q'.min_le_left' _ _

/-- At fixed subunit nome, the explicit ray theorem plus one off-ray raw
resistance-congestion bound gives the full cofinal normalized Poincare law. -/
def fixedNomeMassExactExplicitRayOffRayResistanceCoercivity
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (offRay :
      FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw0) :
    FixedNomeCofinalMassNormalizedPairwiseCoercivity hw0 where
  start := offRay.start
  fraction :=
    fixedNomeMassExactExplicitRayOffRayResistanceFraction hw0 hw1 offRay
  fraction_pos :=
    fixedNomeMassExactExplicitRayOffRayResistanceFraction_pos
      hw0 hw1 offRay
  fraction_le_one :=
    fixedNomeMassExactExplicitRayOffRayResistanceFraction_le_one
      hw0 hw1 offRay
  coercivity := fun K hK coefficient => by
    let ray := explicitSubunitCentralSpinCubeCofinalRayCapacity w hw0 hw1
    have hrayStart : ray.start ≤ K := by
      change 0 ≤ K
      omega
    let rayAt :=
      YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity.FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
        ray K hrayStart
    let offRayAt := (offRay.finiteCapacityAt K hK).toOffRayRootCoercivityAt
    have hcoercivity :=
      (centralLowerExcitedSpinCubeMassExactRootCoercivityData
        offRayAt rayAt).coercivity coefficient
    simpa only [ray, rayAt, offRayAt,
      centralLowerExcitedSpinCubeMassExactNormalizedRootCompiledStrength,
      centralLowerExcitedSpinCubeRootCompiledStrength,
      fixedNomeMassExactExplicitRayOffRayResistanceFraction] using hcoercivity

def fixedNomeMassExactExplicitRayOffRayResistanceConditionalVarianceFraction
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (offRay :
      FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw0) :=
  (fixedNomeMassExactExplicitRayOffRayResistanceCoercivity
    hw0 hw1 offRay).toCofinalConditionalVarianceFraction

end YMGap.Continuum.BF4PhysicalVacuumSectorMassExactExplicitRayOffRayResistanceGap

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactExplicitRayOffRayResistanceGap.centralPhysicalFiniteVacuumSectorPairwiseVariance_le_mass_mul_twice_rayRoot_add_offRayRoot
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactExplicitRayOffRayResistanceGap.centralLowerExcitedSpinCubeRootCompiledStrength_mul_fullPairwiseVariance_le_mass_mul_physicalDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactExplicitRayOffRayResistanceGap.fixedNomeMassExactExplicitRayOffRayResistanceCoercivity
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactExplicitRayOffRayResistanceGap.fixedNomeMassExactExplicitRayOffRayResistanceConditionalVarianceFraction
