/-
# The spin-cube off-ray residual endpoint mass is at most one

The three residual endpoint blocks are a literal duplicate-free sublist of
the Cartesian square of the complete finite physical vacuum sector.  Their
stationary-product mass is therefore at most the square of the sector mass,
which is at most one by normalization of the full finite physical law.

Consequently the simple-path residual load is bounded by the finite carrier
size alone.  This removes the previously explicit residual endpoint-mass
factor from the remaining scalar capacity ratio, but it does not remove the
carrier-size growth or the possible decay of the minimum positive physical
edge.  No cutoff-uniform full-sector gap, thermodynamic or continuum limit,
continuum QFT, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualLinearCongestion
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualLinearCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The residual endpoint list is a duplicate-free subcarrier -/

private theorem filteredRay_ne_offRay
    {w : Q'} {hw : (0 : Q') ≤ w} {K ray off : Nat}
    (hray : ray ∈
      centralLowerExcitedSpinCubeFilteredRayIndices w hw K)
    (hoff : off ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K) :
    ray ≠ off := by
  intro heq
  subst off
  have hrayTest := (List.mem_filter.mp hray).2
  have hoffTest := (List.mem_filter.mp hoff).2
  cases htest : centralLowerExcitedSpinCubeRayMembershipTest w hw K ray with
  | false => simp [htest] at hrayTest
  | true => simp [htest] at hoffTest

theorem centralLowerExcitedSpinCubeOffRayResidualEndpointPairs_nodup
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K).Nodup := by
  let ray := centralLowerExcitedSpinCubeFilteredRayIndices w hw K
  let off := centralLowerExcitedSpinCubeOffRayIndices w hw K
  have hsector := centralPhysicalFiniteVacuumSectorIndices_nodup w hw K 0
  have hray : ray.Nodup := by
    unfold ray centralLowerExcitedSpinCubeFilteredRayIndices
    exact List.filter_sublist.nodup hsector
  have hoff : off.Nodup := by
    unfold off centralLowerExcitedSpinCubeOffRayIndices
    exact List.filter_sublist.nodup hsector
  have hrayOff : (cartesian ray off).Nodup :=
    cartesian_nodup ray off hray hoff
  have hoffRay : (cartesian off ray).Nodup :=
    cartesian_nodup off ray hoff hray
  have hoffOff : (cartesian off off).Nodup :=
    cartesian_nodup off off hoff hoff
  change (cartesian ray off ++
    (cartesian off ray ++ cartesian off off)).Nodup
  apply List.nodup_append.mpr
  refine ⟨hrayOff, ?_, ?_⟩
  · apply List.nodup_append.mpr
    refine ⟨hoffRay, hoffOff, ?_⟩
    intro left hleft right hright heq
    have hleftParts := (mem_cartesian_iff off ray left).mp hleft
    have hrightParts := (mem_cartesian_iff off off right).mp hright
    exact (filteredRay_ne_offRay hleftParts.2 hrightParts.2)
      (congrArg Prod.snd heq)
  · intro left hleft right hright heq
    have hleftParts := (mem_cartesian_iff ray off left).mp hleft
    rcases List.mem_append.mp hright with hrightOffRay | hrightOffOff
    · have hrightParts :=
        (mem_cartesian_iff off ray right).mp hrightOffRay
      exact (filteredRay_ne_offRay hleftParts.1 hrightParts.1)
        (congrArg Prod.fst heq)
    · have hrightParts :=
        (mem_cartesian_iff off off right).mp hrightOffOff
      exact (filteredRay_ne_offRay hleftParts.1 hrightParts.1)
        (congrArg Prod.fst heq)

theorem centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum_le_fullPairWeightSum
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum w hw K ≤
      listQSum
        (fun pair =>
          centralPhysicalFiniteWeight w hw K 0 pair.1 *
            centralPhysicalFiniteWeight w hw K 0 pair.2)
        (cartesian
          (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
          (centralPhysicalFiniteVacuumSectorIndices w hw K 0)) := by
  unfold centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum
  apply listQSum_le_of_injective
    (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)
    (cartesian
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0))
    (fun pair =>
      centralPhysicalFiniteWeight w hw K 0 pair.1 *
        centralPhysicalFiniteWeight w hw K 0 pair.2)
    (fun pair =>
      centralPhysicalFiniteWeight w hw K 0 pair.1 *
        centralPhysicalFiniteWeight w hw K 0 pair.2)
    (fun pair => pair)
  · exact centralLowerExcitedSpinCubeOffRayResidualEndpointPairs_nodup w hw K
  · intro pair hpair
    exact (mem_cartesian_iff _ _ pair).mpr
      (centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair)
  · intro left _hleft right _hright heq
    exact heq
  · intro pair _hpair
    exact Q'.le_refl' _
  · intro pair _hpair
    unfold centralPhysicalFiniteWeight
    exact Q'.mul_nonneg _ _
      (centralPhysicalRowMarginal_nonnegative hw K 0 _)
      (centralPhysicalRowMarginal_nonnegative hw K 0 _)

theorem centralPhysicalFiniteVacuumSectorFullPairWeightSum_eqv_massSquare
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    listQSum
        (fun pair =>
          centralPhysicalFiniteWeight w hw K 0 pair.1 *
            centralPhysicalFiniteWeight w hw K 0 pair.2)
        (cartesian
          (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
          (centralPhysicalFiniteVacuumSectorIndices w hw K 0)) ≈
      centralPhysicalFiniteVacuumSectorMass w hw K 0 *
        centralPhysicalFiniteVacuumSectorMass w hw K 0 := by
  unfold centralPhysicalFiniteVacuumSectorMass finiteWeightedMass
  exact listQSum_cartesian_product _ _ _ _

theorem centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum_le_one
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum w hw K ≤ 1 := by
  exact Q'.le_trans' _ _ _
    (centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum_le_fullPairWeightSum
      w hw K)
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (centralPhysicalFiniteVacuumSectorFullPairWeightSum_eqv_massSquare
          w hw K))
      (centralPhysicalFiniteVacuumSectorMass_square_le_one w hw K 0))

/-! ## 2. The residual flow load is bounded by carrier size alone -/

theorem centralLowerExcitedSpinCubeOffRayResidualFlowLoad_le_sectorSize
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualFlowLoad
        w hw K source target ≤
      Q'.ofNat
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0).length := by
  let size := Q'.ofNat
    (centralPhysicalFiniteVacuumSectorIndices w hw K 0).length
  have hload :=
    centralLowerExcitedSpinCubeOffRayResidualFlowLoad_le_sectorSize_mul_endpointWeightSum
      w hw K source target
  have hsize0 : (0 : Q') ≤ size :=
    Q'.ofNat_le_ofNat (Nat.zero_le _)
  have hscaled : size *
        centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum w hw K ≤
      size * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ size
      (centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum_le_one
        w hw K)
      hsize0
  exact Q'.le_trans' _ _ _ hload
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.mul_one_eqv size)))

def centralLowerExcitedSpinCubeOffRayResidualNormalizedLinearCost
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Q' :=
  1 + Q'.ofNat
    (centralPhysicalFiniteVacuumSectorIndices w hw K 0).length

theorem centralLowerExcitedSpinCubeOffRayResidualNormalizedLinearCost_pos
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    (0 : Q') <
      centralLowerExcitedSpinCubeOffRayResidualNormalizedLinearCost
        w hw K := by
  unfold centralLowerExcitedSpinCubeOffRayResidualNormalizedLinearCost
  exact Q'.pos_add_nonneg (by decide)
    (Q'.ofNat_le_ofNat (Nat.zero_le _))

theorem centralLowerExcitedSpinCubeOffRayResidualFlowLoad_le_normalizedLinearCost
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualFlowLoad
        w hw K source target ≤
      centralLowerExcitedSpinCubeOffRayResidualNormalizedLinearCost
        w hw K := by
  let size := Q'.ofNat
    (centralPhysicalFiniteVacuumSectorIndices w hw K 0).length
  have hload :=
    centralLowerExcitedSpinCubeOffRayResidualFlowLoad_le_sectorSize
      w hw K source target
  have hadd := Q'.add_le_add_right (0 : Q') 1 size
    (by decide : (0 : Q') ≤ 1)
  have hsizeCost : size ≤
      centralLowerExcitedSpinCubeOffRayResidualNormalizedLinearCost
        w hw K := by
    unfold centralLowerExcitedSpinCubeOffRayResidualNormalizedLinearCost
    rwa [Q'.zero_add'] at hadd
  exact Q'.le_trans' _ _ _ hload hsizeCost

/-! ## 3. The mass-free scalar ratio compiles to full finite coercivity -/

structure CentralLowerExcitedSpinCubeOffRayResidualNormalizedLinearRatioAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    Type 1 where
  ratio_bound :
    centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
        centralLowerExcitedSpinCubeOffRayResidualNormalizedLinearCost
          w (Q'.le_of_lt hw) K ≤
      HalfPow.half * centralPhysicalFiniteVacuumSectorEdgeFloor
        w (Q'.le_of_lt hw) K 0

namespace CentralLowerExcitedSpinCubeOffRayResidualNormalizedLinearRatioAt

private theorem q_nonpos_of_not_pos_local {q : Q'}
    (hnot : ¬ (0 : Q') < q) : q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  apply Int.not_lt.mp
  intro hnum
  apply hnot
  exact CReal.pos_of_num_pos hnum

def toResidualFlowCapacityAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (ratio : CentralLowerExcitedSpinCubeOffRayResidualNormalizedLinearRatioAt
      hw K rayCapacity) :
    CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt
      hw K rayCapacity where
  edge_capacity := fun source hsource target htarget => by
    let load := centralLowerExcitedSpinCubeOffRayResidualFlowLoad
      w (Q'.le_of_lt hw) K source target
    have hload0 : (0 : Q') ≤ load :=
      centralLowerExcitedSpinCubeOffRayResidualFlowLoad_nonnegative
        w (Q'.le_of_lt hw) K source target
    by_cases hloadPos : (0 : Q') < load
    · have hloadCost : load ≤
          centralLowerExcitedSpinCubeOffRayResidualNormalizedLinearCost
            w (Q'.le_of_lt hw) K :=
        centralLowerExcitedSpinCubeOffRayResidualFlowLoad_le_normalizedLinearCost
          w (Q'.le_of_lt hw) K source target
      have hshared0 : (0 : Q') ≤
          centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity :=
        Q'.le_of_lt
          (centralLowerExcitedSpinCubeSharedCoercivityFloor_pos rayCapacity)
      have hloadScaled := Q'.mul_le_mul_of_nonneg_left _ _ _
        hloadCost hshared0
      have hkernelPos :=
        centralLowerExcitedSpinCubeOffRayResidualFlowLoad_pos_implies_kernel_pos
          hw K source target hloadPos
      have hfloor :=
        centralPhysicalFiniteVacuumSectorEdgeFloor_le_positive_entry
          w (Q'.le_of_lt hw) K 0 source target
          hsource htarget hkernelPos
      have hhalfFloor := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
        hfloor HalfPow.half_nonneg
      exact Q'.le_trans' _ _ _ hloadScaled
        (Q'.le_trans' _ _ _ ratio.ratio_bound hhalfFloor)
    · have hloadNonpos : load ≤ 0 :=
        q_nonpos_of_not_pos_local hloadPos
      have hloadZero : load ≈ 0 :=
        Q'.eqv_of_le_le hloadNonpos hload0
      have hkernel0 : (0 : Q') ≤ centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K 0 source target := by
        unfold centralPhysicalFiniteKernel
        exact centralNormalizedPhysicalReflectedKernel_nonnegative
          (Q'.le_of_lt hw) K 0 _ _
      have hhalfKernel0 := Q'.mul_nonneg _ _
        HalfPow.half_nonneg hkernel0
      exact Q'.le_trans' _ (0 : Q') _
        (Q'.le_of_eqv
          (Q'.eqv_trans _
            (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity * 0) _
            (Q'.mul_eqv_congr_left _ _ _ hloadZero)
            (Q'.mul_zero_eqv _)))
        hhalfKernel0

theorem sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (ratio : CentralLowerExcitedSpinCubeOffRayResidualNormalizedLinearRatioAt
      hw K rayCapacity)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w (Q'.le_of_lt hw) K 0 coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  exact ratio.toResidualFlowCapacityAt
    |>.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet coefficient

end CentralLowerExcitedSpinCubeOffRayResidualNormalizedLinearRatioAt

/-! ## 4. The remaining cofinal mass-free ratio -/

structure FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio
    {w : Q'} (hw : (0 : Q') < w)
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw) : Type 1 where
  ratio : ∀ K, (hK : rayCapacity.start ≤ K) →
    CentralLowerExcitedSpinCubeOffRayResidualNormalizedLinearRatioAt hw K
      (FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
        rayCapacity K hK)

namespace FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio

def toCofinalResidualFlowCapacity
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family : FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio
      hw rayCapacity) :
    FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity hw rayCapacity where
  flow_capacity := fun K hK =>
    (family.ratio K hK).toResidualFlowCapacityAt

theorem sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family : FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio
      hw rayCapacity)
    {K : Nat} (hK : rayCapacity.start ≤ K)
    (coefficient : Nat → Q') :
    (HalfPow.half * rayCapacity.delta) *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w (Q'.le_of_lt hw) K 0 coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  exact family.toCofinalResidualFlowCapacity
    |>.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
      hK coefficient

end FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound.centralLowerExcitedSpinCubeOffRayResidualEndpointPairs_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound.centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum_le_fullPairWeightSum
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound.centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound.centralLowerExcitedSpinCubeOffRayResidualFlowLoad_le_sectorSize
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound.centralLowerExcitedSpinCubeOffRayResidualFlowLoad_le_normalizedLinearCost
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound.CentralLowerExcitedSpinCubeOffRayResidualNormalizedLinearRatioAt.toResidualFlowCapacityAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound.CentralLowerExcitedSpinCubeOffRayResidualNormalizedLinearRatioAt.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound.FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio.toCofinalResidualFlowCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound.FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
