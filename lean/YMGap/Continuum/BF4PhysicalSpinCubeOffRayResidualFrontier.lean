/-
# The exact off-ray residual frontier after spin-cube ray coercivity

The uniform spin-cube ray theorem controls only ray--ray stationary demand.
This module partitions the complete finite physical vacuum sector by literal
membership in that ray.  The full stationary pairwise variance is exactly

  ray--ray + (ray--off + off--ray + off--off).

The filtered ray is proved to be a permutation of the explicit spin-offset
enumeration used by the uniform ray theorem.  The complement is nonempty at
every cutoff because it contains the vacuum index, which no excited ray
index can equal.

Half of the physical Dirichlet energy pays the already proved ray coercivity.
Consequently one coefficient-uniform inequality paying the displayed
off-ray residual with the other half compiles to full-sector Dirichlet
coercivity.  That residual certificate is stated as an honest Type-level
frontier but is not inhabited uniformly here.

No full-sector transfer gap, thermodynamic or continuum limit, continuum
QFT, or Clay theorem is claimed.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
import YMGap.Continuum.Z4CanonicalPolymerUniverse

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal ray/complement partition of the full finite sector -/

def centralLowerExcitedSpinCubeRayMembershipTest
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Nat → Bool :=
  fun index => decide
    (index ∈ centralLowerExcitedSpinCubeIndices w hw K)

def centralLowerExcitedSpinCubeFilteredRayIndices
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw K 0).filter
    (centralLowerExcitedSpinCubeRayMembershipTest w hw K)

def centralLowerExcitedSpinCubeOffRayIndices
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw K 0).filter
    (fun index =>
      !(centralLowerExcitedSpinCubeRayMembershipTest w hw K index))

theorem mem_centralLowerExcitedSpinCubeFilteredRayIndices_iff
    {w : Q'} (hw : (0 : Q') < w) (K index : Nat) :
    index ∈ centralLowerExcitedSpinCubeFilteredRayIndices
        w (Q'.le_of_lt hw) K ↔
      index ∈ centralLowerExcitedSpinCubeIndices
        w (Q'.le_of_lt hw) K := by
  constructor
  · intro hindex
    have hparts := List.mem_filter.mp hindex
    simpa only [centralLowerExcitedSpinCubeRayMembershipTest,
      decide_eq_true_eq] using hparts.2
  · intro hindex
    apply List.mem_filter.mpr
    exact ⟨
      centralLowerExcitedSpinCubeIndices_subset_vacuumSector
        hw K index hindex,
      by
        simp only [centralLowerExcitedSpinCubeRayMembershipTest,
          decide_eq_true_eq]
        exact hindex⟩

/-- The carrier-ordered filtered ray and the spin-ordered explicit ray have
the same vertices, without duplicates. -/
theorem centralLowerExcitedSpinCubeFilteredRayIndices_perm_rayIndices
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    (centralLowerExcitedSpinCubeFilteredRayIndices
        w (Q'.le_of_lt hw) K).Perm
      (centralLowerExcitedSpinCubeIndices
        w (Q'.le_of_lt hw) K) := by
  apply perm_of_nodup_mem_iff
  · exact List.filter_sublist.nodup
      (centralPhysicalFiniteVacuumSectorIndices_nodup
        w (Q'.le_of_lt hw) K 0)
  · exact centralLowerExcitedSpinCubeIndices_nodup hw K
  · intro index
    exact mem_centralLowerExcitedSpinCubeFilteredRayIndices_iff hw K index

private theorem zero_not_mem_excitedRay
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    0 ∉ centralLowerExcitedSpinCubeIndices
      w (Q'.le_of_lt hw) K := by
  intro hzero
  obtain ⟨offset, hoffsetMem, heq⟩ := List.mem_map.mp hzero
  have hoffset : offset < K := List.mem_range.mp hoffsetMem
  exact centralLowerExcitedSpinCubeIndex_ne_zero hw hoffset heq

/-- The residual is never an empty syntactic complement: it contains the
physical vacuum root at every cutoff, including the empty excited ray. -/
theorem zero_mem_centralLowerExcitedSpinCubeOffRayIndices
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    0 ∈ centralLowerExcitedSpinCubeOffRayIndices
      w (Q'.le_of_lt hw) K := by
  apply List.mem_filter.mpr
  refine ⟨zero_mem_centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0, ?_⟩
  have hfalse : decide
      (0 ∈ centralLowerExcitedSpinCubeIndices
        w (Q'.le_of_lt hw) K) = false :=
    decide_eq_false_iff_not.mpr (zero_not_mem_excitedRay hw K)
  unfold centralLowerExcitedSpinCubeRayMembershipTest
  rw [hfalse]
  rfl

/-! ## 2. Exact stationary pairwise blocks -/

def centralLowerExcitedSpinCubeFilteredRayPairwiseVariance
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (centralLowerExcitedSpinCubeFilteredRayIndices w hw K)
    (centralLowerExcitedSpinCubeFilteredRayIndices w hw K)
    coefficient
    (finiteStationaryProductJoint
      (centralPhysicalFiniteWeight w hw K 0))

def centralLowerExcitedSpinCubeRayOffPairwiseVariance
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (centralLowerExcitedSpinCubeFilteredRayIndices w hw K)
    (centralLowerExcitedSpinCubeOffRayIndices w hw K)
    coefficient
    (finiteStationaryProductJoint
      (centralPhysicalFiniteWeight w hw K 0))

def centralLowerExcitedSpinCubeOffRayPairwiseVariance
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (centralLowerExcitedSpinCubeOffRayIndices w hw K)
    (centralLowerExcitedSpinCubeFilteredRayIndices w hw K)
    coefficient
    (finiteStationaryProductJoint
      (centralPhysicalFiniteWeight w hw K 0))

def centralLowerExcitedSpinCubeOffOffPairwiseVariance
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (centralLowerExcitedSpinCubeOffRayIndices w hw K)
    (centralLowerExcitedSpinCubeOffRayIndices w hw K)
    coefficient
    (finiteStationaryProductJoint
      (centralPhysicalFiniteWeight w hw K 0))

/-- All ordered endpoint demands not already in the ray--ray block. -/
def centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  centralLowerExcitedSpinCubeRayOffPairwiseVariance
      w hw K coefficient +
    (centralLowerExcitedSpinCubeOffRayPairwiseVariance
        w hw K coefficient +
      centralLowerExcitedSpinCubeOffOffPairwiseVariance
        w hw K coefficient)

private theorem listQSum_perm_local {A : Type} (value : A → Q') :
    ∀ {left right : List A}, left.Perm right →
      listQSum value left ≈ listQSum value right
  | _, _, List.Perm.nil => Q'.eqv_refl 0
  | _, _, List.Perm.cons _ hperm =>
      Q'.add_eqv_congr_left _ _ _ (listQSum_perm_local value hperm)
  | _, _, List.Perm.swap first second rest => by
      change value second + (value first + listQSum value rest) ≈
        value first + (value second + listQSum value rest)
      refine Q'.eqv_trans _
        ((value second + value first) + listQSum value rest) _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((value first + value second) + listQSum value rest) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.add_comm_eqv _ _))
        (Q'.add_assoc_eqv _ _ _)
  | _, _, List.Perm.trans hleft hright =>
      Q'.eqv_trans _ _ _
        (listQSum_perm_local value hleft)
        (listQSum_perm_local value hright)

private theorem finiteJointDirichletBlock_perm_local
    {State : Type}
    {leftOld leftNew rightOld rightNew : List State}
    (hleft : leftOld.Perm leftNew) (hright : rightOld.Perm rightNew)
    (coefficient : State → Q') (joint : State → State → Q') :
    finiteJointDirichletBlock leftOld rightOld coefficient joint ≈
      finiteJointDirichletBlock leftNew rightNew coefficient joint := by
  let entry := fun left right =>
    joint left right *
      ((coefficient left + -coefficient right) *
        (coefficient left + -coefficient right))
  unfold finiteJointDirichletBlock
  refine Q'.eqv_trans _
    (listQSum (fun left => listQSum (entry left) rightOld) leftNew) _ ?_ ?_
  · exact listQSum_perm_local _ hleft
  · apply listQSum_congr
    intro left
    exact listQSum_perm_local (entry left) hright

theorem centralLowerExcitedSpinCubeFilteredRayPairwiseVariance_eqv_ray
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeFilteredRayPairwiseVariance
        w (Q'.le_of_lt hw) K coefficient ≈
      centralLowerExcitedSpinCubeRayPairwiseVariance
        w (Q'.le_of_lt hw) K coefficient := by
  unfold centralLowerExcitedSpinCubeFilteredRayPairwiseVariance
    centralLowerExcitedSpinCubeRayPairwiseVariance
    finiteWeightedPairwiseVariance
  change finiteJointDirichletBlock
      (centralLowerExcitedSpinCubeFilteredRayIndices
        w (Q'.le_of_lt hw) K)
      (centralLowerExcitedSpinCubeFilteredRayIndices
        w (Q'.le_of_lt hw) K)
      coefficient _ ≈
    finiteJointDirichletBlock
      (centralLowerExcitedSpinCubeIndices
        w (Q'.le_of_lt hw) K)
      (centralLowerExcitedSpinCubeIndices
        w (Q'.le_of_lt hw) K)
      coefficient _
  exact finiteJointDirichletBlock_perm_local
    (centralLowerExcitedSpinCubeFilteredRayIndices_perm_rayIndices hw K)
    (centralLowerExcitedSpinCubeFilteredRayIndices_perm_rayIndices hw K)
    coefficient _

/-- Exact causal split of the full stationary pairwise form into the already
controlled ray demand and the three remaining ordered off-ray blocks. -/
theorem centralPhysicalFiniteVacuumSectorPairwiseVariance_eqv_ray_add_offRayResidual
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorPairwiseVariance
        w (Q'.le_of_lt hw) K 0 coefficient ≈
      centralLowerExcitedSpinCubeRayPairwiseVariance
          w (Q'.le_of_lt hw) K coefficient +
        centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance
          w (Q'.le_of_lt hw) K coefficient := by
  let states := centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw) K 0
  let test := centralLowerExcitedSpinCubeRayMembershipTest
    w (Q'.le_of_lt hw) K
  let weight := centralPhysicalFiniteWeight
    w (Q'.le_of_lt hw) K 0
  have hfour := finiteJointDirichletEnergy_filter_four_blocks
    states test coefficient (finiteStationaryProductJoint weight)
  have hray :=
    centralLowerExcitedSpinCubeFilteredRayPairwiseVariance_eqv_ray
      hw K coefficient
  unfold centralPhysicalFiniteVacuumSectorPairwiseVariance
    finiteWeightedPairwiseVariance
  refine Q'.eqv_trans _ _ _ hfour ?_
  refine Q'.eqv_trans _
    (centralLowerExcitedSpinCubeFilteredRayPairwiseVariance
        w (Q'.le_of_lt hw) K coefficient +
      (centralLowerExcitedSpinCubeRayOffPairwiseVariance
          w (Q'.le_of_lt hw) K coefficient +
        (centralLowerExcitedSpinCubeOffRayPairwiseVariance
            w (Q'.le_of_lt hw) K coefficient +
          centralLowerExcitedSpinCubeOffOffPairwiseVariance
            w (Q'.le_of_lt hw) K coefficient))) _ ?_ ?_
  · unfold states test weight
    unfold centralLowerExcitedSpinCubeFilteredRayPairwiseVariance
      centralLowerExcitedSpinCubeRayOffPairwiseVariance
      centralLowerExcitedSpinCubeOffRayPairwiseVariance
      centralLowerExcitedSpinCubeOffOffPairwiseVariance
      centralLowerExcitedSpinCubeFilteredRayIndices
      centralLowerExcitedSpinCubeOffRayIndices
    exact Q'.add_assoc_eqv _ _ _
  · unfold centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance
    exact Q'.add_eqv_congr' hray (Q'.eqv_refl _)

theorem centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_nonnegative
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (coefficient : Nat → Q') :
    (0 : Q') ≤
      centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance
        w (Q'.le_of_lt hw) K coefficient := by
  have hjoint : ∀ left right,
      (0 : Q') ≤ finiteStationaryProductJoint
        (centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0)
        left right := by
    intro left right
    unfold finiteStationaryProductJoint
    exact Q'.mul_nonneg _ _
      (centralPhysicalRowMarginal_nonnegative
        (Q'.le_of_lt hw) K 0 _)
      (centralPhysicalRowMarginal_nonnegative
        (Q'.le_of_lt hw) K 0 _)
  unfold centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance
    centralLowerExcitedSpinCubeRayOffPairwiseVariance
    centralLowerExcitedSpinCubeOffRayPairwiseVariance
    centralLowerExcitedSpinCubeOffOffPairwiseVariance
  exact Q'.zero_le_add _ _
    (finiteJointDirichletBlock_nonnegative _ _ coefficient _ hjoint)
    (Q'.zero_le_add _ _
      (finiteJointDirichletBlock_nonnegative _ _ coefficient _ hjoint)
      (finiteJointDirichletBlock_nonnegative _ _ coefficient _ hjoint))

/-! ## 3. The exact residual certificate and lossless compiler -/

def centralLowerExcitedSpinCubeSharedCoercivityFloor
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (capacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) : Q' :=
  HalfPow.half * capacity.delta

theorem centralLowerExcitedSpinCubeSharedCoercivityFloor_pos
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (capacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    (0 : Q') <
      centralLowerExcitedSpinCubeSharedCoercivityFloor capacity := by
  unfold centralLowerExcitedSpinCubeSharedCoercivityFloor
  exact ExpNeg.half_mul_pos _ capacity.delta_pos

/-- The remaining uniform analytic datum after the proved ray estimate.  It
pays every ordered pair involving at least one off-ray state using the half
of physical Dirichlet energy reserved from the ray proof. -/
structure CentralLowerExcitedSpinCubeOffRayResidualCoercivityAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (capacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    Type 1 where
  residual_coercivity : ∀ coefficient : Nat → Q',
    centralLowerExcitedSpinCubeSharedCoercivityFloor capacity *
        centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance
          w (Q'.le_of_lt hw) K coefficient ≤
      HalfPow.half * finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)

namespace CentralLowerExcitedSpinCubeOffRayResidualCoercivityAt

private theorem sharedFloor_mul_ray_le_half_Dirichlet
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {capacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (_certificate :
      CentralLowerExcitedSpinCubeOffRayResidualCoercivityAt
        hw K capacity)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeSharedCoercivityFloor capacity *
        centralLowerExcitedSpinCubeRayPairwiseVariance
          w (Q'.le_of_lt hw) K coefficient ≤
      HalfPow.half * finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  have hray :=
    BF4PhysicalSpinCubeRayDirichletCoercivity.CentralLowerExcitedSpinCubeFiniteRayCapacityAt.delta_mul_rayPairwiseVariance_le_physicalDirichlet
      capacity coefficient
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
    hray HalfPow.half_nonneg
  unfold centralLowerExcitedSpinCubeSharedCoercivityFloor
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.mul_assoc_eqv _ _ _))
    hscaled

/-- Half-energy allocation combines the proved ray block and the one honest
residual obligation into full finite-sector Dirichlet coercivity. -/
theorem sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {capacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (certificate :
      CentralLowerExcitedSpinCubeOffRayResidualCoercivityAt
        hw K capacity)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeSharedCoercivityFloor capacity *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w (Q'.le_of_lt hw) K 0 coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  let ray := centralLowerExcitedSpinCubeRayPairwiseVariance
    w (Q'.le_of_lt hw) K coefficient
  let residual := centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance
    w (Q'.le_of_lt hw) K coefficient
  let energy := finiteJointDirichletEnergy
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    coefficient
    (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)
  have hray := certificate.sharedFloor_mul_ray_le_half_Dirichlet coefficient
  have hresidual := certificate.residual_coercivity coefficient
  have hsum := Q'.add_le_add hray hresidual
  refine Q'.le_trans' _
    (centralLowerExcitedSpinCubeSharedCoercivityFloor capacity *
      (ray + residual)) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_left _ _ _
        (centralPhysicalFiniteVacuumSectorPairwiseVariance_eqv_ray_add_offRayResidual
          hw K coefficient))
  refine Q'.le_trans' _
    (centralLowerExcitedSpinCubeSharedCoercivityFloor capacity * ray +
      centralLowerExcitedSpinCubeSharedCoercivityFloor capacity * residual) _
    (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _)) ?_
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv (ExpNeg.two_halves energy))

end CentralLowerExcitedSpinCubeOffRayResidualCoercivityAt

/-! ## 4. The one cofinal off-ray family now missing -/

/-- A constructively cofinal family of exactly the residual certificates
isolated above.  The ray capacity and its positive constant are data already
supplied; this structure asks only for uniform control of endpoint demands
involving at least one off-ray state.  No inhabitant is asserted here. -/
structure FixedNomeCofinalSpinCubeOffRayResidualCoercivity
    {w : Q'} (hw : (0 : Q') < w)
    (capacity : FixedNomeCofinalSpinCubeRayCapacity hw) : Type 1 where
  residual : ∀ K, (hK : capacity.start ≤ K) →
    CentralLowerExcitedSpinCubeOffRayResidualCoercivityAt hw K
      (BF4PhysicalSpinCubeRayDirichletCoercivity.FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
        capacity K hK)

namespace FixedNomeCofinalSpinCubeOffRayResidualCoercivity

theorem sharedFloor_pos
    {w : Q'} {hw : (0 : Q') < w}
    {capacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (_family :
      FixedNomeCofinalSpinCubeOffRayResidualCoercivity hw capacity) :
    (0 : Q') < HalfPow.half * capacity.delta := by
  exact ExpNeg.half_mul_pos _ capacity.delta_pos

/-- The cofinal residual family supplies a cutoff-independent full-sector
Dirichlet coercivity constant.  This is still a finite-cutoff family; a
uniform sector-mass floor and the existing form/completion bridges are the
subsequent contraction steps. -/
theorem sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w}
    {capacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualCoercivity hw capacity)
    {K : Nat} (hK : capacity.start ≤ K)
    (coefficient : Nat → Q') :
    (HalfPow.half * capacity.delta) *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w (Q'.le_of_lt hw) K 0 coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  exact CentralLowerExcitedSpinCubeOffRayResidualCoercivityAt.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
    (family.residual K hK) coefficient

end FixedNomeCofinalSpinCubeOffRayResidualCoercivity

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier.centralLowerExcitedSpinCubeFilteredRayIndices_perm_rayIndices
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier.zero_mem_centralLowerExcitedSpinCubeOffRayIndices
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier.centralPhysicalFiniteVacuumSectorPairwiseVariance_eqv_ray_add_offRayResidual
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier.centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier.centralLowerExcitedSpinCubeSharedCoercivityFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier.CentralLowerExcitedSpinCubeOffRayResidualCoercivityAt.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier.FixedNomeCofinalSpinCubeOffRayResidualCoercivity.sharedFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier.FixedNomeCofinalSpinCubeOffRayResidualCoercivity.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
