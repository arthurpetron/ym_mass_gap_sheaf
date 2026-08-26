/-
# Contract the off-ray pair frontier to one-body vacuum-root variance

The uniform spin-cube return estimate already pays every excited ray state
directly back to the physical vacuum.  It is therefore wasteful to retain
all ordered endpoint pairs involving an off-ray state.

This module makes the sharper variance decomposition explicit.  The full
finite-sector pairwise variance is at most twice the square distance from the
vacuum root, and that rooted variance splits exactly into

    excited-ray root variance + off-ray root variance.

The existing ray return floor pays the first summand directly through the
literal ray-to-vacuum joint-kernel entries.  Thus the remaining analytic
frontier is one one-body off-ray rooted variance, rather than the previous
quadratic list of ray--off, off--ray, and off--off endpoint pairs.

No cutoff-uniform payment of the off-ray root variance is constructed here.
No completed gap, thermodynamic or continuum limit, continuum QFT, or Clay
conclusion is asserted.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootVariance

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
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-- Pointwise order passes through the constructive finite sum.  Kept local
because the argument is elementary and the imported finite-sum API exposes
congruence, but not this order lemma. -/
private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ states : List A,
    (∀ state, state ∈ states → lower state ≤ upper state) →
      listQSum lower states ≤ listQSum upper states
  | [], _ => Q'.le_refl' 0
  | head :: tail, hpointwise =>
      Q'.add_le_add
        (hpointwise head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun state hstate =>
            hpointwise state (List.mem_cons_of_mem head hstate)))

/-! ## 1. Exact ray/off-ray split of the one-body root variance -/

/-- Square distance from the vacuum, weighted only over the filtered excited
spin-cube ray. -/
def centralLowerExcitedSpinCubeFilteredRayRootVariance
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedRootVariance
    (centralLowerExcitedSpinCubeFilteredRayIndices w hw K)
    (centralPhysicalFiniteWeight w hw K 0)
    coefficient 0

/-- Square distance from the vacuum, weighted only over states outside the
excited spin-cube ray.  The vacuum itself belongs to this list and contributes
the literal zero square. -/
def centralLowerExcitedSpinCubeOffRayRootVariance
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedRootVariance
    (centralLowerExcitedSpinCubeOffRayIndices w hw K)
    (centralPhysicalFiniteWeight w hw K 0)
    coefficient 0

/-- Filtering the finite vacuum sector by excited-ray membership partitions
its rooted variance without loss. -/
theorem centralPhysicalFiniteVacuumSectorRootVariance_eqv_rayRoot_add_offRayRoot
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorRootVariance
        w hw K 0 coefficient ≈
      centralLowerExcitedSpinCubeFilteredRayRootVariance
          w hw K coefficient +
        centralLowerExcitedSpinCubeOffRayRootVariance
          w hw K coefficient := by
  unfold centralPhysicalFiniteVacuumSectorRootVariance
    finiteWeightedRootVariance
    centralLowerExcitedSpinCubeFilteredRayRootVariance
    centralLowerExcitedSpinCubeOffRayRootVariance
    centralLowerExcitedSpinCubeFilteredRayIndices
    centralLowerExcitedSpinCubeOffRayIndices
  exact listQSum_filter_partition
    (fun state =>
      centralPhysicalFiniteWeight w hw K 0 state *
        ((coefficient state + -coefficient 0) *
          (coefficient state + -coefficient 0)))
    (centralLowerExcitedSpinCubeRayMembershipTest w hw K)
    (centralPhysicalFiniteVacuumSectorIndices w hw K 0)

/-- The complete ordered pairwise variance is controlled by two copies of
the sum of the ray-root and off-ray-root one-body variances. -/
theorem centralPhysicalFiniteVacuumSectorPairwiseVariance_le_twice_rayRoot_add_offRayRoot
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorPairwiseVariance
        w hw K 0 coefficient ≤
      (centralLowerExcitedSpinCubeFilteredRayRootVariance
          w hw K coefficient +
        centralLowerExcitedSpinCubeOffRayRootVariance
          w hw K coefficient) +
      (centralLowerExcitedSpinCubeFilteredRayRootVariance
          w hw K coefficient +
        centralLowerExcitedSpinCubeOffRayRootVariance
          w hw K coefficient) := by
  have hroot :=
    centralPhysicalFiniteVacuumSectorPairwiseVariance_le_twice_rootVariance
      w hw K 0 coefficient
  have hsplit :=
    centralPhysicalFiniteVacuumSectorRootVariance_eqv_rayRoot_add_offRayRoot
      w hw K coefficient
  exact Q'.le_trans' _ _ _ hroot
    (Q'.le_of_eqv (Q'.add_eqv_congr' hsplit hsplit))

/-! ## 2. The existing return floor directly pays ray-root variance -/

/-- The directed physical energy carried only by the displayed ray-to-vacuum
spokes. -/
def centralLowerExcitedSpinCubeFilteredRayRootDirectedEnergy
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun index =>
      centralPhysicalFiniteKernel w hw K 0 index 0 *
        ((coefficient index + -coefficient 0) *
          (coefficient index + -coefficient 0)))
    (centralLowerExcitedSpinCubeFilteredRayIndices w hw K)

/-- The finite ray capacity's return-probability field pays the rooted ray
variance at strength `2 * delta`, before any global energy allocation. -/
theorem two_delta_mul_filteredRayRootVariance_le_directedEnergy
    {w : Q'} (hw : (0 : Q') < w) {K : Nat}
    (capacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (coefficient : Nat → Q') :
    (2 * capacity.delta) *
        centralLowerExcitedSpinCubeFilteredRayRootVariance
          w (Q'.le_of_lt hw) K coefficient ≤
      centralLowerExcitedSpinCubeFilteredRayRootDirectedEnergy
        w (Q'.le_of_lt hw) K coefficient := by
  unfold centralLowerExcitedSpinCubeFilteredRayRootVariance
    finiteWeightedRootVariance
    centralLowerExcitedSpinCubeFilteredRayRootDirectedEnergy
  refine Q'.le_trans' _
    (listQSum
      (fun index =>
        (2 * capacity.delta) *
          (centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0 index *
            ((coefficient index + -coefficient 0) *
              (coefficient index + -coefficient 0))))
      (centralLowerExcitedSpinCubeFilteredRayIndices
        w (Q'.le_of_lt hw) K)) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.eqv_symm
        (listQSum_mul_left (2 * capacity.delta)
          (fun index =>
            centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0 index *
              ((coefficient index + -coefficient 0) *
                (coefficient index + -coefficient 0)))
          (centralLowerExcitedSpinCubeFilteredRayIndices
            w (Q'.le_of_lt hw) K)))
  · apply listQSum_mono_local
    intro index hindex
    have hray : index ∈ centralLowerExcitedSpinCubeIndices
        w (Q'.le_of_lt hw) K :=
      (mem_centralLowerExcitedSpinCubeFilteredRayIndices_iff
        hw K index).mp hindex
    obtain ⟨offset, hoffsetRange, rfl⟩ := List.mem_map.mp hray
    have hoffset : offset < K := List.mem_range.mp hoffsetRange
    let rayIndex := centralLowerExcitedSpinCubeIndex
      w (Q'.le_of_lt hw) K offset
    let weight := centralPhysicalFiniteWeight
      w (Q'.le_of_lt hw) K 0 rayIndex
    let square := (coefficient rayIndex + -coefficient 0) *
      (coefficient rayIndex + -coefficient 0)
    let returnProbability :=
      centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset
    have hweight0 : (0 : Q') ≤ weight :=
      Q'.le_of_lt
        (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
          (centralLowerSpinCubeIndex_mem_vacuumSector hw (by omega)))
    have hsquare0 : (0 : Q') ≤ square :=
      SumOfSquares.q_mul_self_nonneg
        (coefficient rayIndex + -coefficient 0)
    have hreturn : 2 * capacity.delta ≤ returnProbability :=
      capacity.twice_le_return offset hoffset
    have hweightReturn :
        weight * (2 * capacity.delta) ≤ weight * returnProbability :=
      Q'.mul_le_mul_of_nonneg_left _ _ weight hreturn hweight0
    have hkernel : weight * returnProbability ≈
        centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 rayIndex 0 :=
      centralLowerExcitedSpinCube_weight_mul_return_eqv_kernel
        hw hoffset
    have hcoefficient :
        (2 * capacity.delta) * weight ≤
          centralPhysicalFiniteKernel
            w (Q'.le_of_lt hw) K 0 rayIndex 0 :=
      Q'.le_trans' _ (weight * (2 * capacity.delta)) _
        (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (Q'.le_trans' _ _ _ hweightReturn (Q'.le_of_eqv hkernel))
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ square
      hcoefficient hsquare0
    exact Q'.le_trans' _ (((2 * capacity.delta) * weight) * square) _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))) hscaled

private theorem centralPhysicalFiniteKernel_squareTerm_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') (left right : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteKernel w hw K 0 left right *
        ((coefficient left + -coefficient right) *
          (coefficient left + -coefficient right)) := by
  apply Q'.mul_nonneg
  · unfold centralPhysicalFiniteKernel
    exact centralNormalizedPhysicalReflectedKernel_nonnegative
      hw K 0 _ _
  · exact SumOfSquares.q_mul_self_nonneg
      (coefficient left + -coefficient right)

/-- The displayed ray-to-vacuum energy is a literal nonnegative sub-sum of
the complete physical Dirichlet form. -/
theorem filteredRayRootDirectedEnergy_le_physicalDirichlet
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeFilteredRayRootDirectedEnergy
        w hw K coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
        coefficient
        (centralPhysicalFiniteKernel w hw K 0) := by
  let sector := centralPhysicalFiniteVacuumSectorIndices w hw K 0
  let ray := centralLowerExcitedSpinCubeFilteredRayIndices w hw K
  let entry := fun left right =>
    centralPhysicalFiniteKernel w hw K 0 left right *
      ((coefficient left + -coefficient right) *
        (coefficient left + -coefficient right))
  let fullRow := fun left => listQSum (entry left) sector
  have hrow : ∀ left, left ∈ ray → entry left 0 ≤ fullRow left := by
    intro left _hleft
    unfold fullRow
    have hsum : listQSum (entry left) [0] ≤
        listQSum (entry left) sector := by
      apply listQSum_le_of_injective
        [0] sector (entry left) (entry left) (fun value => value)
      · decide
      · intro value hvalue
        have hzero : value = 0 := by
          simpa only [List.mem_singleton] using hvalue
        subst value
        exact zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0
      · intro leftValue _ rightValue _ heq
        exact heq
      · intro value hvalue
        have hzero : value = 0 := by
          simpa only [List.mem_singleton] using hvalue
        subst value
        exact Q'.le_refl' _
      · intro right _hright
        exact centralPhysicalFiniteKernel_squareTerm_nonnegative
          w hw K coefficient left right
    exact Q'.le_trans' _ (listQSum (entry left) [0]) _
      (Q'.le_of_eqv
        (Q'.eqv_symm (QPoly.q_add_zero_eqv (entry left 0)))) hsum
  unfold centralLowerExcitedSpinCubeFilteredRayRootDirectedEnergy
    finiteJointDirichletEnergy
  change listQSum (fun left => entry left 0) ray ≤
    listQSum fullRow sector
  apply listQSum_le_of_injective ray sector
    (fun left => entry left 0) fullRow (fun value => value)
  · unfold ray centralLowerExcitedSpinCubeFilteredRayIndices
    exact List.filter_sublist.nodup
      (centralPhysicalFiniteVacuumSectorIndices_nodup w hw K 0)
  · intro left hleft
    unfold ray centralLowerExcitedSpinCubeFilteredRayIndices at hleft
    exact (List.mem_filter.mp hleft).1
  · intro left _ right _ heq
    exact heq
  · exact hrow
  · intro left _hleft
    unfold fullRow
    apply listQSum_nonnegative_on
    intro right _hright
    exact centralPhysicalFiniteKernel_squareTerm_nonnegative
      w hw K coefficient left right

/-- Combining the exact return payment with sub-sum monotonicity gives a
coefficient-uniform ray-root coercivity theorem at strength `2 * delta`. -/
theorem two_delta_mul_filteredRayRootVariance_le_physicalDirichlet
    {w : Q'} (hw : (0 : Q') < w) {K : Nat}
    (capacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (coefficient : Nat → Q') :
    (2 * capacity.delta) *
        centralLowerExcitedSpinCubeFilteredRayRootVariance
          w (Q'.le_of_lt hw) K coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  exact Q'.le_trans' _ _ _
    (two_delta_mul_filteredRayRootVariance_le_directedEnergy
      hw capacity coefficient)
    (filteredRayRootDirectedEnergy_le_physicalDirichlet
      w (Q'.le_of_lt hw) K coefficient)

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootVariance

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootVariance.centralPhysicalFiniteVacuumSectorRootVariance_eqv_rayRoot_add_offRayRoot
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootVariance.centralPhysicalFiniteVacuumSectorPairwiseVariance_le_twice_rayRoot_add_offRayRoot
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootVariance.two_delta_mul_filteredRayRootVariance_le_directedEnergy
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootVariance.filteredRayRootDirectedEnergy_le_physicalDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootVariance.two_delta_mul_filteredRayRootVariance_le_physicalDirichlet
