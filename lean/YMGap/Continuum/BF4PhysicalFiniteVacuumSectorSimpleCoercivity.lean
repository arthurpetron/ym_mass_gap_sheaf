/-
# A generic positive simple-path coercivity floor on every finite BF4 sector

The canonical vacuum component has total stationary mass at most one.  The
loop-erased positive paths have length at most the carrier size, so the
literal positive edge floor controls pairwise variance by

  (1 + carrierSize^2) * finite Dirichlet energy.

Dividing by that explicit positive scale produces a positive rational
coercivity floor at every coupling, cutoff, and finite half-volume.  This
removes the abstract positivity field from the moving-base scalar-payment
frontier; only quantitative comparison of the resulting shrinking floor with
cutoff increment and merger demand remains.

The floor is finite-cutoff and may deteriorate with carrier growth.  No
cutoff-uniform lower bound, moving-base capacity theorem, cofinal contraction,
thermodynamic/continuum construction, or Clay mass gap is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The generic vacuum-component mass is at most one -/

private theorem fullFiniteWeightSum_eqv_one
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) :
    listQSum
        (centralPhysicalFiniteWeight w hw cutoff half)
        (List.range
          (centralPhysicalFiniteCarrierSize w hw cutoff half)) ≈
      1 := by
  let weight := centralPhysicalFiniteWeight w hw cutoff half
  let coefficient := centralPhysicalFiniteCoefficient
    w hw cutoff half (fun _ => 1)
  have hmassMean :
      listQSum weight
          (List.range
            (centralPhysicalFiniteCarrierSize w hw cutoff half)) ≈
        finiteWeightedMean
          (centralPhysicalFiniteCarrierSize w hw cutoff half)
          weight coefficient := by
    unfold finiteWeightedMean
    apply listQSum_congr
    intro index
    unfold coefficient centralPhysicalFiniteCoefficient
    exact Q'.eqv_symm (Q'.one_mul_eqv (weight index))
  exact Q'.eqv_trans _ _ _ hmassMean
    (Q'.eqv_trans _ _ _
      (centralPhysicalFiniteWeightedMean_eqv_stationaryMean
        w hw cutoff half (fun _ => 1))
      (centralPhysicalStationaryMean_one w hw cutoff half))

theorem centralPhysicalFiniteVacuumSectorMass_le_one
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorMass
      w hw cutoff half ≤ 1 := by
  let source := centralPhysicalFiniteVacuumSectorIndices
    w hw cutoff half
  let target := List.range
    (centralPhysicalFiniteCarrierSize w hw cutoff half)
  let weight := centralPhysicalFiniteWeight w hw cutoff half
  have hsubsum : listQSum weight source ≤ listQSum weight target := by
    apply listQSum_le_of_injective
      source target weight weight (fun index => index)
    · exact centralPhysicalFiniteVacuumSectorIndices_nodup
        w hw cutoff half
    · intro index hindex
      exact List.mem_range.mpr
        (centralPhysicalFiniteVacuumSectorIndex_lt
          w hw cutoff half hindex)
    · intro left _ right _ heq
      exact heq
    · intro _ _
      exact Q'.le_refl' _
    · intro index _
      unfold weight centralPhysicalFiniteWeight
      exact centralPhysicalRowMarginal_nonnegative hw cutoff half _
  unfold centralPhysicalFiniteVacuumSectorMass finiteWeightedMass
  exact Q'.le_trans' _ _ _ hsubsum
    (Q'.le_of_eqv
      (fullFiniteWeightSum_eqv_one w hw cutoff half))

theorem centralPhysicalFiniteVacuumSectorMass_square_le_one
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) :
    let mass := centralPhysicalFiniteVacuumSectorMass
      w hw cutoff half
    mass * mass ≤ 1 := by
  let mass := centralPhysicalFiniteVacuumSectorMass w hw cutoff half
  have hmass0 : (0 : Q') ≤ mass :=
    Q'.le_of_lt
      (centralPhysicalFiniteVacuumSectorMass_pos
        w hw cutoff half)
  have hmass1 : mass ≤ 1 :=
    centralPhysicalFiniteVacuumSectorMass_le_one
      w hw cutoff half
  have hfirst : mass * mass ≤ 1 * mass :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hmass1 hmass0
  have hsecond : 1 * mass ≤ 1 * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hmass1
      (by decide : (0 : Q') ≤ 1)
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond
      (Q'.le_of_eqv (Q'.one_mul_eqv 1)))

/-! ## 2. Cleared simple-path coercivity -/

theorem centralPhysicalFiniteVacuumSectorDirichlet_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ finiteJointDirichletEnergy
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      coefficient
      (centralPhysicalFiniteKernel w hw cutoff half) := by
  exact finiteJointDirichletEnergy_nonnegative
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    coefficient (centralPhysicalFiniteKernel w hw cutoff half)
    (fun source target => by
      unfold centralPhysicalFiniteKernel
      exact centralNormalizedPhysicalReflectedKernel_nonnegative
        hw cutoff half _ _)

theorem centralPhysicalFiniteVacuumSector_edgeFloor_mul_pairwise_le_simpleScale_mul_Dirichlet
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorEdgeFloor w hw cutoff half *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w hw cutoff half coefficient ≤
      centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
          w hw cutoff half *
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
          coefficient
          (centralPhysicalFiniteKernel w hw cutoff half) := by
  let states := centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let weight := centralPhysicalFiniteWeight w hw cutoff half
  let mass := centralPhysicalFiniteVacuumSectorMass w hw cutoff half
  let floor := centralPhysicalFiniteVacuumSectorEdgeFloor w hw cutoff half
  let scale := centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
    w hw cutoff half
  let energy := finiteJointDirichletEnergy states coefficient
    (centralPhysicalFiniteKernel w hw cutoff half)
  have hraw : floor *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w hw cutoff half coefficient ≤
      (mass * mass) * (scale * energy) := by
    exact floor_mul_finiteWeightedPairwiseVariance_le
      states weight coefficient floor scale energy
      (fun state _ => by
        unfold weight centralPhysicalFiniteWeight
        exact centralPhysicalRowMarginal_nonnegative
          hw cutoff half _)
      (fun left hleft right hright => by
        unfold floor scale energy states
        exact
          centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_simpleCarrierSquareScale_mul_Dirichlet
            w hw cutoff half coefficient left right hleft hright)
  have hscaleEnergy0 : (0 : Q') ≤ scale * energy :=
    Q'.mul_nonneg _ _
      (Q'.le_of_lt
        (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos
          w hw cutoff half))
      (centralPhysicalFiniteVacuumSectorDirichlet_nonnegative
        w hw cutoff half coefficient)
  have hmassScaled :
      (mass * mass) * (scale * energy) ≤ 1 * (scale * energy) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (centralPhysicalFiniteVacuumSectorMass_square_le_one
        w hw cutoff half)
      hscaleEnergy0
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_trans' _ _ _ hmassScaled
      (Q'.le_of_eqv (Q'.one_mul_eqv (scale * energy))))

/-! ## 3. Divide by the explicit positive simple-path scale -/

def centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) : Q' :=
  Q'.divPos
    (centralPhysicalFiniteVacuumSectorEdgeFloor w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos
      w hw cutoff half)

theorem centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor_pos
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) :
    (0 : Q') < centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor
      w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor
  exact Q'.divPos_pos _ _
    (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorEdgeFloor_pos
      w hw cutoff half)

private theorem divPos_mul_right_eqv_local
    (scale value denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos (scale * value) denominator hdenominator ≈
      Q'.divPos scale denominator hdenominator * value := by
  unfold Q'.divPos
  refine Q'.eqv_trans _
    (scale * (value * Q'.recipPos denominator hdenominator)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (scale * (Q'.recipPos denominator hdenominator * value)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left scale _ _
      (Q'.mul_comm_eqv _ _)
  · exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

theorem centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor_mul_pairwise_le_Dirichlet
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor
        w hw cutoff half *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w hw cutoff half coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        coefficient
        (centralPhysicalFiniteKernel w hw cutoff half) := by
  let floor := centralPhysicalFiniteVacuumSectorEdgeFloor w hw cutoff half
  let scale := centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
    w hw cutoff half
  let pairwise := centralPhysicalFiniteVacuumSectorPairwiseVariance
    w hw cutoff half coefficient
  let energy := finiteJointDirichletEnergy
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    coefficient (centralPhysicalFiniteKernel w hw cutoff half)
  have hraw :=
    centralPhysicalFiniteVacuumSector_edgeFloor_mul_pairwise_le_simpleScale_mul_Dirichlet
      w hw cutoff half coefficient
  have hcommuted : floor * pairwise ≤ energy * scale :=
    Q'.le_trans' _ _ _ hraw
      (Q'.le_of_eqv (Q'.mul_comm_eqv scale energy))
  have hdivision :
      Q'.divPos (floor * pairwise) scale
          (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos
            w hw cutoff half) ≤ energy :=
    Q'.divPos_le_of_le_mul _ _
      (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos
        w hw cutoff half)
      hcommuted
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (divPos_mul_right_eqv_local floor pairwise scale
          (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos
            w hw cutoff half))))
    hdivision

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity.centralPhysicalFiniteVacuumSectorMass_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity.centralPhysicalFiniteVacuumSectorMass_square_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity.centralPhysicalFiniteVacuumSectorDirichlet_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity.centralPhysicalFiniteVacuumSector_edgeFloor_mul_pairwise_le_simpleScale_mul_Dirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity.centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity.centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor_mul_pairwise_le_Dirichlet
