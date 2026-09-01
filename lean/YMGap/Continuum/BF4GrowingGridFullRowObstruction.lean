/-
# The high-spin growing grid has bounded effective multiplicity

The complete literal grid row is larger than its selected summand, but the
minimum defining the common replica floor may be tested at the extreme pair
`(firstSpin, replica) = (1, K)`.  The decorated one-face raw-row ceiling then
bounds that ratio by a fixed constant times the degree-thirteen activity at
spin `K`.  Its exact recurrence absorbs the linear replica count `K + 1`.

Consequently the *computed* effective multiplicity of this high-spin grid is
uniformly bounded for every positive cutoff.  This closes this particular
replica family as a route to cofinal divergence; it does not rule out a
low-spin growing-volume family, establish a physical uniform gap, construct a
continuum measure, or prove the Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Constructive.GeomBeatsLinear
import YMGap.Continuum.BF4GrowingGridRawRowCeiling

namespace YMGap.Continuum.BF4GrowingGridFullRowObstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePhysicalTerm
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound
open YMGap.Continuum.BF4DisjointClosedSpinSurfacePositiveGrid
open YMGap.Continuum.BF4GrowingGridRawRowCeiling
open YMGap.Continuum.BF4GrowingGridSelectedTermRowFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayGrowingGridReplicationWitness
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPositiveReplicationGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationGate
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The extreme-pair raw-row ratio ceiling -/

/-- The fixed positive lower witness in the source row at spin one. -/
def gridHighSpinSourceLower : Q' :=
  (coeffW anchorCoupling 1) ^ 6

theorem gridHighSpinSourceLower_pos :
    (0 : Q') < gridHighSpinSourceLower := by
  unfold gridHighSpinSourceLower anchorCoupling coeffW qpow c4
  decide

/-- The raw-row majorant, ordered so that the cutoff-dependent activity is
the final factor. -/
def gridHighSpinRatioNumerator (cutoff : Nat) : Q' :=
  (anchorDecoratedFaceActivity 1 *
      centralSpinCubeResidualCarrierCeiling) *
    anchorDecoratedFaceActivity cutoff

theorem gridHighSpinRatioNumerator_eqv_rawCeiling (cutoff : Nat) :
    gridHighSpinRatioNumerator cutoff ≈
      (anchorDecoratedFaceActivity 1 *
        anchorDecoratedFaceActivity cutoff) *
        centralSpinCubeResidualCarrierCeiling := by
  unfold gridHighSpinRatioNumerator
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv
      (anchorDecoratedFaceActivity 1)
      centralSpinCubeResidualCarrierCeiling
      (anchorDecoratedFaceActivity cutoff)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (anchorDecoratedFaceActivity 1) _ _
      (Q'.mul_comm_eqv centralSpinCubeResidualCarrierCeiling
        (anchorDecoratedFaceActivity cutoff))) ?_
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv
      (anchorDecoratedFaceActivity 1)
      (anchorDecoratedFaceActivity cutoff)
      centralSpinCubeResidualCarrierCeiling)

def gridHighSpinRawRatioCeiling (cutoff : Nat) : Q' :=
  Q'.divPos (gridHighSpinRatioNumerator cutoff)
    gridHighSpinSourceLower gridHighSpinSourceLower_pos

theorem gridHighSpinRatioNumerator_nonnegative (cutoff : Nat) :
    (0 : Q') ≤ gridHighSpinRatioNumerator cutoff := by
  unfold gridHighSpinRatioNumerator
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (tailTerm_nonneg (by decide) 13 1)
      (Q'.le_of_lt centralSpinCubeResidualCarrierCeiling_pos))
    (tailTerm_nonneg (by decide) 13 cutoff)

theorem gridHighSpinRawRatioCeiling_nonnegative (cutoff : Nat) :
    (0 : Q') ≤ gridHighSpinRawRatioCeiling cutoff := by
  unfold gridHighSpinRawRatioCeiling Q'.divPos
  exact Q'.mul_nonneg _ _
    (gridHighSpinRatioNumerator_nonnegative cutoff)
    (Q'.le_of_lt
      (Q'.recipPos_pos gridHighSpinSourceLower
        gridHighSpinSourceLower_pos))

/-- Testing the finite minimum at `(offset, replica) = (0, K)` makes the full
computed common floor no larger than the decorated extreme-pair ceiling. -/
theorem growingGridRawRowRatioFloor_le_highSpinCeiling
    {cutoff : Nat} (hcutoff : 0 < cutoff) :
    (growingGridPositiveRawReplication
        anchorCoupling (by decide) cutoff).rawRowRatioFloor ≤
      gridHighSpinRawRatioCeiling cutoff := by
  let replication := growingGridPositiveRawReplication
    anchorCoupling (by decide) cutoff
  let sourceRow := centralPhysicalPositiveRawRowMass
    anchorCoupling (by decide) cutoff 0
    (centralLowerSpinCubeState 1)
  let targetRow := centralPhysicalPositiveRawRowMass
    anchorCoupling (by decide) cutoff 0
    (centralGridRowState 1 cutoff)
  have hsourcePos : (0 : Q') < sourceRow := by
    unfold sourceRow
    exact centralPhysicalPositiveRawRowMass_pos
      (centralLowerSpinCubeState_mem_centralPositiveHalfStates
        (by decide) (by omega))
  have hfloorClip := replication.rawRowRatioFloor_le_clippedRawRowRatio
    0 cutoff (by omega) (by
      change cutoff < cutoff + 1
      omega)
  have hclipRatio :
      replication.clippedRawRowRatio (0, cutoff) ≤
        Q'.divPos targetRow sourceRow hsourcePos := by
    unfold CentralLowerExcitedSpinCubePositiveRawReplication.clippedRawRowRatio
    split
    next _hpair =>
      change Q'.min' 1 (Q'.divPos targetRow sourceRow _) ≤
        Q'.divPos targetRow sourceRow hsourcePos
      exact Q'.min_le_right'
        1 (Q'.divPos targetRow sourceRow hsourcePos)
    next hpair =>
      exfalso
      apply hpair
      exact ⟨hcutoff, by
        unfold replication
        change cutoff < cutoff + 1
        omega⟩
  have hsourceLower : gridHighSpinSourceLower ≤ sourceRow := by
    have hterm := centralLowerSpinCubePhysicalTerm_le_rawRowMass
      (w := anchorCoupling) (by decide) cutoff 1
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (centralLowerSpinCubePhysicalTerm_eqv
          anchorCoupling (K := cutoff) (spin := 1) (by omega))) hterm
  have htargetUpper : targetRow ≤
      gridHighSpinRatioNumerator cutoff := by
    unfold targetRow
    exact Q'.le_trans' _ _ _
      (centralGridPositiveRawRow_le_decoratedActivities_mul_ceiling
        (cutoff := cutoff) (firstSpin := 1) (replica := cutoff)
        (by omega) (Nat.le_refl cutoff))
      (Q'.ge_of_eqv (gridHighSpinRatioNumerator_eqv_rawCeiling cutoff))
  have hratioUpper : Q'.divPos targetRow sourceRow hsourcePos ≤
      gridHighSpinRawRatioCeiling cutoff := by
    apply Q'.divPos_le_of_le_mul
    have hscaledLower :
        gridHighSpinRawRatioCeiling cutoff * gridHighSpinSourceLower ≤
          gridHighSpinRawRatioCeiling cutoff * sourceRow :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hsourceLower
        (gridHighSpinRawRatioCeiling_nonnegative cutoff)
    exact Q'.le_trans' _ _ _ htargetUpper
      (Q'.le_trans' _ _ _
        (Q'.ge_of_eqv
          (Q'.divPos_mul_eqv
            (gridHighSpinRatioNumerator cutoff)
            gridHighSpinSourceLower gridHighSpinSourceLower_pos))
        hscaledLower)
  exact Q'.le_trans' _ _ _ hfloorClip
    (Q'.le_trans' _ _ _ hclipRatio hratioUpper)

/-! ## 2. The decorated recurrence absorbs the linear replica count -/

theorem twice_anchorDecoratedRatio_le_one :
    (2 : Q') * anchorDecoratedRatio ≤ (1 : Q') := by
  unfold anchorDecoratedRatio anchorCoupling qpow
  decide

/-- Direct recurrence proof that `(K + 1) * activity(K)` is bounded by twice
the spin-one activity for every `K = 1 + offset`. -/
theorem linear_anchorDecoratedFaceActivity_le_two_at_one :
    ∀ offset : Nat,
      Q'.ofNat (offset + 2) *
          anchorDecoratedFaceActivity (1 + offset) ≤
        Q'.ofNat 2 * anchorDecoratedFaceActivity 1
  | 0 => Q'.le_refl' _
  | offset + 1 => by
      have hrecurrence := anchorDecoratedFaceActivity_succ_ratio offset
      have hscaledRecurrence := Q'.mul_le_mul_of_nonneg_left _ _ _
        hrecurrence (zero_le_ofNat (offset + 3))
      have hregroup :
          Q'.ofNat (offset + 3) *
              (anchorDecoratedRatio *
                anchorDecoratedFaceActivity (1 + offset)) ≈
            (Q'.ofNat (offset + 3) * anchorDecoratedRatio) *
              anchorDecoratedFaceActivity (1 + offset) :=
        Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (Q'.ofNat (offset + 3)) anchorDecoratedRatio
            (anchorDecoratedFaceActivity (1 + offset)))
      have hlinearStep := ofNat_succ_succ_mul_le
        anchorDecoratedRatio_nonnegative
        twice_anchorDecoratedRatio_le_one (offset + 1)
      have hactivity0 : (0 : Q') ≤
          anchorDecoratedFaceActivity (1 + offset) :=
        tailTerm_nonneg (by decide) 13 (1 + offset)
      have hscaledLinear := Q'.mul_le_mul_of_nonneg_right _ _ _
        hlinearStep hactivity0
      exact Q'.le_trans' _ _ _ hscaledRecurrence
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup)
          (Q'.le_trans' _ _ _ hscaledLinear
            (linear_anchorDecoratedFaceActivity_le_two_at_one offset)))

/-- The cutoff-independent factor multiplying the final decorated activity. -/
def gridHighSpinObstructionConstant : Q' :=
  Q'.divPos
    (anchorDecoratedFaceActivity 1 *
      centralSpinCubeResidualCarrierCeiling)
    gridHighSpinSourceLower gridHighSpinSourceLower_pos

theorem gridHighSpinObstructionConstant_nonnegative :
    (0 : Q') ≤ gridHighSpinObstructionConstant := by
  unfold gridHighSpinObstructionConstant Q'.divPos
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (tailTerm_nonneg (by decide) 13 1)
      (Q'.le_of_lt centralSpinCubeResidualCarrierCeiling_pos))
    (Q'.le_of_lt
      (Q'.recipPos_pos gridHighSpinSourceLower
        gridHighSpinSourceLower_pos))

theorem gridHighSpinRawRatioCeiling_eqv_constant_mul_activity
    (cutoff : Nat) :
    gridHighSpinRawRatioCeiling cutoff ≈
      gridHighSpinObstructionConstant *
        anchorDecoratedFaceActivity cutoff := by
  unfold gridHighSpinRawRatioCeiling gridHighSpinRatioNumerator
    gridHighSpinObstructionConstant Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv
      (anchorDecoratedFaceActivity 1 *
        centralSpinCubeResidualCarrierCeiling)
      (anchorDecoratedFaceActivity cutoff)
      (Q'.recipPos gridHighSpinSourceLower
        gridHighSpinSourceLower_pos)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      (anchorDecoratedFaceActivity 1 *
        centralSpinCubeResidualCarrierCeiling) _ _
      (Q'.mul_comm_eqv
        (anchorDecoratedFaceActivity cutoff)
        (Q'.recipPos gridHighSpinSourceLower
          gridHighSpinSourceLower_pos))) ?_
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv
      (anchorDecoratedFaceActivity 1 *
        centralSpinCubeResidualCarrierCeiling)
      (Q'.recipPos gridHighSpinSourceLower
        gridHighSpinSourceLower_pos)
      (anchorDecoratedFaceActivity cutoff))

/-- A fixed ceiling for the actual high-spin-grid effective multiplicity. -/
def gridHighSpinEffectiveMultiplicityCeiling : Q' :=
  gridHighSpinObstructionConstant *
    (Q'.ofNat 2 * anchorDecoratedFaceActivity 1)

/-- **Full-row high-spin-grid obstruction.**  The actual finite minimum, not
merely the selected lower witness, makes the computed effective multiplicity
uniformly bounded at all positive cutoffs. -/
theorem growingGridComputedEffectiveMultiplicity_le_fixedCeiling
    {cutoff : Nat} (hcutoff : 0 < cutoff) :
    (growingGridPositiveRawReplication
        anchorCoupling (by decide) cutoff).toWeighted.effectiveMultiplicity ≤
      gridHighSpinEffectiveMultiplicityCeiling := by
  have hfloor := growingGridRawRowRatioFloor_le_highSpinCeiling hcutoff
  have heffective :
      (growingGridPositiveRawReplication
          anchorCoupling (by decide) cutoff).toWeighted.effectiveMultiplicity ≤
        Q'.ofNat (cutoff + 1) * gridHighSpinRawRatioCeiling cutoff := by
    change Q'.ofNat (cutoff + 1) *
        (growingGridPositiveRawReplication
          anchorCoupling (by decide) cutoff).rawRowRatioFloor ≤
      Q'.ofNat (cutoff + 1) * gridHighSpinRawRatioCeiling cutoff
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hfloor
      (zero_le_ofNat (cutoff + 1))
  have hrewrite :
      Q'.ofNat (cutoff + 1) * gridHighSpinRawRatioCeiling cutoff ≈
        gridHighSpinObstructionConstant *
          (Q'.ofNat (cutoff + 1) *
            anchorDecoratedFaceActivity cutoff) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (cutoff + 1)) _ _
        (gridHighSpinRawRatioCeiling_eqv_constant_mul_activity cutoff)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (Q'.ofNat (cutoff + 1))
          gridHighSpinObstructionConstant
          (anchorDecoratedFaceActivity cutoff))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_comm_eqv (Q'.ofNat (cutoff + 1))
          gridHighSpinObstructionConstant)) ?_
    exact Q'.mul_assoc_eqv gridHighSpinObstructionConstant
      (Q'.ofNat (cutoff + 1))
      (anchorDecoratedFaceActivity cutoff)
  have hlinear :
      Q'.ofNat (cutoff + 1) * anchorDecoratedFaceActivity cutoff ≤
        Q'.ofNat 2 * anchorDecoratedFaceActivity 1 := by
    have h := linear_anchorDecoratedFaceActivity_le_two_at_one
      (cutoff - 1)
    have hone : 1 ≤ cutoff := by omega
    have hspin : 1 + (cutoff - 1) = cutoff :=
      Nat.add_sub_of_le hone
    have hcount : cutoff - 1 + 2 = cutoff + 1 := by omega
    rw [hspin, hcount] at h
    exact h
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hlinear
    gridHighSpinObstructionConstant_nonnegative
  exact Q'.le_trans' _ _ _ heffective
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hrewrite) hscaled)

end YMGap.Continuum.BF4GrowingGridFullRowObstruction

#print axioms
  YMGap.Continuum.BF4GrowingGridFullRowObstruction.growingGridRawRowRatioFloor_le_highSpinCeiling
#print axioms
  YMGap.Continuum.BF4GrowingGridFullRowObstruction.linear_anchorDecoratedFaceActivity_le_two_at_one
#print axioms
  YMGap.Continuum.BF4GrowingGridFullRowObstruction.growingGridComputedEffectiveMultiplicity_le_fixedCeiling
