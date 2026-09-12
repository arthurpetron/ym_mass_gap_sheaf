/-
# Base-independent reflected control of physical head centering

At w=1/400 and extent one the pulled root denominator is the SAME root
row marginal for every presentation base, even before that base is admitted.
The actual 64/65 row floor therefore bounds the squared head correction by
the squared original mean. Combined with the exact reflected residual norm,
this controls centering without a coefficient-l1 or growing-cutoff cost.

These are estimates on the existing centered vectors. Density still needs
the explicit approximation/centering limit assembly; no strict spectral gap,
geometric time, varying-coupling uniformity, or continuum result is claimed.
-/

import YMGap.Continuum.BF4PhysicalCubeCenteringPairing

namespace YMGap.Continuum.BF4PhysicalCubeCenteringControl

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeSectorComparison
open YMGap.Continuum.BF4PhysicalCubeSectorVacuum
open YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm
open YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization
open YMGap.Continuum.BF4PhysicalCubeCenteringPairing
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseVacuumPairing
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.ScaledGNSCompletion
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv
local notation "D" => cubeGNSData anchorCoupling (by decide)
local notation "M" => centralPhysicalVacuumSectorCylinderSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "j" => cubeReflectedEmbed
local notation "B" => cubeReflectedInner

def denominatorFloor : Q' := Q'.mkPos 64 65 (by decide)

theorem denominatorFloor_pos : (0 : Q') < denominatorFloor := by decide

def meanLimit (p : SectorPresentation) : CReal :=
  centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
    (w := anchorCoupling) (by decide) (by decide) p.base 0 p.coefficient

theorem pulledRoot_eq (base K : Nat) :
    centralPhysicalFinitePulledWeight anchorCoupling (by decide) base K 0 0 =
      centralPhysicalRowMarginal anchorCoupling (by decide) K 0 zeroEdgeLabelling := by
  unfold centralPhysicalFinitePulledWeight centralPhysicalFiniteWeight
  rw [centralPhysicalFiniteCutoffIndexMap_zero, centralPhysicalFiniteStateAt_zero_eq_vacuum]

theorem pulledRoot_floor (base K : Nat) :
    denominatorFloor ≤ centralPhysicalFinitePulledWeight anchorCoupling (by decide) base K 0 0 := by
  rw [pulledRoot_eq]
  exact vacuumRow_floor K

theorem correction_times_root (p : SectorPresentation) (K : Nat) :
    (correctionLimit p).approx K *
      centralPhysicalFinitePulledWeight anchorCoupling (by decide) p.base K 0 0 ≈
        (meanLimit p).approx K :=
  Q'.divPos_mul_eqv _ _ (centralPhysicalFinitePulledWeight_zero_pos
    anchorCoupling (by decide) p.base K 0)

private theorem square_product (a b : Q') : (a * b) * (a * b) ≈ (a * a) * (b * b) :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
        (Q'.mul_assoc_eqv _ _ _)))) (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))

/-- Every presentation and every original cutoff, with the SAME denominator floor. -/
theorem correction_square_bound (p : SectorPresentation) (K : Nat) :
    (denominatorFloor * denominatorFloor) *
      ((correctionLimit p).approx K * (correctionLimit p).approx K) ≤
        (meanLimit p).approx K * (meanLimit p).approx K := by
  let c := (correctionLimit p).approx K
  let r := centralPhysicalFinitePulledWeight anchorCoupling (by decide) p.base K 0 0
  have hr : denominatorFloor ≤ r := pulledRoot_floor p.base K
  have hr0 := Q'.le_trans' _ _ _ (Q'.le_of_lt denominatorFloor_pos) hr
  have hsq : denominatorFloor * denominatorFloor ≤ r * r :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ denominatorFloor hr (Q'.le_of_lt denominatorFloor_pos))
      (Q'.mul_le_mul_of_nonneg_left _ _ r hr hr0)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (c * c) hsq (SumOfSquares.q_mul_self_nonneg c)
  have heq : (c * c) * (r * r) ≈ (meanLimit p).approx K * (meanLimit p).approx K :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (square_product c r))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (correction_times_root p K))
        (Q'.mul_eqv_congr_left _ _ _ (correction_times_root p K)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv heq))

theorem meanLimit_physical (p : SectorPresentation) :
    B reflectedSectorVacuum (j (presentationToCube p)) = Quotient.mk CReal.crealSetoid (meanLimit p) := by
  have h := reflectedSectorVacuum_pairing_eq_mean ((M).embedRep p)
  rw [sectorToReflected_embed,
    centralPhysicalVacuumSectorCylinder_completedVacuumPairing_embedRep_eq_pulled] at h
  exact h

private theorem dense_pairing (left right : CubeSpan) :
    B (j left) (j right) = Quotient.mk CReal.crealSetoid
      (normalizedFormLimit (w := anchorCoupling) (by decide) (by decide) left right) :=
  scaledCompletedInner_embed D anchorNormalization left right

private theorem root_norm_nonnegative (K : Nat) :
    (0 : Q') ≤ (normalizedFormLimit (w := anchorCoupling) (by decide) (by decide) rootVector rootVector).approx K :=
  Q'.mul_nonneg _ _ ((D).self_nonneg rootVector)
    (Q'.le_trans' _ _ _ (by decide) (inversePartitionLimit_anchor_floor K))

/-- Base-independent control in the ACTUAL completed reflected form. Its
right side uses the original stationary mean, not coefficient counting. -/
theorem centeringResidual_mean_bound (p : SectorPresentation) :
    CReal.RCle
      (CReal.RCmul (Quotient.mk CReal.crealSetoid (CReal.ofQ' (denominatorFloor * denominatorFloor)))
        (B (centeringResidual p) (centeringResidual p)))
      (CReal.RCmul
        (CReal.RCmul (B reflectedSectorVacuum (j (presentationToCube p)))
          (B reflectedSectorVacuum (j (presentationToCube p))))
        (B (j rootVector) (j rootVector))) := by
  rw [centeringResidual_norm, meanLimit_physical, dense_pairing]
  intro epsilon hepsilon
  refine ⟨0, fun K _ => ?_⟩
  have h := Q'.mul_le_mul_of_nonneg_right _ _
    ((normalizedFormLimit (w := anchorCoupling) (by decide) (by decide) rootVector rootVector).approx K)
    (correction_square_bound p K) (root_norm_nonnegative K)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
    (Q'.le_trans' _ _ _ h (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hepsilon)))

end YMGap.Continuum.BF4PhysicalCubeCenteringControl

#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringControl.denominatorFloor
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringControl.denominatorFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringControl.meanLimit
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringControl.pulledRoot_eq
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringControl.pulledRoot_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringControl.correction_times_root
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringControl.correction_square_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringControl.meanLimit_physical
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringControl.centeringResidual_mean_bound
