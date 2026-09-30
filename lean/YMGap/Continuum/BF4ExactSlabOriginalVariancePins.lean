/-
# Original partition and centered variance pins

The chronological replica determinant uses the SAME unnormalized full-action
form as the existing conditional projections. These exact pins and the
constructed partition positivity justify cancellation of its common mass.
-/

import YMGap.Continuum.BF4ExactSlabOrderedPathVariance
import YMGap.Continuum.BF4ExactSlabStarFullActionProbe
import YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal

namespace YMGap.Continuum.BF4ExactSlabOriginalVariancePins

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabReplicaPathVariance
open YMGap.Continuum.BF4ExactSlabOrderedPathVariance
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- The original full partition, without a comparison or normalization. -/
def originalPartition (w : Q') (K extent : Nat) : Q' :=
  quaternionHaar (blocks extent) (fullWeight w K extent)

theorem originalPartition_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) :
    (0 : Q') < originalPartition w K extent :=
  Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 (slabPhysicalFaceEdges extent))
    (partition_floor hw0 hw1 extent (slabPhysicalFaceEdges extent) (fun _ h => h) K hK)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "U" => (Subtype.mk polyOne (supported_one (blocks extent)))

/-- The path's second moment is the existing unnormalized full-action norm. -/
theorem original_norm_pin (p : (F).V) :
    (F).B p p ≈ quaternionHaar (blocks extent)
      (polyMul (fullWeight w K extent) (polyMul p.val p.val)) :=
  haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)

/-- Centering is in the original interacting law, not free product Haar. -/
theorem original_mean_pin (p : (F).V) :
    (F).B p U ≈ quaternionHaar (blocks extent)
      (polyMul (fullWeight w K extent) p.val) :=
  haar_of_coeff (((RatPolyCoeffEqv.mul_one p.val).mul_right (fullWeight w K extent)).trans
    (RatPolyCoeffEqv.mul_comm _ _))

/-- Original mean zero removes precisely the squared mean term. -/
theorem centered_determinant_pin (p : (F).V) (hcenter : (F).B p U ≈ 0) :
    varianceDeterminant w K extent p.val ≈ originalPartition w K extent * (F).B p p := by
  have hm : quaternionHaar (blocks extent) (polyMul (fullWeight w K extent) p.val) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (original_mean_pin hw0 hw1 K extent hK p)) hcenter
  have hs : Q'.eqv
      (quaternionHaar (blocks extent) (polyMul (fullWeight w K extent) p.val) *
        quaternionHaar (blocks extent) (polyMul (fullWeight w K extent) p.val)) 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hm) (Q'.mul_zero_eqv _)
  have hn : Q'.eqv
      (-(quaternionHaar (blocks extent) (polyMul (fullWeight w K extent) p.val) *
        quaternionHaar (blocks extent) (polyMul (fullWeight w K extent) p.val))) 0 :=
    Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hs) (by decide : Q'.eqv (-(0 : Q')) 0)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (original_norm_pin hw0 hw1 K extent hK p))) hn)
    (Q'.eqv_of_eq (Q'.add_zero' _))

#print axioms originalPartition_positive
#print axioms original_norm_pin
#print axioms original_mean_pin
#print axioms centered_determinant_pin

end YMGap.Continuum.BF4ExactSlabOriginalVariancePins
