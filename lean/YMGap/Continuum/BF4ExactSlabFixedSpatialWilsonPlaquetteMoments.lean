/-
# The same original plaquette moments in the Wilson and old spatial limits

The actual recentered Wilson plaquette insertion has the old singleton face
polynomial on every original chart. The first and second finite moments keep
the SAME extent, selected chain, heat stage, time buffer and partition. Their
separate existing diagonal convergence witnesses therefore identify the two
families of limiting moments, without equating their representative moduli.

The Wilson second moment minus its first moment squared consequently inherits
the already proved positive local-star variance floor. This is a scalar pin
at fixed nome/spacing with the original small-nome guards. It is not a map
of completed carriers or a rational expression for the CReal-centered and
normalized vector; it gives no enlarged-carrier strict bound or continuum gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialVariance

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance (recenter_faceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialLimit (recenteredScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialVariance
  (recenter_unit spatialVariance spatialVariance_floor spatialVariance_ne_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
open YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance (finiteValue_coeff_congr)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

/-- The fundamental character on the actual witnessed closed source plaquette. -/
def plaquetteExpression {base : Nat} (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    WindowExpression base := .loop 0 (plaquetteLoop face hf) 1

private theorem chartInsertion_plaquette {base : Nat}
    (face : Z4Plaq) (hf : face ∈ spatialFaces base) (r t : Nat) :
    RatPolyCoeffEqv (chartInsertion r 0 t (plaquetteExpression face hf))
      (faceCharacter (chartExtent base r 0 t)
        (timeShiftPlaquette (paddedWidth base r+1+t) (shiftFace (r+1) 0 face))) :=
  (recentered_fundamental_placedSpan (space := r+1)
    (by unfold paddedWidth; omega : base+(r+1) ≤ paddedWidth base r)
    (chartExtent base r 0 t) (paddedWidth base r+1+t) face hf).trans
      (placedSpan_character (chartExtent base r 0 t) (paddedWidth base r+1+t)
        (shiftFace (r+1) 0 face))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {base : Nat} (face : Z4Plaq) (hf : face ∈ spatialFaces base)

local notation "e" => plaquetteExpression face hf
local notation "x" => faceSpan base face hf

/-- SAME original finite chart, heat cutoff and partition in both first moments. -/
theorem chartScalar_mean_pin (r stage t : Nat) :
    chartScalar hw0 hw1 0 e r stage t ≈
      recenteredScalar hw0 hw1 base 0 x (unit base) r stage t := by
  have hnew := finiteValue_coeff_congr w hw0 hw1
    (chartExtent base r 0 t) (chartIds base r 0 t) (fun _ hi => chartIds_physical hi)
    _ _ (chartInsertion_plaquette face hf r t) stage
  change chartScalar hw0 hw1 0 e r stage t ≈ _ at hnew
  unfold recenteredScalar
  rw [recenter_faceSpan base face hf r, recenter_unit]
  refine Q'.eqv_trans _ _ _ hnew ?_
  simpa only [chartIds, chartExtent, Nat.add_zero, Nat.mul_zero, Nat.zero_add] using
    (Q'.eqv_symm (chartScalar_mean_finiteValue hw0 hw1 (paddedWidth base r)
      (shiftFace (r+1) 0 face) (shiftFace_spatial (by unfold paddedWidth; omega) hf) stage t))

/-- The square insertion has the SAME two physical factors and SAME action/Z. -/
theorem chartScalar_square_pin (r stage t : Nat) :
    chartScalar hw0 hw1 0 (.mul e e) r stage t ≈
      recenteredScalar hw0 hw1 base 0 x x r stage t := by
  have hp := (chartInsertion_plaquette face hf r t).mul (chartInsertion_plaquette face hf r t)
  change RatPolyCoeffEqv (chartInsertion r 0 t (.mul e e)) _ at hp
  have hnew := finiteValue_coeff_congr w hw0 hw1
    (chartExtent base r 0 t) (chartIds base r 0 t) (fun _ hi => chartIds_physical hi)
    _ _ hp stage
  change chartScalar hw0 hw1 0 (.mul e e) r stage t ≈ _ at hnew
  unfold recenteredScalar
  rw [recenter_faceSpan base face hf r]
  refine Q'.eqv_trans _ _ _ hnew ?_
  simpa only [chartIds, chartExtent, Nat.add_zero, Nat.mul_zero, Nat.zero_add] using
    (Q'.eqv_symm (chartScalar_square_finiteValue hw0 hw1 (paddedWidth base r)
      (shiftFace (r+1) 0 face) (shiftFace_spatial (by unfold paddedWidth; omega) hf) stage t))

variable (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0<base)

attribute [local irreducible] chartScalar recenteredScalar spatialLimit
  BF4ExactSlabFixedSpatialSpatialLimit.spatialLimit

local notation "mean" => spatialLimit hw0 hw1 0 e (Nat.le_refl 0) hsmall hd hs hb
local notation "second" => spatialLimit hw0 hw1 0 (WindowExpression.mul e e)
  (And.intro (Nat.le_refl 0) (Nat.le_refl 0)) hsmall hd hs hb

/-- The two original diagonals have their OWN constructive convergence witnesses. -/
theorem meanLimit_pin :
    Equiv mean
      (BF4ExactSlabFixedSpatialSpatialLimit.spatialLimit hw0 hw1 base 0 x (unit base)
        (Nat.le_refl 0) (Nat.le_refl 0) hsmall hd hs hb) :=
  Equiv_of_limit_of_equal
    (fun n => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => chartScalar_mean_pin hw0 hw1 face hf n n n))
    (spatial_diagonal_converges hw0 hw1 0 e (Nat.le_refl 0) hsmall hd hs hb)
    (BF4ExactSlabFixedSpatialSpatialLimit.spatial_diagonal_converges hw0 hw1 base 0
      x (unit base) (Nat.le_refl 0) (Nat.le_refl 0) hsmall hd hs hb)

theorem squareLimit_pin :
    Equiv second
      (BF4ExactSlabFixedSpatialSpatialLimit.spatialLimit hw0 hw1 base 0 x x
        (Nat.le_refl 0) (Nat.le_refl 0) hsmall hd hs hb) :=
  Equiv_of_limit_of_equal
    (fun n => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => chartScalar_square_pin hw0 hw1 face hf n n n))
    (spatial_diagonal_converges hw0 hw1 0 (.mul e e)
      ⟨Nat.le_refl 0, Nat.le_refl 0⟩ hsmall hd hs hb)
    (BF4ExactSlabFixedSpatialSpatialLimit.spatial_diagonal_converges hw0 hw1 base 0
      x x (Nat.le_refl 0) (Nat.le_refl 0) hsmall hd hs hb)

/-- Equality of actual scalar variances, not a claim that a centered CReal is rational. -/
theorem variance_pin :
    Equiv (sub second (mul mean mean))
      (spatialVariance hw0 hw1 base face hf hsmall hd hs hb) := by
  have hm := meanLimit_pin hw0 hw1 face hf hsmall hd hs hb
  exact Pivot2.add_congr (squareLimit_pin hw0 hw1 face hf hsmall hd hs hb)
    (CReal.neg_congr ((Pivot2.mul_congr_left hm).trans (Pivot2.mul_congr_right hm)))

/-- Reuse the original local-star floor on these SAME Wilson scalar moments. -/
theorem variance_floor : leEv (ofQ' (starRatio w)) (sub second (mul mean mean)) :=
  leEv_trans (spatialVariance_floor hw0 hw1 base face hf hsmall hd hs hb)
    (leEv_of_equiv (variance_pin hw0 hw1 face hf hsmall hd hs hb).symm)

theorem variance_ne_zero : ¬ Equiv (sub second (mul mean mean)) (ofQ' 0) :=
  fun hz => spatialVariance_ne_zero hw0 hw1 base face hf hsmall hd hs hb
    ((variance_pin hw0 hw1 face hf hsmall hd hs hb).symm.trans hz)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteMoments

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteMoments.plaquetteExpression
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteMoments.chartScalar_mean_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteMoments.chartScalar_square_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteMoments.meanLimit_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteMoments.squareLimit_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteMoments.variance_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteMoments.variance_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteMoments.variance_ne_zero
