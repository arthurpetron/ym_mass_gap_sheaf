/-
# Enlarging the source base preserves the SAME limiting Wilson form

Zero spatial translation retains the original ordered loop words. At a
common spatial margin the source action is the masked part of the target
action, with its own partition. The signed boundary estimate compares this
masked law to the full target law on a support box computed from the SOURCE
expression, not the larger base. Its explicit late-margin modulus identifies
the two original three-regulator limits.

This is coherence of the actual fixed-spacing small-nome SU(2) Wilson form,
not equality of finite-volume laws, a continuum construction, or a claim
that an arbitrary Cauchy stream has one common support base.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
import YMGap.Continuum.BF4ExactSlabFixedSpatialBaseBoundaryComparison
import YMGap.Continuum.BF4ExactSlabFixedSpatialBaseCoherence
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseCoherence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBoxLocality
open YMGap.Continuum.BF4ExactSlabSpatialWilsonControl (windowCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (distSq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz (form)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (paddedWidth_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
  (chartExtent chartIds chartIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseAlignedBoxes (placement)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseCoherence (inside_finiteValue_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary (carrierSize)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (LinkLocal)
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry (shiftLink)
open YMGap.Continuum.Z4FiniteBoxExhaustion (boxLinks)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- The larger guard has not enlarged the original expression's support. -/
theorem centered_include {base larger : Nat} (h : base ≤ larger) (r : Nat)
    (e : WindowExpression base) :
    centeredExpression r (includeExpression h e) =
      recenterExpression (space := r+1)
        (by unfold paddedWidth; omega : base+(r+1) ≤ paddedWidth larger r) e := by
  simpa only [centeredExpression, includeExpression, Nat.zero_add] using
    recenterExpression_comp (first := 0) (second := r+1)
      (by omega : base+0 ≤ larger)
      (by unfold paddedWidth; omega : larger+(r+1) ≤ paddedWidth larger r) e

theorem centered_inclusion_pin {base larger : Nat} (h : base ≤ larger) (r : Nat)
    (e : WindowExpression base) :
    recenterExpression (space := 0)
      (by have := paddedWidth_mono h r; omega : paddedWidth base r+0 ≤ paddedWidth larger r)
      (centeredExpression r e) = centeredExpression r (includeExpression h e) := by
  rw [centered_include h r e]
  simpa only [centeredExpression, Nat.add_zero] using
    recenterExpression_comp (first := r+1) (second := 0)
      (by unfold paddedWidth; omega : base+(r+1) ≤ paddedWidth base r)
      (by have := paddedWidth_mono h r; omega : paddedWidth base r+0 ≤ paddedWidth larger r) e

/-- Literal ordered Wilson insertion under the SAME original Haar embedding. -/
theorem aligned_chartInsertion_pin {base larger : Nat} (h : base ≤ larger)
    (r H t : Nat) (e : WindowExpression base) (he : Within (2*H) e) :
    QuaternionPrefixPolynomialEqv (B (chartExtent larger r H t))
      ((placement h r H t).embedding.polynomial (chartInsertion r H t e))
      (chartInsertion r H t (includeExpression h e)) := by
  have hw : paddedWidth base r ≤ (placement h r H t).source := by
    change paddedWidth base r ≤ chartExtent base r H t
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have ht : paddedWidth base r+1+t+2*H ≤ (placement h r H t).source := by
    change paddedWidth base r+1+t+2*H ≤ chartExtent base r H t
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have hroom : paddedWidth base r+(placement h r H t).space ≤ paddedWidth larger r := by
    change paddedWidth base r+0 ≤ paddedWidth larger r
    have := paddedWidth_mono h r
    omega
  have hp := placed_pin (placement h r H t) hroom hw ht (centeredExpression r e)
    ((centered_within r (2*H) e).mpr he)
  have htime : paddedWidth base r+1+t+(larger-base) = paddedWidth larger r+1+t := by
    unfold paddedWidth
    omega
  change QuaternionPrefixPolynomialEqv (B (chartExtent larger r H t))
    ((placement h r H t).embedding.polynomial (chartInsertion r H t e))
    (placedPolynomial (chartExtent larger r H t) (paddedWidth base r+1+t+(larger-base))
      (recenterExpression (space := 0)
        (by have := paddedWidth_mono h r; omega : paddedWidth base r+0 ≤ paddedWidth larger r)
        (centeredExpression r e))) at hp
  rw [htime, centered_inclusion_pin h r e] at hp
  exact hp

/-- Source-sized locality, even when the ambient guard is arbitrarily larger. -/
theorem included_chartInsertion_local {base larger : Nat} (h : base ≤ larger)
    (r H t : Nat) (e : WindowExpression base) (he : Within (2*H) e) :
    LinkLocal (chartExtent larger r H t)
      ((boxLinks (boxSize base (2*H))).map (shiftLink (r+1) (paddedWidth larger r+1+t)))
      (chartInsertion r H t (includeExpression h e)) := by
  unfold chartInsertion
  rw [centered_include h r e]
  exact placed_recenter_local _ (2*H) e he

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

include hsmall in
/-- Actual full and masked action comparison; both original partitions remain. -/
theorem chartScalar_inclusion_bound {base larger : Nat} (h : base ≤ larger)
    (r H t stage : Nat) (hb : 0<base) (e : WindowExpression base) (he : Within (2*H) e) :
    Q'.abs (chartScalar hw0 hw1 H (includeExpression h e) r stage t +
      -(chartScalar hw0 hw1 H e r stage t)) ≤
      spatialAmplitude w hd hs H e *
        (entropyRate 625 (adjustedCoreRate w hd))^(r+1-carrierSize (boxSize base (2*H))) := by
  have he' := (includeExpression_within h (2*H) e).mpr he
  have Pi := chart_interval r H t (includeExpression h e) he'
  have P : Interval (B (chartExtent larger r H t))
      (chartInsertion r H t (includeExpression h e)) (windowCap e) := by
    simpa only [includeExpression_cap] using Pi
  have hpin := inside_finiteValue_pin hw0 hw1 h r H t
    (chartInsertion r H t e) (chart_interval r H t e he).support
    (chartInsertion r H t (includeExpression h e)) P.support
    (aligned_chartInsertion_pin h r H t e he) stage
  have hbnd := BF4ExactSlabFixedSpatialBaseBoundaryComparison.finiteValue_bound
    hw0 hw1 hsmall hd hs h r H t (paddedWidth larger r+1+t) (boxSize base (2*H))
    hb (boxSize_pos base (2*H)) _ (windowCap e) P
    (included_chartInsertion_local h r H t e he) stage
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.abs_eqv_congr (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ hpin)))) hbnd

/-- A computed threshold independent of the larger base and inner regulators. -/
def inclusionModulus {base : Nat} (H : Nat) (e : WindowExpression base) (epsilon : Q') : Nat :=
  carrierSize (boxSize base (2*H)) + geometricCutoff
    (entropyRate 625 (adjustedCoreRate w hd)) (spatialAmplitude w hd hs H e) epsilon

attribute [local irreducible] chartScalar spatialLimit

include hsmall in
theorem chartScalar_inclusion_close {base larger : Nat} (h : base ≤ larger)
    (H : Nat) (hb : 0<base) (e : WindowExpression base) (he : Within (2*H) e)
    (epsilon : Q') (heps : (0 : Q') < epsilon) (r stage t : Nat)
    (hr : inclusionModulus hd hs H e epsilon ≤ r) :
    chartScalar hw0 hw1 H e r stage t ≤ chartScalar hw0 hw1 H (includeExpression h e) r stage t+epsilon ∧
      chartScalar hw0 hw1 H (includeExpression h e) r stage t ≤ chartScalar hw0 hw1 H e r stage t+epsilon := by
  have hn : geometricCutoff (entropyRate 625 (adjustedCoreRate w hd))
      (spatialAmplitude w hd hs H e) epsilon ≤ r+1-carrierSize (boxSize base (2*H)) := by
    unfold inclusionModulus at hr
    omega
  have hgeo := geometric_bound (rate_nonnegative hw0 hd) hs
    (spatialAmplitude_nonnegative w hd hs H e he) heps _ hn
  have hsmall' := Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) hgeo
  have habs := Q'.le_trans' _ _ _
    (chartScalar_inclusion_bound hw0 hw1 hsmall hd hs h r H t stage hb e he) hsmall'
  have hp := Q'.two_sided_of_abs_sub_le habs
  exact ⟨hp.2, hp.1⟩

/-- The two actual diagonal Cauchy constructions agree; neither is replaced. -/
theorem spatialLimit_inclusion {base larger : Nat} (h : base ≤ larger)
    (H : Nat) (hb : 0<base) (e : WindowExpression base) (he : Within (2*H) e) :
    Equiv (spatialLimit hw0 hw1 H e he hsmall hd hs hb)
      (spatialLimit hw0 hw1 H (includeExpression h e)
        ((includeExpression_within h (2*H) e).mpr he) hsmall hd hs (Nat.lt_of_lt_of_le hb h)) := by
  apply Equiv_of_ofQ'_limit_close
    (spatial_diagonal_converges hw0 hw1 H e he hsmall hd hs hb)
    (spatial_diagonal_converges hw0 hw1 H (includeExpression h e)
      ((includeExpression_within h (2*H) e).mpr he) hsmall hd hs (Nat.lt_of_lt_of_le hb h))
  intro epsilon heps
  exact ⟨inclusionModulus hd hs H e epsilon, fun n hn =>
    chartScalar_inclusion_close hw0 hw1 hsmall hd hs h H hb e he epsilon heps n n n hn⟩

theorem form_inclusion {base larger : Nat} (h : base ≤ larger) (hb : 0<base)
    (H : Nat) (e f : WindowExpression base) (he : Within H e) (hf : Within H f) :
    Equiv (form hw0 hw1 hsmall hd hs hb H e f he hf)
      (form hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le hb h) H
        (includeExpression h e) (includeExpression h f)
        ((includeExpression_within h H e).mpr he) ((includeExpression_within h H f).mpr hf)) := by
  have hp := spatialLimit_inclusion hw0 hw1 hsmall hd hs h H hb (.mul (mirror H e) f)
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) f hf⟩
  simpa only [form, includeExpression, recenterExpression, recenter_mapOffsets, mirror] using hp

/-- The consumer for the all-finite-support carrier: the SAME mixed form. -/
theorem intrinsicForm_inclusion {base larger : Nat} (h : base ≤ larger) (hb : 0<base)
    (x y : IntrinsicExpression base) :
    Equiv (intrinsicForm hw0 hw1 hsmall hd hs hb x y)
      (intrinsicForm hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le hb h) (inclusion h x) (inclusion h y)) := by
  simpa only [intrinsicForm, inclusion_radius, inclusion_chart] using
    form_inclusion hw0 hw1 hsmall hd hs h hb (max x.radius y.radius)
      (chart (max x.radius y.radius) x) (chart (max x.radius y.radius) y)
      (chart_within _ x (Nat.le_max_left _ _)) (chart_within _ y (Nat.le_max_right _ _))

theorem distSq_inclusion {base larger : Nat} (h : base ≤ larger) (hb : 0<base)
    (x y : IntrinsicExpression base) :
    Equiv (distSq hw0 hw1 hsmall hd hs hb x y)
      (distSq hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le hb h) (inclusion h x) (inclusion h y)) := by
  simpa only [distSq, inclusion_difference] using
    intrinsicForm_inclusion hw0 hw1 hsmall hd hs h hb
      (BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.difference x y)
      (BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.difference x y)

#print axioms centered_include
#print axioms centered_inclusion_pin
#print axioms aligned_chartInsertion_pin
#print axioms included_chartInsertion_local
#print axioms chartScalar_inclusion_bound
#print axioms inclusionModulus
#print axioms chartScalar_inclusion_close
#print axioms spatialLimit_inclusion
#print axioms form_inclusion
#print axioms intrinsicForm_inclusion
#print axioms distSq_inclusion

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseCoherence
