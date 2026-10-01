/-
# Complete original signed remainder: cancel the source-curvature flux

Collect the EXISTING angular-weight defect into one full-range Gamma pairing.
The projected endpoint is exactly P_fringe(V*g_n), at depth n throughout.
Its quadratic curvature flux cancels against the Taylor expansion of that
defect BEFORE normalization or absolute estimates. The negative commutator
square, signed angular pair remainder and actual cubic/cutoff debts survive.

The concrete whole-family consumers keep the SAME odd mean, variance and
partition. No near-one rate, changing-source budget, spatial/spacing limit,
continuum survival or physical mass gap is asserted.
-/

import YMGap.Continuum.SU2QuaternionCompleteRemainderCancellation
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyRelativeWard
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceTaylor

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialRemainderCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
  (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar
  (weighted_gamma_finSum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal (angularWeightDefect)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance wardResidual)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceTaylor
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyRelativeWard
  (familyLengthAngularVarianceFactor padded_family_energy_relative_ward)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (normalizedEnergy oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound
  (endpointRelativeCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialRelativeWardBound
  (headCutoff_le_endpointRelativeCutoff)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.SU2QuaternionCompleteRemainderCancellation

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private theorem source_supported (w : Q') (K width n : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width n)) := by
  unfold projectedEndpointSource
  exact familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width n))

/-- The finite-sum defect is one full Gamma pairing. No support, positivity,
independence or cutoff assumption is needed for this collection step. -/
theorem angularWeightDefect_generic (w : Q') (K width n : Nat) (f : RatPoly) :
    angularWeightDefect w K width n f ≈
      angularWeightChange (N width-1) w K
        (projectedEndpointSource w K width (terminalMessage w K width n)) f := by
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  unfold angularWeightDefect angularWeightChange angularSquare
  rw [hN]
  exact Q'.eqv_symm (weighted_gamma_finSum (N width) _ f)

/-- Pin the complete ORIGINAL signed numerator to the generic cancellation
object without replacing q*P(q) by q^2. -/
theorem signedRemainder_generic (w : Q') (K width n : Nat) (f : RatPoly) :
    signedRemainder w K width n f ≈
      completeRemainder (N width-1) w K
        (projectedEndpointSource w K width (terminalMessage w K width n)) f := by
  unfold signedRemainder completeRemainder
  exact Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _
      (angularWeightDefect_generic w K width n f)))

/-- The reduced expression retains a NEGATIVE commutator square and the
entire signed angular pair remainder, cubic term and omitted-mode debt. -/
def cancellationValue (w : Q') (K width n : Nat) (f : RatPoly) : Q' :=
  cancelledRemainder (N width-1) w K
    (projectedEndpointSource w K width (terminalMessage w K width n)) f

/-- Exact quadratic source-flux cancellation on the ACTUAL projected source.
This requires no positivity, eigenpin, near-one estimate or source stationarity. -/
theorem signedRemainder_cancellation (w : Q') (K width n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f) :
    signedRemainder w K width n f ≈ cancellationValue w K width n f := by
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  exact Q'.eqv_trans _ _ _ (signedRemainder_generic w K width n f)
    (completeRemainder_cancellation (N width-1) w K _ f
      (by simpa only [hN] using source_supported w K width n)
      (by simpa only [hN] using hf))

/-- Normalize only AFTER the source-flux cancellation, with SAME positive Z. -/
def normalizedCancellation {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  cancellationValue w K width n f *
    Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)

theorem normalizedRemainder_cancellation {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f) :
    normalizedRemainder hw0 hw1 K width hK n f ≈
      normalizedCancellation hw0 hw1 K width hK n f :=
  Q'.mul_eqv_congr_right _ _ _ (signedRemainder_cancellation w K width n f hf)

/-- The complete-weight Ward correction, with its own original mean, stays
SIGNED. Neither the raw angular cost nor a source error is called variance. -/
def cancelledVarianceRemainder {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  (cancellationValue w K width n f -
    ((1 : Q')-w)*wardResidual hw0 hw1 K width hK n f) *
    Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)

theorem varianceRemainder_cancellation {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f) :
    varianceRemainder hw0 hw1 K width hK n f ≈
      cancelledVarianceRemainder hw0 hw1 K width hK n f :=
  Q'.eqv_trans _ _ _ (varianceRemainder_raw hw0 hw1 K width hK n f)
    (Q'.mul_eqv_congr_right _ _ _ (Q'.add_eqv_congr'
      (signedRemainder_cancellation w K width n f hf) (Q'.eqv_refl _)))

/-- Whole signed/repeated-family SAME-variance consumer of the exact reduced
correction. This is an identity, not its missing physical-scaling estimate. -/
theorem padded_family_energy_cancellation {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (coeff : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    normalizedEnergy hw0 hw1 K width hK n (spatialSpan width coeff qs) ≈
      12*(((1 : Q')-w)*oddVariance hw0 hw1 K width hK n
        (spatialSpan width coeff qs)) +
      cancelledVarianceRemainder hw0 hw1 K width hK n (spatialSpan width coeff qs) :=
  Q'.eqv_trans _ _ _
    (padded_family_energy_variance hw0 hw1 K hwidth hK n qs coeff hqs)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (varianceRemainder_cancellation hw0 hw1 K width hK n _
        (spatialSpan_supported width coeff qs)))

/-- Computed join of the two existing cutoff onsets. It depends on nome,
not width, terminal depth or the particular signed family. -/
def cancellationCutoff (w : Q') : Nat :=
  max (endpointRelativeCutoff w) (sufficientCutoff w)

/-- Explicit original-source ceiling: the negative square remains; only the
cubic, omitted-mode and angular pair debts receive their existing budgets. -/
def normalizedRetainedCeiling {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  retainedCeiling (N width-1) w K
    (projectedEndpointSource w K width (terminalMessage w K width n)) f *
    Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)

theorem normalizedRemainder_le_retained {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (hquad : sufficientCutoff w ≤ K)
    (n : Nat) (f : RatPoly) (hf : SupportedQuaternionBlocks (N width) f) :
    normalizedRemainder hw0 hw1 K width hK n f ≤
      normalizedRetainedCeiling hw0 hw1 K width hK n f := by
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hraw := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (signedRemainder_generic w K width n f))
    (completeRemainder_le_retained (N width-1) (Q'.le_of_lt hw0) hw1 K hquad _ f
      (by simpa only [hN] using source_supported w K width n)
      (by simpa only [hN] using hf))
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ hraw
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

/-- Concrete join to the new angular/SAME-variance producer. All coefficients
and changing-source budgets remain explicit; no useful scaling calibration
of either this angular coefficient or the retained ceiling is supplied. -/
theorem padded_family_energy_le_cancelled {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : cancellationCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (coeff : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let hrel := Nat.le_trans (Nat.le_max_left _ _) hK
    let hhead := Nat.le_trans (headCutoff_le_endpointRelativeCutoff w) hrel
    normalizedEnergy hw0 hw1 K width hhead n (spatialSpan width coeff qs) ≤
      ((1 : Q')-w)*(familyLengthAngularVarianceFactor w qs *
        oddVariance hw0 hw1 K width hhead n (spatialSpan width coeff qs)) +
      normalizedRetainedCeiling hw0 hw1 K width hhead n (spatialSpan width coeff qs) := by
  dsimp only
  have hrel : endpointRelativeCutoff w ≤ K :=
    Nat.le_trans (Nat.le_max_left _ _) hK
  have hhead := Nat.le_trans (headCutoff_le_endpointRelativeCutoff w) hrel
  have hquad : sufficientCutoff w ≤ K := Nat.le_trans (Nat.le_max_right _ _) hK
  exact Q'.le_trans' _ _ _
    (padded_family_energy_relative_ward hw0 hw1 K hwidth hrel n qs coeff hqs)
    (Q'.add_le_add_left _ _ _
      (normalizedRemainder_le_retained hw0 hw1 K width hhead hquad n _
        (spatialSpan_supported width coeff qs)))

#print axioms angularWeightDefect_generic
#print axioms signedRemainder_generic
#print axioms cancellationValue
#print axioms signedRemainder_cancellation
#print axioms normalizedCancellation
#print axioms normalizedRemainder_cancellation
#print axioms cancelledVarianceRemainder
#print axioms varianceRemainder_cancellation
#print axioms padded_family_energy_cancellation
#print axioms cancellationCutoff
#print axioms normalizedRetainedCeiling
#print axioms normalizedRemainder_le_retained
#print axioms padded_family_energy_le_cancelled

end YMGap.Continuum.BF4ExactSlabFixedSpatialRemainderCancellation
