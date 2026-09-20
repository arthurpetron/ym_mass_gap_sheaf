/-
# Spacing-uniform tracking by the rescaled coercivity strength

For the same completed family, write `S` for its normalized strength and
`a` for its positive transfer spacing. The physical margin proxy is
`g = (S / (1 + S)) / a`. Define `r = S / a` using those actual data.

The existing strength band gives `S <= U * a`. Positive cancellation, before
estimating, yields `r = g + g * S` and hence

    g <= r <= g + U^2 * a.

This is a uniform error estimate, not a new equality hypothesis. It remains
valid when `a` tends to zero. In particular no standalone variation or
boundedness of `1/a` is needed. Combined with the existing direct-log
remainder, summable variation of `r` and an inverse-square spacing tail
construct the exact same-separator logarithmic-rate Cauchy modulus.

The completed family, strength law/band, observable pin, and variation of
`r` remain supplied inputs. This does not construct any of them, identify a
legacy carrier with the original Wilson OS carrier, or prove continuum/QFT,
all-group, or Clay closure. The rescaled strength is not the bare AF coupling.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler
import YMGap.Continuum.SummableRationalStepVariationAlgebra

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRescaledStrengthTracking

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler
open YMGap.Continuum.DirectLogQuadraticRemainder
open YMGap.Continuum.EventualCRealRationalProxyTracking
open YMGap.Continuum.FullLogRateInnerRegularity
open YMGap.Continuum.InverseSquareAntitoneTailControl
open YMGap.Continuum.QuadraticRateErrorTailControl
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra

local infix:50 " ≈ " => Q'.eqv

variable {half : Nat} {family : DynamicVacuumSectorCompletedFamily half}

/-- The actual strength divided by the same family's physical spacing. -/
def rescaledStrength (law : DynamicVacuumSectorNormalizedStrengthLaw family)
    (j : Nat) : Q' :=
  Q'.divPos (law.strength j) (family.transferSpacing.spacing j)
    (family.transferSpacing.spacing_pos j)

private theorem mul_swap_last (x y z : Q') : (x * y) * z ≈ (x * z) * y := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv x y z) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left x _ _ (Q'.mul_comm_eqv y z)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv x z y)

/-- Exact cancellation leaves only the vanishing normalization correction. -/
theorem rescaledStrength_eqv_gap_add
    (law : DynamicVacuumSectorNormalizedStrengthLaw family) (j : Nat) :
    rescaledStrength law j ≈
      family.physicalGap j + family.physicalGap j * law.strength j := by
  have hmargin : family.latticeMargin j * (1 + law.strength j) ≈
      law.strength j :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (law.margin_eqv j))
      (Q'.divPos_mul_eqv _ _ _)
  have hcancel : family.physicalGap j * (1 + law.strength j) ≈
      rescaledStrength law j := by
    unfold DynamicVacuumSectorCompletedFamily.physicalGap rescaledStrength Q'.divPos
    exact Q'.eqv_trans _ _ _ (mul_swap_last _ _ _)
      (Q'.mul_eqv_congr_right _ _ _ hmargin)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hcancel) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _) ?_
  exact Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv _)

theorem physicalGap_le_rescaledStrength
    (law : DynamicVacuumSectorNormalizedStrengthLaw family) (j : Nat) :
    family.physicalGap j <= rescaledStrength law j := by
  have hgap : (0 : Q') < family.physicalGap j :=
    Q'.divPos_pos _ _ _ (family.latticeMargin_pos j)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _
      (Q'.mul_nonneg _ _ (Q'.le_of_lt hgap)
        (Q'.le_of_lt (law.strength_pos j))))
    (Q'.ge_of_eqv (rescaledStrength_eqv_gap_add law j))

/-- The explicit normalization error, with no reciprocal-spacing factor. -/
def normalizationError {law : DynamicVacuumSectorNormalizedStrengthLaw family}
    (band : DynamicVacuumSectorStrengthBand law) (j : Nat) : Q' :=
  (band.upper * band.upper) * family.transferSpacing.spacing j

theorem normalizationError_nonnegative
    {law : DynamicVacuumSectorNormalizedStrengthLaw family}
    (band : DynamicVacuumSectorStrengthBand law) (j : Nat) :
    (0 : Q') <= normalizationError band j :=
  Q'.le_of_lt (Q'.mul_pos (Q'.mul_pos band.upper_pos band.upper_pos)
    (family.transferSpacing.spacing_pos j))

/-- A spacing-uniform estimate for the normalization correction. -/
theorem rescaledStrength_le_gap_add_normalizationError
    {law : DynamicVacuumSectorNormalizedStrengthLaw family}
    (band : DynamicVacuumSectorStrengthBand law) (j : Nat) :
    rescaledStrength law j <= family.physicalGap j + normalizationError band j := by
  have hproduct : family.physicalGap j * law.strength j <=
      band.upper * (band.upper * family.transferSpacing.spacing j) := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (band.toPhysicalRateBand.physicalGap_le_ceiling j)
        (Q'.le_of_lt (law.strength_pos j)))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (band.upperScale j)
        (Q'.le_of_lt band.upper_pos))
  have herror : family.physicalGap j * law.strength j <=
      normalizationError band j :=
    Q'.le_trans' _ _ _ hproduct
      (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (rescaledStrength_eqv_gap_add law j))
    (Q'.add_le_add_left _ _ _ herror)

/-- A computable scale for the normalization error to be at most epsilon. -/
def normalizationErrorModulus
    {law : DynamicVacuumSectorNormalizedStrengthLaw family}
    (band : DynamicVacuumSectorStrengthBand law) (epsilon : Q') : Nat :=
  family.transferSpacingToZero.modulus
    (Q'.divPos epsilon (band.upper * band.upper)
      (Q'.mul_pos band.upper_pos band.upper_pos))

theorem normalizationError_le_epsilon
    {law : DynamicVacuumSectorNormalizedStrengthLaw family}
    (band : DynamicVacuumSectorStrengthBand law)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (j : Nat) (hj : normalizationErrorModulus band epsilon <= j) :
    normalizationError band j <= epsilon := by
  let square := band.upper * band.upper
  have hsquare : (0 : Q') < square := Q'.mul_pos band.upper_pos band.upper_pos
  have hspacing := family.transferSpacingToZero.spacing_le
    (Q'.divPos epsilon square hsquare)
    (Q'.divPos_pos _ _ _ hepsilon) j hj
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ square hspacing
    (Q'.le_of_lt hsquare)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_comm_eqv square (family.transferSpacing.spacing j)))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.divPos_mul_eqv epsilon square hsquare)))

/-- Summability of the normalization error follows from the supplied spacing
tail; no variation of the spacing or its reciprocal is requested. -/
def normalizationErrorTailControl
    {law : DynamicVacuumSectorNormalizedStrengthLaw family}
    (band : DynamicVacuumSectorStrengthBand law) (start : Nat)
    (spacingTail : InverseSquareSpacingTail family.transferSpacing start) :
    AntitoneTailControl (fun j => normalizationError band (start + j)) := by
  let square := band.upper * band.upper
  have hsquare : (0 : Q') <= square :=
    Q'.le_of_lt (Q'.mul_pos band.upper_pos band.upper_pos)
  apply inverseSquareTermTailControl _ 2 (by decide)
    (square * spacingTail.coefficient)
    (Q'.mul_nonneg _ _ hsquare spacingTail.coefficient_nonnegative)
  intro j
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ square (spacingTail.spacing_le j) hsquare)
    (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))

/-- The existing exact-log error plus the proved normalization correction. -/
def rescaledStrengthLogError
    {law : DynamicVacuumSectorNormalizedStrengthLaw family}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorStrengthBand law) (j : Nat) : Q' :=
  quadraticRateError pin.toPhysicalSeparator family.transferSpacing j +
    normalizationError band j

/-- The combined logarithmic and normalization error is at most `4*U^2*a`.
The four rational square terms are kept explicit in the statement. -/
theorem rescaledStrengthLogError_le_spacing
    {law : DynamicVacuumSectorNormalizedStrengthLaw family}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorStrengthBand law) (j : Nat) :
    rescaledStrengthLogError pin band j <=
      ((band.upper * band.upper +
        (band.upper * band.upper + band.upper * band.upper)) +
          band.upper * band.upper) * family.transferSpacing.spacing j := by
  let linear := DynamicVacuumSectorObservablePin.exactLogLinearMarginTail
    pin band.toPhysicalRateBand
  have hquad :=
    YMGap.Continuum.QuadraticRateErrorTailControl.LinearMarginTail.quadraticRateError_le_spacing
      linear j (Nat.zero_le _)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ (normalizationError band j) hquad)
    (Q'.ge_of_eqv (Q'.add_mul_eqv _ _ _))

/-- The exact same-separator logarithmic rate tracks the actual rescaled
strength. The error is `3*margin^2/a + U^2*a`, at most `4*U^2*a`. -/
def rescaledStrengthLogApproximation
    {law : DynamicVacuumSectorNormalizedStrengthLaw family}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorStrengthBand law) :
    EventualCRealRationalProxyApproximation
      ((fullRangeRateFamily pin).rate) (rescaledStrength law)
      (rescaledStrengthLogError pin band)
      (DynamicVacuumSectorObservablePin.exactLogRateStart pin band.toPhysicalRateBand) := by
  let linear := DynamicVacuumSectorObservablePin.exactLogLinearMarginTail
    pin band.toPhysicalRateBand
  let start := DynamicVacuumSectorObservablePin.exactLogRateStart pin band.toPhysicalRateBand
  let approximation := (eventualFullMassRateMarginProxyApproximation
    pin.toPhysicalSeparator family.transferSpacing start
    (linear.toEventualHalfWindow family.transferSpacingToZero)).proxyEqv
      (fun j _ => DynamicVacuumSectorObservablePin.marginRate_eqv_physicalGap pin j)
  refine { proxyRate := approximation.proxyRate, approximates := ?_ }
  intro j hj epsilon hepsilon k hk
  obtain ⟨hup, hdown⟩ := approximation.approximates j hj epsilon hepsilon k hk
  have herror := normalizationError_nonnegative band j
  constructor
  · exact Q'.le_trans' _ _ _ hup
      (Q'.add_le_add_right _ _ epsilon
        (Q'.add_le_add (physicalGap_le_rescaledStrength law j)
          (Q'.add_le_self_of_nonneg _ _ herror)))
  · have hbound := Q'.le_trans' _ _ _
      (rescaledStrength_le_gap_add_normalizationError band j)
      (Q'.add_le_add_right _ _ (normalizationError band j) hdown)
    have hregroup :
        ((((fullRangeRateFamily pin).rate j).approx k +
          quadraticRateError pin.toPhysicalSeparator family.transferSpacing j) + epsilon) +
            normalizationError band j ≈
        (((fullRangeRateFamily pin).rate j).approx k +
          rescaledStrengthLogError pin band j) + epsilon := by
      unfold rescaledStrengthLogError
      show _ * (_ : Int) = _ * (_ : Int)
      simp only [Q'.add_num_cast, Q'.add_den_cast, Int.add_mul]
      ac_rfl
    exact Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hregroup)

/-- Rescaled-strength variation replaces the impossible reciprocal-spacing
variation input. The family, pin, band, and physical time remain unchanged. -/
def exactLogRateCauchyOfRescaledStrength
    {law : DynamicVacuumSectorNormalizedStrengthLaw family}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorStrengthBand law)
    (variation : SummableRationalStepVariation (rescaledStrength law))
    (spacingTail : InverseSquareSpacingTail family.transferSpacing 0) :
    CReal.ModCauchyEv ((fullRangeRateFamily pin).rate) := by
  let linear := DynamicVacuumSectorObservablePin.exactLogLinearMarginTail
    pin band.toPhysicalRateBand
  let start := DynamicVacuumSectorObservablePin.exactLogRateStart pin band.toPhysicalRateBand
  have hspacing : InverseSquareSpacingTail family.transferSpacing start := by
    simpa only [Nat.zero_add] using spacingTail.shifted start
  let logErrorControl :=
    YMGap.Continuum.QuadraticRateErrorTailControl.LinearMarginTail.quadraticRateErrorTailControl
      linear start
    (by
      unfold start DynamicVacuumSectorObservablePin.exactLogRateStart
      exact Nat.le_max_left _ _)
    hspacing
  let normalizationControl := normalizationErrorTailControl band start hspacing
  exact (rescaledStrengthLogApproximation pin band).toModCauchyEv
    (fun j => fullMassRateInnerRegularity pin.toPhysicalSeparator family.transferSpacing j)
    { step := fun j _ => variation.stepBound j }
    variation.variation_nonnegative
    (fun j => Q'.zero_le_add _ _
      (quadraticRateError_nonneg pin.toPhysicalSeparator family.transferSpacing j)
      (normalizationError_nonnegative band j))
    (shiftedTailControl variation.tailControl start)
    (addAntitoneTailControl logErrorControl normalizationControl)

#print axioms rescaledStrength
#print axioms rescaledStrength_eqv_gap_add
#print axioms physicalGap_le_rescaledStrength
#print axioms normalizationError_nonnegative
#print axioms rescaledStrength_le_gap_add_normalizationError
#print axioms normalizationErrorModulus
#print axioms normalizationError_le_epsilon
#print axioms normalizationErrorTailControl
#print axioms rescaledStrengthLogError_le_spacing
#print axioms rescaledStrengthLogApproximation
#print axioms exactLogRateCauchyOfRescaledStrength

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRescaledStrengthTracking
