/-
# The finite centered output angular reserve is bounded by the bond norm

This module retains the complete spatial source and the moving odd-marginal
center.  It bounds finite angular energies by an explicit representative of
the existing completed bond norm; it does not construct an angular limit or
assert a positive angular fraction of that norm.
-/

import YMGap.Continuum.BF4WilsonAllNomeCenteredTransferBondLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSmoothing

namespace YMGap.Continuum.BF4WilsonAllNomeCenteredAngularBondBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSmoothing
  (transferStep_angular_smoothing)
open YMGap.Continuum.BF4WilsonAllNomeCenteredTransferBondLimit
  (finiteScalar transferCauchy transferLimit transferLimit_approx
    cutoffThreshold timeThreshold)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
  (WindowExpression Within sourcePolynomial source_supported)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionChannelAngularContraction (angularListSum)

local notation:max "N" width:arg => List.length (baseLinks width)

/-- Angular energy of the ACTUAL full transfer output, divided by the SAME
positive odd partition.  The source polynomial can be signed; radius-zero
support is supplied only when the estimate is used. -/
def normalizedAngularReserve {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (e : WindowExpression width) (k t : Nat) : Q' :=
  let K := headCutoff w+k
  let g := terminalMessage w K width t
  let psi := oddCentered hw0 hw1 K width (Nat.le_add_right _ _) t (sourcePolynomial e)
  (((1 : Q')-w)*angularListSum (N width) (List.range (N width))
    (transferStep w K width (polyMul g psi))) *
    Q'.recipPos (oddMass w K width t)
      (oddMass_positive hw0 hw1 K width (Nat.le_add_right _ _) t)

/-- Original full-output smoothing pays the angular reserve from the finite
centered transfer quadratic, not from a bare or unweighted source square. -/
theorem normalizedAngularReserve_le_finiteScalar {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (e : WindowExpression width) (he : Within 0 e)
    (k t : Nat) :
    normalizedAngularReserve hw0 hw1 e k t ≤
      finiteScalar hw0 hw1 e k t := by
  let K := headCutoff w+k
  let f := sourcePolynomial e
  let g := terminalMessage w K width t
  let psi := oddCentered hw0 hw1 K width (Nat.le_add_right _ _) t f
  let r := Q'.recipPos (oddMass w K width t)
    (oddMass_positive hw0 hw1 K width (Nat.le_add_right _ _) t)
  have hf : SupportedQuaternionBlocks (N width) f := by
    simpa only [Nat.zero_add, Nat.one_mul] using source_supported 0 e he
  have hsource : SupportedQuaternionBlocks (N width) (polyMul g psi) :=
    supported_polyMul (terminalMessage_supported w K width t)
      (oddCentered_supported hw0 hw1 K width (Nat.le_add_right _ _) t hf)
  have hs := transferStep_angular_smoothing (Q'.le_of_lt hw0)
    (Q'.le_of_lt hw1) K width (polyMul g psi) hsource
  have hr := Q'.mul_le_mul_of_nonneg_right _ _ r hs
    (Q'.le_of_lt (Q'.recipPos_pos _
      (oddMass_positive hw0 hw1 K width (Nat.le_add_right _ _) t)))
  change (((1 : Q')-w)*angularListSum (N width) (List.range (N width))
      (transferStep w K width (polyMul g psi)))*r ≤
    weightedMass w K width
      (polyMul (polyMul g psi) (transferStep w K width (polyMul g psi)))*r
  exact hr

/-- Explicit independent cutoff, time and CReal-representative thresholds.
This is a finite limsup bound against the existing bond norm representative;
it makes no assertion that the angular outputs themselves converge. -/
theorem normalizedAngularReserve_completed_approx {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (e : WindowExpression width) (he : Within 0 e)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k t p : Nat)
    (hk : cutoffThreshold hw0 hw1 e he epsilon ≤ k)
    (ht : timeThreshold hw0 hw1 e he epsilon ≤ t)
    (hp : (transferCauchy hw0 hw1 e he).M epsilon ≤ p) :
    normalizedAngularReserve hw0 hw1 e k t ≤
      (transferLimit hw0 hw1 e he).approx p + epsilon :=
  Q'.le_trans' _ _ _
    (normalizedAngularReserve_le_finiteScalar hw0 hw1 e he k t)
    (transferLimit_approx hw0 hw1 e he epsilon hepsilon k t p hk ht hp).1

#print axioms normalizedAngularReserve
#print axioms normalizedAngularReserve_le_finiteScalar
#print axioms normalizedAngularReserve_completed_approx

end YMGap.Continuum.BF4WilsonAllNomeCenteredAngularBondBound
