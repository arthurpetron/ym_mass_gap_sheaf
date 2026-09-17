/-
# Finite positive window for the original odd terminal marginal

The weight is literally nu=(V*T^n1)*T^(n+1)1. Its positive lower
constant uses the complete spatial floor and the two actual terminal-message
floors. Its upper constant is computed from the full polynomial, with positive
slack. Every constant retains nome, cutoff, width and depth as explicit data.

These certificates supply finite-regulator polynomial approximation data.
They do not give a width-, depth-, cutoff- or spacing-uniform gap, replace the
odd marginal by an even central density, or identify a stationary vacuum.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
  (kineticFloor kineticFloor_positive weightedMass transferStepLowerCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (spatialFloorCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate terminalMessage_mass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalWeight_supported)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks spatialWeight weightedMass

/-- The zero-depth message is one; every later floor retains its exact
previous V-weighted mass rather than bounding that mass by a surrogate. -/
def messageFloor (w : Q') (K width : Nat) : Nat → Q'
  | 0 => 1
  | n+1 => kineticFloor w width * weightedMass w K width (terminalMessage w K width n)

theorem messageFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    (0 : Q') < messageFloor w K width n := by
  cases n with
  | zero => exact (by decide : (0 : Q') < 1)
  | succ n =>
      exact Q'.mul_pos (kineticFloor_positive hw0 hw1 width)
        (terminalMessage_mass_positive hw0 hw1 K width hK n)

def messageFloorCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    Certificate (N width) (polyAdd (terminalMessage w K width n)
      (polyNeg (cap (messageFloor w K width n)))) := by
  cases n with
  | zero =>
      change Certificate (N width) (polyAdd polyOne (polyNeg (cap (1 : Q'))))
      exact .ofCoeff
        (((RatPolyCoeffEqv.refl _).add
          (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.one_smul polyOne))).trans
          (coeffEvalExpr_eqv_of_normalize_eq
            (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide) (fun _ => polyOne)))
        (.constant (N width) 0 (Q'.le_refl' _))
  | succ n =>
      change Certificate (N width) (polyAdd (terminalMessage w K width (n+1))
        (polyNeg (cap (kineticFloor w width *
          weightedMass w K width (terminalMessage w K width n)))))
      rw [← terminalMessage_next w K width n]
      exact transferStepLowerCertificate hw0 hw1 K width hK
        (terminalMessage_supported w K width n) (terminalMessage_certificate hw0 hw1 K width hK n)

/-- The actual odd marginal retains one spatial potential and both unequal
terminal depths. This is finite positive rational data, not a uniform rate. -/
def lower (w : Q') (K width n : Nat) : Q' :=
  ((headFloor w)^(spatialFaces width).length * messageFloor w K width n) *
    messageFloor w K width (n+1)

theorem lower_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    (0 : Q') < lower w K width n :=
  Q'.mul_pos
    (Q'.mul_pos (HKPos.pow_pos (headFloor_positive hw0 hw1) _)
      (messageFloor_positive hw0 hw1 K width hK n))
    (messageFloor_positive hw0 hw1 K width hK (n+1))

private def lowerMul {blocks : Nat} {p q : RatPoly} {a b : Q'}
    (ha : (0 : Q') ≤ a) (Q : Certificate blocks q)
    (Plo : Certificate blocks (polyAdd p (polyNeg (cap a))))
    (Qlo : Certificate blocks (polyAdd q (polyNeg (cap b)))) :
    Certificate blocks (polyAdd (polyMul p q) (polyNeg (cap (a*b)))) :=
  .ofCoeff (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul a b).symm)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3))))
      (.add (.mul (.add (.var 0) (.neg (.var 2))) (.var 1))
        (.mul (.var 2) (.add (.var 1) (.neg (.var 3)))))
      (by decide) (fun | 0 => p | 1 => q | 2 => cap a | _ => cap b)))
    ((Plo.mul Q).add ((Certificate.constant blocks a ha).mul Qlo))

/-- A certificate for nu-cap(lower) on the SAME retained Haar carrier. -/
def lowerCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    Certificate (N width) (polyAdd (marginalWeight w K width n)
      (polyNeg (cap (lower w K width n)))) :=
  lowerMul
    (Q'.le_of_lt (Q'.mul_pos (HKPos.pow_pos (headFloor_positive hw0 hw1) _)
      (messageFloor_positive hw0 hw1 K width hK n)))
    (terminalMessage_certificate hw0 hw1 K width hK (n+1))
    (lowerMul (Q'.le_of_lt (HKPos.pow_pos (headFloor_positive hw0 hw1) _))
      (terminalMessage_certificate hw0 hw1 K width hK n)
      (spatialFloorCertificate hw0 hw1 K width hK)
      (messageFloorCertificate hw0 hw1 K width hK n))
    (messageFloorCertificate hw0 hw1 K width hK (n+1))

/-- A computed finite cap of the FULL original polynomial, with positive
slack. Presentation size, nome, cutoff, width and depth may all enter. -/
def upper (w : Q') (K width n : Nat) : Q' :=
  polynomialCap (marginalWeight w K width n) + (lower w K width n + 1)

theorem lower_le_upper (w : Q') (K width n : Nat) :
    lower w K width n ≤ upper w K width n := by
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
    (Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ _ (polynomialCap_nonnegative (marginalWeight w K width n)))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

theorem upper_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    (0 : Q') < upper w K width n :=
  Q'.pos_of_lt_of_le (lower_positive hw0 hw1 K width hK n)
    (lower_le_upper w K width n)

/-- The cap is certified, not merely asserted finite or pointwise bounded. -/
def upperCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    Certificate (N width) (polyAdd (cap (upper w K width n))
      (polyNeg (marginalWeight w K width n))) :=
  ((polynomialInterval (N width) (marginalWeight w K width n)
    (marginalWeight_supported w K width n)).raise (lower w K width n+1)
      (Q'.zero_le_add _ _ (Q'.le_of_lt (lower_positive hw0 hw1 K width hK n))
        Q'.zero_le_one)).upper

end YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow.messageFloor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow.messageFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow.messageFloorCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow.lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow.lower_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow.lowerCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow.upper
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow.lower_le_upper
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow.upper_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow.upperCertificate
