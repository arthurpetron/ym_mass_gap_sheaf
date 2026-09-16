/-
# Actual central density bounds with a common boundary-mass factor

At positive boundary depth the original density is V*(T^(t+1)1)^2.
Its certified lower and upper constants contain the SAME positive square
of H[V*T^t1]. Nome and spatial width remain explicit; the remaining
constants are independent of t and the late heat cutoff. Shared variables
and the central spatial potential are retained throughout.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff headFloor headFloor_positive)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap prefixCap_nonnegative)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

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

private def upperMul {blocks : Nat} {p q : RatPoly} {a b : Q'}
    (ha : (0 : Q') ≤ a) (Q : Certificate blocks q)
    (Phi : Certificate blocks (polyAdd (cap a) (polyNeg p)))
    (Qhi : Certificate blocks (polyAdd (cap b) (polyNeg q))) :
    Certificate blocks (polyAdd (cap (a*b)) (polyNeg (polyMul p q))) :=
  .ofCoeff (((cap_mul a b).symm.add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 2) (.var 3)) (.neg (.mul (.var 0) (.var 1))))
      (.add (.mul (.add (.var 2) (.neg (.var 0))) (.var 1))
        (.mul (.var 2) (.add (.var 3) (.neg (.var 1)))))
      (by decide) (fun | 0 => p | 1 => q | 2 => cap a | _ => cap b)))
    ((Phi.mul Q).add ((Certificate.constant blocks a ha).mul Qhi))

def spatialFloor (w : Q') (width : Nat) : Q' :=
  headFloor w ^ (spatialFaces width).length

def spatialCeiling (w : Q') (width : Nat) : Q' :=
  prefixCap w ^ (spatialFaces width).length

def densityFloor (w : Q') (width : Nat) : Q' :=
  spatialFloor w width * (kineticFloor w width * kineticFloor w width)

def densityCeiling (w : Q') (width : Nat) : Q' :=
  spatialCeiling w width * (kineticCap w width * kineticCap w width)

def boundaryMass (w : Q') (K width t : Nat) : Q' :=
  weightedMass w K width (terminalMessage w K width t)

/-- One central potential, and both original terminal messages. -/
def centralDensity (w : Q') (K width t : Nat) : RatPoly :=
  polyMul (spatialWeight w K width)
    (polyMul (terminalMessage w K width (t+1)) (terminalMessage w K width (t+1)))

private theorem terminal_succ (w : Q') (K width t : Nat) :
    terminalMessage w K width (t+1) = transferStep w K width (terminalMessage w K width t) := by
  change iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) (t+1) polyOne = _
  rw [iterateStep_add]
  rfl

private theorem collect (v a m : Q') : v*((a*m)*(a*m)) ≈ (v*(a*a))*(m*m) :=
  poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))
    (by decide) (fun | 0 => v | 1 => a | _ => m)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

include hw0 hw1

theorem densityFloor_positive (width : Nat) : (0 : Q') < densityFloor w width :=
  Q'.mul_pos (HKPos.pow_pos (headFloor_positive hw0 hw1) _)
    (Q'.mul_pos (kineticFloor_positive hw0 hw1 width) (kineticFloor_positive hw0 hw1 width))

theorem boundaryMass_positive (K width : Nat) (hK : headCutoff w ≤ K) (t : Nat) :
    (0 : Q') < boundaryMass w K width t :=
  terminalMessage_mass_positive hw0 hw1 K width hK t

def centralDensity_certificate (K width : Nat) (hK : headCutoff w ≤ K) (t : Nat) :
    Certificate (N width) (centralDensity w K width t) :=
  (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
    ((terminalMessage_certificate hw0 hw1 K width hK (t+1)).mul
      (terminalMessage_certificate hw0 hw1 K width hK (t+1)))

/-- The displayed boundary mass is not bounded away by a depth-dependent constant. -/
def centralDensity_lower (K width : Nat) (hK : headCutoff w ≤ K) (t : Nat) :
    Certificate (N width) (polyAdd (centralDensity w K width t)
      (polyNeg (cap (densityFloor w width * (boundaryMass w K width t * boundaryMass w K width t))))) := by
  let U := terminalMessage_certificate hw0 hw1 K width hK (t+1)
  have L : Certificate (N width) (polyAdd (terminalMessage w K width (t+1))
      (polyNeg (cap (kineticFloor w width * boundaryMass w K width t)))) := by
    rw [terminal_succ]
    exact transferStepLowerCertificate hw0 hw1 K width hK
      (terminalMessage_supported w K width t) (terminalMessage_certificate hw0 hw1 K width hK t)
  let U2 := lowerMul (Q'.le_of_lt (Q'.mul_pos (kineticFloor_positive hw0 hw1 width)
    (boundaryMass_positive hw0 hw1 K width hK t))) U L L
  let C := lowerMul (Q'.le_of_lt (HKPos.pow_pos (headFloor_positive hw0 hw1) (spatialFaces width).length))
    (U.mul U) (spatialFloorCertificate hw0 hw1 K width hK) U2
  exact .ofCoeff ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg
    (RatPolyCoeffEqv.smul_coefficient (Q'.eqv_symm
      (collect (spatialFloor w width) (kineticFloor w width) (boundaryMass w K width t))) polyOne))) C

def centralDensity_upper (K width : Nat) (hK : headCutoff w ≤ K) (t : Nat) :
    Certificate (N width) (polyAdd
      (cap (densityCeiling w width * (boundaryMass w K width t * boundaryMass w K width t)))
      (polyNeg (centralDensity w K width t))) := by
  let U := terminalMessage_certificate hw0 hw1 K width hK (t+1)
  have H : Certificate (N width) (polyAdd (cap (kineticCap w width * boundaryMass w K width t))
      (polyNeg (terminalMessage w K width (t+1)))) := by
    rw [terminal_succ]
    exact transferStepUpperCertificate hw0 hw1 K width hK
      (terminalMessage_supported w K width t) (terminalMessage_certificate hw0 hw1 K width hK t)
  let U2 := upperMul (Q'.le_of_lt (Q'.mul_pos (kineticCap_positive hw0 hw1 width)
    (boundaryMass_positive hw0 hw1 K width hK t))) U H H
  let C := upperMul (Q'.pow_nonneg _ (prefixCap_nonnegative hw0) (spatialFaces width).length)
    (U.mul U) (spatialInterval hw0 hw1 K width (N width) (Nat.le_refl _)).upper U2
  exact .ofCoeff ((RatPolyCoeffEqv.smul_coefficient (Q'.eqv_symm
    (collect (spatialCeiling w width) (kineticCap w width) (boundaryMass w K width t))) polyOne).add
      (RatPolyCoeffEqv.refl _)) C

end YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity.spatialFloor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity.spatialCeiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity.densityFloor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity.densityCeiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity.boundaryMass
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity.centralDensity
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity.densityFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity.boundaryMass_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity.centralDensity_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity.centralDensity_lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity.centralDensity_upper
