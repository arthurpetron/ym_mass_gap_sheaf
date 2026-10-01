/-
# The actual positive-depth terminal source and odd marginal share a mass scale

For terminal depth `n+1`, the projected source has a certified scalar cap
proportional to the PREVIOUS original V-weighted mass. The ORIGINAL odd
marginal has a certified scalar floor proportional to its square. The constants
use the existing spatial and kinetic heat floors/caps; no source, variance,
or spacing-uniform estimate is assumed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity
import YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
import YMGap.Continuum.SU2QuaternionHaarFamilyCertificate
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSourceBounds

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate spatialInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (kineticCap_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
  (weightedMass_one_floor weightedMass_transfer_floor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate
    terminalMessage_mass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity
  (spatialFloor spatialCeiling boundaryMass boundaryMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow
  (lower lowerCertificate messageFloor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff headFloor_positive)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject)
open YMGap.Continuum.SU2QuaternionHaarFamilyCertificate
  (familyProject_certificate familyProject_interval)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_add)
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight weightedMass terminalMessage

/-- The strictly positive original boundary mass before the tested step. -/
def predecessorMass (w : Q') (K width n : Nat) : Q' :=
  boundaryMass w K width n

theorem predecessorMass_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    (0 : Q') < predecessorMass w K width n :=
  boundaryMass_positive hw0 hw1 K width hK n

/-- The actual projected source at depth `n+1` is capped by this scalar. -/
def projectedCap (w : Q') (K width n : Nat) : Q' :=
  spatialCeiling w width * (kineticCap w width * predecessorMass w K width n)

/-- A floor for the ORIGINAL `V*T_(n+1)*T_(n+2)` odd marginal. Its factorization
displays exactly two spatial floors, three kinetic floors and the same previous
mass twice; no different measure or terminal depth enters. -/
def marginalFloor (w : Q') (K width n : Nat) : Q' :=
  (spatialFloor w width * (kineticFloor w width * predecessorMass w K width n)) *
    (kineticFloor w width *
      ((kineticFloor w width * predecessorMass w K width n) * spatialFloor w width))

theorem marginalFloor_factor (w : Q') (K width n : Nat) :
    marginalFloor w K width n ≈
      ((spatialFloor w width * spatialFloor w width) *
        ((kineticFloor w width * kineticFloor w width) * kineticFloor w width)) *
          (predecessorMass w K width n * predecessorMass w K width n) :=
  poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.mul (.var 1) (.var 2)) (.var 0))))
    (.mul (.mul (.mul (.var 0) (.var 0))
      (.mul (.mul (.var 1) (.var 1)) (.var 1)))
      (.mul (.var 2) (.var 2)))
    (by decide) (fun
      | 0 => spatialFloor w width
      | 1 => kineticFloor w width
      | _ => predecessorMass w K width n)

/-- Positive data of the exact projected source, not a surrogate density. -/
def projectedSource_certificate {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    Certificate (N width)
      (projectedEndpointSource w K width (terminalMessage w K width (n+1))) := by
  unfold projectedEndpointSource
  exact familyProject_certificate (N width) (fringeBlocks width) (fringeBlocks_lt width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width (n+1)))
    ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
      (terminalMessage_certificate hw0 hw1 K width hK (n+1)))

private def nextMessage_interval {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    Interval (N width) (terminalMessage w K width (n+1))
      (kineticCap w width * predecessorMass w K width n) where
  support := terminalMessage_supported w K width (n+1)
  nonnegative := Q'.mul_nonneg _ _ (Q'.le_of_lt (kineticCap_positive hw0 hw1 width))
    (Q'.le_of_lt (predecessorMass_positive hw0 hw1 K width hK n))
  upper := by
    rw [← terminalMessage_next]
    exact transferStepUpperCertificate hw0 hw1 K width hK
      (terminalMessage_supported w K width n)
      (terminalMessage_certificate hw0 hw1 K width hK n)
  lower := (Certificate.constant (N width) _
      (Q'.mul_nonneg _ _ (Q'.le_of_lt (kineticCap_positive hw0 hw1 width))
        (Q'.le_of_lt (predecessorMass_positive hw0 hw1 K width hK n)))).add
    (terminalMessage_certificate hw0 hw1 K width hK (n+1))

/-- Constructed cap of the projected source, preserving the complete spatial
action before the existing fringe integration. -/
def projectedSource_upperCertificate {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    Certificate (N width)
      (polyAdd (cap (projectedCap w K width n))
        (polyNeg (projectedEndpointSource w K width
          (terminalMessage w K width (n+1))))) := by
  let I := (spatialInterval hw0 hw1 K width (N width) (Nat.le_refl _)).mul
    (nextMessage_interval hw0 hw1 K width hK n)
  exact (familyProject_interval (N width) (fringeBlocks width)
    (fringeBlocks_lt width) I).upper

private theorem cap_neg (c : Q') : RatPolyCoeffEqv (polyNeg (cap c)) (cap (-c)) := by
  intro weight
  change (-(c*1)) * weight [] + 0 ≈ ((-c)*1) * weight [] + 0
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv c 1)))
    (Q'.eqv_refl _)

private def lowerWeaken {blocks : Nat} {p : RatPoly} {a b : Q'} (h : b ≤ a)
    (P : Certificate blocks (polyAdd p (polyNeg (cap a)))) :
    Certificate blocks (polyAdd p (polyNeg (cap b))) :=
  .ofCoeff ((coeffEvalExpr_eqv_of_normalize_eq
    (.add (.var 0) (.neg (.var 2)))
    (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
    (by decide) (fun | 0 => p | 1 => cap a | _ => cap b)).trans
      ((RatPolyCoeffEqv.refl _).add
        (((RatPolyCoeffEqv.refl _).add (cap_neg b)).trans (cap_add a (-b)))))
    (P.add (Certificate.constant blocks (a + -b) (Q'.sub_nonneg_of_le h)))

/-- The original next mass pays one additional kinetic and spatial floor. -/
theorem nextMass_floor {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    (kineticFloor w width * predecessorMass w K width n) * spatialFloor w width ≤
      predecessorMass w K width (n+1) := by
  have hstep := weightedMass_transfer_floor hw0 hw1 K width hK
    (terminalMessage_supported w K width n)
    (terminalMessage_certificate hw0 hw1 K width hK n)
  rw [terminalMessage_next] at hstep
  have hsp := weightedMass_one_floor hw0 hw1 K width hK
  have hleft := Q'.mul_le_mul_of_nonneg_left _ _ _ hsp
    (Q'.le_of_lt (Q'.mul_pos (kineticFloor_positive hw0 hw1 width)
      (predecessorMass_positive hw0 hw1 K width hK n)))
  exact Q'.le_trans' _ _ _ hleft hstep

private theorem marginalFloor_le_windowLower {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    marginalFloor w K width n ≤ lower w K width (n+1) := by
  let v := spatialFloor w width
  let k := kineticFloor w width
  let m := predecessorMass w K width n
  let mnext := predecessorMass w K width (n+1)
  have hnext : (k*m)*v ≤ mnext := nextMass_floor hw0 hw1 K width hK n
  have hk : (0 : Q') ≤ k := Q'.le_of_lt (kineticFloor_positive hw0 hw1 width)
  have hv : (0 : Q') ≤ v := Q'.le_of_lt
    (HKPos.pow_pos (headFloor_positive hw0 hw1) _)
  have hm : (0 : Q') ≤ m := Q'.le_of_lt
    (predecessorMass_positive hw0 hw1 K width hK n)
  have ha : (0 : Q') ≤ v*(k*m) :=
    Q'.mul_nonneg _ _ hv (Q'.mul_nonneg _ _ hk hm)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hnext hk
  have hprod := Q'.mul_le_mul_of_nonneg_left _ _ _ hscaled ha
  change (v*(k*m))*(k*((k*m)*v)) ≤ (v*(k*m))*(k*mnext)
  exact hprod

/-- A certificate for the unchanged odd marginal at depth `n+1`, with the
same predecessor mass squared that appears in the projected-source cap. -/
def marginalWeight_lowerCertificate {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    Certificate (N width)
      (polyAdd (marginalWeight w K width (n+1))
        (polyNeg (cap (marginalFloor w K width n)))) :=
  lowerWeaken (marginalFloor_le_windowLower hw0 hw1 K width hK n)
    (lowerCertificate hw0 hw1 K width hK (n+1))

#print axioms predecessorMass
#print axioms predecessorMass_positive
#print axioms projectedCap
#print axioms marginalFloor
#print axioms marginalFloor_factor
#print axioms projectedSource_certificate
#print axioms projectedSource_upperCertificate
#print axioms nextMass_floor
#print axioms marginalWeight_lowerCertificate

end YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSourceBounds
