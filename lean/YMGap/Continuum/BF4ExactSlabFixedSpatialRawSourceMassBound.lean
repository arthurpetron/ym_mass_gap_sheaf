/-
# Original raw-source mass with an explicit late-cutoff modulus

The actual positive-depth source cap and ORIGINAL odd-marginal floor share
the SAME predecessor mass squared. Scaled substitution removes that mass;
only the explicit positive floor coefficient is inverted. The resulting
constant depends on nome and FULL width, but not cutoff or positive depth.
An explicit geometric cutoff pays the raw-mass term in the original Haar
energy ceiling to any prescribed positive rational tolerance.

This is an additive cutoff estimate, NOT an OWN-variance-relative estimate,
width/coupling-uniform bound, physical scaling family or continuum theorem.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilySourceVarianceBound
import YMGap.Continuum.BF4DyadicWilsonSquareProjectionGain
import YMGap.Continuum.SU2QuaternionCyclicOmittedNorm
import YMGap.Continuum.PositiveContractionResidual
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialRawSourceMassBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarIntervalSecondMoment
open YMGap.Continuum.QuaternionHaarPositiveFloorCancellation (floor_insertion)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (kineticCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (kineticCap_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity (spatialCeiling)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor (spatialCeiling_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (marginalMass_pin marginalMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSourceBounds
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilySourceVarianceBound
open YMGap.Continuum.BF4DyadicWilsonSquareProjectionGain (rawSourceMass)
open YMGap.Continuum.SU2QuaternionCyclicOmittedNorm (omittedRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound (rg_qpow_eqv_pow)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks

attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource
  predecessorMass oddMass rawSourceMass

private theorem haar_one (blocks : Nat) : H blocks polyOne ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _))
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one blocks))

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    H blocks (polyNeg p) ≈ -(H blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_cap (blocks : Nat) (c : Q') : H blocks (cap c) ≈ c :=
  Q'.eqv_trans _ _ _ (quaternionHaar_polySmul blocks c polyOne)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ (haar_one blocks))
      (Q'.mul_one_eqv c))

private theorem haar_square_le {blocks : Nat} {p : RatPoly} {c : Q'}
    (S : SquareBound blocks p c) : H blocks (polyMul p p) ≤ c := by
  have he : H blocks (gap c p) ≈ c + -(H blocks (polyMul p p)) :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (haar_cap blocks c) (haar_neg blocks _))
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ S.certificate.haar_nonnegative (Q'.le_of_eqv he))

/-- A constructed interval for the ACTUAL source at positive terminal depth. -/
def rawSourceInterval {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    Interval (N width)
      (projectedEndpointSource w K width (terminalMessage w K width (n+1)))
      (projectedCap w K width n) where
  support := by
    unfold projectedEndpointSource
    exact familyProject_supported _ (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width (n+1)))
  nonnegative := Q'.le_of_lt
    (Q'.mul_pos (spatialCeiling_positive hw0 hw1 width)
      (Q'.mul_pos (kineticCap_positive hw0 hw1 width)
        (predecessorMass_positive hw0 hw1 K width hK n)))
  upper := projectedSource_upperCertificate hw0 hw1 K width hK n
  lower := (Certificate.constant (N width) (projectedCap w K width n)
    (Q'.le_of_lt (Q'.mul_pos (spatialCeiling_positive hw0 hw1 width)
      (Q'.mul_pos (kineticCap_positive hw0 hw1 width)
        (predecessorMass_positive hw0 hw1 K width hK n))))).add
    (projectedSource_certificate hw0 hw1 K width hK n)

/-- Both factors of the same predecessor mass are retained in the raw cap. -/
theorem rawSourceMass_le_capSquare {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    rawSourceMass w K width (n+1) ≤ sourceCapScale w width *
      (predecessorMass w K width n * predecessorMass w K width n) := by
  unfold rawSourceMass
  change H (N width) (polyMul
    (projectedEndpointSource w K width (terminalMessage w K width (n+1)))
    (projectedEndpointSource w K width (terminalMessage w K width (n+1)))) ≤ _
  have hs := haar_square_le
    (YMGap.Continuum.QuaternionHaarIntervalSecondMoment.Interval.squareBound
      (rawSourceInterval hw0 hw1 K width hK n))
  have he : projectedCap w K width n * projectedCap w K width n ≈
      sourceCapScale w width * (predecessorMass w K width n * predecessorMass w K width n) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 0) (.mul (.var 1) (.var 2))))
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.var 2) (.var 2)))
      (by decide) (fun
        | 0 => spatialCeiling w width
        | 1 => kineticCap w width
        | _ => predecessorMass w K width n)
  exact Q'.le_trans' _ _ _ hs (Q'.le_of_eqv he)

/-- ORIGINAL marginal mass, with exactly the same predecessor square. -/
theorem marginalMass_floor {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    sourceFloorScale w width *
      (predecessorMass w K width n * predecessorMass w K width n) ≤
        oddMass w K width (n+1) := by
  have hf := floor_insertion (Certificate.one (N width))
    (marginalWeight_lowerCertificate hw0 hw1 K width hK n)
  have hl : marginalFloor w K width n * H (N width) polyOne ≈
      sourceFloorScale w width *
        (predecessorMass w K width n * predecessorMass w K width n) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (haar_one (N width)))
      (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (marginalFloor_factor w K width n))
  have hr : H (N width) (polyMul polyOne (marginalWeight w K width (n+1))) ≈
      oddMass w K width (n+1) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.one_mul _))
      (marginalMass_pin w K width (n+1))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _ hf (Q'.le_of_eqv hr))

/-- Scaled substitution, without dividing by predecessor mass or variance. -/
theorem rawSourceMass_cleared {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    sourceFloorScale w width * rawSourceMass w K width (n+1) ≤
      sourceCapScale w width * oddMass w K width (n+1) := by
  let L := sourceFloorScale w width
  let U := sourceCapScale w width
  let M := predecessorMass w K width n * predecessorMass w K width n
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ L
    (rawSourceMass_le_capSquare hw0 hw1 K width hK n)
    (Q'.le_of_lt (sourceFloorScale_positive hw0 hw1 width))
  have hf := Q'.mul_le_mul_of_nonneg_left _ _ U
    (marginalMass_floor hw0 hw1 K width hK n)
    (Q'.le_of_lt (sourceCapScale_positive hw0 hw1 width))
  have he : L*(U*M) ≈ U*(L*M) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => L | 1 => U | _ => M)
  exact Q'.le_trans' _ _ _ hs (Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hf)

/-- Computed cap/floor ratio; nome/width dependence is explicit in the type. -/
def rawSourceMassConstant {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width : Nat) : Q' :=
  sourceCapScale w width *
    Q'.recipPos (sourceFloorScale w width) (sourceFloorScale_positive hw0 hw1 width)

theorem rawSourceMassConstant_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width : Nat) :
    (0 : Q') < rawSourceMassConstant hw0 hw1 width :=
  Q'.mul_pos (sourceCapScale_positive hw0 hw1 width) (Q'.recipPos_pos _ _)

/-- Uniform in late cutoff and positive depth, NOT nome or spatial width. -/
theorem rawSourceMass_bound {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    rawSourceMass w K width (n+1) ≤
      rawSourceMassConstant hw0 hw1 width * oddMass w K width (n+1) := by
  let L := sourceFloorScale w width
  let a := Q'.recipPos L (sourceFloorScale_positive hw0 hw1 width)
  let A := rawSourceMass w K width (n+1)
  let Z := oddMass w K width (n+1)
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ a
    (rawSourceMass_cleared hw0 hw1 K width hK n) (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have hl : (L*A)*a ≈ A :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ a (Q'.mul_comm_eqv L A))
      (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A L a)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left A _ _ (Q'.mul_recipPos_eqv L _))
          (Q'.mul_one_eqv A)))
  have hr : (sourceCapScale w width*Z)*a ≈ rawSourceMassConstant hw0 hw1 width*Z :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => sourceCapScale w width | 1 => Z | _ => a)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hr))

/-- Explicit tolerance modulus. It includes the original heat-head guard. -/
def rawSourceMassCutoff {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width : Nat) (epsilon : Q') : Nat :=
  max (headCutoff w)
    (PositiveContractionResidual.geometricCutoff w
      (rawSourceMassConstant hw0 hw1 width) epsilon)

/-- The unhalved raw term; half of it occurs in the original energy ceiling.
It is divided by the SAME positive original partition. EVERY positive depth
shares this cutoff modulus. No variance-relative conclusion is asserted. -/
theorem omitted_rawSourceMass_bound {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width : Nat) {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) (K : Nat)
    (hK : rawSourceMassCutoff hw0 hw1 width epsilon ≤ K) (n : Nat) :
    (omittedRate w K * rawSourceMass w K width (n+1)) *
      Q'.recipPos (oddMass w K width (n+1))
        (oddMass_positive hw0 hw1 K width (Nat.le_trans (Nat.le_max_left _ _) hK) (n+1))
      ≤ epsilon := by
  have hhead : headCutoff w ≤ K := Nat.le_trans (Nat.le_max_left _ _) hK
  let B := rawSourceMassConstant hw0 hw1 width
  let Z := oddMass w K width (n+1)
  let hz := oddMass_positive hw0 hw1 K width hhead (n+1)
  let a := Q'.recipPos Z hz
  have hrho : (0 : Q') ≤ omittedRate w K :=
    RGTransport.qpow_nonneg w (Q'.le_of_lt hw0) _
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ a
    (Q'.mul_le_mul_of_nonneg_left _ _ (omittedRate w K)
      (rawSourceMass_bound hw0 hw1 K width hhead n) hrho)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have hc : (omittedRate w K*(B*Z))*a ≈ omittedRate w K*B :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ a (Q'.eqv_symm
      (Q'.mul_assoc_eqv (omittedRate w K) B Z)))
      (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (omittedRate w K*B) Z a)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Z hz))
          (Q'.mul_one_eqv _)))
  have hexp : K ≤ (K+1)*(K+3) :=
    Nat.le_trans (Nat.le_succ K)
      (by simpa using Nat.mul_le_mul_left (K+1) (by omega : 1 ≤ K+3))
  have hp : omittedRate w K ≤ w^K :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (rg_qpow_eqv_pow w _))
      (HKConvGen.pow_base_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hexp)
  have ht := PositiveContractionResidual.geometric_bound (Q'.le_of_lt hw0) hw1
    (Q'.le_of_lt (rawSourceMassConstant_positive hw0 hw1 width)) hepsilon K
    (Nat.le_trans (Nat.le_max_right _ _) hK)
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hc)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ B hp
          (Q'.le_of_lt (rawSourceMassConstant_positive hw0 hw1 width))) ht))

/-- The halved raw-mass contribution as written in `haarCenteredDebt`.
Its upper bound is epsilon/2, with the same computed cutoff at every n+1. -/
theorem omitted_half_rawSourceMass_bound {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width : Nat) {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) (K : Nat)
    (hK : rawSourceMassCutoff hw0 hw1 width epsilon ≤ K) (n : Nat) :
    (omittedRate w K * (HalfPow.half*rawSourceMass w K width (n+1))) *
      Q'.recipPos (oddMass w K width (n+1))
        (oddMass_positive hw0 hw1 K width (Nat.le_trans (Nat.le_max_left _ _) hK) (n+1))
      ≤ HalfPow.half*epsilon := by
  let a := Q'.recipPos (oddMass w K width (n+1))
    (oddMass_positive hw0 hw1 K width (Nat.le_trans (Nat.le_max_left _ _) hK) (n+1))
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
    (omitted_rawSourceMass_bound hw0 hw1 width hepsilon K hK n) HalfPow.half_nonneg
  have he : (omittedRate w K*(HalfPow.half*rawSourceMass w K width (n+1)))*a ≈
      HalfPow.half*((omittedRate w K*rawSourceMass w K width (n+1))*a) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
      (.mul (.var 1) (.mul (.mul (.var 0) (.var 2)) (.var 3))) (by decide)
      (fun
        | 0 => omittedRate w K
        | 1 => HalfPow.half
        | 2 => rawSourceMass w K width (n+1)
        | _ => a)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hs

#print axioms rawSourceInterval
#print axioms rawSourceMass_le_capSquare
#print axioms marginalMass_floor
#print axioms rawSourceMass_cleared
#print axioms rawSourceMassConstant
#print axioms rawSourceMassConstant_positive
#print axioms rawSourceMass_bound
#print axioms rawSourceMassCutoff
#print axioms omitted_rawSourceMass_bound
#print axioms omitted_half_rawSourceMass_bound

end YMGap.Continuum.BF4ExactSlabFixedSpatialRawSourceMassBound
