/-
# SAME original full partition versus the spectator background

The original unit form is pinned through the existing temporal change of
variables to the positive spectator background times the actual lower
collar, its reflected upper collar, and the four complete crossing heat
factors. No crossing factor is replaced by a selected representation.

The local interval cap is (1+delta)^52: at most 24 lower and 24 upper
faces, and exactly four crossing faces. At the fixed nome this is at
most two, independently of K and half. Thus the SAME original full
partition is at most 2*Zsp. Limit passages and thermodynamic excitation
are not asserted here.
-/

import YMGap.Continuum.BF4ExactSlabBulkProbeHomogeneousFloor

namespace YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests
open YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization
open YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes
open YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin
open YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate
open YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation (product_eq_one_add)
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (heatProduct_supported)
open YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm (reflected_coeff)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS (rawForm rawForm_unit)
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarHeatCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit (fullHeatProduct)
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram (faceLinkA)

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

/-- Full crossing heat prefixes on precisely the four removed probe faces. -/
def crossingHeat (w : Q') (K half : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K half) (crossingIds half)

def localHeat (w : Q') (K half : Nat) : RatPoly :=
  polyMul (polyMul (collarHeat w K half) (upperCollarHeat w K half)) (crossingHeat w K half)

def partitionCap (w : Q') : Q' :=
  ((1+productErrorCap w 24)*(1+productErrorCap w 24)) * (1+heatRemainderBound w)^4

theorem interface_split (w : Q') (K half : Nat) :
    RatPolyCoeffEqv (interfacePolynomial w K half)
      (polyMul (crossingHeat w K half) (spectatorInterface w K half)) :=
  (polynomialProduct_perm (faceHeatPolynomial w K half) (crossing_spectator_partition half).symm).trans
    (polynomialProduct_append _ _ _)

theorem dressedLower_unit_collar (w : Q') (K half : Nat) :
    RatPolyCoeffEqv (dressedLower w K (.unit : PlaquetteExpression half))
      (polyMul (collarHeat w K half) (spectatorHeat w K half)) :=
  (dressedLower_collar w K (.unit : PlaquetteExpression half)).trans
    ((RatPolyCoeffEqv.one_mul (collarHeat w K half)).mul_right _)

theorem dressedUpper_unit_collar (w : Q') (K half : Nat) :
    PaddedPolynomialCoeffEqv (blocks half) (dressedUpper w K (.unit : PlaquetteExpression half))
      (polyMul (upperCollarHeat w K half) (upperSpectatorHeat w K half)) :=
  (dressed_reflection w K (.unit : PlaquetteExpression half)).symm.trans
    ((PaddedPolynomialCoeffEqv.of_coeff (reflected_coeff _ (dressedLower_unit_collar w K half))).trans
      (ReflectionImage.mul (upperCollarHeat_image w K half) (upperSpectatorHeat_image w K half)))

private theorem reorder (c l i j u v : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul c l) (polyMul (polyMul i j) (polyMul u v)))
      (polyMul (polyMul (polyMul v l) j) (polyMul (polyMul c u) i)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.mul (.var 2) (.var 3)) (.mul (.var 4) (.var 5))))
    (.mul (.mul (.mul (.var 5) (.var 1)) (.var 3)) (.mul (.mul (.var 0) (.var 4)) (.var 2)))
    (by decide) (fun | 0 => c | 1 => l | 2 => i | 3 => j | 4 => u | _ => v)

variable {w : Q'} (hw : (0 : Q') ≤ w)
include hw

theorem crossingHeat_supported (K half : Nat) : SupportedQuaternionBlocks (blocks half) (crossingHeat w K half) :=
  (LocalSquareExpansion.finiteProduct _ _ (fun _ hi => faceExpansion hw K (crossingIds_fixed hi))).polynomialSupported

/-- The unit of the ORIGINAL form, after proved changes of variables only. -/
theorem originalUnit_partition_pin (K half : Nat) :
    rawForm w K (.unit : PlaquetteExpression half) .unit ≈
      quaternionHaar (blocks half) (polyMul (positiveBackground w K half) (localHeat w K half)) := by
  have hc := heatProduct_supported w K (centralExtent half) (lowerCollar half)
  have hl := spectatorHeat_supported w K half
  have hu := upperCollarHeat_supported w K half
  have hv := upperSpectatorHeat_supported w K half
  have hi := crossingHeat_supported hw K half
  have hj := (spectatorExpansion hw K half).polynomialSupported
  have hp := PaddedPolynomialCoeffEqv.mul (.of_coeff (dressedLower_unit_collar w K half))
    (PaddedPolynomialCoeffEqv.mul (.of_coeff (interface_split w K half)) (dressedUpper_unit_collar w K half))
  have hh := hp.haar
    (supported_polyMul (dressedLower_supported w K (.unit : PlaquetteExpression half))
      (supported_polyMul (interfaceExpansion hw K half).polynomialSupported
        (dressedUpper_supported w K (.unit : PlaquetteExpression half))))
    (supported_polyMul (supported_polyMul hc hl) (supported_polyMul (supported_polyMul hi hj) (supported_polyMul hu hv)))
  exact Q'.eqv_trans _ _ _ (upper_numerator_spatialGram w K (.unit : PlaquetteExpression half))
    (Q'.eqv_trans _ _ _ hh (haar_of_coeff (reorder _ _ _ _ _ _)))

omit hw in
/-- Arbitrary-insertion equality transports both interval endpoints. -/
def intervalTransport {blockCount : Nat} {p q : RatPoly} {c : Q'}
    (hp : SupportedQuaternionBlocks blockCount p) (h : HaarCarrierEqv blockCount p q)
    (P : Interval blockCount q c) : Interval blockCount p c where
  support := hp
  nonnegative := P.nonnegative
  upper := .transport (HaarCarrierEqv.add (.refl _ _) (HaarCarrierEqv.neg h)) P.upper
  lower := .transport (HaarCarrierEqv.add (.refl _ _) h) P.lower

variable (hw1 : w ≤ (1 : Q')) (hsmall : heatRatio w ≤ HalfPow.half)

def crossingFaceInterval (K : Nat) {half id : Nat} (hi : id ∈ centralFixedFaceIds half) :
    Interval (blocks half) (faceHeatPolynomial w K half id) (1+heatRemainderBound w) := by
  let link := faceLinkA (slabPlaquetteAt (centralExtent half) id)
  let p := (spatialWord (centralExtent half) link).scalar
  have h : HaarCarrierEqv (blocks half) (faceHeatPolynomial w K half id)
      (polyAdd polyOne (heatRemainder w K p)) :=
    HaarCarrierEqv.trans (faceHeat_pin w K half id) (RatPolyCoeffEqv.haarCarrier (heatPrefix_split w K p))
  exact intervalTransport (faceExpansion hw K hi).polynomialSupported h
    ((Interval.one _).add (remainderInterval hw hw1 hsmall (spatialScalarBound (centralExtent half) link) K))

def crossingHeatInterval (K half : Nat) :
    Interval (blocks half) (crossingHeat w K half) ((1+heatRemainderBound w)^4) := by
  have P := Interval.productUniform (faceHeatPolynomial w K half) (1+heatRemainderBound w) (crossingIds half)
    (fun _ hi => crossingFaceInterval hw hw1 hsmall K (crossingIds_fixed hi))
  rw [crossingIds_length] at P
  exact P

def lowerCollarHeatInterval (K half : Nat) :
    Interval (blocks half) (collarHeat w K half) (1+productErrorCap w 24) :=
  .ofCoeff (heatProduct_supported w K (centralExtent half) (lowerCollar half))
    (product_eq_one_add w (centralExtent half) K (lowerCollar half))
    ((Interval.one _).add (collarInterval hw hw1 hsmall K half))

def upperCollarHeatInterval (K half : Nat) :
    Interval (blocks half) (upperCollarHeat w K half) (1+productErrorCap w 24) :=
  .ofCoeff (upperCollarHeat_supported w K half)
    (product_eq_one_add w (centralExtent half) K (reflectedCollarIds half))
    ((Interval.one _).add (reflectedCollarInterval hw hw1 hsmall K half))

def localHeatInterval (K half : Nat) : Interval (blocks half) (localHeat w K half) (partitionCap w) :=
  ((lowerCollarHeatInterval hw hw1 hsmall K half).mul (upperCollarHeatInterval hw hw1 hsmall K half)).mul
    (crossingHeatInterval hw hw1 hsmall K half)

variable (hdelta : heatRemainderBound w ≤ 1)
include hw hw1 hsmall hdelta

theorem originalUnit_partition_upper (K half : Nat) :
    rawForm w K (.unit : PlaquetteExpression half) .unit ≤ partitionCap w * backgroundMass w K half :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (originalUnit_partition_pin hw K half))
    (Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (Q'.le_trans' _ _ _
        ((localHeatInterval hw hw1 hsmall K half).weighted_haar_bound (backgroundCertificate hw hw1 hsmall hdelta K half))
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (background_integral_pin hw K half)))))

omit hw hw1 hsmall hdelta in
theorem existingNome_partitionCap_le_two : partitionCap nome ≤ 2 := by decide

omit hw hw1 hsmall hdelta in
/-- All cutoffs and translated volumes, at the explicitly fixed nome. -/
theorem existingNome_originalUnit_upper (K half : Nat) :
    rawForm nome K (.unit : PlaquetteExpression half) .unit ≤ 2 * backgroundMass nome K half :=
  Q'.le_trans' _ _ _
    (originalUnit_partition_upper (Q'.le_of_lt nome_pos) (Q'.le_of_lt nome_lt_one)
      existingNome_guards.1 (Q'.le_of_lt existingNome_guards.2) K half)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ existingNome_partitionCap_le_two
      (Q'.le_of_lt (existingNome_background_positive K half)))

omit hw hw1 hsmall hdelta in
theorem existingNome_fullPartition_upper (K half : Nat) :
    quaternionHaar (blocks half) (fullHeatProduct nome K half) ≤ 2 * backgroundMass nome K half :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (rawForm_unit nome K half)) (existingNome_originalUnit_upper K half)

end YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison.interface_split
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison.dressedLower_unit_collar
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison.dressedUpper_unit_collar
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison.crossingHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison.originalUnit_partition_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison.intervalTransport
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison.crossingFaceInterval
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison.crossingHeatInterval
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison.lowerCollarHeatInterval
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison.upperCollarHeatInterval
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison.localHeatInterval
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison.originalUnit_partition_upper
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison.existingNome_partitionCap_le_two
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison.existingNome_originalUnit_upper
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbePartitionComparison.existingNome_fullPartition_upper
