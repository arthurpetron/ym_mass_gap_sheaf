/-
# Exact collar-removed tests on the full ORIGINAL spectator OS background

The local scalar-square moment is checked from the original extent-one
polynomial and transported through the original block embedding. The
computational pilot is computations/original_plaquette_small_nome_minor.py.

The two reference tests retain the full spectator interface and detached
lower action. Their amplitudes are (0, lambda*Zsp/32768, Zsp, 0) and their
energies are (Zsp, lambda*Zsp/65536), with lambda=(2*w^3)^4.
These are NOT the amplitudes with the local lower collar reinstated.
-/

import YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorFactorization

namespace YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests
open YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization
open YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorFactorization
open YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm (reflected_coeff)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels
open YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

theorem haar_one (blockCount : Nat) : quaternionHaar blockCount polyOne ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one _))
    (Q'.eqv_refl _)) (Q'.eqv_of_eq (Q'.add_zero' 1))

theorem source_scalar_square : quaternionHaar 116
    (polyMul (loopPolynomial (fun _ => (false,false))) (loopPolynomial (fun _ => (false,false)))) ≈ Q'.invSucc 255 :=
  by decide +kernel

theorem bulkScalar_square_haar (half : Nat) :
    quaternionHaar (blocks half) (polyMul (bulkScalar half) (bulkScalar half)) ≈ Q'.invSucc 255 := by
  apply Q'.eqv_trans _ _ _ (embedded_moment half (supported_polyMul source_scalar_supported source_scalar_supported)
    (supported_polyMul (bulkScalar_supported half) (bulkScalar_supported half)) ?_) source_scalar_square
  rw [BlockEmbedding.polynomial_mul]
  exact (bulkScalar_embedding half).mul (bulkScalar_embedding half)

theorem spectatorPair_coeff (w : Q') (K half : Nat) {p p' q q' : RatPoly}
    (hp : RatPolyCoeffEqv p p') (hq : RatPolyCoeffEqv q q') :
    spectatorPair w K half p q ≈ spectatorPair w K half p' q' :=
  haar_of_coeff_eqv _ (((reflected_coeff _ hp).mul hq).mul_right _)

/-- Insert the actual scalar loop on both sides of the same OS pairing. -/
theorem scalar_pair_insert {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) (p q : RatPoly)
    (hq : SupportedQuaternionBlocks (blocks half) q) :
    scalarSpectatorPair w K half p q ≈
      spectatorPair w K half (polyMul p (bulkScalar half)) (polyMul q (bulkScalar half)) := by
  let S := bulkScalar half
  let I := spectatorInterface w K half
  let rp := reflectCorrectedSlabPolynomial (centralExtent half) p
  let rS := reflectCorrectedSlabPolynomial (centralExtent half) S
  have h : PaddedPolynomialCoeffEqv (blocks half)
      (polyMul (polyMul rp q) (polyMul (polyMul rS S) I))
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) (polyMul p S)) (polyMul q S)) I) :=
    (PaddedPolynomialCoeffEqv.of_coeff ((RatPolyCoeffEqv.mul_assoc _ _ _).symm.trans
      ((RatPolyCoeffEqv.mul_four_swap rp q rS S).mul_right I))).trans
      (((PaddedPolynomialCoeffEqv.of_prefix (reflectCorrectedSlabPolynomial_mul_prefix (centralExtent half) p S)).symm.mul
        (.refl _ _)).mul (.refl _ _))
  have hs := bulkScalar_supported half
  have hi := (spectatorExpansion hw K half).polynomialSupported
  exact h.haar
    (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hq)
      (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hs) hi))
    (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) (supported_polyMul hq hs)) hi)

private theorem swap_last (p q r : RatPoly) : RatPolyCoeffEqv (polyMul (polyMul p q) r) (polyMul (polyMul p r) q) :=
  (RatPolyCoeffEqv.mul_assoc p q r).trans (((RatPolyCoeffEqv.mul_comm q r).mul_left p).trans
    (RatPolyCoeffEqv.mul_assoc p r q).symm)

def unitReferencePair (w : Q') (K half : Nat) (p q : RatPoly) : Q' :=
  spectatorPair w K half (polyMul p (spectatorHeat w K half)) (polyMul q (spectatorHeat w K half))

def scalarReferencePair (w : Q') (K half : Nat) (p q : RatPoly) : Q' :=
  channelWeightPower w 4 * scalarSpectatorPair w K half
    (polyMul p (spectatorHeat w K half)) (polyMul q (spectatorHeat w K half))

theorem scalarReferencePair_factor {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (blocks half) p) (hq : SupportedQuaternionBlocks (blocks half) q)
    (hlp : LinkLocal (centralExtent half) (probeLinks half) p) (hlq : LinkLocal (centralExtent half) (probeLinks half) q) :
    scalarReferencePair w K half p q ≈
      (channelWeightPower w 4 * (quaternionHaar (blocks half) (polyMul p (bulkScalar half)) *
        quaternionHaar (blocks half) (polyMul q (bulkScalar half)))) * backgroundMass w K half := by
  have h := Q'.eqv_trans _ _ _ (scalar_pair_insert hw K half _ _
    (supported_polyMul hq (spectatorHeat_supported w K half)))
    (Q'.eqv_trans _ _ _ (spectatorPair_coeff w K half (swap_last _ _ _) (swap_last _ _ _))
      (detached_pair_factor hw K half (supported_polyMul hp (bulkScalar_supported half))
        (supported_polyMul hq (bulkScalar_supported half)) ((hlp).mul (bulkScalar_local half)) ((hlq).mul (bulkScalar_local half))))
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h) (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

def unitAmplitudeReference (w : Q') (K half : Nat) (p : RatPoly) : Q' := unitReferencePair w K half p polyOne
def scalarAmplitudeReference (w : Q') (K half : Nat) (p : RatPoly) : Q' := scalarReferencePair w K half p (bulkScalar half)
def unitEnergyReference (w : Q') (K half : Nat) : Q' := unitReferencePair w K half polyOne polyOne
def scalarEnergyReference (w : Q') (K half : Nat) : Q' := scalarReferencePair w K half (bulkScalar half) (bulkScalar half)

/-- The exact local signal, with all nome dependence exposed. -/
def signal (w : Q') : Q' := channelWeightPower w 4 * Q'.invSucc 32767
def energyScale (w : Q') : Q' := channelWeightPower w 4 * Q'.invSucc 65535

variable {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)

include hw

theorem unitAmplitudeReference_factor {p : RatPoly} (hp : SupportedQuaternionBlocks (blocks half) p)
    (hl : LinkLocal (centralExtent half) (probeLinks half) p) :
    unitAmplitudeReference w K half p ≈ quaternionHaar (blocks half) p * backgroundMass w K half :=
  Q'.eqv_trans _ _ _ (detached_pair_factor hw K half hp (supported_one _) hl (BlockLocal.one _ _))
    (qmul (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (haar_one _)) (Q'.mul_one_eqv _)) (Q'.eqv_refl _))

theorem unit_probe_zero : unitAmplitudeReference w K half (lower (bulkProbe half)) ≈ 0 :=
  Q'.eqv_trans _ _ _ (unitAmplitudeReference_factor hw K half (lower_supported _) (bulkProbe_local half))
    (Q'.eqv_trans _ _ _ (qmul (bulkProbe_haar_zero half) (Q'.eqv_refl _)) (RingNormaliser.q_zero_mul _))

theorem unit_unit_pin : unitAmplitudeReference w K half polyOne ≈ backgroundMass w K half :=
  Q'.eqv_trans _ _ _ (unitAmplitudeReference_factor hw K half (supported_one _) (BlockLocal.one _ _))
    (Q'.eqv_trans _ _ _ (qmul (haar_one _) (Q'.eqv_refl _)) (Q'.one_mul_eqv _))

theorem scalar_probe_pin : scalarAmplitudeReference w K half (lower (bulkProbe half)) ≈ signal w * backgroundMass w K half :=
  Q'.eqv_trans _ _ _
    (scalarReferencePair_factor hw K half (lower_supported _) (bulkScalar_supported half) (bulkProbe_local half) (bulkScalar_local half))
    (qmul (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (qmul (bulk_mixed_haar half) (bulkScalar_square_haar half))
      (by decide : Q'.invSucc 127 * Q'.invSucc 255 ≈ Q'.invSucc 32767))) (Q'.eqv_refl _))

theorem scalar_unit_zero : scalarAmplitudeReference w K half polyOne ≈ 0 := by
  have hS := Q'.eqv_trans _ _ _ (haar_of_coeff_eqv (blocks half) (RatPolyCoeffEqv.one_mul (bulkScalar half)))
    (bulkScalar_haar_zero half)
  have hz := Q'.eqv_trans _ _ _ (qmul hS (bulkScalar_square_haar half)) (RingNormaliser.q_zero_mul _)
  exact Q'.eqv_trans _ _ _
    (scalarReferencePair_factor hw K half (supported_one _) (bulkScalar_supported half) (BlockLocal.one _ _) (bulkScalar_local half))
    (Q'.eqv_trans _ _ _ (qmul (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (QPoly.q_mul_zero _))
      (Q'.eqv_refl _)) (RingNormaliser.q_zero_mul _))

theorem unit_energy_pin : unitEnergyReference w K half ≈ backgroundMass w K half := unit_unit_pin hw K half

theorem scalar_energy_pin : scalarEnergyReference w K half ≈ energyScale w * backgroundMass w K half :=
  Q'.eqv_trans _ _ _
    (scalarReferencePair_factor hw K half (bulkScalar_supported half) (bulkScalar_supported half)
      (bulkScalar_local half) (bulkScalar_local half))
    (qmul (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (qmul (bulkScalar_square_haar half) (bulkScalar_square_haar half))
      (by decide : Q'.invSucc 255 * Q'.invSucc 255 ≈ Q'.invSucc 65535))) (Q'.eqv_refl _))

end YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference.haar_one
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference.source_scalar_square
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference.bulkScalar_square_haar
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference.spectatorPair_coeff
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference.scalar_pair_insert
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference.scalarReferencePair_factor
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference.unitAmplitudeReference_factor
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference.unit_probe_zero
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference.unit_unit_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference.scalar_probe_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference.scalar_unit_zero
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference.unit_energy_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference.scalar_energy_pin
