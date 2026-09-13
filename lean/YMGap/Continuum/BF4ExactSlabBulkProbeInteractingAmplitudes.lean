/-
# Concrete ORIGINAL test amplitudes and the full spectator OS background

The two translated tests have exact Haar formulas with the full original
lower action and every unselected interface heat factor. The scalar test
retains its four original fundamental weights explicitly.

The unit reference energy is the actual spectator OS background
Zsp = Haar(theta(Lfar) * Lfar * Isp), not Haar(Lfar^2). Its positive floor
is explicit in the nome and spectator-face count, independent of cutoff,
and NOT uniform in volume. No interacting minor sign or normalized
thermodynamic excitation floor is asserted.
-/

import YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization
import YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison

namespace YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests
open YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization
open YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm
open YMGap.Continuum.BF4ExactSlabPartialInterfaceTests
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabLowerChannelLocality
open YMGap.Continuum.BF4ExactSlabLocalBilinearChannels
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels (channelWeightPower)
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.ClusterCount4DProgress

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

theorem linkLocal_lower {half : Nat} {links : List Z4Link} {p : RatPoly}
    (hp : LinkLocal (centralExtent half) links p)
    (hl : ∀ link, link ∈ links → linkHalfSide half link = .lower) : LowerLocal half p :=
  fun t ht block hb hn => hp t ht block hb (fun hm => hn (hl _ hm))

theorem spectatorHeat_lower (w : Q') (K half : Nat) : LowerLocal half (spectatorHeat w K half) := by
  apply linkLocal_lower (spectatorHeat_local w K half)
  intro link hl
  obtain ⟨id, hi, he⟩ := List.mem_flatMap.mp hl
  exact lower_face_link (mem_centralLowerFaceIds.mp (detached_mem hi)).2 he

theorem probeFace_lower (half : Nat) : plaquetteHalfSide half (probeFace half) = .lower := by
  rw [probeFace, translated_side]
  exact (mem_centralLowerFaceIds.mp BF4ExactSlabPlaquetteCoordinateChannels.probeId_lower).2

theorem bulkScalar_lower (half : Nat) : LowerLocal half (bulkScalar half) :=
  linkLocal_lower (bulkScalar_local half) (fun _ hi => lower_face_link (probeFace_lower half) hi)

theorem scalarTest_supported (w : Q') (K half : Nat) :
    SupportedQuaternionBlocks (blocks half) (scalarTest w K half) :=
  supported_polyMul (bulkScalar_supported half) (spectatorHeat_supported w K half)

theorem scalarTest_lower (w : Q') (K half : Nat) : LowerLocal half (scalarTest w K half) :=
  (bulkScalar_lower half).mul (spectatorHeat_lower w K half)

/-- Canonical integral with the full spectator interface. -/
def spectatorPair (w : Q') (K half : Nat) (p q : RatPoly) : Q' :=
  quaternionHaar (blocks half) (polyMul
    (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) q) (spectatorInterface w K half))

/-- The local scalar square is unweighted here; the four heat weights are
exhibited outside the integral in the scalar pin theorems. -/
def scalarSpectatorPair (w : Q') (K half : Nat) (p q : RatPoly) : Q' :=
  quaternionHaar (blocks half) (polyMul
    (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) q)
    (polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) (bulkScalar half)) (bulkScalar half))
      (spectatorInterface w K half)))

variable {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) (hK : 1 ≤ K) (half : Nat)

include hw in
theorem unit_integrand_pin (p q : RatPoly) (hq : SupportedQuaternionBlocks (blocks half) q) :
    quaternionHaar (blocks half) (polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) q)
      (retainedPolynomial (w := w) K half (localChoice half none))) ≈ spectatorPair w K half p q :=
  (retained_unit_pin w K half).haar_insert (product_supported hw K half _ _ (fun _ hi => hi))
    (spectatorExpansion hw K half).polynomialSupported _ (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hq)

include hw in
theorem scalar_integrand_pin (p q : RatPoly) (hq : SupportedQuaternionBlocks (blocks half) q) :
    quaternionHaar (blocks half) (polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) q)
      (retainedPolynomial (w := w) K half (localChoice half (some (false,false))))) ≈
        channelWeightPower w 4 * scalarSpectatorPair w K half p q := by
  have hs := supported_polyMul (reflectCorrectedSlabPolynomial_support _ (bulkScalar half)) (bulkScalar_supported half)
  have h := (retained_scalar_pin w K half).haar_insert
    (product_supported hw K half _ _ (fun _ hi => hi))
    (supported_polyMul (supported_smul hs _) (spectatorExpansion hw K half).polynomialSupported)
    (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) q)
    (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hq)
  exact Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _
    (haar_of_coeff_eqv _ (((RatPolyCoeffEqv.polyMul_smul_left (channelWeightPower w 4) _ _).mul_left _).trans
      (RatPolyCoeffEqv.polyMul_smul_right (channelWeightPower w 4) _ _)))
    (quaternionHaar_polySmul _ _ _))

theorem unitAmplitude_pin (e : PlaquetteExpression half) :
    testAmplitude hw K hK half (localChoice half none) (spectatorHeat w K half) e ≈
      spectatorPair w K half (dressedLower w K e) (spectatorHeat w K half) :=
  Q'.eqv_trans _ _ _
    (testAmplitude_haar hw K hK half _ _ (spectatorHeat_supported w K half) (spectatorHeat_lower w K half) e)
    (unit_integrand_pin hw K half _ _ (spectatorHeat_supported w K half))

theorem scalarAmplitude_pin (e : PlaquetteExpression half) :
    testAmplitude hw K hK half (localChoice half (some (false,false))) (scalarTest w K half) e ≈
      channelWeightPower w 4 * scalarSpectatorPair w K half (dressedLower w K e) (scalarTest w K half) :=
  Q'.eqv_trans _ _ _
    (testAmplitude_haar hw K hK half _ _ (scalarTest_supported w K half) (scalarTest_lower w K half) e)
    (scalar_integrand_pin hw K half _ _ (scalarTest_supported w K half))

omit hw hK in
def backgroundMass (w : Q') (K half : Nat) : Q' :=
  spectatorPair w K half (spectatorHeat w K half) (spectatorHeat w K half)

theorem unitEnergy_pin : referenceEnergy hw K hK half (localChoice half none) (spectatorHeat w K half) ≈
    backgroundMass w K half :=
  Q'.eqv_trans _ _ _
    (referenceEnergy_haar hw K hK half _ _ (spectatorHeat_supported w K half) (spectatorHeat_lower w K half))
    (unit_integrand_pin hw K half _ _ (spectatorHeat_supported w K half))

theorem scalarEnergy_pin :
    referenceEnergy hw K hK half (localChoice half (some (false,false))) (scalarTest w K half) ≈
      channelWeightPower w 4 * scalarSpectatorPair w K half (scalarTest w K half) (scalarTest w K half) :=
  Q'.eqv_trans _ _ _
    (referenceEnergy_haar hw K hK half _ _ (scalarTest_supported w K half) (scalarTest_lower w K half))
    (scalar_integrand_pin hw K half _ _ (scalarTest_supported w K half))

/-- An explicit path inside the full spectator tree, not a replacement of it. -/
def spectatorUnit : UnitLeaf (spectatorExpansion hw K half).tree :=
  productUnit _ _ (fun _ hi => faceExpansion hw K (spectatorIds_fixed hi))
    (fun _ hi => faceUnit hw K (spectatorIds_fixed hi))

include hw in
theorem background_lower_square :
    quaternionHaar (blocks half) (spectatorHeat w K half) * quaternionHaar (blocks half) (spectatorHeat w K half) ≤
      backgroundMass w K half := by
  have hpin := Q'.eqv_trans _ _ _
    (expansion_mixed_pairing (spectatorExpansion hw K half) _ _
      (spectatorHeat_supported w K half) (spectatorHeat_supported w K half)
      (spectatorHeat_lower w K half) (spectatorHeat_lower w K half))
    (ReflectedSquareTreeTestForm.diagonal_pin _ _ _)
  exact Q'.le_trans' _ _ _
    ((spectatorUnit hw K half).observable_square_le (spectatorExpansion hw K half).weightsNonnegative _ _)
    (Q'.ge_of_eqv hpin)

omit hw hK in
/-- Cutoff-independent but explicitly volume-dependent. -/
def backgroundFloor (w : Q') (half : Nat) : Q' :=
  (1 + -heatRemainderBound w)^(lowerSpectators half).length *
    (1 + -heatRemainderBound w)^(lowerSpectators half).length

include hw in
theorem background_floor (hw1 : w ≤ 1) (hsmall : heatRatio w ≤ HalfPow.half)
    (hdelta : heatRemainderBound w < 1) : backgroundFloor w half ≤ backgroundMass w K half := by
  have hp := HKPos.pow_pos (HKPos.one_sub_pos hdelta) (lowerSpectators half).length
  have hf : (1 + -heatRemainderBound w)^(lowerSpectators half).length ≤
      quaternionHaar (blocks half) (spectatorHeat w K half) :=
    faceProduct_floor hw hw1 hsmall (Q'.le_of_lt hdelta) K _ _
      (fun _ hi => (mem_centralLowerFaceIds.mp (detached_mem hi)).1)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg hf hf (Q'.le_trans' _ _ _ (Q'.le_of_lt hp) hf) (Q'.le_of_lt hp))
    (background_lower_square hw K half)

omit hw hK in
theorem backgroundFloor_positive (w : Q') (half : Nat) (hdelta : heatRemainderBound w < 1) :
    (0 : Q') < backgroundFloor w half :=
  Q'.mul_pos (HKPos.pow_pos (HKPos.one_sub_pos hdelta) _) (HKPos.pow_pos (HKPos.one_sub_pos hdelta) _)

include hw in
theorem background_positive (hw1 : w ≤ 1) (hsmall : heatRatio w ≤ HalfPow.half)
    (hdelta : heatRemainderBound w < 1) : (0 : Q') < backgroundMass w K half :=
  Q'.pos_of_lt_of_le (backgroundFloor_positive w half hdelta) (background_floor hw K half hw1 hsmall hdelta)

omit hw hK in
theorem existingNome_background_positive (K half : Nat) :
    (0 : Q') < backgroundMass BF4ExactSlabPlaquetteSmallNomeCertificate.nome K half :=
  background_positive (Q'.le_of_lt BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos) K half
    (Q'.le_of_lt BF4ExactSlabPlaquetteSmallNomeCertificate.nome_lt_one) existingNome_guards.1 existingNome_guards.2

end YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.linkLocal_lower
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.spectatorHeat_lower
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.probeFace_lower
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.bulkScalar_lower
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.scalarTest_supported
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.scalarTest_lower
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.unit_integrand_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.scalar_integrand_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.unitAmplitude_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.scalarAmplitude_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.unitEnergy_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.scalarEnergy_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.spectatorUnit
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.background_lower_square
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.background_floor
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.backgroundFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.background_positive
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes.existingNome_background_positive
