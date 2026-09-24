/-
# Actual selected spin-two heat transmission

The exposed spin-two solid is moved into the five-block selected chart by
three explicit tail swaps.  Harmonicity and degree are transported through
that literal chart, while prefix equivalence accounts for the harmless zero
padding introduced by block reindexing.  The final heat pairing therefore
uses the computed retained substitution rather than an assumed heat image.
-/

import YMGap.Continuum.SU2QuaternionSpinTwoHeatImage
import YMGap.Continuum.SU2QuaternionHeadHarmonicReindex
import YMGap.Continuum.SU2QuaternionFourBlockSelection
import YMGap.Continuum.SU2QuaternionRetainedImagePrefix
import YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
import YMGap.Continuum.SU2QuaternionHaarCertificateLift

namespace YMGap.Continuum.SU2QuaternionSpinTwoHeatTransmission

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul varMono)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonic
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.SU2QuaternionHeadHarmonicReindex
open YMGap.Continuum.SU2QuaternionHarmonicHeatInsertion
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionRelativeHeatInsertion
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionSpinTwoHeatImage
open YMGap.Continuum.SU2QuaternionRetainedImagePrefix
open YMGap.Continuum.SU2QuaternionAllCarrierExposedSelection
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.RGTransport (qpow)

local infix:50 " ≈ " => Q'.eqv

private theorem chain_add_local {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (p q : RatPoly) :
    applyQuaternionBlockSwapChain steps (polyAdd p q) =
      polyAdd (applyQuaternionBlockSwapChain steps p)
        (applyQuaternionBlockSwapChain steps q) := by
  induction steps generalizing p q with
  | nil => rfl
  | cons s rest ih =>
      simp only [applyQuaternionBlockSwapChain,
        reindexQuaternionPolynomial_add, ih]

private theorem chain_smul_local {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (c : Q') (p : RatPoly) :
    applyQuaternionBlockSwapChain steps (polySmul c p) =
      polySmul c (applyQuaternionBlockSwapChain steps p) := by
  induction steps generalizing p with
  | nil => rfl
  | cons s rest ih =>
      simp only [applyQuaternionBlockSwapChain,
        reindexQuaternionPolynomial_smul, ih]

/-- Three transpositions insert the retained partner at block one while
fixing the selected head block zero. -/
def spinTwoTailSteps : List (QuaternionBlockInvolution 5) :=
  [blockSwapInvolution 5 3 4 (by omega) (by omega),
   blockSwapInvolution 5 2 3 (by omega) (by omega),
   blockSwapInvolution 5 1 2 (by omega) (by omega)]

private theorem spinTwoTailSteps_source_zero :
    quaternionBlockSwapChainSource spinTwoTailSteps 0 = 0 := by
  decide

private theorem spinTwoTailSteps_source_two :
    quaternionBlockSwapChainSource spinTwoTailSteps 2 = 1 := by
  decide

private theorem spinTwoTailSteps_source_three :
    quaternionBlockSwapChainSource spinTwoTailSteps 3 = 2 := by
  decide

private theorem spinTwoTailSteps_source_four :
    quaternionBlockSwapChainSource spinTwoTailSteps 4 = 3 := by
  decide

private theorem spinTwoTailSteps_fix_head :
    ∀ s, s ∈ spinTwoTailSteps → s.map 0 = 0 := by
  intro s hs
  simp only [spinTwoTailSteps, List.mem_cons, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl <;> decide

/-- The coefficient-level harmonic representative used for the selected
five-block chart. -/
def selectedChartSolidTwo (r0 r1 r2 r3 : Bool) : RatPoly :=
  applyQuaternionBlockSwapChain spinTwoTailSteps
    (exposedSolidZonalCharacter r0 r1 r2 r3 2)

private theorem selectedChartWord_prefix (r0 r1 r2 r3 : Bool) :
    QuaternionPrefixPolynomialEqv 5
      (applyQuaternionBlockSwapChain spinTwoTailSteps
        (exposedFourWord r0 r1 r2 r3).scalar)
      (selectedWord r0 r1 r2 r3).scalar := by
  have hq : QuaternionPrefixPolyQuaternionEqv 5
      (applyQuaternionBlockSwapChainQuaternion spinTwoTailSteps
        (exposedFourWord r0 r1 r2 r3))
      (selectedWord r0 r1 r2 r3) := by
    unfold exposedFourWord selectedWord
    rw [applyQuaternionBlockSwapChainQuaternion_mul,
      applyQuaternionBlockSwapChainQuaternion_mul,
      applyQuaternionBlockSwapChainQuaternion_mul]
    exact (((applyQuaternionBlockSwapChain_orientedCoordinate_prefix
      spinTwoTailSteps (by omega) spinTwoTailSteps_source_zero r0).mul
      (applyQuaternionBlockSwapChain_orientedCoordinate_prefix
        spinTwoTailSteps (by omega) spinTwoTailSteps_source_two r1)).mul
      (applyQuaternionBlockSwapChain_orientedCoordinate_prefix
        spinTwoTailSteps (by omega) spinTwoTailSteps_source_three r2)).mul
      (applyQuaternionBlockSwapChain_orientedCoordinate_prefix
        spinTwoTailSteps (by omega) spinTwoTailSteps_source_four r3)
  have hs := hq.scalar
  rw [applyQuaternionBlockSwapChainQuaternion_scalar] at hs
  exact hs

private def radiusSquares (block : Nat) : RatPoly :=
  polyAdd
    (polyMul (polyVar (4*block)) (polyVar (4*block)))
    (polyAdd
      (polyMul (polyVar (4*block+1)) (polyVar (4*block+1)))
      (polyAdd
        (polyMul (polyVar (4*block+2)) (polyVar (4*block+2)))
        (polyMul (polyVar (4*block+3)) (polyVar (4*block+3)))))

private theorem monoMul_varMono_self_local : ∀ coordinate : Nat,
    monoMul (varMono coordinate) (varMono coordinate) =
      coordinateSquareMono coordinate
  | 0 => rfl
  | coordinate + 1 => by
      change monoMul (0 :: varMono coordinate) (0 :: varMono coordinate) =
        0 :: coordinateSquareMono coordinate
      simp only [monoMul, Nat.zero_add]
      rw [monoMul_varMono_self_local coordinate]

private theorem prefix_symm {blocks : Nat} {p q : RatPoly}
    (h : QuaternionPrefixPolynomialEqv blocks p q) :
    QuaternionPrefixPolynomialEqv blocks q p := by
  induction h with
  | nil => exact .nil
  | cons hterm _ ih =>
      exact .cons
        ⟨Q'.eqv_symm hterm.coefficient,
          fun coordinate hc => (hterm.exponent coordinate hc).symm⟩ ih

private theorem radiusSquares_prefix (block : Nat) :
    QuaternionPrefixPolynomialEqv 5
      (radiusSquares block) (quaternionRadiusPolynomial block) := by
  unfold radiusSquares quaternionRadiusPolynomial polyAdd polyMul polyVar
  simp only [List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    List.append_nil, List.cons_append, List.nil_append]
  rw [monoMul_varMono_self_local, monoMul_varMono_self_local,
    monoMul_varMono_self_local, monoMul_varMono_self_local]
  exact .cons
    ⟨Q'.mul_one_eqv 1, fun _ _ => rfl⟩ (.cons
      ⟨Q'.mul_one_eqv 1, fun _ _ => rfl⟩ (.cons
        ⟨Q'.mul_one_eqv 1, fun _ _ => rfl⟩ (.cons
          ⟨Q'.mul_one_eqv 1, fun _ _ => rfl⟩ .nil)))

private theorem selectedChart_radius_at_prefix
    (source target : Nat) (htarget : target < 5)
    (hmap : quaternionBlockSwapChainSource spinTwoTailSteps target = source) :
    QuaternionPrefixPolynomialEqv 5
      (applyQuaternionBlockSwapChain spinTwoTailSteps
        (quaternionRadiusPolynomial source))
      (quaternionRadiusPolynomial target) := by
  have hc (i : Fin 4) := coordinate_exposed spinTwoTailSteps htarget hmap i
  have hsquares : QuaternionPrefixPolynomialEqv 5
      (applyQuaternionBlockSwapChain spinTwoTailSteps (radiusSquares source))
      (radiusSquares target) := by
    unfold radiusSquares
    rw [chain_add_local, chain_add_local, chain_add_local,
      chain_mul, chain_mul, chain_mul, chain_mul]
    exact QuaternionPrefixPolynomialEqv.append
      ((hc 0).mul (hc 0))
      (QuaternionPrefixPolynomialEqv.append
        ((hc 1).mul (hc 1))
        (QuaternionPrefixPolynomialEqv.append
          ((hc 2).mul (hc 2)) ((hc 3).mul (hc 3))))
  exact (applyQuaternionBlockSwapChain_prefix spinTwoTailSteps
      (prefix_symm (radiusSquares_prefix source))).trans
    (hsquares.trans (radiusSquares_prefix target))

private theorem selectedChart_radius_zero_prefix :
    QuaternionPrefixPolynomialEqv 5
      (applyQuaternionBlockSwapChain spinTwoTailSteps
        (quaternionRadiusPolynomial 0))
      (quaternionRadiusPolynomial 0) :=
  selectedChart_radius_at_prefix 0 0 (by omega)
    spinTwoTailSteps_source_zero

private theorem selectedChart_radius_one_prefix :
    QuaternionPrefixPolynomialEqv 5
      (applyQuaternionBlockSwapChain spinTwoTailSteps
        (quaternionRadiusPolynomial 1))
      (quaternionRadiusPolynomial 2) :=
  selectedChart_radius_at_prefix 1 2 (by omega)
    spinTwoTailSteps_source_two

private theorem selectedChart_radius_two_prefix :
    QuaternionPrefixPolynomialEqv 5
      (applyQuaternionBlockSwapChain spinTwoTailSteps
        (quaternionRadiusPolynomial 2))
      (quaternionRadiusPolynomial 3) :=
  selectedChart_radius_at_prefix 2 3 (by omega)
    spinTwoTailSteps_source_three

private theorem selectedChart_radius_three_prefix :
    QuaternionPrefixPolynomialEqv 5
      (applyQuaternionBlockSwapChain spinTwoTailSteps
        (quaternionRadiusPolynomial 3))
      (quaternionRadiusPolynomial 4) :=
  selectedChart_radius_at_prefix 3 4 (by omega)
    spinTwoTailSteps_source_four

private theorem selectedChart_radius_prefix :
    QuaternionPrefixPolynomialEqv 5
      (applyQuaternionBlockSwapChain spinTwoTailSteps
        fourQuaternionRadiusProduct)
      selectedRadius := by
  unfold fourQuaternionRadiusProduct fourQuaternionRadiusProductAt selectedRadius
  rw [chain_mul, chain_mul, chain_mul]
  exact selectedChart_radius_zero_prefix.mul
    (selectedChart_radius_one_prefix.mul
      (selectedChart_radius_two_prefix.mul selectedChart_radius_three_prefix))

private theorem selectedChart_one_prefix :
    QuaternionPrefixPolynomialEqv 5
      (applyQuaternionBlockSwapChain spinTwoTailSteps polyOne) polyOne := by
  have h := (applyQuaternionBlockSwapChainQuaternion_one_prefix
    spinTwoTailSteps).scalar
  rw [applyQuaternionBlockSwapChainQuaternion_scalar] at h
  exact h

/-- The harmonic chart and the literal selected polynomial differ only by
trailing-zero padding inside the declared five-block carrier. -/
theorem selectedChartSolidTwo_prefix (r0 r1 r2 r3 : Bool) :
    QuaternionPrefixPolynomialEqv 5
      (selectedChartSolidTwo r0 r1 r2 r3)
      (selectedSolidTwo r0 r1 r2 r3) := by
  unfold selectedChartSolidTwo selectedSolidTwo exposedSolidZonalCharacter
  simp only [solidZonalCharacterPolynomial, chain_add_local, chain_mul,
    chain_smul_local]
  exact QuaternionPrefixPolynomialEqv.append
    (((selectedChartWord_prefix r0 r1 r2 r3).smul 2).mul
      ((selectedChartWord_prefix r0 r1 r2 r3).smul 2))
    ((selectedChart_radius_prefix.mul selectedChart_one_prefix).smul (-1))

/-- Literal harmonicity in the selected five-block chart, obtained by
head-fixing reindexing of the checked exposed solid. -/
theorem selectedChartSolidTwo_harmonic (r0 r1 r2 r3 : Bool) :
    RatPolyCoeffEqv
      (headLaplacian (selectedChartSolidTwo r0 r1 r2 r3)) polyZero := by
  apply harmonic_swapChain (by omega) spinTwoTailSteps
    spinTwoTailSteps_fix_head
  exact laplacian_exposedSolidZonalCharacter_zero r0 r1 r2 r3 2

private theorem exposedSolidTwo_supported (r0 r1 r2 r3 : Bool) :
    SupportedQuaternionBlocks 5
      (exposedSolidZonalCharacter r0 r1 r2 r3 2) := by
  have oriented (block : Nat) (hb : block < 5) (r : Bool) :
      QuaternionSupported 5 (orientedCoordinateQuaternion block r) := by
    cases r
    · exact QuaternionSupported.coordinate hb
    · exact (QuaternionSupported.coordinate hb).conj
  have hs : SupportedQuaternionBlocks 5
      (exposedFourWord r0 r1 r2 r3).scalar :=
    ((((oriented 0 (by omega) r0).mul (oriented 1 (by omega) r1)).mul
      (oriented 2 (by omega) r2)).mul (oriented 3 (by omega) r3)).scalar
  have hr : SupportedQuaternionBlocks 5 fourQuaternionRadiusProduct := by
    exact supported_polyMul (quaternionRadiusPolynomial_supported 5 0 (by omega))
      (supported_polyMul (quaternionRadiusPolynomial_supported 5 1 (by omega))
        (supported_polyMul (quaternionRadiusPolynomial_supported 5 2 (by omega))
          (quaternionRadiusPolynomial_supported 5 3 (by omega))))
  unfold exposedSolidZonalCharacter solidZonalCharacterPolynomial
  exact polyAdd_supported
    (supported_polyMul (polySmul_supported hs 2) (polySmul_supported hs 2))
    (polySmul_supported (supported_polyMul hr (supported_one 5)) (-1))

private theorem selectedChartSolidTwo_supported (r0 r1 r2 r3 : Bool) :
    SupportedQuaternionBlocks 5 (selectedChartSolidTwo r0 r1 r2 r3) :=
  applyQuaternionBlockSwapChain_supported spinTwoTailSteps _
    (exposedSolidTwo_supported r0 r1 r2 r3)

private theorem selectedChartSolidTwo_degree (r0 r1 r2 r3 : Bool) :
    HasQuaternionBlockDegree 0 2
      (selectedChartSolidTwo r0 r1 r2 r3) := by
  apply chain_degree spinTwoTailSteps (by omega)
  rw [spinTwoTailSteps_source_zero]
  exact exposedSolidZonalCharacter_blockDegree
    r0 r1 r2 r3 0 (by decide) 2

/-- The actual relative heat factor reproduces the selected spin-two solid
with multiplier `w^8`.  The right endpoint is the computed retained image,
identified coefficientwise with the canonical exposed four-block solid.
No heat-image identity is assumed. -/
theorem selectedSolidTwo_heat_pairing
    (tail : Nat) (htail : 4 ≤ tail)
    (r0 r1 r2 r3 : Bool) (w : Q') (K : Nat) (hK : 2 ≤ K)
    (r : RatPoly) (hr : SupportedQuaternionBlocks (tail+1) r)
    (hindependent : HeadQuaternionIndependent r) :
    quaternionHaar (tail+1)
      (polyMul (polyMul (relativeHeat w K)
        (selectedSolidTwo r0 r1 r2 r3)) r) ≈
      qpow w 8 * quaternionHaar (tail+1)
        (polyMul (liftHead
          (exposedSolidZonalCharacter r0 r1 r2 r3 2)) r) := by
  let chart := selectedChartSolidTwo r0 r1 r2 r3
  have hchart5 : SupportedQuaternionBlocks 5 chart :=
    selectedChartSolidTwo_supported r0 r1 r2 r3
  have hselected5 := selectedSolidTwo_supported r0 r1 r2 r3
  have hchart : SupportedQuaternionBlocks (tail+1) chart := by
    intro term hterm
    exact Nat.le_trans (hchart5 term hterm) (by omega)
  have hselected : SupportedQuaternionBlocks (tail+1)
      (selectedSolidTwo r0 r1 r2 r3) := by
    intro term hterm
    exact Nat.le_trans (hselected5 term hterm) (by omega)
  have hheat : SupportedQuaternionBlocks (tail+1) (relativeHeat w K) :=
    heat_supported (by omega) (by omega) w K
  have hprefix5 := selectedChartSolidTwo_prefix r0 r1 r2 r3
  have hprefix : QuaternionPrefixPolynomialEqv (tail+1) chart
      (selectedSolidTwo r0 r1 r2 r3) :=
    prefix_on_supported hprefix5 hchart5 hselected5
  have hleft := quaternionHaar_prefixPolynomialEqv (tail+1)
    (((QuaternionPrefixPolynomialEqv.refl (tail+1) (relativeHeat w K)).mul hprefix).mul
      (QuaternionPrefixPolynomialEqv.refl (tail+1) r))
    (supported_polyMul (supported_polyMul hheat hchart) hr)
    (supported_polyMul (supported_polyMul hheat hselected) hr)
  have htrans := harmonic_transmission_same_carrier tail (by omega) w K 2 chart r
    (selectedChartSolidTwo_degree r0 r1 r2 r3)
    (selectedChartSolidTwo_harmonic r0 r1 r2 r3) hindependent
  rw [if_pos hK] at htrans
  have houtPrefix := quaternionHaar_prefixPolynomialEqv (tail+1)
    ((retainedImage_prefix hprefix).mul
      (QuaternionPrefixPolynomialEqv.refl (tail+1) r))
    (supported_polyMul (retainedImage_supported tail (by omega) hchart) hr)
    (supported_polyMul (retainedImage_supported tail (by omega) hselected) hr)
  have houtCoeff := haar_of_coeff (blocks := tail+1)
    ((retainedImage_selectedSolidTwo r0 r1 r2 r3).mul_right r)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ htrans
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ houtPrefix houtCoeff)))

/-- Remove the four radii in the original Haar carrier, not by a false
coefficient equality with the constant polynomial. -/
theorem selectedSolidTwo_eq_character {blocks : Nat} (hb : 4 < blocks)
    (r0 r1 r2 r3 : Bool) :
    QuaternionHaarCarrierEqv blocks (selectedSolidTwo r0 r1 r2 r3)
      (characterPolynomial (selectedWord r0 r1 r2 r3).scalar 2) :=
  solidZonalCharacterPolynomial_eq_character_of_radius_eq_one _ _
    (fourQuaternionRadiusProductAt_eq_one blocks 0 2 3 4
      (by omega) (by omega) (by omega) hb) 2

private theorem haar_shuffle (blocks : Nat) (a p r : RatPoly) :
    quaternionHaar blocks (polyMul (polyMul a p) r) ≈
      quaternionHaar blocks (polyMul (polyMul a r) p) :=
  haar_of_coeff ((RatPolyCoeffEqv.mul_assoc a p r).trans
    (((RatPolyCoeffEqv.mul_comm p r).mul_left a).trans
      (RatPolyCoeffEqv.mul_assoc a r p).symm))

/-- Actual label-two character transmission with all spectator insertions
retained. The ordinary character is not asserted to be coefficientwise
harmonic: the proof passes through the solid representative in the SAME
Haar carrier on both sides. -/
theorem selectedCharacterTwo_heat_pairing
    (tail : Nat) (htail : 4 ≤ tail)
    (r0 r1 r2 r3 : Bool) (w : Q') (K : Nat) (hK : 2 ≤ K)
    (r : RatPoly) (hr : SupportedQuaternionBlocks (tail+1) r)
    (hindependent : HeadQuaternionIndependent r) :
    quaternionHaar (tail+1)
      (polyMul (polyMul (relativeHeat w K)
        (characterPolynomial (selectedWord r0 r1 r2 r3).scalar 2)) r) ≈
      qpow w 8 * quaternionHaar (tail+1)
        (polyMul (liftHead
          (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar 2)) r) := by
  have hin := selectedSolidTwo_eq_character (by omega : 4 < tail+1)
    r0 r1 r2 r3 (polyMul (relativeHeat w K) r)
  have hleft := Q'.eqv_trans _ _ _
    (haar_shuffle (tail+1) (relativeHeat w K) _ r)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hin)
      (Q'.eqv_symm (haar_shuffle (tail+1) (relativeHeat w K)
        (selectedSolidTwo r0 r1 r2 r3) r)))
  have hout : quaternionHaar (tail+1)
      (polyMul r (liftHead (exposedSolidZonalCharacter r0 r1 r2 r3 2))) ≈
      quaternionHaar (tail+1)
        (polyMul r (liftHead
          (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar 2))) := by
    simpa only [liftBoundary] using
      (lift_carrier 1 (exposedSolid_eq_character (by omega : 3 < tail)
        r0 r1 r2 r3 2) r)
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _
      (selectedSolidTwo_heat_pairing tail htail r0 r1 r2 r3 w K hK r hr hindependent)
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _
          (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ r))
          (Q'.eqv_trans _ _ _ hout
            (haar_of_coeff (RatPolyCoeffEqv.mul_comm r _))))))

end YMGap.Continuum.SU2QuaternionSpinTwoHeatTransmission

#print axioms YMGap.Continuum.SU2QuaternionSpinTwoHeatTransmission.selectedChartSolidTwo_prefix
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoHeatTransmission.selectedChartSolidTwo_harmonic
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoHeatTransmission.selectedSolidTwo_heat_pairing
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoHeatTransmission.selectedSolidTwo_eq_character
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoHeatTransmission.selectedCharacterTwo_heat_pairing
