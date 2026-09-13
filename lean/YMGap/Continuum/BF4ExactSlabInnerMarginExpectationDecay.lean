/-
# Geometric comparison of ORIGINAL normalized plaquette-character means

For a fixed physical base face and representation label, grow an inner slab
around the face by margin, then compare with ANY further outer padding.
The existing original normalized expectations differ by at most

  characterAmplitude(w,spin) * (625*rho(w))^margin.

Both partition factors have been cancelled. The carrier, locality, interval
certificate, and literal embedding pin are constructed for this observable;
no analytic or geometric estimate is supplied by the caller. Coupling guards
are explicit and are fully discharged at the existing w=1/1024 pilot.
This is fixed-coupling inter-volume comparison, not a continuum or gap claim.
-/

import YMGap.Continuum.BF4ExactSlabBoundaryLimitNormalization
import YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay

namespace YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding
open YMGap.Continuum.BF4ExactSlabBulkExpectationComparison
open YMGap.Continuum.BF4ExactSlabBoundaryLimitNormalization
open YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

def shiftedCharacter (base margin : Nat) (face : Z4Plaq) (spin : Nat) : RatPoly :=
  characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent (base+margin))
    (shiftFace margin margin face)).scalar spin

def characterMean (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base : Nat) (face : Z4Plaq) (spin margin : Nat) : CReal :=
  expectation w hw0 hw1 (base+margin) (shiftedCharacter base margin face spin)

def characterAmplitude (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (spin : Nat) : Q' :=
  ((2*(16 : Q')^spin)+(2*(16 : Q')^spin))*singlePlaquetteAmplitude w hd hs

theorem shiftedFace_physical {base : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (margin : Nat) :
    shiftFace margin margin face ∈ boundaryCompleteSlabPlaquettes (centralExtent (base+margin)) :=
  shiftFace_mem (central_room (by omega)) (central_room (by omega)) hf

theorem characterImage_prefix {base : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (margin padding spin : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (centralExtent ((base+margin)+padding))).length
      ((slabEmbedding (base+margin) padding).polynomial (shiftedCharacter base margin face spin))
      (characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent ((base+margin)+padding))
        (shiftFace (margin+padding) (margin+padding) face)).scalar spin) := by
  have h := character_pin (padding := padding) (shiftedFace_physical hf margin) spin
  simpa only [shiftedCharacter, shiftFace_comp] using h

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

theorem characterMean_difference_pin {base : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (margin padding spin : Nat) :
    Equiv (CReal.sub (characterMean w hw0 hw1 base face spin (margin+padding))
      (characterMean w hw0 hw1 base face spin margin))
      (expectationDifference w hw0 hw1 (base+margin) padding (shiftedCharacter base margin face spin)) := by
  have h := expectation_prefix w hw0 hw1 ((base+margin)+padding) (characterImage_prefix hf margin padding spin)
    ((slabEmbedding (base+margin) padding).polynomial_supported _) (original_character_support _ _ spin)
  have hsub := CReal.sub_congr_left
    (y := expectation w hw0 hw1 (base+margin) (shiftedCharacter base margin face spin)) h.symm
  simpa only [characterMean, shiftedCharacter, expectationDifference, Nat.add_assoc] using hsub

/-- A fully constructed observable instance of the normalized comparison. -/
theorem characterMean_difference_bound
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base : Nat} {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes (centralExtent base))
    (margin padding spin : Nat) :
    leEv (CReal.abs (CReal.sub (characterMean w hw0 hw1 base face spin (margin+padding))
      (characterMean w hw0 hw1 base face spin margin)))
      (ofQ' (characterAmplitude w hd hs spin * (entropyRate 625 (adjustedCoreRate w hd))^margin)) := by
  let extent := centralExtent ((base+margin)+padding)
  let target := shiftFace (margin+padding) (margin+padding) face
  let q := characterPolynomial (correctedSlabPlaquettePolynomial extent target).scalar spin
  have htarget : target ∈ boundaryCompleteSlabPlaquettes extent := by
    simpa only [extent, target, Nat.add_assoc] using shiftedFace_physical hf (margin+padding)
  let P : Interval (boundaryCompleteSlabLinks extent).length q (2*(16 : Q')^spin) :=
    characterInterval (.scalar (supported_slabPlaquette _ _) (haarNorm_slabPlaquette htarget)) spin
  have hfinite := fun K => singlePlaquette_boundary_geometric_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
    hsmall hd hs K base margin padding face hf q (2*(16 : Q')^spin) P ((face_scalar_local extent target).character spin)
  have h := expectationDifference_bound_of_prefix w hw0 hw1 (base+margin) padding
    (shiftedCharacter base margin face spin) (original_character_support _ _ spin) q P.support
    (characterImage_prefix hf margin padding spin) _ hfinite
  exact leEv_trans (leEv_of_equiv (abs_equiv_congr (characterMean_difference_pin w hw0 hw1 hf margin padding spin))) h

theorem existingNome_characterMean_difference_bound {base : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (margin padding spin : Nat) :
    let w := BF4ExactSlabPlaquetteSmallNomeCertificate.nome
    let hw0 := BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos
    let hw1 := BF4ExactSlabPlaquetteSmallNomeCertificate.nome_lt_one
    let hd := BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    let hs := BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2
    leEv (CReal.abs (CReal.sub (characterMean w hw0 hw1 base face spin (margin+padding))
      (characterMean w hw0 hw1 base face spin margin)))
      (ofQ' (characterAmplitude w hd hs spin * (entropyRate 625 (adjustedCoreRate w hd))^margin)) :=
  characterMean_difference_bound _ BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos
    BF4ExactSlabPlaquetteSmallNomeCertificate.nome_lt_one BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.1
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2 BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2
    hf margin padding spin

end YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay

#print axioms YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay.shiftedCharacter
#print axioms YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay.characterMean
#print axioms YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay.characterAmplitude
#print axioms YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay.shiftedFace_physical
#print axioms YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay.characterImage_prefix
#print axioms YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay.characterMean_difference_pin
#print axioms YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay.characterMean_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay.existingNome_characterMean_difference_bound
