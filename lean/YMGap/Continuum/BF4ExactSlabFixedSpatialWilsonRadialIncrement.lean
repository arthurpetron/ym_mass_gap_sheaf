/-
# Radial displacement and its quartic correction in the ORIGINAL Wilson edge

The literal lower and upper ordered words are Haar-unit quaternions. Their
fundamental trace increment is bounded by the mixed radial/chordal term
and the necessary squared-chordal correction under the COMPLETE original
edge density. The existing energy identity and odd partition are unchanged.

This does not bound either new moment, factor an expectation, or compare
the result with centered variance. In particular, the quartic correction
cannot be discarded. No small relative loss or scaling survival is claimed.
-/

import YMGap.Continuum.QuaternionHaarRadialChordalIncrement
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRadialIncrement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement
  (upperOriented upper_character_lift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWordDifference
open YMGap.Continuum.QuaternionHaarRadialChordalIncrement

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage oddMass

private theorem lower_supported {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) : Supported (N width+N width) (orientedLink width e) := by
  have hi := List.idxOf_lt_length_of_mem he
  have hs : Supported (N width+N width)
      (PolyQuaternion.coordinateVariable ((baseLinks width).idxOf e.link)) :=
    Supported.coordinate (by omega)
  unfold orientedLink link
  rw [if_pos he]
  split
  · exact hs.conj
  · exact hs

private theorem upper_supported {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) : Supported (N width+N width) (upperOriented width e) := by
  have hi := List.idxOf_lt_length_of_mem he
  have hs : Supported (N width+N width)
      (PolyQuaternion.coordinateVariable (N width+(baseLinks width).idxOf e.link)) :=
    Supported.coordinate (by omega)
  unfold upperOriented
  split
  · exact hs.conj
  · exact hs

private theorem lower_unit {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) :
    HaarCarrierEqv (N width+N width) (polyQuaternionNorm (orientedLink width e)) polyOne := by
  have hi := List.idxOf_lt_length_of_mem he
  have hu := haarNorm_coordinate (by omega : (baseLinks width).idxOf e.link < N width+N width)
  unfold orientedLink link
  rw [if_pos he]
  split
  · exact HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)) hu
  · exact hu

private theorem upper_unit {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) :
    HaarCarrierEqv (N width+N width) (polyQuaternionNorm (upperOriented width e)) polyOne := by
  have hi := List.idxOf_lt_length_of_mem he
  have hu := haarNorm_coordinate (by omega : N width+(baseLinks width).idxOf e.link < N width+N width)
  unfold upperOriented
  split
  · exact HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)) hu
  · exact hu

private theorem neg_supported {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem padded_neg {n : Nat} {p q : RatPoly} (h : PaddedPolynomialCoeffEqv n p q) :
    PaddedPolynomialCoeffEqv n (polyNeg p) (polyNeg q) := by
  unfold PaddedPolynomialCoeffEqv
  rw [reindexQuaternionPolynomial_neg, reindexQuaternionPolynomial_neg]
  exact RatPolyCoeffEqv.neg h

/-- The mixed radial and quartic terms use the original lower and upper words. -/
def wilsonRadialBudget (width : Nat) (loop : SourceLoop width) : RatPoly :=
  radialBudget (sourceWord width loop.edges) (wordWith (upperOriented width) loop.edges)

/-- The SAME unnormalized energy is bounded in its actual complete edge
measure. No active-link or source-factorization premise is used by kinematics. -/
theorem wilson_energy_radial_cleared {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) (loop : SourceLoop width) :
    (2 : Q') * energy w K width (terminalMessage w K width depth)
        (sourceCharacter width loop.edges 1) ≤
      quaternionHaar (N width+N width)
        (polyMul (edgeDensity w K width (terminalMessage w K width depth))
          (wilsonRadialBudget width loop)) := by
  let p := sourceWord width loop.edges
  let q := wordWith (upperOriented width) loop.edges
  let W := edgeDensity w K width (terminalMessage w K width depth)
  have hp := word_supported (orientedLink width) loop.edges
    (fun e he => lower_supported (loop.physical e he))
  have hq := word_supported (upperOriented width) loop.edges
    (fun e he => upper_supported (loop.physical e he))
  have hup := word_unit (orientedLink width) loop.edges
    (fun e he => lower_unit (loop.physical e he))
  have huq := word_unit (upperOriented width) loop.edges
    (fun e he => upper_unit (loop.physical e he))
  have hw := edgeDensity_supported w K width (terminalMessage_supported w K width depth)
  have hj := jump_supported width (sourceCharacter_supported width loop.edges 1)
  have hd : SupportedQuaternionBlocks (N width+N width) (traceDifference p q) :=
    supported_add (character_supported hp.scalar 1)
      (neg_supported (character_supported hq.scalar 1))
  have hpin : PaddedPolynomialCoeffEqv (N width+N width)
      (jump width (sourceCharacter width loop.edges 1)) (traceDifference p q) :=
    (PaddedPolynomialCoeffEqv.refl _ _).add (padded_neg (upper_character_lift width loop))
  have he := Q'.eqv_trans _ _ _
    (energy_identity w K width (terminalMessage_supported w K width depth)
      (sourceCharacter_supported width loop.edges 1))
    ((hpin.mul hpin).haar_insert (supported_polyMul hj hj) (supported_polyMul hd hd) W hw)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (weighted_radial_bound
      (edgeCertificate hw0 hw1 K width hK (terminalMessage_supported w K width depth)
        (terminalMessage_certificate hw0 hw1 K width hK depth)) hp hq hup huq)

/-- Normalization uses only the SAME original positive odd partition. The
mixed radial-displacement and quartic moments are still unestimated. -/
theorem wilson_energy_radial_normalized {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) (loop : SourceLoop width) :
    (2 : Q') * normalizedEnergy hw0 hw1 K width hK depth
        (sourceCharacter width loop.edges 1) ≤
      quaternionHaar (N width+N width)
          (polyMul (edgeDensity w K width (terminalMessage w K width depth))
            (wilsonRadialBudget width loop)) *
        Q'.recipPos (oddMass w K width depth) (oddMass_positive hw0 hw1 K width hK depth) := by
  have hz := oddMass_positive hw0 hw1 K width hK depth
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
    (Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recipPos _ hz)
      (wilson_energy_radial_cleared hw0 hw1 K width hK depth loop)
      (Q'.le_of_lt (Q'.recipPos_pos _ hz)))

#print axioms wilsonRadialBudget
#print axioms wilson_energy_radial_cleared
#print axioms wilson_energy_radial_normalized

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRadialIncrement
