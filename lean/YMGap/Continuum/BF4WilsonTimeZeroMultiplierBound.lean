/-
# Time-zero Wilson multiplication is bounded in the ORIGINAL reflected form

A source loop at offset H lies exactly on the reflection-fixed slice of
the H-window chart. Its constructed character square bound therefore feeds
the selected-action OS multiplier estimate, retaining all original heat
factors and the SAME positive reciprocal partition. The bound passes to
the existing limiting reflected form through its original diagonal moduli.

The rational squared-norm cap depends only on the spin (four at spin one),
not the test vector or lattice regulators. Finite statements need 0<w<1;
the existing limiting form retains its explicit small-nome guards. This
does not yet construct the multiplication map on the spatial-union
completion or assert bounded multiplication by arbitrary positive-time
observables or arbitrary OS-null states.
-/

import YMGap.Continuum.BF4ExactSlabSiteMultiplierBound
import YMGap.Continuum.BF4WilsonTimeZeroChart
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz

namespace YMGap.Continuum.BF4WilsonTimeZeroMultiplierBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization (blockCount)
open YMGap.Continuum.BF4ExactSlabSiteConditionalSquare (OneSided)
open YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction
open YMGap.Continuum.BF4ExactSlabSiteMultiplierBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz (form)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal (reciprocalTerm)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (characterBound)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex (slabFaceReflectId)
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.BF4WilsonTimeZeroChart

local infix:50 " ≈ " => Q'.eqv

private theorem chart_reflection {base : Nat} (H : Nat)
    (e : WindowExpression base) (he : Within H e) (r t : Nat) :
    ReflectionImage (chartExtent base r H t)
      (chartInsertion r H t e) (chartInsertion r H t (mirror H e)) := by
  have hw : paddedWidth base r ≤ chartExtent base r H t := by
    unfold chartExtent adjacentEvenExtent centralExtent
    omega
  have hc : paddedWidth base r+1+t+H = (paddedWidth base r+t+H)+1 := by omega
  have hp := placed_reflection hw hc (centeredExpression r e)
    ((centered_within r H e).mpr he)
  simpa only [chartInsertion, centeredExpression, mirror, recenter_mapOffsets] using hp

private theorem chart_reflected_value {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H : Nat) (e : WindowExpression base) (he : Within H e)
    (r stage t : Nat) :
    finiteValue w hw0 hw1 (chartExtent base r H t) (chartIds base r H t)
      (fun _ hi => chartIds_physical hi)
      (polyMul (reflectCorrectedSlabPolynomial (chartExtent base r H t) (chartInsertion r H t e))
        (chartInsertion r H t e)) stage ≈
      chartScalar hw0 hw1 H (.mul (mirror H e) e) r stage t := by
  let p := chartInsertion r H t e
  let action := selectedHeat w (headCutoff w+stage) (paddedWidth base r+t+H) (chartIds base r H t)
  have hp := placed_supported (chartExtent base r H t) (paddedWidth base r+1+t) (centeredExpression r e)
  have hrp := placed_supported (chartExtent base r H t) (paddedWidth base r+1+t)
    (centeredExpression r (mirror H e))
  have ha := selectedHeat_supported w (headCutoff w+stage) (paddedWidth base r+t+H) (chartIds base r H t)
  have hhaar := ((PaddedPolynomialCoeffEqv.mul
    (chart_reflection H e he r t) (.refl _ p)).mul (.refl _ action)).haar
    (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hp) ha)
    (supported_polyMul (supported_polyMul hrp hp) ha)
  unfold chartScalar finiteValue numerator
  exact Q'.mul_eqv_congr_right _ _ _ hhaar

/-- Original finite normalized OS bound, with one shared action and partition. -/
theorem chartScalar_timeZero_multiplier_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H : Nat) (L : SourceLoop base) (spin : Nat)
    (e : WindowExpression base) (he : Within H e) (r stage t : Nat) :
    chartScalar hw0 hw1 H
      (.mul (mirror H (.mul (.loop H L spin) e)) (.mul (.loop H L spin) e)) r stage t ≤
      characterBound spin * chartScalar hw0 hw1 H (.mul (mirror H e) e) r stage t := by
  let R := paddedWidth base r+t+H
  let E := chartExtent base r H t
  let ids := chartIds base r H t
  let p := chartInsertion r H t e
  let a := chartInsertion r H t (.loop H L spin)
  have hw : paddedWidth base r ≤ E := by
    unfold E chartExtent adjacentEvenExtent centralExtent
    omega
  have hc : paddedWidth base r+1+t+H = R+1 := by dsimp [R]; omega
  have hp : OneSided R p := placed_oneSided hw hc (centeredExpression r e)
    ((centered_within r H e).mpr he)
  have hps := placed_supported E (paddedWidth base r+1+t) (centeredExpression r e)
  have hcount : t+(2*H+t)=2*(t+H) := by omega
  have hperm : ((lowerFaceIds R ids).map (slabFaceReflectId E)).Perm (upperFaceIds R ids) := by
    have h := selectedLower_reflection_perm (radius := R) (width := paddedWidth base r)
      (start := paddedWidth base r+1) (depth := t+H) (by dsimp [R]; omega)
    simpa only [ids, R, E, chartIds, chartExtent, selectedIds, hcount] using h
  have hraw := selectedAction_multiplier_bound hw0 hw1 (headCutoff w+stage) R
    (Nat.le_add_right _ _) ids (fun _ hi => chartIds_physical hi) hperm p a hp hps
    (chart_fixed_local r H t L spin) (chart_squareBound r H t L spin)
  let reciprocal := reciprocalTerm w hw0 hw1 E ids (fun _ hi => chartIds_physical hi) stage
  have hr : (0 : Q') ≤ reciprocal :=
    Q'.le_of_lt (PositiveRationalCauchyReciprocal.term_pos _ _ _ stage)
  have hnormalized :
      finiteValue w hw0 hw1 E ids (fun _ hi => chartIds_physical hi)
        (polyMul (reflectCorrectedSlabPolynomial E (polyMul a p)) (polyMul a p)) stage ≤
      characterBound spin * finiteValue w hw0 hw1 E ids (fun _ hi => chartIds_physical hi)
        (polyMul (reflectCorrectedSlabPolynomial E p) p) stage :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ reciprocal hraw hr)
      (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
  have hleft := chart_reflected_value hw0 hw1 H (.mul (.loop H L spin) e) ⟨Nat.le_refl H, he⟩ r stage t
  have hright := chart_reflected_value hw0 hw1 H e he r stage t
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hnormalized (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hright)))

attribute [local irreducible] chartScalar spatialLimit

/-- The existing reflected form inherits the bound with unchanged diagonal moduli. -/
theorem form_timeZero_multiplier_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base : Nat} (hb : 0<base) (H : Nat) (L : SourceLoop base) (spin : Nat)
    (e : WindowExpression base) (he : Within H e) :
    leEv (form hw0 hw1 hsmall hd hs hb H
      (.mul (.loop H L spin) e) (.mul (.loop H L spin) e) ⟨Nat.le_refl H, he⟩ ⟨Nat.le_refl H, he⟩)
      (mul (ofQ' (characterBound spin)) (form hw0 hw1 hsmall hd hs hb H e e he he)) := by
  let ae : WindowExpression base := .mul (.loop H L spin) e
  have hae : Within H ae := ⟨Nat.le_refl H, he⟩
  have ha := spatial_diagonal_converges hw0 hw1 H (.mul (mirror H ae) ae)
    ⟨mirror_within H ae, within_mono (by omega : H ≤ 2*H) ae hae⟩ hsmall hd hs hb
  have hp := spatial_diagonal_converges hw0 hw1 H (.mul (mirror H e) e)
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) e he⟩ hsmall hd hs hb
  apply leEv_of_convergesTo_le ha (convergesTo_const_mul (ofQ' (characterBound spin)) hp)
  intro n
  apply leEv_ofQ'_of_approx_ge
  intro k
  exact chartScalar_timeZero_multiplier_bound hw0 hw1 H L spin e he n n n

#print axioms chartScalar_timeZero_multiplier_bound
#print axioms form_timeZero_multiplier_bound

end YMGap.Continuum.BF4WilsonTimeZeroMultiplierBound
