/-
# The retained channel square pays the same original variance

The lower and upper local bands compare the actual fringe-projected terminal
source with one common passive spectator. The lower band keeps the complete
signed spatial family inside the retained channel square. The upper band
compares the ORIGINAL uncentered second moment, which bounds its OWN variance.
No source, channel mass, or variance is inverted. The coefficient depends on
the nome and complete family footprint; no scaling-uniform claim is made.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelRetainedSquare
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelVarianceBound
import YMGap.Continuum.SU2QuaternionPassiveChannelLinearBand

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelSquareCredit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyLocalBand
  (familySpectator_supported familySpectator_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
  (localLower localUpper localLower_positive localUpper_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent
  (spatialSpan_fringe_independent_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource oddMoment_projected_source)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSourceBounds
  (projectedSource_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance marginalMass_pin marginalMass_positive marginalVariance_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelVarianceBound
  (projectedFamilySpectator projectedFamilySpectator_outside_passive
    projectedFamily_lowerCertificate projectedFamily_upperCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelRetainedSquare
  (familyChannelObservableSquare)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyMul)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyCertificate
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionFamilyHeatGramPositiveWeight
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
open YMGap.Continuum.SU2QuaternionPassiveChannelLinearBand
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n
attribute [local irreducible] baseLinks terminalMessage marginalWeight
  oddMass oddVariance spatialSpan

section OriginalVariance

attribute [local irreducible] projectedEndpointSource

private theorem shifted_zero (f : RatPoly) : RatPolyCoeffEqv (shifted f 0) f :=
  ((RatPolyCoeffEqv.one_smul f).add
    ((RatPolyCoeffEqv.smul_coefficient (by decide : Q'.eqv (-0) 0) polyOne).trans
      (RatPolyCoeffEqv.zero_smul polyOne))).trans (RatPolyCoeffEqv.add_zero f)

/-- The source square on the right is the original uncentered moment. -/
theorem original_variance_le_projected_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat)
    (f : RatPoly) (hf : SupportedQuaternionBlocks (N width) f)
    (hfringe : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    oddMass w K width depth * oddVariance hw0 hw1 K width hK depth f ≤
      sourceMoment (N width) w K (List.range (N width))
        (projectedEndpointSource w K width (terminalMessage w K width depth))
        (polyMul f f) := by
  let W := marginalWeight w K width depth
  let z := H (N width) W
  let hz := marginalMass_positive hw0 hw1 K width hK depth
  let r := Q'.recipPos z hz
  let A := H (N width) (polyMul W (polyMul f f))
  let nv := normalizedVariance (N width) W f hz
  have hshift := shifted_zero f
  have hzero : normalizedMoment (N width) W
      (polyMul (shifted f 0) (shifted f 0)) hz ≈
      normalizedMoment (N width) W (polyMul f f) hz := by
    unfold normalizedMoment
    exact Q'.mul_eqv_congr_right _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.refl W).mul (hshift.mul hshift)))
  have hvar : nv ≤ A*r :=
    Q'.le_trans' _ _ _
      (normalized_variance_le_shifted
        (marginalCertificate hw0 hw1 K width hK depth) hf hz 0)
      (Q'.le_of_eqv hzero)
  have hraw := Q'.mul_le_mul_of_nonneg_left _ _ z hvar (Q'.le_of_lt hz)
  have hleft : oddMass w K width depth *
      oddVariance hw0 hw1 K width hK depth f ≈ z*nv :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (marginalMass_pin w K width depth).symm)
      (Q'.mul_eqv_congr_left z _ _
        (marginalVariance_pin hw0 hw1 K width hK depth f).symm)
  have hright : z*(A*r) ≈ A :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => z | 1 => A | _ => r))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left A _ _ (Q'.mul_recipPos_eqv z hz))
        (Q'.mul_one_eqv A))
  have hmoment := oddMoment_projected_source w K width depth (polyMul f f)
    (supported_polyMul hf hf)
    (fun i hi => quaternionBlockIndependent_polyMul (hfringe i hi) (hfringe i hi))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hraw
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hright) (Q'.le_of_eqv hmoment)))

end OriginalVariance

/-- Exact identification of the signed observable square with a positive
whole-polynomial insertion in the original passive channel square. -/
theorem familyChannelObservableSquare_eq_channelSquare
    (w : Q') (K width depth : Nat) (coeff : Z4Plaq → Q')
    (qs : List Z4Plaq) :
    let f := spatialSpan width coeff qs
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let ids := familySpectatorBlocks width qs
    familyChannelObservableSquare w K width depth coeff qs ≈
      channelSquare (N width) w K ids q (polyMul f f) := by
  dsimp only
  let f := spatialSpan width coeff qs
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let ids := familySpectatorBlocks width qs
  unfold familyChannelObservableSquare channelSquare
  apply channelSum_congr
  intro c hc
  let b := channelSource ids q c.2
  exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
    (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
    (by decide) (fun | 0 => b | _ => f))

/-- The actual retained square controls the SAME original odd partition times
OWN variance. Signed and repeated faces remain inside one square; the empty
family and zero variance require no exception. -/
theorem family_channel_square_variance_credit_cleared {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) {base width : Nat} (hwidth : base < width)
    (n : Nat) (coeff : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let f := spatialSpan width coeff qs
    let l := localLower w (4*qs.length)
    let u := localUpper w (4*qs.length)
    (l*l)*(oddMass w K width (n+1) *
      oddVariance hw0 hw1 K width hK (n+1) f) ≤
      (u*u)*familyChannelObservableSquare w K width (n+1) coeff qs := by
  dsimp only
  let f := spatialSpan width coeff qs
  let q := projectedEndpointSource w K width (terminalMessage w K width (n+1))
  let R := projectedFamilySpectator w K width n qs
  let ids := familySpectatorBlocks width qs
  let active := familyObservableBlocks width qs
  let e := polyMul f f
  let l := localLower w (4*qs.length)
  let u := localUpper w (4*qs.length)
  let M := channelMass (N width) w K ids R
  let B := M * H (N width) e
  let V := oddMass w K width (n+1) * oddVariance hw0 hw1 K width hK (n+1) f
  let S := familyChannelObservableSquare w K width (n+1) coeff qs
  have hids := familySpectatorBlocks_lt width qs
  have hnd := familySpectatorBlocks_nodup width qs
  have hf := spatialSpan_supported width coeff qs
  have he := supported_polyMul hf hf
  have hq : SupportedQuaternionBlocks (N width) q := by
    dsimp only [q, projectedEndpointSource]
    exact familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width (n+1)))
  have hR : SupportedQuaternionBlocks (N width) R :=
    familyProject_supported _ (familySpectator_supported w K width n qs)
  have CQ := projectedSource_certificate hw0 hw1 K width hK n
  have CR := familyProject_certificate (N width) (fringeBlocks width) (fringeBlocks_lt width)
    (familySpectator_supported w K width n qs)
    (familySpectator_certificate hw0 hw1 K width hK n qs)
  have hRi := projectedFamilySpectator_outside_passive hwidth qs hqs w K n
  have hfi : ∀ i, i ∈ ids → QuaternionBlockIndependent i f :=
    fun i hi => spatialSpan_familySpectator_independent width coeff qs i hi
  have hei : ∀ i, i ∈ ids → QuaternionBlockIndependent i e :=
    fun i hi => quaternionBlockIndependent_polyMul (hfi i hi) (hfi i hi)
  have hM : (0 : Q') ≤ M :=
    channelMass_nonnegative (N width) (Q'.le_of_lt hw0) K ids hids R hR
  have hl : (0 : Q') ≤ l := Q'.le_of_lt (localLower_positive hw0 hw1 _)
  have hu : (0 : Q') ≤ u := Q'.le_of_lt (localUpper_positive hw0 hw1 _)
  have hlowMono := productChannels_familyProject_positiveWeighted_square_mono
    (N width) hw0 hw1 K hK ids hnd hids (polySmul l R) q e
    (polySmul_supported hR l) hq he (CR.smul l hl) CQ
    (Certificate.square f hf)
    (projectedFamily_lowerCertificate hw0 hw1 K width hK n qs) hei
  change channelSquare (N width) w K ids (polySmul l R) e ≤
    channelSquare (N width) w K ids q e at hlowMono
  have hlowScale := productChannels_familyProject_weighted_square_smul
    (N width) w K ids hnd hids R e hR he hei l
  change channelSquare (N width) w K ids (polySmul l R) e ≈
    (l*l)*channelSquare (N width) w K ids R e at hlowScale
  have hfactor := channelSquare_factor (N width) w K ids hids R e hR he hRi
  have hSq := familyChannelObservableSquare_eq_channelSquare w K width (n+1) coeff qs
  have hlow : (l*l)*B ≤ S :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left (l*l) _ _ hfactor.symm))
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hlowScale)
        (Q'.le_trans' _ _ _ hlowMono (Q'.ge_of_eqv hSq)))
  have hvar := original_variance_le_projected_square hw0 hw1 K width hK
    (n+1) f hf (spatialSpan_fringe_independent_after_padding hwidth coeff qs hqs)
  have hsource := sourceMoment_square_mono hw0 hw1 K hK (List.range (N width))
    (fun i hi => List.mem_range.mp hi) q (polySmul u R) f
    hq (polySmul_supported hR u) hf CQ (CR.smul u hu)
    (projectedFamily_upperCertificate hw0 hw1 K width hK n qs)
  have hscale := sourceMoment_smul (N width) w K (List.range (N width)) R e u
  have hB := spectator_sourceMoment_factor (N width) w K active ids
    (familyObservableBlocks_lt width qs) hids (familySpectator_not_observable width qs)
    (familySpectator_observable_cover width qs) R e hR he hRi hei
  have hupper : V ≤ (u*u)*B :=
    Q'.le_trans' _ _ _ hvar
      (Q'.le_trans' _ _ _ hsource
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hscale)
          (Q'.le_of_eqv (Q'.mul_eqv_congr_left (u*u) _ _ hB))))
  have hV := Q'.mul_le_mul_of_nonneg_left _ _ (l*l) hupper
    (SumOfSquares.q_mul_self_nonneg l)
  have hS := Q'.mul_le_mul_of_nonneg_left _ _ (u*u) hlow
    (SumOfSquares.q_mul_self_nonneg u)
  have hmiddle : (l*l)*((u*u)*B) ≈ (u*u)*((l*l)*B) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => l*l | 1 => u*u | _ => B)
  exact Q'.le_trans' _ _ _ hV
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmiddle) hS)

/-- Positive finite credit at fixed nome and complete signed-family footprint.
The coefficient is computed from the actual local source band, with no
uniformity assertion as the nome or footprint changes. -/
def channelObservableSquareVarianceCredit {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (size : Nat) : Q' :=
  let l := localLower w (4*size)
  let u := localUpper w (4*size)
  (l*l)*Q'.recipPos (u*u)
    (Q'.mul_pos (localUpper_positive hw0 hw1 _)
      (localUpper_positive hw0 hw1 _))

theorem channelObservableSquareVarianceCredit_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (size : Nat) :
    (0 : Q') < channelObservableSquareVarianceCredit hw0 hw1 size :=
  Q'.mul_pos
    (Q'.mul_pos (localLower_positive hw0 hw1 _)
      (localLower_positive hw0 hw1 _))
    (Q'.recipPos_pos _ _)

/-- The retained observable square pays an explicit portion of the same
original partition times OWN variance. -/
theorem family_channel_observableSquare_variance_credit {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) {base width : Nat} (hwidth : base < width)
    (n : Nat) (coeff : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    channelObservableSquareVarianceCredit hw0 hw1 qs.length *
      (oddMass w K width (n+1) *
        oddVariance hw0 hw1 K width hK (n+1) (spatialSpan width coeff qs)) ≤
      familyChannelObservableSquare w K width (n+1) coeff qs := by
  let l := localLower w (4*qs.length)
  let u := localUpper w (4*qs.length)
  let U := u*u
  have hU : (0 : Q') < U :=
    Q'.mul_pos (localUpper_positive hw0 hw1 _)
      (localUpper_positive hw0 hw1 _)
  let a := Q'.recipPos U hU
  let V := oddMass w K width (n+1) *
    oddVariance hw0 hw1 K width hK (n+1) (spatialSpan width coeff qs)
  let S := familyChannelObservableSquare w K width (n+1) coeff qs
  have h := Q'.mul_le_mul_of_nonneg_right _ _ a
    (family_channel_square_variance_credit_cleared
      hw0 hw1 K hK hwidth n coeff qs hqs)
    (Q'.le_of_lt (Q'.recipPos_pos U hU))
  have hleft : ((l*l)*V)*a ≈ channelObservableSquareVarianceCredit hw0 hw1 qs.length*V :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun | 0 => l*l | 1 => V | _ => a)
  have hright : (U*S)*a ≈ S := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun | 0 => U | 1 => S | _ => a))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ S (Q'.mul_recipPos_eqv U hU))
      (Q'.one_mul_eqv S))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright))

/-- Keeping one actual source leg unchanged improves the squared band to a
linear band. The mixed spectator pairing is full-heat only because the
spectator is independent of every active block. -/
theorem family_channel_square_linear_variance_credit_cleared {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) {base width : Nat} (hwidth : base < width)
    (n : Nat) (coeff : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let f := spatialSpan width coeff qs
    let l := localLower w (4*qs.length)
    let u := localUpper w (4*qs.length)
    l*(oddMass w K width (n+1) *
      oddVariance hw0 hw1 K width hK (n+1) f) ≤
      u*familyChannelObservableSquare w K width (n+1) coeff qs := by
  dsimp only
  let f := spatialSpan width coeff qs
  let q := projectedEndpointSource w K width (terminalMessage w K width (n+1))
  let R := projectedFamilySpectator w K width n qs
  let ids := familySpectatorBlocks width qs
  let active := familyObservableBlocks width qs
  let l := localLower w (4*qs.length)
  let u := localUpper w (4*qs.length)
  have hf := spatialSpan_supported width coeff qs
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width (n+1)))
  have hR : SupportedQuaternionBlocks (N width) R :=
    familyProject_supported _ (familySpectator_supported w K width n qs)
  have hl : (0 : Q') ≤ l := Q'.le_of_lt (localLower_positive hw0 hw1 _)
  have hu : (0 : Q') ≤ u := Q'.le_of_lt (localUpper_positive hw0 hw1 _)
  have hband := channelSquare_sourceMoment_linear_band hw0 hw1 K hK active ids
    (familySpectatorBlocks_nodup width qs) (familySpectatorBlocks_lt width qs)
    (familySpectator_observable_cover width qs) q R f hq hR hf
    (projectedSource_certificate hw0 hw1 K width hK n) l u hl hu
    (projectedFamily_lowerCertificate hw0 hw1 K width hK n qs)
    (projectedFamily_upperCertificate hw0 hw1 K width hK n qs)
    (projectedFamilySpectator_outside_passive hwidth qs hqs w K n)
    (fun i hi => spatialSpan_familySpectator_independent width coeff qs i hi)
  have hvar := Q'.mul_le_mul_of_nonneg_left _ _ l
    (original_variance_le_projected_square hw0 hw1 K width hK (n+1) f hf
      (spatialSpan_fringe_independent_after_padding hwidth coeff qs hqs)) hl
  exact Q'.le_trans' _ _ _ hvar
    (Q'.le_trans' _ _ _ hband
      (Q'.ge_of_eqv (Q'.mul_eqv_congr_left u _ _
        (familyChannelObservableSquare_eq_channelSquare w K width (n+1) coeff qs))))

/-- Linear credit computed from the SAME nome and complete family size.
Only the positive scalar upper band is inverted, not an interacting moment. -/
def channelObservableSquareLinearVarianceCredit {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (size : Nat) : Q' :=
  localLower w (4*size) * Q'.recipPos (localUpper w (4*size))
    (localUpper_positive hw0 hw1 _)

theorem channelObservableSquareLinearVarianceCredit_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (size : Nat) :
    (0 : Q') < channelObservableSquareLinearVarianceCredit hw0 hw1 size :=
  Q'.mul_pos (localLower_positive hw0 hw1 _) (Q'.recipPos_pos _ _)

/-- The sharper linear band pays the actual retained square against OWN
variance, including signed/repeated families and zero variance. -/
theorem family_channel_observableSquare_linear_variance_credit {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) {base width : Nat} (hwidth : base < width)
    (n : Nat) (coeff : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    channelObservableSquareLinearVarianceCredit hw0 hw1 qs.length *
      (oddMass w K width (n+1) *
        oddVariance hw0 hw1 K width hK (n+1) (spatialSpan width coeff qs)) ≤
      familyChannelObservableSquare w K width (n+1) coeff qs := by
  let l := localLower w (4*qs.length)
  let u := localUpper w (4*qs.length)
  have hu : (0 : Q') < u := localUpper_positive hw0 hw1 _
  let a := Q'.recipPos u hu
  let V := oddMass w K width (n+1) *
    oddVariance hw0 hw1 K width hK (n+1) (spatialSpan width coeff qs)
  let S := familyChannelObservableSquare w K width (n+1) coeff qs
  have h := Q'.mul_le_mul_of_nonneg_right _ _ a
    (family_channel_square_linear_variance_credit_cleared
      hw0 hw1 K hK hwidth n coeff qs hqs)
    (Q'.le_of_lt (Q'.recipPos_pos u hu))
  have hleft : (l*V)*a ≈ channelObservableSquareLinearVarianceCredit hw0 hw1 qs.length*V :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun | 0 => l | 1 => V | _ => a)
  have hright : (u*S)*a ≈ S := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun | 0 => u | 1 => S | _ => a))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ S (Q'.mul_recipPos_eqv u hu))
      (Q'.one_mul_eqv S))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright))

private theorem one_le_pow (r : Q') (hr : (1 : Q') ≤ r) :
    ∀ k : Nat, (1 : Q') ≤ r^k
  | 0 => Q'.le_refl' _
  | k+1 => by
      rw [Q'.pow_succ]
      have hr0 : (0 : Q') ≤ r := Q'.le_trans' _ _ _ Q'.zero_le_one hr
      have hm := Q'.mul_le_mul_of_nonneg_right _ _ _ hr (Q'.pow_nonneg r hr0 k)
      exact Q'.le_trans' _ _ _ (one_le_pow r hr k)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _).symm) hm)

/-- The computed linear credit is at least the previously constructed
squared credit. The nome and family-size dependence remain explicit. -/
theorem channelObservableSquareVarianceCredit_le_linear {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (size : Nat) :
    channelObservableSquareVarianceCredit hw0 hw1 size ≤
      channelObservableSquareLinearVarianceCredit hw0 hw1 size := by
  let l := localLower w (4*size)
  let u := localUpper w (4*size)
  let U := u*u
  have hl0 : (0 : Q') ≤ l := Q'.le_of_lt (localLower_positive hw0 hw1 _)
  have hu : (0 : Q') < u := localUpper_positive hw0 hw1 _
  have hU : (0 : Q') < U := Q'.mul_pos hu hu
  have hl1 : l ≤ (1 : Q') := HKPos.pow_le_one
    (Q'.le_of_lt (BF4ExactSlabRetainedHeatHeadComparison.headFloor_positive hw0 hw1))
    (Q'.le_trans' _ _ _
      (BF4ExactSlabSharedWindowFloorBound.headFloor_le_oneThirtySecond hw0 hw1) (by decide)) _
  have hu1 : (1 : Q') ≤ u := one_le_pow _
    (BF4ExactSlabStarRateObstruction.prefixCap_ge_one hw0 hw1) _
  have hlu : l ≤ u := Q'.le_trans' _ _ _ hl1 hu1
  let old := channelObservableSquareVarianceCredit hw0 hw1 size
  let new := channelObservableSquareLinearVarianceCredit hw0 hw1 size
  have hold : old*U ≈ l*l :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (l*l) _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv U hU)))
        (Q'.mul_one_eqv _))
  have hnew : new*U ≈ l*u := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 2) (.var 1)))
      (by decide) (fun | 0 => l | 1 => Q'.recipPos u hu | _ => u))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (l*u) _ _ (Q'.mul_recipPos_eqv u hu))
      (Q'.mul_one_eqv _))
  apply Q'.le_of_mul_le_mul_left (c := U) _ hU
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv U old))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hold)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ l hlu hl0)
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hnew)
          (Q'.le_of_eqv (Q'.mul_comm_eqv new U)))))

#print axioms original_variance_le_projected_square
#print axioms familyChannelObservableSquare_eq_channelSquare
#print axioms family_channel_square_variance_credit_cleared
#print axioms channelObservableSquareVarianceCredit
#print axioms channelObservableSquareVarianceCredit_positive
#print axioms family_channel_observableSquare_variance_credit
#print axioms family_channel_square_linear_variance_credit_cleared
#print axioms channelObservableSquareLinearVarianceCredit
#print axioms channelObservableSquareLinearVarianceCredit_positive
#print axioms family_channel_observableSquare_linear_variance_credit
#print axioms channelObservableSquareVarianceCredit_le_linear

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelSquareCredit
