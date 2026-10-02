/-
# Active-only Sobolev error in the ORIGINAL signed family channels

The passive Gram expansion remains exact.  Its channelwise cubic Sobolev
moments and omitted-mode Haar norms contract to one active-footprint budget.
The signed curvature, negative observable square, original source, partition,
and OWN variance are unchanged.  This gives no scaling-smallness assertion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelRetainedSquare
import YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelSobolev

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelVarianceBound
  (familyChannelFirstOrder family_channel_firstOrder_variance_bound
    channelFirstOrderVarianceConstant)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelTaylorVariance
  (familyChannelTaylorDebt familyChannelFirstOrder_eq_angular
    padded_family_channel_energy_taylor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelRetainedSquare
  (familyChannelCurvature familyChannelObservableSquare)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir (spatialSpan_casimir)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
  (channelSource_supported channelSum_congr channelSum_smul)
open YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairRemainder)
open YMGap.Continuum.SU2QuaternionCyclicSobolevProjection
  (sourceSobolevErrorBudget)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
  (weightedAngularEnergy)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n
attribute [local irreducible] baseLinks terminalMessage

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private theorem channelSum_neg (value : RatPoly → Q') (cs : List GramChannel) :
    channelSum cs (fun z => -(value z)) ≈ -(channelSum cs value) :=
  Q'.eqv_trans _ _ _
    (channelSum_congr _ (fun z => (-1)*value z) cs (fun z _ =>
      poly_identity_of_normal_eq (.neg (.var 0))
        (.mul (.const (-1)) (.var 0)) (by decide) (fun _ => value z.2)))
    (Q'.eqv_trans _ _ _ (channelSum_smul value (-1) cs)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
        (.neg (.var 0)) (by decide) (fun _ => channelSum cs value)))

private theorem channel_budget_sum (cs : List GramChannel) (t : Q')
    (angular curvature square error : RatPoly → Q') :
    channelSum cs (fun z => t*((angular z-curvature z)-48*square z)+error z) ≈
      t*((channelSum cs angular-channelSum cs curvature)-
        48*channelSum cs square)+channelSum cs error := by
  have hminus (u v : RatPoly → Q') :
      channelSum cs (fun z => u z-v z) ≈
        channelSum cs u-channelSum cs v := by
    exact Q'.eqv_trans _ _ _ (channelSum_add u (fun z => -(v z)) cs)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (channelSum_neg v cs))
  have h48 : channelSum cs (fun z => 48*square z) ≈
      48*channelSum cs square := channelSum_smul square 48 cs
  have hinner : channelSum cs
      (fun z => (angular z-curvature z)-48*square z) ≈
      (channelSum cs angular-channelSum cs curvature)-48*channelSum cs square :=
    Q'.eqv_trans _ _ _
      (hminus (fun z => angular z-curvature z) (fun z => 48*square z))
      (Q'.add_eqv_congr' (hminus angular curvature)
        (Q'.neg_eqv_congr _ _ h48))
  exact Q'.eqv_trans _ _ _
    (channelSum_add (fun z => t*((angular z-curvature z)-48*square z)) error cs)
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (channelSum_smul _ t cs)
        (Q'.mul_eqv_congr_left t _ _ hinner))
      (Q'.eqv_refl _))

/-- The computed cubic third moments and Haar omitted norms are paid only on
the original active footprint.  No coefficient or scaling rate is asserted. -/
def familyActiveSobolevErrorBudget (w : Q') (K width depth : Nat)
    (coeff : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  activeSourceSobolevErrorBudget (N width-1) (familyObservableBlocks width qs)
    w K (projectedEndpointSource w K width (terminalMessage w K width depth))
    (spatialSpan width coeff qs)

/-- The original signed passive-channel debt retains the negative 48-square
and signed curvature; only its computed error budget is contracted. -/
theorem familyChannelTaylorDebt_le_activeSobolev_retained {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    {base width : Nat} (hwidth : base < width) (depth : Nat)
    (coeff : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let t := HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
    familyChannelTaylorDebt w K width depth coeff qs ≤
      t*((familyChannelFirstOrder w K width depth coeff qs -
        familyChannelCurvature w K width depth coeff qs) -
        48*familyChannelObservableSquare w K width depth coeff qs) +
      familyActiveSobolevErrorBudget w K width depth coeff qs := by
  dsimp only
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := spatialSpan width coeff qs
  let ids := familySpectatorBlocks width qs
  let active := familyObservableBlocks width qs
  let cs := productChannels (N width) w K ids
  let b := fun z => channelSource ids q z
  let ang := fun z => weightedAngularEnergy (N width-1) (b z) f
  let curv := fun z => H (N width) (polyMul (polyMul (b z) (b z))
    (activeCasimirPolynomial (List.range (N width))
      (activeGamma (List.range (N width)) f f)))
  let sq := fun z => H (N width) (polyMul (polyMul (b z) f) (polyMul (b z) f))
  let err := fun z => sourceSobolevErrorBudget (N width-1) w K (b z) f
  let t := HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
  have hn : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth))
  have hf := spatialSpan_supported width coeff qs
  have hind : ∀ i, i ∈ ids → QuaternionBlockIndependent i f :=
    fun i hi => spatialSpan_familySpectator_independent width coeff qs i hi
  have hCf := spatialSpan_casimir width coeff qs
    (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
  have hle : channelSum cs (fun z =>
      pairRemainder (N width-1) w K (b z)
          (polyMul (b z) (polyMul f f)) +
        -(pairRemainder (N width-1) w K (polyMul (b z) f) (polyMul (b z) f))) ≤
      channelSum cs (fun z => t*((ang z-curv z)-48*sq z)+err z) := by
    apply channelSum_le
    · exact productChannels_nonnegative (N width) (Q'.le_of_lt hw0) K ids
    · intro z hz
      have hb := channelSource_supported (N width) w K ids
        (familySpectatorBlocks_lt width qs) hq z hz
      have hb' : SupportedQuaternionBlocks (N width-1+1) (b z.2) := by
        simpa only [hn] using hb
      have hf' : SupportedQuaternionBlocks (N width-1+1) f := by
        simpa only [hn] using hf
      have hCf' : HaarCarrierEqv (N width-1+1)
          (activeCasimirPolynomial (List.range (N width-1+1)) f)
          (polySmul 12 f) := by simpa only [hn] using hCf
      have hR := sourceRemainder_le_sobolev_retainedSquare (N width-1)
        (Q'.le_of_lt hw0) hw1 K (b z.2) f hb' hf' hCf'
      simpa only [hn] using hR
  have hbudget := channel_budget_sum cs t ang curv sq err
  have hfirst := familyChannelFirstOrder_eq_angular w K width depth coeff qs
  have hshape :
      t*((channelSum cs ang-channelSum cs curv)-48*channelSum cs sq)+
          channelSum cs err ≈
      t*((familyChannelFirstOrder w K width depth coeff qs-
        familyChannelCurvature w K width depth coeff qs)-
          48*familyChannelObservableSquare w K width depth coeff qs)+
          channelSum cs err := by
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left t _ _
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' hfirst.symm
            (Q'.neg_eqv_congr _ _ (Q'.eqv_refl _)))
          (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left 48 _ _ (Q'.eqv_refl _)))))
      (Q'.eqv_refl _)
  have hagg : channelSum cs err ≤
      familyActiveSobolevErrorBudget w K width depth coeff qs := by
    simpa only [hn] using channelSource_sobolevError_sum_le_active (N width-1)
      (Q'.le_of_lt hw0) hw1 K ids active
      (familySpectatorBlocks_nodup width qs)
      (by simpa only [hn] using familySpectatorBlocks_lt width qs)
      (by simpa only [hn] using familyObservableBlocks_lt width qs)
      (familySpectator_not_observable width qs)
      (by simpa only [hn] using familySpectator_observable_cover width qs)
      q f (by simpa only [hn] using hq) (by simpa only [hn] using hf)
      hind
  have hagg' :
      t*((familyChannelFirstOrder w K width depth coeff qs-
        familyChannelCurvature w K width depth coeff qs)-
          48*familyChannelObservableSquare w K width depth coeff qs)+
          channelSum cs err ≤
      t*((familyChannelFirstOrder w K width depth coeff qs-
        familyChannelCurvature w K width depth coeff qs)-
          48*familyChannelObservableSquare w K width depth coeff qs)+
          familyActiveSobolevErrorBudget w K width depth coeff qs :=
    Q'.add_le_add_left _ _ _ hagg
  exact Q'.le_trans' _ _ _ hle
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hbudget)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hshape) hagg'))

attribute [local irreducible] oddMass oddVariance familyChannelFirstOrder
  familyChannelTaylorDebt familyChannelCurvature familyChannelObservableSquare
  familyActiveSobolevErrorBudget channelFirstOrderVarianceConstant

/-- Actual finite original energy versus its OWN interacting variance.  The
active Sobolev budget, signed curvature and negative square remain explicit. -/
theorem padded_family_energy_le_activeSobolevChannelVariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) {base width : Nat} (hwidth : base < width)
    (n : Nat) (coeff : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let h := (1 : Q')-w
    let t := HalfPow.half*(h*h)
    energy w K width (terminalMessage w K width (n+1)) (spatialSpan width coeff qs) ≤
      (h+t)*(channelFirstOrderVarianceConstant hw0 hw1 qs.length *
        (oddMass w K width (n+1) *
          oddVariance hw0 hw1 K width hK (n+1) (spatialSpan width coeff qs))) +
      (t*(-familyChannelCurvature w K width (n+1) coeff qs -
        48*familyChannelObservableSquare w K width (n+1) coeff qs) +
        familyActiveSobolevErrorBudget w K width (n+1) coeff qs) := by
  dsimp only
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  let A := familyChannelFirstOrder w K width (n+1) coeff qs
  let curv := familyChannelCurvature w K width (n+1) coeff qs
  let sq := familyChannelObservableSquare w K width (n+1) coeff qs
  let err := familyActiveSobolevErrorBudget w K width (n+1) coeff qs
  let V := oddMass w K width (n+1) *
    oddVariance hw0 hw1 K width hK (n+1) (spatialSpan width coeff qs)
  let C := channelFirstOrderVarianceConstant hw0 hw1 qs.length
  have hh0 : (0 : Q') ≤ h := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have ht0 : (0 : Q') ≤ t := Q'.mul_nonneg _ _ HalfPow.half_nonneg
    (Q'.mul_nonneg _ _ hh0 hh0)
  have hlead : (0 : Q') ≤ h+t := Q'.zero_le_add _ _ hh0 ht0
  have hD := familyChannelTaylorDebt_le_activeSobolev_retained
    hw0 hw1 K hwidth (n+1) coeff qs hqs
  have hE := Q'.add_le_add_left (h*A) _ _ hD
  have hshape : h*A+(t*((A-curv)-48*sq)+err) ≈
      (h+t)*A+(t*(-curv-48*sq)+err) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2))
        (.add (.mul (.var 1)
          (.add (.add (.var 2) (.neg (.var 3))) (.neg (.mul (.const 48) (.var 4)))))
          (.var 5)))
      (.add (.mul (.add (.var 0) (.var 1)) (.var 2))
        (.add (.mul (.var 1)
          (.add (.neg (.var 3)) (.neg (.mul (.const 48) (.var 4))))) (.var 5)))
      (by decide) (fun | 0 => h | 1 => t | 2 => A | 3 => curv | 4 => sq | _ => err)
  have hA := Q'.mul_le_mul_of_nonneg_left _ _ (h+t)
    (family_channel_firstOrder_variance_bound hw0 hw1 K hK hwidth n coeff qs hqs) hlead
  have hbudget : (h+t)*A+(t*(-curv-48*sq)+err) ≤
      (h+t)*(C*V)+(t*(-curv-48*sq)+err) :=
    Q'.add_le_add_right _ _ (t*(-curv-48*sq)+err) hA
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (padded_family_channel_energy_taylor w K hwidth (n+1) coeff qs hqs))
    (Q'.le_trans' _ _ _ hE (Q'.le_trans' _ _ _ (Q'.le_of_eqv hshape) hbudget))

#print axioms familyActiveSobolevErrorBudget
#print axioms familyChannelTaylorDebt_le_activeSobolev_retained
#print axioms padded_family_energy_le_activeSobolevChannelVariance

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelSobolev
