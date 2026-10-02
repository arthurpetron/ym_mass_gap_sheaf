/-
# Active cubic cost with the literal observable Casimir square retained

Exact passive-channel expansion precedes every estimate. The observable need
not be a Casimir eigenvector: the negative square keeps C(f), including after
OWN centering. Raw angular and cubic costs contract with coefficient one to
the original source; signed channel curvature is retained without a sign.
This is not a normalized interacting-variance or scaling-smallness bound.
-/

import YMGap.Continuum.SU2QuaternionGeneralRetainedCasimir
import YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError
import YMGap.Continuum.SU2QuaternionPassiveChannelAngularBudget

namespace YMGap.Continuum.SU2QuaternionPassiveChannelRetainedCasimirSobolev

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder
open YMGap.Continuum.SU2QuaternionCyclicSobolevProjection
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
  (channelSum_congr channelSum_smul channelSource_supported)
open YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError
open YMGap.Continuum.SU2QuaternionPassiveChannelAngularBudget
open YMGap.Continuum.SU2QuaternionGeneralRetainedCasimir

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The actual signed curvature after the exact heat-channel expansion. -/
def channelCurvature (tail : Nat) (w : Q') (K : Nat) (passive : List Nat)
    (q f : RatPoly) : Q' :=
  channelSum (productChannels (tail+1) w K passive) (fun c =>
    let b := channelSource passive q c
    H (tail+1) (polyMul (polyMul b b)
      (activeCasimirPolynomial (List.range (tail+1))
        (activeGamma (List.range (tail+1)) f f))))

/-- The literal C(f) remains in the retained square, not an eigenvalue guess. -/
def channelCasimirSquare (tail : Nat) (w : Q') (K : Nat) (passive : List Nat)
    (q f : RatPoly) : Q' :=
  channelSum (productChannels (tail+1) w K passive) (fun c =>
    let v := polyMul (channelSource passive q c)
      (activeCasimirPolynomial (List.range (tail+1)) f)
    H (tail+1) (polyMul v v))

/-- A signed channel source requires no positivity or Casimir eigenpin. -/
theorem sourceEnergy_le_sobolev_retainedCasimir (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    let h := (1 : Q')-w
    let t := HalfPow.half*(h*h)
    sourceEnergy (tail+1) w K (List.range (tail+1)) q f ≤
      (h+t)*weightedAngularEnergy tail q f+
        (t*(-H (tail+1) (polyMul (polyMul q q)
          (activeCasimirPolynomial (List.range (tail+1))
            (activeGamma (List.range (tail+1)) f f)))-
          oneThird*H (tail+1) (polyMul
            (polyMul q (activeCasimirPolynomial (List.range (tail+1)) f))
            (polyMul q (activeCasimirPolynomial (List.range (tail+1)) f))))+
          sourceSobolevErrorBudget tail w K q f) := by
  dsimp only
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  let A := weightedAngularEnergy tail q f
  let R := H (tail+1) (polyMul (polyMul q q)
    (activeCasimirPolynomial (List.range (tail+1))
      (activeGamma (List.range (tail+1)) f f)))
  let S := H (tail+1) (polyMul
    (polyMul q (activeCasimirPolynomial (List.range (tail+1)) f))
    (polyMul q (activeCasimirPolynomial (List.range (tail+1)) f)))
  have ht : (0 : Q') ≤ t := Q'.mul_nonneg _ _ HalfPow.half_nonneg
    (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
      (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)))
  have hquad := Q'.mul_le_mul_of_nonneg_left _ _ t
    (Q'.add_le_add_right _ _ A (sourceSecondMoment_le_retainedCasimir tail q f hq hf)) ht
  have herr := sourceError_le_sobolev tail hw0 hw1 K q f hq hf
  have hgroup : h*A+(t*(sourceSecondMoment tail q f+A)+
      sourceCubic tail w q f-sourceOmitted tail w K q f) ≈
      h*A+(t*(sourceSecondMoment tail q f+A)+
        (sourceCubic tail w q f-sourceOmitted tail w K q f)) :=
    Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.add_assoc_eqv _ _ _)
  have hshape : h*A+(t*((-R-oneThird*S)+A)+sourceSobolevErrorBudget tail w K q f) ≈
      (h+t)*A+(t*(-R-oneThird*S)+sourceSobolevErrorBudget tail w K q f) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2))
        (.add (.mul (.var 1)
          (.add (.add (.neg (.var 3)) (.neg (.mul (.var 5) (.var 4)))) (.var 2))) (.var 6)))
      (.add (.mul (.add (.var 0) (.var 1)) (.var 2))
        (.add (.mul (.var 1)
          (.add (.neg (.var 3)) (.neg (.mul (.var 5) (.var 4))))) (.var 6)))
      (by decide) (fun
        | 0 => h | 1 => t | 2 => A | 3 => R | 4 => S
        | 5 => oneThird | _ => sourceSobolevErrorBudget tail w K q f)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (sourceEnergy_secondOrder tail w K q f hq hf) hgroup))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left (h*A) _ _ (Q'.add_le_add hquad herr))
      (Q'.le_of_eqv hshape))

private theorem channelSum_neg (value : RatPoly → Q') (cs : List GramChannel) :
    channelSum cs (fun z => -(value z)) ≈ -(channelSum cs value) :=
  Q'.eqv_trans _ _ _ (channelSum_congr _ (fun z => (-1)*value z) cs (fun z _ =>
    poly_identity_of_normal_eq (.neg (.var 0)) (.mul (.const (-1)) (.var 0))
      (by decide) (fun _ => value z.2)))
    (Q'.eqv_trans _ _ _ (channelSum_smul value (-1) cs)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => channelSum cs value)))

private theorem channelSum_budget (cs : List GramChannel) (h t : Q')
    (A R S E : RatPoly → Q') :
    channelSum cs (fun z => (h+t)*A z+(t*(-R z-oneThird*S z)+E z)) ≈
      (h+t)*channelSum cs A+
        (t*(-channelSum cs R-oneThird*channelSum cs S)+channelSum cs E) := by
  have hinner : channelSum cs (fun z => -R z-oneThird*S z) ≈
      -channelSum cs R-oneThird*channelSum cs S :=
    Q'.eqv_trans _ _ _ (channelSum_add (fun z => -R z) (fun z => -(oneThird*S z)) cs)
      (Q'.add_eqv_congr' (channelSum_neg R cs)
        (Q'.eqv_trans _ _ _ (channelSum_neg (fun z => oneThird*S z) cs)
          (Q'.neg_eqv_congr _ _ (channelSum_smul S oneThird cs))))
  exact Q'.eqv_trans _ _ _ (channelSum_add _ _ cs)
    (Q'.add_eqv_congr' (channelSum_smul A (h+t) cs)
      (Q'.eqv_trans _ _ _ (channelSum_add _ E cs)
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (channelSum_smul _ t cs)
            (Q'.mul_eqv_congr_left t _ _ hinner)) (Q'.eqv_refl _))))

/-- Original source energy with active-only cubic costs and literal retained
Casimir square. The raw angular term is not silently called OWN variance. -/
theorem sourceEnergy_le_activeSobolev_retainedCasimir (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (passive active : List Nat) (hnd : passive.Nodup)
    (hpassive : ∀ i, i ∈ passive → i < tail+1)
    (hactive : ∀ i, i ∈ active → i < tail+1)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive++active).Perm (List.range (tail+1)))
    (q f : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i f) :
    let h := (1 : Q')-w
    let t := HalfPow.half*(h*h)
    sourceEnergy (tail+1) w K (List.range (tail+1)) q f ≤
      (h+t)*weightedAngularEnergy tail q f+
        (t*(-channelCurvature tail w K passive q f-
          oneThird*channelCasimirSquare tail w K passive q f)+
          activeSourceSobolevErrorBudget tail active w K q f) := by
  dsimp only
  let cs := productChannels (tail+1) w K passive
  let b := fun c => channelSource passive q c
  let A := fun c => weightedAngularEnergy tail (b c) f
  let R := fun c => H (tail+1) (polyMul (polyMul (b c) (b c))
    (activeCasimirPolynomial (List.range (tail+1)) (activeGamma (List.range (tail+1)) f f)))
  let S := fun c => H (tail+1) (polyMul
    (polyMul (b c) (activeCasimirPolynomial (List.range (tail+1)) f))
    (polyMul (b c) (activeCasimirPolynomial (List.range (tail+1)) f)))
  let E := fun c => sourceSobolevErrorBudget tail w K (b c) f
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  have hraw : channelSum cs (fun c =>
      sourceEnergy (tail+1) w K (List.range (tail+1)) (b c) f) ≤
      channelSum cs (fun c => (h+t)*A c+(t*(-R c-oneThird*S c)+E c)) :=
    channelSum_le _ _ cs (productChannels_nonnegative (tail+1) hw0 K passive)
      (fun c hc => sourceEnergy_le_sobolev_retainedCasimir tail hw0 hw1 K (b c.2) f
        (channelSource_supported (tail+1) w K passive hpassive hq c hc) hf)
  have hh := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have hcoef : (0 : Q') ≤ h+t := Q'.zero_le_add _ _ hh
    (Q'.mul_nonneg _ _ HalfPow.half_nonneg (Q'.mul_nonneg _ _ hh hh))
  have hA := Q'.mul_le_mul_of_nonneg_left _ _ (h+t)
    (channelSource_weightedAngularEnergy_le tail hw0 (Q'.le_of_lt hw1)
      K passive hpassive hnd q f hq hf hind) hcoef
  have hE := channelSource_sobolevError_sum_le_active tail hw0 hw1 K passive active
    hnd hpassive hactive hnot hcover q f hq hf hind
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (sourceEnergy_projected_channels (tail+1) w K active passive hactive hpassive
      hnot hcover q f hq hf hind))
    (Q'.le_trans' _ _ _ hraw
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (channelSum_budget cs h t A R S E))
        (Q'.add_le_add hA (Q'.add_le_add (Q'.le_refl' _) hE))))

/-- The exact original channel angular sum is retained with no Bessel loss.
Only the cubic and omitted-mode errors are bounded by the active budget;
the signed curvature and literal full-Casimir square are unchanged. -/
theorem sourceEnergy_le_exactChannelAngular_activeSobolev_retainedCasimir
    (tail : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (passive active : List Nat) (hnd : passive.Nodup)
    (hpassive : ∀ i, i ∈ passive → i < tail+1)
    (hactive : ∀ i, i ∈ active → i < tail+1)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive++active).Perm (List.range (tail+1)))
    (q f : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i f) :
    let h := (1 : Q')-w
    let t := HalfPow.half*(h*h)
    sourceEnergy (tail+1) w K (List.range (tail+1)) q f ≤
      (h+t)*channelSum (productChannels (tail+1) w K passive)
        (fun c => weightedAngularEnergy tail (channelSource passive q c) f)+
        (t*(-channelCurvature tail w K passive q f-
          oneThird*channelCasimirSquare tail w K passive q f)+
          activeSourceSobolevErrorBudget tail active w K q f) := by
  dsimp only
  let cs := productChannels (tail+1) w K passive
  let b := fun c => channelSource passive q c
  let A := fun c => weightedAngularEnergy tail (b c) f
  let R := fun c => H (tail+1) (polyMul (polyMul (b c) (b c))
    (activeCasimirPolynomial (List.range (tail+1)) (activeGamma (List.range (tail+1)) f f)))
  let S := fun c => H (tail+1) (polyMul
    (polyMul (b c) (activeCasimirPolynomial (List.range (tail+1)) f))
    (polyMul (b c) (activeCasimirPolynomial (List.range (tail+1)) f)))
  let E := fun c => sourceSobolevErrorBudget tail w K (b c) f
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  have hraw : channelSum cs (fun c =>
      sourceEnergy (tail+1) w K (List.range (tail+1)) (b c) f) ≤
      channelSum cs (fun c => (h+t)*A c+(t*(-R c-oneThird*S c)+E c)) :=
    channelSum_le _ _ cs (productChannels_nonnegative (tail+1) hw0 K passive)
      (fun c hc => sourceEnergy_le_sobolev_retainedCasimir tail hw0 hw1 K (b c.2) f
        (channelSource_supported (tail+1) w K passive hpassive hq c hc) hf)
  have hE := channelSource_sobolevError_sum_le_active tail hw0 hw1 K passive active
    hnd hpassive hactive hnot hcover q f hq hf hind
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (sourceEnergy_projected_channels (tail+1) w K active passive hactive hpassive
      hnot hcover q f hq hf hind))
    (Q'.le_trans' _ _ _ hraw
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (channelSum_budget cs h t A R S E))
        (Q'.add_le_add (Q'.le_refl' _) (Q'.add_le_add (Q'.le_refl' _) hE))))

#print axioms channelCurvature
#print axioms channelCasimirSquare
#print axioms sourceEnergy_le_sobolev_retainedCasimir
#print axioms sourceEnergy_le_activeSobolev_retainedCasimir
#print axioms sourceEnergy_le_exactChannelAngular_activeSobolev_retainedCasimir

end YMGap.Continuum.SU2QuaternionPassiveChannelRetainedCasimirSobolev
