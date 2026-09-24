/-
# Computed Casimir-square contraction through passive channels

The cyclic differential sweep is first identified, at original Haar-square
level, with the active literal Casimir.  The complete spectator Gram family
then contracts that one full square with coefficient one.
-/

import YMGap.Continuum.SU2QuaternionLiteralCasimirPairing

namespace YMGap.Continuum.SU2QuaternionPassiveChannelCasimirSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionCyclicCasimirSweep
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionLiteralCasimirPairing
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (channelSum_congr left right cs
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

/-- The complete passive channel sum of the actual cyclic Casimir-sweep square
contracts to the original active-only literal Casimir square. -/
theorem channelSource_casimirSweep_square_le (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (K : Nat)
    (passive active : List Nat)
    (hnd : passive.Nodup)
    (hpassive : ∀ i, i ∈ passive → i < tail+1)
    (hactive : ∀ i, i ∈ active → i < tail+1)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive ++ active).Perm (List.range (tail+1)))
    (q : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q) :
    channelSum (productChannels (tail+1) w K passive) (fun c =>
      H (tail+1) (polyMul
        (casimirSweep tail (tail+1) (channelSource passive q c))
        (casimirSweep tail (tail+1) (channelSource passive q c)))) ≤
      H (tail+1) (polyMul (activeCasimirPolynomial active q)
        (activeCasimirPolynomial active q)) := by
  let cs := productChannels (tail+1) w K passive
  have hsource (c : GramChannel) (hc : c ∈ cs) :
      SupportedQuaternionBlocks (tail+1) (channelSource passive q c.2) :=
    familyProject_supported passive (supported_polyMul hq
      (productChannels_supported (tail+1) w K passive hpassive c hc))
  have he : channelSum cs (fun c => H (tail+1) (polyMul
      (casimirSweep tail (tail+1) (channelSource passive q c))
      (casimirSweep tail (tail+1) (channelSource passive q c)))) ≈
      channelSum cs (fun c => H (tail+1) (polyMul
        (activeCasimirPolynomial active (channelSource passive q c))
        (activeCasimirPolynomial active (channelSource passive q c)))) := by
    exact channelSum_congr _ _ cs (fun c hc =>
      casimirSweep_square_eq_active tail passive active hcover
        (channelSource passive q c.2) (hsource c hc)
        (fun i hi => channelSource_independent passive q c.2 i hi))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (channelSource_activeCasimir_square_le (tail+1) hw0 hw1 K
      passive active hnd hpassive hactive hnot q hq)

private theorem sweep_square_congr (tail : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (h : RatPolyCoeffEqv p q) :
    H (tail+1) (polyMul (casimirSweep tail (tail+1) p)
      (casimirSweep tail (tail+1) p)) ≈
    H (tail+1) (polyMul (casimirSweep tail (tail+1) q)
      (casimirSweep tail (tail+1) q)) := by
  let Sp := casimirSweep tail (tail+1) p
  let Sq := casimirSweep tail (tail+1) q
  have hs : HaarCarrierEqv (tail+1) Sp Sq :=
    casimirSweep_carrier tail (tail+1) hp hq (RatPolyCoeffEqv.haarCarrier h)
  exact Q'.eqv_trans _ _ _ (hs Sp)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm Sp Sq))
      (hs Sq))

/-- A spectator-independent insertion may be retained inside every channel
source.  The original right side is the active Casimir square of `q*r`. -/
theorem channelSource_mul_casimirSweep_square_le (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (K : Nat)
    (passive active : List Nat)
    (hnd : passive.Nodup)
    (hpassive : ∀ i, i ∈ passive → i < tail+1)
    (hactive : ∀ i, i ∈ active → i < tail+1)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive ++ active).Perm (List.range (tail+1)))
    (q r : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hr : SupportedQuaternionBlocks (tail+1) r)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i r) :
    channelSum (productChannels (tail+1) w K passive) (fun c =>
      H (tail+1) (polyMul
        (casimirSweep tail (tail+1) (polyMul (channelSource passive q c) r))
        (casimirSweep tail (tail+1) (polyMul (channelSource passive q c) r)))) ≤
      H (tail+1) (polyMul (activeCasimirPolynomial active (polyMul q r))
        (activeCasimirPolynomial active (polyMul q r))) := by
  let cs := productChannels (tail+1) w K passive
  have hpull (c : RatPoly) : RatPolyCoeffEqv
      (channelSource passive (polyMul q r) c)
      (polyMul (channelSource passive q c) r) :=
    (familyProject_congr passive (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => q | 1 => r | _ => c))).trans
      ((familyProject_mul_of_independent passive r (polyMul q c) hind).trans
        (RatPolyCoeffEqv.mul_comm _ _))
  have he : channelSum cs (fun c => H (tail+1) (polyMul
      (casimirSweep tail (tail+1) (channelSource passive (polyMul q r) c))
      (casimirSweep tail (tail+1) (channelSource passive (polyMul q r) c)))) ≈
      channelSum cs (fun c => H (tail+1) (polyMul
        (casimirSweep tail (tail+1) (polyMul (channelSource passive q c) r))
        (casimirSweep tail (tail+1) (polyMul (channelSource passive q c) r)))) := by
    exact channelSum_congr _ _ cs (fun c hc => sweep_square_congr tail
      (familyProject_supported passive (supported_polyMul (supported_polyMul hq hr)
        (productChannels_supported (tail+1) w K passive hpassive c hc)))
      (supported_polyMul (familyProject_supported passive (supported_polyMul hq
        (productChannels_supported (tail+1) w K passive hpassive c hc))) hr)
      (hpull c.2))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (channelSource_casimirSweep_square_le tail hw0 hw1 K passive active hnd
      hpassive hactive hnot hcover (polyMul q r) (supported_polyMul hq hr))

end YMGap.Continuum.SU2QuaternionPassiveChannelCasimirSquare

#print axioms YMGap.Continuum.SU2QuaternionPassiveChannelCasimirSquare.channelSource_casimirSweep_square_le
#print axioms YMGap.Continuum.SU2QuaternionPassiveChannelCasimirSquare.channelSource_mul_casimirSweep_square_le
