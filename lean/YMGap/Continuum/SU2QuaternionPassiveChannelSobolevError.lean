/-
# Active cubic norms in the actual spectator channel error

Expand the ORIGINAL source energy into its computed passive Gram channels
before applying the cubic bound. Third moments contract with coefficient one
to ACTIVE derivatives of the original source; omitted Haar norms contract
with coefficient one as well. No global cubic weight is replaced by an
active weight. The signed Casimir-12 remainder still retains its original
negative square, for arbitrary supported signed channel sources.

These are raw active Sobolev costs, not interacting variance or a scaling rate.
-/

import YMGap.Continuum.SU2QuaternionPassiveChannelCasimirCube
import YMGap.Continuum.SU2QuaternionCyclicSobolevProjection
import YMGap.Continuum.SU2QuaternionSecondOrderRetainedSquare
import YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization

namespace YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionFamilyHeatGramBessel
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
  (channelSum_congr channelSum_smul channelSource_supported)
open YMGap.Continuum.SU2QuaternionPassiveChannelCasimirCube
open YMGap.Continuum.SU2QuaternionCyclicCasimirCube
open YMGap.Continuum.SU2QuaternionCyclicSobolevProjection
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder
open YMGap.Continuum.SU2QuaternionCyclicOmittedNorm
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionSecondOrderRetainedSquare
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

theorem channelSum_add (left right : RatPoly → Q') : ∀ cs : List GramChannel,
    channelSum cs (fun z => left z+right z) ≈ channelSum cs left+channelSum cs right
  | [] => by change (0 : Q') ≈ 0+0; decide
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_add_eqv _ _ _) (channelSum_add left right cs))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3))) (by decide)
        (fun | 0 => c.1*left c.2 | 1 => c.1*right c.2
             | 2 => channelSum cs left | _ => channelSum cs right))

theorem channelSum_le (left right : RatPoly → Q') : ∀ cs : List GramChannel,
    (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
    (∀ c, c ∈ cs → left c.2 ≤ right c.2) → channelSum cs left ≤ channelSum cs right
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, h => Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (h c List.mem_cons_self) (hw c List.mem_cons_self))
      (channelSum_le left right cs (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_triple (cs : List GramChannel) (k : Q')
    (a b c : RatPoly → Q') :
    channelSum cs (fun z => k*(HalfPow.half*(a z+b z)+c z)) ≈
      k*(HalfPow.half*(channelSum cs a+channelSum cs b)+channelSum cs c) :=
  Q'.eqv_trans _ _ _ (channelSum_smul _ k cs)
    (Q'.mul_eqv_congr_left k _ _ (Q'.eqv_trans _ _ _
      (channelSum_add (fun z => HalfPow.half*(a z+b z)) c cs)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (channelSum_smul _ HalfPow.half cs)
          (Q'.mul_eqv_congr_left _ _ _ (channelSum_add a b cs))) (Q'.eqv_refl _))))

/-- Spectator-independent insertions stay inside the coefficient-one raw norm cap. -/
theorem channelSource_mul_haarSquare_sum_le (n : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (K : Nat) (passive : List Nat)
    (hnd : passive.Nodup) (hpassive : ∀ i, i ∈ passive → i < n)
    (q r : RatPoly) (hq : SupportedQuaternionBlocks n q)
    (hr : SupportedQuaternionBlocks n r)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i r) :
    channelSum (productChannels n w K passive) (fun c =>
      H n (polyMul (polyMul (channelSource passive q c) r)
        (polyMul (channelSource passive q c) r))) ≤
      H n (polyMul (polyMul q r) (polyMul q r)) := by
  have he : channelSum (productChannels n w K passive) (fun c =>
      H n (polyMul (channelSource passive (polyMul q r) c)
        (channelSource passive (polyMul q r) c))) ≈
      channelSum (productChannels n w K passive) (fun c =>
        H n (polyMul (polyMul (channelSource passive q c) r)
          (polyMul (channelSource passive q c) r))) :=
    channelSum_congr _ _ (productChannels n w K passive) (fun c _ =>
    haar_of_coeff ((channelSource_mul_pullback passive q r c.2 hind).mul
      (channelSource_mul_pullback passive q r c.2 hind)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (productChannels_familyProject_square_le n hw0 hw1 K passive hnd hpassive
      (polyMul q r) (supported_polyMul hq hr))

/-- No passive derivative or channel-count factor appears in this original-source cost. -/
def activeSourceSobolevErrorBudget (tail : Nat) (active : List Nat)
    (w : Q') (K : Nat) (q f : RatPoly) : Q' :=
  (sixth*((((1 : Q')-w)*((1 : Q')-w))*((1 : Q')-w)))*
    (HalfPow.half*(activeThirdMoment (tail+1) active q+
      activeThirdMoment (tail+1) active (polyMul q (polyMul f f)))+
      activeThirdMoment (tail+1) active (polyMul q f)) +
    omittedRate w K*(HalfPow.half*(H (tail+1) (polyMul q q)+
      H (tail+1) (polyMul (polyMul q (polyMul f f)) (polyMul q (polyMul f f))))+
      H (tail+1) (polyMul (polyMul q f) (polyMul q f)))

/-- The complete actual channel error is bounded AFTER exact energy decomposition.
The cubic moment and Haar contractions both have coefficient one. -/
theorem channelSource_sobolevError_sum_le_active (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (passive active : List Nat) (hnd : passive.Nodup)
    (hpassive : ∀ i, i ∈ passive → i < tail+1)
    (hactive : ∀ i, i ∈ active → i < tail+1)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive++active).Perm (List.range (tail+1)))
    (q f : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i f) :
    channelSum (productChannels (tail+1) w K passive) (fun c =>
      sourceSobolevErrorBudget tail w K (channelSource passive q c) f) ≤
      activeSourceSobolevErrorBudget tail active w K q f := by
  let cs := productChannels (tail+1) w K passive
  let b := fun c => channelSource passive q c
  let c3 := sixth*((((1 : Q')-w)*((1 : Q')-w))*((1 : Q')-w))
  let rho := omittedRate w K
  let a := fun z => thirdMoment tail (b z)
  let d := fun z => thirdMoment tail (polyMul (b z) (polyMul f f))
  let e := fun z => thirdMoment tail (polyMul (b z) f)
  let u := fun z => H (tail+1) (polyMul (b z) (b z))
  let v := fun z => H (tail+1)
    (polyMul (polyMul (b z) (polyMul f f)) (polyMul (b z) (polyMul f f)))
  let s := fun z => H (tail+1) (polyMul (polyMul (b z) f) (polyMul (b z) f))
  have ha := channelSource_thirdMoment_le_activeThirdMoment tail hw0 (Q'.le_of_lt hw1)
    K passive active hnd hpassive hactive hnot hcover q hq
  have hd := channelSource_mul_thirdMoment_le_activeThirdMoment tail hw0 (Q'.le_of_lt hw1)
    K passive active hnd hpassive hactive hnot hcover q (polyMul f f) hq
    (supported_polyMul hf hf)
    (fun i hi => quaternionBlockIndependent_polyMul (hind i hi) (hind i hi))
  have he := channelSource_mul_thirdMoment_le_activeThirdMoment tail hw0 (Q'.le_of_lt hw1)
    K passive active hnd hpassive hactive hnot hcover q f hq hf hind
  have hu := productChannels_familyProject_square_le (tail+1) hw0 (Q'.le_of_lt hw1)
    K passive hnd hpassive q hq
  have hv := channelSource_mul_haarSquare_sum_le (tail+1) hw0 (Q'.le_of_lt hw1)
    K passive hnd hpassive q (polyMul f f) hq (supported_polyMul hf hf)
    (fun i hi => quaternionBlockIndependent_polyMul (hind i hi) (hind i hi))
  have hs := channelSource_mul_haarSquare_sum_le (tail+1) hw0 (Q'.le_of_lt hw1)
    K passive hnd hpassive q f hq hf hind
  have hh : (0 : Q') ≤ (1 : Q')-w := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have hc3 : (0 : Q') ≤ c3 := Q'.mul_nonneg _ _ sixth_nonnegative
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hh hh) hh)
  have hrho : (0 : Q') ≤ rho := RGTransport.qpow_nonneg w hw0 _
  have hthird := Q'.mul_le_mul_of_nonneg_left _ _ c3
    (Q'.add_le_add (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      (Q'.add_le_add ha hd) HalfPow.half_nonneg) he) hc3
  have hnorm := Q'.mul_le_mul_of_nonneg_left _ _ rho
    (Q'.add_le_add (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      (Q'.add_le_add hu hv) HalfPow.half_nonneg) hs) hrho
  have hleft : channelSum cs (fun z => sourceSobolevErrorBudget tail w K (b z) f) ≈
      c3*(HalfPow.half*(channelSum cs a+channelSum cs d)+channelSum cs e)+
        rho*(HalfPow.half*(channelSum cs u+channelSum cs v)+channelSum cs s) :=
    Q'.eqv_trans _ _ _ (channelSum_add _ _ cs)
      (Q'.add_eqv_congr' (channelSum_triple cs c3 a d e) (channelSum_triple cs rho u v s))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) (Q'.add_le_add hthird hnorm)

/-- The original signed remainder retains its Casimir-12 negative square.
No source positivity or separate channel centering is assumed. -/
theorem sourceRemainder_le_sobolev_retainedSquare (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hCf : HaarCarrierEqv (tail+1)
      (activeCasimirPolynomial (List.range (tail+1)) f) (polySmul 12 f)) :
    pairRemainder tail w K q (polyMul q (polyMul f f))-
      pairRemainder tail w K (polyMul q f) (polyMul q f) ≤
      (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*
        ((weightedAngularEnergy tail q f-
          H (tail+1) (polyMul (polyMul q q)
            (activeCasimirPolynomial (List.range (tail+1))
              (activeGamma (List.range (tail+1)) f f))))-
          48*H (tail+1) (polyMul (polyMul q f) (polyMul q f)))+
        sourceSobolevErrorBudget tail w K q f := by
  let t := HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
  let curv := H (tail+1) (polyMul (polyMul q q)
    (activeCasimirPolynomial (List.range (tail+1)) (activeGamma (List.range (tail+1)) f f)))
  let sq := H (tail+1) (polyMul (polyMul q f) (polyMul q f))
  let ang := weightedAngularEnergy tail q f
  have ht : (0 : Q') ≤ t := Q'.mul_nonneg _ _ HalfPow.half_nonneg
    (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
      (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)))
  have hquad := Q'.mul_le_mul_of_nonneg_left _ _ t
    (Q'.add_le_add (sourceSecondMoment_le_retainedSquare tail q f hq hf hCf)
      (Q'.le_of_eqv (sourceFirstOrder_eq_weightedAngularEnergy tail q f hq hf))) ht
  have herr := sourceError_le_sobolev tail hw0 hw1 K q f hq hf
  have hgroup : t*(sourceSecondMoment tail q f+
      SU2QuaternionProductHeatSourceTaylor.sourceFirstOrder tail q f)+
      sourceCubic tail w q f-sourceOmitted tail w K q f ≈
      t*(sourceSecondMoment tail q f+
        SU2QuaternionProductHeatSourceTaylor.sourceFirstOrder tail q f)+
        (sourceCubic tail w q f-sourceOmitted tail w K q f) := Q'.add_assoc_eqv _ _ _
  have hright : t*((-curv-48*sq)+ang)+sourceSobolevErrorBudget tail w K q f ≈
      t*((ang-curv)-48*sq)+sourceSobolevErrorBudget tail w K q f :=
    Q'.add_eqv_congr' (Q'.mul_eqv_congr_left t _ _ (poly_identity_of_normal_eq
      (.add (.add (.neg (.var 1)) (.neg (.mul (.const 48) (.var 2)))) (.var 0))
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.mul (.const 48) (.var 2))))
      (by decide) (fun | 0 => ang | 1 => curv | _ => sq))) (Q'.eqv_refl _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (sourceRemainder_secondOrder tail w K q f) hgroup))
    (Q'.le_trans' _ _ _ (Q'.add_le_add hquad herr) (Q'.le_of_eqv hright))

#print axioms channelSum_add
#print axioms channelSum_le
#print axioms channelSource_mul_haarSquare_sum_le
#print axioms activeSourceSobolevErrorBudget
#print axioms channelSource_sobolevError_sum_le_active
#print axioms sourceRemainder_le_sobolev_retainedSquare

end YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError
