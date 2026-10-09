/-
# Complete signed energy of an ORIGINAL spatial family

Contract the actual retained-square inequality and ordered-pair curvature
identity BEFORE any absolute error estimate. Arbitrary signed coefficients,
repeated faces, all depths and the full passive Gram channels remain.
The exact unpaid expression is (h-19t)G-tR+C-O-tK, t=h^2/2,
where K is the literal retained-square certificate slack, nonnegative for
nonnegative channel weights. Dropping -tK gives a weaker upper bound.
This is an original finite energy bound, not a SAME-variance payment,
warmed-observable estimate, scaling theorem or physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCurvature
import YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairRemainder)
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder
open YMGap.Continuum.SU2QuaternionSecondOrderRetainedSquare
open YMGap.Continuum.SU2QuaternionSecondOrderCancellation
  (commutatorPolynomial sourceSecondMoment_curvature)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
  (channelSource_supported channelSum_congr channelSum_smul)
open YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError
  (channelSum_add channelSum_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir (spatialSpan_casimir)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelVarianceBound
  (familyChannelFirstOrder)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelTaylorVariance
  (familyChannelTaylorDebt familyChannelFirstOrder_eq_angular padded_family_channel_energy_taylor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelRetainedSquare
  (familyChannelCurvature familyChannelObservableSquare)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCurvature
  (familyChannelGradient familyChannelPairRemainder familyChannel_curvature_remainder)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks

attribute [local irreducible] baseLinks terminalMessage

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

/-- The literal signed cubic on the ORIGINAL family channels; not a budget. -/
def signedFamilyCubic (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := spatialSpan width c qs
  let ids := familySpectatorBlocks width qs
  channelSum (productChannels (N width) w K ids)
    (fun z => sourceCubic (N width-1) w (channelSource ids q z) f)

/-- The literal signed omitted form. Its NEGATIVE is the energy loss. -/
def signedFamilyOmitted (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := spatialSpan width c qs
  let ids := familySpectatorBlocks width qs
  channelSum (productChannels (N width) w K ids)
    (fun z => sourceOmitted (N width-1) w K (channelSource ids q z) f)

/- Keep the ACTUAL certificate polynomial, not just its 48-square credit. -/
private def retainedSlackValue (n : Nat) (b f : RatPoly) : Q' :=
  let active := List.range n
  let comm := commutatorPolynomial active b f
  let v := polyMul b f
  H n (polyAdd
    (polyAdd (polyMul comm comm)
      (polySmul 2 (polyMul (activeGamma active b b) (activeGamma active f f))))
    (polySmul (-48) (polyMul v v)))

private theorem retainedSlackValue_nonnegative (n : Nat) (b f : RatPoly)
    (hb : SupportedQuaternionBlocks n b) (hf : SupportedQuaternionBlocks n f)
    (hCf : HaarCarrierEqv n
      (activeCasimirPolynomial (List.range n) f) (polySmul 12 f)) :
    (0 : Q') ≤ retainedSlackValue n b f :=
  (retainedSquareCertificate (List.range n) (fun _ hi => List.mem_range.mp hi)
    b f hb hf hCf).haar_nonnegative

/-- The actual commutator/Gram certificate slack on unchanged channels. -/
def signedFamilyRetainedSlack (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := spatialSpan width c qs
  let ids := familySpectatorBlocks width qs
  channelSum (productChannels (N width) w K ids)
    (fun z => retainedSlackValue (N width) (channelSource ids q z) f)

private theorem channelSum_nonnegative (value : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ z, z ∈ cs → (0 : Q') ≤ z.1) →
      (∀ z, z ∈ cs → (0 : Q') ≤ value z.2) →
      (0 : Q') ≤ channelSum cs value
  | [], _, _ => Q'.le_refl' _
  | z::cs, hw, hv => Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (hw z List.mem_cons_self) (hv z List.mem_cons_self))
      (channelSum_nonnegative value cs
        (fun d hd => hw d (List.mem_cons_of_mem z hd))
        (fun d hd => hv d (List.mem_cons_of_mem z hd)))

/-- Produced positivity, without a source sign or inverse and including
empty/zero/repeated families and depth zero. -/
theorem signedFamilyRetainedSlack_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K width depth : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    (0 : Q') ≤ signedFamilyRetainedSlack w K width depth c qs := by
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := spatialSpan width c qs
  let ids := familySpectatorBlocks width qs
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth))
  have hf := spatialSpan_supported width c qs
  have hCf := spatialSpan_casimir width c qs hqs
  have hpositive : ∀ z, z ∈ productChannels (N width) w K ids →
      (0 : Q') ≤ retainedSlackValue (N width) (channelSource ids q z.2) f := by
    intro z hz
    have hb := channelSource_supported (N width) w K ids
      (familySpectatorBlocks_lt width qs) hq z hz
    exact retainedSlackValue_nonnegative (N width) (channelSource ids q z.2) f hb hf hCf
  exact channelSum_nonnegative
    (fun z => retainedSlackValue (N width) (channelSource ids q z) f)
    (productChannels (N width) w K ids)
    (productChannels_nonnegative (N width) hw0 K ids) hpositive

private theorem channelSum_neg (value : RatPoly → Q') (cs : List GramChannel) :
    channelSum cs (fun z => -(value z)) ≈ -(channelSum cs value) :=
  Q'.eqv_trans _ _ _ (channelSum_congr _ (fun z => (-1)*value z) cs (fun z _ =>
    poly_identity_of_normal_eq (.neg (.var 0)) (.mul (.const (-1)) (.var 0))
      (by decide) (fun _ => value z.2)))
    (Q'.eqv_trans _ _ _ (channelSum_smul value (-1) cs)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => channelSum cs value)))

private theorem channelSum_sub (a b : RatPoly → Q') (cs : List GramChannel) :
    channelSum cs (fun z => a z-b z) ≈ channelSum cs a-channelSum cs b :=
  Q'.eqv_trans _ _ _ (channelSum_add a (fun z => -(b z)) cs)
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (channelSum_neg b cs))

private theorem channel_budget (cs : List GramChannel) (t : Q')
    (A R S C O : RatPoly → Q') :
    channelSum cs (fun z => t*((A z-R z)-48*S z)+(C z-O z)) ≈
      t*((channelSum cs A-channelSum cs R)-48*channelSum cs S)+
        (channelSum cs C-channelSum cs O) := by
  have hinner := Q'.eqv_trans _ _ _
    (channelSum_sub (fun z => A z-R z) (fun z => 48*S z) cs)
    (Q'.add_eqv_congr' (channelSum_sub A R cs)
      (Q'.neg_eqv_congr _ _ (channelSum_smul S 48 cs)))
  exact Q'.eqv_trans _ _ _ (channelSum_add _ _ cs)
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (channelSum_smul _ t cs)
        (Q'.mul_eqv_congr_left t _ _ hinner))
      (channelSum_sub C O cs))

private theorem retainedSlackValue_expansion (n : Nat) (b f : RatPoly) :
    retainedSlackValue n b f ≈
      H n (polyMul (commutatorPolynomial (List.range n) b f)
        (commutatorPolynomial (List.range n) b f))+
      2*H n (polyMul (activeGamma (List.range n) b b) (activeGamma (List.range n) f f))-
      48*H n (polyMul (polyMul b f) (polyMul b f)) :=
  Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (quaternionHaar_polySmul n 2 _)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-48) _)
        (poly_identity_of_normal_eq (.mul (.const (-48)) (.var 0))
          (.neg (.mul (.const 48) (.var 0))) (by decide)
          (fun _ => H n (polyMul (polyMul b f) (polyMul b f))))))

private theorem channel_debt_exact (tail : Nat) (w : Q') (K : Nat)
    (b f : RatPoly) (hb : SupportedQuaternionBlocks (tail+1) b)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    let t := HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
    pairRemainder tail w K b (polyMul b (polyMul f f))-
        pairRemainder tail w K (polyMul b f) (polyMul b f) ≈
      t*((weightedAngularEnergy tail b f-
        H (tail+1) (polyMul (polyMul b b)
          (activeCasimirPolynomial (List.range (tail+1))
            (activeGamma (List.range (tail+1)) f f))))-
        48*H (tail+1) (polyMul (polyMul b f) (polyMul b f)))+
      (sourceCubic tail w b f-sourceOmitted tail w K b f)-
      t*retainedSlackValue (tail+1) b f := by
  dsimp only
  let t := HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
  let A := weightedAngularEnergy tail b f
  let X := H (tail+1) (polyMul (commutatorPolynomial (List.range (tail+1)) b f)
    (commutatorPolynomial (List.range (tail+1)) b f))
  let Y := H (tail+1) (polyMul (activeGamma (List.range (tail+1)) b b)
    (activeGamma (List.range (tail+1)) f f))
  let R := H (tail+1) (polyMul (polyMul b b)
    (activeCasimirPolynomial (List.range (tail+1)) (activeGamma (List.range (tail+1)) f f)))
  let S := H (tail+1) (polyMul (polyMul b f) (polyMul b f))
  let C := sourceCubic tail w b f
  let O := sourceOmitted tail w K b f
  have hfirst := sourceFirstOrder_eq_weightedAngularEnergy tail b f hb hf
  have hsecond := sourceSecondMoment_curvature tail b f hb hf
  have hstart :
      pairRemainder tail w K b (polyMul b (polyMul f f))-
        pairRemainder tail w K (polyMul b f) (polyMul b f) ≈
      t*((-X-2*Y-R)+A)+C-O :=
    Q'.eqv_trans _ _ _ (sourceRemainder_secondOrder tail w K b f)
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left t _ _ (Q'.add_eqv_congr' hsecond hfirst))
          (Q'.eqv_refl _)) (Q'.eqv_refl _))
  have hring : t*((-X-2*Y-R)+A)+C-O ≈
      t*((A-R)-48*S)+(C-O)-t*(X+2*Y-48*S) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0)
        (.add (.add (.add (.neg (.var 2)) (.neg (.mul (.const 2) (.var 3))))
          (.neg (.var 4))) (.var 1))) (.var 6)) (.neg (.var 7)))
      (.add (.add (.mul (.var 0)
        (.add (.add (.var 1) (.neg (.var 4))) (.neg (.mul (.const 48) (.var 5)))))
        (.add (.var 6) (.neg (.var 7))))
        (.neg (.mul (.var 0) (.add (.add (.var 2) (.mul (.const 2) (.var 3)))
          (.neg (.mul (.const 48) (.var 5)))))))
      (by decide) (fun | 0 => t | 1 => A | 2 => X | 3 => Y | 4 => R | 5 => S | 6 => C | _ => O)
  have hslack : t*((A-R)-48*S)+(C-O)-t*(X+2*Y-48*S) ≈
      t*((A-R)-48*S)+(C-O)-t*retainedSlackValue (tail+1) b f :=
    Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left t _ _
        (retainedSlackValue_expansion (tail+1) b f).symm))
  exact Q'.eqv_trans _ _ _ hstart (Q'.eqv_trans _ _ _ hring hslack)

/-- EXACT Taylor debt, preserving the actual certificate slack. No nome-sign
condition is needed for an equality of finite rational polynomial forms. -/
theorem familyChannelTaylorDebt_signed_exact (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    let t := HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
    familyChannelTaylorDebt w K width depth c qs ≈
      t*((familyChannelFirstOrder w K width depth c qs-
        familyChannelCurvature w K width depth c qs)-
        48*familyChannelObservableSquare w K width depth c qs)+
      (signedFamilyCubic w K width depth c qs-signedFamilyOmitted w K width depth c qs)-
      t*signedFamilyRetainedSlack w K width depth c qs := by
  dsimp only
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := spatialSpan width c qs
  let ids := familySpectatorBlocks width qs
  let cs := productChannels (N width) w K ids
  let b := fun z => channelSource ids q z
  let A := fun z => weightedAngularEnergy (N width-1) (b z) f
  let R := fun z => H (N width) (polyMul (polyMul (b z) (b z))
    (activeCasimirPolynomial (List.range (N width)) (activeGamma (List.range (N width)) f f)))
  let S := fun z => H (N width) (polyMul (polyMul (b z) f) (polyMul (b z) f))
  let C := fun z => sourceCubic (N width-1) w (b z) f
  let O := fun z => sourceOmitted (N width-1) w K (b z) f
  let B := fun z => retainedSlackValue (N width) (b z) f
  let t := HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth))
  have hf := spatialSpan_supported width c qs
  have hexact : channelSum cs (fun z =>
      pairRemainder (N width-1) w K (b z) (polyMul (b z) (polyMul f f))-
        pairRemainder (N width-1) w K (polyMul (b z) f) (polyMul (b z) f)) ≈
      channelSum cs (fun z => t*((A z-R z)-48*S z)+(C z-O z)-t*B z) := by
    apply channelSum_congr
    intro z hz
    have hb := channelSource_supported (N width) w K ids
      (familySpectatorBlocks_lt width qs) hq z hz
    have he := channel_debt_exact (N width-1) w K (b z.2) f
      (by simpa only [hN] using hb) (by simpa only [hN] using hf)
    simpa only [hN] using he
  have hcollect : channelSum cs (fun z => t*((A z-R z)-48*S z)+(C z-O z)-t*B z) ≈
      (t*((channelSum cs A-channelSum cs R)-48*channelSum cs S)+
        (channelSum cs C-channelSum cs O))-t*channelSum cs B :=
    Q'.eqv_trans _ _ _ (channelSum_sub _ _ cs)
      (Q'.add_eqv_congr' (channel_budget cs t A R S C O)
        (Q'.neg_eqv_congr _ _ (channelSum_smul B t cs)))
  have htarget :
      (t*((channelSum cs A-channelSum cs R)-48*channelSum cs S)+
        (channelSum cs C-channelSum cs O))-t*channelSum cs B ≈
      t*((familyChannelFirstOrder w K width depth c qs-
        familyChannelCurvature w K width depth c qs)-
        48*familyChannelObservableSquare w K width depth c qs)+
        (signedFamilyCubic w K width depth c qs-signedFamilyOmitted w K width depth c qs)-
        t*signedFamilyRetainedSlack w K width depth c qs :=
    Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left t _ _ (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' (familyChannelFirstOrder_eq_angular w K width depth c qs).symm
            (Q'.eqv_refl _)) (Q'.eqv_refl _))) (Q'.eqv_refl _))
      (Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ hexact (Q'.eqv_trans _ _ _ hcollect htarget)

/- The second-order source remainder stays exact; no sourceError_bound. -/
private theorem channel_debt_signed (tail : Nat) (w : Q') (K : Nat)
    (b f : RatPoly) (hb : SupportedQuaternionBlocks (tail+1) b)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hCf : HaarCarrierEqv (tail+1)
      (activeCasimirPolynomial (List.range (tail+1)) f) (polySmul 12 f)) :
    let t := HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
    pairRemainder tail w K b (polyMul b (polyMul f f)) -
        pairRemainder tail w K (polyMul b f) (polyMul b f) ≤
      t*((weightedAngularEnergy tail b f-
        H (tail+1) (polyMul (polyMul b b)
          (activeCasimirPolynomial (List.range (tail+1))
            (activeGamma (List.range (tail+1)) f f))))-
        48*H (tail+1) (polyMul (polyMul b f) (polyMul b f))) +
      (sourceCubic tail w b f-sourceOmitted tail w K b f) := by
  dsimp only
  let t := HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
  let A := weightedAngularEnergy tail b f
  let R := H (tail+1) (polyMul (polyMul b b)
    (activeCasimirPolynomial (List.range (tail+1))
      (activeGamma (List.range (tail+1)) f f)))
  let S := H (tail+1) (polyMul (polyMul b f) (polyMul b f))
  have ht : (0 : Q') ≤ t := Q'.mul_nonneg _ _ HalfPow.half_nonneg
    (SumOfSquares.q_mul_self_nonneg ((1 : Q')-w))
  have hsecond := sourceSecondMoment_le_retainedSquare tail b f hb hf hCf
  have hfirst := sourceFirstOrder_eq_weightedAngularEnergy tail b f hb hf
  have hle := Q'.add_le_add_right _ _ (sourceCubic tail w b f-sourceOmitted tail w K b f)
    (Q'.mul_le_mul_of_nonneg_left _ _ t
      (Q'.add_le_add hsecond (Q'.le_of_eqv hfirst)) ht)
  have hleft := Q'.eqv_trans _ _ _ (sourceRemainder_secondOrder tail w K b f)
    (Q'.add_assoc_eqv _ _ _)
  have hright : t*((-R-48*S)+A)+(sourceCubic tail w b f-sourceOmitted tail w K b f) ≈
      t*((A-R)-48*S)+(sourceCubic tail w b f-sourceOmitted tail w K b f) :=
    Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left t _ _ (poly_identity_of_normal_eq
        (.add (.add (.neg (.var 1)) (.neg (.mul (.const 48) (.var 2)))) (.var 0))
        (.add (.add (.var 0) (.neg (.var 1))) (.neg (.mul (.const 48) (.var 2))))
        (by decide) (fun | 0 => A | 1 => R | _ => S)))
      (Q'.eqv_refl _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hle (Q'.le_of_eqv hright))

/-- The actual family Taylor debt retains BOTH signed corrections at every
depth. No positivity of the channel source, cubic or omitted form is used. -/
theorem familyChannelTaylorDebt_le_signed {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K : Nat) {base width : Nat} (hwidth : base < width) (depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let t := HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
    familyChannelTaylorDebt w K width depth c qs ≤
      t*((familyChannelFirstOrder w K width depth c qs-
        familyChannelCurvature w K width depth c qs)-
        48*familyChannelObservableSquare w K width depth c qs)+
      (signedFamilyCubic w K width depth c qs-signedFamilyOmitted w K width depth c qs) := by
  dsimp only
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := spatialSpan width c qs
  let ids := familySpectatorBlocks width qs
  let cs := productChannels (N width) w K ids
  let b := fun z => channelSource ids q z
  let A := fun z => weightedAngularEnergy (N width-1) (b z) f
  let R := fun z => H (N width) (polyMul (polyMul (b z) (b z))
    (activeCasimirPolynomial (List.range (N width)) (activeGamma (List.range (N width)) f f)))
  let S := fun z => H (N width) (polyMul (polyMul (b z) f) (polyMul (b z) f))
  let C := fun z => sourceCubic (N width-1) w (b z) f
  let O := fun z => sourceOmitted (N width-1) w K (b z) f
  let t := HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth))
  have hf := spatialSpan_supported width c qs
  have hCf := spatialSpan_casimir width c qs
    (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
  have hle : channelSum cs (fun z =>
      pairRemainder (N width-1) w K (b z) (polyMul (b z) (polyMul f f))-
        pairRemainder (N width-1) w K (polyMul (b z) f) (polyMul (b z) f)) ≤
      channelSum cs (fun z => t*((A z-R z)-48*S z)+(C z-O z)) := by
    apply channelSum_le
    · exact productChannels_nonnegative (N width) hw0 K ids
    · intro z hz
      have hb := channelSource_supported (N width) w K ids
        (familySpectatorBlocks_lt width qs) hq z hz
      have hs := channel_debt_signed (N width-1) w K (b z.2) f
        (by simpa only [hN] using hb) (by simpa only [hN] using hf)
        (by simpa only [hN] using hCf)
      simpa only [hN] using hs
  have hfirst := (familyChannelFirstOrder_eq_angular w K width depth c qs).symm
  have hcollect := channel_budget cs t A R S C O
  have htarget :
      t*((channelSum cs A-channelSum cs R)-48*channelSum cs S)+
        (channelSum cs C-channelSum cs O) ≈
      t*((familyChannelFirstOrder w K width depth c qs-
        familyChannelCurvature w K width depth c qs)-
        48*familyChannelObservableSquare w K width depth c qs)+
        (signedFamilyCubic w K width depth c qs-signedFamilyOmitted w K width depth c qs) :=
    Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left t _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' hfirst (Q'.eqv_refl _)) (Q'.eqv_refl _)))
    (Q'.eqv_refl _)
  exact Q'.le_trans' _ _ _ hle
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect) (Q'.le_of_eqv htarget))

/-- Complete ORIGINAL unfiltered energy for arbitrary signed/repeated
padded families. The combined signed right side is UNPAID against OWN variance. -/
theorem padded_family_energy_le_signed {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K : Nat) {base width : Nat} (hwidth : base < width) (depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let h := (1 : Q')-w
    let t := HalfPow.half*(h*h)
    energy w K width (terminalMessage w K width depth) (spatialSpan width c qs) ≤
      (h-19*t)*familyChannelGradient w K width depth c qs +
        ((signedFamilyCubic w K width depth c qs-
          t*familyChannelPairRemainder w K width depth c qs)-
          signedFamilyOmitted w K width depth c qs) := by
  dsimp only
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  let G := familyChannelGradient w K width depth c qs
  let R := familyChannelCurvature w K width depth c qs
  let S := familyChannelObservableSquare w K width depth c qs
  let P := familyChannelPairRemainder w K width depth c qs
  let C := signedFamilyCubic w K width depth c qs
  let O := signedFamilyOmitted w K width depth c qs
  have hbound := Q'.add_le_add_left (h*familyChannelFirstOrder w K width depth c qs) _ _
    (familyChannelTaylorDebt_le_signed hw0 K hwidth depth c qs hqs)
  have hAG : familyChannelFirstOrder w K width depth c qs = G := rfl
  have hcurv := familyChannel_curvature_remainder w K width depth c qs
    (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
  have hshape : h*G+(t*((G-R)-48*S)+(C-O)) ≈
      (h+t)*G-t*(R+48*S)+(C-O) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2))
        (.add (.mul (.var 1) (.add (.add (.var 2) (.neg (.var 3)))
          (.neg (.mul (.const 48) (.var 4))))) (.add (.var 5) (.neg (.var 6)))))
      (.add (.add (.mul (.add (.var 0) (.var 1)) (.var 2))
        (.neg (.mul (.var 1) (.add (.var 3) (.mul (.const 48) (.var 4))))))
        (.add (.var 5) (.neg (.var 6)))) (by decide)
      (fun | 0 => h | 1 => t | 2 => G | 3 => R | 4 => S | 5 => C | _ => O)
  have hreplace : (h+t)*G-t*(R+48*S)+(C-O) ≈
      (h+t)*G-t*(20*G+P)+(C-O) := Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left t _ _ hcurv))) (Q'.eqv_refl _)
  have hfinal : (h+t)*G-t*(20*G+P)+(C-O) ≈ (h-19*t)*G+((C-t*P)-O) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.add (.var 0) (.var 1)) (.var 2))
        (.neg (.mul (.var 1) (.add (.mul (.const 20) (.var 2)) (.var 3)))))
        (.add (.var 4) (.neg (.var 5))))
      (.add (.mul (.add (.var 0) (.neg (.mul (.const 19) (.var 1)))) (.var 2))
        (.add (.add (.var 4) (.neg (.mul (.var 1) (.var 3)))) (.neg (.var 5))))
      (by decide) (fun | 0 => h | 1 => t | 2 => G | 3 => P | 4 => C | _ => O)
  rw [hAG] at hbound
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (padded_family_channel_energy_taylor w K hwidth depth c qs hqs))
    (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ hshape (Q'.eqv_trans _ _ _ hreplace hfinal))))

/-- EXACT ORIGINAL energy, including the nonnegative retained-square slack.
No component sign or SAME-variance payment is assumed. Nome may be signed;
positivity of the slack is separately produced above for nonnegative nome. -/
theorem padded_family_energy_signed_exact (w : Q') (K : Nat)
    {base width : Nat} (hwidth : base < width) (depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let h := (1 : Q')-w
    let t := HalfPow.half*(h*h)
    energy w K width (terminalMessage w K width depth) (spatialSpan width c qs) ≈
      (h-19*t)*familyChannelGradient w K width depth c qs+
        ((signedFamilyCubic w K width depth c qs-
          t*familyChannelPairRemainder w K width depth c qs)-
          signedFamilyOmitted w K width depth c qs)-
        t*signedFamilyRetainedSlack w K width depth c qs := by
  dsimp only
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  let G := familyChannelGradient w K width depth c qs
  let R := familyChannelCurvature w K width depth c qs
  let S := familyChannelObservableSquare w K width depth c qs
  let P := familyChannelPairRemainder w K width depth c qs
  let C := signedFamilyCubic w K width depth c qs
  let O := signedFamilyOmitted w K width depth c qs
  let B := signedFamilyRetainedSlack w K width depth c qs
  have hstart :
      energy w K width (terminalMessage w K width depth) (spatialSpan width c qs) ≈
      h*G+(t*((G-R)-48*S)+(C-O)-t*B) :=
    Q'.eqv_trans _ _ _ (padded_family_channel_energy_taylor w K hwidth depth c qs hqs)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (familyChannelTaylorDebt_signed_exact w K width depth c qs))
  have hcurv := familyChannel_curvature_remainder w K width depth c qs
    (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
  have hshape : h*G+(t*((G-R)-48*S)+(C-O)-t*B) ≈
      ((h+t)*G-t*(R+48*S)+(C-O))-t*B :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2))
        (.add (.add (.mul (.var 1) (.add (.add (.var 2) (.neg (.var 3)))
          (.neg (.mul (.const 48) (.var 4))))) (.add (.var 5) (.neg (.var 6))))
          (.neg (.mul (.var 1) (.var 7)))))
      (.add (.add (.add (.mul (.add (.var 0) (.var 1)) (.var 2))
        (.neg (.mul (.var 1) (.add (.var 3) (.mul (.const 48) (.var 4))))))
        (.add (.var 5) (.neg (.var 6)))) (.neg (.mul (.var 1) (.var 7))))
      (by decide) (fun | 0 => h | 1 => t | 2 => G | 3 => R | 4 => S | 5 => C | 6 => O | _ => B)
  have hreplace : ((h+t)*G-t*(R+48*S)+(C-O))-t*B ≈
      ((h+t)*G-t*(20*G+P)+(C-O))-t*B :=
    Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left t _ _ hcurv)))
        (Q'.eqv_refl _)) (Q'.eqv_refl _)
  have hfinal : ((h+t)*G-t*(20*G+P)+(C-O))-t*B ≈
      (h-19*t)*G+((C-t*P)-O)-t*B :=
    Q'.add_eqv_congr'
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.add (.var 0) (.var 1)) (.var 2))
          (.neg (.mul (.var 1) (.add (.mul (.const 20) (.var 2)) (.var 3)))))
          (.add (.var 4) (.neg (.var 5))))
        (.add (.mul (.add (.var 0) (.neg (.mul (.const 19) (.var 1)))) (.var 2))
          (.add (.add (.var 4) (.neg (.mul (.var 1) (.var 3)))) (.neg (.var 5))))
        (by decide) (fun | 0 => h | 1 => t | 2 => G | 3 => P | 4 => C | _ => O))
      (Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ hstart
    (Q'.eqv_trans _ _ _ hshape (Q'.eqv_trans _ _ _ hreplace hfinal))

#print axioms signedFamilyCubic
#print axioms signedFamilyOmitted
#print axioms signedFamilyRetainedSlack
#print axioms signedFamilyRetainedSlack_nonnegative
#print axioms familyChannelTaylorDebt_signed_exact
#print axioms familyChannelTaylorDebt_le_signed
#print axioms padded_family_energy_le_signed
#print axioms padded_family_energy_signed_exact

end YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyEnergy
