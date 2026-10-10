/-
# Exact retained-square coercivity on ORIGINAL family channels

The actual projected terminal source is dressed by every unchanged passive
Gram channel. Completing the retained square produces an exact, inverse-free
identity with a nonnegative square/Gram residual. The original energy join
keeps SIGNED cubic, pair remainder and omitted loss; only the latter is paid
by the existing computed cutoff. No interacting variance payment for the
remaining signed debt, warmed-source Casimir pin, moving-family uniformity,
physical scaling or mass gap is asserted.
-/

import YMGap.Continuum.SU2QuaternionRetainedSquareCoercivity
import YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyEnergyPayment

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct (activeGamma)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
  (channelSource_supported channelSum_congr channelSum_smul)
open YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError (channelSum_add)
open YMGap.Continuum.SU2QuaternionRetainedSquareCoercivity
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir (spatialSpan_casimir)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelRetainedSquare
  (familyChannelObservableSquare)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCurvature
  (familyChannelGradient familyChannelPairRemainder)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyEnergy
  (signedFamilyRetainedSlack signedFamilyCubic signedFamilyOmitted)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyEnergyPayment
  (remainingFamilyEnergy energy_eq_remaining normalizedEnergy_signed_cutoff_payment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyOmittedPayment
  (familyBareNorm omittedPaymentCutoff headCutoff_le_omittedPaymentCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n

attribute [local irreducible] baseLinks terminalMessage

/-- Literal square residual, summed on the SAME original passive channels. -/
def channelCoercivitySquare (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) (a t : Q') : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := spatialSpan width c qs
  let ids := familySpectatorBlocks width qs
  channelSum (productChannels (N width) w K ids) (fun z =>
    let s := coercivitySquare (List.range (N width)) (channelSource ids q z) f a t
    H (N width) (polyMul s s))

/-- Literal angular Gram determinant on the SAME signed channel sources. -/
def channelCoercivityGram (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := spatialSpan width c qs
  let ids := familySpectatorBlocks width qs
  channelSum (productChannels (N width) w K ids) (fun z =>
    H (N width) (coercivityGram (List.range (N width)) (channelSource ids q z) f))

/-- Both residuals retained with the exact nonnegative coefficient. -/
def channelCoercivityResidual (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) (a t : Q') : Q' :=
  channelCoercivitySquare w K width depth c qs a t+
    (12*t*t)*channelCoercivityGram w K width depth c qs

private theorem sum_neg (value : RatPoly → Q') : ∀ cs : List GramChannel,
    channelSum cs (fun z => -(value z)) ≈ -(channelSum cs value)
  | [] => by change (0 : Q') ≈ -0; decide
  | z::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (poly_identity_of_normal_eq (.mul (.var 0) (.neg (.var 1)))
          (.neg (.mul (.var 0) (.var 1))) (by decide)
          (fun | 0 => z.1 | _ => value z.2)) (sum_neg value cs))
      (Q'.neg_add_eqv_split _ _).symm

private theorem sum_sub (left right : RatPoly → Q') (cs : List GramChannel) :
    channelSum cs (fun z => left z-right z) ≈
      channelSum cs left-channelSum cs right :=
  Q'.eqv_trans _ _ _ (channelSum_add left (fun z => -(right z)) cs)
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_neg right cs))

private theorem sum_coercivity (cs : List GramChannel)
    (Q G B : RatPoly → Q') (a t : Q') :
    channelSum cs (fun z => (a*a+24*a*t)*Q z-6*t*(a*G z-t*B z)) ≈
      (a*a+24*a*t)*channelSum cs Q-
        6*t*(a*channelSum cs G-t*channelSum cs B) :=
  Q'.eqv_trans _ _ _
    (sum_sub (fun z => (a*a+24*a*t)*Q z) (fun z => 6*t*(a*G z-t*B z)) cs)
    (Q'.add_eqv_congr' (channelSum_smul Q (a*a+24*a*t) cs)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
        (channelSum_smul (fun z => a*G z-t*B z) (6*t) cs)
        (Q'.mul_eqv_congr_left (6*t) _ _ (Q'.eqv_trans _ _ _
          (sum_sub (fun z => a*G z) (fun z => t*B z) cs)
          (Q'.add_eqv_congr' (channelSum_smul G a cs)
            (Q'.neg_eqv_congr _ _ (channelSum_smul B t cs))))))))

/-- Exact channel fold. Equality needs no nome sign and no face deduplication. -/
theorem family_channel_coercivity_identity (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) (a t : Q') :
    (a*a+24*a*t)*familyChannelObservableSquare w K width depth c qs-
        6*t*(a*familyChannelGradient w K width depth c qs-
          t*signedFamilyRetainedSlack w K width depth c qs) ≈
      channelCoercivityResidual w K width depth c qs a t := by
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := spatialSpan width c qs
  let ids := familySpectatorBlocks width qs
  let cs := productChannels (N width) w K ids
  let b := fun z => channelSource ids q z
  let Q := fun z => H (N width) (polyMul (polyMul (b z) f) (polyMul (b z) f))
  let G := fun z => H (N width) (polyMul (polyMul (b z) (b z))
    (activeGamma (List.range (N width)) f f))
  let B := fun z => retainedSlackValue (N width) (List.range (N width)) (b z) f
  let S := fun z => H (N width) (polyMul
    (coercivitySquare (List.range (N width)) (b z) f a t)
    (coercivitySquare (List.range (N width)) (b z) f a t))
  let D := fun z => H (N width) (coercivityGram (List.range (N width)) (b z) f)
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth))
  have hf := spatialSpan_supported width c qs
  have hCf := spatialSpan_casimir width c qs hqs
  have hp : channelSum cs (fun z => (a*a+24*a*t)*Q z-6*t*(a*G z-t*B z)) ≈
      channelSum cs (fun z => S z+(12*t*t)*D z) := by
    apply channelSum_congr
    intro z hz
    have hb := channelSource_supported (N width) w K ids
      (familySpectatorBlocks_lt width qs) hq z hz
    exact retained_coercivity_identity (N width) (List.range (N width))
      (fun i hi => List.mem_range.mp hi) (b z.2) f hb hf hCf a t
  have hr : channelSum cs (fun z => S z+(12*t*t)*D z) ≈
      channelSum cs S+(12*t*t)*channelSum cs D :=
    Q'.eqv_trans _ _ _ (channelSum_add S (fun z => (12*t*t)*D z) cs)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (channelSum_smul D (12*t*t) cs))
  exact Q'.eqv_trans _ _ _ (sum_coercivity cs Q G B a t).symm
    (Q'.eqv_trans _ _ _ hp hr)

private theorem sum_nonnegative (value : RatPoly → Q') : ∀ cs : List GramChannel,
    (∀ z, z ∈ cs → (0 : Q') ≤ z.1) →
    (∀ z, z ∈ cs → (0 : Q') ≤ value z.2) → (0 : Q') ≤ channelSum cs value
  | [], _, _ => Q'.le_refl' _
  | z::cs, hw, hv => Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (hw z List.mem_cons_self) (hv z List.mem_cons_self))
      (sum_nonnegative value cs
        (fun u hu => hw u (List.mem_cons_of_mem z hu))
        (fun u hu => hv u (List.mem_cons_of_mem z hu)))

/-- Produced residual positivity; channel sources may be signed, and a/t arbitrary. -/
theorem channelCoercivityResidual_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K width depth : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) (a t : Q') :
    (0 : Q') ≤ channelCoercivityResidual w K width depth c qs a t := by
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := spatialSpan width c qs
  let ids := familySpectatorBlocks width qs
  let cs := productChannels (N width) w K ids
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth))
  have hf := spatialSpan_supported width c qs
  have hw := productChannels_nonnegative (N width) hw0 K ids
  let S := fun z => H (N width) (polyMul
    (coercivitySquare (List.range (N width)) (channelSource ids q z) f a t)
    (coercivitySquare (List.range (N width)) (channelSource ids q z) f a t))
  let D := fun z => H (N width)
    (coercivityGram (List.range (N width)) (channelSource ids q z) f)
  have hS : (0 : Q') ≤ channelSum cs S := sum_nonnegative S cs hw (fun z hz =>
    coercivitySquare_haar_nonnegative (N width) (List.range (N width))
      (fun i hi => List.mem_range.mp hi) (channelSource ids q z.2) f
      (channelSource_supported (N width) w K ids (familySpectatorBlocks_lt width qs) hq z hz)
      hf a t)
  have hD : (0 : Q') ≤ channelSum cs D := sum_nonnegative D cs hw (fun z hz =>
    coercivityGram_nonnegative (N width) (List.range (N width))
      (fun i hi => List.mem_range.mp hi) (channelSource ids q z.2) f
      (channelSource_supported (N width) w K ids (familySpectatorBlocks_lt width qs) hq z hz) hf)
  have ht : (0 : Q') ≤ 12*t*t := Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 12) (SumOfSquares.q_mul_self_nonneg t))
    (Q'.ge_of_eqv (Q'.mul_assoc_eqv 12 t t))
  change (0 : Q') ≤ channelSum cs S+(12*t*t)*channelSum cs D
  exact Q'.zero_le_add _ _ hS (Q'.mul_nonneg _ _ ht hD)

private theorem rearrange (a t Q G B C R D : Q')
    (h : (a*a+24*a*t)*Q-6*t*(a*G-t*B) ≈ D) :
    6*t*((a*G+(C-t*R))-t*B)+D ≈ (a*a+24*a*t)*Q+6*t*(C-t*R) :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) h.symm)
    (poly_identity_of_normal_eq
      (.add (.mul (.mul (.const 6) (.var 1))
        (.add (.add (.mul (.var 0) (.var 3))
          (.add (.var 5) (.neg (.mul (.var 1) (.var 6)))))
          (.neg (.mul (.var 1) (.var 4)))))
        (.add (.mul (.add (.mul (.var 0) (.var 0))
          (.mul (.mul (.const 24) (.var 0)) (.var 1))) (.var 2))
          (.neg (.mul (.mul (.const 6) (.var 1))
            (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 4))))))))
      (.add (.mul (.add (.mul (.var 0) (.var 0))
          (.mul (.mul (.const 24) (.var 0)) (.var 1))) (.var 2))
        (.mul (.mul (.const 6) (.var 1)) (.add (.var 5) (.neg (.mul (.var 1) (.var 6))))))
      (by decide) (fun | 0 => a | 1 => t | 2 => Q | 3 => G | 4 => B | 5 => C | _ => R))

/-- Exact completion of the UNPAID remaining signed energy; no division by t. -/
theorem remainingFamilyEnergy_coercivity_identity (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    let h := (1 : Q')-w
    let t := HalfPow.half*(h*h)
    let a := h-19*t
    6*t*remainingFamilyEnergy w K width depth c qs+
        channelCoercivityResidual w K width depth c qs a t ≈
      (a*a+24*a*t)*familyChannelObservableSquare w K width depth c qs+
        6*t*(signedFamilyCubic w K width depth c qs-
          t*familyChannelPairRemainder w K width depth c qs) := by
  dsimp only
  exact rearrange ((1-w)-19*(HalfPow.half*((1-w)*(1-w))))
    (HalfPow.half*((1-w)*(1-w)))
    (familyChannelObservableSquare w K width depth c qs)
    (familyChannelGradient w K width depth c qs)
    (signedFamilyRetainedSlack w K width depth c qs)
    (signedFamilyCubic w K width depth c qs)
    (familyChannelPairRemainder w K width depth c qs)
    (channelCoercivityResidual w K width depth c qs
      ((1-w)-19*(HalfPow.half*((1-w)*(1-w)))) (HalfPow.half*((1-w)*(1-w))))
    (family_channel_coercivity_identity w K width depth c qs hqs _ _)

/-- ORIGINAL energy equality, retaining the omitted form and both residuals. -/
theorem padded_family_energy_coercivity_identity (w : Q') (K : Nat)
    {base width : Nat} (hwidth : base < width) (depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let h := (1 : Q')-w
    let t := HalfPow.half*(h*h)
    let a := h-19*t
    6*t*energy w K width (terminalMessage w K width depth) (spatialSpan width c qs)+
        channelCoercivityResidual w K width depth c qs a t ≈
      (a*a+24*a*t)*familyChannelObservableSquare w K width depth c qs+
        6*t*((signedFamilyCubic w K width depth c qs-
          t*familyChannelPairRemainder w K width depth c qs)-
          signedFamilyOmitted w K width depth c qs) := by
  dsimp only
  let t := HalfPow.half*((1-w)*(1-w))
  let a := (1-w)-19*t
  let D := channelCoercivityResidual w K width depth c qs a t
  let E := remainingFamilyEnergy w K width depth c qs
  let O := signedFamilyOmitted w K width depth c qs
  let Q := (a*a+24*a*t)*familyChannelObservableSquare w K width depth c qs
  let C := signedFamilyCubic w K width depth c qs-t*familyChannelPairRemainder w K width depth c qs
  have he := energy_eq_remaining w K hwidth depth c qs hqs
  have hc := remainingFamilyEnergy_coercivity_identity w K width depth c qs
    (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
  have hr : 6*t*(E+(-O))+D ≈ (6*t*E+D)+(-(6*t*O)) :=
    poly_identity_of_normal_eq
      (.add (.mul (.mul (.const 6) (.var 0)) (.add (.var 1) (.neg (.var 2)))) (.var 3))
      (.add (.add (.mul (.mul (.const 6) (.var 0)) (.var 1)) (.var 3))
        (.neg (.mul (.mul (.const 6) (.var 0)) (.var 2))))
      (by decide) (fun | 0 => t | 1 => E | 2 => O | _ => D)
  have hf : (Q+6*t*C)+(-(6*t*O)) ≈ Q+6*t*(C-O) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.mul (.mul (.const 6) (.var 1)) (.var 2)))
        (.neg (.mul (.mul (.const 6) (.var 1)) (.var 3))))
      (.add (.var 0) (.mul (.mul (.const 6) (.var 1)) (.add (.var 2) (.neg (.var 3)))))
      (by decide) (fun | 0 => Q | 1 => t | 2 => C | _ => O)
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left (6*t) _ _ he) (Q'.eqv_refl _))
    (Q'.eqv_trans _ _ _ hr (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hc (Q'.eqv_refl _)) hf))

/-- Existing actual omitted cutoff pays only O. No source/variance inverse,
nor a comparison of the remaining C/R debt, is assumed or concluded. -/
theorem normalizedEnergy_coercivity_cutoff_payment {w delta : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hdelta : (0 : Q') < delta)
    {base width : Nat} (hwidth : base < width) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)
    (hB : (0 : Q') < familyBareNorm width c qs) (K : Nat)
    (hK : omittedPaymentCutoff hw0 hw1 width c qs hB delta ≤ K) (n : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_omittedPaymentCutoff hw0 hw1 width c qs hB delta) hK
    let r := Q'.recipPos (oddMass w K width (n+1)) (oddMass_positive hw0 hw1 K width hhead (n+1))
    let h := (1 : Q')-w
    let t := HalfPow.half*(h*h)
    let a := h-19*t
    6*t*normalizedEnergy hw0 hw1 K width hhead (n+1) (spatialSpan width c qs)+
        channelCoercivityResidual w K width (n+1) c qs a t*r ≤
      ((a*a+24*a*t)*familyChannelObservableSquare w K width (n+1) c qs+
        6*t*(signedFamilyCubic w K width (n+1) c qs-
          t*familyChannelPairRemainder w K width (n+1) c qs))*r+
        (6*t*delta)*oddVariance hw0 hw1 K width hhead (n+1) (spatialSpan width c qs) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_omittedPaymentCutoff hw0 hw1 width c qs hB delta) hK
  let r := Q'.recipPos (oddMass w K width (n+1)) (oddMass_positive hw0 hw1 K width hhead (n+1))
  let t := HalfPow.half*((1-w)*(1-w))
  let a := (1-w)-19*t
  let D := channelCoercivityResidual w K width (n+1) c qs a t
  let E := remainingFamilyEnergy w K width (n+1) c qs
  let V := oddVariance hw0 hw1 K width hhead (n+1) (spatialSpan width c qs)
  let P := (a*a+24*a*t)*familyChannelObservableSquare w K width (n+1) c qs+
    6*t*(signedFamilyCubic w K width (n+1) c qs-t*familyChannelPairRemainder w K width (n+1) c qs)
  have ht : (0 : Q') ≤ 6*t := Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 6)
    (Q'.mul_nonneg _ _ HalfPow.half_nonneg (SumOfSquares.q_mul_self_nonneg (1-w)))
  have hb := normalizedEnergy_signed_cutoff_payment hw0 hw1 hdelta hwidth c qs hqs hB K hK n
  have hs := Q'.add_le_add_right _ _ (D*r)
    (Q'.mul_le_mul_of_nonneg_left _ _ (6*t) hb ht)
  have hr : 6*t*(E*r+delta*V)+D*r ≈ (6*t*E+D)*r+(6*t*delta)*V :=
    poly_identity_of_normal_eq
      (.add (.mul (.mul (.const 6) (.var 0))
        (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4)))) (.mul (.var 5) (.var 2)))
      (.add (.mul (.add (.mul (.mul (.const 6) (.var 0)) (.var 1)) (.var 5)) (.var 2))
        (.mul (.mul (.mul (.const 6) (.var 0)) (.var 3)) (.var 4)))
      (by decide) (fun | 0 => t | 1 => E | 2 => r | 3 => delta | 4 => V | _ => D)
  have hc : 6*t*E+D ≈ P := remainingFamilyEnergy_coercivity_identity w K width (n+1) c qs
    (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
  exact Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hr
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ r hc) (Q'.eqv_refl _))))

#print axioms channelCoercivitySquare
#print axioms channelCoercivityGram
#print axioms channelCoercivityResidual
#print axioms family_channel_coercivity_identity
#print axioms channelCoercivityResidual_nonnegative
#print axioms remainingFamilyEnergy_coercivity_identity
#print axioms padded_family_energy_coercivity_identity
#print axioms normalizedEnergy_coercivity_cutoff_payment

end YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCoercivity
