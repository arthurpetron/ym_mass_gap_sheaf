/-
# Remove the raw constant mode on ORIGINAL signed-family channels

The complete weighted channel form, not each separately normalized channel,
produces a connected determinant and a nonnegative rank-one residual. The
existing exact energy and computed omitted cutoff retain both credits.
No source-mass inverse, equality of channel/OWN means, positivity of the
signed cubic/pair correction, warmed pin or scaling estimate is asserted.
The connected determinant is RAW channel data, not OWN interacting variance.
-/

import YMGap.Continuum.SU2QuaternionChannelConnectedCoercivity
import YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCoercivity

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyConnectedCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization (channelSource_supported)
open YMGap.Continuum.SU2QuaternionChannelConnectedCoercivity
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
  (remainingFamilyEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCoercivity
open YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyOmittedPayment
  (familyBareNorm omittedPaymentCutoff headCutoff_le_omittedPaymentCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks terminalMessage

/-- TOTAL raw source-square mass; no channel is separately normalized. -/
def familyChannelSourceMass (w : Q') (K width depth : Nat) (qs : List Z4Plaq) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let ids := familySpectatorBlocks width qs
  let b := channelSource ids q
  channelHaarPair (N width) (productChannels (N width) w K ids) b b

/-- TOTAL raw first moment on the unchanged signed family and channel sources. -/
def familyChannelSourceMoment (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let ids := familySpectatorBlocks width qs
  let b := channelSource ids q
  channelHaarPair (N width) (productChannels (N width) w K ids)
    b (fun z => polyMul (b z) (spatialSpan width c qs))

/-- A cleared RAW connected determinant, not the original OWN variance. -/
def familyChannelConnectedDeterminant (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  familyChannelSourceMass w K width depth qs *
      familyChannelObservableSquare w K width depth c qs-
    familyChannelSourceMoment w K width depth c qs *
      familyChannelSourceMoment w K width depth c qs

/-- The full earlier residual minus only its produced constant-mode credit. -/
def familyChannelConnectedResidual (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) (a t : Q') : Q' :=
  familyChannelSourceMass w K width depth qs *
      channelCoercivityResidual w K width depth c qs a t-
    ((a+12*t)*(a+12*t))*
      (familyChannelSourceMoment w K width depth c qs *
        familyChannelSourceMoment w K width depth c qs)

theorem familyChannelSourceMass_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K width depth : Nat) (qs : List Z4Plaq) :
    (0 : Q') ≤ familyChannelSourceMass w K width depth qs := by
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let ids := familySpectatorBlocks width qs
  have hq := familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width depth))
  exact channelHaarPair_self_nonnegative (N width)
    (productChannels (N width) w K ids) (productChannels_nonnegative (N width) hw0 K ids)
    (channelSource ids q) (fun z hz => channelSource_supported (N width) w K ids
      (familySpectatorBlocks_lt width qs) hq z hz)

/-- Raw total-channel variance positivity; no OWN-mean identification is used. -/
theorem familyChannelConnectedDeterminant_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K width depth : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq) :
    (0 : Q') ≤ familyChannelConnectedDeterminant w K width depth c qs := by
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let ids := familySpectatorBlocks width qs
  let b := channelSource ids q
  have hq := familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width depth))
  have hb := fun z hz => channelSource_supported (N width) w K ids
    (familySpectatorBlocks_lt width qs) hq z hz
  have hc := channelHaarPair_cauchySchwarz (N width)
    (productChannels (N width) w K ids) (productChannels_nonnegative (N width) hw0 K ids)
    b (fun z => polyMul (b z) (spatialSpan width c qs)) hb
    (fun z hz => supported_polyMul (hb z hz) (spatialSpan_supported width c qs))
  exact Q'.sub_nonneg_of_le hc

/-- Actual FULL-channel extraction, preserving signs, repeated faces and zero mass. -/
theorem family_channel_connected_coercivity {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K width depth : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) (a t : Q') :
    6*t*familyChannelSourceMass w K width depth qs *
        (a*familyChannelGradient w K width depth c qs-
          t*signedFamilyRetainedSlack w K width depth c qs)+
        144*t*t*familyChannelSourceMoment w K width depth c qs *
          familyChannelSourceMoment w K width depth c qs ≤
      (a*a+24*a*t)*familyChannelConnectedDeterminant w K width depth c qs := by
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let ids := familySpectatorBlocks width qs
  have hq := familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width depth))
  exact connected_channel_coercivity (N width) (List.range (N width))
    (fun i hi => List.mem_range.mp hi) (productChannels (N width) w K ids)
    (productChannels_nonnegative (N width) hw0 K ids) (channelSource ids q)
    (fun z hz => channelSource_supported (N width) w K ids
      (familySpectatorBlocks_lt width qs) hq z hz)
    (spatialSpan width c qs) (spatialSpan_supported width c qs)
    (spatialSpan_casimir width c qs hqs) a t

private theorem connected_rearrange (a t S M Q G B D : Q')
    (h : (a*a+24*a*t)*Q-6*t*(a*G-t*B) ≈ D) :
    (a*a+24*a*t)*(S*Q-M*M)-
        (6*t*S*(a*G-t*B)+144*t*t*M*M) ≈
      S*D-((a+12*t)*(a+12*t))*(M*M) := by
  have hd := Q'.mul_eqv_congr_left S _ _ h.symm
  have hr := Q'.add_eqv_congr' hd
    (Q'.eqv_refl (-(((a+12*t)*(a+12*t))*(M*M))))
  let A : PolyExpr := .var 0
  let T : PolyExpr := .var 1
  let Se : PolyExpr := .var 2
  let Me : PolyExpr := .var 3
  let Qe : PolyExpr := .var 4
  let Ge : PolyExpr := .var 5
  let Be : PolyExpr := .var 6
  let Ke : PolyExpr := .add (.mul A A) (.mul (.mul (.const 24) A) T)
  let Le : PolyExpr := .add (.mul A Ge) (.neg (.mul T Be))
  let Ve : PolyExpr := .add A (.mul (.const 12) T)
  let env : Nat → Q' := fun
    | 0 => a
    | 1 => t
    | 2 => S
    | 3 => M
    | 4 => Q
    | 5 => G
    | _ => B
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.add (.mul Ke (.add (.mul Se Qe) (.neg (.mul Me Me))))
        (.neg (.add (.mul (.mul (.mul (.const 6) T) Se) Le)
          (.mul (.mul (.mul (.mul (.const 144) T) T) Me) Me))))
      (.add (.mul Se (.add (.mul Ke Qe) (.neg (.mul (.mul (.const 6) T) Le))))
        (.neg (.mul (.mul Ve Ve) (.mul Me Me))))
      (by decide) env)
    (Q'.eqv_symm hr)

/-- Produced rank-one residual positivity, not an assumed centered eigenfunction. -/
theorem familyChannelConnectedResidual_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K width depth : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) (a t : Q') :
    (0 : Q') ≤ familyChannelConnectedResidual w K width depth c qs a t := by
  have hb := family_channel_connected_coercivity hw0 K width depth c qs hqs a t
  have hc := family_channel_coercivity_identity w K width depth c qs hqs a t
  have hp := connected_rearrange a t (familyChannelSourceMass w K width depth qs)
    (familyChannelSourceMoment w K width depth c qs)
    (familyChannelObservableSquare w K width depth c qs)
    (familyChannelGradient w K width depth c qs)
    (signedFamilyRetainedSlack w K width depth c qs)
    (channelCoercivityResidual w K width depth c qs a t) hc
  exact Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hb) (Q'.le_of_eqv hp)

private theorem energy_centering (a t S M Q C R O E D : Q')
    (h : 6*t*E+D ≈ (a*a+24*a*t)*Q+6*t*((C-t*R)-O)) :
    6*t*S*E+144*t*t*M*M+(S*D-((a+12*t)*(a+12*t))*(M*M)) ≈
      (a*a+24*a*t)*(S*Q-M*M)+6*t*S*((C-t*R)-O) := by
  let A : PolyExpr := .var 0
  let T : PolyExpr := .var 1
  let Se : PolyExpr := .var 2
  let Me : PolyExpr := .var 3
  let Ee : PolyExpr := .var 4
  let De : PolyExpr := .var 5
  let Ke : PolyExpr := .add (.mul A A) (.mul (.mul (.const 24) A) T)
  let Ve : PolyExpr := .add A (.mul (.const 12) T)
  let env : Nat → Q' := fun
    | 0 => a
    | 1 => t
    | 2 => S
    | 3 => M
    | 4 => E
    | _ => D
  have hr : 6*t*S*E+144*t*t*M*M+(S*D-((a+12*t)*(a+12*t))*(M*M)) ≈
      S*(6*t*E+D)-(a*a+24*a*t)*(M*M) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.mul (.const 6) T) Se) Ee)
        (.mul (.mul (.mul (.mul (.const 144) T) T) Me) Me))
        (.add (.mul Se De) (.neg (.mul (.mul Ve Ve) (.mul Me Me)))))
      (.add (.mul Se (.add (.mul (.mul (.const 6) T) Ee) De))
        (.neg (.mul Ke (.mul Me Me)))) (by decide) env
  have hs := Q'.add_eqv_congr' (Q'.mul_eqv_congr_left S _ _ h)
    (Q'.eqv_refl (-((a*a+24*a*t)*(M*M))))
  have hf : S*((a*a+24*a*t)*Q+6*t*((C-t*R)-O))-(a*a+24*a*t)*(M*M) ≈
      (a*a+24*a*t)*(S*Q-M*M)+6*t*S*((C-t*R)-O) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 2) (.add (.mul (.var 0) (.var 4))
        (.mul (.mul (.const 6) (.var 1)) (.var 5))))
        (.neg (.mul (.var 0) (.mul (.var 3) (.var 3)))))
      (.add (.mul (.var 0) (.add (.mul (.var 2) (.var 4)) (.neg (.mul (.var 3) (.var 3)))))
        (.mul (.mul (.mul (.const 6) (.var 1)) (.var 2)) (.var 5)))
      (by decide) (fun
        | 0 => a*a+24*a*t
        | 1 => t
        | 2 => S
        | 3 => M
        | 4 => Q
        | _ => (C-t*R)-O)
  exact Q'.eqv_trans _ _ _ hr (Q'.eqv_trans _ _ _ hs hf)

/-- Exact ORIGINAL energy, with raw mean and remaining square/Gram credits explicit. -/
theorem padded_family_energy_connected_identity (w : Q') (K : Nat)
    {base width : Nat} (hwidth : base < width) (depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let h := (1 : Q')-w
    let t := HalfPow.half*(h*h)
    let a := h-19*t
    let S := familyChannelSourceMass w K width depth qs
    let M := familyChannelSourceMoment w K width depth c qs
    6*t*S*energy w K width (terminalMessage w K width depth) (spatialSpan width c qs)+
        144*t*t*M*M+familyChannelConnectedResidual w K width depth c qs a t ≈
      (a*a+24*a*t)*familyChannelConnectedDeterminant w K width depth c qs+
        6*t*S*((signedFamilyCubic w K width depth c qs-
          t*familyChannelPairRemainder w K width depth c qs)-
          signedFamilyOmitted w K width depth c qs) := by
  dsimp only
  exact energy_centering _ _ _ _ _ _ _ _ _ _
    (padded_family_energy_coercivity_identity w K hwidth depth c qs hqs)

private theorem normalized_centering (a t S M Q C R E D r delta V : Q')
    (h : 6*t*E+D*r ≤ ((a*a+24*a*t)*Q+6*t*(C-t*R))*r+(6*t*delta)*V)
    (hS : (0 : Q') ≤ S) :
    6*t*S*E+(144*t*t*M*M+(S*D-((a+12*t)*(a+12*t))*(M*M)))*r ≤
      ((a*a+24*a*t)*(S*Q-M*M)+6*t*S*(C-t*R))*r+(6*t*S*delta)*V := by
  have hs := Q'.add_le_add_right _ _ (-((a*a+24*a*t)*(M*M)*r))
    (Q'.mul_le_mul_of_nonneg_left _ _ S h hS)
  let A : PolyExpr := .var 0
  let T : PolyExpr := .var 1
  let Se : PolyExpr := .var 2
  let Me : PolyExpr := .var 3
  let Ee : PolyExpr := .var 4
  let De : PolyExpr := .var 5
  let Re : PolyExpr := .var 6
  let Ke : PolyExpr := .add (.mul A A) (.mul (.mul (.const 24) A) T)
  let Ve : PolyExpr := .add A (.mul (.const 12) T)
  let env : Nat → Q' := fun
    | 0 => a
    | 1 => t
    | 2 => S
    | 3 => M
    | 4 => E
    | 5 => D
    | _ => r
  have hl : 6*t*S*E+(144*t*t*M*M+(S*D-((a+12*t)*(a+12*t))*(M*M)))*r ≈
      S*(6*t*E+D*r)+(-((a*a+24*a*t)*(M*M)*r)) :=
    poly_identity_of_normal_eq
      (.add (.mul (.mul (.mul (.const 6) T) Se) Ee)
        (.mul (.add (.mul (.mul (.mul (.mul (.const 144) T) T) Me) Me)
          (.add (.mul Se De) (.neg (.mul (.mul Ve Ve) (.mul Me Me))))) Re))
      (.add (.mul Se (.add (.mul (.mul (.const 6) T) Ee) (.mul De Re)))
        (.neg (.mul (.mul Ke (.mul Me Me)) Re))) (by decide) env
  have hr : S*(((a*a+24*a*t)*Q+6*t*(C-t*R))*r+(6*t*delta)*V)+
        (-((a*a+24*a*t)*(M*M)*r)) ≈
      ((a*a+24*a*t)*(S*Q-M*M)+6*t*S*(C-t*R))*r+(6*t*S*delta)*V :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 2) (.add (.mul (.add (.mul (.var 0) (.var 4))
        (.mul (.mul (.const 6) (.var 1)) (.var 5))) (.var 6))
        (.mul (.mul (.mul (.const 6) (.var 1)) (.var 7)) (.var 8))))
        (.neg (.mul (.mul (.var 0) (.mul (.var 3) (.var 3))) (.var 6))))
      (.add (.mul (.add (.mul (.var 0) (.add (.mul (.var 2) (.var 4))
        (.neg (.mul (.var 3) (.var 3)))))
        (.mul (.mul (.mul (.const 6) (.var 1)) (.var 2)) (.var 5))) (.var 6))
        (.mul (.mul (.mul (.mul (.const 6) (.var 1)) (.var 2)) (.var 7)) (.var 8)))
      (by decide) (fun
        | 0 => a*a+24*a*t
        | 1 => t
        | 2 => S
        | 3 => M
        | 4 => Q
        | 5 => C-t*R
        | 6 => r
        | 7 => delta
        | _ => V)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hr))

/-- SAME original partition/OWN variance at the existing computed cutoff.
Only omitted loss is paid; the connected signed numerator remains UNPAID. -/
theorem normalizedEnergy_connected_cutoff_payment {w delta : Q'}
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
    let S := familyChannelSourceMass w K width (n+1) qs
    let M := familyChannelSourceMoment w K width (n+1) c qs
    6*t*S*normalizedEnergy hw0 hw1 K width hhead (n+1) (spatialSpan width c qs)+
        (144*t*t*M*M+familyChannelConnectedResidual w K width (n+1) c qs a t)*r ≤
      ((a*a+24*a*t)*familyChannelConnectedDeterminant w K width (n+1) c qs+
        6*t*S*(signedFamilyCubic w K width (n+1) c qs-
          t*familyChannelPairRemainder w K width (n+1) c qs))*r+
        (6*t*S*delta)*oddVariance hw0 hw1 K width hhead (n+1) (spatialSpan width c qs) := by
  dsimp only
  exact normalized_centering _ _ _ _ _ _ _ _ _ _ _ _
    (normalizedEnergy_coercivity_cutoff_payment hw0 hw1 hdelta hwidth c qs hqs hB K hK n)
    (familyChannelSourceMass_nonnegative (Q'.le_of_lt hw0) K width (n+1) qs)

#print axioms familyChannelSourceMass
#print axioms familyChannelSourceMoment
#print axioms familyChannelConnectedDeterminant
#print axioms familyChannelConnectedResidual
#print axioms familyChannelSourceMass_nonnegative
#print axioms familyChannelConnectedDeterminant_nonnegative
#print axioms family_channel_connected_coercivity
#print axioms familyChannelConnectedResidual_nonnegative
#print axioms padded_family_energy_connected_identity
#print axioms normalizedEnergy_connected_cutoff_payment

end YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyConnectedCoercivity
