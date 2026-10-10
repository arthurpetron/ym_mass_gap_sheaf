/-
# ORIGINAL signed family energy with omitted modes paid

The exact original energy identity keeps its favorable retained-square slack.
The new computed general-family cutoff pays ONLY the signed omitted loss by
delta times the SAME OWN-centered interacting variance. The remaining complete
signed expression is explicit and UNPAID. The concrete padded ALL-face family
constructs the required bare norm; no analytic input is added.

This is an initial spatial-family result at fixed nome/full width/family,
uniform in positive terminal depth. Temporal smoothing, complete signed cost,
chronological mass conversion and changing-family/scaling remain OPEN.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyOmittedPayment

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyEnergyPayment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyCurvature
  (familyChannelGradient familyChannelPairRemainder)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyEnergy
  (signedFamilyCubic signedFamilyOmitted signedFamilyRetainedSlack
    padded_family_energy_signed_exact)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareGram
  (padded_all_faces_square_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyOmittedPayment
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] baseLinks terminalMessage oddMass oddVariance
  signedFamilyOmitted signedFamilyRetainedSlack familyChannelGradient
  familyChannelPairRemainder signedFamilyCubic energy

/-- Remaining actual signed cost, keeping the nonnegative-slack CREDIT.
It is not claimed bounded, nonpositive, or relative to OWN variance. -/
def remainingFamilyEnergy (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  ((h-19*t)*familyChannelGradient w K width depth c qs+
    (signedFamilyCubic w K width depth c qs-t*familyChannelPairRemainder w K width depth c qs))-
    t*signedFamilyRetainedSlack w K width depth c qs

/-- Lossless separation on the SAME original unfiltered transfer energy. -/
theorem energy_eq_remaining (w : Q') (K : Nat) {base width : Nat}
    (hwidth : base < width) (depth : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    energy w K width (terminalMessage w K width depth) (spatialSpan width c qs) ≈
      remainingFamilyEnergy w K width depth c qs+(-signedFamilyOmitted w K width depth c qs) :=
  Q'.eqv_trans _ _ _ (padded_family_energy_signed_exact w K hwidth depth c qs hqs)
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.add (.var 1) (.neg (.var 2)))) (.neg (.var 3)))
      (.add (.add (.add (.var 0) (.var 1)) (.neg (.var 3))) (.neg (.var 2)))
      (by decide) (fun
        | 0 => ((1-w)-19*(HalfPow.half*((1-w)*(1-w))))*familyChannelGradient w K width depth c qs
        | 1 => signedFamilyCubic w K width depth c qs-
            (HalfPow.half*((1-w)*(1-w)))*familyChannelPairRemainder w K width depth c qs
        | 2 => signedFamilyOmitted w K width depth c qs
        | _ => (HalfPow.half*((1-w)*(1-w)))*signedFamilyRetainedSlack w K width depth c qs))

/-- Exact energy join with only omitted loss paid. Every positive depth uses
one produced cutoff; the remaining signed cost is NOT paid by this theorem. -/
theorem normalizedEnergy_signed_cutoff_payment {w delta : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hdelta : (0 : Q') < delta)
    {base width : Nat} (hwidth : base < width) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)
    (hB : (0 : Q') < familyBareNorm width c qs) (K : Nat)
    (hK : omittedPaymentCutoff hw0 hw1 width c qs hB delta ≤ K) (n : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_omittedPaymentCutoff hw0 hw1 width c qs hB delta) hK
    normalizedEnergy hw0 hw1 K width hhead (n+1) (spatialSpan width c qs) ≤
      remainingFamilyEnergy w K width (n+1) c qs*
        Q'.recipPos (oddMass w K width (n+1)) (oddMass_positive hw0 hw1 K width hhead (n+1))+
      delta*oddVariance hw0 hw1 K width hhead (n+1) (spatialSpan width c qs) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_omittedPaymentCutoff hw0 hw1 width c qs hB delta) hK
  let a := Q'.recipPos (oddMass w K width (n+1)) (oddMass_positive hw0 hw1 K width hhead (n+1))
  let D := remainingFamilyEnergy w K width (n+1) c qs
  let O := -signedFamilyOmitted w K width (n+1) c qs
  have he := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ a (energy_eq_remaining w K hwidth (n+1) c qs hqs))
    (Q'.add_mul_eqv D O a)
  have ho := normalized_signedFamilyOmitted_le_variance hw0 hw1 hdelta width c qs
    (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp)) hB K hK n
  have hs := Q'.add_le_add_left (D*a) _ _ ho
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hs

/-- Concrete unit ALL-face consumer; the norm guard is produced from the
original physical face Gram, not assumed as survival of a warmed family. -/
theorem allFaces_normalizedEnergy_signed_cutoff_payment {w delta : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hdelta : (0 : Q') < delta)
    (base width : Nat) (hbase : 0 < base) (hwidth : base < width) (K : Nat)
    (hK : allFacesPaymentCutoff hw0 hw1 base width hbase hwidth delta ≤ K) (n : Nat) :
    let hhead : headCutoff w ≤ K := Nat.le_trans (Nat.le_max_left _ _) hK
    normalizedEnergy hw0 hw1 K width hhead (n+1)
        (spatialSpan width (fun _ => 1) (spatialFaces base)) ≤
      remainingFamilyEnergy w K width (n+1) (fun _ => 1) (spatialFaces base)*
        Q'.recipPos (oddMass w K width (n+1)) (oddMass_positive hw0 hw1 K width hhead (n+1))+
      delta*oddVariance hw0 hw1 K width hhead (n+1)
        (spatialSpan width (fun _ => 1) (spatialFaces base)) :=
  normalizedEnergy_signed_cutoff_payment hw0 hw1 hdelta hwidth (fun _ => 1) (spatialFaces base)
    (fun _ hp => hp) (padded_all_faces_square_positive base width hbase (Nat.le_of_lt hwidth)) K hK n

#print axioms remainingFamilyEnergy
#print axioms energy_eq_remaining
#print axioms normalizedEnergy_signed_cutoff_payment
#print axioms allFaces_normalizedEnergy_signed_cutoff_payment

end YMGap.Continuum.BF4ExactSlabFixedSpatialSignedFamilyEnergyPayment
