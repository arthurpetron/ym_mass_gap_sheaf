/-
# Quantitative retained gain of the SAME passive angular channels

The vacuum contribution is the literal conditional Haar projection of the
supplied source. Nonvacuum channels receive at most w^3; the existing
nome-one Bessel inequality supplies the raw source-square ceiling. This
improves coefficient-one contraction without a channel-count or spatial-size
factor. Raw source-square angular energy is NOT interacting variance, and
no lower comparison with that variance or scaling smallness is asserted.
-/

import YMGap.Continuum.SU2QuaternionProductHeatChannelVacuum
import YMGap.Continuum.SU2QuaternionPassiveChannelAngularBudget
import YMGap.Constructive.AbsQ

namespace YMGap.Continuum.SU2QuaternionPassiveChannelStrictAngular

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionPassiveChannelAngularBudget
open YMGap.Continuum.SU2QuaternionProductHeatChannelVacuum
open YMGap.Continuum.SU2QuaternionProductHeatChannelNomeComparison
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem angular_source_congr (tail : Nat) {a b : RatPoly}
    (h : RatPolyCoeffEqv a b) (f : RatPoly) :
    weightedAngularEnergy tail a f ≈ weightedAngularEnergy tail b f :=
  finSum_eqv_congr _ _ (fun _ => haar_of_coeff ((h.mul h).mul_right _)) _

private theorem angular_source_zero (tail : Nat) (f : RatPoly) :
    weightedAngularEnergy tail polyZero f ≈ 0 := by
  change finSum (fun _ => (0 : Q')) (tail+1) ≈ 0
  rw [finSum_zero_seq]
  exact Q'.eqv_refl _

private theorem projection_zero : ∀ ids : List Nat,
    RatPolyCoeffEqv (familyProject ids polyZero) polyZero
  | [] => .refl _
  | _::ids => projection_zero ids

/-- Positivity is supplied by the six ORIGINAL supported angular squares,
not a blanket assumption about out-of-carrier polynomial functionals. -/
theorem weightedAngularEnergy_nonnegative (tail : Nat) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    (0 : Q') ≤ weightedAngularEnergy tail a f := by
  have hblock : ∀ block, block < tail+1 →
      (0 : Q') ≤ quaternionHaar (tail+1)
        (polyMul (polyMul a a) (blockAngularSquare block f)) := by
    intro block hb
    let planes := fun i j => quaternionHaar (tail+1)
      (polyMul (polyMul a a)
        (polyMul (blockAngularDerivative block i j f) (blockAngularDerivative block i j f)))
    have hp : ∀ i j, i < 4 → j < 4 → (0 : Q') ≤ planes i j := by
      intro i j hi hj
      exact ((Certificate.square a ha).mul (Certificate.square _
        (angularDerivative_supported_at (by omega) (by omega) hf))).haar_nonnegative
    have hz : sixValue (fun _ _ => (0 : Q')) ≈ 0 := by decide
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hz)
      (Q'.le_trans' _ _ _ (sixValue_mono _ _ hp)
        (Q'.ge_of_eqv (haar_six (tail+1) (polyMul a a) _)))
  have h := finSum_le_lt (fun _ => (0 : Q'))
    (fun i => quaternionHaar (tail+1) (polyMul (polyMul a a) (blockAngularSquare i f)))
    (tail+1) hblock
  rw [finSum_zero_seq] at h
  exact h

/-- The actual zero-nome angular channel contribution, with all selected
coordinates integrated by the original conditional Haar projection. -/
theorem channel_angular_zero_nome (tail K : Nat) (ids : List Nat) (q f : RatPoly) :
    channelSum (productChannels (tail+1) 0 K ids)
      (fun c => weightedAngularEnergy tail (channelSource ids q c) f) ≈
      weightedAngularEnergy tail (familyProject ids q) f := by
  let F := fun c => weightedAngularEnergy tail (channelSource ids q c) f
  have hF : ∀ p r, RatPolyCoeffEqv p r → F p ≈ F r :=
    fun p r h => angular_source_congr tail (familyProject_congr ids (h.mul_left q)) f
  have hz : F polyZero ≈ 0 :=
    Q'.eqv_trans _ _ _ (angular_source_congr tail
      ((familyProject_congr ids (RatPolyCoeffEqv.mul_zero_right q)).trans
        (projection_zero ids)) f) (angular_source_zero tail f)
  exact Q'.eqv_trans _ _ _ (productChannels_zero_nome (tail+1) K ids F hF hz)
    (angular_source_congr tail (familyProject_congr ids (RatPolyCoeffEqv.mul_one q)) f)

/-- The passive vacuum-channel cost is at most the original raw cost. Thus
their difference is a genuine nonnegative budget, not an assumed reserve. -/
theorem channel_angular_vacuum_le_raw (tail K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < tail+1) (hnd : ids.Nodup)
    (q f : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hind : ∀ i, i ∈ ids → QuaternionBlockIndependent i f) :
    weightedAngularEnergy tail (familyProject ids q) f ≤ weightedAngularEnergy tail q f :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (channel_angular_zero_nome tail K ids q f))
    (channelSource_weightedAngularEnergy_le tail (Q'.le_refl' 0) (by decide : (0 : Q') ≤ 1)
      K ids hids hnd q f hq hf hind)

/-- Quantitative nonvacuum attenuation of the COMPLETE angular channel sum.
No cutoff guard enters; distinctness is used only by the actual Bessel
consumer at nome one. The SAME signed source and observable remain fixed. -/
theorem channel_angular_vacuum_bound (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < tail+1) (hnd : ids.Nodup)
    (q f : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hind : ∀ i, i ∈ ids → QuaternionBlockIndependent i f) :
    channelSum (productChannels (tail+1) w K ids)
      (fun c => weightedAngularEnergy tail (channelSource ids q c) f) ≤
      ((1 : Q')-qpow w 3)*weightedAngularEnergy tail (familyProject ids q) f +
        qpow w 3*weightedAngularEnergy tail q f := by
  let F := fun c => weightedAngularEnergy tail (channelSource ids q c) f
  have hp : ∀ p, SupportedQuaternionBlocks (tail+1) p → (0 : Q') ≤ F p :=
    fun p hs => weightedAngularEnergy_nonnegative tail _ f
      (familyProject_supported ids (supported_polyMul hq hs)) hf
  have h := productChannels_nome_interpolation (tail+1) hw0 hw1 K ids hids F hp
  have hv := channel_angular_zero_nome tail K ids q f
  have h1 := channelSource_weightedAngularEnergy_le tail (by decide : (0 : Q') ≤ 1)
    (Q'.le_refl' 1) K ids hids hnd q f hq hf hind
  exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ hv) (Q'.eqv_refl _)))
    (Q'.add_le_add (Q'.le_refl' _)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ h1 (qpow_nonneg w hw0 3))))

/-- The retained source/channel loss pays an explicit fraction of the SAME
raw-minus-vacuum angular cost. Its comparison with interacting variance is
NOT assumed. All signed cross terms remain in each complete square. -/
theorem channel_angular_gain_lower (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < tail+1) (hnd : ids.Nodup)
    (q f : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hind : ∀ i, i ∈ ids → QuaternionBlockIndependent i f) :
    ((1 : Q')-qpow w 3)*(weightedAngularEnergy tail q f -
      weightedAngularEnergy tail (familyProject ids q) f) ≤
      weightedAngularEnergy tail q f -
        channelSum (productChannels (tail+1) w K ids)
          (fun c => weightedAngularEnergy tail (channelSource ids q c) f) := by
  let A := weightedAngularEnergy tail q f
  let V := weightedAngularEnergy tail (familyProject ids q) f
  have h := channel_angular_vacuum_bound tail hw0 hw1 K ids hids hnd q f hq hf hind
  have hsub := Q'.add_le_add (Q'.le_refl' A) (Q'.neg_le_neg h)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (poly_identity_of_normal_eq
    (.add (.var 0) (.neg (.add
      (.mul (.add (.const 1) (.neg (.var 2))) (.var 1)) (.mul (.var 2) (.var 0)))))
    (.mul (.add (.const 1) (.neg (.var 2))) (.add (.var 0) (.neg (.var 1))))
    (by decide) (fun | 0 => A | 1 => V | _ => qpow w 3))) hsub

#print axioms weightedAngularEnergy_nonnegative
#print axioms channel_angular_zero_nome
#print axioms channel_angular_vacuum_le_raw
#print axioms channel_angular_vacuum_bound
#print axioms channel_angular_gain_lower

end YMGap.Continuum.SU2QuaternionPassiveChannelStrictAngular
