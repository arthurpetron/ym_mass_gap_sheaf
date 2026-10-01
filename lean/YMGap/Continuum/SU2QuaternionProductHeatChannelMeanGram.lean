/-
# Exact spectator-channel mean squares and the constant-vector floor

The passive Gram identity, with no active heat factors, identifies the
selected-product kinetic square with a weighted sum of ordinary Haar mean
squares.  Cauchy--Schwarz in that same positive kinetic form, tested against
one, shows the sum dominates the square of the original Haar mean.  This is
not an interacting marginal or a variance-relative lower bound.
-/

import YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
import YMGap.Continuum.SU2QuaternionProductHeatDualForm
import YMGap.Continuum.SU2QuaternionProductHeatConstant

namespace YMGap.Continuum.SU2QuaternionProductHeatChannelMeanGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap_nil productMap)
open YMGap.Continuum.SU2QuaternionProductHeatConstant (productMap_one)
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (SupportedHaarEqv)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff supported_one)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QPolyHaarPositiveSubstitution (haar_one)

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

private theorem qmul_eqv_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

/-- The unnormalized finite Gram sum of ordinary Haar mean squares. -/
def channelMeanSquares (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (p : RatPoly) : Q' :=
  channelSum (productChannels n w K ids) (fun c =>
    H n (polyMul p c) * H n (polyMul p c))

private theorem sourceMoment_nil_square (n : Nat) (w : Q') (K : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks n p) :
    sourceMoment n w K [] p polyOne ≈ H n p * H n p := by
  let a := H n p
  have hnil := productMap_nil n w K p hp
  have hcoeff : RatPolyCoeffEqv
      (polyMul (polyMul p polyOne) (productMap n w K [] p))
      (polySmul a p) :=
    ((RatPolyCoeffEqv.mul_one p).mul hnil).trans
      ((RatPolyCoeffEqv.mul_comm p (cap a)).trans (cap_mul_left a p))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hcoeff)
    (quaternionHaar_polySmul n a p)

/-- The source-moment passive-channel identity with empty active set is an
exact Gram pin, not merely a Bessel upper bound. -/
theorem channelMeanSquares_pin (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (p : RatPoly) (hp : SupportedQuaternionBlocks n p) :
    kineticPair n w K ids p p ≈ channelMeanSquares n w K ids p := by
  have hsource : kineticPair n w K ids p p ≈
      sourceMoment n w K ids p polyOne := by
    unfold kineticPair sourceMoment
    exact haar_of_coeff (((RatPolyCoeffEqv.mul_one p).symm).mul_right _)
  have hchannels := sourceMoment_passive_channels n w K [] ids hids p polyOne
  have hpin : channelSum (productChannels n w K ids)
      (fun c => sourceMoment n w K [] (polyMul p c) polyOne) ≈
        channelMeanSquares n w K ids p := by
    unfold channelMeanSquares
    exact channelSum_congr _ _ _ (fun c hc =>
      sourceMoment_nil_square n w K (polyMul p c.2)
        (supported_polyMul hp
          (productChannels_supported n w K ids hids c hc)))
  exact Q'.eqv_trans _ _ _ hsource
    (Q'.eqv_trans _ _ _ hchannels hpin)

private theorem kineticPair_one_mean (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (p : RatPoly) (hp : SupportedQuaternionBlocks n p) :
    kineticPair n w K ids p polyOne ≈ H n p := by
  unfold kineticPair
  exact Q'.eqv_trans _ _ _ ((productMap_one n w K ids hnd hids) p hp)
    (haar_of_coeff (RatPolyCoeffEqv.mul_one p))

/-- The positive selected-product kinetic form dominates the square of the
original ordinary Haar mean.  No pointwise channel source sign is used. -/
theorem channelMeanSquares_ge_haar_square (n : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (K : Nat) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (p : RatPoly) (hp : SupportedQuaternionBlocks n p) :
    H n p * H n p ≤ channelMeanSquares n w K ids p := by
  let B := kineticPair n w K ids
  have hmean : B p polyOne ≈ H n p :=
    kineticPair_one_mean n w K ids hnd hids p hp
  have hunit : B polyOne polyOne ≈ 1 :=
    Q'.eqv_trans _ _ _
      (kineticPair_one_mean n w K ids hnd hids polyOne (supported_one n))
      (haar_one n)
  have hcs := kineticPair_cauchySchwarz n w hw0 K ids hids
    p polyOne hp (supported_one n)
  have hleft : H n p * H n p ≈ B p polyOne * B p polyOne :=
    qmul_eqv_congr (Q'.eqv_symm hmean) (Q'.eqv_symm hmean)
  have hright : B p p * B polyOne polyOne ≈ channelMeanSquares n w K ids p :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hunit)
      (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _)
        (channelMeanSquares_pin n w K ids hids p hp))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv hright))

/-- A spectator-independent observable may be pulled through the original
in-place Haar projection before taking each channel mean. -/
theorem channel_mean_projected (n : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) (q f c : RatPoly)
    (hind : ∀ i, i ∈ ids → QuaternionBlockIndependent i f) :
    H n (polyMul (polyMul q f) c) ≈
      H n (polyMul (channelSource ids q c) f) := by
  have hswap : RatPolyCoeffEqv (polyMul (polyMul q f) c)
      (polyMul f (polyMul q c)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => q | 1 => f | _ => c)
  have hpull := familyProject_mul_of_independent ids f (polyMul q c) hind
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hswap)
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (familyProject_mean n ids hids (polyMul f (polyMul q c))))
      (Q'.eqv_trans _ _ _ (haar_of_coeff hpull)
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm f (channelSource ids q c)))))

/-- The exact Gram sum for `q*f` uses the spectator-integrated source and
retains all signed cross terms already present in `f`. -/
theorem channelMeanSquares_projected_pin (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (q f : RatPoly)
    (hind : ∀ i, i ∈ ids → QuaternionBlockIndependent i f) :
    channelMeanSquares n w K ids (polyMul q f) ≈
      channelSum (productChannels n w K ids) (fun c =>
        H n (polyMul (channelSource ids q c) f) *
          H n (polyMul (channelSource ids q c) f)) := by
  unfold channelMeanSquares
  exact channelSum_congr _ _ _ (fun c _ =>
    qmul_eqv_congr
      (channel_mean_projected n ids hids q f c.2 hind)
      (channel_mean_projected n ids hids q f c.2 hind))

end YMGap.Continuum.SU2QuaternionProductHeatChannelMeanGram

#print axioms YMGap.Continuum.SU2QuaternionProductHeatChannelMeanGram.channelMeanSquares_pin
#print axioms YMGap.Continuum.SU2QuaternionProductHeatChannelMeanGram.channelMeanSquares_ge_haar_square
#print axioms YMGap.Continuum.SU2QuaternionProductHeatChannelMeanGram.channel_mean_projected
#print axioms YMGap.Continuum.SU2QuaternionProductHeatChannelMeanGram.channelMeanSquares_projected_pin
