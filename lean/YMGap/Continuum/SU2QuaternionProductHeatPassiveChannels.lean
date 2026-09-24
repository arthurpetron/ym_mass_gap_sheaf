/-
# Exact passive-channel reduction of the ORIGINAL source energy

Expand only the passive heat factors into their computed positive Gram
channels. Each channel multiplies BOTH endpoints of the complete source.
The existing inactive-coordinate identity then integrates that channel
source, not the original source with the passive heat factors discarded.

All inactive-independent moments and the full signed temporal energy are
preserved. This supplies actual finite sources for localized Taylor bounds;
it does not bound their total budget uniformly in volume, nome or cutoff.
-/

import YMGap.Continuum.SU2QuaternionProductHeatGramChannels
import YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder

namespace YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private def kernelPair (n : Nat) (W a b : RatPoly) : Q' :=
  H (n+n) (polyMul W (polyMul a (liftBoundary n b)))

private theorem kernelPair_coeff (n : Nat) {W V : RatPoly}
    (h : RatPolyCoeffEqv W V) (a b : RatPoly) :
    kernelPair n W a b ≈ kernelPair n V a b :=
  haar_of_coeff (h.mul_right _)

private theorem kernelPair_carrier (n : Nat) {W V : RatPoly}
    (h : HaarCarrierEqv (n+n) W V) (a b : RatPoly) :
    kernelPair n W a b ≈ kernelPair n V a b :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ (h (polyMul a (liftBoundary n b)))
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))

private theorem kernelPair_add (n : Nat) (W V a b : RatPoly) :
    kernelPair n (polyAdd W V) a b ≈
      kernelPair n W a b + kernelPair n V a b :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 0) (.var 1)) (.var 2))
    (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2))) (by decide)
    (fun | 0 => W | 1 => V | _ => polyMul a (liftBoundary n b))))
    (quaternionHaar_append _ _ _)

private theorem kernelPair_smul (n : Nat) (W a b : RatPoly) (c : Q') :
    kernelPair n (polySmul c W) a b ≈ c * kernelPair n W a b :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c _ _))
    (quaternionHaar_polySmul _ _ _)

private theorem kernelPair_channel (n : Nat) (W a b c : RatPoly) :
    kernelPair n (polyMul W (polyMul c (liftBoundary n c))) a b ≈
      kernelPair n W (polyMul a c) (polyMul b c) := by
  unfold kernelPair
  rw [lift_product]
  exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.mul (.var 3) (.var 4)))
      (.mul (.var 1) (.var 2)))
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 3))
      (.mul (.var 2) (.var 4)))) (by decide)
    (fun | 0 => W | 1 => a | 2 => liftBoundary n b
         | 3 => c | _ => liftBoundary n c))

/-- Computed weighted channel sum; the weights are NOT renormalized. -/
def channelSum (cs : List (Q' × RatPoly)) (value : RatPoly → Q') : Q' :=
  qListSum (cs.map fun c => c.1 * value c.2)

private theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List (Q' × RatPoly),
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (channelSum_congr left right cs (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_sub (left right : RatPoly → Q') :
    ∀ cs : List (Q' × RatPoly),
      channelSum cs left + -(channelSum cs right) ≈
        channelSum cs (fun c => left c + -(right c))
  | [] => by change (0 : Q') + -(0 : Q') ≈ 0; decide
  | c::cs => by
      change c.1*left c.2 + channelSum cs left +
        -(c.1*right c.2 + channelSum cs right) ≈
          c.1*(left c.2 + -(right c.2)) +
            channelSum cs (fun d => left d + -(right d))
      exact Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.add (.add (.mul (.var 0) (.var 1)) (.var 3))
            (.neg (.add (.mul (.var 0) (.var 2)) (.var 4))))
          (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
            (.add (.var 3) (.neg (.var 4)))) (by decide)
          (fun | 0 => c.1 | 1 => left c.2 | 2 => right c.2
               | 3 => channelSum cs left | _ => channelSum cs right))
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (channelSum_sub left right cs))

private theorem channelSum_le (left right : RatPoly → Q') :
    ∀ cs : List (Q' × RatPoly),
      (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
      (∀ c, c ∈ cs → left c.2 ≤ right c.2) →
      channelSum cs left ≤ channelSum cs right
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, h => Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (h c List.mem_cons_self) (hw c List.mem_cons_self))
      (channelSum_le left right cs (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem productPair_perm (n : Nat) (w : Q') (K : Nat)
    {left right : List Nat} (h : left.Perm right) (a b : RatPoly) :
    H n (polyMul b (productMap n w K left a)) ≈
      H n (polyMul b (productMap n w K right a)) :=
  Q'.eqv_trans _ _ _ (productMap_pairing n w K left a b)
    (Q'.eqv_trans _ _ _ (kernelPair_coeff n (polynomialProduct_perm _ h) a b)
      (productMap_pairing n w K right a b).symm)

private theorem sourceEnergy_perm (n : Nat) (w : Q') (K : Nat)
    {left right : List Nat} (h : left.Perm right) (a f : RatPoly) :
    sourceEnergy n w K left a f ≈ sourceEnergy n w K right a f :=
  Q'.add_eqv_congr' (productPair_perm n w K h a (polyMul a (polyMul f f)))
    (Q'.neg_eqv_congr _ _ (productPair_perm n w K h (polyMul a f) (polyMul a f)))

private theorem kernelPair_channels (n : Nat) (W a b : RatPoly) :
    ∀ cs : List (Q' × RatPoly),
      kernelPair n (polyMul W (channelKernel n cs)) a b ≈
        channelSum cs (fun c => kernelPair n W (polyMul a c) (polyMul b c))
  | [] => haar_of_coeff (((RatPolyCoeffEqv.mul_zero_right W).mul_right _).trans
      (RatPolyCoeffEqv.mul_zero_left _))
  | c::cs => by
      let p := polyMul c.2 (liftBoundary n c.2)
      have hdist := kernelPair_coeff n
        (RatPolyCoeffEqv.mul_add_right W (polySmul c.1 p) (channelKernel n cs)) a b
      have hscale := Q'.eqv_trans _ _ _
        (kernelPair_coeff n (RatPolyCoeffEqv.polyMul_smul_right c.1 W p) a b)
        (Q'.eqv_trans _ _ _ (kernelPair_smul n (polyMul W p) a b c.1)
          (Q'.mul_eqv_congr_left _ _ _ (kernelPair_channel n W a b c.2)))
      exact Q'.eqv_trans _ _ _ hdist
        (Q'.eqv_trans _ _ _ (kernelPair_add n _ _ a b)
          (Q'.add_eqv_congr' hscale (kernelPair_channels n W a b cs)))

private theorem productPair_passive (n : Nat) (w : Q') (K : Nat)
    (active passive : List Nat) (hpassive : ∀ i, i ∈ passive → i < n)
    (a b : RatPoly) :
    H n (polyMul b (productMap n w K (active++passive) a)) ≈
      channelSum (productChannels n w K passive) (fun c =>
        H n (polyMul (polyMul b c) (productMap n w K active (polyMul a c)))) := by
  have hprod : RatPolyCoeffEqv (productHeat n w K (active++passive))
      (polyMul (productHeat n w K active) (productHeat n w K passive)) :=
    polynomialProduct_append _ _ _
  have hgram := HaarCarrierEqv.mul_left (productHeat n w K active)
    (productHeat_gram_carrier n w K passive hpassive)
  exact Q'.eqv_trans _ _ _ (productMap_pairing n w K (active++passive) a b)
    (Q'.eqv_trans _ _ _ (kernelPair_coeff n hprod a b)
      (Q'.eqv_trans _ _ _ (kernelPair_carrier n hgram a b)
        (Q'.eqv_trans _ _ _ (kernelPair_channels n (productHeat n w K active) a b _)
          (channelSum_congr _ _ _ (fun c _ =>
            (productMap_pairing n w K active (polyMul a c.2) (polyMul b c.2)).symm)))))

/-- Every passive Gram channel dresses the complete source at BOTH endpoints.
This is equality of the original moment, with the original normalization. -/
theorem sourceMoment_passive_channels (n : Nat) (w : Q') (K : Nat)
    (active passive : List Nat) (hpassive : ∀ i, i ∈ passive → i < n)
    (a p : RatPoly) :
    sourceMoment n w K (active++passive) a p ≈
      channelSum (productChannels n w K passive) (fun c =>
        sourceMoment n w K active (polyMul a c) p) := by
  exact Q'.eqv_trans _ _ _ (productPair_passive n w K active passive hpassive a (polyMul a p))
    (channelSum_congr _ _ _ (fun c _ => haar_of_coeff
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
        (fun | 0 => a | 1 => p | _ => c.2)).mul_right _)))

/-- Exact signed energy decomposition; no cross term is discarded. -/
theorem sourceEnergy_passive_channels (n : Nat) (w : Q') (K : Nat)
    (active passive : List Nat) (hpassive : ∀ i, i ∈ passive → i < n)
    (a f : RatPoly) :
    sourceEnergy n w K (active++passive) a f ≈
      channelSum (productChannels n w K passive) (fun c =>
        sourceEnergy n w K active (polyMul a c) f) := by
  have hm := sourceMoment_passive_channels n w K active passive hpassive a (polyMul f f)
  have hp := productPair_passive n w K active passive hpassive (polyMul a f) (polyMul a f)
  have he := Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hm (Q'.neg_eqv_congr _ _ hp))
    (channelSum_sub _ _ _)
  exact Q'.eqv_trans _ _ _ he (channelSum_congr _ _ _ (fun c _ => by
    have hcomm : RatPolyCoeffEqv (polyMul (polyMul a f) c.2)
        (polyMul (polyMul a c.2) f) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
        (fun | 0 => a | 1 => f | _ => c.2)
    exact Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _
      (haar_of_coeff (hcomm.mul (productMap_congr n w K active hcomm))))))

/-- The actual projected source for one retained passive Gram channel. -/
def channelSource (passive : List Nat) (a c : RatPoly) : RatPoly :=
  familyProject passive (polyMul a c)

/-- Every passive coordinate has actually been integrated out of each source. -/
theorem channelSource_independent (passive : List Nat) (a c : RatPoly)
    (i : Nat) (hi : i ∈ passive) :
    QuaternionBlockIndependent i (channelSource passive a c) :=
  familyProject_independent passive (polyMul a c) i hi

/-- The same identity preserves mass and all allowed inserted moments, not
only the energy numerator. Weights retain the original partition factor. -/
theorem sourceMoment_projected_channels (n : Nat) (w : Q') (K : Nat)
    (active passive : List Nat) (hactive : ∀ i, i ∈ active → i < n)
    (hpassive : ∀ i, i ∈ passive → i < n)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive++active).Perm (List.range n)) (a p : RatPoly)
    (ha : SupportedQuaternionBlocks n a) (hp : SupportedQuaternionBlocks n p)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i p) :
    sourceMoment n w K (List.range n) a p ≈
      channelSum (productChannels n w K passive) (fun c =>
        sourceMoment n w K (List.range n) (channelSource passive a c) p) := by
  have hperm : (active++passive).Perm (List.range n) :=
    List.perm_append_comm.trans hcover
  exact Q'.eqv_trans _ _ _ (productPair_perm n w K hperm.symm a (polyMul a p))
    (Q'.eqv_trans _ _ _ (sourceMoment_passive_channels n w K active passive hpassive a p)
      (channelSum_congr _ _ _ (fun c hc =>
        sourceMoment_project n w K active passive hactive hpassive hnot hcover
          (polyMul a c.2) p (supported_polyMul ha
            (productChannels_supported n w K passive hpassive c hc)) hp hind)))

/-- Passive heat is retained exactly in the computed sources. Only the
observable must be independent of passive coordinates. -/
theorem sourceEnergy_projected_channels (n : Nat) (w : Q') (K : Nat)
    (active passive : List Nat) (hactive : ∀ i, i ∈ active → i < n)
    (hpassive : ∀ i, i ∈ passive → i < n)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive++active).Perm (List.range n)) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks n a) (hf : SupportedQuaternionBlocks n f)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i f) :
    sourceEnergy n w K (List.range n) a f ≈
      channelSum (productChannels n w K passive) (fun c =>
        sourceEnergy n w K (List.range n) (channelSource passive a c) f) := by
  have hperm : (active++passive).Perm (List.range n) :=
    List.perm_append_comm.trans hcover
  exact Q'.eqv_trans _ _ _ (sourceEnergy_perm n w K hperm.symm a f)
    (Q'.eqv_trans _ _ _ (sourceEnergy_passive_channels n w K active passive hpassive a f)
      (channelSum_congr _ _ _ (fun c hc =>
        sourceEnergy_project n w K active passive hactive hpassive hnot hcover
          (polyMul a c.2) f (supported_polyMul ha
            (productChannels_supported n w K passive hpassive c hc)) hf hind)))

/-- Positive-channel consumer of the proved angular/mixed-remainder bound.
The passive heat has NOT been Taylor-expanded. Its entire dependence is
retained in the positive weights and the computed integrated sources. No
uniform bound on this sum, or comparison with centered variance, is claimed. -/
theorem sourceEnergy_le_projected_channel_budgets (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (active passive : List Nat)
    (hactive : ∀ i, i ∈ active → i < tail+1)
    (hpassive : ∀ i, i ∈ passive → i < tail+1)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive++active).Perm (List.range (tail+1))) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i f) :
    sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≤
      channelSum (productChannels (tail+1) w K passive) (fun c =>
        ((1 : Q')-w) * weightedAngularEnergy tail (channelSource passive a c) f +
          (((1 : Q')-w)*((1 : Q')-w)) *
            pairBudget tail (channelSource passive a c)
              (polyMul (channelSource passive a c) (polyMul f f))) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (sourceEnergy_projected_channels (tail+1) w K active passive hactive hpassive
      hnot hcover a f ha hf hind))
    (channelSum_le _ _ _ (productChannels_nonnegative (tail+1) hw0 K passive)
      (fun c hc => sourceEnergy_le_angular_add_mixed_quadratic tail hw0 hw1 K hK
        (channelSource passive a c.2) f
        (familyProject_supported passive (supported_polyMul ha
          (productChannels_supported (tail+1) w K passive hpassive c hc))) hf))

end YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels

#print axioms YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels.sourceMoment_passive_channels
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels.sourceEnergy_passive_channels
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels.channelSource_independent
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels.sourceMoment_projected_channels
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels.sourceEnergy_projected_channels
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels.sourceEnergy_le_projected_channel_budgets
