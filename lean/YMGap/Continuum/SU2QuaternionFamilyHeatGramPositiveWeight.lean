/-
# Positive spectator weights in the full finite Gram-channel contraction

The weight is a genuinely certified polynomial independent of the selected
heat blocks. Its certificate need not have independent square generators.
The proof uses the complete doubled heat kernel and a partial-swap square;
it does not assume an analytic bound on the channel sum.
-/

import YMGap.Continuum.SU2QuaternionPartialSwapHeat
import YMGap.Continuum.SU2QuaternionFamilyChannelCone
import YMGap.Continuum.SU2QuaternionProductHeatContraction
import YMGap.Continuum.SU2QuaternionHaarCertificateExtension

namespace YMGap.Continuum.SU2QuaternionFamilyHeatGramPositiveWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionPartialSliceSwap
open YMGap.Continuum.SU2QuaternionPartialSwapHeat
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionFamilyChannelCone
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem support_lower {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks (n+n) p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))

private theorem support_neg {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  exact hp r hr

private theorem haar_neg (n : Nat) (p : RatPoly) : H n (polyNeg p) ≈ -(H n p) := by
  have h := quaternionHaar_polySmul n (-1) p
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (YMGap.Continuum.QuaternionHaarAngularCarrier.neg_smul p))
    (Q'.eqv_trans _ _ _ h
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => H n p)))

private theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (channelSum_congr left right cs
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

/- The existing conditional-kernel identity pins the mixed term in the
partial-swap square to the SAME channel family. -/
private theorem weighted_cross_pin (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (q e : RatPoly) (hq : SupportedQuaternionBlocks n q)
    (he : SupportedQuaternionBlocks n e)
    (hind : ∀ i, i ∈ ids → QuaternionBlockIndependent i e) :
    H (n+n) (polyMul (productHeat n w K ids)
      (polyMul (polyMul q (reindexQuaternionPolynomial (swap n ids) q)) e)) ≈
      channelSum (productChannels n w K ids) (fun c =>
        H n (polyMul
          (polyMul (familyProject ids (polyMul q c))
            (familyProject ids (polyMul q c))) e)) := by
  let s := swap n ids
  have hpair := familyChannelPair_eq_conditionalKernel n w K ids hn hids
    (polyMul q e) q (supported_polyMul hq he) hq
  have hleft : H (n+n) (polyMul (productHeat n w K ids)
      (polyMul (polyMul q (reindexQuaternionPolynomial s q)) e)) ≈
      H (n+n) (polyMul (productHeat n w K ids)
        (polyMul (polyMul q e) (reindexQuaternionPolynomial s q))) :=
    haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 3)) (.var 2)))
      (by decide) (fun | 0 => productHeat n w K ids | 1 => q
                       | 2 => reindexQuaternionPolynomial s q | _ => e))
  have hright : familyChannelPair n w K ids (polyMul q e) q ≈
      channelSum (productChannels n w K ids) (fun c =>
        H n (polyMul
          (polyMul (familyProject ids (polyMul q c))
            (familyProject ids (polyMul q c))) e)) := by
    unfold familyChannelPair
    apply channelSum_congr
    intro c hc
    let b := familyProject ids (polyMul q c.2)
    have hraw : RatPolyCoeffEqv (polyMul (polyMul q e) c.2)
        (polyMul e (polyMul q c.2)) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => q | 1 => e | _ => c.2)
    have hp : RatPolyCoeffEqv
        (familyProject ids (polyMul (polyMul q e) c.2)) (polyMul e b) :=
      (familyProject_congr ids hraw).trans
        (familyProject_mul_of_independent ids e (polyMul q c.2) hind)
    exact haar_of_coeff
      ((hp.mul (RatPolyCoeffEqv.refl b)).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.mul (.var 1) (.var 2)) (.var 0))
          (by decide) (fun | 0 => e | 1 => b | _ => b)))
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ hpair.symm hright)

/-- Coefficient-one weighted Bessel contraction for the *actual* selected
product heat channels. The positive weight is certified as a whole; its
individual square witnesses need not be independent of the selected blocks. -/
theorem productChannels_familyProject_positiveWeighted_square_le
    (n : Nat) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison.headCutoff w ≤ K)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (q e : RatPoly) (hq : SupportedQuaternionBlocks n q)
    (he : SupportedQuaternionBlocks n e) (E : Certificate n e)
    (hind : ∀ i, i ∈ ids → QuaternionBlockIndependent i e) :
    channelSum (productChannels n w K ids) (fun c =>
      H n (polyMul
        (polyMul (familyProject ids (polyMul q c))
          (familyProject ids (polyMul q c))) e)) ≤
      H n (polyMul (polyMul q q) e) := by
  let s := swap n ids
  let k := productHeat n w K ids
  let q' := reindexQuaternionPolynomial s q
  let d := polyAdd q (polyNeg q')
  let a := H n (polyMul (polyMul q q) e)
  let c := channelSum (productChannels n w K ids) (fun z =>
    H n (polyMul
      (polyMul (familyProject ids (polyMul q z))
        (familyProject ids (polyMul q z))) e))
  let lower := polyMul k (polyMul (polyMul q q) e)
  let upper := polyMul k (polyMul (polyMul q' q') e)
  let mixed := polyMul k (polyMul (polyMul q q') e)
  let square := polyMul k (polyMul (polyMul d d) e)
  have hq' : SupportedQuaternionBlocks (n+n) q' := reindex_supported s q
  have hd : SupportedQuaternionBlocks (n+n) d :=
    supported_add (support_lower hq) (support_neg hq')
  have hsquare : Certificate (n+n) square :=
    (productHeatCertificate n hw0 hw1 K hK ids hids).mul
      ((Certificate.square d hd).mul (certificate_extend n he E))
  have hnonneg : (0 : Q') ≤ H (n+n) square := hsquare.haar_nonnegative
  have hlower : H (n+n) lower ≈ a := by
    have hp := productHeat_lower_marginal n w K ids hn hids
      (polyMul (polyMul q q) e)
      (supported_polyMul (supported_polyMul hq hq) he)
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.refl lower)) hp
  have hcross : H (n+n) mixed ≈ c :=
    weighted_cross_pin n w K ids hn hids q e hq he hind
  have hfixed : PaddedPolynomialCoeffEqv (n+n)
      (reindexQuaternionPolynomial s e) e :=
    PaddedPolynomialCoeffEqv.of_prefix
      (reindex_fixed_prefix n ids e he (fun i _ hi => hind i hi))
  have hkernel := productHeat_partialSwap n w K ids hids
  have hq'pair : PaddedPolynomialCoeffEqv (n+n)
      (reindexQuaternionPolynomial s lower) upper := by
    dsimp only [lower, upper, q', k]
    simp only [reindexQuaternionPolynomial_mul]
    exact hkernel.mul (((PaddedPolynomialCoeffEqv.refl _ _).mul
      (PaddedPolynomialCoeffEqv.refl _ _)).mul hfixed)
  have hlowerSupport : SupportedQuaternionBlocks (n+n) lower :=
    supported_polyMul (productHeat_supported n w K ids hids)
      (supported_polyMul (supported_polyMul (support_lower hq) (support_lower hq))
        (support_lower he))
  have hupperSupport : SupportedQuaternionBlocks (n+n) upper :=
    supported_polyMul (productHeat_supported n w K ids hids)
      (supported_polyMul (supported_polyMul hq' hq') (support_lower he))
  have hupper : H (n+n) upper ≈ a :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (hq'pair.haar (reindex_supported s lower) hupperSupport))
      (Q'.eqv_trans _ _ _ (quaternionHaar_reindex s lower hlowerSupport) hlower)
  have hexpand : H (n+n) square ≈
      H (n+n) lower + (H (n+n) upper + -((2 : Q') * H (n+n) mixed)) := by
    have hp0 : RatPolyCoeffEqv square
        (polyAdd lower (polyAdd upper (polyNeg (polyMul (cap 2) mixed)))) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0)
          (.mul (.mul (.add (.var 1) (.neg (.var 2)))
            (.add (.var 1) (.neg (.var 2)))) (.var 3)))
        (.add (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 3)))
          (.add (.mul (.var 0) (.mul (.mul (.var 2) (.var 2)) (.var 3)))
            (.neg (.mul (.const 2)
              (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))))))
        (by decide) (fun | 0 => k | 1 => q | 2 => q' | _ => e)
    have hp : RatPolyCoeffEqv square
        (polyAdd lower (polyAdd upper (polyNeg (polySmul 2 mixed)))) :=
      hp0.trans ((RatPolyCoeffEqv.refl lower).add
        ((RatPolyCoeffEqv.refl upper).add (RatPolyCoeffEqv.neg (cap_mul_left 2 mixed))))
    exact Q'.eqv_trans _ _ _ (haar_of_coeff hp)
      (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
            (Q'.add_eqv_congr' (Q'.eqv_refl _)
              (Q'.eqv_trans _ _ _ (haar_neg _ _)
                (Q'.neg_eqv_congr _ _ (quaternionHaar_polySmul _ 2 _)))))))
  have htwo : H (n+n) square ≈ (2 : Q') * (a-c) :=
    Q'.eqv_trans _ _ _ hexpand
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' hlower
          (Q'.add_eqv_congr' hupper
            (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left 2 _ _ hcross))))
        (poly_identity_of_normal_eq
          (.add (.var 0) (.add (.var 0) (.neg (.mul (.const 2) (.var 1)))))
          (.mul (.const 2) (.add (.var 0) (.neg (.var 1))))
          (by decide) (fun | 0 => a | _ => c)))
  have hmul : (2 : Q') * (0 : Q') ≤ 2 * (a-c) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_zero_eqv 2).symm)
      (Q'.le_trans' _ _ _ hnonneg (Q'.le_of_eqv htwo))
  have hsub : (0 : Q') ≤ a-c :=
    Q'.le_of_mul_le_mul_left hmul (by decide : (0 : Q') < 2)
  exact Q'.le_of_sub_nonneg hsub

#print axioms productChannels_familyProject_positiveWeighted_square_le

end YMGap.Continuum.SU2QuaternionFamilyHeatGramPositiveWeight
