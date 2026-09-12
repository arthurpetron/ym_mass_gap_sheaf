/-
# Mixed reflected channel pairings on the original odd-slab Haar carrier

Two lower-local polynomials have disjoint dependence after reflecting one
of them. Their mixed pairing factors into their own rational Haar values.
For every actual local square expansion, retaining two arbitrary lower
observables gives an explicit weighted sum of products of channel values.

This establishes symmetry of the full mixed pairing, not just positivity
of its diagonal. All shared lower-half variables remain inside each channel.
-/

import YMGap.Continuum.BF4ExactSlabLocalSquareExpansion

namespace YMGap.Continuum.BF4ExactSlabLocalBilinearChannels

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabLowerChannelLocality
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv

theorem lower_mixed_disjoint {half : Nat} {p q : RatPoly}
    (hp : LowerLocal half p) (hq : LowerLocal half q) :
    BlockDisjoint (boundaryCompleteSlabLinks (centralExtent half)).length
      (reflectCorrectedSlabPolynomial (centralExtent half) p) q := by
  have hu := lower_reflection_upper hp
  intro s hs t ht block hb
  haveI : Decidable (LowerBlock half block) := inferInstanceAs
    (Decidable (linkHalfSide half (correctedSlabLinkAt (centralExtent half) block) = .lower))
  by_cases hl : LowerBlock half block
  · apply Or.inl
    apply hu s hs block hb
    intro hup
    change linkHalfSide half (correctedSlabLinkAt (centralExtent half) block) = .upper at hup
    change linkHalfSide half (correctedSlabLinkAt (centralExtent half) block) = .lower at hl
    rw [hl] at hup
    cases hup
  · exact Or.inr (hq t ht block hb hl)

theorem lower_reflected_haar_pair {half : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length q)
    (hlp : LowerLocal half p) (hlq : LowerLocal half q) :
    quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) q) ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length p *
        quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length q :=
  Q'.eqv_trans _ _ _
    (haar_product (reflectCorrectedSlabPolynomial_support (centralExtent half) p) hq (lower_mixed_disjoint hlp hlq))
    (Q'.mul_eqv_congr_right _ _ _ (quaternionHaar_reflectCorrectedSlabPolynomial (centralExtent half) p hp))

private theorem channel_pair {half : Nat} {p q c : RatPoly}
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length q)
    (hc : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length c)
    (hlp : LowerLocal half p) (hlq : LowerLocal half q) (hlc : LowerLocal half c) :
    quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) q)
        (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) c) c)) ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (polyMul p c) *
        quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (polyMul q c) := by
  have h := (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.mul_four_swap
    (reflectCorrectedSlabPolynomial (centralExtent half) p) q
    (reflectCorrectedSlabPolynomial (centralExtent half) c) c)).trans
    (((PaddedPolynomialCoeffEqv.of_prefix (reflectCorrectedSlabPolynomial_mul_prefix
      (centralExtent half) p c)).symm).mul (PaddedPolynomialCoeffEqv.refl _ (polyMul q c)))
  have ht := h.haar
    (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ p) hq)
      (supported_polyMul (reflectCorrectedSlabPolynomial_support _ c) hc))
    (supported_polyMul (reflectCorrectedSlabPolynomial_support _ (polyMul p c)) (supported_polyMul hq hc))
  exact Q'.eqv_trans _ _ _ ht
    (lower_reflected_haar_pair (supported_polyMul hp hc) (supported_polyMul hq hc) (hlp.mul hlc) (hlq.mul hlc))

/-- Actual mixed channel values, preserving both supplied observables. -/
def channelBilinearValue (blocks : Nat) (p q : RatPoly) : SquareTree → Q'
  | .zero => 0
  | .term w c => w * (quaternionHaar blocks (polyMul p c) * quaternionHaar blocks (polyMul q c))
  | .add s t => channelBilinearValue blocks p q s + channelBilinearValue blocks p q t

theorem tree_mixed_pairing {half : Nat} (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length q)
    (hlp : LowerLocal half p) (hlq : LowerLocal half q) : ∀ t : SquareTree,
    SquareTreeSupported (boundaryCompleteSlabLinks (centralExtent half)).length t → LowerSquareTree half t →
    quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) q) (t.eval (centralExtent half))) ≈
      channelBilinearValue (boundaryCompleteSlabLinks (centralExtent half)).length p q t
  | .zero, _, _ => by
    have hz (r : RatPoly) : polyMul r polyZero = polyZero :=
      List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
    rw [SquareTree.eval, hz]
    exact Q'.eqv_refl _
  | .term w c, hc, hlc => by
    refine Q'.eqv_trans _ _ _ ?_ (Q'.mul_eqv_congr_left _ _ _ (channel_pair hp hq hc hlp hlq hlc))
    exact Q'.eqv_trans _ _ _
      ((PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.polyMul_smul_right w _ _)).haar
        (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ p) hq)
          (squareTree_eval_support _ (.term w c) hc))
        (by
          intro term ht
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
          exact supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ p) hq)
            (supported_polyMul (reflectCorrectedSlabPolynomial_support _ c) hc) s hs))
      (quaternionHaar_polySmul _ w _)
  | .add s t, hst, hlt =>
    Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right _ _ _ _)
      (Q'.add_eqv_congr' (tree_mixed_pairing p q hp hq hlp hlq s hst.1 hlt.1)
        (tree_mixed_pairing p q hp hq hlp hlq t hst.2 hlt.2))

theorem channelBilinearValue_symm (blocks : Nat) (p q : RatPoly) : ∀ t : SquareTree,
    channelBilinearValue blocks p q t ≈ channelBilinearValue blocks q p t
  | .zero => Q'.eqv_refl _
  | .term _ _ => Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)
  | .add s t => Q'.add_eqv_congr' (channelBilinearValue_symm blocks p q s) (channelBilinearValue_symm blocks p q t)

theorem expansion_mixed_pairing {half : Nat} {H : RatPoly} (E : LocalSquareExpansion half H) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length q)
    (hlp : LowerLocal half p) (hlq : LowerLocal half q) :
    quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) q) H) ≈
      channelBilinearValue (boundaryCompleteSlabLinks (centralExtent half)).length p q E.tree := by
  have hm := supported_polyMul (reflectCorrectedSlabPolynomial_support (centralExtent half) p) hq
  exact Q'.eqv_trans _ _ _
    (((PaddedPolynomialCoeffEqv.refl _ _).mul E.image).haar
      (supported_polyMul hm E.polynomialSupported)
      (supported_polyMul hm (squareTree_eval_support _ E.tree E.treeSupported)))
    (tree_mixed_pairing p q hp hq hlp hlq E.tree E.treeSupported E.treeLower)

end YMGap.Continuum.BF4ExactSlabLocalBilinearChannels

#print axioms YMGap.Continuum.BF4ExactSlabLocalBilinearChannels.lower_mixed_disjoint
#print axioms YMGap.Continuum.BF4ExactSlabLocalBilinearChannels.lower_reflected_haar_pair
#print axioms YMGap.Continuum.BF4ExactSlabLocalBilinearChannels.channelBilinearValue
#print axioms YMGap.Continuum.BF4ExactSlabLocalBilinearChannels.tree_mixed_pairing
#print axioms YMGap.Continuum.BF4ExactSlabLocalBilinearChannels.channelBilinearValue_symm
#print axioms YMGap.Continuum.BF4ExactSlabLocalBilinearChannels.expansion_mixed_pairing
