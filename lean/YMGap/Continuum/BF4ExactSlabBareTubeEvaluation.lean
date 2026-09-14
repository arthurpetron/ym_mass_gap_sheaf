/-
# Exact normalization of the original three-layer tube moment

The upper plaquette is the retained four-block boundary of the existing
full-carrier contraction. Its Haar square is one, including all inactive
spectator variables. This closes the value of the literal tube integral;
it does not count its occurrences in the original leading expansion.
-/

import YMGap.Continuum.BF4ExactSlabMinimalTubeSweep
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint

namespace YMGap.Continuum.BF4ExactSlabBareTubeEvaluation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding
open YMGap.Continuum.BF4ExactSlabTubeCarrierWords
open YMGap.Continuum.BF4ExactSlabTubeCarrierContraction
open YMGap.Continuum.BF4ExactSlabMinimalTubeMomentPin
open YMGap.Continuum.BF4ExactSlabMinimalTubeSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube
open YMGap.Continuum.SU2QuaternionFundamentalTubeComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" margin:max => List.length (boundaryCompleteSlabLinks (responseExtent margin))
local notation "P" => plaquette 0 1 2 3

theorem upper_lift_eq : liftBoundary 12 P = compactSlice ⟨3,by decide⟩ := by decide +kernel

theorem plaquette_supported : SupportedQuaternionBlocks 4 P := by
  have h : List.all P (fun t => decide (t.1.length ≤ 16)) = true := by decide +kernel
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp h t ht)

theorem retained_square_one (margin : Nat) : quaternionHaar (N margin-12) (polyMul P P) ≈ 1 := by
  have hn := carrier_size margin
  exact Q'.eqv_trans _ _ _ (quaternionHaar_extend_supported_endpoint (by omega)
    (polyMul P P) (supported_polyMul plaquette_supported plaquette_supported)) plaquette_square_one

private theorem append_factor_congr {blocks : Nat} {p q : RatPoly}
    (h : PaddedPolynomialCoeffEqv blocks p q) : ∀ fs : List RatPoly,
    PaddedPolynomialCoeffEqv blocks (factorProduct (fs ++ [p])) (factorProduct (fs ++ [q]))
  | [] => h.mul (.refl _ polyOne)
  | f::fs => (PaddedPolynomialCoeffEqv.refl _ f).mul (append_factor_congr h fs)

private theorem factors_supported {blocks : Nat} : ∀ fs : List RatPoly,
    (∀ p, p ∈ fs → SupportedQuaternionBlocks blocks p) → SupportedQuaternionBlocks blocks (factorProduct fs)
  | [], _ => supported_one _
  | p::ps, h => supported_polyMul (h p List.mem_cons_self)
      (factors_supported ps (fun q hq => h q (List.mem_cons_of_mem p hq)))

private theorem literal_factors_supported (margin : Nat) : ∀ p, p ∈ literalFactors margin →
    SupportedQuaternionBlocks (N margin) p := by
  intro p hp
  rcases List.mem_cons.mp hp with he | hp
  · subst p
    exact original_character_support _ _ _
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact swept_character_supported _ _ _ _

theorem upper_boundary_haar (margin : Nat) :
    quaternionHaar (N margin) (factorProduct (literalFactors margin ++ [literalSlice margin ⟨3,by decide⟩])) ≈
      quaternionHaar (N margin) (factorProduct (literalFactors margin ++ [literalBoundary margin P])) := by
  have h := slice_embedding_pin margin ⟨3,by decide⟩
  rw [← upper_lift_eq] at h
  have hp (p : RatPoly) (hs : SupportedQuaternionBlocks (N margin) p) :
      SupportedQuaternionBlocks (N margin) (factorProduct (literalFactors margin ++ [p])) := by
    apply factors_supported
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact literal_factors_supported margin q hq
    · exact (List.mem_singleton.mp hq) ▸ hs
  exact (append_factor_congr h.symm (literalFactors margin)).haar
    (hp _ (original_character_support _ _ _)) (hp _ ((carrierEmbedding margin).polynomial_supported _))

theorem dimension_times_tube (margin : Nat) : (4096 : Q') * bareTubeMoment margin ≈ 1 := by
  have hn := carrier_size margin
  have hb : SupportedQuaternionBlocks (N margin-12) P := by
    intro t ht
    have hs := plaquette_supported t ht
    omega
  have hc := literal_weighted_boundary_haar (1 : Q') margin P hb
  have he : heatCoefficient (1 : Q') ≈ (4096 : Q') := by decide +kernel
  have hpow : RingNormaliser.qpow (1 : Q') 36 ≈ (1 : Q') := by decide +kernel
  have hleft := quaternionHaar_polySmul (N margin) (heatCoefficient (1 : Q'))
    (factorProduct (literalFactors margin ++ [literalBoundary margin P]))
  have hpin := Q'.eqv_trans _ _ _ (original_tube_sweep margin) (upper_boundary_haar margin)
  have hscale : (4096 : Q') * bareTubeMoment margin ≈
      heatCoefficient (1 : Q') * quaternionHaar (N margin)
        (factorProduct (literalFactors margin ++ [literalBoundary margin P])) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm he))
      (Q'.mul_eqv_congr_left _ _ _ hpin)
  exact Q'.eqv_trans _ _ _ hscale (Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ hc (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hpow)
      (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (retained_square_one margin)))))

end YMGap.Continuum.BF4ExactSlabBareTubeEvaluation

#print axioms YMGap.Continuum.BF4ExactSlabBareTubeEvaluation.upper_lift_eq
#print axioms YMGap.Continuum.BF4ExactSlabBareTubeEvaluation.plaquette_supported
#print axioms YMGap.Continuum.BF4ExactSlabBareTubeEvaluation.retained_square_one
#print axioms YMGap.Continuum.BF4ExactSlabBareTubeEvaluation.upper_boundary_haar
#print axioms YMGap.Continuum.BF4ExactSlabBareTubeEvaluation.dimension_times_tube
