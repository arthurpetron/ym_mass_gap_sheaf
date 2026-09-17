/-
# The exact fundamental moment of one retained original face heat

One original face link is absent from the entire spectator q. Multiplying
the fundamental character by every term of the COMPLETE heat prefix leaves
only spin one after Haar integration. The answer is coeffW(w,1)*H[q],
at every cutoff K>=1 and every rational nome, without positivity assumptions.

Consumer: the first ORIGINAL transfer of a fringe-face insertion, whose
unique inactive leaf is absent from the other spatial factors, terminal
message and kinetic adjoint test. No incident factor is silently dropped.
This is a moment identity, not a variance or interacting-gap estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
import YMGap.Continuum.PolynomialWeightedSumBounds

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFaceHeatMoment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

private theorem first_mul_succ (p : RatPoly) (n : Nat) :
    RatPolyCoeffEqv (polyMul (characterPolynomial p 1) (characterPolynomial p (n+1)))
      (polyAdd (characterPolynomial p (n+2)) (characterPolynomial p n)) := by
  let a := polyMul (characterPolynomial p 1) (characterPolynomial p (n+1))
  let b := characterPolynomial p n
  exact (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.mul (.const (-1)) (.var 1))) (.var 1)) (by decide)
    (fun i => if i = 0 then a else b)).trans
    (((RatPolyCoeffEqv.refl a).add (cap_mul_left (-1) b)).add (.refl b))

/-- Weighted orthogonality keeps the arbitrary link-independent spectator. -/
theorem character_pair_moment {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q)
    (hi : QuaternionBlockIndependent ((baseLinks width).idxOf l) q) (spin : Nat) :
    quaternionHaar (N width)
      (polyMul (polyMul (characterPolynomial (plaquette width face).scalar 1)
        (characterPolynomial (plaquette width face).scalar spin)) q) ≈
      (if spin = 1 then quaternionHaar (N width) q else 0) := by
  cases spin with
  | zero =>
      exact Q'.eqv_trans _ _ _
        (haar_of_coeff ((RatPolyCoeffEqv.mul_one _).mul_right q))
        (character_haar_zero hf l hl 1 (by decide) q hq hi)
  | succ n =>
      have he := (first_mul_succ (plaquette width face).scalar n).mul_right q
      refine Q'.eqv_trans _ _ _ (haar_of_coeff he) ?_
      rw [polyMul_add_left_exact]
      refine Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) ?_
      cases n with
      | zero =>
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (character_haar_zero hf l hl 2 (by decide) q hq hi)
              (haar_of_coeff (RatPolyCoeffEqv.one_mul q)))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | succ n =>
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr'
              (character_haar_zero hf l hl (n+1+2) (by omega) q hq hi)
              (character_haar_zero hf l hl (n+1) (by omega) q hq hi))
            (by simp only [Nat.succ.injEq, Nat.add_eq_zero_iff, Nat.one_ne_zero,
              and_false, ↓reduceIte]; exact Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem prefix_step (w : Q') (K : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (heatPrefix w (K+1) p)
      (polyAdd (heatPrefix w K p) (polySmul (coeffW w (K+1)) (characterPolynomial p (K+1)))) := by
  unfold heatPrefix
  rw [List.range_succ, PolynomialWeightedSumBounds.sum_append]
  exact (RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_zero _)

private theorem heat_term_moment (w : Q') {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q)
    (hi : QuaternionBlockIndependent ((baseLinks width).idxOf l) q) (spin : Nat) :
    quaternionHaar (N width)
      (polyMul (polySmul (coeffW w spin) (characterPolynomial (plaquette width face).scalar spin))
        (polyMul (characterPolynomial (plaquette width face).scalar 1) q)) ≈
      coeffW w spin * (if spin = 1 then quaternionHaar (N width) q else 0) := by
  have he : RatPolyCoeffEqv
      (polyMul (characterPolynomial (plaquette width face).scalar spin)
        (polyMul (characterPolynomial (plaquette width face).scalar 1) q))
      (polyMul (polyMul (characterPolynomial (plaquette width face).scalar 1)
        (characterPolynomial (plaquette width face).scalar spin)) q) :=
    (RatPolyCoeffEqv.mul_assoc _ _ _).symm.trans
      ((RatPolyCoeffEqv.mul_comm _ _).mul_right q)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (haar_of_coeff he) (character_pair_moment hf l hl q hq hi spin))))

private theorem prefix_moment (w : Q') {width : Nat} {face : Z4Plaq}
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q)
    (hi : QuaternionBlockIndependent ((baseLinks width).idxOf l) q) :
    ∀ K, quaternionHaar (N width)
      (polyMul (heatPrefix w K (plaquette width face).scalar)
        (polyMul (characterPolynomial (plaquette width face).scalar 1) q)) ≈
      (if K = 0 then 0 else coeffW w 1 * quaternionHaar (N width) q)
  | 0 => by
      have hp := QuaternionHaarHeatCertificate.heatPrefix_split w 0 (plaquette width face).scalar
      have he : RatPolyCoeffEqv (heatPrefix w 0 (plaquette width face).scalar) polyOne :=
        hp.trans (RatPolyCoeffEqv.add_zero polyOne)
      exact Q'.eqv_trans _ _ _
        (haar_of_coeff ((he.mul_right _).trans (RatPolyCoeffEqv.one_mul _)))
        (character_haar_zero hf l hl 1 (by decide) q hq hi)
  | K+1 => by
      have he := (prefix_step w K (plaquette width face).scalar).mul_right
        (polyMul (characterPolynomial (plaquette width face).scalar 1) q)
      refine Q'.eqv_trans _ _ _ (haar_of_coeff he) ?_
      rw [polyMul_add_left_exact]
      refine Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (prefix_moment w hf l hl q hq hi K)
              (heat_term_moment w hf l hl q hq hi (K+1))) ?_)
      cases K with
      | zero => exact Q'.eqv_of_eq (Q'.zero_add' _)
      | succ K =>
          simp only [Nat.succ_ne_zero, Nat.succ.injEq, ↓reduceIte]
          exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.mul_zero_eqv _))
            (Q'.eqv_of_eq (Q'.add_zero' _))

/-- The full original prefix contributes exactly its fundamental coefficient.
No upper spin is discarded before its cancellation is proved. -/
theorem heatFace_character_moment (w : Q') (K : Nat) (hK : 1 ≤ K)
    {width : Nat} {face : Z4Plaq} (hf : face ∈ spatialFaces width)
    (l : Z4Link) (hl : l ∈ edgesOf face) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q)
    (hi : QuaternionBlockIndependent ((baseLinks width).idxOf l) q) :
    quaternionHaar (N width)
      (polyMul (heatPrefix w K (plaquette width face).scalar)
        (polyMul (characterPolynomial (plaquette width face).scalar 1) q)) ≈
      coeffW w 1 * quaternionHaar (N width) q := by
  have hn : K ≠ 0 := by omega
  simpa only [if_neg hn] using prefix_moment w hf l hl q hq hi K

end YMGap.Continuum.BF4ExactSlabFixedSpatialFaceHeatMoment

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceHeatMoment.character_pair_moment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFaceHeatMoment.heatFace_character_moment
