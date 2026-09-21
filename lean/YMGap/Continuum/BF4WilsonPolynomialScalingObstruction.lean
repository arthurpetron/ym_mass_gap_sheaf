/-
# Polynomial norm renormalization cannot defeat a fixed guarded lattice rate

The ACTUAL centered Wilson autocorrelation is bounded by q^n times its
original squared norm. Allow that norm to grow as C*a_j^(-p), with arbitrary
fixed natural degree p, and sample n=floor(t/a_j). The exact sampler bounds
a_j^(-1) by n+1 for positive INTEGER physical time. PolynomialGeometricDecay
then gives a computed scale modulus for the SAME response to vanish.

A fixed guarded nome ceiling supplies q<1 by the already checked monotonicity
of the original two-step rate. No common-rate certificate is postulated in
that consumer. This excludes polynomial norm growth below each such ceiling,
not faster growth, approaching the open guard boundary, or arbitrary weak
coupling. It constructs no continuum trajectory or Yang--Mills counterexample.
The supplied physical spacing is the duration of TWO original time steps.
-/

import YMGap.Continuum.PolynomialGeometricDecay
import YMGap.Continuum.PhysicalSamplingPolynomialEnvelope
import YMGap.Continuum.BF4WilsonGuardedCouplingEscape

namespace YMGap.Continuum.BF4WilsonPolynomialScalingObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PhysicalSeparatorLogRate (PhysicalSpacing)
open YMGap.Continuum.PhysicalSeparatorLinearTail (SpacingToZero)
open YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero (floorLatticeSteps)
open YMGap.Continuum.PhysicalSeparationSamplingEscape
open YMGap.Continuum.PhysicalSamplingPolynomialEnvelope
open YMGap.Continuum.PolynomialGeometricDecay
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonUniformLatticeRateScalingObstruction
  (sampledAutocorrelation sampledAutocorrelation_nonnegative sampledAutocorrelation_geometric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate twoStepRate_positive twoStepRate_lt_one)
open YMGap.Continuum.BF4ExactSlabCouplingRateMonotonicity (twoStepRate_mono)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- The spacing modulus composed with the proved polynomial/geometric cutoff. -/
def polynomialPhysicalModulus {A : PhysicalSpacing} (Z : SpacingToZero A)
    (q C : Q') (p t : Nat) (epsilon : Q') : Nat :=
  stepEscapeModulus A Z t (polynomialCutoff q C p epsilon)

variable {w : Nat → Q'} (hw0 : ∀ j, (0 : Q') < w j) (hw1 : ∀ j, w j < (1 : Q'))
  (hsmall : ∀ j, heatRatio (w j) ≤ HalfPow.half)
  (hd : ∀ j, heatRemainderBound (w j) < 1)
  (hs : ∀ j, entropyRate 625 (adjustedCoreRate (w j) (hd j)) < 1)

variable (x : (j : Nat) → UnionCompletion (hw0 j) (hw1 j) (hsmall j) (hd j) (hs j))

local notation:max "B" j:arg => completedInner (hw0 j) (hw1 j) (hsmall j) (hd j) (hs j)
local notation:max "U" j:arg => completedUnit (hw0 j) (hw1 j) (hsmall j) (hd j) (hs j)

/-- Pointwise in the actual changing carrier/vector: only this scale's norm
and rate are needed. The modulus retains the polynomial degree and amplitude. -/
theorem sampled_polynomial_small
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0 < t)
    (q C : Q') (p : Nat) (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q')) (hC : (0 : Q') ≤ C)
    (epsilon : Q') (he : (0 : Q') < epsilon) (j : Nat)
    (hj : polynomialPhysicalModulus Z q C p t epsilon ≤ j)
    (hx : B j (x j) (U j) = RCzero)
    (hq : twoStepRate (w j) (hd j) ≤ q)
    (hcap : RCle (B j (x j) (x j))
      (Quotient.mk crealSetoid (ofQ' (C * (inverseSpacing A j)^p)))) :
    RCle (sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j)
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  let n := floorLatticeSteps A j t
  let cap := C * Q'.ofNat ((n+1)^p)
  have hcap' : RCle (B j (x j) (x j)) (Quotient.mk crealSetoid (ofQ' cap)) :=
    RCle_trans hcap (leEv_le_ofQ'_of_approx_le (fun _ =>
      Q'.mul_le_mul_of_nonneg_left _ _ C (inverseSpacing_power_le A (j := j) ht p) hC))
  have hdecay := sampledAutocorrelation_geometric
    (fun _ => hw0 j) (fun _ => hw1 j) (fun _ => hsmall j) (fun _ => hd j) (fun _ => hs j)
    (fun _ => x j) (fun _ => hx) q cap
    (Q'.mul_nonneg _ _ hC (ClusterCount.ofNat_nonneg _))
    (fun _ => hq) (fun _ => hcap') A t j
  have hn := floorLatticeSteps_ge_stepEscapeModulus A Z ht hj
  exact RCle_trans hdecay (leEv_le_ofQ'_of_approx_le (fun _ =>
    polynomial_bound hq0 hq1 hC he p n hn))

/-- A nonzero sampled response with any fixed polynomial norm budget forces
escape from W at the computed scale. W need not be a physical critical point. -/
theorem nome_gt_of_polynomial_response
    (W : Q') (hW0 : (0 : Q') < W) (hdW : heatRemainderBound W < 1)
    (hsW : entropyRate 625 (adjustedCoreRate W hdW) < 1)
    (C floor : Q') (p : Nat) (hC : (0 : Q') ≤ C) (hf : (0 : Q') < floor)
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0 < t) (j : Nat)
    (hj : polynomialPhysicalModulus Z (twoStepRate W hdW) C p t (HalfPow.half*floor) ≤ j)
    (hx : B j (x j) (U j) = RCzero)
    (hcap : RCle (B j (x j) (x j))
      (Quotient.mk crealSetoid (ofQ' (C * (inverseSpacing A j)^p))))
    (hresponse : RCle (Quotient.mk crealSetoid (ofQ' floor))
      (sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j)) : W < w j := by
  apply Int.lt_of_not_ge
  intro hwW
  have hsmallResponse := sampled_polynomial_small hw0 hw1 hsmall hd hs x A Z t ht
    (twoStepRate W hdW) C p (Q'.le_of_lt (twoStepRate_positive hW0 hdW))
    (twoStepRate_lt_one hW0 hdW hsW) hC (HalfPow.half*floor)
    (ExpNeg.half_mul_pos floor hf) j hj hx
    (twoStepRate_mono (Q'.le_of_lt (hw0 j)) hwW (hd j) hdW) hcap
  have hbad := GNSQuotient.GNSData.RCofQ'_le_reflect (RCle_trans hresponse hsmallResponse)
  have hstrict : HalfPow.half * floor < floor :=
    ClusteringImpliesGap.lt_of_lt_of_le
      (ClusteringImpliesGap.mul_lt_mul_of_pos_right hf (by decide : HalfPow.half < (1 : Q')))
      (Q'.le_of_eqv (Q'.one_mul_eqv floor))
  exact Int.not_lt.mpr hbad hstrict

/-- Exact scalar representatives are supplied, not selected from their quotient. -/
theorem sampledRepresentative_converges_zero
    (W : Q') (hW0 : (0 : Q') < W) (hdW : heatRemainderBound W < 1)
    (hsW : entropyRate 625 (adjustedCoreRate W hdW) < 1) (hwW : ∀ j, w j ≤ W)
    (C : Q') (p : Nat) (hC : (0 : Q') ≤ C)
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0 < t)
    (hx : ∀ j, B j (x j) (U j) = RCzero)
    (hcap : ∀ j, RCle (B j (x j) (x j))
      (Quotient.mk crealSetoid (ofQ' (C * (inverseSpacing A j)^p))))
    (f : Nat → CReal)
    (hpin : ∀ j, Quotient.mk crealSetoid (f j) =
      sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j) :
    ConvergesTo f czero := by
  intro epsilon he
  let delta := HalfPow.half * epsilon
  have hdelta : (0 : Q') < delta := ExpNeg.half_mul_pos epsilon he
  refine ⟨polynomialPhysicalModulus Z (twoStepRate W hdW) C p t delta, fun j hj => ?_⟩
  have hu := sampled_polynomial_small hw0 hw1 hsmall hd hs x A Z t ht
    (twoStepRate W hdW) C p (Q'.le_of_lt (twoStepRate_positive hW0 hdW))
    (twoStepRate_lt_one hW0 hdW hsW) hC delta hdelta j hj (hx j)
    (twoStepRate_mono (Q'.le_of_lt (hw0 j)) (hwW j) (hd j) hdW) (hcap j)
  have hl := sampledAutocorrelation_nonnegative hw0 hw1 hsmall hd hs x A t j
  rw [← hpin j] at hu hl
  obtain ⟨N, hN⟩ := hu delta hdelta
  obtain ⟨M, hM⟩ := hl epsilon he
  refine ⟨max N M, fun n hn => ⟨?_, hM n (by omega)⟩⟩
  exact Q'.le_trans' _ _ _ (hN n (by omega))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (ExpNeg.two_halves epsilon)
      (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' epsilon)))))

/-- Any supplied continuum response limit below W is zero even with the
displayed polynomially divergent squared norm. No continuum existence follows. -/
theorem sampledLimit_zero_of_polynomial_norm
    (W : Q') (hW0 : (0 : Q') < W) (hdW : heatRemainderBound W < 1)
    (hsW : entropyRate 625 (adjustedCoreRate W hdW) < 1) (hwW : ∀ j, w j ≤ W)
    (C : Q') (p : Nat) (hC : (0 : Q') ≤ C)
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0 < t)
    (hx : ∀ j, B j (x j) (U j) = RCzero)
    (hcap : ∀ j, RCle (B j (x j) (x j))
      (Quotient.mk crealSetoid (ofQ' (C * (inverseSpacing A j)^p))))
    (f : Nat → CReal)
    (hpin : ∀ j, Quotient.mk crealSetoid (f j) =
      sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j)
    (l : CReal) (hl : ConvergesTo f l) : Equiv l czero :=
  Equiv_of_limit_of_equal (fun j => Equiv.refl (f j)) hl
    (sampledRepresentative_converges_zero hw0 hw1 hsmall hd hs x W hW0 hdW hsW hwW
      C p hC A Z t ht hx hcap f hpin)

end YMGap.Continuum.BF4WilsonPolynomialScalingObstruction

#print axioms YMGap.Continuum.BF4WilsonPolynomialScalingObstruction.polynomialPhysicalModulus
#print axioms YMGap.Continuum.BF4WilsonPolynomialScalingObstruction.sampled_polynomial_small
#print axioms YMGap.Continuum.BF4WilsonPolynomialScalingObstruction.nome_gt_of_polynomial_response
#print axioms YMGap.Continuum.BF4WilsonPolynomialScalingObstruction.sampledRepresentative_converges_zero
#print axioms YMGap.Continuum.BF4WilsonPolynomialScalingObstruction.sampledLimit_zero_of_polynomial_norm
