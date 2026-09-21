/-
# Polynomially bounded responses vanish throughout the OLD guarded region

The improved SAME-completed-carrier gap supplies one constant two-step
rate 1/16 throughout the old 625-entropy guard. Therefore the existing
polynomial/geometric sampling argument needs neither a fixed nome ceiling
nor an assumed uniform bound on the old, looser rate. Approaching that
guard boundary does not preserve this original positive-integer-time
response under any fixed polynomial squared-norm envelope.

This rules out that specific scaling route, not Yang--Mills theory. It says
nothing about leaving the old guard, faster-than-polynomial norm growth,
or other observables without the stated same-carrier norm/control pins.
Spacing is the supplied duration of TWO original lattice steps. No physical
calibration, continuum existence or QFT axiom is constructed here.
-/
import YMGap.Continuum.BF4WilsonDescentCompletedGap
import YMGap.Continuum.BF4WilsonPolynomialScalingObstruction

namespace YMGap.Continuum.BF4WilsonOldGuardScalingObstruction

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
  (sampledAutocorrelation sampledAutocorrelation_nonnegative)
open YMGap.Continuum.BF4WilsonPolynomialScalingObstruction (polynomialPhysicalModulus)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay
  (twoStepRate twoStepRate_positive twoStepRate_lt_one)
open YMGap.Continuum.BF4WilsonDescentCompletedGap (even_autocorrelation_decay)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Nat → Q'} (hw0 : ∀ j, (0 : Q') < w j) (hw1 : ∀ j, w j < (1 : Q'))
  (hsmall : ∀ j, heatRatio (w j) ≤ HalfPow.half)
  (hd : ∀ j, heatRemainderBound (w j) < 1)
  (hs : ∀ j, entropyRate 625 (adjustedCoreRate (w j) (hd j)) < 1)
  (x : (j : Nat) → UnionCompletion (hw0 j) (hw1 j) (hsmall j) (hd j) (hs j))

local notation:max "B" j:arg => completedInner (hw0 j) (hw1 j) (hsmall j) (hd j) (hs j)
local notation:max "U" j:arg => completedUnit (hw0 j) (hw1 j) (hsmall j) (hd j) (hs j)

/-- Executable modulus, independent of the changing coupling sequence. -/
def scaleModulus {A : PhysicalSpacing} (Z : SpacingToZero A)
    (C : Q') (p t : Nat) (epsilon : Q') : Nat :=
  polynomialPhysicalModulus Z twoStepRate C p t epsilon

/-- Unlike the earlier ceiling theorem, this has NO W or extra common-rate
assumption. The original guard itself now supplies the improved common rate. -/
theorem sampled_polynomial_small
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0<t)
    (C : Q') (p : Nat) (hC : (0 : Q') ≤ C) (epsilon : Q') (he : (0 : Q') < epsilon)
    (j : Nat) (hj : scaleModulus Z C p t epsilon ≤ j)
    (hx : B j (x j) (U j) = RCzero)
    (hcap : RCle (B j (x j) (x j))
      (Quotient.mk crealSetoid (ofQ' (C*(inverseSpacing A j)^p)))) :
    RCle (sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j)
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  let n := floorLatticeSteps A j t
  let cap := C*Q'.ofNat ((n+1)^p)
  have hcap' : RCle (B j (x j) (x j)) (Quotient.mk crealSetoid (ofQ' cap)) :=
    RCle_trans hcap (leEv_le_ofQ'_of_approx_le (fun _ =>
      Q'.mul_le_mul_of_nonneg_left _ _ C (inverseSpacing_power_le A (j := j) ht p) hC))
  have hdecay := RCle_trans
    (even_autocorrelation_decay (hw0 j) (hw1 j) (hsmall j) (hd j) (hs j) (x j) hx n)
    (RCscale_mono (Q'.pow_nonneg _ (Q'.le_of_lt twoStepRate_positive) n) hcap')
  have hn := floorLatticeSteps_ge_stepEscapeModulus A Z ht hj
  exact RCle_trans hdecay (leEv_le_ofQ'_of_approx_le (fun _ =>
    polynomial_bound (Q'.le_of_lt twoStepRate_positive) twoStepRate_lt_one hC he p n hn))

theorem sampled_floor_impossible
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0<t)
    (C floor : Q') (p : Nat) (hC : (0 : Q') ≤ C) (hf : (0 : Q') < floor)
    (j : Nat) (hj : scaleModulus Z C p t (HalfPow.half*floor) ≤ j)
    (hx : B j (x j) (U j) = RCzero)
    (hcap : RCle (B j (x j) (x j))
      (Quotient.mk crealSetoid (ofQ' (C*(inverseSpacing A j)^p))))
    (hfloor : RCle (Quotient.mk crealSetoid (ofQ' floor))
      (sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j)) : False := by
  have hsmallResponse := sampled_polynomial_small hw0 hw1 hsmall hd hs x A Z t ht C p hC
    (HalfPow.half*floor) (ExpNeg.half_mul_pos floor hf) j hj hx hcap
  have hbad := GNSQuotient.GNSData.RCofQ'_le_reflect (RCle_trans hfloor hsmallResponse)
  have hstrict : HalfPow.half*floor < floor :=
    ClusteringImpliesGap.lt_of_lt_of_le
      (ClusteringImpliesGap.mul_lt_mul_of_pos_right hf (by decide : HalfPow.half < (1 : Q')))
      (Q'.le_of_eqv (Q'.one_mul_eqv floor))
  exact Int.not_lt.mpr hbad hstrict

/-- The scalar representatives are supplied with exact same-response pins;
none is chosen from a quotient. The explicit scale modulus above controls them. -/
theorem sampledRepresentative_converges_zero
    (C : Q') (p : Nat) (hC : (0 : Q') ≤ C)
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0<t)
    (hx : ∀ j, B j (x j) (U j) = RCzero)
    (hcap : ∀ j, RCle (B j (x j) (x j))
      (Quotient.mk crealSetoid (ofQ' (C*(inverseSpacing A j)^p))))
    (f : Nat → CReal) (hpin : ∀ j, Quotient.mk crealSetoid (f j) =
      sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j) : ConvergesTo f czero := by
  intro epsilon he
  let delta := HalfPow.half*epsilon
  have hdelta : (0 : Q') < delta := ExpNeg.half_mul_pos epsilon he
  refine ⟨scaleModulus Z C p t delta, fun j hj => ?_⟩
  have hu := sampled_polynomial_small hw0 hw1 hsmall hd hs x A Z t ht C p hC delta hdelta j hj (hx j) (hcap j)
  have hl := sampledAutocorrelation_nonnegative hw0 hw1 hsmall hd hs x A t j
  rw [← hpin j] at hu hl
  obtain ⟨N, hN⟩ := hu delta hdelta
  obtain ⟨M, hM⟩ := hl epsilon he
  refine ⟨max N M, fun n hn => ⟨?_, hM n (by omega)⟩⟩
  exact Q'.le_trans' _ _ _ (hN n (by omega))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (ExpNeg.two_halves epsilon)
      (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' epsilon)))))

theorem sampledLimit_zero
    (C : Q') (p : Nat) (hC : (0 : Q') ≤ C)
    (A : PhysicalSpacing) (Z : SpacingToZero A) (t : Nat) (ht : 0<t)
    (hx : ∀ j, B j (x j) (U j) = RCzero)
    (hcap : ∀ j, RCle (B j (x j) (x j))
      (Quotient.mk crealSetoid (ofQ' (C*(inverseSpacing A j)^p))))
    (f : Nat → CReal) (hpin : ∀ j, Quotient.mk crealSetoid (f j) =
      sampledAutocorrelation hw0 hw1 hsmall hd hs x A t j)
    (l : CReal) (hl : ConvergesTo f l) : Equiv l czero :=
  Equiv_of_limit_of_equal (fun j => Equiv.refl (f j)) hl
    (sampledRepresentative_converges_zero hw0 hw1 hsmall hd hs x C p hC A Z t ht hx hcap f hpin)

end YMGap.Continuum.BF4WilsonOldGuardScalingObstruction

#print axioms YMGap.Continuum.BF4WilsonOldGuardScalingObstruction.scaleModulus
#print axioms YMGap.Continuum.BF4WilsonOldGuardScalingObstruction.sampled_polynomial_small
#print axioms YMGap.Continuum.BF4WilsonOldGuardScalingObstruction.sampled_floor_impossible
#print axioms YMGap.Continuum.BF4WilsonOldGuardScalingObstruction.sampledRepresentative_converges_zero
#print axioms YMGap.Continuum.BF4WilsonOldGuardScalingObstruction.sampledLimit_zero
