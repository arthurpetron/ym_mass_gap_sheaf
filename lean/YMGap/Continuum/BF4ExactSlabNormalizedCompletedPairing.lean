/-
# Original-action normalization on the SAME completed slab carrier

Divide the original completed pairing by its proved positive action limit.
The ACTUAL full heat unit then has squared norm one. Positivity, symmetry,
additivity, Cauchy--Schwarz and explicit two-sided norm comparison are proved
on the unchanged vectors, with an exact recovery of the unnormalized form.

This normalizes the finite-slab form, not a stationary physical vacuum. No
inter-slab compatibility, observable multiplication, geometric time transfer,
strict physical gap, volume/spacing limit or continuum QFT is supplied here.
-/

import YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
import YMGap.Continuum.ScaledGNSCompletionEstimates

namespace YMGap.Continuum.BF4ExactSlabNormalizedCompletedPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm
open YMGap.Continuum.BF4ExactSlabAllExtentFiniteBoundaryObservable
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitNormAction
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.ScaledGNSCompletionEstimates

private theorem scaled_dense_approximation (D : GNSData) (lambda : CReal)
    (R : Q') (hR : (0 : Q') < R) (hupper : ∀ n, lambda.approx n ≤ R)
    (X : CauchyGNS D) (epsilon : Q') (he : (0 : Q') < epsilon)
    (p : Nat) (hp : X.modulus (Q'.divPos epsilon R hR) ≤ p) :
    RCle (RCmul
      (D.cinnerCompl (D.cSub (embedV D (X.seq p)) (Quotient.mk (cauchySetoid D) X))
        (D.cSub (embedV D (X.seq p)) (Quotient.mk (cauchySetoid D) X)))
      (Quotient.mk crealSetoid lambda)) (Quotient.mk crealSetoid (CReal.ofQ' epsilon)) := by
  intro delta hd
  let budget := Q'.divPos epsilon R hR
  have hb : (0 : Q') < budget := Q'.divPos_pos _ _ _ he
  refine ⟨X.modulus budget, fun n hn => ?_⟩
  let U := constCauchy D (X.seq p)
  let i := CReal.QMhat (fun m => D.distSqQ (U.seq m) (X.seq m)) (D.distSqSeqCauchy U X) n
  have hi : X.modulus budget ≤ i := Nat.le_trans hn (CReal.self_le_QMhat _ _ n)
  have hdist := X.isCauchy budget hb p i hp hi
  have hproduct : D.distSqQ (X.seq p) (X.seq i) * lambda.approx n ≤ epsilon :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (hupper n) (D.self_nonneg (D.sub (X.seq p) (X.seq i))))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ R hdist (Q'.le_of_lt hR))
        (Q'.le_of_eqv (Q'.divPos_mul_eqv _ _ _)))
  exact Q'.le_trans' _ _ _ hproduct (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hd))

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat)

local notation "D" => cutoffLimitGNSData w (Q'.le_of_lt hw0) half
local notation "V" => CutoffLimitCarrier w (Q'.le_of_lt hw0) half
local notation "lambda" => Quotient.mk crealSetoid (actionReciprocal w hw0 hw1 half)
local notation "Z" => Quotient.mk crealSetoid (fullActionLimit w hw0 hw1 half)

def normalizedInner (x y : V) : RC := RCmul ((D).cinnerCompl x y) lambda

theorem reciprocal_nonnegative : RCnonneg lambda :=
  CReal.leEv_ofQ'_of_approx_ge (fun n => Q'.le_of_lt (actionReciprocal_approx_pos w hw0 hw1 half n))

theorem normalizedInner_nonnegative (x : V) : RCnonneg (normalizedInner w hw0 hw1 half x x) := by
  have hmul (a b : RC) (ha : RCnonneg a) (hb : RCnonneg b) : RCnonneg (RCmul a b) := by
    refine Quotient.inductionOn₂ a b ?_ ha hb
    intro A B hA hB
    exact CReal.mul_nonneg hA hB
  exact hmul _ _ ((D).cinner_self_nonneg x) (reciprocal_nonnegative w hw0 hw1 half)

theorem normalizedInner_symm (x y : V) :
    normalizedInner w hw0 hw1 half x y = normalizedInner w hw0 hw1 half y x :=
  congrArg (fun a => RCmul a lambda) ((D).cinnerCompl_comm x y)

theorem normalizedInner_add_left (x y z : V) :
    normalizedInner w hw0 hw1 half ((D).cAdd x y) z =
      RCadd (normalizedInner w hw0 hw1 half x z) (normalizedInner w hw0 hw1 half y z) := by
  unfold normalizedInner
  rw [(D).cinnerCompl_cAdd_left, ScaledGNSCompletionEstimates.mul_add]

/-- Exact normalization of the completed FULL heat unit, not the cutoff-zero code. -/
theorem completedHeatUnit_norm_one :
    normalizedInner w hw0 hw1 half (completedHeatUnit w hw0 hw1 half) (completedHeatUnit w hw0 hw1 half) =
      Quotient.mk crealSetoid CReal.cone :=
  (congrArg (fun a => RCmul a lambda) (completedHeatUnit_norm_action w hw0 hw1 half)).trans
    (Quotient.sound (action_mul_reciprocal w hw0 hw1 half))

theorem normalizedInner_dense (a b : BoundaryObservable half) :
    normalizedInner w hw0 hw1 half (cutoffLimitEmbed w (Q'.le_of_lt hw0) a)
      (cutoffLimitEmbed w (Q'.le_of_lt hw0) b) =
      Quotient.mk crealSetoid (CReal.mul (CReal.ofQ' (limitForm w a b)) (actionReciprocal w hw0 hw1 half)) :=
  congrArg (fun z => RCmul z lambda) (cutoffLimitEmbed_pairing w (Q'.le_of_lt hw0) a b)

/-- Multiplying by the SAME action recovers every original pairing. -/
theorem normalizedInner_recover (x y : V) :
    RCmul (normalizedInner w hw0 hw1 half x y) Z = (D).cinnerCompl x y := by
  have hrec : CReal.Equiv
      (CReal.mul (actionReciprocal w hw0 hw1 half) (fullActionLimit w hw0 hw1 half)) CReal.cone :=
    (CRealAlg.cmul_comm _ _).trans (action_mul_reciprocal w hw0 hw1 half)
  have h (a : RC) : RCmul (RCmul a lambda) Z = a := by
    refine Quotient.inductionOn a ?_
    intro A
    exact Quotient.sound ((CRealAlg.cmul_assoc _ _ _).trans
      ((Pivot2.mul_congr_right hrec).trans (CRealAlg.cmul_cone A)))
  exact h _

/-- No new null vectors are introduced by normalization. -/
theorem normalizedInner_zero_iff (x y : V) :
    normalizedInner w hw0 hw1 half x y = RCzero ↔ (D).cinnerCompl x y = RCzero := by
  have hz (a : RC) : RCmul RCzero a = RCzero := by
    refine Quotient.inductionOn a ?_
    intro A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv (A.approx n)))
  constructor
  · intro h
    rw [← normalizedInner_recover w hw0 hw1 half x y, h, hz]
  · intro h
    unfold normalizedInner
    rw [h, hz]

theorem normalizedInner_norm_lower (x : V) :
    RCle (RCmul ((D).cinnerCompl x x) (Quotient.mk crealSetoid (CReal.ofQ' (reciprocalFloor w hw0 half))))
      (normalizedInner w hw0 hw1 half x x) :=
  mul_mono_left ((D).cinner_self_nonneg x)
    (CReal.leEv_ofQ'_of_approx_ge (actionReciprocal_approx_ge w hw0 hw1 half))

theorem normalizedInner_norm_upper (x : V) :
    RCle (normalizedInner w hw0 hw1 half x x)
      (RCmul ((D).cinnerCompl x x) (Quotient.mk crealSetoid (CReal.ofQ' (reciprocalCeiling w hw0 hw1 half)))) :=
  mul_mono_left ((D).cinner_self_nonneg x)
    (CReal.leEv_of_le (fun n => Q'.le_trans' _ _ _ (actionReciprocal_approx_le w hw0 hw1 half n)
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (Q'.invSucc_pos n)))))

theorem normalizedInner_cauchySchwarz (x y : V) :
    RCle (RCmul (normalizedInner w hw0 hw1 half x y) (normalizedInner w hw0 hw1 half x y))
      (RCmul (normalizedInner w hw0 hw1 half x x) (normalizedInner w hw0 hw1 half y y)) := by
  unfold normalizedInner
  rw [product_shuffle, product_shuffle]
  exact mul_mono_left (square_nonnegative lambda) ((D).RC_cauchy_schwarz x y)

/-- Explicit rescaling of any supplied original squared-distance modulus. -/
def normalizedModulus (X : CauchyGNS D) (epsilon : Q') : Nat :=
  X.modulus (Q'.divPos epsilon (reciprocalCeiling w hw0 hw1 half) (reciprocalCeiling_pos w hw0 hw1 half))

theorem normalizedRepresentative_cauchy (X : CauchyGNS D) (epsilon : Q') (he : (0 : Q') < epsilon)
    (p q : Nat) (hp : normalizedModulus w hw0 hw1 half X epsilon ≤ p)
    (hq : normalizedModulus w hw0 hw1 half X epsilon ≤ q) (n : Nat) :
    (D).distSqQ (X.seq p) (X.seq q) * (actionReciprocal w hw0 hw1 half).approx n ≤ epsilon := by
  let R := reciprocalCeiling w hw0 hw1 half
  have hR := reciprocalCeiling_pos w hw0 hw1 half
  let delta := Q'.divPos epsilon R hR
  have hd : (0 : Q') < delta := Q'.divPos_pos _ _ _ he
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (actionReciprocal_approx_le w hw0 hw1 half n)
      ((D).self_nonneg ((D).sub (X.seq p) (X.seq q))))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ R (X.isCauchy delta hd p q hp hq) (Q'.le_of_lt hR))
      (Q'.le_of_eqv (Q'.divPos_mul_eqv _ _ _)))

/-- The same representative converges in the normalized completed distance,
with the displayed rescaled modulus. -/
theorem normalizedDense_approximation (X : CauchyGNS D) (epsilon : Q') (he : (0 : Q') < epsilon)
    (p : Nat) (hp : normalizedModulus w hw0 hw1 half X epsilon ≤ p) :
    RCle (normalizedInner w hw0 hw1 half
      ((D).cSub (embedV D (X.seq p)) (Quotient.mk (cauchySetoid D) X))
      ((D).cSub (embedV D (X.seq p)) (Quotient.mk (cauchySetoid D) X)))
      (Quotient.mk crealSetoid (CReal.ofQ' epsilon)) :=
  scaled_dense_approximation D (actionReciprocal w hw0 hw1 half)
    (reciprocalCeiling w hw0 hw1 half) (reciprocalCeiling_pos w hw0 hw1 half)
    (actionReciprocal_approx_le w hw0 hw1 half) X epsilon he p hp

end YMGap.Continuum.BF4ExactSlabNormalizedCompletedPairing

#print axioms YMGap.Continuum.BF4ExactSlabNormalizedCompletedPairing.normalizedInner
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedCompletedPairing.reciprocal_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedCompletedPairing.normalizedInner_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedCompletedPairing.normalizedInner_symm
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedCompletedPairing.normalizedInner_add_left
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedCompletedPairing.completedHeatUnit_norm_one
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedCompletedPairing.normalizedInner_dense
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedCompletedPairing.normalizedInner_recover
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedCompletedPairing.normalizedInner_zero_iff
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedCompletedPairing.normalizedInner_norm_lower
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedCompletedPairing.normalizedInner_norm_upper
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedCompletedPairing.normalizedInner_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedCompletedPairing.normalizedModulus
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedCompletedPairing.normalizedRepresentative_cauchy
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedCompletedPairing.normalizedDense_approximation
