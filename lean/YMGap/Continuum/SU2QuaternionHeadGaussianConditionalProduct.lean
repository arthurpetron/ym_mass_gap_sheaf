/-
# Retained-coefficient product law for the partial Gaussian integral

A factor with head degree zero pulls through partialGaussianHead, with its
four empty head exponents removed. The statement is coefficientwise, so
arbitrary tail spectators remain available. In particular the actual tail
radius in the quaternion Stein recurrence pulls out as radius block zero.
-/

import YMGap.Continuum.SU2QuaternionHeadGaussianIBP
import YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

namespace YMGap.Continuum.SU2QuaternionHeadGaussianConditionalProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadHomogeneousGaussian
open YMGap.Continuum.SU2QuaternionHeadGaussianIBP
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct

local infix:50 " ≈ " => Q'.eqv

theorem partialGaussianHead_smul (a : Q') (p : RatPoly) :
    RatPolyCoeffEqv (partialGaussianHead (polySmul a p)) (polySmul a (partialGaussianHead p)) := by
  intro weight
  refine Q'.eqv_trans _ _ _ (partialGaussianHead_probe weight _) ?_
  refine Q'.eqv_trans _ _ _ (ratWeightedSum_smul (gaussianHeadProbe weight) a p) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_symm (partialGaussianHead_probe weight p))) ?_
  exact Q'.eqv_symm (ratWeightedSum_smul weight a _)

theorem partialGaussianHead_one : RatPolyCoeffEqv (partialGaussianHead polyOne) polyOne := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide

private theorem drop_monoMul : ∀ (n : Nat) (a b : List Nat),
    (monoMul a b).drop n = monoMul (a.drop n) (b.drop n)
  | 0, _, _ => rfl
  | n + 1, [], _ => by simp [monoMul]
  | n + 1, a, [] => by
    have hnil (m : List Nat) : monoMul m [] = m := by cases m <;> rfl
    rw [hnil, List.drop_nil, hnil]
  | n + 1, _ :: a, _ :: b => drop_monoMul n a b

private theorem gaussianMoment_independent (a b : List Nat) (hb : quaternionBlockDegree b 0 = 0) :
    headGaussianMoment (monoMul a b) = headGaussianMoment a := by
  change exponentAt b 0 + exponentAt b 1 + exponentAt b 2 + exponentAt b 3 = 0 at hb
  have h0 : exponentAt b 0 = 0 := by omega
  have h1 : exponentAt b 1 = 0 := by omega
  have h2 : exponentAt b 2 = 0 := by omega
  have h3 : exponentAt b 3 = 0 := by omega
  simp only [headGaussianMoment, exponentAt_monoMul, h0, h1, h2, h3, Nat.add_zero]

private theorem coefficient_pair (a b g : Q') : (a * b) * g ≈ (a * g) * b :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b g)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (Q'.mul_comm_eqv b g))
      (Q'.eqv_symm (Q'.mul_assoc_eqv a g b)))

private theorem conditional_row (source : RatTerm) : ∀ q : RatPoly,
    HasQuaternionBlockDegree 0 0 q →
    RatPolyTermwiseEqv
      (partialGaussianHead (q.map fun t => (monoMul source.1 t.1, source.2 * t.2)))
      ((dropHeadPolynomial q).map fun t =>
        (monoMul (source.1.drop 4) t.1, (source.2 * headGaussianMoment source.1) * t.2))
  | [], _ => True.intro
  | term :: rest, hq => by
    refine ⟨drop_monoMul 4 source.1 term.1, ?_,
      conditional_row source rest (fun t ht => hq t (List.mem_cons_of_mem term ht))⟩
    change (source.2 * term.2) * headGaussianMoment (monoMul source.1 term.1) ≈ _
    rw [gaussianMoment_independent source.1 term.1 (hq term List.mem_cons_self)]
    exact coefficient_pair _ _ _

private theorem conditional_product : ∀ p q : RatPoly,
    HasQuaternionBlockDegree 0 0 q →
    RatPolyTermwiseEqv (partialGaussianHead (polyMul p q))
      (polyMul (partialGaussianHead p) (dropHeadPolynomial q))
  | [], _, _ => True.intro
  | source :: rest, q, hq => by
    have hr := conditional_row source q hq
    have ht := conditional_product rest q hq
    simpa only [polyMul, partialGaussianHead, List.flatMap_cons, List.map_append, List.map_cons]
      using RatPolyTermwiseEqv.append hr ht

/-- Pull through any head-independent factor on the SAME coefficient
carrier. No factorization of the remaining tail measure is assumed. -/
theorem partialGaussianHead_mul_independent (p q : RatPoly)
    (hq : HasQuaternionBlockDegree 0 0 q) :
    RatPolyCoeffEqv (partialGaussianHead (polyMul p q))
      (polyMul (partialGaussianHead p) (dropHeadPolynomial q)) := by
  intro weight
  exact ratWeightedSum_termwise_eqv weight (conditional_product p q hq)

/-- The actual block-one radius is independent of the integrated head. -/
theorem tailRadius_independent : HasQuaternionBlockDegree 0 0 (quaternionRadiusPolynomial 1) :=
  hasQuaternionBlockDegree_radius 1 0

theorem dropHeadPolynomial_tailRadius :
    dropHeadPolynomial (quaternionRadiusPolynomial 1) = quaternionRadiusPolynomial 0 := rfl

theorem partialGaussianHead_mul_radius (p : RatPoly) :
    RatPolyCoeffEqv (partialGaussianHead (polyMul p (quaternionRadiusPolynomial 1)))
      (polyMul (partialGaussianHead p) (quaternionRadiusPolynomial 0)) :=
  partialGaussianHead_mul_independent p _ tailRadius_independent

theorem partialGaussianHead_radius_mul (p : RatPoly) :
    RatPolyCoeffEqv (partialGaussianHead (polyMul (quaternionRadiusPolynomial 1) p))
      (polyMul (quaternionRadiusPolynomial 0) (partialGaussianHead p)) :=
  (partialGaussianHead_congr (RatPolyCoeffEqv.mul_comm _ _)).trans
    ((partialGaussianHead_mul_radius p).trans (RatPolyCoeffEqv.mul_comm _ _))

end YMGap.Continuum.SU2QuaternionHeadGaussianConditionalProduct

#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianConditionalProduct.partialGaussianHead_smul
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianConditionalProduct.partialGaussianHead_one
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianConditionalProduct.partialGaussianHead_mul_independent
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianConditionalProduct.tailRadius_independent
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianConditionalProduct.dropHeadPolynomial_tailRadius
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianConditionalProduct.partialGaussianHead_mul_radius
#print axioms YMGap.Continuum.SU2QuaternionHeadGaussianConditionalProduct.partialGaussianHead_radius_mul
