/-
# Ordinary Cauchy--Schwarz for the original signed-time Wilson mean

The finite ordinary product inequality passes through the existing original
three-regulator limits, retaining the distinct convergence witnesses for all
three products. A common guarded window then gives the inequality for the
computed-radius signed mean. Zero ordinary square implies zero pairing with
every signed test, without square roots or a positivity oracle.

This is an ordinary ambient-state result, not a replacement for the reflected
OS form. Its consumer is spatial-base transport of contextual nullity. The
fixed-nome guards, canonical OS and changing-spacing obligations are unchanged.
-/

import YMGap.Continuum.BF4WilsonSignedTimeFiniteCauchySchwarz

namespace YMGap.Continuum.BF4WilsonSignedTimeCauchySchwarz

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSignedTimeExpression
open YMGap.Continuum.BF4WilsonSignedTimeExpectation
open YMGap.Continuum.BF4WilsonSignedTimeFiniteCauchySchwarz
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (WindowExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) {base : Nat} (hb : 0 < base)

attribute [local irreducible] chartScalar spatialLimit

/-- Ordinary mixed products, each with its own original convergence witness. -/
theorem spatialLimit_cauchySchwarz (H : Nat) (e f : WindowExpression base)
    (he : BF4ExactSlabFixedSpatialWilsonWindow.Within (2*H) e)
    (hf : BF4ExactSlabFixedSpatialWilsonWindow.Within (2*H) f) :
    leEv (mul (spatialLimit hw0 hw1 H (.mul e f) ⟨he,hf⟩ hsmall hd hs hb)
        (spatialLimit hw0 hw1 H (.mul e f) ⟨he,hf⟩ hsmall hd hs hb))
      (mul (spatialLimit hw0 hw1 H (.mul e e) ⟨he,he⟩ hsmall hd hs hb)
        (spatialLimit hw0 hw1 H (.mul f f) ⟨hf,hf⟩ hsmall hd hs hb)) := by
  have hxy := spatial_diagonal_converges hw0 hw1 H (.mul e f) ⟨he,hf⟩ hsmall hd hs hb
  have hxx := spatial_diagonal_converges hw0 hw1 H (.mul e e) ⟨he,he⟩ hsmall hd hs hb
  have hyy := spatial_diagonal_converges hw0 hw1 H (.mul f f) ⟨hf,hf⟩ hsmall hd hs hb
  refine leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hxy hxy)
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hxx hyy) ?_
  intro n epsilon hepsilon
  refine ⟨0, fun i _ => ?_⟩
  change chartScalar hw0 hw1 H (.mul e f) n n n *
      chartScalar hw0 hw1 H (.mul e f) n n n ≤
    chartScalar hw0 hw1 H (.mul e e) n n n *
      chartScalar hw0 hw1 H (.mul f f) n n n + epsilon
  exact Q'.le_trans' _ _ _ (chartScalar_cauchySchwarz hw0 hw1 H e f he hf n n n)
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))

/-- Sharp ordinary Cauchy--Schwarz on the actual signed-time expression carrier. -/
theorem mean_cauchySchwarz (e f : Expression base) :
    leEv (mul (mean hw0 hw1 hsmall hd hs hb (.mul e f))
        (mean hw0 hw1 hsmall hd hs hb (.mul e f)))
      (mul (mean hw0 hw1 hsmall hd hs hb (.mul e e))
        (mean hw0 hw1 hsmall hd hs hb (.mul f f))) := by
  let H := max (radius e) (radius f)
  have he : Within H e := within_mono (Nat.le_max_left _ _) e (within_radius e)
  have hf : Within H f := within_mono (Nat.le_max_right _ _) f (within_radius f)
  have hxy := mean_at hw0 hw1 hsmall hd hs hb H (.mul e f) ⟨he,hf⟩
  have hxx := mean_at hw0 hw1 hsmall hd hs hb H (.mul e e) ⟨he,he⟩
  have hyy := mean_at hw0 hw1 hsmall hd hs hb H (.mul f f) ⟨hf,hf⟩
  exact leEv_trans (leEv_of_equiv (Pivot2.mul_congr hxy hxy))
    (leEv_trans (spatialLimit_cauchySchwarz hw0 hw1 hsmall hd hs hb H
      (window H e) (window H f) (window_within H e he) (window_within H f hf))
      (leEv_of_equiv (Pivot2.mul_congr hxx.symm hyy.symm)))

private theorem zero_of_square_le_zero (A : CReal)
    (h : leEv (mul A A) (ofQ' 0)) : Equiv A (ofQ' 0) := by
  intro epsilon he
  obtain ⟨index, hN⟩ := h (epsilon*epsilon) (Q'.mul_pos he he)
  refine ⟨index, fun n hn => ?_⟩
  have hs : A.approx n * A.approx n ≤ epsilon*epsilon := by
    have hs := hN n hn
    change A.approx n * A.approx n ≤ 0 + epsilon*epsilon at hs
    rwa [Q'.zero_add'] at hs
  have ha := Q'.abs_le_two_sided (Q'.abs_le_of_sq_le_sq he hs)
  constructor
  · exact Q'.le_trans' _ _ _ ha.1 (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _)))
  · apply Q'.le_add_of_sub_le
    change 0 + -A.approx n ≤ epsilon
    rw [Q'.zero_add']
    exact ha.2

/-- Zero ordinary square annihilates every signed test at this spatial base. -/
theorem mean_radical_zero (e f : Expression base)
    (hnull : Equiv (mean hw0 hw1 hsmall hd hs hb (.mul e e)) (ofQ' 0)) :
    Equiv (mean hw0 hw1 hsmall hd hs hb (.mul e f)) (ofQ' 0) :=
  zero_of_square_le_zero _ (leEv_trans
    (mean_cauchySchwarz hw0 hw1 hsmall hd hs hb e f)
    (leEv_of_equiv ((Pivot2.mul_congr_left hnull).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun n =>
        Q'.zero_mul_eqv ((mean hw0 hw1 hsmall hd hs hb (.mul f f)).approx n))))))

end YMGap.Continuum.BF4WilsonSignedTimeCauchySchwarz

#print axioms YMGap.Continuum.BF4WilsonSignedTimeCauchySchwarz.spatialLimit_cauchySchwarz
#print axioms YMGap.Continuum.BF4WilsonSignedTimeCauchySchwarz.mean_cauchySchwarz
#print axioms YMGap.Continuum.BF4WilsonSignedTimeCauchySchwarz.mean_radical_zero
