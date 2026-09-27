/-
# Ordinary square-nullity transports every ambient context across spatial bases

All-test contextual equality is equivalent to zero mean of the ordinary
squared difference. Cauchy--Schwarz makes the criterion sufficient, including
against tests that appear only at a larger spatial base. The original mean's
inclusion identity therefore constructs an injective map of the actual
observable quotients, preserving product, linear operations, both time
directions, reflection and mean.

No OS-null ideal is used. A spatial inclusion of these discrete-time ambient
observables is not yet a canonical reflected OS root or a continuum theory.
-/

import YMGap.Continuum.BF4WilsonSignedTimeCauchySchwarz
import YMGap.Continuum.BF4WilsonSignedTimeBaseInclusion
import YMGap.Continuum.BF4WilsonSignedTimeObservable

namespace YMGap.Continuum.BF4WilsonSignedTimeContextInclusion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSignedTimeExpression
open YMGap.Continuum.BF4WilsonSignedTimeExpectation
open YMGap.Continuum.BF4WilsonSignedTimeContext
open YMGap.Continuum.BF4WilsonSignedTimeCauchySchwarz
open YMGap.Continuum.BF4WilsonSignedTimeBaseInclusion
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Literal rational signed difference, retaining both original expressions. -/
def difference {base : Nat} (a b : Expression base) : Expression base :=
  .add a (.smul (-1) b)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) {base : Nat} (hb : 0 < base)

local notation "E" => mean hw0 hw1 hsmall hd hs hb

/-- The ordinary mean of a tested difference is the difference of its means. -/
theorem mean_difference_mul (a b t : Expression base) :
    Equiv (E (.mul (difference a b) t)) (sub (E (.mul a t)) (E (.mul b t))) := by
  have hexpand : Equiv (E (.mul (difference a b) t))
      (E (.add (.mul a t) (.smul (-1) (.mul b t)))) := by
    apply mean_of_polynomial_eq hw0 hw1 hsmall hd hs hb
    intro H r k
    apply SU2QuaternionTranslationPolynomialImages.PaddedPolynomialCoeffEqv.of_coeff
    change RatPolyCoeffEqv
      (polyMul (polyAdd (insertion H r k a) (polySmul (-1) (insertion H r k b)))
        (insertion H r k t)) _
    rw [polyMul_add_left_exact]
    exact (RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.polyMul_smul_left (-1) _ _)
  refine hexpand.trans ((mean_add hw0 hw1 hsmall hd hs hb _ _).trans
    (Equiv_add (Equiv.refl _) ((mean_smul hw0 hw1 hsmall hd hs hb (-1) _).trans ?_)))
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 ((E (.mul b t)).approx n))
    (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv ((E (.mul b t)).approx n)))

/-- One ordinary squared difference detects all signed-time tests. -/
theorem context_iff_square_zero (a b : Expression base) :
    ContextEq hw0 hw1 hsmall hd hs hb a b ↔
      Equiv (E (.mul (difference a b) (difference a b))) (ofQ' 0) := by
  constructor
  · intro h
    exact (mean_difference_mul hw0 hw1 hsmall hd hs hb a b (difference a b)).trans
      ((Equiv_add (h (difference a b)) (Equiv.refl _)).trans
        (SumOfSquares.Equiv_of_approx_eqv (fun n =>
          Q'.add_neg_self_eqv ((E (.mul b (difference a b))).approx n))))
  · intro h t
    apply CReal.Equiv_of_sub_eqv_zero
    exact (mean_difference_mul hw0 hw1 hsmall hd hs hb a b t).symm.trans
      (mean_radical_zero hw0 hw1 hsmall hd hs hb (difference a b) t h)

/-- The extra larger-base tests are handled by ordinary square-nullity, not
by assuming that mean inclusion already gives contextual inclusion. -/
theorem context_include {larger : Nat} (h : base ≤ larger) {a b : Expression base}
    (hab : ContextEq hw0 hw1 hsmall hd hs hb a b) :
    ContextEq hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le hb h)
      (inclusion h a) (inclusion h b) := by
  apply (context_iff_square_zero hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le hb h) _ _).mpr
  have hz := (context_iff_square_zero hw0 hw1 hsmall hd hs hb a b).mp hab
  exact (mean_include hw0 hw1 hsmall hd hs h hb
    (.mul (difference a b) (difference a b))).symm.trans hz

/-- Inclusion both preserves and reflects the full contextual relation. -/
theorem context_include_iff {larger : Nat} (h : base ≤ larger) (a b : Expression base) :
    ContextEq hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le hb h)
      (inclusion h a) (inclusion h b) ↔ ContextEq hw0 hw1 hsmall hd hs hb a b := by
  constructor
  · intro hab
    apply (context_iff_square_zero hw0 hw1 hsmall hd hs hb a b).mpr
    have hz := (context_iff_square_zero hw0 hw1 hsmall hd hs
      (Nat.lt_of_lt_of_le hb h) (inclusion h a) (inclusion h b)).mp hab
    exact (mean_include hw0 hw1 hsmall hd hs h hb
      (.mul (difference a b) (difference a b))).trans hz
  · exact context_include hw0 hw1 hsmall hd hs hb h

local notation:max "O" hb':arg => BF4WilsonSignedTimeObservable.Observable hw0 hw1 hsmall hd hs hb'

/-- Constructed inclusion of the actual contextual quotients. -/
def observableInclusion {larger : Nat} (h : base ≤ larger) :
    O hb → O (Nat.lt_of_lt_of_le hb h) :=
  Quotient.lift
    (fun e => BF4WilsonSignedTimeObservable.ofExpression hw0 hw1 hsmall hd hs
      (Nat.lt_of_lt_of_le hb h) (inclusion h e))
    (fun _ _ he => Quotient.sound (context_include hw0 hw1 hsmall hd hs hb h he))

theorem observableInclusion_injective {larger : Nat} (h : base ≤ larger)
    (a b : O hb) (hab : observableInclusion hw0 hw1 hsmall hd hs hb h a =
      observableInclusion hw0 hw1 hsmall hd hs hb h b) : a = b := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      exact Quotient.sound ((context_include_iff hw0 hw1 hsmall hd hs hb h a b).mp
        (Quotient.exact hab))

theorem observableInclusion_mean {larger : Nat} (h : base ≤ larger) (a : O hb) :
    BF4WilsonSignedTimeObservable.meanRC hw0 hw1 hsmall hd hs
        (Nat.lt_of_lt_of_le hb h) (observableInclusion hw0 hw1 hsmall hd hs hb h a) =
      BF4WilsonSignedTimeObservable.meanRC hw0 hw1 hsmall hd hs hb a := by
  induction a using Quotient.inductionOn with
  | h a => exact Quotient.sound (mean_include hw0 hw1 hsmall hd hs h hb a).symm

theorem observableInclusion_mul {larger : Nat} (h : base ≤ larger) (a b : O hb) :
    observableInclusion hw0 hw1 hsmall hd hs hb h
        (BF4WilsonSignedTimeObservable.mul hw0 hw1 hsmall hd hs hb a b) =
      BF4WilsonSignedTimeObservable.mul hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le hb h)
        (observableInclusion hw0 hw1 hsmall hd hs hb h a)
        (observableInclusion hw0 hw1 hsmall hd hs hb h b) := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b => rfl

theorem observableInclusion_one {larger : Nat} (h : base ≤ larger) :
    observableInclusion hw0 hw1 hsmall hd hs hb h
        (BF4WilsonSignedTimeObservable.one hw0 hw1 hsmall hd hs hb) =
      BF4WilsonSignedTimeObservable.one hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le hb h) := rfl

theorem observableInclusion_add {larger : Nat} (h : base ≤ larger) (a b : O hb) :
    observableInclusion hw0 hw1 hsmall hd hs hb h
        (BF4WilsonSignedTimeObservable.add hw0 hw1 hsmall hd hs hb a b) =
      BF4WilsonSignedTimeObservable.add hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le hb h)
        (observableInclusion hw0 hw1 hsmall hd hs hb h a)
        (observableInclusion hw0 hw1 hsmall hd hs hb h b) := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b => rfl

theorem observableInclusion_smul {larger : Nat} (h : base ≤ larger) (s : Q') (a : O hb) :
    observableInclusion hw0 hw1 hsmall hd hs hb h
        (BF4WilsonSignedTimeObservable.smul hw0 hw1 hsmall hd hs hb s a) =
      BF4WilsonSignedTimeObservable.smul hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le hb h) s
        (observableInclusion hw0 hw1 hsmall hd hs hb h a) := by
  induction a using Quotient.inductionOn with
  | h a => rfl

theorem observableInclusion_forward {larger : Nat} (h : base ≤ larger) (n : Nat) (a : O hb) :
    observableInclusion hw0 hw1 hsmall hd hs hb h
        (BF4WilsonSignedTimeObservable.forwardTime hw0 hw1 hsmall hd hs hb n a) =
      BF4WilsonSignedTimeObservable.forwardTime hw0 hw1 hsmall hd hs
        (Nat.lt_of_lt_of_le hb h) n (observableInclusion hw0 hw1 hsmall hd hs hb h a) := by
  induction a using Quotient.inductionOn with
  | h a => exact congrArg (BF4WilsonSignedTimeObservable.ofExpression hw0 hw1 hsmall hd hs
      (Nat.lt_of_lt_of_le hb h)) (include_forward h n a)

theorem observableInclusion_backward {larger : Nat} (h : base ≤ larger) (n : Nat) (a : O hb) :
    observableInclusion hw0 hw1 hsmall hd hs hb h
        (BF4WilsonSignedTimeObservable.backwardTime hw0 hw1 hsmall hd hs hb n a) =
      BF4WilsonSignedTimeObservable.backwardTime hw0 hw1 hsmall hd hs
        (Nat.lt_of_lt_of_le hb h) n (observableInclusion hw0 hw1 hsmall hd hs hb h a) := by
  induction a using Quotient.inductionOn with
  | h a => exact congrArg (BF4WilsonSignedTimeObservable.ofExpression hw0 hw1 hsmall hd hs
      (Nat.lt_of_lt_of_le hb h)) (include_backward h n a)

theorem observableInclusion_reflection {larger : Nat} (h : base ≤ larger) (a : O hb) :
    observableInclusion hw0 hw1 hsmall hd hs hb h
        (BF4WilsonSignedTimeObservable.reflection hw0 hw1 hsmall hd hs hb a) =
      BF4WilsonSignedTimeObservable.reflection hw0 hw1 hsmall hd hs
        (Nat.lt_of_lt_of_le hb h) (observableInclusion hw0 hw1 hsmall hd hs hb h a) := by
  induction a using Quotient.inductionOn with
  | h a => exact congrArg (BF4WilsonSignedTimeObservable.ofExpression hw0 hw1 hsmall hd hs
      (Nat.lt_of_lt_of_le hb h)) (include_reflect h a)

end YMGap.Continuum.BF4WilsonSignedTimeContextInclusion

#print axioms YMGap.Continuum.BF4WilsonSignedTimeContextInclusion.difference
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContextInclusion.mean_difference_mul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContextInclusion.context_iff_square_zero
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContextInclusion.context_include
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContextInclusion.context_include_iff
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContextInclusion.observableInclusion
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContextInclusion.observableInclusion_injective
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContextInclusion.observableInclusion_mean
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContextInclusion.observableInclusion_mul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContextInclusion.observableInclusion_one
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContextInclusion.observableInclusion_add
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContextInclusion.observableInclusion_smul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContextInclusion.observableInclusion_forward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContextInclusion.observableInclusion_backward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeContextInclusion.observableInclusion_reflection
