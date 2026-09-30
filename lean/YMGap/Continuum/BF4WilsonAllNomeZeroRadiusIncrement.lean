/-
# Exact all-nome time increment for arbitrary zero-radius Wilson syntax

The source is any signed `WindowExpression` supported at time zero. The
increment and reflected pairing use the existing original joint limit on
the same literal-width carrier. This file adds no decay or analytic input.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeIncrement
import YMGap.Continuum.BF4WilsonAllNomeLoopTimePin

namespace YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
  (shift shift_zero shift_comp shift_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
  (advance advance_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity
  (originalJoint_padding)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
open YMGap.Continuum.BF4WilsonJointFunctionalLaws
open YMGap.Continuum.BF4WilsonAllNomeTimeIncrement

attribute [local irreducible] originalJointLimit intrinsicForm

/-- The same signed window expression at time zero and time `n`. -/
def differenceAt {width : Nat} (e : WindowExpression width) (n : Nat) :
    WindowExpression width := difference e (shift n e)

def squareAt {width : Nat} (e : WindowExpression width) (n : Nat) :
    WindowExpression width := .mul (differenceAt e n) (differenceAt e n)

theorem square_within {width : Nat} {e : WindowExpression width}
    (he : Within 0 e) (n : Nat) : Within n (squareAt e n) :=
  let h0 := within_mono (Nat.zero_le n) e he
  let hn : Within n (shift n e) := by
    simpa only [Nat.zero_add] using shift_within 0 n e he
  ⟨difference_within h0 hn, difference_within h0 hn⟩

def increment {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (e : WindowExpression width) (he : Within 0 e)
    (n : Nat) : CReal :=
  originalJointLimit hw0 hw1 n (squareAt e n) (square_within he n)

/-- An arbitrary zero-radius expression, retaining its signed syntax. -/
def state {width : Nat} (e : WindowExpression width) (he : Within 0 e) :
    IntrinsicExpression width := ⟨0, e, he⟩

private theorem mirror_shift_zero {width : Nat} (H m : Nat) (hm : m ≤ H) :
    ∀ e : WindowExpression width, (he : Within 0 e) →
      mirror H (shift (H-m) e) = shift (H+m) e
  | .one, _ => rfl
  | .loop offset value spin, he => by
      have hz : offset = 0 := Nat.eq_zero_of_le_zero he
      subst offset
      change WindowExpression.loop (2*H-(0+(H-m))) value spin =
        WindowExpression.loop (0+(H+m)) value spin
      congr 1
      omega
  | .add a b, he => by
      change WindowExpression.add (mirror H (shift (H-m) a))
          (mirror H (shift (H-m) b)) =
        WindowExpression.add (shift (H+m) a) (shift (H+m) b)
      rw [mirror_shift_zero H m hm a he.1,
        mirror_shift_zero H m hm b he.2]
  | .mul a b, he => by
      change WindowExpression.mul (mirror H (shift (H-m) a))
          (mirror H (shift (H-m) b)) =
        WindowExpression.mul (shift (H+m) a) (shift (H+m) b)
      rw [mirror_shift_zero H m hm a he.1,
        mirror_shift_zero H m hm b he.2]
  | .smul c a, he => by
      change WindowExpression.smul c (mirror H (shift (H-m) a)) =
        WindowExpression.smul c (shift (H+m) a)
      exact congrArg (WindowExpression.smul c)
        (mirror_shift_zero H m hm a he)

/-- The stationary lag is still computed from the original signed source,
not from factorization of interacting expectations. -/
def lagExpressionAt {width : Nat} (e : WindowExpression width) (n : Nat) :
    WindowExpression width := .mul (shift n e) e

theorem lag_within {width : Nat} {e : WindowExpression width}
    (he : Within 0 e) (n : Nat) : Within n (lagExpressionAt e n) :=
  ⟨by simpa only [Nat.zero_add] using shift_within 0 n e he,
    within_mono (Nat.zero_le n) e he⟩

def lagMomentAt {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (e : WindowExpression width) (he : Within 0 e)
    (n : Nat) : CReal :=
  originalJointLimit hw0 hw1 n (lagExpressionAt e n) (lag_within he n)

private theorem shift0_within {width : Nat} (e : WindowExpression width)
    (he : Within 0 e) (t L : Nat) (ht : t ≤ L) :
    Within L (shift t e) := by
  have h : Within t (shift t e) := by
    simpa only [Nat.zero_add] using shift_within 0 t e he
  exact within_mono ht _ h

theorem pair_lag {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) {width : Nat}
    (e : WindowExpression width) (he : Within 0 e)
    (L s t : Nat) (hst : s ≤ t) (ht : t ≤ L) :
    Equiv
      (originalJointLimit hw0 hw1 L (.mul (shift t e) (shift s e))
        ⟨shift0_within e he t L ht,
          shift0_within e he s L (Nat.le_trans hst ht)⟩)
      (lagMomentAt hw0 hw1 e he (t-s)) := by
  have h := originalJoint_padding hw0 hw1 (t-s) s (L-t)
    (lagExpressionAt e (t-s)) (lag_within he (t-s))
  have htime : (t-s)+s+(L-t)=L := by omega
  have hsource : shift s (lagExpressionAt e (t-s)) =
      .mul (shift t e) (shift s e) := by
    change WindowExpression.mul (shift s (shift (t-s) e)) (shift s e) = _
    rw [shift_comp, Nat.sub_add_cancel hst]
  simpa only [htime, hsource, lagMomentAt] using h

private theorem qring (a b : PolyExpr) (h : normalize a = normalize b)
    (env : Nat → Q') : (eval env a).eqv (eval env b) :=
  poly_identity_of_normal_eq a b h env

/-- Exact original-joint squared-increment polarization, including `n=0`. -/
theorem increment_pin {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) {width : Nat}
    (e : WindowExpression width) (he : Within 0 e) (n : Nat) :
    Equiv (increment hw0 hw1 e he n)
      (CReal.mul (ofQ' 2)
        (CReal.sub (lagMomentAt hw0 hw1 e he 0)
          (lagMomentAt hw0 hw1 e he n))) := by
  let e0 := e
  let en := shift n e
  have h0 : Within n e0 := within_mono (Nat.zero_le n) e he
  have hn : Within n en := by
    simpa only [Nat.zero_add] using shift_within 0 n e he
  have heq := joint_difference_product hw0 hw1 n e0 en e0 en h0 hn h0 hn
  have hc := joint_congr hw0 hw1 n (.mul e0 en) (.mul en e0)
    ⟨h0,hn⟩ ⟨hn,h0⟩
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.var 1)) (.mul (.var 1) (.var 0))
      (by decide) (fun | 0 => sourcePolynomial e0 | _ => sourcePolynomial en))
  have h00 := pair_lag hw0 hw1 e he n 0 0 (Nat.le_refl _) (Nat.zero_le _)
  have hnn := pair_lag hw0 hw1 e he n n n (Nat.le_refl _) (Nat.le_refl _)
  have hn0 := pair_lag hw0 hw1 e he n 0 n (Nat.zero_le _) (Nat.le_refl _)
  simp only [shift_zero] at h00 hn0
  have hp := equiv_add (equiv_sub h00 (Equiv.trans hc hn0))
    (equiv_sub hnn hn0)
  simp only [Nat.sub_self, Nat.sub_zero] at hp
  exact Equiv.trans heq (Equiv.trans hp
    (SumOfSquares.Equiv_of_approx_eqv (fun k =>
      qring (.add (.add (.var 0) (.neg (.var 1)))
        (.add (.var 0) (.neg (.var 1))))
        (.mul (.const 2) (.add (.var 0) (.neg (.var 1))))
        (by decide)
        (fun | 0 => (lagMomentAt hw0 hw1 e he 0).approx k
             | _ => (lagMomentAt hw0 hw1 e he n).approx k))))

/-- The literal signed source has the same reflected lag pairing. -/
theorem time_pairing_lag {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) {width : Nat}
    (e : WindowExpression width) (he : Within 0 e) (m n : Nat) :
    Equiv
      (intrinsicForm hw0 hw1 (advance m (state e he))
        (advance n (state e he)))
      (lagMomentAt hw0 hw1 e he (m+n)) := by
  let H := max m n
  have hm : m ≤ H := Nat.le_max_left _ _
  have hn : n ≤ H := Nat.le_max_right _ _
  have hmirror : mirror H (shift (H-m) e) = shift (H+m) e :=
    mirror_shift_zero H m hm e he
  have hlag : (H+m)-(H-n)=m+n := by omega
  have h := pair_lag hw0 hw1 e he (2*H) (H-n) (H+m)
    (by omega) (by omega)
  simpa only [intrinsicForm, commonForm, state, advance, chart,
    Nat.zero_add, hmirror, hlag, H] using h

/-- Exact equality with the loss of the SAME reflected pairing. -/
theorem increment_reflected_pin {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) {width : Nat}
    (e : WindowExpression width) (he : Within 0 e) (n : Nat) :
    Equiv (increment hw0 hw1 e he n)
      (mul (ofQ' 2)
        (sub (intrinsicForm hw0 hw1 (state e he) (state e he))
          (intrinsicForm hw0 hw1 (state e he)
            (advance n (state e he))))) := by
  have h0 : Equiv
      (intrinsicForm hw0 hw1 (state e he) (state e he))
      (lagMomentAt hw0 hw1 e he 0) := by
    simpa only [advance_zero] using time_pairing_lag hw0 hw1 e he 0 0
  have hn : Equiv
      (intrinsicForm hw0 hw1 (state e he) (advance n (state e he)))
      (lagMomentAt hw0 hw1 e he n) := by
    simpa only [advance_zero, Nat.zero_add] using
      time_pairing_lag hw0 hw1 e he 0 n
  exact (increment_pin hw0 hw1 e he n).trans
    (Pivot2.mul_congr_right (equiv_sub h0.symm hn.symm))

end YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement

#print axioms YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement.differenceAt
#print axioms YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement.squareAt
#print axioms YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement.square_within
#print axioms YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement.increment
#print axioms YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement.state
#print axioms YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement.pair_lag
#print axioms YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement.increment_pin
#print axioms YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement.time_pairing_lag
#print axioms YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement.increment_reflected_pin
