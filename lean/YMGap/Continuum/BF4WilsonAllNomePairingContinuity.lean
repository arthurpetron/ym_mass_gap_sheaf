/-
# Pairing continuity for the literal-width all-nome Wilson form

Sharp Cauchy--Schwarz for the actual all-nome intrinsic form turns the
existing computed squared-distance tolerance into a two-sided pairing
tolerance.  The diagonal ceiling is obtained from the same form's
parallelogram estimate and literal difference cancellation.

No small-nome premise, widened spatial carrier, completion, or new analytic
input is introduced here.
-/

import YMGap.Continuum.BF4WilsonAllNomeSeminorm
import YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity

namespace YMGap.Continuum.BF4WilsonAllNomePairingContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
  (sum difference)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
  (intrinsicForm intrinsicForm_symm intrinsicForm_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeFormLaws
  (intrinsicForm_sum_left intrinsicForm_difference_left intrinsicForm_difference_right)
open YMGap.Continuum.BF4WilsonAllNomeCauchySchwarz
  (intrinsicForm_cauchySchwarz)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm
  (distSq pairing_sum_bound)
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
  (smallTolerance smallTolerance_pos smallTolerance_budget signed_small_of_square
    pairingTolerance)

private theorem mul_mono_right {F a b : CReal}
    (hF : leEv czero F) (hab : leEv a b) :
    leEv (mul a F) (mul b F) :=
  leEv_trans (leEv_of_equiv (CRealAlg.cmul_comm a F))
    (leEv_trans (leEv_mul_nonneg_left hF hab)
      (leEv_of_equiv (CRealAlg.cmul_comm F b)))

private theorem sub_add_sub (a b c : CReal) :
    Equiv (add (sub a b) (sub b c)) (sub a c) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
    (.add (.var 0) (.neg (.var 2))) (by decide)
    (fun | 0 => a.approx n | 1 => b.approx n | _ => c.approx n)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

local notation "F" => intrinsicForm hw0 hw1
local notation "d" => distSq hw0 hw1

/-- Sharp Cauchy--Schwarz supplies the displayed scalar tolerance for the
actual intrinsic pairing. -/
theorem pairing_small {width : Nat} (x y : IntrinsicExpression width)
    (B : Q') (hB : (0 : Q') <= B) (r : Q') (hr : (0 : Q') < r)
    (hx : leEv (F x x) (ofQ' (smallTolerance B hB r)))
    (hy : leEv (F y y) (ofQ' B)) :
    leRat (F x y) r ∧ leRat (neg (F x y)) r := by
  apply signed_small_of_square _ r hr
  have hdelta : leEv czero (ofQ' (smallTolerance B hB r)) :=
    leEv_ofQ'_of_approx_ge (fun _ => Q'.le_of_lt (smallTolerance_pos B hB hr))
  have hprod := leEv_trans
    (mul_mono_right (intrinsicForm_nonnegative hw0 hw1 y) hx)
    (leEv_mul_nonneg_left hdelta hy)
  exact leEv_trans (intrinsicForm_cauchySchwarz hw0 hw1 x y)
    (leEv_trans hprod
      (leEv_le_ofQ'_of_approx_le (fun _ => smallTolerance_budget B hB hr)))

/-- Both errors are literal intrinsic differences in the same fixed-width
carrier. -/
theorem pairing_difference_split {width : Nat}
    (x x' y y' : IntrinsicExpression width) :
    Equiv (sub (F x y) (F x' y'))
      (add (F (difference x x') y) (F (difference y y') x')) := by
  have hleft := intrinsicForm_difference_left hw0 hw1 x x' y
  have hright := (intrinsicForm_symm hw0 hw1 (difference y y') x').trans
    (intrinsicForm_difference_right hw0 hw1 x' y y')
  exact ((Equiv_add hleft hright).trans (sub_add_sub _ _ _)).symm

/-- Only the unchanged diagonals of `y` and `x'` require the supplied
ceiling. -/
theorem pairing_close {width : Nat}
    (x x' y y' : IntrinsicExpression width) (B : Q') (hB : (0 : Q') <= B)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hx : leEv (d x x') (ofQ' (pairingTolerance B hB epsilon)))
    (hy : leEv (d y y') (ofQ' (pairingTolerance B hB epsilon)))
    (hynorm : leEv (F y y) (ofQ' B))
    (hxnorm : leEv (F x' x') (ofQ' B)) :
    leRat (sub (F x y) (F x' y')) epsilon ∧
      leRat (sub (F x' y') (F x y)) epsilon := by
  have hr := ExpNeg.half_mul_pos epsilon hepsilon
  have h1 := pairing_small hw0 hw1 (difference x x') y B hB _ hr hx hynorm
  have h2 := pairing_small hw0 hw1 (difference y y') x' B hB _ hr hy hxnorm
  have hsplit := pairing_difference_split hw0 hw1 x x' y y'
  have hreverse : Equiv (sub (F x' y') (F x y))
      (add (neg (F (difference x x') y)) (neg (F (difference y y') x'))) :=
    (SumOfSquares.Equiv_of_approx_eqv
      (fun _ => Q'.eqv_symm (Q'.neg_sub_eqv _ _))).trans
      ((CReal.neg_congr hsplit).trans
        (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.neg_add_eqv _ _)))
  exact ⟨CReal.leRat_of_equiv hsplit
      (leRat_mono (leRat_add h1.1 h2.1) (Q'.le_of_eqv (ExpNeg.two_halves epsilon))),
    CReal.leRat_of_equiv hreverse
      (leRat_mono (leRat_add h1.2 h2.2) (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))⟩

private theorem difference_add_anchor {width : Nat}
    (x anchor u : IntrinsicExpression width) :
    Equiv (F (sum (difference x anchor) anchor) u) (F x u) :=
  (intrinsicForm_sum_left hw0 hw1 (difference x anchor) anchor u).trans
    ((Equiv_add (intrinsicForm_difference_left hw0 hw1 x anchor u)
      (Equiv.refl (F anchor u))).trans
        (SumOfSquares.Equiv_of_approx_eqv (fun n =>
          Q'.sub_add_cancel_eqv ((F x u).approx n) ((F anchor u).approx n))))

/-- The diagonal ceiling is internal to the same all-nome form. -/
theorem diagonal_anchor_bound {width : Nat}
    (x anchor : IntrinsicExpression width) :
    leEv (F x x)
      (add (add (d x anchor) (d x anchor))
        (add (F anchor anchor) (F anchor anchor))) := by
  let s := sum (difference x anchor) anchor
  have hpin : Equiv (F s s) (F x x) :=
    (difference_add_anchor hw0 hw1 x anchor s).trans
      ((intrinsicForm_symm hw0 hw1 x s).trans
        (difference_add_anchor hw0 hw1 x anchor x))
  exact leEv_trans (leEv_of_equiv hpin.symm)
    (pairing_sum_bound hw0 hw1 (difference x anchor) anchor)

#print axioms pairing_small
#print axioms pairing_difference_split
#print axioms pairing_close
#print axioms diagonal_anchor_bound

end YMGap.Continuum.BF4WilsonAllNomePairingContinuity
