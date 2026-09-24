/-
# Rational linear operations on the literal all-nome Wilson completion

The dense Wilson syntax has addition and rational scaling.  Bilinearity of
the SAME literal-width reflected form gives the quadratic distance estimates
needed by the generic explicit-modulus completion machinery.  The resulting
operations act on the existing all-nome completion; no older carrier or
analytic input is substituted.
-/

import YMGap.Continuum.BF4WilsonAllNomeCompletedInner
import YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear

namespace YMGap.Continuum.BF4WilsonAllNomeLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
  (sum difference)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra
  (smul zero)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
  (intrinsicForm intrinsicForm_symm)
open YMGap.Continuum.BF4WilsonAllNomeFormLaws
open YMGap.Continuum.BF4WilsonAllNomeSeminorm
  (distSq pairing_sum_bound seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion embed)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
  (scalarTolerance scalarTolerance_pos scalarTolerance_bound)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "F" => intrinsicForm hw0 hw1
local notation "d" => distSq hw0 hw1
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width

private theorem norm_congr (x y : IntrinsicExpression width)
    (h : ∀ z, Equiv (F x z) (F y z)) : Equiv (F x x) (F y y) :=
  (h x).trans ((intrinsicForm_symm hw0 hw1 y x).trans (h y))

private theorem difference_sum_pair
    (x x' y y' z : IntrinsicExpression width) :
    Equiv (F (difference (sum x y) (sum x' y')) z)
      (F (sum (difference x x') (difference y y')) z) := by
  have hl := (intrinsicForm_difference_left hw0 hw1 (sum x y) (sum x' y') z).trans
    (Equiv_add (intrinsicForm_sum_left hw0 hw1 x y z)
      (neg_congr (intrinsicForm_sum_left hw0 hw1 x' y' z)))
  have hr := (intrinsicForm_sum_left hw0 hw1 (difference x x') (difference y y') z).trans
    (Equiv_add (intrinsicForm_difference_left hw0 hw1 x x' z)
      (intrinsicForm_difference_left hw0 hw1 y y' z))
  refine hl.trans (Equiv.trans ?_ hr.symm)
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 2)) (.neg (.add (.var 1) (.var 3))))
    (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3))))
    (by decide)
    (fun | 0 => (F x z).approx n | 1 => (F x' z).approx n
         | 2 => (F y z).approx n | _ => (F y' z).approx n)

/-- Dense addition has the quadratic two-variable Lipschitz bound. -/
theorem distSq_sum (x x' y y' : IntrinsicExpression width) :
    leEv (d (sum x y) (sum x' y'))
      (add (add (d x x') (d x x')) (add (d y y') (d y y'))) := by
  have hpin : Equiv (d (sum x y) (sum x' y'))
      (F (sum (difference x x') (difference y y'))
        (sum (difference x x') (difference y y'))) := by
    unfold distSq
    exact norm_congr hw0 hw1 _ _
      (difference_sum_pair hw0 hw1 x x' y y')
  exact leEv_trans (leEv_of_equiv hpin)
    (pairing_sum_bound hw0 hw1 (difference x x') (difference y y'))

private theorem difference_smul_pair (c : Q')
    (x y z : IntrinsicExpression width) :
    Equiv (F (difference (smul c x) (smul c y)) z)
      (F (smul c (difference x y)) z) := by
  have hl := (intrinsicForm_difference_left hw0 hw1 (smul c x) (smul c y) z).trans
    (Equiv_add (intrinsicForm_smul_left hw0 hw1 c x z)
      (neg_congr (intrinsicForm_smul_left hw0 hw1 c y z)))
  have hr := (intrinsicForm_smul_left hw0 hw1 c (difference x y) z).trans
    (Pivot2.mul_congr_right (intrinsicForm_difference_left hw0 hw1 x y z))
  refine hl.trans (Equiv.trans ?_ hr.symm)
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
    (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))) (by decide)
    (fun | 0 => c | 1 => (F x z).approx n | _ => (F y z).approx n)

/-- Dense rational scaling has the exact squared scalar factor. -/
theorem distSq_smul (c : Q') (x y : IntrinsicExpression width) :
    Equiv (d (smul c x) (smul c y)) (mul (ofQ' (c*c)) (d x y)) := by
  let z := difference x y
  have hpin : Equiv (d (smul c x) (smul c y)) (F (smul c z) (smul c z)) := by
    unfold distSq
    exact norm_congr hw0 hw1 _ _ (difference_smul_pair hw0 hw1 c x y)
  have hscale := (intrinsicForm_smul_left hw0 hw1 c z (smul c z)).trans
    (Pivot2.mul_congr_right (intrinsicForm_smul_right hw0 hw1 c z z))
  have halg : Equiv (mul (ofQ' c) (mul (ofQ' c) (F z z)))
      (mul (ofQ' (c*c)) (F z z)) :=
    SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.eqv_symm (Q'.mul_assoc_eqv c c ((F z z).approx n)))
  exact hpin.trans (hscale.trans (halg.trans (Equiv.refl _)))

/-- Addition with the explicit quarter-tolerance modulus supplied by the
generic quadratic completion constructor. -/
def addition : (D).BinaryQuadraticLipschitz where
  toFun := sum
  contraction := distSq_sum hw0 hw1

/-- Rational scaling with its explicit scalar-dependent tolerance. -/
def scalarContinuous (c : Q') : (D).ModulusContinuous where
  toFun := smul c
  tolerance := scalarTolerance c
  tolerance_pos := fun _ => scalarTolerance_pos c
  contraction := by
    intro epsilon he x y h
    have hc : leEv czero (ofQ' (c*c)) :=
      leEv_ofQ'_of_approx_ge (fun _ => SumOfSquares.q_mul_self_nonneg c)
    exact leEv_trans (leEv_of_equiv (distSq_smul hw0 hw1 c x y))
      (leEv_trans (leEv_mul_nonneg_left hc h)
        (leEv_le_ofQ'_of_approx_le (fun _ => scalarTolerance_bound c he)))

def completedAdd : V → V → V :=
  (addition hw0 hw1 (width := width)).completionMap

def completedSmul (c : Q') : V → V :=
  (scalarContinuous hw0 hw1 (width := width) c).completionMap

def completedZero (width : Nat) : Completion hw0 hw1 width :=
  embed hw0 hw1 (zero width)

def completedNeg : V → V := completedSmul hw0 hw1 (-1)

def completedSub (x y : V) : V :=
  completedAdd hw0 hw1 x (completedNeg hw0 hw1 y)

theorem addition_cauchy_modulus (X Y : (D).Cauchy) (epsilon : Q') :
    ((addition hw0 hw1 (width := width)).mapCauchy X Y).modulus epsilon =
      max (X.modulus (HalfPow.half*(HalfPow.half*epsilon)))
        (Y.modulus (HalfPow.half*(HalfPow.half*epsilon))) := rfl

theorem scalar_cauchy_modulus (c epsilon : Q') (X : (D).Cauchy) :
    ((scalarContinuous hw0 hw1 (width := width) c).mapCauchy X).modulus epsilon =
      X.modulus (scalarTolerance c epsilon) := rfl

/-- Pointwise equality against every dense test makes two Cauchy
representatives close, with the generic zero modulus. -/
def closeOfPointwisePairingEq {X Y : (D).Cauchy}
    (h : ∀ n z, Equiv (F (X.seq n) z) (F (Y.seq n) z)) : (D).Close X Y :=
  SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull (fun n => by
    change Equiv (distSq hw0 hw1 (X.seq n) (Y.seq n)) czero
    unfold distSq
    refine (intrinsicForm_difference_left hw0 hw1
      (X.seq n) (Y.seq n) (difference (X.seq n) (Y.seq n))).trans ?_
    exact (Equiv_add (h n (difference (X.seq n) (Y.seq n))) (Equiv.refl _)).trans
      (CReal.sub_self_eqv_zero _))

/-- Dense pairing equality descends directly to equality in the SAME
all-nome completion. -/
theorem completion_eq_of_pointwise {X Y : (D).Cauchy}
    (h : ∀ n z, Equiv (F (X.seq n) z) (F (Y.seq n) z)) :
    Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y :=
  Quotient.sound ⟨closeOfPointwisePairingEq hw0 hw1 h⟩

theorem completedAdd_embed (x y : IntrinsicExpression width) :
    completedAdd hw0 hw1 (embed hw0 hw1 x) (embed hw0 hw1 y) =
      embed hw0 hw1 (sum x y) := rfl

theorem completedSmul_embed (c : Q') (x : IntrinsicExpression width) :
    completedSmul hw0 hw1 c (embed hw0 hw1 x) =
      embed hw0 hw1 (smul c x) := rfl

theorem completedZero_embed :
    completedZero hw0 hw1 width = embed hw0 hw1 (zero width) := rfl

theorem completedNeg_embed (x : IntrinsicExpression width) :
    completedNeg hw0 hw1 (embed hw0 hw1 x) =
      embed hw0 hw1 (smul (-1) x) := rfl

theorem completedSub_embed (x y : IntrinsicExpression width) :
    completedSub hw0 hw1 (embed hw0 hw1 x) (embed hw0 hw1 y) =
      embed hw0 hw1 (sum x (smul (-1) y)) := rfl

#print axioms distSq_sum
#print axioms distSq_smul
#print axioms addition
#print axioms scalarContinuous
#print axioms completedAdd
#print axioms completedSmul
#print axioms completedZero
#print axioms completedNeg
#print axioms completedSub
#print axioms addition_cauchy_modulus
#print axioms scalar_cauchy_modulus
#print axioms closeOfPointwisePairingEq
#print axioms completion_eq_of_pointwise
#print axioms completedAdd_embed
#print axioms completedSmul_embed
#print axioms completedZero_embed
#print axioms completedNeg_embed
#print axioms completedSub_embed

end YMGap.Continuum.BF4WilsonAllNomeLinear
