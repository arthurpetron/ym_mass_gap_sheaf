/-
# Rational linear closure of the witnessed original derivative graph

Graph witnesses retain explicit squared-distance moduli. Rational scaling
and addition preserve those witnesses, so the existing quotient graph domain
inherits concrete rational operations whose input and action are linear.
This does not assert density, a full-real domain, or self-adjointness.
-/

import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph
import YMGap.Continuum.BF4WilsonAllNomeGraphDistance
import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws
import YMGap.Constructive.QDivArctanSeries

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "N" => completedNeg hw0 hw1
local notation "D" => completedSub hw0 hw1
local notation "d" => completedDist hw0 hw1
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

private theorem smul_neg (c : Q') (x : V) : N (S c x) = S c (N x) := by
  unfold completedNeg
  rw [completedSmul_mul, completedSmul_mul]
  exact completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv (-1) c) x

private theorem smul_sub (c : Q') (x y : V) : D (S c x) (S c y) = S c (D x y) := by
  unfold completedSub
  rw [smul_neg hw0 hw1]
  exact (completedSmul_add hw0 hw1 c x (N y)).symm

/-- Squared distance scales by the square of the rational coefficient. -/
theorem completedDist_smul (c : Q') (x y : V) :
    d (S c x) (S c y) = RCscale (c*c) (d x y) := by
  unfold completedDist
  rw [smul_sub hw0 hw1, completedInner_smul_left,
    completedInner_smul_right, RCscale_RCscale]

private def scalarDen (c : Q') : Q' := 1+c*c

private theorem scalarDen_pos (c : Q') : (0 : Q') < scalarDen c :=
  Q'.pos_add_nonneg (by decide) (SumOfSquares.q_mul_self_nonneg c)

private def scalarTolerance (c e : Q') : Q' :=
  Q'.divPos e (scalarDen c) (scalarDen_pos c)

private theorem scalarTolerance_pos (c e : Q') (he : (0 : Q') < e) :
    (0 : Q') < scalarTolerance c e :=
  Q'.divPos_pos e (scalarDen c) (scalarDen_pos c) he

private theorem scalarTolerance_budget_nonneg (c e : Q') (he : (0 : Q') < e) :
    c*c*scalarTolerance c e ≤ e := by
  have hden : c*c ≤ scalarDen c :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg (c*c) 1 (by decide))
      (Q'.le_of_eqv (Q'.add_comm_eqv (c*c) 1))
  have ht : (0 : Q') ≤ scalarTolerance c e := Q'.le_of_lt (scalarTolerance_pos c e he)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hden ht)
    (Q'.le_of_eqv (QDivArctanSeries.mul_divPos_eqv e (scalarDen c) (scalarDen_pos c)))

private theorem scalar_distance_budget (c e : Q') (he : (0 : Q') < e)
    {x y : V} (h : RCle (d x y) (rat (scalarTolerance c e))) :
    RCle (d (S c x) (S c y)) (rat e) := by
  rw [completedDist_smul hw0 hw1]
  have hscale := RCscale_mono (SumOfSquares.q_mul_self_nonneg c) h
  have hrat : RCscale (c*c) (rat (scalarTolerance c e)) =
      rat (c*c*scalarTolerance c e) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))
  rw [hrat] at hscale
  exact RCle_trans hscale
    (leEv_le_ofQ'_of_approx_le (fun _ => scalarTolerance_budget_nonneg c e he))

/-- Scaling is witnessed by the original source stream; the explicit
modulus uses epsilon divided by one plus the squared scalar. -/
def scale {input output : V} (c : Q')
    (G : GraphLimit hw0 hw1 input output) :
    GraphLimit hw0 hw1 (S c input) (S c output) where
  source := fun n => S c (G.source n)
  modulus := fun e => G.modulus (scalarTolerance c e)
  bound := by
    intro e he n hn
    have h := G.bound (scalarTolerance c e) (scalarTolerance_pos c e he) n hn
    constructor
    · rw [completedTime_smul]
      exact scalar_distance_budget hw0 hw1 c e he h.1
    · rw [derivativeAction_smul]
      exact scalar_distance_budget hw0 hw1 c e he h.2

private theorem neg_neg (x : V) : N (N x) = x := by
  unfold completedNeg
  rw [completedSmul_mul]
  exact (completedSmul_congr hw0 hw1 (by decide : Q'.eqv ((-1 : Q')*(-1)) 1) x).trans
    (completedSmul_one hw0 hw1 x)

/-- Addition is the already checked subtraction of a scaled negative
witness, so no separate graph-distance estimate is assumed. -/
def add {x y u v : V} (G : GraphLimit hw0 hw1 x u)
    (H : GraphLimit hw0 hw1 y v) :
    GraphLimit hw0 hw1 (A x y) (A u v) := by
  have W := BF4WilsonAllNomeDerivativeGraph.subtract hw0 hw1 G
    (scale hw0 hw1 (-1) H)
  have hi : D x (S (-1) y) = A x y := by
    change A x (N (N y)) = A x y
    rw [neg_neg hw0 hw1]
  have ho : D u (S (-1) v) = A u v := by
    change A u (N (N v)) = A u v
    rw [neg_neg hw0 hw1]
  rw [hi, ho] at W
  exact W

/-- The quotient domain retains actual graph witnesses under addition. -/
def domainAdd (p q : Domain hw0 hw1 (width := width)) :
    Domain hw0 hw1 (width := width) :=
  Quotient.liftOn₂ p q
    (fun P Q => Quotient.mk (inputSetoid hw0 hw1)
      ⟨A P.1 Q.1, A P.2.1 Q.2.1, add hw0 hw1 P.2.2 Q.2.2⟩)
    (by
      intro P P' Q Q' hP hQ
      apply Quotient.sound
      change A P.1 P'.1 = A Q.1 Q'.1
      rw [hP, hQ])

/-- Rational scalar action on the existing graph quotient. -/
def domainSmul (c : Q') (p : Domain hw0 hw1 (width := width)) :
    Domain hw0 hw1 (width := width) :=
  Quotient.liftOn p
    (fun P => Quotient.mk (inputSetoid hw0 hw1)
      ⟨S c P.1, S c P.2.1, scale hw0 hw1 c P.2.2⟩)
    (by
      intro P Q h
      apply Quotient.sound
      exact congrArg (S c) h)

theorem input_add (p q : Domain hw0 hw1 (width := width)) :
    input hw0 hw1 (domainAdd hw0 hw1 p q) =
      A (input hw0 hw1 p) (input hw0 hw1 q) := by
  refine Quotient.inductionOn₂ p q ?_
  intro P Q
  rfl

theorem action_add (p q : Domain hw0 hw1 (width := width)) :
    action hw0 hw1 (domainAdd hw0 hw1 p q) =
      A (action hw0 hw1 p) (action hw0 hw1 q) := by
  refine Quotient.inductionOn₂ p q ?_
  intro P Q
  rfl

theorem input_smul (c : Q') (p : Domain hw0 hw1 (width := width)) :
    input hw0 hw1 (domainSmul hw0 hw1 c p) =
      S c (input hw0 hw1 p) := by
  refine Quotient.inductionOn p ?_
  intro P
  rfl

theorem action_smul (c : Q') (p : Domain hw0 hw1 (width := width)) :
    action hw0 hw1 (domainSmul hw0 hw1 c p) =
      S c (action hw0 hw1 p) := by
  refine Quotient.inductionOn p ?_
  intro P
  rfl

end YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear

#print axioms YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear.completedDist_smul
#print axioms YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear.scale
#print axioms YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear.add
#print axioms YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear.domainAdd
#print axioms YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear.domainSmul
#print axioms YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear.input_add
#print axioms YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear.action_add
#print axioms YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear.input_smul
#print axioms YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear.action_smul
