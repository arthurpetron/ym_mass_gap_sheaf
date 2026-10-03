/-
# Original derivative graph retains the exact core form margin

The unconditional defect-form lower bound for the actual derivative A
passes through its witnessed graph closure. Only image norms enter the
pairing modulus. On the same vacuum complement the margin is (1-q)/2,
with the original nome/width dependence retained. No equality to the
log-series graph, self-adjoint Hamiltonian or physical mass is assumed.

The sharp graph and domain bounds below instead retain the exact original
one-step kinetic floor/cap fraction. The older declarations are unchanged.
-/

import YMGap.Continuum.BF4WilsonAllNomeLogCoreGap
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphForm

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance (dist_zero_right)
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows (completedDist_time)
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (pairing_close completedInner_sub_right)
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
  (pairingTolerance pairingTolerance_pos)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defect)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeGap
  (derivative_form_ge_defect)
open YMGap.Continuum.BF4WilsonAllNomeLogCoreGap
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphForm
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "P" => pairingData hw0 hw1 (width := width)
local notation "Z" => BF4WilsonAllNomeLinear.completedZero hw0 hw1 width
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

private theorem rat_four_sum (a b : Q') :
    RCadd (RCadd (rat a) (rat a)) (RCadd (rat b) (rat b)) =
      rat ((a+a)+(b+b)) :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))

private theorem rat_two_halves (a : RC) (e : Q') :
    RCadd (RCadd a (rat (HalfPow.half*e))) (rat (HalfPow.half*e)) =
      RCadd a (rat e) := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves e))))

private theorem neg_add_cancel (a b : RC) :
    RCadd (RCneg (RCadd a b)) b = RCneg a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.neg (.add (.var 0) (.var 1))) (.var 1)) (.neg (.var 0))
      (by decide) (fun | 0 => A.approx n | _ => B'.approx n)))

private theorem negate_error {a b : RC} (e : Q')
    (h : RCle a (RCadd b (rat e))) :
    RCle (RCneg b) (RCadd (RCneg a) (rat e)) := by
  have hh := RCadd_le_add (RCSignedPairBudget.neg_mono h) (RCle_refl (rat e))
  rwa [neg_add_cancel] at hh

/-- Explicit input-pairing tail index, using only the limiting input norm
cap, graph modulus and existing pairing tolerance. -/
def graphInputPairingModulus {x y : V} (G : GraphLimit hw0 hw1 x y)
    (c : Q') (hc : (0 : Q') ≤ c) (epsilon : Q') : Nat :=
  max (G.modulus (pairingTolerance (graphPairingCap c c)
    (graphPairingCap_nonnegative c c hc) epsilon)) (G.modulus 1)

/-- Both input norm and input/time pairing converge along the SAME graph
approximants. The unbounded preimage sequence is never used as a norm cap. -/
theorem graph_input_pairings_close {x y : V} (G : GraphLimit hw0 hw1 x y)
    (c : Q') (hc : (0 : Q') ≤ c) (hcx : RCle (B x x) (rat c))
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : graphInputPairingModulus hw0 hw1 G c hc epsilon ≤ n) :
    let a := T 1 (G.source n)
    (RCle (B x x) (RCadd (B a a) (rat epsilon)) ∧
      RCle (B a a) (RCadd (B x x) (rat epsilon))) ∧
    (RCle (B x (T 1 x)) (RCadd (B a (T 1 a)) (rat epsilon)) ∧
      RCle (B a (T 1 a)) (RCadd (B x (T 1 x)) (rat epsilon))) := by
  let a := T 1 (G.source n)
  let cap := graphPairingCap c c
  have hcap : (0 : Q') ≤ cap := graphPairingCap_nonnegative c c hc
  let delta := pairingTolerance cap hcap epsilon
  have hd : (0 : Q') < delta := pairingTolerance_pos cap hcap he
  change max (G.modulus delta) (G.modulus 1) ≤ n at hn
  have hclose := (G.bound delta hd n (Nat.le_trans (Nat.le_max_left _ _) hn)).1
  have hdist : RCle (completedDist hw0 hw1 x a) (rat delta) := by
    rw [completedDist_symm]
    exact hclose
  have ht := RCle_trans (completedDist_time hw0 hw1 1 x a) hdist
  have h1 := (G.bound 1 (by decide) n (Nat.le_trans (Nat.le_max_right _ _) hn)).1
  have htri := completedDist_triangle hw0 hw1 a x Z
  rw [dist_zero_right, dist_zero_right] at htri
  have hnear : RCle (B a a) (rat ((1+1)+(c+c))) := by
    have h := RCle_trans htri
      (RCadd_le_add (RCadd_le_add h1 h1) (RCadd_le_add hcx hcx))
    rwa [rat_four_sum] at h
  have ha : RCle (B a a) (rat cap) := RCle_trans hnear
    (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_max'_right _ _))
  have hxcap : RCle (B x x) (rat cap) := RCle_trans hcx
    (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_max'_left _ _))
  have htx := RCle_trans (completedInner_time_contraction hw0 hw1 1 x) hxcap
  exact ⟨pairing_close hw0 hw1 x a x a cap hcap epsilon he hdist hdist hxcap ha,
    pairing_close hw0 hw1 x a (T 1 x) (T 1 a) cap hcap epsilon he hdist ht htx ha⟩

/-- The universal first-term bound survives the existing witnessed graph
limit, with no orthogonality requirement on its preimages. -/
theorem graph_defect_form_le {x y : V} (G : GraphLimit hw0 hw1 x y) :
    RCle (B x (defect hw0 hw1 x)) (B x y) := by
  revert G
  refine Quotient.inductionOn₂ x y ?_
  intro X Y G
  let x : V := Class X
  let y : V := Class Y
  let cx := normCeiling P X
  let cy := normCeiling P Y
  have hcx0 := normCeiling_nonnegative P X
  have hcx := completedInner_diagonal_le_normCeiling P X
  have hcy := completedInner_diagonal_le_normCeiling P Y
  change RCle (B x (defect hw0 hw1 x)) (B x y)
  rw [defect, completedInner_sub_right]
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let d := HalfPow.half*epsilon
  let e := HalfPow.half*d
  have hd : (0 : Q') < d := ExpNeg.half_mul_pos epsilon he
  have he' : (0 : Q') < e := ExpNeg.half_mul_pos d hd
  let n := max (graphInputPairingModulus hw0 hw1 G cx hcx0 e)
    (graphPairingModulus hw0 hw1 G G cx cy hcx0 d)
  have hi := graph_input_pairings_close hw0 hw1 G cx hcx0 hcx e he' n
    (Nat.le_max_left _ _)
  have ho := (graph_pairing_close hw0 hw1 G G cx cy hcx0 hcx hcy d hd n
    (Nat.le_max_right _ _)).1
  let a := T 1 (G.source n)
  have hleft := RationalScalarTwoSidedError.add_error
    (B x x) (RCneg (B x (T 1 x))) (B a a) (RCneg (B a (T 1 a))) e e
    hi.1.1 (negate_error e hi.2.2)
  have htwo : rat (e+e) = rat d :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => ExpNeg.two_halves d))
  rw [htwo] at hleft
  have hfirst := derivative_form_ge_defect hw0 hw1 (G.source n)
  rw [defect, completedInner_sub_right] at hfirst
  have h := RCle_trans hleft
    (RCadd_le_add (RCle_trans hfirst ho) (RCle_refl (rat d)))
  rwa [rat_two_halves] at h

/-- The exact original core margin survives on EVERY existing witnessed
graph input orthogonal to the SAME vacuum. -/
theorem graph_form_gap {x y : V} (G : GraphLimit hw0 hw1 x y)
    (hx : B U x = RCzero) :
    RCle (RCscale (coreMargin hw0 hw1 width) (B x x)) (B x y) :=
  RCle_trans (completed_defect_form_gap hw0 hw1 x hx)
    (graph_defect_form_le hw0 hw1 G)

/-- The sharp SAME one-step margin survives the actual witnessed derivative
graph, without a new graph, preimage bound or scalar-log identification. -/
theorem graph_form_sharp_gap {x y : V} (G : GraphLimit hw0 hw1 x y)
    (hx : B U x = RCzero) :
    RCle (RCscale
      (BF4ExactSlabFixedSpatialTransferMixingRate.mixFraction hw0 hw1 width)
      (B x x)) (B x y) := by
  have h := BF4WilsonAllNomeOneStepGap.completed_oneStep_defect_margin
    hw0 hw1 x ((completedInner_symm hw0 hw1 x U).trans hx)
  rw [← completedInner_sub_right, ← defect] at h
  exact RCle_trans h (graph_defect_form_le hw0 hw1 G)

/-- Quantitative form bound on the already constructed graph domain;
no newly postulated operator or graph is introduced. -/
theorem action_form_gap (p : Domain hw0 hw1 (width := width))
    (hp : B U (input hw0 hw1 p) = RCzero) :
    RCle (RCscale (coreMargin hw0 hw1 width)
      (B (input hw0 hw1 p) (input hw0 hw1 p)))
      (B (input hw0 hw1 p) (action hw0 hw1 p)) := by
  revert hp
  refine Quotient.inductionOn p ?_
  intro P' hp
  exact graph_form_gap hw0 hw1 P'.2.2 hp

/-- The exact kinetic fraction bounds the already constructed domain action
on its original vacuum complement. Its nome/width dependence remains explicit. -/
theorem action_form_sharp_gap (p : Domain hw0 hw1 (width := width))
    (hp : B U (input hw0 hw1 p) = RCzero) :
    RCle (RCscale
      (BF4ExactSlabFixedSpatialTransferMixingRate.mixFraction hw0 hw1 width)
      (B (input hw0 hw1 p) (input hw0 hw1 p)))
      (B (input hw0 hw1 p) (action hw0 hw1 p)) := by
  revert hp
  refine Quotient.inductionOn p ?_
  intro P' hp
  exact graph_form_sharp_gap hw0 hw1 P'.2.2 hp

#print axioms graphInputPairingModulus
#print axioms graph_input_pairings_close
#print axioms graph_defect_form_le
#print axioms graph_form_gap
#print axioms action_form_gap
#print axioms graph_form_sharp_gap
#print axioms action_form_sharp_gap

end YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphGap
