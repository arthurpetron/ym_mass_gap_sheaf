/-
# Coupling comparison after ORIGINAL Wilson time and cutoff removal

Truncate both time tails at the same chosen finite depth. Compare the
existing normalized finite-chain expectations there, then add the two
proved geometric boundary errors. All three terms use the original action
and the SAME Wilson expression. Only the two nomes change.

This applies throughout 0<u<=v<=W<1, with no small-nome/entropy guard.
The infinite time-volume face count is replaced by a finite pivot count.
Width, nome, expression and pivot dependence remain explicit. The computed
comparison depth makes each boundary error small; it is not a uniform
modulus in changing couplings or widths. No spatial limit, physical
normalization, survival floor, OS identification or continuum gap follows.
-/
import YMGap.Continuum.BF4ExactSlabWilsonFiniteWindowCoupling
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
import YMGap.Constructive.CRealAbsContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeTimeCoupling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabWilsonFiniteWindowCoupling
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary
  (windowTimeCap windowTimeCap_nonnegative polynomialWindow_commonTail)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

attribute [local irreducible] originalWindowScalar originalJointLimit finiteWindowExpectation

/-- No heat cutoff or outer time-boundary length appears in this budget. -/
def boundaryBudget {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (e : WindowExpression width) (s : Nat) : Q' :=
  mixRate hw0 hw1 width ^ s *
    windowTimeCap hw0 hw1 width (polynomialCap (sourcePolynomial e))

private theorem original_tail_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (he : Within L e)
    (stage s t n : Nat) (ht : s+1 ≤ t) (hn : s+1 ≤ n) :
    Q'.abs (originalWindowScalar hw0 hw1 L e stage t t +
      -originalWindowScalar hw0 hw1 L e stage n n) ≤ boundaryBudget hw0 hw1 e s := by
  have hb := polynomialWindow_commonTail hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) L s t t n n (sourcePolynomial e) (source_supported L e he)
    ht ht hn hn
  have hp := originalWindowScalar_pin hw0 hw1 L e he stage t t
  have hq := originalWindowScalar_pin hw0 hw1 L e he stage n n
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr
      (Q'.add_eqv_congr' hp (Q'.neg_eqv_congr _ _ hq))))
    (CReal.abs_sub_le_of_bounds hb.1 hb.2)

/-- The fixed finite-chain cutoff limit approximates the pre-existing
infinite-time/cutoff Wilson limit with the actual geometric time budget.
Both convergences are proved constructions, not new input fields. -/
theorem finiteWindow_tail_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (he : Within L e)
    (s t : Nat) (ht : s+1 ≤ t) :
    leEv (CReal.abs (CReal.sub (finiteWindowExpectation hw0 hw1 L e t)
      (originalJointLimit hw0 hw1 L e he))) (ofQ' (boundaryBudget hw0 hw1 e s)) := by
  have h := convergesTo_abs (convergesTo_add
    (finiteWindow_converges hw0 hw1 L e t)
    (TrigAddCReal.convergesTo_neg (originalJoint_diagonal_converges hw0 hw1 L e he)))
  have hc : ConvergesTo
      (fun k => ofQ' (Q'.abs (originalWindowScalar hw0 hw1 L e k t t +
        -originalWindowScalar hw0 hw1 L e k k k)))
      (CReal.abs (CReal.sub (finiteWindowExpectation hw0 hw1 L e t)
        (originalJointLimit hw0 hw1 L e he))) := by
    refine TrigAddCReal.convergesTo_congr_seq ?_ h
    intro k
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  apply leEv_of_ofQ'_limit_le hc (convergesTo_const _)
  intro epsilon heps
  exact ⟨s+1, fun k hk => Q'.le_trans' _ _ _
    (original_tail_bound hw0 hw1 L e he k s t k ht hk)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt heps))⟩

private theorem abs_chain {a b c : CReal} {x y : Q'}
    (hab : leEv (CReal.abs (CReal.sub a b)) (ofQ' x))
    (hbc : leEv (CReal.abs (CReal.sub b c)) (ofQ' y)) :
    leEv (CReal.abs (CReal.sub a c)) (ofQ' (x+y)) := by
  have hsum := leRat_add hab hbc
  intro epsilon he
  obtain ⟨N, hN⟩ := hsum epsilon he
  refine ⟨N, fun n hn => ?_⟩
  have ht : Q'.eqv (a.approx n + -c.approx n)
      ((a.approx n + -b.approx n)+(b.approx n + -c.approx n)) :=
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 2)))
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
      (by decide) (fun | 0 => a.approx n | 1 => b.approx n | _ => c.approx n)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr ht))
    (Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) (hN n hn))

private theorem abs_reverse {a b : CReal} {x : Q'}
    (h : leEv (CReal.abs (CReal.sub a b)) (ofQ' x)) :
    leEv (CReal.abs (CReal.sub b a)) (ofQ' x) := by
  have heq : Equiv (CReal.abs (CReal.sub b a)) (CReal.abs (CReal.sub a b)) :=
    SumOfSquares.Equiv_of_approx_eqv
      (fun n => ExpNeg.abs_sub_comm (b.approx n) (a.approx n))
  exact leEv_trans (leEv_of_equiv heq) h

variable {u v W : Q'} (hu0 : (0 : Q') < u) (huv : u ≤ v)
  (hvW : v ≤ W) (hW1 : W < (1 : Q'))

local notation "hv0" => Q'.pos_of_lt_of_le hu0 huv
local notation "hv1" => Q'.lt_of_le_of_lt hvW hW1
local notation "hu1" => Q'.lt_of_le_of_lt huv hv1

/-- An explicit tradeoff between geometric time errors and finite path cost. -/
def couplingBudget {width : Nat} (L : Nat) (e : WindowExpression width) (s : Nat) : Q' :=
  (boundaryBudget hv0 hv1 e s + finiteWindowCap W u v L e (s+1)) +
    boundaryBudget hu0 hu1 e s

/-- SAME original Wilson expression and normalization at each nome; no
spatial or coupling guard beyond 0<u<=v<=W<1. The pivot is arbitrary. -/
theorem joint_coupling_bound {width : Nat} (L : Nat) (e : WindowExpression width)
    (he : Within L e) (s : Nat) :
    leEv (CReal.abs (CReal.sub (originalJointLimit hv0 hv1 L e he)
      (originalJointLimit hu0 hu1 L e he)))
      (ofQ' (couplingBudget hu0 huv hvW hW1 L e s)) :=
  abs_chain
    (abs_chain (abs_reverse (finiteWindow_tail_bound hv0 hv1 L e he s (s+1) (Nat.le_refl _)))
      (finiteWindow_difference_bound hu0 huv hvW hW1 L e he (s+1)))
    (finiteWindow_tail_bound hu0 hu1 L e he s (s+1) (Nat.le_refl _))

/-- Computed depth making each of the two tail errors at most epsilon.
This depends on BOTH actual nomes and the fixed spatial width. -/
def comparisonDepth {width : Nat} (e : WindowExpression width) (epsilon : Q') : Nat :=
  max (geometricCutoff (mixRate hv0 hv1 width)
      (windowTimeCap hv0 hv1 width (polynomialCap (sourcePolynomial e))) epsilon)
    (geometricCutoff (mixRate hu0 hu1 width)
      (windowTimeCap hu0 hu1 width (polynomialCap (sourcePolynomial e))) epsilon)

theorem comparisonDepth_budget {width : Nat} (e : WindowExpression width)
    (epsilon : Q') (heps : (0 : Q') < epsilon) :
    boundaryBudget hv0 hv1 e (comparisonDepth hu0 huv hvW hW1 e epsilon) ≤ epsilon ∧
      boundaryBudget hu0 hu1 e (comparisonDepth hu0 huv hvW hW1 e epsilon) ≤ epsilon := by
  constructor
  · exact geometric_bound (mixRate_nonnegative hv0 hv1 width) (mixRate_lt_one hv0 hv1 width)
      (windowTimeCap_nonnegative hv0 hv1 width (polynomialCap_nonnegative (sourcePolynomial e)))
      heps _ (Nat.le_max_left _ _)
  · exact geometric_bound (mixRate_nonnegative hu0 hu1 width) (mixRate_lt_one hu0 hu1 width)
      (windowTimeCap_nonnegative hu0 hu1 width (polynomialCap_nonnegative (sourcePolynomial e)))
      heps _ (Nat.le_max_right _ _)

/-- Infinite-time comparison with two arbitrarily small explicit tail
errors. Only a FINITE original chain's face count remains in the middle. -/
theorem joint_coupling_tolerance_bound {width : Nat} (L : Nat) (e : WindowExpression width)
    (he : Within L e) (epsilon : Q') (heps : (0 : Q') < epsilon) :
    leEv (CReal.abs (CReal.sub (originalJointLimit hv0 hv1 L e he)
      (originalJointLimit hu0 hu1 L e he)))
      (ofQ' ((epsilon + finiteWindowCap W u v L e
        (comparisonDepth hu0 huv hvW hW1 e epsilon + 1)) + epsilon)) := by
  have hb := comparisonDepth_budget hu0 huv hvW hW1 e epsilon heps
  exact leEv_trans (joint_coupling_bound hu0 huv hvW hW1 L e he _)
    (leEv_ofQ'_of_approx_ge (fun _ =>
      Q'.add_le_add (Q'.add_le_add_right _ _ _ hb.1) hb.2))

end YMGap.Continuum.BF4WilsonAllNomeTimeCoupling

#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeCoupling.boundaryBudget
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeCoupling.finiteWindow_tail_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeCoupling.couplingBudget
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeCoupling.joint_coupling_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeCoupling.comparisonDepth
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeCoupling.comparisonDepth_budget
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeCoupling.joint_coupling_tolerance_bound
