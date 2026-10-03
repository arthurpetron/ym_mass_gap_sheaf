/-
# The complete original multiplication cost has a nonpositive SAME limit

The source is T^t(g_n*(f-c_n)), with its actual OWN mean c_n. Both original
partitions remain in the normalization. The limit is the difference between
the completed Dirichlet drops at lags 2*t and zero, hence nonpositive.
Explicit original joint and geometric onsets control the finite source.

This is not finite all-depth nonpositivity, a relative filtered-variance
estimate, a uniform changing-family bound, or continuum/Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSignedMultiplicationWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagLimit
import YMGap.Continuum.BF4WilsonAllNomeDyadicChronologicalResponse
import YMGap.Continuum.BF4WilsonAllNomeCenteredVector
import YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail

namespace YMGap.Continuum.BF4WilsonAllNomeSignedMultiplicationLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagLimit (raw_original_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference (rawPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSignedMultiplicationWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4WilsonAllNomeDyadicChronologicalResponse
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (mixedMoment mixedMoment_split)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail (mixedMoment_time_decreasing)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (equiv_sub)
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
  (polynomialCap polynomialCap_nonnegative polynomialInterval)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {width : Nat} (loop : SourceLoop width)

private def pairExpression (L : Nat) : WindowExpression width :=
  .mul (.loop 0 loop 1) (.loop L loop 1)

private theorem pair_within (L : Nat) : Within L (pairExpression loop L) :=
  ⟨Nat.zero_le L, Nat.le_refl L⟩

local notation:max "Joint" L:arg => originalJointLimit hw0 hw1 L
  (pairExpression loop L) (pair_within loop L)
local notation:max "Moment" L:arg => centeredTimeMoment hw0 hw1 L
  (loopState loop) (loopState loop)

/-- A difference of EXISTING original joint limits, not a new limit object. -/
def signedCostLimit (t : Nat) : CReal :=
  sub (sub (Joint (2*t)) (Joint (2*t+1))) (sub (Joint 0) (Joint 1))

private theorem drop_centered_pin (L : Nat) :
    Equiv (sub (Moment L) (Moment (L+1))) (sub (Joint L) (Joint (L+1))) := by
  have h := equiv_sub (centeredTimeMoment_chronological_pin hw0 hw1 loop L)
    (centeredTimeMoment_chronological_pin hw0 hw1 loop (L+1))
  refine h.trans (SumOfSquares.Equiv_of_approx_eqv (fun p => ?_))
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 2)))
      (.neg (.add (.var 1) (.neg (.var 2)))))
    (.add (.var 0) (.neg (.var 1))) (by decide)
    (fun
      | 0 => (Joint L).approx p
      | 1 => (Joint (L+1)).approx p
      | _ => (mul (intrinsicForm hw0 hw1 (loopState loop) (unit width))
          (intrinsicForm hw0 hw1 (loopState loop) (unit width))).approx p)

private theorem add_sub_first (a b : RC) : RCsub (RCadd a b) a = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
      (.var 1) (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

private theorem first_defect_pin (x : Completion hw0 hw1 width) (L : Nat) :
    mixedMoment hw0 hw1 x L 1 = RCsub
      (completedInner hw0 hw1 x (completedTime hw0 hw1 L x))
      (completedInner hw0 hw1 x (completedTime hw0 hw1 (L+1) x)) := by
  have h := mixedMoment_split hw0 hw1 x L 0
  change completedInner hw0 hw1 x (completedTime hw0 hw1 L x) = RCadd
    (completedInner hw0 hw1 x (completedTime hw0 hw1 (L+1) x))
    (mixedMoment hw0 hw1 x L 1) at h
  have hc := congrArg (fun z => RCsub z
    (completedInner hw0 hw1 x (completedTime hw0 hw1 (L+1) x))) h
  change RCsub (completedInner hw0 hw1 x (completedTime hw0 hw1 L x))
      (completedInner hw0 hw1 x (completedTime hw0 hw1 (L+1) x)) =
    RCsub (RCadd (completedInner hw0 hw1 x (completedTime hw0 hw1 (L+1) x))
      (mixedMoment hw0 hw1 x L 1))
      (completedInner hw0 hw1 x (completedTime hw0 hw1 (L+1) x)) at hc
  rw [add_sub_first] at hc
  exact hc.symm

private theorem joint_drop_completed_pin (L : Nat) :
    Quotient.mk crealSetoid (sub (Joint L) (Joint (L+1))) =
      mixedMoment hw0 hw1 (centeredVector hw0 hw1 (loopState loop)) L 1 := by
  rw [first_defect_pin, centeredVector_time_pairing, centeredVector_time_pairing]
  exact Quotient.sound (drop_centered_pin hw0 hw1 loop L).symm

/-- Literal original centered vector, original time defect and original carrier. -/
theorem signedCostLimit_completed_pin (t : Nat) :
    Quotient.mk crealSetoid (signedCostLimit hw0 hw1 loop t) =
      RCsub (mixedMoment hw0 hw1 (centeredVector hw0 hw1 (loopState loop)) (2*t) 1)
        (mixedMoment hw0 hw1 (centeredVector hw0 hw1 (loopState loop)) 0 1) := by
  change RCsub (Quotient.mk crealSetoid (sub (Joint (2*t)) (Joint (2*t+1))))
    (Quotient.mk crealSetoid (sub (Joint 0) (Joint 1))) = _
  rw [joint_drop_completed_pin, joint_drop_completed_pin]

private theorem mixed_le_initial (x : Completion hw0 hw1 width) (L : Nat) :
    RCle (mixedMoment hw0 hw1 x L 1) (mixedMoment hw0 hw1 x 0 1) := by
  induction L with
  | zero => exact RCle_refl _
  | succ L ih => exact RCle_trans (mixedMoment_time_decreasing hw0 hw1 x L 1) ih

/-- A favorable sign for the COMPLETE component, with no favorable-sign premise. -/
theorem signedCostLimit_nonpositive (t : Nat) :
    leEv (signedCostLimit hw0 hw1 loop t) czero := by
  have h := mixed_le_initial hw0 hw1
    (centeredVector hw0 hw1 (loopState loop)) (2*t)
  have hs := RCadd_le_add h (RCle_refl (RCneg
    (mixedMoment hw0 hw1 (centeredVector hw0 hw1 (loopState loop)) 0 1)))
  have hz (a : RC) : RCsub a a = RCzero := by
    refine Quotient.inductionOn a ?_
    intro A
    exact Quotient.sound (sub_self_eqv_zero A)
  change RCle (RCsub _ _) (RCsub _ _) at hs
  rw [hz, ← signedCostLimit_completed_pin hw0 hw1 loop t] at hs
  exact hs

private theorem difference_upper (x y X Y d : Q')
    (hx : x ≤ X+d) (hy : Y ≤ y+d) : x + -y ≤ X + -Y + (d+d) :=
  Q'.le_trans' _ _ _ (Q'.add_le_add hx (Q'.neg_le_neg_add hy))
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 2)) (.add (.neg (.var 1)) (.var 2)))
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.var 2)))
      (by decide) (fun | 0 => X | 1 => Y | _ => d)))

private theorem four_difference_upper (a b c d A B C D e : Q')
    (ha : a ≤ A+e) (hb : B ≤ b+e) (hc : C ≤ c+e) (hd : d ≤ D+e) :
    (a + -b) + -(c + -d) ≤ (A + -B) + -(C + -D) + 4*e := by
  have h := difference_upper _ _ _ _ (e+e)
    (difference_upper _ _ _ _ e ha hb) (difference_upper _ _ _ _ e hc hd)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.add (.var 0) (.add (.add (.var 1) (.var 1)) (.add (.var 1) (.var 1))))
      (.add (.var 0) (.mul (.const 4) (.var 1))) (by decide)
      (fun | 0 => (A + -B) + -(C + -D) | _ => e)))

private theorem joint_representative_regular (L : Nat) (delta : Q')
    (hd : (0 : Q') < delta) (p q : Nat) (hpq : p ≤ q) (hp : delta.den ≤ p) :
    (Joint L).approx p ≤ (Joint L).approx q+delta ∧
      (Joint L).approx q ≤ (Joint L).approx p+delta := by
  exact QMhat_directed _ (originalJointCauchy hw0 hw1 L
    (pairExpression loop L) (pair_within loop L)) delta hd p q hpq hp

/-- Explicit representative order control. The eventual-order witness is used
only inside this Prop proof; the published onset is delta.den, never extracted. -/
theorem signedCostLimit_representative_bound (t : Nat) (delta : Q')
    (hd : (0 : Q') < delta) (p : Nat) (hp : delta.den ≤ p) :
    (signedCostLimit hw0 hw1 loop t).approx p ≤ 5*delta := by
  obtain ⟨N, hN⟩ := signedCostLimit_nonpositive hw0 hw1 loop t delta hd
  let q := max N p
  have hpq : p ≤ q := Nat.le_max_right _ _
  have h0 := joint_representative_regular hw0 hw1 loop (2*t) delta hd p q hpq hp
  have h1 := joint_representative_regular hw0 hw1 loop (2*t+1) delta hd p q hpq hp
  have h2 := joint_representative_regular hw0 hw1 loop 0 delta hd p q hpq hp
  have h3 := joint_representative_regular hw0 hw1 loop 1 delta hd p q hpq hp
  have h := four_difference_upper _ _ _ _ _ _ _ _ delta h0.1 h1.2 h2.2 h3.1
  have hq : (signedCostLimit hw0 hw1 loop t).approx q ≤ delta := by
    simpa only [czero, ofQ', Q'.zero_add'] using hN q (Nat.le_max_left _ _)
  change (signedCostLimit hw0 hw1 loop t).approx p ≤
    (signedCostLimit hw0 hw1 loop t).approx q+4*delta at h
  exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hq)
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.var 0) (.mul (.const 4) (.var 0))) (.mul (.const 5) (.var 0))
      (by decide) (fun _ => delta))))

private def fourMax (a b c d : Nat) : Nat := max (max a b) (max c d)

private theorem fourMax_bounds (a b c d N : Nat) (h : fourMax a b c d ≤ N) :
    a ≤ N ∧ b ≤ N ∧ c ≤ N ∧ d ≤ N := by
  dsimp only [fourMax] at h
  exact ⟨Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) h,
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) h,
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) h,
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) h⟩

private def part (epsilon : Q') : Q' := (Q'.mkPos 1 16 (by decide))*epsilon

private theorem part_positive {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < part epsilon := Q'.mul_pos (by decide) he

/-- Independent heat-stage onset for the four EXISTING chronological joints. -/
def signedCostCutoffOnset (t : Nat) (epsilon : Q') : Nat :=
  fourMax
    (jointCutoffThreshold hw0 hw1 (2*t) (pairExpression loop (2*t)) (part epsilon))
    (jointCutoffThreshold hw0 hw1 (2*t+1) (pairExpression loop (2*t+1)) (part epsilon))
    (jointCutoffThreshold hw0 hw1 0 (pairExpression loop 0) (part epsilon))
    (jointCutoffThreshold hw0 hw1 1 (pairExpression loop 1) (part epsilon))

/-- Independent exterior-depth onset; BOTH finite mean-error terms are paid. -/
def signedCostDepthOnset (t : Nat) (epsilon : Q') : Nat :=
  let C := polynomialCap (sourceCharacter width loop.edges 1)
  max (fourMax
    (jointTimeThreshold hw0 hw1 (pairExpression loop (2*t)) (part epsilon))
    (jointTimeThreshold hw0 hw1 (pairExpression loop (2*t+1)) (part epsilon))
    (jointTimeThreshold hw0 hw1 (pairExpression loop 0) (part epsilon))
    (jointTimeThreshold hw0 hw1 (pairExpression loop 1) (part epsilon)))
    (geometricCutoff (mixRate hw0 hw1 width) ((C+C)*(C+C)) (part epsilon))

/-- Representative onset is explicit, including the rational denominator
needed to transfer the completed sign to these particular representatives. -/
def signedCostRepresentativeOnset (t : Nat) (epsilon : Q') : Nat :=
  max (part epsilon).den (fourMax
    (jointModulus hw0 hw1 (2*t) (pairExpression loop (2*t)) (part epsilon))
    (jointModulus hw0 hw1 (2*t+1) (pairExpression loop (2*t+1)) (part epsilon))
    (jointModulus hw0 hw1 0 (pairExpression loop 0) (part epsilon))
    (jointModulus hw0 hw1 1 (pairExpression loop 1) (part epsilon)))

private theorem raw_joint_approx (L stage n p : Nat) (delta : Q')
    (hd : (0 : Q') < delta)
    (hk : jointCutoffThreshold hw0 hw1 L (pairExpression loop L) delta ≤ stage)
    (ht : jointTimeThreshold hw0 hw1 (pairExpression loop L) delta ≤ n)
    (hp : jointModulus hw0 hw1 L (pairExpression loop L) delta ≤ p) :
    rawPair hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) n L
      (sourceCharacter width loop.edges 1) ≤ (Joint L).approx p+delta ∧
    (Joint L).approx p ≤ rawPair hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) n L (sourceCharacter width loop.edges 1)+delta := by
  have h := originalJoint_approx hw0 hw1 L (pairExpression loop L)
    (pair_within loop L) delta hd stage n p hk ht hp
  have hpin := raw_original_pin hw0 hw1 width loop stage n L
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin) h.1,
    Q'.le_trans' _ _ _ h.2
      (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ delta hpin))⟩

private theorem six_error_chain (S R L error delta : Q')
    (hs : S ≤ R+error) (hr : R ≤ L+4*delta) (he : error ≤ delta+delta) :
    S ≤ L+6*delta := by
  have h := Q'.le_trans' _ _ _ hs (Q'.add_le_add hr he)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.mul (.const 4) (.var 1))) (.add (.var 1) (.var 1)))
      (.add (.var 0) (.mul (.const 6) (.var 1))) (by decide)
      (fun | 0 => L | _ => delta)))

private theorem six_error_reverse (L R S error delta : Q')
    (hl : L ≤ R+4*delta) (hs : R ≤ S+error) (he : error ≤ delta+delta) :
    L ≤ S+6*delta := by
  have h := Q'.le_trans' _ _ _ hl (Q'.add_le_add_right _ _ (4*delta) hs)
  have he' := Q'.add_le_add_right _ _ (4*delta) (Q'.add_le_add_left S _ _ he)
  exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ he' (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.add (.var 1) (.var 1))) (.mul (.const 4) (.var 1)))
      (.add (.var 0) (.mul (.const 6) (.var 1))) (by decide)
      (fun | 0 => S | _ => delta))))

/-- Whole original source versus its SAME limit, in BOTH orders, on the
independent late cutoff/depth rectangle. All three onsets are Type-valued. -/
theorem original_signed_joint_approx (t : Nat) (epsilon : Q')
    (he : (0 : Q') < epsilon) (stage n p : Nat)
    (hk : signedCostCutoffOnset hw0 hw1 loop t epsilon ≤ stage)
    (hn : signedCostDepthOnset hw0 hw1 loop t epsilon ≤ n)
    (hp : signedCostRepresentativeOnset hw0 hw1 loop t epsilon ≤ p) :
    let S := normalizedSignedMultiplicationCost hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) n t (sourceCharacter width loop.edges 1)
    S ≤ (signedCostLimit hw0 hw1 loop t).approx p + 6*part epsilon ∧
      (signedCostLimit hw0 hw1 loop t).approx p ≤ S + 6*part epsilon := by
  let delta := part epsilon
  have hd : (0 : Q') < delta := part_positive he
  let f := sourceCharacter width loop.edges 1
  let C := polynomialCap f
  let cap := (C+C)*(C+C)
  have hcap : (0 : Q') ≤ cap := SumOfSquares.q_mul_self_nonneg _
  have hk4 := fourMax_bounds _ _ _ _ stage hk
  have ht4 := fourMax_bounds _ _ _ _ n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hp4 := fourMax_bounds _ _ _ _ p (Nat.le_trans (Nat.le_max_right _ _) hp)
  have h0 := raw_joint_approx hw0 hw1 loop (2*t) stage n p delta hd
    hk4.1 ht4.1 hp4.1
  have h1 := raw_joint_approx hw0 hw1 loop (2*t+1) stage n p delta hd
    hk4.2.1 ht4.2.1 hp4.2.1
  have h2 := raw_joint_approx hw0 hw1 loop 0 stage (n+t) p delta hd
    hk4.2.2.1 (Nat.le_trans ht4.2.2.1 (Nat.le_add_right _ _)) hp4.2.2.1
  have h3 := raw_joint_approx hw0 hw1 loop 1 stage (n+t) p delta hd
    hk4.2.2.2 (Nat.le_trans ht4.2.2.2 (Nat.le_add_right _ _)) hp4.2.2.2
  have hr := four_difference_upper _ _ _ _ _ _ _ _ delta h0.1 h1.2 h2.2 h3.1
  have hl := four_difference_upper _ _ _ _ _ _ _ _ delta h0.2 h1.1 h2.1 h3.2
  have hg : geometricCutoff (mixRate hw0 hw1 width) cap delta ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  have he0 := geometric_bound (mixRate_nonnegative hw0 hw1 width)
    (mixRate_lt_one hw0 hw1 width) hcap hd n hg
  have he1 := geometric_bound (mixRate_nonnegative hw0 hw1 width)
    (mixRate_lt_one hw0 hw1 width) hcap hd (n+t)
    (Nat.le_trans hg (Nat.le_add_right _ _))
  have he2 := Q'.add_le_add he0 he1
  have hs := original_signed_raw_bounds hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) n t
    (polynomialInterval (List.length (baseLinks width)) f
      (sourceCharacter_supported width loop.edges 1))
  exact ⟨six_error_chain _ _ _ _ delta hs.1 hr he2,
    six_error_reverse _ _ _ _ delta hl hs.2 he2⟩

private theorem part_budget (epsilon : Q') (he : (0 : Q') < epsilon) :
    11*part epsilon ≤ epsilon := by
  have h := Q'.mul_le_mul_of_nonneg_right _ _ epsilon
    (by decide : (11 : Q')*(Q'.mkPos 1 16 (by decide)) ≤ 1) (Q'.le_of_lt he)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm
    (Q'.mul_assoc_eqv 11 (Q'.mkPos 1 16 (by decide)) epsilon)))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv epsilon)))

/-- No sign premise: every sufficiently late original source is at most the
requested positive tolerance. Nome, width, loop and smoothing lag stay fixed. -/
theorem original_signed_eventual_upper (t : Nat) (epsilon : Q')
    (he : (0 : Q') < epsilon) (stage n : Nat)
    (hk : signedCostCutoffOnset hw0 hw1 loop t epsilon ≤ stage)
    (hn : signedCostDepthOnset hw0 hw1 loop t epsilon ≤ n) :
    normalizedSignedMultiplicationCost hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) n t (sourceCharacter width loop.edges 1) ≤ epsilon := by
  let p := signedCostRepresentativeOnset hw0 hw1 loop t epsilon
  have h := (original_signed_joint_approx hw0 hw1 loop t epsilon he stage n p
    hk hn (Nat.le_refl _)).1
  have hp : (part epsilon).den ≤ p := Nat.le_max_left _ _
  have hs := signedCostLimit_representative_bound hw0 hw1 loop t
    (part epsilon) (part_positive he) p hp
  have hb := Q'.le_trans' _ _ _ h (Q'.add_le_add_right _ _ (6*part epsilon) hs)
  exact Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.mul (.const 5) (.var 0)) (.mul (.const 6) (.var 0)))
      (.mul (.const 11) (.var 0)) (by decide) (fun _ => part epsilon)))
    (part_budget epsilon he))

/-- Diagonal convergence into the EXISTING joint-limit expression. The
independent source and representative onsets remain computable definitions. -/
theorem original_signed_diagonal_converges (t : Nat) :
    ConvergesTo (fun s => ofQ' (normalizedSignedMultiplicationCost hw0 hw1
      (headCutoff w+s) width (Nat.le_add_right _ _) s t
        (sourceCharacter width loop.edges 1))) (signedCostLimit hw0 hw1 loop t) := by
  intro epsilon he
  let N := max (signedCostCutoffOnset hw0 hw1 loop t epsilon)
    (signedCostDepthOnset hw0 hw1 loop t epsilon)
  refine ⟨N, fun s hs => ⟨signedCostRepresentativeOnset hw0 hw1 loop t epsilon,
    fun p hp => ?_⟩⟩
  have h := original_signed_joint_approx hw0 hw1 loop t epsilon he s s p
    (Nat.le_trans (Nat.le_max_left _ _) hs)
    (Nat.le_trans (Nat.le_max_right _ _) hs) hp
  have h6 : 6*part epsilon ≤ epsilon := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ (part epsilon)
      (by decide : (6 : Q') ≤ 11) (Q'.le_of_lt (part_positive he)))
    (part_budget epsilon he)
  exact ⟨Q'.le_trans' _ _ _ h.1 (Q'.add_le_add_left _ _ _ h6),
    Q'.le_trans' _ _ _ h.2 (Q'.add_le_add_left _ _ _ h6)⟩

end YMGap.Continuum.BF4WilsonAllNomeSignedMultiplicationLimit

#print axioms YMGap.Continuum.BF4WilsonAllNomeSignedMultiplicationLimit.signedCostLimit
#print axioms YMGap.Continuum.BF4WilsonAllNomeSignedMultiplicationLimit.signedCostLimit_completed_pin
#print axioms YMGap.Continuum.BF4WilsonAllNomeSignedMultiplicationLimit.signedCostLimit_nonpositive
#print axioms YMGap.Continuum.BF4WilsonAllNomeSignedMultiplicationLimit.signedCostLimit_representative_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeSignedMultiplicationLimit.signedCostCutoffOnset
#print axioms YMGap.Continuum.BF4WilsonAllNomeSignedMultiplicationLimit.signedCostDepthOnset
#print axioms YMGap.Continuum.BF4WilsonAllNomeSignedMultiplicationLimit.signedCostRepresentativeOnset
#print axioms YMGap.Continuum.BF4WilsonAllNomeSignedMultiplicationLimit.original_signed_joint_approx
#print axioms YMGap.Continuum.BF4WilsonAllNomeSignedMultiplicationLimit.original_signed_eventual_upper
#print axioms YMGap.Continuum.BF4WilsonAllNomeSignedMultiplicationLimit.original_signed_diagonal_converges
