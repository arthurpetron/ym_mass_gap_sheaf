/-
# Quantitative complex pairing continuity on the SAME reflected carrier

Four sharp REAL Cauchy--Schwarz estimates give a complex continuity bound
with an explicit factor TWO. This is sufficient to transport pairings through
the represented complex limits; it is not sharp complex Cauchy--Schwarz and
does not change the existing strict transfer rate.

All estimates concern the original all-nome fixed-width JointCompletion.
Spatial/scaling limits, continuous time and full QFT remain open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCauchySchwarz
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPairingContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCauchySchwarz
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingBounds
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexification
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness

def valueSub (z u : ComplexValue) : ComplexValue := (RCsub z.1 u.1, RCsub z.2 u.2)

def valueNormSq (z : ComplexValue) : RC :=
  RCadd (RCmul z.1 z.1) (RCmul z.2 z.2)

private theorem rc_sum_square (a b : RC) :
    RCle (RCmul (RCadd a b) (RCadd a b))
      (RCadd (RCadd (RCmul a a) (RCmul b b)) (RCadd (RCmul a a) (RCmul b b))) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B epsilon he
  refine ⟨0, fun n _ => ?_⟩
  exact Q'.le_trans' _ _ _
    (BF4PhysicalFiniteVacuumSectorPathEnergy.square_add_le_double_square_sum
      (A.approx n) (B.approx n))
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he))

private theorem rc_neg_square (a : RC) : RCmul (RCneg a) (RCneg a) = RCmul a a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.neg (.var 0)) (.neg (.var 0))) (.mul (.var 0) (.var 0))
      (by decide) (fun _ => A.approx n)))

private theorem rc_difference_square (a b : RC) :
    RCle (RCmul (RCsub a b) (RCsub a b))
      (RCadd (RCadd (RCmul a a) (RCmul b b)) (RCadd (RCmul a a) (RCmul b b))) := by
  have h := rc_sum_square a (RCneg b)
  rw [rc_neg_square] at h
  exact h

private theorem rc_four_products (a b c d : RC) :
    RCadd
      (RCadd (RCadd (RCmul a c) (RCmul b d)) (RCadd (RCmul a c) (RCmul b d)))
      (RCadd (RCadd (RCmul a d) (RCmul b c)) (RCadd (RCmul a d) (RCmul b c))) =
    RCadd (RCmul (RCadd a b) (RCadd c d)) (RCmul (RCadd a b) (RCadd c d)) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  refine Quotient.inductionOn₂ c d ?_
  intro C D
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => by
    change (((A.approx n*C.approx n + B.approx n*D.approx n) +
      (A.approx n*C.approx n + B.approx n*D.approx n)) +
      ((A.approx n*D.approx n + B.approx n*C.approx n) +
      (A.approx n*D.approx n + B.approx n*C.approx n))).eqv
      (((A.approx n+B.approx n)*(C.approx n+D.approx n)) +
        ((A.approx n+B.approx n)*(C.approx n+D.approx n)))
    ring_qeqv))

private theorem rc_subtraction (a b c d : RC) :
    (RCadd (RCsub a c) (RCsub b d), RCsub (RCsub a c) (RCsub b d)) =
      (RCsub (RCadd a b) (RCadd c d), RCsub (RCsub a b) (RCsub c d)) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  refine Quotient.inductionOn₂ c d ?_
  intro C D
  apply Prod.ext
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => by
      change ((A.approx n + -C.approx n) + (B.approx n + -D.approx n)).eqv
        ((A.approx n+B.approx n) + -(C.approx n+D.approx n))
      ring_qeqv))
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => by
      change ((A.approx n + -C.approx n) + -(B.approx n + -D.approx n)).eqv
        ((A.approx n + -B.approx n) + -(C.approx n + -D.approx n))
      ring_qeqv))

private theorem rc_mul_mono_right {a b c : RC} (hc : RCnonneg c) (h : RCle a b) :
    RCle (RCmul a c) (RCmul b c) := by
  rw [RCmul_comm a c, RCmul_comm b c]
  revert hc h
  refine Quotient.inductionOn₃ c a b ?_
  exact fun C A B hc h => leEv_mul_nonneg_left hc h

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "VC" => ComplexCarrier hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "I" => inner hw0 hw1 width

/-- A factor-two bound for continuity, NOT sharp complex Cauchy--Schwarz. -/
theorem inner_two_bound (x y : VC) :
    RCle (valueNormSq (I x y))
      (RCadd (RCmul (I x x).1 (I y y).1) (RCmul (I x x).1 (I y y).1)) := by
  have hr := RCadd_le_add (completedInner_cauchySchwarz hw0 hw1 width x.1 y.1)
    (completedInner_cauchySchwarz hw0 hw1 width x.2 y.2)
  have hi := RCadd_le_add (completedInner_cauchySchwarz hw0 hw1 width x.1 y.2)
    (completedInner_cauchySchwarz hw0 hw1 width x.2 y.1)
  have h := RCadd_le_add
    (RCle_trans (rc_sum_square (B x.1 y.1) (B x.2 y.2)) (RCadd_le_add hr hr))
    (RCle_trans (rc_difference_square (B x.1 y.2) (B x.2 y.1)) (RCadd_le_add hi hi))
  rw [rc_four_products] at h
  exact h

theorem inner_sub_left (x y z : VC) :
    I (complexSub hw0 hw1 width x y) z = valueSub (I x z) (I y z) := by
  apply Prod.ext
  · simp only [inner, complexSub, valueSub, completedInner_sub_left]
    exact congrArg Prod.fst (rc_subtraction (B x.1 z.1) (B x.2 z.2)
      (B y.1 z.1) (B y.2 z.2))
  · simp only [inner, complexSub, valueSub, completedInner_sub_left]
    exact congrArg Prod.snd (rc_subtraction (B x.1 z.2) (B x.2 z.1)
      (B y.1 z.2) (B y.2 z.1))

/-- Pairing errors are bounded in the ACTUAL norm, with every complex cross
term retained until the explicit factor-two estimate is applied. -/
theorem pairing_error_bound (x y test : VC) :
    RCle (valueNormSq (valueSub (I x test) (I y test)))
      (RCadd (RCmul (complexDistSq hw0 hw1 width x y) (I test test).1)
        (RCmul (complexDistSq hw0 hw1 width x y) (I test test).1)) := by
  rw [← inner_sub_left]
  exact inner_two_bound hw0 hw1 width (complexSub hw0 hw1 width x y) test

/-- Explicit norm-to-pairing convergence estimate. The rational input epsilon
is a squared-norm tolerance; the displayed factor TWO is not suppressed. -/
theorem limit_pairing_error (X : PresentedComplexCauchy hw0 hw1 width) (test : VC)
    (epsilon : Q') (he : (0 : Q') < epsilon) (p : Nat)
    (hp : X.limitRate hw0 hw1 width epsilon ≤ p) :
    RCle (valueNormSq (valueSub (I (X.point hw0 hw1 width p) test)
      (I (X.limit hw0 hw1 width) test)))
      (RCadd (RCmul (Quotient.mk crealSetoid (ofQ' epsilon)) (I test test).1)
        (RCmul (Quotient.mk crealSetoid (ofQ' epsilon)) (I test test).1)) := by
  have h := rc_mul_mono_right (inner_nonnegative hw0 hw1 width test)
    (X.limit_converges hw0 hw1 width epsilon he p hp)
  exact RCle_trans (pairing_error_bound hw0 hw1 width _ _ test) (RCadd_le_add h h)

/-- A rational norm ceiling computed from the supplied test representatives.
The added one makes division safe even for the zero test. -/
def testNormCap (Y : (D).Cauchy × (D).Cauchy) : Q' :=
  1 + (normCeiling hw0 hw1 width Y.1 + normCeiling hw0 hw1 width Y.2)

theorem testNormCap_positive (Y : (D).Cauchy × (D).Cauchy) :
    (0 : Q') < testNormCap hw0 hw1 width Y :=
  Q'.pos_add_nonneg (by decide) (Q'.zero_le_add _ _
    (normCeiling_nonnegative hw0 hw1 width Y.1)
    (normCeiling_nonnegative hw0 hw1 width Y.2))

def representedTest (Y : (D).Cauchy × (D).Cauchy) : VC :=
  (Quotient.mk (D).completionSetoid Y.1, Quotient.mk (D).completionSetoid Y.2)

theorem representedTest_norm_le (Y : (D).Cauchy × (D).Cauchy) :
    RCle (I (representedTest hw0 hw1 width Y) (representedTest hw0 hw1 width Y)).1
      (Quotient.mk crealSetoid (ofQ' (testNormCap hw0 hw1 width Y))) := by
  have h := leEv_add (representativeInner_le_normCeiling hw0 hw1 width Y.1)
    (representativeInner_le_normCeiling hw0 hw1 width Y.2)
  rw [ofQ'_add] at h
  apply leEv_trans h
  apply leEv_ofQ'_of_approx_ge
  intro n
  change normCeiling hw0 hw1 width Y.1 + normCeiling hw0 hw1 width Y.2 ≤
    1 + (normCeiling hw0 hw1 width Y.1 + normCeiling hw0 hw1 width Y.2)
  have hq := Q'.add_le_add_right (0 : Q') 1
    (normCeiling hw0 hw1 width Y.1 + normCeiling hw0 hw1 width Y.2) (by decide)
  rwa [Q'.zero_add'] at hq

/-- Squared-norm tolerance that pays for both real/imaginary pairing errors. -/
def pairingTolerance (Y : (D).Cauchy × (D).Cauchy) (epsilon : Q') : Q' :=
  Q'.divPos (HalfPow.half * epsilon) (testNormCap hw0 hw1 width Y)
    (testNormCap_positive hw0 hw1 width Y)

def pairingRate (X : PresentedComplexCauchy hw0 hw1 width)
    (Y : (D).Cauchy × (D).Cauchy) (epsilon : Q') : Nat :=
  X.limitRate hw0 hw1 width (pairingTolerance hw0 hw1 width Y epsilon)

/-- Genuine epsilon-to-index modulus for the squared complex pairing error.
The test norm is bounded from its supplied representatives, never chosen. -/
theorem pairing_converges (X : PresentedComplexCauchy hw0 hw1 width)
    (Y : (D).Cauchy × (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (p : Nat) (hp : pairingRate hw0 hw1 width X Y epsilon ≤ p) :
    RCle (valueNormSq (valueSub
      (I (X.point hw0 hw1 width p) (representedTest hw0 hw1 width Y))
      (I (X.limit hw0 hw1 width) (representedTest hw0 hw1 width Y))))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  let delta := pairingTolerance hw0 hw1 width Y epsilon
  have hd : (0 : Q') < delta :=
    Q'.divPos_pos _ _ _ (ExpNeg.half_mul_pos epsilon he)
  have hd0 : RCnonneg (Quotient.mk crealSetoid (ofQ' delta)) :=
    leEv_ofQ'_of_approx_ge (fun _ => Q'.le_of_lt hd)
  have hmono := rc_mul_mono_right hd0 (representedTest_norm_le hw0 hw1 width Y)
  rw [RCmul_comm _ (Quotient.mk crealSetoid (ofQ' delta)),
    RCmul_comm (Quotient.mk crealSetoid (ofQ' (testNormCap hw0 hw1 width Y)))] at hmono
  have hcancel : RCmul (Quotient.mk crealSetoid (ofQ' delta))
      (Quotient.mk crealSetoid (ofQ' (testNormCap hw0 hw1 width Y))) =
      Quotient.mk crealSetoid (ofQ' (HalfPow.half * epsilon)) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.divPos_mul_eqv _ _ _))
  rw [hcancel] at hmono
  have hsum := RCadd_le_add hmono hmono
  have hhalf : RCadd (Quotient.mk crealSetoid (ofQ' (HalfPow.half * epsilon)))
      (Quotient.mk crealSetoid (ofQ' (HalfPow.half * epsilon))) =
      Quotient.mk crealSetoid (ofQ' epsilon) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => ExpNeg.two_halves epsilon))
  rw [hhalf] at hsum
  exact RCle_trans (limit_pairing_error hw0 hw1 width X
    (representedTest hw0 hw1 width Y) delta hd p hp) hsum

/-- The concrete consumer: complex matrix coefficients at actual discrete
time pass through the constructed norm limit, with an explicit modulus.
Time is fixed here; no continuous-time or spacing-uniform claim is made. -/
theorem time_pairing_converges (X : PresentedComplexCauchy hw0 hw1 width)
    (Y : (D).Cauchy × (D).Cauchy) (time : Nat)
    (epsilon : Q') (he : (0 : Q') < epsilon) (p : Nat)
    (hp : pairingRate hw0 hw1 width (X.mapTime hw0 hw1 width time) Y epsilon ≤ p) :
    RCle (valueNormSq (valueSub
      (I (complexTime hw0 hw1 width time (X.point hw0 hw1 width p))
        (representedTest hw0 hw1 width Y))
      (I (complexTime hw0 hw1 width time (X.limit hw0 hw1 width))
        (representedTest hw0 hw1 width Y))))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have h := pairing_converges hw0 hw1 width (X.mapTime hw0 hw1 width time)
    Y epsilon he p hp
  rw [PresentedComplexCauchy.mapTime_point, PresentedComplexCauchy.mapTime_limit] at h
  exact h

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPairingContinuity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPairingContinuity.valueNormSq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPairingContinuity.inner_two_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPairingContinuity.inner_sub_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPairingContinuity.pairing_error_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPairingContinuity.limit_pairing_error
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPairingContinuity.testNormCap_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPairingContinuity.representedTest_norm_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPairingContinuity.pairingRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPairingContinuity.pairing_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPairingContinuity.time_pairing_converges
