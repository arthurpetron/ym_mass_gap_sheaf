/-
# Positive orbit smoothing preserves the original response-ratio order

Every response on the SAME original Wilson completion has increasing cleared
block ratios. Positive rational time-orbit combinations therefore improve
these ratios, including at zero moments. The proof regularizes only scalar
responses, uses actual second-defect positivity, and removes the regularizer
by constructive order closure. No spectral measure, norm inverse, auxiliary
carrier, or source-overlap premise is introduced.

Raw retention is sufficient for positive smoothing, not necessary. None of
these unconditional inequalities supplies useful changing-family retention,
the original innovation ceiling, or a continuum/physical gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen
import YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
import YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail

namespace YMGap.Continuum.BF4WilsonAllNomePositiveOrbitResponseOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (completedInner_sub_left completedInner_sub_right)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen
  (response_nonnegative response_log_convex_step)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
  (leEv_cancel_mul_right_posEv)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance (familyExcitation)
open YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState (timeKernel smoothedResponse)

local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem mul_zero (a : RC) : RCmul RCzero a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (A.approx n)))

private theorem mul_assoc (a b c : RC) :
    RCmul (RCmul a b) c = RCmul a (RCmul b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_assoc_eqv (A.approx n) (B.approx n) (C.approx n)))

private theorem mul_swap_last (a b c : RC) :
    RCmul (RCmul a b) c = RCmul (RCmul a c) b := by
  rw [mul_assoc, RCmul_comm b c, ← mul_assoc]

private theorem mul_mono_left {a b c : RC} (ha : RCnonneg a) (h : RCle b c) :
    RCle (RCmul a b) (RCmul a c) := by
  revert ha h
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B C ha h => leEv_mul_nonneg_left ha h

private theorem mul_mono_right {a b c : RC} (hc : RCnonneg c) (h : RCle a b) :
    RCle (RCmul a c) (RCmul b c) := by
  rw [RCmul_comm a c, RCmul_comm b c]
  exact mul_mono_left hc h

private theorem rat_nonnegative (q : Q') (hq : (0 : Q') ≤ q) : RCnonneg (rat q) :=
  leEv_ofQ'_of_approx_ge (fun _ => hq)

private theorem cancel_floor {a b c : RC} (epsilon : Q')
    (he : (0 : Q') < epsilon) (hc : RCle (rat epsilon) c)
    (h : RCle (RCmul a c) (RCmul b c)) : RCle a b := by
  revert hc h
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B C hc h => leEv_cancel_mul_right_posEv ⟨epsilon, he, hc⟩ h

private theorem sub_add_cancel (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.sub_add_cancel_eqv (A.approx n) (B.approx n)))

private theorem le_of_sub_nonnegative {a b : RC} (h : RCnonneg (RCsub a b)) :
    RCle b a := by
  have hh := RCadd_le_add h (RCle_refl b)
  rwa [zero_add, sub_add_cancel] at hh

private theorem difference_of_split (a b c : RC) (h : a = RCadd b c) :
    RCsub a b = c := by
  rw [h]
  refine Quotient.inductionOn₂ b c ?_
  exact fun B C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun | 0 => B.approx n | _ => C.approx n)))

private theorem second_difference_regroup (a b c : RC) :
    RCsub (RCadd a c) (RCadd b b) = RCsub (RCsub a b) (RCsub b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 2)) (.neg (.add (.var 1) (.var 1))))
      (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.add (.var 1) (.neg (.var 2)))))
      (by decide) (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

private theorem regularized_product (a b : RC) (epsilon : Q') :
    RCmul (RCadd a (rat epsilon)) (RCadd b (rat epsilon)) =
      RCadd (RCadd (RCmul a b) (RCscale epsilon (RCadd a b)))
        (rat (epsilon*epsilon)) := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => poly_identity_of_normal_eq
      (.mul (.add (.var 0) (.var 2)) (.add (.var 1) (.var 2)))
      (.add (.add (.mul (.var 0) (.var 1))
        (.mul (.var 2) (.add (.var 0) (.var 1)))) (.mul (.var 2) (.var 2)))
      (by decide) (fun | 0 => A.approx n | 1 => B.approx n | _ => epsilon)))

/-! Two finite inductions; all cancelled factors have the produced epsilon floor. -/

private theorem positive_chain_adjacent (E : Nat → RC) (epsilon : Q')
    (he : (0 : Q') < epsilon) (hf : ∀ n, RCle (rat epsilon) (E n))
    (hn : ∀ n, RCnonneg (E n))
    (hs : ∀ n, RCle (RCmul (E (n+1)) (E (n+1))) (RCmul (E n) (E (n+2))))
    (L : Nat) : ∀ j : Nat,
    RCle (RCmul (E (L+j)) (E (L+1))) (RCmul (E (L+j+1)) (E L))
  | 0 => by
      rw [Nat.add_zero, RCmul_comm (E L) (E (L+1))]
      exact RCle_refl _
  | j+1 => by
      have h1 := mul_mono_right (hn (L+j+1))
        (positive_chain_adjacent E epsilon he hf hn hs L j)
      have h2 := mul_mono_right (hn L) (hs (L+j))
      have hleft : RCmul (RCmul (E (L+j)) (E (L+1))) (E (L+j+1)) =
          RCmul (RCmul (E (L+j+1)) (E (L+1))) (E (L+j)) := by
        rw [RCmul_comm (E (L+j)) (E (L+1)), mul_swap_last,
          RCmul_comm (E (L+1)) (E (L+j+1))]
      have hmiddle : RCmul (RCmul (E (L+j+1)) (E L)) (E (L+j+1)) =
          RCmul (RCmul (E (L+j+1)) (E (L+j+1))) (E L) := mul_swap_last _ _ _
      have hright : RCmul (RCmul (E (L+j)) (E (L+j+2))) (E L) =
          RCmul (RCmul (E (L+j+2)) (E L)) (E (L+j)) := by
        rw [RCmul_comm (E (L+j)) (E (L+j+2)), mul_swap_last]
      rw [hleft, hmiddle] at h1
      rw [hright] at h2
      have hc := cancel_floor epsilon he (hf (L+j)) (RCle_trans h1 h2)
      simpa only [show L+(j+1)=L+j+1 by omega,
        show L+(j+1)+1=L+j+2 by omega] using hc

private theorem positive_chain_crossRatio (E : Nat → RC) (epsilon : Q')
    (he : (0 : Q') < epsilon) (hf : ∀ n, RCle (rat epsilon) (E n))
    (hn : ∀ n, RCnonneg (E n))
    (hs : ∀ n, RCle (RCmul (E (n+1)) (E (n+1))) (RCmul (E n) (E (n+2))))
    (L j : Nat) : ∀ h : Nat,
    RCle (RCmul (E (L+j)) (E (L+h))) (RCmul (E (L+j+h)) (E L))
  | 0 => by simp only [Nat.add_zero]; exact RCle_refl _
  | h+1 => by
      have h1 := mul_mono_right (hn (L+h+1))
        (positive_chain_crossRatio E epsilon he hf hn hs L j h)
      have h2 := mul_mono_right (hn L)
        (positive_chain_adjacent E epsilon he hf hn hs (L+h) j)
      have hleft : RCmul (RCmul (E (L+j)) (E (L+h))) (E (L+h+1)) =
          RCmul (RCmul (E (L+j)) (E (L+h+1))) (E (L+h)) := mul_swap_last _ _ _
      have hmiddle : RCmul (RCmul (E (L+j+h)) (E L)) (E (L+h+1)) =
          RCmul (RCmul (E (L+j+h)) (E (L+h+1))) (E L) := mul_swap_last _ _ _
      have hright : RCmul (RCmul (E (L+j+h+1)) (E L)) (E (L+h)) =
          RCmul (RCmul (E (L+j+h+1)) (E (L+h))) (E L) := mul_swap_last _ _ _
      rw [hleft, hmiddle] at h1
      simp only [show L+h+j=L+j+h by omega] at h2
      rw [← hright] at h2
      have hc := cancel_floor epsilon he (hf (L+h)) (RCle_trans h1 h2)
      simpa only [show L+(h+1)=L+h+1 by omega,
        show L+j+(h+1)=L+j+h+1 by omega] using hc

/-! The explicit null sequence removes scalar regularization at four endpoints. -/

private theorem invSucc_converges_zero :
    ConvergesTo (fun n => ofQ' (Q'.invSucc n)) czero := by
  intro epsilon he
  refine ⟨epsilon.den, fun n hn => ⟨0, fun _ _ => ?_⟩⟩
  change Q'.invSucc n ≤ 0+epsilon ∧ (0 : Q') ≤ Q'.invSucc n+epsilon
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn)
        (HalfPow.invSucc_den_le epsilon he))
      (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' epsilon)))
  · exact Q'.zero_le_add _ _ (Q'.le_of_lt (Q'.invSucc_pos n)) (Q'.le_of_lt he)

private theorem regularized_converges (A : CReal) :
    ConvergesTo (fun n => add A (ofQ' (Q'.invSucc n))) A :=
  convergesTo_limit_congr
    (TrigAddCReal.convergesTo_add (convergesTo_const A) invSucc_converges_zero)
    (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem remove_regularization (a b c d : RC)
    (h : ∀ epsilon : Q', (0 : Q') < epsilon →
      RCle (RCmul (RCadd a (rat epsilon)) (RCadd b (rat epsilon)))
        (RCmul (RCadd c (rat epsilon)) (RCadd d (rat epsilon)))) :
    RCle (RCmul a b) (RCmul c d) := by
  revert h
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  refine Quotient.inductionOn₂ c d ?_
  intro C D h
  exact leEv_of_convergesTo_le
    (YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (regularized_converges A) (regularized_converges B))
    (YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (regularized_converges C) (regularized_converges D))
    (fun n => h (Q'.invSucc n) (Q'.invSucc_pos n))

section Completed

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation:max "R" x:arg n:arg => B x (T n x)
attribute [local irreducible] completedInner completedTime

private theorem first_defect_pin (x : V) (n : Nat) :
    RCsub (R x n) (R x (n+1)) = mixedMoment hw0 hw1 x n 1 := by
  exact difference_of_split _ _ _ (mixedMoment_split hw0 hw1 x n 0)

private theorem response_convex_step (x : V) (n : Nat) :
    RCle (RCadd (R x (n+1)) (R x (n+1))) (RCadd (R x n) (R x (n+2))) := by
  apply le_of_sub_nonnegative
  rw [second_difference_regroup, first_defect_pin hw0 hw1 x n,
    show n+2=(n+1)+1 by omega, first_defect_pin hw0 hw1 x (n+1)]
  rw [difference_of_split _ _ _ (mixedMoment_split hw0 hw1 x n 1)]
  exact mixedMoment_nonnegative hw0 hw1 x n 2

private theorem regularized_response_crossRatio (x : V) (epsilon : Q')
    (he : (0 : Q') < epsilon) (L j h : Nat) :
    RCle (RCmul (RCadd (R x (L+j)) (rat epsilon))
      (RCadd (R x (L+h)) (rat epsilon)))
      (RCmul (RCadd (R x (L+j+h)) (rat epsilon)) (RCadd (R x L) (rat epsilon))) := by
  let E : Nat → RC := fun n => RCadd (R x n) (rat epsilon)
  have hf : ∀ n, RCle (rat epsilon) (E n) := by
    intro n
    have hh := RCadd_le_add (response_nonnegative hw0 hw1 width x n)
      (RCle_refl (rat epsilon))
    simpa only [zero_add] using hh
  have hn : ∀ n, RCnonneg (E n) := fun n =>
    RCle_trans (rat_nonnegative epsilon (Q'.le_of_lt he)) (hf n)
  have hs : ∀ n, RCle (RCmul (E (n+1)) (E (n+1))) (RCmul (E n) (E (n+2))) := by
    intro n
    dsimp only [E]
    rw [regularized_product, regularized_product]
    exact RCadd_le_add
      (RCadd_le_add (response_log_convex_step hw0 hw1 width x n)
        (RCscale_mono (Q'.le_of_lt he) (response_convex_step hw0 hw1 x n)))
      (RCle_refl _)
  exact positive_chain_crossRatio E epsilon he hf hn hs L j h

/-- Every cleared block ratio increases along the actual original response.
All three lags are arbitrary and zero responses need no excluded case. -/
theorem response_crossRatio (x : V) (L j h : Nat) :
    RCle (RCmul (R x (L+j)) (R x (L+h)))
      (RCmul (R x (L+j+h)) (R x L)) :=
  remove_regularization _ _ _ _
    (fun epsilon he => regularized_response_crossRatio hw0 hw1 x epsilon he L j h)

private theorem mul_add (a b c : RC) :
    RCmul (RCadd a b) c = RCadd (RCmul a c) (RCmul b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A0 B0 C0 => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_mul_eqv (A0.approx n) (B0.approx n) (C0.approx n)))

private theorem mul_scale (q : Q') (a b : RC) :
    RCmul (RCscale q a) b = RCscale q (RCmul a b) := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A0 B0 => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_assoc_eqv q (A0.approx n) (B0.approx n)))

/-! Quantitative temporal covariance, on the SAME source and arbitrary shift. -/

private theorem add_comm (a b : RC) : RCadd a b = RCadd b a := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun X Y => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_comm_eqv (X.approx n) (Y.approx n)))

private theorem sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 0))) (.const 0)
      (by decide) (fun _ => X.approx n)))

private theorem subnonneg_of_le {a b : RC} (h : RCle a b) :
    RCnonneg (RCsub b a) := by
  have hh := RCadd_le_add h (RCle_refl (RCneg a))
  change RCle (RCsub a a) (RCsub b a) at hh
  rwa [sub_self] at hh

private theorem scale_zero (a : RC) : RCscale 0 a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (X.approx n)))

private theorem scale_nat_succ (n : Nat) (a : RC) :
    RCscale (Q'.ofNat (n+1)) a = RCadd (RCscale (Q'.ofNat n) a) a := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun j =>
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv n 1))
      (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
            (by decide : Q'.eqv (Q'.ofNat 1) 1)) (Q'.one_mul_eqv (X.approx j)))))))

private theorem mul_add_left (a b c : RC) :
    RCmul a (RCadd b c) = RCadd (RCmul a b) (RCmul a c) := by
  rw [RCmul_comm a (RCadd b c), mul_add, RCmul_comm b a, RCmul_comm c a]

private def residualQuadratic (c a u v z : RC) : RC :=
  RCsub (RCmul c (RCsub (RCmul c z) (RCmul a v)))
    (RCmul a (RCsub (RCmul c v) (RCmul a u)))

private theorem residualQuadratic_initial (c a z : RC) :
    residualQuadratic c a c a z =
      RCmul c (RCsub (RCmul c z) (RCmul a a)) := by
  refine Quotient.inductionOn₃ c a z ?_
  exact fun X Y Z => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.mul (.var 0) (.var 2))
        (.neg (.mul (.var 1) (.var 1)))))
        (.neg (.mul (.var 1) (.add (.mul (.var 0) (.var 1))
          (.neg (.mul (.var 1) (.var 0)))))))
      (.mul (.var 0) (.add (.mul (.var 0) (.var 2))
        (.neg (.mul (.var 1) (.var 1)))))
      (by decide) (fun | 0 => X.approx n | 1 => Y.approx n | _ => Z.approx n)))

private theorem residualQuadratic_recurrence (c a u v z : RC) :
    RCadd (RCmul a (RCsub (RCmul c v) (RCmul a u)))
      (residualQuadratic c a u v z) = RCmul c (RCsub (RCmul c z) (RCmul a v)) := by
  unfold residualQuadratic
  rw [add_comm, sub_add_cancel]

private theorem residual_response_pin (x : V) (c a : CReal)
    (cc : QCauchy c.approx) (ca : QCauchy a.approx) (n : Nat) :
    let y := completedSub hw0 hw1
      (completedRealSmul hw0 hw1 c cc (T 1 x)) (completedRealSmul hw0 hw1 a ca x)
    R y n = residualQuadratic (Quotient.mk crealSetoid c) (Quotient.mk crealSetoid a)
      (R x n) (R x (n+1)) (R x (n+2)) := by
  dsimp only
  have h2 : B (T 1 x) (T n (T 1 x)) = R x (n+2) := by
    rw [← completedTime_add, completedInner_time_sum, show 1+(n+1)=n+2 by omega]
  have h10 : B (T 1 x) (T n x) = R x (n+1) := by
    rw [completedInner_time_sum, show 1+n=n+1 by omega]
  have h01 : B x (T n (T 1 x)) = R x (n+1) := by rw [← completedTime_add]
  simp only [completedTime_sub, completedTime_realSmul, completedInner_sub_left,
    completedInner_sub_right, completedInner_realSmul_left, completedInner_realSmul_right,
    h2, h10, h01, residualQuadratic]

private theorem response_increment_with_scalars (x : V) (L : Nat) (c a : CReal)
    (cc : QCauchy c.approx) (ca : QCauchy a.approx)
    (hc : Quotient.mk crealSetoid c = R x L)
    (ha : Quotient.mk crealSetoid a = R x (L+1)) (epsilon : Q')
    (he : (0 : Q') < epsilon) (hfloor : RCle (rat epsilon) (R x L)) :
    ∀ h : Nat, RCle
      (RCsub (RCmul (R x L) (R x (L+h+1))) (RCmul (R x (L+1)) (R x (L+h))))
      (RCscale (Q'.ofNat h)
        (RCsub (RCmul (R x L) (R x (L+2))) (RCmul (R x (L+1)) (R x (L+1))))) := by
  let C := R x L
  let A := R x (L+1)
  let S := RCsub (RCmul C (R x (L+2))) (RCmul A A)
  let delta := fun h => RCsub (RCmul C (R x (L+h+1))) (RCmul A (R x (L+h)))
  let y := completedSub hw0 hw1
    (completedRealSmul hw0 hw1 c cc (T 1 x)) (completedRealSmul hw0 hw1 a ca x)
  have hY (n : Nat) : R y n = residualQuadratic C A (R x n) (R x (n+1)) (R x (n+2)) := by
    simpa only [hc, ha, C, A] using residual_response_pin hw0 hw1 x c a cc ca n
  have hS : RCnonneg S := subnonneg_of_le (response_log_convex_step hw0 hw1 width x L)
  have hA := response_nonnegative hw0 hw1 width x (L+1)
  have hAC : RCle A C := BF4WilsonAllNomeOddResponseJensen.response_le_of_le
    hw0 hw1 width x (by omega : L ≤ L+1)
  change ∀ h, RCle (delta h) (RCscale (Q'.ofNat h) S)
  intro h
  induction h with
  | zero =>
      dsimp only [delta]
      simp only [Nat.add_zero]
      rw [RCmul_comm C A, sub_self,
        RCSignedPairBudget.scale_congr (by decide : Q'.eqv (Q'.ofNat 0) 0), scale_zero]
      exact RCle_refl _
  | succ h ih =>
      have hy := BF4WilsonAllNomeOddResponseJensen.response_le_of_le hw0 hw1 width y
        (by omega : L ≤ L+h)
      rw [hY (L+h), hY L, residualQuadratic_initial] at hy
      have hhs : RCnonneg (RCscale (Q'.ofNat h) S) := by
        simpa only [RCscale_RCzero] using RCscale_mono (Q'.ofNat_nonneg h) hS
      have hfirst := RCle_trans (mul_mono_left hA ih) (mul_mono_right hhs hAC)
      have hh := RCadd_le_add hfirst hy
      rw [residualQuadratic_recurrence, ← mul_add_left, ← scale_nat_succ] at hh
      apply cancel_floor epsilon he hfloor
      rw [RCmul_comm (delta (h+1)) C, RCmul_comm (RCscale (Q'.ofNat (h+1)) S) C]
      simpa only [delta, C, A, S, Nat.add_assoc] using hh

/-- Actual temporal covariance grows at most linearly in the SAME initial
Hankel spread. The supplied positive rational floor is used only to cancel
R_x(L); arbitrary shifts (including odd L) and zero spread are retained.
No relative spread, overlap, window survival or physical gap is supplied. -/
theorem response_crossRatio_increment_le (x : V) (L h : Nat) (epsilon : Q')
    (he : (0 : Q') < epsilon) (hfloor : RCle (rat epsilon) (R x L)) :
    RCle (RCsub (RCmul (R x L) (R x (L+h+1)))
      (RCmul (R x (L+1)) (R x (L+h))))
      (RCscale (Q'.ofNat h) (RCsub (RCmul (R x L) (R x (L+2)))
        (RCmul (R x (L+1)) (R x (L+1))))) := by
  revert hfloor
  refine Quotient.inductionOn x ?_
  intro X hfloor
  let P := pairingData hw0 hw1 (width := width)
  let c := CRealSeminormPairingCompletion.representativeInner P X
    ((timeNonexpansive hw0 hw1 L).mapCauchy X)
  let a := CRealSeminormPairingCompletion.representativeInner P X
    ((timeNonexpansive hw0 hw1 (L+1)).mapCauchy X)
  let cc := CRealSeminormPairingCompletion.representativeInnerCauchy P X
    ((timeNonexpansive hw0 hw1 L).mapCauchy X)
  let ca := CRealSeminormPairingCompletion.representativeInnerCauchy P X
    ((timeNonexpansive hw0 hw1 (L+1)).mapCauchy X)
  exact response_increment_with_scalars hw0 hw1 _ L c a cc ca
    (by unfold completedInner completedTime; rfl)
    (by unfold completedInner completedTime; rfl) epsilon he hfloor h

private theorem late_defect_gap (c a u v : RC) :
    RCsub (RCmul (RCsub c a) u)
      (RCsub (RCmul c v) (RCmul a u)) = RCmul c (RCsub u v) := by
  refine Quotient.inductionOn₂ c a ?_
  intro C A
  refine Quotient.inductionOn₂ u v ?_
  exact fun U0 V0 => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
        (.neg (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2))))))
      (.mul (.var 0) (.add (.var 2) (.neg (.var 3))))
      (by decide) (fun
        | 0 => C.approx n
        | 1 => A.approx n
        | 2 => U0.approx n
        | _ => V0.approx n)))

/-- The SAME shifted covariance saturates at initial first-defect times late
response. No positive response floor is needed, including at zero responses
or odd shifts. This is an alternative payment bound, not a survival estimate. -/
theorem response_crossRatio_increment_le_late_defect (x : V) (L h : Nat) :
    RCle (RCsub (RCmul (R x L) (R x (L+h+1)))
      (RCmul (R x (L+1)) (R x (L+h))))
      (RCmul (RCsub (R x L) (R x (L+1))) (R x (L+h))) := by
  apply le_of_sub_nonnegative
  rw [late_defect_gap, first_defect_pin hw0 hw1 x (L+h)]
  have hh := mul_mono_left (response_nonnegative hw0 hw1 width x L)
    (mixedMoment_nonnegative hw0 hw1 x (L+h) 1)
  rw [RCmul_comm _ RCzero, mul_zero] at hh
  exact hh

private theorem spread_defect_difference (c a z : RC) :
    RCsub (RCmul c (RCsub (RCsub c a) (RCsub a z)))
      (RCsub (RCmul c z) (RCmul a a)) = RCmul (RCsub c a) (RCsub c a) := by
  refine Quotient.inductionOn₃ c a z ?_
  exact fun X Y Z => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.add (.var 1) (.neg (.var 2))))))
        (.neg (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1))))))
      (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
      (by decide) (fun | 0 => X.approx n | 1 => Y.approx n | _ => Z.approx n)))

private theorem spread_le_second_defect (x : V) (L : Nat) :
    RCle (RCsub (RCmul (R x L) (R x (L+2))) (RCmul (R x (L+1)) (R x (L+1))))
      (RCmul (R x L) (mixedMoment hw0 hw1 x L 2)) := by
  have hd : RCsub (RCsub (R x L) (R x (L+1)))
      (RCsub (R x (L+1)) (R x (L+2))) = mixedMoment hw0 hw1 x L 2 := by
    rw [first_defect_pin hw0 hw1 x L, show L+2=(L+1)+1 by omega,
      first_defect_pin hw0 hw1 x (L+1)]
    exact difference_of_split _ _ _ (mixedMoment_split hw0 hw1 x L 1)
  apply le_of_sub_nonnegative
  rw [← hd, spread_defect_difference, first_defect_pin hw0 hw1 x L]
  have hn := mixedMoment_nonnegative hw0 hw1 x L 1
  have hh := mul_mono_left hn hn
  rw [RCmul_comm _ RCzero, mul_zero] at hh
  exact hh

/-- Warming pays the SAME source's cleared covariance in its original
preimage norm, at inverse-square rate. This does not pay a relative overlap
or survival floor; the rational floor on the warmed response remains explicit. -/
theorem warmed_response_crossRatio_increment_le (x : V) (q h : Nat) (epsilon : Q')
    (he : (0 : Q') < epsilon) (hfloor : RCle (rat epsilon) (R x (2*q))) :
    RCle (RCsub (RCmul (R x (2*q)) (R x (2*q+h+1)))
      (RCmul (R x (2*q+1)) (R x (2*q+h))))
      (RCscale (Q'.ofNat h * (Q'.invSucc q * Q'.invSucc q))
        (RCmul (R x (2*q)) (B x x))) := by
  have hc := response_nonnegative hw0 hw1 width x (2*q)
  have hs := RCle_trans (spread_le_second_defect hw0 hw1 x (2*q))
    (mul_mono_left hc
      (BF4WilsonAllNomeTimeDefectTail.mixedMoment_two_defect_bound hw0 hw1 x q))
  have hp : RCmul (R x (2*q))
      (RCscale (Q'.invSucc q * Q'.invSucc q) (B x x)) =
      RCscale (Q'.invSucc q * Q'.invSucc q) (RCmul (R x (2*q)) (B x x)) := by
    rw [RCmul_comm, mul_scale, RCmul_comm (B x x) (R x (2*q))]
  rw [hp] at hs
  have hh := RCle_trans (response_crossRatio_increment_le hw0 hw1 x (2*q) h epsilon he hfloor)
    (RCscale_mono (Q'.ofNat_nonneg h) hs)
  rwa [RCscale_RCscale] at hh

private theorem sum_mul_right (cs : List (Q' × Nat)) (f : Nat → RC) (a : RC) :
    RCmul (responseSum cs f) a = responseSum cs (fun n => RCmul (f n) a) := by
  induction cs with
  | nil => exact mul_zero a
  | cons c cs ih =>
      simp only [responseSum, mul_add, mul_scale, ih]

private theorem sum_mono (cs : List (Q' × Nat)) (f g : Nat → RC)
    (hc : ∀ c ∈ cs, (0 : Q') ≤ c.1) (hfg : ∀ n, RCle (f n) (g n)) :
    RCle (responseSum cs f) (responseSum cs g) := by
  revert hc
  induction cs with
  | nil => intro hc; exact RCle_refl _
  | cons c cs ih =>
      intro hc
      exact RCadd_le_add (RCscale_mono (hc c (List.mem_cons_self)) (hfg c.2))
        (ih (fun c hm => hc c (List.mem_cons_of_mem _ hm)))

private theorem orbit_response_expand (x : V) (cs : List (Q' × Nat)) (n : Nat) :
    R (orbitSum hw0 hw1 x cs) n = responseSum cs (fun j =>
      responseSum cs (fun k => R x (j+k+n))) := by
  rw [orbitSum_time, orbitSum_pairing]
  apply congrArg (responseSum cs)
  funext j
  apply congrArg (responseSum cs)
  funext k
  rw [← completedTime_add]

/-- Positive rational orbit weights improve the response ratio on the SAME
carrier. Repeated orbit entries and every double-orbit cross term remain. -/
theorem positiveOrbit_response_crossRatio (x : V) (cs : List (Q' × Nat))
    (hc : ∀ c ∈ cs, (0 : Q') ≤ c.1) (L h : Nat) :
    RCle (RCmul (R (orbitSum hw0 hw1 x cs) L) (R x (L+h)))
      (RCmul (R (orbitSum hw0 hw1 x cs) (L+h)) (R x L)) := by
  rw [orbit_response_expand hw0 hw1 x cs L,
    orbit_response_expand hw0 hw1 x cs (L+h), sum_mul_right, sum_mul_right]
  apply sum_mono cs _ _ hc
  intro j
  rw [sum_mul_right, sum_mul_right]
  apply sum_mono cs _ _ hc
  intro k
  have hh := response_crossRatio hw0 hw1 x L (j+k) h
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

private theorem scale_regularized (q epsilon : Q') (a : RC) :
    RCscale q (RCadd a (rat epsilon)) =
      RCadd (RCscale q a) (rat (q*epsilon)) := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_add_eqv q (A.approx n) epsilon))

private theorem scale_move (q : Q') (a b : RC) :
    RCmul a (RCscale q b) = RCmul (RCscale q a) b := by
  rw [RCmul_comm a (RCscale q b), mul_scale, RCmul_comm b a, ← mul_scale]

private theorem remove_scaled_regularization (q : Q') (a b : RC)
    (h : ∀ epsilon : Q', (0 : Q') < epsilon →
      RCle (RCscale q (RCadd a (rat epsilon))) (RCadd b (rat epsilon))) :
    RCle (RCscale q a) b := by
  revert h
  refine Quotient.inductionOn₂ a b ?_
  intro A0 B0 h
  exact leEv_of_convergesTo_le
    (convergesTo_const_mul (ofQ' q) (regularized_converges A0))
    (regularized_converges B0) (fun n => h (Q'.invSucc n) (Q'.invSucc_pos n))

/-- A retained block fraction at L also holds at every later lag, without
cancelling a possibly zero original response. -/
theorem shifted_response_floor (x : V) (kappa : Q')
    (hk : kappa ≤ (1 : Q')) (L h j : Nat)
    (hf : RCle (RCscale kappa (R x L)) (R x (L+h))) :
    RCle (RCscale kappa (R x (L+j))) (R x (L+j+h)) := by
  apply remove_scaled_regularization
  intro epsilon he
  have hfloor (n : Nat) : RCle (rat epsilon) (RCadd (R x n) (rat epsilon)) := by
    have hh := RCadd_le_add (response_nonnegative hw0 hw1 width x n)
      (RCle_refl (rat epsilon))
    simpa only [zero_add] using hh
  have hnonneg (n : Nat) : RCnonneg (RCadd (R x n) (rat epsilon)) :=
    RCle_trans (rat_nonnegative epsilon (Q'.le_of_lt he)) (hfloor n)
  have hke : kappa*epsilon ≤ epsilon :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ epsilon hk (Q'.le_of_lt he))
      (Q'.le_of_eqv (Q'.one_mul_eqv epsilon))
  have hregular : RCle (RCscale kappa (RCadd (R x L) (rat epsilon)))
      (RCadd (R x (L+h)) (rat epsilon)) := by
    rw [scale_regularized]
    exact RCadd_le_add hf (leEv_ofQ'_of_approx_ge (fun _ => hke))
  have h1 := mul_mono_left (hnonneg (L+j)) hregular
  rw [scale_move] at h1
  exact cancel_floor epsilon he (hfloor L)
    (RCle_trans h1 (regularized_response_crossRatio hw0 hw1 x epsilon he L j h))

private theorem sum_scale (cs : List (Q' × Nat)) (f : Nat → RC) (q : Q') :
    RCscale q (responseSum cs f) = responseSum cs (fun n => RCscale q (f n)) := by
  induction cs with
  | nil => exact RCscale_RCzero q
  | cons c cs ih =>
      change RCscale q (RCadd (RCscale c.1 (f c.2)) (responseSum cs f)) = _
      have hadd (a b : RC) : RCscale q (RCadd a b) =
          RCadd (RCscale q a) (RCscale q b) := by
        refine Quotient.inductionOn₂ a b ?_
        exact fun A0 B0 => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
          (fun n => Q'.mul_add_eqv q (A0.approx n) (B0.approx n)))
      rw [hadd, ih, RCscale_RCscale]
      change RCadd (RCscale (q*c.1) (f c.2)) _ =
        RCadd (RCscale c.1 (RCscale q (f c.2))) _
      rw [RCscale_RCscale, RCSignedPairBudget.scale_congr (Q'.mul_comm_eqv q c.1)]

/-- A raw retained fraction transfers to every positive smoothing without a
norm floor. This is sufficient, not necessary; the raw floor is not produced.
Neither a zero response nor an empty orbit is excluded. -/
theorem positiveOrbit_response_retention (x : V) (cs : List (Q' × Nat))
    (hc : ∀ c ∈ cs, (0 : Q') ≤ c.1) (kappa : Q')
    (_hk0 : (0 : Q') ≤ kappa) (hk1 : kappa ≤ (1 : Q')) (L h : Nat)
    (hf : RCle (RCscale kappa (R x L)) (R x (L+h))) :
    RCle (RCscale kappa (R (orbitSum hw0 hw1 x cs) L))
      (R (orbitSum hw0 hw1 x cs) (L+h)) := by
  rw [orbit_response_expand hw0 hw1 x cs L,
    orbit_response_expand hw0 hw1 x cs (L+h), sum_scale]
  apply sum_mono cs _ _ hc
  intro j
  rw [sum_scale]
  apply sum_mono cs _ _ hc
  intro k
  have hh := shifted_response_floor hw0 hw1 x kappa hk1 L h (j+k) hf
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

/-! Signed double-orbit credit: the early negative term is not discarded. -/

private theorem scaled_sub_add_sub (q : Q') (a b c d : RC) :
    RCadd (RCscale q (RCsub a b)) (RCsub c d) =
      RCsub (RCadd (RCscale q a) c) (RCadd (RCscale q b) d) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A0 B0 C0
  refine Quotient.inductionOn d ?_
  exact fun D0 => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.add (.var 3) (.neg (.var 4))))
      (.add (.add (.mul (.var 0) (.var 1)) (.var 3))
        (.neg (.add (.mul (.var 0) (.var 2)) (.var 4))))
      (by decide) (fun
        | 0 => q
        | 1 => A0.approx n
        | 2 => B0.approx n
        | 3 => C0.approx n
        | _ => D0.approx n)))

private theorem sum_sub (cs : List (Q' × Nat)) (f g : Nat → RC) :
    responseSum cs (fun n => RCsub (f n) (g n)) =
      RCsub (responseSum cs f) (responseSum cs g) := by
  induction cs with
  | nil => exact (sub_self RCzero).symm
  | cons c cs ih =>
      simp only [responseSum, ih]
      exact scaled_sub_add_sub c.1 _ _ _ _

private theorem sum_mul_left (cs : List (Q' × Nat)) (f : Nat → RC) (a : RC) :
    RCmul a (responseSum cs f) = responseSum cs (fun n => RCmul a (f n)) := by
  rw [RCmul_comm a (responseSum cs f), sum_mul_right]
  exact congrArg (responseSum cs) (funext (fun n => RCmul_comm (f n) a))

private theorem credit_reassemble (theta : Q') (a b c d : RC) :
    RCmul a (RCsub c (RCscale theta d)) =
      RCadd (RCmul (RCsub b (RCscale theta a)) d)
        (RCsub (RCmul a c) (RCmul b d)) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A0 B0 C0
  refine Quotient.inductionOn d ?_
  exact fun D0 => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.var 2) (.neg (.mul (.var 4) (.var 3)))))
      (.add (.mul (.add (.var 1) (.neg (.mul (.var 4) (.var 0)))) (.var 3))
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 3)))))
      (by decide) (fun
        | 0 => A0.approx n
        | 1 => B0.approx n
        | 2 => C0.approx n
        | 3 => D0.approx n
        | _ => theta)))

/-- Exact SAME-source double-orbit credit, for arbitrary signed filter weights
and arbitrary rational theta. No response floor or positivity is assumed. -/
theorem signedOrbit_response_credit_identity (x : V) (cs : List (Q' × Nat))
    (theta : Q') (L h : Nat) :
    let y := orbitSum hw0 hw1 x cs
    let a := R x (L+1)
    let b := R x (L+h+1)
    RCmul a (RCsub (R y (L+h)) (RCscale theta (R y L))) =
      RCadd (RCmul (RCsub b (RCscale theta a)) (R y L))
        (responseSum cs (fun j => responseSum cs (fun k =>
          RCsub (RCmul a (R x (L+(j+k)+h))) (RCmul b (R x (L+(j+k))))))) := by
  dsimp only
  rw [credit_reassemble]
  congr 1
  rw [orbit_response_expand hw0 hw1 x cs (L+h),
    orbit_response_expand hw0 hw1 x cs L]
  simp only [sum_sub, ← sum_mul_left, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Every late raw credit is nonnegative; signed orbit coefficients are NOT
asserted to preserve this sign after summation. -/
theorem response_credit_nonnegative (x : V) (L h s : Nat) (hs : 1 ≤ s) :
    RCnonneg (RCsub (RCmul (R x (L+1)) (R x (L+s+h)))
      (RCmul (R x (L+h+1)) (R x (L+s)))) := by
  apply subnonneg_of_le
  have hh := response_crossRatio hw0 hw1 x (L+1) (s-1) h
  simpa only [show L+1+(s-1)=L+s by omega,
    show L+1+h=L+h+1 by omega, RCmul_comm] using hh

private theorem sub_reverse (a b : RC) : RCsub a b = RCneg (RCsub b a) := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A0 B0 => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 1)))
      (.neg (.add (.var 1) (.neg (.var 0))))
      (by decide) (fun | 0 => A0.approx n | _ => B0.approx n)))

/-- The shift-zero credit is exactly the negative early covariance. -/
theorem response_credit_zero (x : V) (L h : Nat) :
    RCsub (RCmul (R x (L+1)) (R x (L+0+h)))
      (RCmul (R x (L+h+1)) (R x (L+0))) =
      RCneg (RCsub (RCmul (R x L) (R x (L+h+1)))
        (RCmul (R x (L+1)) (R x (L+h)))) := by
  simpa only [Nat.add_zero, RCmul_comm] using sub_reverse
    (RCmul (R x (L+1)) (R x (L+h))) (RCmul (R x (L+h+1)) (R x L))

/-- Literal existing box response and timeKernel, with the SAME unsmoothed
centered family source. No second smoothing or finite-source identification. -/
theorem smoothedResponse_credit_identity (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) (M : Nat) (theta : Q') (L h : Nat) :
    let x := (familyExcitation hw0 hw1 width qs c hqs).val
    let a := R x (L+1)
    let b := R x (L+h+1)
    RCmul a (RCsub (smoothedResponse hw0 hw1 width qs c hqs M (L+h))
      (RCscale theta (smoothedResponse hw0 hw1 width qs c hqs M L))) =
      RCadd (RCmul (RCsub b (RCscale theta a))
        (smoothedResponse hw0 hw1 width qs c hqs M L))
        (responseSum (timeKernel M) (fun j => responseSum (timeKernel M) (fun k =>
          RCsub (RCmul a (R x (L+(j+k)+h))) (RCmul b (R x (L+(j+k))))))) :=
  signedOrbit_response_credit_identity hw0 hw1
    (familyExcitation hw0 hw1 width qs c hqs).val (timeKernel M) theta L h

end Completed

#print axioms positive_chain_crossRatio
#print axioms invSucc_converges_zero
#print axioms remove_regularization
#print axioms response_convex_step
#print axioms response_crossRatio
#print axioms response_crossRatio_increment_le
#print axioms response_crossRatio_increment_le_late_defect
#print axioms warmed_response_crossRatio_increment_le
#print axioms orbit_response_expand
#print axioms positiveOrbit_response_crossRatio
#print axioms shifted_response_floor
#print axioms positiveOrbit_response_retention
#print axioms scaled_sub_add_sub
#print axioms sum_sub
#print axioms sum_mul_left
#print axioms credit_reassemble
#print axioms signedOrbit_response_credit_identity
#print axioms response_credit_nonnegative
#print axioms sub_reverse
#print axioms response_credit_zero
#print axioms smoothedResponse_credit_identity

end YMGap.Continuum.BF4WilsonAllNomePositiveOrbitResponseOrder
