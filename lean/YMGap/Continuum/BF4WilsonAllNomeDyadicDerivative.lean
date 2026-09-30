/-
Dyadic difference quotients on the ORIGINAL positive-time range. The actual
root square law makes consecutive quotients differ by a second defect; the
same-carrier smoothing estimate gives an explicit geometric squared-distance
modulus. This constructs only the dyadic derivative of T(1)x, not a
full-carrier generator or a physical-time calibration.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay
import YMGap.Continuum.BF4WilsonAllNomeDyadicRepresentatives
import YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity
import YMGap.Continuum.BF4WilsonAllNomeCauchyRows
import YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
import YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial
import YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Constructive.SU3CharFactor (ofNat_mul_eqv)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity (completedInner_sub_left)
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root root_sub)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility (root_square)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (full_mesh_time half_power_normalizes)
open YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity (rangeModulus scaled_norm_small)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay
open YMGap.Continuum.BF4WilsonAllNomeDyadicRepresentatives (rootRepresentative rootRepresentative_pin)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr four_copies four_quarter_scale)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments (scale_add)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "PD" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

def differenceQuotient (depth : Nat) (x : V) : V :=
  completedSmul hw0 hw1 (Q'.ofNat (2^depth))
    (defect hw0 hw1 depth (completedTime hw0 hw1 1 x))

/-- Exact refinement of actual root defects, before any norm estimate. -/
theorem refinement_difference (depth : Nat) (c : Q') (x : V) :
    completedSub hw0 hw1
      (completedSmul hw0 hw1 (c*2) (defect hw0 hw1 (depth+1) x))
      (completedSmul hw0 hw1 c (defect hw0 hw1 depth x)) =
      completedSmul hw0 hw1 c (defectPower hw0 hw1 (depth+1) 2 x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro y
  change B (completedSub hw0 hw1
    (completedSmul hw0 hw1 (c*2) (defect hw0 hw1 (depth+1) x))
    (completedSmul hw0 hw1 c (defect hw0 hw1 depth x))) y =
    B (completedSmul hw0 hw1 c
      (defect hw0 hw1 (depth+1) (defect hw0 hw1 (depth+1) x))) y
  unfold defect
  rw [show root hw0 hw1 (depth+1)
      (completedSub hw0 hw1 x (root hw0 hw1 (depth+1) x)) =
      completedSub hw0 hw1 (root hw0 hw1 (depth+1) x)
        (root hw0 hw1 (depth+1) (root hw0 hw1 (depth+1) x)) from
        root_sub hw0 hw1 (depth+1) x _,root_square hw0 hw1 depth x]
  simp only [completedInner_sub_left,completedInner_smul_left]
  refine Quotient.inductionOn₃ (B x y)
    (B (root hw0 hw1 (depth+1) x) y) (B (root hw0 hw1 depth x) y) ?_
  intro A C F
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun j =>
    poly_identity_of_normal_eq
      (.add (.mul (.mul (.var 0) (.const 2)) (.add (.var 1) (.neg (.var 2))))
        (.neg (.mul (.var 0) (.add (.var 1) (.neg (.var 3))))))
      (.mul (.var 0) (.add (.add (.var 1) (.neg (.var 2)))
        (.neg (.add (.var 2) (.neg (.var 3)))))) (by decide)
      (fun | 0 => c | 1 => A.approx j | 2 => C.approx j | _ => F.approx j)))

theorem quotient_step (depth : Nat) (x : V) :
    completedSub hw0 hw1 (differenceQuotient hw0 hw1 (depth+1) x)
      (differenceQuotient hw0 hw1 depth x) =
      completedSmul hw0 hw1 (Q'.ofNat (2^depth))
        (defectPower hw0 hw1 (depth+1) 2 (completedTime hw0 hw1 1 x)) := by
  unfold differenceQuotient
  rw [Nat.pow_succ,completedSmul_congr hw0 hw1 (ofNat_mul_eqv (2^depth) 2)]
  exact refinement_difference hw0 hw1 depth (Q'.ofNat (2^depth)) (completedTime hw0 hw1 1 x)

theorem fourth_normalization (c h : Q') (hc : Q'.eqv (h*c) 1) :
    Q'.eqv ((h*h)*(c^(2+2))) (c*c) := by
  have ha : Q'.eqv ((h*h)*(c^(2+2))) (((h*c)*(h*c))*(c*c)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0))
        (.mul (.var 1) (.mul (.var 1) (.mul (.var 1) (.mul (.var 1) (.const 1))))))
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.var 1) (.var 1))) (by decide) (fun | 0 => h | _ => c)
  have hb : Q'.eqv ((h*c)*(h*c)) 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hc)
      (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) hc)
  exact Q'.eqv_trans _ _ _ ha
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hb) (Q'.one_mul_eqv _))

/-- Squared norm of one actual quotient refinement. -/
theorem quotient_step_bound (depth : Nat) (x : V) :
    RCle (dist (differenceQuotient hw0 hw1 (depth+1) x)
      (differenceQuotient hw0 hw1 depth x))
      (RCscale (half^depth*half^depth) (B x x)) := by
  have h := RCscale_mono
    (Q'.mul_nonneg _ _ (Q'.pow_nonneg half half_nonneg depth)
      (Q'.pow_nonneg half half_nonneg depth))
    (smoothing_bound hw0 hw1 (depth+1) (2^depth) 2 x)
  rw [RCscale_RCscale,
    scale_congr (fourth_normalization _ _ (half_power_normalizes depth)),
    time_defectPower,
    show 2*2^depth = 2^(depth+1) by rw [Nat.pow_succ,Nat.mul_comm 2],
    full_mesh_time] at h
  unfold completedDist
  rw [quotient_step,completedInner_smul_left,completedInner_smul_right,RCscale_RCscale]
  exact h

theorem tail_budget (a : Q') :
    Q'.eqv ((a*a+a*a)+(4*((half*a)*(half*a))+4*((half*a)*(half*a))))
      (4*(a*a)) := by
  have h : Q'.eqv ((a*a+a*a)+(4*((half*a)*(half*a))+4*((half*a)*(half*a))))
      ((2+8*half*half)*(a*a)) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))
        (.add (.mul (.const 4) (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))))
          (.mul (.const 4) (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))))))
      (.mul (.add (.const 2) (.mul (.mul (.const 8) (.var 1)) (.var 1)))
        (.mul (.var 0) (.var 0))) (by decide) (fun | 0 => a | _ => half)
  exact Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_right _ _ _
    (by decide : Q'.eqv (2+8*half*half) 4))

theorem quotient_tail_bound (start length : Nat) (x : V) :
    RCle (dist (differenceQuotient hw0 hw1 start x)
      (differenceQuotient hw0 hw1 (start+length) x))
      (RCscale (4*(half^start*half^start)) (B x x)) := by
  induction length generalizing start with
  | zero =>
      rw [Nat.add_zero,(completedDist_zero_iff hw0 hw1 _ _).mpr rfl]
      have h := RCscale_mono (Q'.mul_nonneg _ _ (by decide : (0 : Q')≤4)
        (SumOfSquares.q_mul_self_nonneg (half^start))) (completedInner_nonnegative hw0 hw1 x)
      rw [RCscale_RCzero] at h
      exact h
  | succ length ih =>
      have hs := quotient_step_bound hw0 hw1 start x
      rw [completedDist_symm] at hs
      have ht := ih (start+1)
      have h := RCle_trans (completedDist_triangle hw0 hw1
        (differenceQuotient hw0 hw1 start x)
        (differenceQuotient hw0 hw1 (start+1) x)
        (differenceQuotient hw0 hw1 ((start+1)+length) x))
        (RCadd_le_add (RCadd_le_add hs hs) (RCadd_le_add ht ht))
      rw [← scale_add,← scale_add,← scale_add] at h
      have budget : Q'.eqv ((half^start*half^start+half^start*half^start)+
          (4*(half^(start+1)*half^(start+1))+4*(half^(start+1)*half^(start+1))))
          (4*(half^start*half^start)) := tail_budget (half^start)
      rw [scale_congr budget] at h
      simpa only [Nat.add_assoc,Nat.add_comm 1 length] using h

theorem quotient_pair_bound (start m n : Nat) (hm : start≤m) (hn : start≤n) (x : V) :
    RCle (dist (differenceQuotient hw0 hw1 m x) (differenceQuotient hw0 hw1 n x))
      (RCscale (16*(half^start*half^start)) (B x x)) := by
  have hm' := quotient_tail_bound hw0 hw1 start (m-start) x
  have hn' := quotient_tail_bound hw0 hw1 start (n-start) x
  rw [Nat.add_sub_of_le hm,completedDist_symm] at hm'
  rw [Nat.add_sub_of_le hn] at hn'
  have h := RCle_trans (completedDist_triangle hw0 hw1
    (differenceQuotient hw0 hw1 m x)
    (differenceQuotient hw0 hw1 start x)
    (differenceQuotient hw0 hw1 n x))
    (RCadd_le_add (RCadd_le_add hm' hm') (RCadd_le_add hn' hn'))
  have budget : Q'.eqv (4*(4*(half^start*half^start)))
      (16*(half^start*half^start)) :=
    poly_identity_of_normal_eq
      (.mul (.const 4) (.mul (.const 4) (.var 0)))
      (.mul (.const 16) (.var 0)) (by decide)
      (fun _ => half^start*half^start)
  rw [four_copies,RCscale_RCscale,scale_congr budget] at h
  exact h

def quotientModulus (X : (PD).Cauchy) (epsilon : Q') : Nat :=
  rangeModulus hw0 hw1 X (quarter (quarter epsilon))

theorem quotient_cauchy (X : (PD).Cauchy) (epsilon : Q')
    (he : (0 : Q')<epsilon) (m n : Nat)
    (hm : quotientModulus hw0 hw1 X epsilon≤m)
    (hn : quotientModulus hw0 hw1 X epsilon≤n) :
    RCle (dist (differenceQuotient hw0 hw1 m (Class X))
      (differenceQuotient hw0 hw1 n (Class X))) (rat epsilon) := by
  let k := quotientModulus hw0 hw1 X epsilon
  have hk : (0 : Q')≤half^k := Q'.pow_nonneg half half_nonneg k
  have hk1 : half^k≤1 := HKPos.pow_le_one half_nonneg (by decide) k
  have hsq : half^k*half^k≤half^k := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hk1 hk)
    (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have h := RCle_trans (quotient_pair_bound hw0 hw1 k m n hm hn (Class X))
    (RCscale_scalar_mono (Q'.mul_le_mul_of_nonneg_left _ _ _ hsq
      (by decide : (0 : Q')≤16)) (completedInner_nonnegative hw0 hw1 (Class X)))
  have hs := RCscale_mono (by decide : (0 : Q')≤16)
    (scaled_norm_small hw0 hw1 X (quarter (quarter epsilon))
      (quarter_pos (quarter_pos he)) k (Nat.le_refl k))
  rw [RCscale_RCscale] at hs
  have budget : RCscale 16 (rat (quarter (quarter epsilon)))=rat epsilon := by
    rw [scale_congr (by decide : Q'.eqv (16 : Q') (4*4)),← RCscale_RCscale,
      four_quarter_scale,four_quarter_scale]
  rw [budget] at hs
  exact RCle_trans h hs

/-- A concrete original Cauchy representative at each finite quotient depth. -/
def quotientRepresentative (depth : Nat) (X : (PD).Cauchy) : (PD).Cauchy :=
  (scalarContinuous hw0 hw1 (Q'.ofNat (2^depth))).mapCauchy
    (differenceCauchy hw0 hw1
      ((timeNonexpansive hw0 hw1 1).mapCauchy X)
      (rootRepresentative hw0 hw1 depth ((timeNonexpansive hw0 hw1 1).mapCauchy X)))

theorem quotientRepresentative_pin (depth : Nat) (X : (PD).Cauchy) :
    Class (quotientRepresentative hw0 hw1 depth X) =
      differenceQuotient hw0 hw1 depth (Class X) := by
  change completedSmul hw0 hw1 (Q'.ofNat (2^depth))
    (completedSub hw0 hw1 (completedTime hw0 hw1 1 (Class X))
      (Class (rootRepresentative hw0 hw1 depth
        ((timeNonexpansive hw0 hw1 1).mapCauchy X)))) = _
  rw [rootRepresentative_pin]
  rfl

def quotientRows (X : (PD).Cauchy) : RepresentedCauchy hw0 hw1 (width := width) where
  row := fun depth => quotientRepresentative hw0 hw1 depth X
  modulus := quotientModulus hw0 hw1 X
  isCauchy := by
    intro epsilon he m n hm hn
    change RCle (dist (Class (quotientRepresentative hw0 hw1 m X))
      (Class (quotientRepresentative hw0 hw1 n X))) _
    rw [quotientRepresentative_pin,quotientRepresentative_pin]
    exact quotient_cauchy hw0 hw1 X epsilon he m n hm hn

theorem quotientRows_pin (X : (PD).Cauchy) (depth : Nat) :
    rowPoint hw0 hw1 (quotientRows hw0 hw1 X) depth =
      differenceQuotient hw0 hw1 depth (Class X) :=
  quotientRepresentative_pin hw0 hw1 depth X

def representedLimit (X : (PD).Cauchy) : V := limit hw0 hw1 (quotientRows hw0 hw1 X)

def derivativeRate (X : (PD).Cauchy) : Q' → Nat := limitRate hw0 hw1 (quotientRows hw0 hw1 X)

theorem derivative_bound (X : (PD).Cauchy) (epsilon : Q')
    (he : (0 : Q')<epsilon) (n : Nat) (hn : derivativeRate hw0 hw1 X epsilon≤n) :
    RCle (dist (differenceQuotient hw0 hw1 n (Class X))
      (representedLimit hw0 hw1 X)) (rat epsilon) := by
  have h := limit_bound hw0 hw1 (quotientRows hw0 hw1 X) epsilon he n hn
  rw [quotientRows_pin] at h
  exact h

theorem representedLimit_congr (X Y : (PD).Cauchy) (h : Class X = Class Y) :
    representedLimit hw0 hw1 X = representedLimit hw0 hw1 Y := by
  apply limit_independent hw0 hw1
  intro n
  rw [quotientRows_pin,quotientRows_pin,h]

def derivativeAction : V → V :=
  Quotient.lift (representedLimit hw0 hw1)
    (fun X Y h => representedLimit_congr hw0 hw1 X Y (Quotient.sound h))

theorem derivativeAction_pin (X : (PD).Cauchy) :
    derivativeAction hw0 hw1 (Class X) = representedLimit hw0 hw1 X := rfl

def derivativeCertificate (X : (PD).Cauchy) :
    Σ' Y : (PD).Cauchy, Σ' rate : Q' → Nat,
      (Class Y = derivativeAction hw0 hw1 (Class X)) ×'
      (∀ epsilon : Q', (0 : Q')<epsilon → ∀ n, rate epsilon≤n →
        RCle (dist (differenceQuotient hw0 hw1 n (Class X)) (Class Y)) (rat epsilon)) :=
  ⟨CRealSeminormCauchyRows.diagonalCauchy (distanceData hw0 hw1 (width := width))
      (quotientRows hw0 hw1 X),derivativeRate hw0 hw1 X,rfl,derivative_bound hw0 hw1 X⟩

#print axioms differenceQuotient
#print axioms refinement_difference
#print axioms quotient_step
#print axioms fourth_normalization
#print axioms quotient_step_bound
#print axioms tail_budget
#print axioms quotient_tail_bound
#print axioms quotient_pair_bound
#print axioms quotientModulus
#print axioms quotient_cauchy
#print axioms quotientRepresentative
#print axioms quotientRepresentative_pin
#print axioms quotientRows
#print axioms quotientRows_pin
#print axioms representedLimit
#print axioms derivativeRate
#print axioms derivative_bound
#print axioms representedLimit_congr
#print axioms derivativeAction
#print axioms derivativeAction_pin
#print axioms derivativeCertificate

end YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
