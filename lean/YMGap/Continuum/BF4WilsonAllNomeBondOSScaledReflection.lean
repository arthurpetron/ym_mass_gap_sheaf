/-
# Scaled original physical resolvent reflection and strict Neumann step

For each positive rational t, the constructed R_t=(I+t*A)^(-1) on the
ORIGINAL physical bond carrier has a symmetric contractive reflection
S_t=2*R_t-I. Graph positivity includes the ACTUAL scaled derivative term.
Consequently N_t=(I-S_t^2)/2 has squared-norm/distance factor 1/4,
independent of t, nome, width and state. Its exact pin is 2*R_t*(I-R_t).

This supplies the parameterized iteration input for the denominator and
scaled imaginary shifts, not their completed inverse or a time group.
No physical-time calibration, continuum gap or signed scaling bound follows.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSScaledResolvent
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSScaledReflection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion bondCompletedInner bondCompletedDistance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_inner bondValue_distance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_sub bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeBondOSDerivative (input output nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeBondOSScaledResolvent
  (resolvent resolventDomain input_resolventDomain graph_sum
    resolvent_sub resolvent_smul resolvent_symmetric)
open YMGap.Continuum.RCSignedPairBudget (neg_mono scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}
  (t : Q') (ht : (0 : Q') < t)

local notation "H" => BondCompletion hw0 hw1 (width := width)
local notation "B" => bondCompletedInner hw0 hw1
local notation "BV" => completedInner hw0 hw1
local notation "value" => bondValue hw0 hw1
local notation "Add" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "Sub" => BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
local notation "Scale" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "R" => resolvent hw0 hw1 t ht
local notation "Out" => (fun p => Scale t (output hw0 hw1 p))
local notation "Dom" => resolventDomain hw0 hw1 t ht

private theorem inner_add_left (x y z : H) :
    B (Add x y) z = RCadd (B x z) (B y z) := by
  rw [bondValue_inner, bondValue_add, completedInner_add_left,
    bondValue_inner, bondValue_inner]

private theorem inner_add_right (x y z : H) :
    B x (Add y z) = RCadd (B x y) (B x z) := by
  rw [bondValue_inner, bondValue_add, completedInner_add_right,
    bondValue_inner, bondValue_inner]

private theorem inner_sub_left (x y z : H) :
    B (Sub x y) z = RCsub (B x z) (B y z) := by
  rw [bondValue_inner, bondValue_sub, completedInner_sub_left,
    bondValue_inner, bondValue_inner]

private theorem inner_sub_right (x y z : H) :
    B x (Sub y z) = RCsub (B x y) (B x z) := by
  rw [bondValue_inner, bondValue_sub, completedInner_sub_right,
    bondValue_inner, bondValue_inner]

private theorem inner_smul_left (a : Q') (x y : H) :
    B (Scale a x) y = RCscale a (B x y) := by
  rw [bondValue_inner, bondValue_smul, completedInner_smul_left, bondValue_inner]

private theorem inner_smul_right (a : Q') (x y : H) :
    B x (Scale a y) = RCscale a (B x y) := by
  rw [bondValue_inner, bondValue_smul, completedInner_smul_right, bondValue_inner]

private theorem inner_symm (x y : H) : B x y = B y x := by
  rw [bondValue_inner, bondValue_inner, completedInner_symm]

private theorem inner_nonnegative (x : H) : RCnonneg (B x x) := by
  rw [bondValue_inner]
  exact completedInner_nonnegative hw0 hw1 _

/-- Reflected actual positive resolvent. This is NOT a physical time step. -/
def reflection (x : H) : H := Sub (Scale 2 (R x)) x

private theorem reflection_graph (x : H) :
    reflection hw0 hw1 t ht x = Sub (R x) (Out (Dom x)) := by
  apply bondValue_injective hw0 hw1
  apply completed_eq_of_pairings hw0 hw1
  intro z
  unfold reflection
  rw [bondValue_sub, bondValue_smul, bondValue_sub,
    completedInner_sub_left, completedInner_smul_left, completedInner_sub_left]
  have hx := congrArg (fun a => BV (value a) z) (graph_sum hw0 hw1 t ht x)
  dsimp only at hx
  rw [bondValue_add, completedInner_add_left] at hx
  rw [← hx]
  refine Quotient.inductionOn₂ (BV (value (R x)) z) (BV (value (Out (Dom x))) z) ?_
  intro a b
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.const 2) (.var 0)) (.neg (.add (.var 0) (.var 1))))
      (.add (.var 0) (.neg (.var 1))) (by decide)
      (fun | 0 => a.approx n | _ => b.approx n)))

theorem reflection_symmetric (x y : H) :
    B (reflection hw0 hw1 t ht x) y = B x (reflection hw0 hw1 t ht y) := by
  unfold reflection
  rw [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    resolvent_symmetric]

theorem reflection_sub (x y : H) :
    reflection hw0 hw1 t ht (Sub x y) = Sub (reflection hw0 hw1 t ht x) (reflection hw0 hw1 t ht y) := by
  unfold reflection
  rw [resolvent_sub]
  apply bondValue_injective hw0 hw1
  apply completed_eq_of_pairings hw0 hw1
  intro z
  simp only [bondValue_sub, bondValue_smul, completedInner_sub_left, completedInner_smul_left]
  refine Quotient.inductionOn₃ (BV (value (R x)) z) (BV (value (R y)) z)
    (BV (value x) z) ?_
  intro a b c
  refine Quotient.inductionOn (BV (value y) z) ?_
  intro d
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.const 2) (.add (.var 0) (.neg (.var 1))))
        (.neg (.add (.var 2) (.neg (.var 3)))))
      (.add (.add (.mul (.const 2) (.var 0)) (.neg (.var 2)))
        (.neg (.add (.mul (.const 2) (.var 1)) (.neg (.var 3)))))
      (by decide) (fun | 0 => a.approx n | 1 => b.approx n | 2 => c.approx n | _ => d.approx n)))

theorem reflection_smul (a : Q') (x : H) :
    reflection hw0 hw1 t ht (Scale a x) =
      Scale a (reflection hw0 hw1 t ht x) := by
  unfold reflection
  rw [resolvent_smul]
  apply bondValue_injective hw0 hw1
  apply completed_eq_of_pairings hw0 hw1
  intro z
  simp only [bondValue_sub, bondValue_smul,
    completedInner_sub_left, completedInner_smul_left]
  refine Quotient.inductionOn₂ (BV (value (R x)) z) (BV (value x) z) ?_
  intro X Y
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.const 2) (.mul (.var 2) (.var 0))) (.neg (.mul (.var 2) (.var 1))))
      (.mul (.var 2) (.add (.mul (.const 2) (.var 0)) (.neg (.var 1))))
      (by decide) (fun | 0 => X.approx n | 1 => Y.approx n | _ => a)))

private theorem sub_norm_le_add_norm (x y : H) (h : RCnonneg (B x y)) :
    RCle (B (Sub x y) (Sub x y)) (B (Add x y) (Add x y)) := by
  have hz : RCnonneg (RCscale (4 : Q') (B x y)) := by
    change RCle RCzero (RCscale (4 : Q') (B x y))
    rw [← RCscale_RCzero (4 : Q')]
    exact RCscale_mono (by decide) h
  have ha := RCadd_le_add (RCle_refl (B (Sub x y) (Sub x y))) hz
  have hzero (a : RC) : RCadd a RCzero = a := by
    refine Quotient.inductionOn a ?_
    intro A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => QPoly.q_add_zero_eqv (A.approx n)))
  rw [hzero] at ha
  have hp : RCadd (B (Sub x y) (Sub x y)) (RCscale 4 (B x y)) =
      B (Add x y) (Add x y) := by
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      inner_symm hw0 hw1 y x]
    refine Quotient.inductionOn₃ (B x x) (B x y) (B y y) ?_
    intro a b c
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add
          (.add (.add (.var 0) (.neg (.var 1)))
            (.neg (.add (.var 1) (.neg (.var 2)))))
          (.mul (.const 4) (.var 1)))
        (.add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 2)))
        (by decide) (fun | 0 => a.approx n | 1 => b.approx n | _ => c.approx n)))
  rwa [hp] at ha

/-- Graph positivity makes the reflected resolvent contractive on EVERY
original physical bond class, with no inverse heat floor or width factor. -/
theorem reflection_norm_bound (x : H) :
    RCle (B (reflection hw0 hw1 t ht x) (reflection hw0 hw1 t ht x)) (B x x) := by
  have h := nonnegative hw0 hw1 (Dom x)
  rw [input_resolventDomain] at h
  have hscale := RCscale_mono (Q'.le_of_lt ht) h
  rw [RCscale_RCzero] at hscale
  have hp : RCnonneg (B (R x) (Out (Dom x))) := by
    rw [inner_smul_right]
    exact hscale
  have hn := sub_norm_le_add_norm hw0 hw1 (R x) (Out (Dom x)) hp
  rw [reflection_graph, graph_sum] at *
  exact hn

/-- The concrete contraction whose geometric series will invert
R^2+(I-R)^2. Defined directly by the symmetric reflected resolvent. -/
def neumannStep (x : H) : H :=
  Scale HalfPow.half (Sub x (reflection hw0 hw1 t ht (reflection hw0 hw1 t ht x)))

private theorem sub_cancel (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.sub_add_cancel_eqv (A.approx n) (B'.approx n)))

private theorem sub_le_self (a b : RC) (hb : RCnonneg b) : RCle (RCsub a b) a := by
  have h := RCadd_le_add (RCle_refl a) (neg_mono hb)
  have hz : RCneg RCzero = RCzero := Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun _ => (by decide : Q'.eqv (-(0 : Q')) 0)))
  have ha : RCadd a RCzero = a := by
    refine Quotient.inductionOn a ?_
    intro A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => QPoly.q_add_zero_eqv (A.approx n)))
  rwa [hz, ha] at h

theorem square_complement_bound (x : H) :
    RCle (B (Sub x (reflection hw0 hw1 t ht (reflection hw0 hw1 t ht x)))
      (Sub x (reflection hw0 hw1 t ht (reflection hw0 hw1 t ht x)))) (B x x) := by
  let sx := reflection hw0 hw1 t ht x
  let ssx := reflection hw0 hw1 t ht sx
  have hc := reflection_norm_bound hw0 hw1 t ht sx
  have hb := inner_nonnegative hw0 hw1 sx
  have hs : B x ssx = B sx sx := (reflection_symmetric hw0 hw1 t ht x sx).symm
  have heq : B (Sub x ssx) (Sub x ssx) =
      RCadd (RCsub (RCsub (B x x) (B sx sx)) (B sx sx)) (B ssx ssx) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hs, inner_symm hw0 hw1 ssx x, hs]
    refine Quotient.inductionOn₃ (B x x) (B sx sx) (B ssx ssx) ?_
    intro a b c
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1)))
          (.neg (.add (.var 1) (.neg (.var 2)))))
        (.add (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 1))) (.var 2))
        (by decide) (fun | 0 => a.approx n | 1 => b.approx n | _ => c.approx n)))
  rw [heq]
  have h := RCadd_le_add (RCle_refl (RCsub (RCsub (B x x) (B sx sx)) (B sx sx))) hc
  rw [sub_cancel] at h
  exact RCle_trans h (sub_le_self _ _ hb)

/-- Sharp squared-norm factor 1/4, independent of nome, width and state.
This is an actual operator estimate, NOT a supplied contraction certificate. -/
theorem neumannStep_norm_bound (x : H) :
    RCle (B (neumannStep hw0 hw1 t ht x) (neumannStep hw0 hw1 t ht x))
      (RCscale (HalfPow.half*HalfPow.half) (B x x)) := by
  unfold neumannStep
  rw [inner_smul_left, inner_smul_right, RCscale_RCscale]
  exact RCscale_mono (by decide) (square_complement_bound hw0 hw1 t ht x)

/-- Exact same-operator polynomial pin. No auxiliary dynamics replaces A. -/
theorem neumannStep_resolvent_pin (x : H) :
    neumannStep hw0 hw1 t ht x = Scale 2 (R (Sub x (R x))) := by
  unfold neumannStep reflection
  rw [resolvent_sub, resolvent_smul, resolvent_sub]
  apply bondValue_injective hw0 hw1
  apply completed_eq_of_pairings hw0 hw1
  intro z
  simp only [bondValue_sub, bondValue_smul, completedInner_sub_left, completedInner_smul_left]
  refine Quotient.inductionOn₃ (BV (value x) z) (BV (value (R x)) z)
    (BV (value (R (R x))) z) ?_
  intro a b c
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  have h := poly_identity_of_normal_eq
      (.mul (.var 3)
        (.add (.var 0) (.neg
          (.add (.mul (.const 2) (.add (.mul (.const 2) (.var 2)) (.neg (.var 1))))
            (.neg (.add (.mul (.const 2) (.var 1)) (.neg (.var 0))))))))
      (.mul (.var 3) (.mul (.const 2) (.mul (.const 2) (.add (.var 1) (.neg (.var 2))))))
      (by decide) (fun | 0 => a.approx n | 1 => b.approx n | 2 => c.approx n | _ => HalfPow.half)
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv (HalfPow.half*2) 1))
        (Q'.one_mul_eqv _)))

theorem neumannStep_sub (x y : H) :
    neumannStep hw0 hw1 t ht (Sub x y) = Sub (neumannStep hw0 hw1 t ht x) (neumannStep hw0 hw1 t ht y) := by
  unfold neumannStep
  rw [reflection_sub, reflection_sub]
  apply bondValue_injective hw0 hw1
  apply completed_eq_of_pairings hw0 hw1
  intro z
  simp only [bondValue_sub, bondValue_smul, completedInner_sub_left, completedInner_smul_left]
  refine Quotient.inductionOn₃ (BV (value x) z) (BV (value y) z)
    (BV (value (reflection hw0 hw1 t ht (reflection hw0 hw1 t ht x))) z) ?_
  intro a b c
  refine Quotient.inductionOn
    (BV (value (reflection hw0 hw1 t ht (reflection hw0 hw1 t ht y))) z) ?_
  intro d
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.var 4) (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.add (.var 2) (.neg (.var 3))))))
      (.add (.mul (.var 4) (.add (.var 0) (.neg (.var 2))))
        (.neg (.mul (.var 4) (.add (.var 1) (.neg (.var 3))))))
      (by decide) (fun | 0 => a.approx n | 1 => b.approx n | 2 => c.approx n | 3 => d.approx n | _ => HalfPow.half)))

theorem neumannStep_smul (a : Q') (x : H) :
    neumannStep hw0 hw1 t ht (Scale a x) =
      Scale a (neumannStep hw0 hw1 t ht x) := by
  unfold neumannStep
  rw [reflection_smul, reflection_smul]
  apply bondValue_injective hw0 hw1
  apply completed_eq_of_pairings hw0 hw1
  intro z
  simp only [bondValue_sub, bondValue_smul,
    completedInner_sub_left, completedInner_smul_left]
  refine Quotient.inductionOn₂ (BV (value x) z)
    (BV (value (reflection hw0 hw1 t ht (reflection hw0 hw1 t ht x))) z) ?_
  intro X Y
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.var 3) (.add (.mul (.var 2) (.var 0))
        (.neg (.mul (.var 2) (.var 1)))))
      (.mul (.var 2) (.mul (.var 3) (.add (.var 0) (.neg (.var 1)))))
      (by decide) (fun | 0 => X.approx n | 1 => Y.approx n | 2 => a | _ => HalfPow.half)))

/-- The strict factor also controls differences of arbitrary physical states. -/
theorem neumannStep_distance_bound (x y : H) :
    RCle (bondCompletedDistance hw0 hw1 (neumannStep hw0 hw1 t ht x) (neumannStep hw0 hw1 t ht y))
      (RCscale (HalfPow.half*HalfPow.half) (bondCompletedDistance hw0 hw1 x y)) := by
  have h := neumannStep_norm_bound hw0 hw1 t ht (Sub x y)
  rw [neumannStep_sub, bondValue_inner, bondValue_inner, bondValue_sub] at h
  simpa only [bondValue_distance, BF4WilsonAllNomeDistance.completedDist,
    bondValue_sub] using h

#print axioms reflection
#print axioms reflection_symmetric
#print axioms reflection_sub
#print axioms reflection_smul
#print axioms reflection_norm_bound
#print axioms neumannStep
#print axioms square_complement_bound
#print axioms neumannStep_norm_bound
#print axioms neumannStep_resolvent_pin
#print axioms neumannStep_sub
#print axioms neumannStep_smul
#print axioms neumannStep_distance_bound

end YMGap.Continuum.BF4WilsonAllNomeBondOSScaledReflection
