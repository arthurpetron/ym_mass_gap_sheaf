/-
# Actual two-sided resolvent-denominator inverse on the physical bond carrier

The represented geometric limit descends to EVERY original physical bond
class without representative choice. It constructs the inverse of
D=I-2R(I-R)=R^2+(I-R)^2, R=(I+A)^(-1). The norm ceiling is 2 (squared
ceiling 4); positivity gives D a form floor 1/2 and hence injectivity.
No new analytic premise is added. This is the real denominator needed by
imaginary shifts and the complex Cayley transform of the SAME derivative.
Those maps, physical time calibration and continuum reconstruction remain
separate obligations at this checkpoint.
-/

import YMGap.Continuum.BF4WilsonAllNomeResolventNeumannLimit

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSResolventDenominator

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
  (BondCompletion Rows toSectorRep rowSetoid close_iff_limit_eq bondCompletedInner bondCompletedDistance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_inner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (ofState ofState_congr bondValue_ofState bondValue_add bondValue_sub bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeBondOSResolventReflection
  (reflection reflection_symmetric neumannStep neumannStep_sub neumannStep_smul)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => BondCompletion hw0 hw1 (width := width)
local notation "B" => bondCompletedInner hw0 hw1
local notation "BV" => completedInner hw0 hw1
local notation "value" => bondValue hw0 hw1
local notation "Add" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "Sub" => BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
local notation "Scale" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "N" => neumannStep hw0 hw1
local notation "R" => BF4WilsonAllNomeBondOSResolvent.resolvent hw0 hw1 1 (by decide)

/-- The exact original-operator denominator, not a supplied invertible map. -/
def denominator (x : H) : H := Sub x (N x)

/-- Literal square denominator of the SAME positive resolvent and complement. -/
theorem denominator_resolvent_square_pin (x : H) :
    denominator hw0 hw1 x = Add (R (R x)) (Sub (Sub x (R x)) (R (Sub x (R x)))) := by
  unfold denominator
  rw [BF4WilsonAllNomeBondOSResolventReflection.neumannStep_resolvent_pin]
  simp only [BF4WilsonAllNomeBondOSResolventReflection.resolvent_sub]
  apply bondValue_injective hw0 hw1
  apply completed_eq_of_pairings hw0 hw1
  intro z
  simp only [bondValue_sub, bondValue_add, bondValue_smul,
    completedInner_sub_left, completedInner_add_left, completedInner_smul_left]
  refine Quotient.inductionOn₃ (BV (value x) z) (BV (value (R x)) z) (BV (value (R (R x))) z) ?_
  intro A B' C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.mul (.const 2) (.add (.var 1) (.neg (.var 2))))))
      (.add (.var 2) (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.add (.var 1) (.neg (.var 2))))))
      (by decide) (fun | 0 => A.approx n | 1 => B'.approx n | _ => C.approx n)))

/-- Stored Rows supply their own time-range states and geometric moduli.
Congruence compares limits; it never chooses a quotient representative. -/
def normalized : H → H := Quotient.lift
  (fun X => ofState hw0 hw1 (BF4WilsonAllNomeResolventNeumannLimit.normalized hw0 hw1
    (toSectorRep hw0 hw1 X)))
  (fun X Y h => ofState_congr hw0 hw1
    (BF4WilsonAllNomeResolventNeumannLimit.normalized_congr hw0 hw1
      ((close_iff_limit_eq hw0 hw1 X Y).mp h)))

def inverse (x : H) : H := Scale 2 (normalized hw0 hw1 x)

theorem normalized_fixed_point (x : H) :
    normalized hw0 hw1 x = Add (Scale HalfPow.half x) (N (normalized hw0 hw1 x)) := by
  apply bondValue_injective hw0 hw1
  induction x using Quotient.inductionOn with
  | h X =>
      let u := BF4WilsonAllNomeResolventNeumannLimit.normalized hw0 hw1 (toSectorRep hw0 hw1 X)
      change value (ofState hw0 hw1 u) = value
        (Add (Scale HalfPow.half
          (Quotient.mk (BF4WilsonAllNomeBondOSCompletion.rowSetoid hw0 hw1) X))
          (N (ofState hw0 hw1 u)))
      rw [bondValue_add, bondValue_smul,
        ← BF4WilsonAllNomeResolventNeumannLimit.stepState_pin,
        bondValue_ofState, bondValue_ofState]
      exact BF4WilsonAllNomeResolventNeumannLimit.fixed_point hw0 hw1 (toSectorRep hw0 hw1 X)

theorem normalized_norm_bound (x : H) :
    RCle (B (normalized hw0 hw1 x) (normalized hw0 hw1 x)) (B x x) := by
  rw [bondValue_inner, bondValue_inner]
  induction x using Quotient.inductionOn with
  | h X =>
      change RCle (BV (value (ofState hw0 hw1
        (BF4WilsonAllNomeResolventNeumannLimit.normalized hw0 hw1 (toSectorRep hw0 hw1 X))))
        (value (ofState hw0 hw1
          (BF4WilsonAllNomeResolventNeumannLimit.normalized hw0 hw1 (toSectorRep hw0 hw1 X)))))
        (BV (toSectorRep hw0 hw1 X).val (toSectorRep hw0 hw1 X).val)
      rw [bondValue_ofState]
      exact BF4WilsonAllNomeResolventNeumannLimit.normalized_norm_bound hw0 hw1 _

/-- The constructed all-class inverse has squared-norm ceiling 4. -/
theorem inverse_norm_bound (x : H) :
    RCle (B (inverse hw0 hw1 x) (inverse hw0 hw1 x)) (RCscale 4 (B x x)) := by
  unfold inverse
  simp only [bondValue_inner, bondValue_smul, completedInner_smul_left,
    completedInner_smul_right, RCscale_RCscale]
  rw [scale_congr (by decide : Q'.eqv ((2 : Q')*2) 4)]
  simpa only [bondValue_inner] using
    RCscale_mono (by decide : (0 : Q') ≤ 4) (normalized_norm_bound hw0 hw1 x)

private theorem sub_add_right_cancel (a b : RC) : RCsub (RCadd a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
      (by decide) (fun | 0 => A.approx n | _ => B'.approx n)))

/-- The actual geometric construction is a right inverse on EVERY bond class. -/
theorem inverse_right (x : H) : denominator hw0 hw1 (inverse hw0 hw1 x) = x := by
  unfold denominator inverse
  rw [neumannStep_smul]
  apply bondValue_injective hw0 hw1
  apply completed_eq_of_pairings hw0 hw1
  intro z
  simp only [bondValue_sub, bondValue_smul, completedInner_sub_left, completedInner_smul_left]
  have hf := congrArg (fun a => BV (value a) z) (normalized_fixed_point hw0 hw1 x)
  dsimp only at hf
  rw [bondValue_add, bondValue_smul, completedInner_add_left, completedInner_smul_left] at hf
  rw [hf, RCscale_RCadd, RCscale_RCscale,
    scale_congr (by decide : Q'.eqv ((2 : Q')*HalfPow.half) 1), RCscale_one,
    sub_add_right_cancel]

private theorem inner_sub_left (x y z : H) : B (Sub x y) z = RCsub (B x z) (B y z) := by
  rw [bondValue_inner, bondValue_sub, completedInner_sub_left, bondValue_inner, bondValue_inner]

private theorem inner_sub_right (x y z : H) : B x (Sub y z) = RCsub (B x y) (B x z) := by
  rw [bondValue_inner, bondValue_sub, completedInner_sub_right, bondValue_inner, bondValue_inner]

private theorem inner_smul_right (a : Q') (x y : H) : B x (Scale a y) = RCscale a (B x y) := by
  rw [bondValue_inner, bondValue_smul, completedInner_smul_right, bondValue_inner]

theorem denominator_diagonal (x : H) :
    B x (denominator hw0 hw1 x) =
      RCadd (RCscale HalfPow.half (B x x))
        (RCscale HalfPow.half (B (reflection hw0 hw1 x) (reflection hw0 hw1 x))) := by
  unfold denominator neumannStep
  rw [inner_sub_right, inner_smul_right, inner_sub_right,
    ← reflection_symmetric hw0 hw1 x (reflection hw0 hw1 x)]
  refine Quotient.inductionOn₂ (B x x) (B (reflection hw0 hw1 x) (reflection hw0 hw1 x)) ?_
  intro A B'
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  have h := poly_identity_of_normal_eq
    (.add (.var 0) (.neg (.mul (.var 2) (.add (.var 0) (.neg (.var 1))))))
    (.add (.mul (.add (.const 1) (.neg (.var 2))) (.var 0)) (.mul (.var 2) (.var 1)))
    (by decide) (fun | 0 => A.approx n | 1 => B'.approx n | _ => HalfPow.half)
  exact Q'.eqv_trans _ _ _ h
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv (1-HalfPow.half) HalfPow.half))
      (Q'.eqv_refl _))

/-- Uniform coercivity of this actual resolvent denominator, NOT a mass gap. -/
theorem denominator_form_floor (x : H) :
    RCle (RCscale HalfPow.half (B x x)) (B x (denominator hw0 hw1 x)) := by
  rw [denominator_diagonal]
  have hn : RCnonneg (B (reflection hw0 hw1 x) (reflection hw0 hw1 x)) := by
    rw [bondValue_inner]
    exact completedInner_nonnegative hw0 hw1 _
  have h := RCscale_mono (by decide : (0 : Q') ≤ HalfPow.half) hn
  rw [RCscale_RCzero] at h
  have hs := RCadd_le_add (RCle_refl (RCscale HalfPow.half (B x x))) h
  have hz (a : RC) : RCadd a RCzero = a := by
    refine Quotient.inductionOn a ?_
    intro A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => QPoly.q_add_zero_eqv (A.approx n)))
  rwa [hz] at hs

theorem denominator_sub (x y : H) :
    denominator hw0 hw1 (Sub x y) = Sub (denominator hw0 hw1 x) (denominator hw0 hw1 y) := by
  unfold denominator
  rw [neumannStep_sub]
  apply bondValue_injective hw0 hw1
  apply completed_eq_of_pairings hw0 hw1
  intro z
  simp only [bondValue_sub, completedInner_sub_left]
  refine Quotient.inductionOn₃ (BV (value x) z) (BV (value y) z) (BV (value (N x)) z) ?_
  intro A B' C
  refine Quotient.inductionOn (BV (value (N y)) z) ?_
  intro D
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.neg (.var 3)))))
      (.add (.add (.var 0) (.neg (.var 2))) (.neg (.add (.var 1) (.neg (.var 3)))))
      (by decide) (fun | 0 => A.approx n | 1 => B'.approx n | 2 => C.approx n | _ => D.approx n)))

theorem denominator_injective {x y : H}
    (h : denominator hw0 hw1 x = denominator hw0 hw1 y) : x = y := by
  let d := Sub x y
  have hz : value (denominator hw0 hw1 d) = completedZero hw0 hw1 width := by
    rw [denominator_sub, h, bondValue_sub, completedSub_self]
  have hp := denominator_form_floor hw0 hw1 d
  rw [bondValue_inner, bondValue_inner, hz, completedInner_zero_right] at hp
  have hc := RCscale_mono (by decide : (0 : Q') ≤ 2) hp
  rw [RCscale_RCscale, RCscale_RCzero,
    scale_congr (by decide : Q'.eqv ((2 : Q')*HalfPow.half) 1), RCscale_one] at hc
  have hn := completedInner_nonnegative hw0 hw1 (value d)
  have hd : BV (value d) (value d) = RCzero := RCle_antisymm hc hn
  rw [bondValue_sub] at hd
  exact bondValue_injective hw0 hw1
    ((BF4WilsonAllNomeDistance.completedDist_zero_iff hw0 hw1 (value x) (value y)).mp hd)

/-- Both inverse laws refer to the SAME actual denominator and completion. -/
theorem inverse_left (x : H) : inverse hw0 hw1 (denominator hw0 hw1 x) = x :=
  denominator_injective hw0 hw1 (inverse_right hw0 hw1 (denominator hw0 hw1 x))

/-- Actual finite iterates on supplied physical Rows, retaining their witness. -/
def inverseApproximation (X : Rows hw0 hw1 (width := width)) (n : Nat) : H :=
  Scale 2 (ofState hw0 hw1
    (BF4WilsonAllNomeResolventNeumannLimit.neumannPartial hw0 hw1 (toSectorRep hw0 hw1 X) n))

/-- Squared-distance factor four is paid explicitly at epsilon/4. -/
def inverseRate (X : Rows hw0 hw1 (width := width)) (epsilon : Q') : Nat :=
  BF4WilsonAllNomeResolventNeumannLimit.normalizedRate hw0 hw1 (toSectorRep hw0 hw1 X)
    (BF4ExactSlabPlaquetteCompletedApproximation.quarter epsilon)

theorem inverse_approximation_bound (X : Rows hw0 hw1 (width := width))
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat) (hn : inverseRate hw0 hw1 X epsilon ≤ n) :
    RCle (bondCompletedDistance hw0 hw1 (inverseApproximation hw0 hw1 X n)
      (inverse hw0 hw1 (Quotient.mk (rowSetoid hw0 hw1) X)))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  let q := BF4ExactSlabPlaquetteCompletedApproximation.quarter epsilon
  have h := BF4WilsonAllNomeResolventNeumannLimit.normalized_bound hw0 hw1
    (toSectorRep hw0 hw1 X) q (BF4ExactSlabPlaquetteCompletedApproximation.quarter_pos he) n hn
  change RCle (bondCompletedDistance hw0 hw1
    (Scale 2 (ofState hw0 hw1
      (BF4WilsonAllNomeResolventNeumannLimit.neumannPartial hw0 hw1 (toSectorRep hw0 hw1 X) n)))
    (Scale 2 (ofState hw0 hw1
      (BF4WilsonAllNomeResolventNeumannLimit.normalized hw0 hw1 (toSectorRep hw0 hw1 X))))) _
  rw [BF4WilsonAllNomeBondOSTime.bondValue_distance, bondValue_smul, bondValue_smul,
    bondValue_ofState, bondValue_ofState, BF4WilsonAllNomeDerivativeGraphLinear.completedDist_smul]
  have hs := RCscale_mono (by decide : (0 : Q') ≤ (2 : Q')*2) h
  have hb : RCscale ((2 : Q')*2) (Quotient.mk crealSetoid (ofQ' q)) =
      Quotient.mk crealSetoid (ofQ' epsilon) := by
    apply Quotient.sound
    apply SumOfSquares.Equiv_of_approx_eqv
    intro k
    change Q'.eqv (((2 : Q')*2)*(HalfPow.half*(HalfPow.half*epsilon))) epsilon
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.const 2) (.const 2)) (.mul (.var 0) (.mul (.var 0) (.var 1))))
        (.mul (.mul (.mul (.const 2) (.const 2)) (.mul (.var 0) (.var 0))) (.var 1))
        (by decide) (fun | 0 => HalfPow.half | _ => epsilon))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv (((2 : Q')*2)*(HalfPow.half*HalfPow.half)) 1))
        (Q'.one_mul_eqv _))
  rwa [hb] at hs

/-- Both constructive inverse and convergence modulus remain Type-level data.
The input is supplied Rows; no rate is extracted by selecting a class representative. -/
def inverseCertificate (X : Rows hw0 hw1 (width := width)) :
    Σ' y : H, Σ' rate : Q' → Nat,
      (denominator hw0 hw1 y = Quotient.mk (rowSetoid hw0 hw1) X) ×'
      (∀ epsilon, (0 : Q') < epsilon → ∀ n, rate epsilon ≤ n →
        RCle (bondCompletedDistance hw0 hw1 (inverseApproximation hw0 hw1 X n) y)
          (Quotient.mk crealSetoid (ofQ' epsilon))) :=
  ⟨inverse hw0 hw1 (Quotient.mk (rowSetoid hw0 hw1) X), inverseRate hw0 hw1 X,
    inverse_right hw0 hw1 _, inverse_approximation_bound hw0 hw1 X⟩

#print axioms denominator
#print axioms denominator_resolvent_square_pin
#print axioms normalized
#print axioms inverse
#print axioms normalized_fixed_point
#print axioms normalized_norm_bound
#print axioms inverse_norm_bound
#print axioms inverse_right
#print axioms denominator_diagonal
#print axioms denominator_form_floor
#print axioms denominator_sub
#print axioms denominator_injective
#print axioms inverse_left
#print axioms inverseApproximation
#print axioms inverseRate
#print axioms inverse_approximation_bound
#print axioms inverseCertificate

end YMGap.Continuum.BF4WilsonAllNomeBondOSResolventDenominator
