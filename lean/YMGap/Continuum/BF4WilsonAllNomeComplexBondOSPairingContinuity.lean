/-
# Two-slot Hermitian pairing continuity on the original Wilson bond carrier

The four real completed pairings retain both diagonal terms and both signed
cross terms.  A single rational cap and the existing real pairing tolerance
control two varying complex inputs.  This finite estimate is the continuity
input for passing original unitary difference quotients to the intrinsic
adjoint graph; it asserts no generator or physical-clock identification.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
import YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
import YMGap.Continuum.RCSignedPairBudget
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSPairingContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist)
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
  (pairingTolerance pairingTolerance_pos)
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity (pairing_close)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion value inner inner_value)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "D" => completedDist hw0 hw1
local notation "I" => inner hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem rat_eqv {a b : Q'} (h : Q'.eqv a b) : (rat a) = (rat b) :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => h))

/-- Moving two summands by `q` costs exactly two copies of `q`. -/
private theorem add_two_errors (a b : RC) (q e : Q')
    (hqe : Q'.eqv (q+q) e) :
    RCadd (RCadd a (rat q)) (RCadd b (rat q)) =
      RCadd (RCadd a b) (rat e) := by
  have hcore : RCadd (RCadd a (rat q)) (RCadd b (rat q)) =
      RCadd (RCadd a b) (rat (q+q)) := by
    refine Quotient.inductionOn₂ a b ?_
    intro A C
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 2)))
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 2)))
        (by decide) (fun | 0 => A.approx n | 1 => C.approx n | _ => q)))
  exact hcore.trans (congrArg (RCadd (RCadd a b)) (rat_eqv hqe))

/-- A two-sided real error stays two-sided when the quantity is negated. -/
private theorem neg_close {a b : RC} (q : Q')
    (h : RCle b (RCadd a (rat q))) :
    RCle (RCneg a) (RCadd (RCneg b) (rat q)) := by
  have hn := RCSignedPairBudget.neg_mono h
  have hsum := RCadd_le_add hn (RCle_refl (rat q))
  have hcancel : RCadd (RCneg (RCadd a (rat q))) (rat q) = RCneg a := by
    refine Quotient.inductionOn a ?_
    intro A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.neg (.add (.var 0) (.var 1))) (.var 1))
        (.neg (.var 0)) (by decide)
        (fun | 0 => A.approx n | _ => q)))
  rwa [hcancel] at hsum

private theorem sum_close {a a' b b' : RC} (q e : Q')
    (hqe : Q'.eqv (q+q) e)
    (ha : RCle a (RCadd a' (rat q)))
    (hb : RCle b (RCadd b' (rat q))) :
    RCle (RCadd a b) (RCadd (RCadd a' b') (rat e)) := by
  have h := RCadd_le_add ha hb
  rwa [add_two_errors a' b' q e hqe] at h

private theorem difference_close {a a' b b' : RC} (q e : Q')
    (hqe : Q'.eqv (q+q) e)
    (ha : RCle a (RCadd a' (rat q)))
    (hb : RCle b' (RCadd b (rat q))) :
    RCle (RCsub a b) (RCadd (RCsub a' b') (rat e)) := by
  change RCle (RCadd a (RCneg b)) (RCadd (RCadd a' (RCneg b')) (rat e))
  exact sum_close q e hqe ha (neg_close q hb)

/-- The actual complex Hermitian pairing is continuous in BOTH inputs.
The eight norm/distance pins are exactly the four applications of the
original real two-slot estimate.  The common cap and tolerance are explicit
rational data, not an inferred uniform source bound. -/
theorem inner_pairing_close (x x' y y' : H)
    (cap : Q') (hcap : (0 : Q') ≤ cap)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hx₁ : RCle (D (value hw0 hw1 x).1 (value hw0 hw1 x').1)
      (rat (pairingTolerance cap hcap (HalfPow.half*epsilon))))
    (hx₂ : RCle (D (value hw0 hw1 x).2 (value hw0 hw1 x').2)
      (rat (pairingTolerance cap hcap (HalfPow.half*epsilon))))
    (hy₁ : RCle (D (value hw0 hw1 y).1 (value hw0 hw1 y').1)
      (rat (pairingTolerance cap hcap (HalfPow.half*epsilon))))
    (hy₂ : RCle (D (value hw0 hw1 y).2 (value hw0 hw1 y').2)
      (rat (pairingTolerance cap hcap (HalfPow.half*epsilon))))
    (hyNorm₁ : RCle (B (value hw0 hw1 y).1 (value hw0 hw1 y).1) (rat cap))
    (hyNorm₂ : RCle (B (value hw0 hw1 y).2 (value hw0 hw1 y).2) (rat cap))
    (hxNorm₁ : RCle (B (value hw0 hw1 x').1 (value hw0 hw1 x').1) (rat cap))
    (hxNorm₂ : RCle (B (value hw0 hw1 x').2 (value hw0 hw1 x').2) (rat cap)) :
    (RCle (I x y).1 (RCadd (I x' y').1 (rat epsilon)) ∧
      RCle (I x' y').1 (RCadd (I x y).1 (rat epsilon))) ∧
    (RCle (I x y).2 (RCadd (I x' y').2 (rat epsilon)) ∧
      RCle (I x' y').2 (RCadd (I x y).2 (rat epsilon))) := by
  let q := HalfPow.half*epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  have hqe : Q'.eqv (q+q) epsilon := ExpNeg.two_halves epsilon
  let X := value hw0 hw1 x
  let X' := value hw0 hw1 x'
  let Y := value hw0 hw1 y
  let Y' := value hw0 hw1 y'
  have h₁₁ := pairing_close hw0 hw1 X.1 X'.1 Y.1 Y'.1 cap hcap q hq
    hx₁ hy₁ hyNorm₁ hxNorm₁
  have h₂₂ := pairing_close hw0 hw1 X.2 X'.2 Y.2 Y'.2 cap hcap q hq
    hx₂ hy₂ hyNorm₂ hxNorm₂
  have h₁₂ := pairing_close hw0 hw1 X.1 X'.1 Y.2 Y'.2 cap hcap q hq
    hx₁ hy₂ hyNorm₂ hxNorm₁
  have h₂₁ := pairing_close hw0 hw1 X.2 X'.2 Y.1 Y'.1 cap hcap q hq
    hx₂ hy₁ hyNorm₁ hxNorm₂
  simp only [inner_value, BF4WilsonAllNomeComplexification.inner]
  constructor
  · constructor
    · change RCle (RCadd (B X.1 Y.1) (B X.2 Y.2))
        (RCadd (RCadd (B X'.1 Y'.1) (B X'.2 Y'.2)) (rat epsilon))
      exact sum_close q epsilon hqe h₁₁.1 h₂₂.1
    · change RCle (RCadd (B X'.1 Y'.1) (B X'.2 Y'.2))
        (RCadd (RCadd (B X.1 Y.1) (B X.2 Y.2)) (rat epsilon))
      exact sum_close q epsilon hqe h₁₁.2 h₂₂.2
  · constructor
    · change RCle (RCsub (B X.1 Y.2) (B X.2 Y.1))
        (RCadd (RCsub (B X'.1 Y'.2) (B X'.2 Y'.1)) (rat epsilon))
      exact difference_close q epsilon hqe h₁₂.1 h₂₁.2
    · change RCle (RCsub (B X'.1 Y'.2) (B X'.2 Y'.1))
        (RCadd (RCsub (B X.1 Y.2) (B X.2 Y.1)) (rat epsilon))
      exact difference_close q epsilon hqe h₁₂.2 h₂₁.1

#print axioms inner_pairing_close

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSPairingContinuity
