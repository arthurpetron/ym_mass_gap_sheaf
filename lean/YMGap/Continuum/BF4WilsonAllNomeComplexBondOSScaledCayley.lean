/-
# Actual unitary Cayley map on the ORIGINAL complex physical bond completion

For EVERY positive rational t, the constructed scaled imaginary-shift
preimages and the original graph symmetry
give a two-sided Cayley inverse and preservation of the full Hermitian form.
Surjective pairing tests then prove complex linearity, without separately
assuming linearity of the denominator inverse. Scalars retain their supplied
Cauchy witnesses. No spectral theorem, representative choice or analytic
hypothesis is added. The parameter t is explicit and nome/width stay fixed. This is not a
continuum Hamiltonian, physical-time unitary group or physical mass gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCayley

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayley

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist_zero_iff)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (BondCompletion bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_inner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_sub bondValue_smul bondValue_zero)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCayley (eq_of_pairings)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion (ComplexBondCompletion inner)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSTime
  (inner_add_left inner_smul_left)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts
  (plus minus plusDomain minusDomain plus_right minus_right)
open YMGap.Continuum.BF4WilsonAllNomeComplexification (valueAdd valueMul valueConj scalarValue)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}
  (t : Q') (ht : (0 : Q') < t)

local notation "RH" => BondCompletion hw0 hw1 (width := width)
local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "Domain" => BF4WilsonAllNomeComplexBondOSDerivative.Domain hw0 hw1 (width := width)
local notation "B" => bondCompletedInner hw0 hw1
local notation "BV" => completedInner hw0 hw1
local notation "V" => bondValue hw0 hw1
local notation "Add" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "Sub" => BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
local notation "Scale" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "Z" => BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 (width := width)
local notation "In" => BF4WilsonAllNomeBondOSDerivative.input hw0 hw1
local notation "Out" => (fun d : BF4WilsonAllNomeBondOSDerivative.Domain hw0 hw1 (width := width) =>
  Scale t (BF4WilsonAllNomeBondOSDerivative.output hw0 hw1 d))
local notation "I" => inner hw0 hw1
local notation "P" => plus hw0 hw1 t
local notation "M" => minus hw0 hw1 t

private theorem b_add_left (x y z : RH) : B (Add x y) z = RCadd (B x z) (B y z) := by
  rw [bondValue_inner, bondValue_add, completedInner_add_left, bondValue_inner, bondValue_inner]

private theorem b_add_right (x y z : RH) : B x (Add y z) = RCadd (B x y) (B x z) := by
  rw [bondValue_inner, bondValue_add, completedInner_add_right, bondValue_inner, bondValue_inner]

private theorem b_sub_left (x y z : RH) : B (Sub x y) z = RCsub (B x z) (B y z) := by
  rw [bondValue_inner, bondValue_sub, completedInner_sub_left, bondValue_inner, bondValue_inner]

private theorem b_sub_right (x y z : RH) : B x (Sub y z) = RCsub (B x y) (B x z) := by
  rw [bondValue_inner, bondValue_sub, completedInner_sub_right, bondValue_inner, bondValue_inner]

private theorem b_smul_left (c : Q') (x y : RH) :
    B (Scale c x) y = RCscale c (B x y) := by
  rw [bondValue_inner, bondValue_smul, completedInner_smul_left, bondValue_inner]

private theorem b_smul_right (c : Q') (x y : RH) :
    B x (Scale c y) = RCscale c (B x y) := by
  rw [bondValue_inner, bondValue_smul, completedInner_smul_right, bondValue_inner]

private theorem scaled_symmetric
    (d e : BF4WilsonAllNomeBondOSDerivative.Domain hw0 hw1 (width := width)) :
    B (In d) (Out e) = B (Out d) (In e) := by
  rw [b_smul_left, b_smul_right, BF4WilsonAllNomeBondOSDerivative.symmetric]

private theorem real_cross_cancel (a c g e f l : RC) :
    RCadd (RCsub (RCsub a c) (RCsub g e)) (RCadd (RCadd f g) (RCadd c l)) =
      RCadd (RCadd (RCadd a c) (RCadd g e)) (RCsub (RCsub f g) (RCsub c l)) := by
  refine Quotient.inductionOn₃ a c g ?_
  intro A C G
  refine Quotient.inductionOn₃ e f l ?_
  intro E F L
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.neg (.var 3)))))
        (.add (.add (.var 4) (.var 2)) (.add (.var 1) (.var 5))))
      (.add (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 4) (.neg (.var 2))) (.neg (.add (.var 1) (.neg (.var 5))))))
      (by decide)
      (fun | 0 => A.approx n | 1 => C.approx n | 2 => G.approx n
           | 3 => E.approx n | 4 => F.approx n | _ => L.approx n)))

private theorem imaginary_cross_cancel (a b f d e h : RC) :
    RCsub (RCsub (RCadd a b) (RCadd f d)) (RCadd (RCsub e f) (RCsub b h)) =
      RCsub (RCadd (RCsub a b) (RCsub f d)) (RCsub (RCadd e f) (RCadd b h)) := by
  refine Quotient.inductionOn₃ a b f ?_
  intro A B' F
  refine Quotient.inductionOn₃ d e h ?_
  intro D E H'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
        (.neg (.add (.add (.var 4) (.neg (.var 2))) (.add (.var 1) (.neg (.var 5))))))
      (.add (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3))))
        (.neg (.add (.add (.var 4) (.var 2)) (.neg (.add (.var 1) (.var 5))))))
      (by decide)
      (fun | 0 => A.approx n | 1 => B'.approx n | 2 => F.approx n
           | 3 => D.approx n | 4 => E.approx n | _ => H'.approx n)))

/-- Full graph symmetry cancels ALL real and imaginary cross pairings. -/
theorem shift_pairing (d e : Domain) : I (P d) (P e) = I (M d) (M e) := by
  apply Prod.ext
  · change RCadd (B (Sub (In d.1) (Out d.2)) (Sub (In e.1) (Out e.2)))
      (B (Add (In d.2) (Out d.1)) (Add (In e.2) (Out e.1))) =
      RCadd (B (Add (In d.1) (Out d.2)) (Add (In e.1) (Out e.2)))
      (B (Sub (In d.2) (Out d.1)) (Sub (In e.2) (Out e.1)))
    rw [b_sub_left hw0 hw1 (In d.1) (Out d.2) (Sub (In e.1) (Out e.2)),
      b_sub_right hw0 hw1 (In d.1) (In e.1) (Out e.2),
      b_sub_right hw0 hw1 (Out d.2) (In e.1) (Out e.2),
      b_add_left hw0 hw1 (In d.2) (Out d.1) (Add (In e.2) (Out e.1)),
      b_add_right hw0 hw1 (In d.2) (In e.2) (Out e.1),
      b_add_right hw0 hw1 (Out d.1) (In e.2) (Out e.1),
      b_add_left hw0 hw1 (In d.1) (Out d.2) (Add (In e.1) (Out e.2)),
      b_add_right hw0 hw1 (In d.1) (In e.1) (Out e.2),
      b_add_right hw0 hw1 (Out d.2) (In e.1) (Out e.2),
      b_sub_left hw0 hw1 (In d.2) (Out d.1) (Sub (In e.2) (Out e.1)),
      b_sub_right hw0 hw1 (In d.2) (In e.2) (Out e.1),
      b_sub_right hw0 hw1 (Out d.1) (In e.2) (Out e.1),
      scaled_symmetric hw0 hw1 t d.2 e.1, scaled_symmetric hw0 hw1 t d.1 e.2]
    exact real_cross_cancel _ _ _ _ _ _
  · change RCsub (B (Sub (In d.1) (Out d.2)) (Add (In e.2) (Out e.1)))
      (B (Add (In d.2) (Out d.1)) (Sub (In e.1) (Out e.2))) =
      RCsub (B (Add (In d.1) (Out d.2)) (Sub (In e.2) (Out e.1)))
      (B (Sub (In d.2) (Out d.1)) (Add (In e.1) (Out e.2)))
    rw [b_sub_left hw0 hw1 (In d.1) (Out d.2) (Add (In e.2) (Out e.1)),
      b_add_right hw0 hw1 (In d.1) (In e.2) (Out e.1),
      b_add_right hw0 hw1 (Out d.2) (In e.2) (Out e.1),
      b_add_left hw0 hw1 (In d.2) (Out d.1) (Sub (In e.1) (Out e.2)),
      b_sub_right hw0 hw1 (In d.2) (In e.1) (Out e.2),
      b_sub_right hw0 hw1 (Out d.1) (In e.1) (Out e.2),
      b_add_left hw0 hw1 (In d.1) (Out d.2) (Sub (In e.2) (Out e.1)),
      b_sub_right hw0 hw1 (In d.1) (In e.2) (Out e.1),
      b_sub_right hw0 hw1 (Out d.2) (In e.2) (Out e.1),
      b_sub_left hw0 hw1 (In d.2) (Out d.1) (Add (In e.1) (Out e.2)),
      b_add_right hw0 hw1 (In d.2) (In e.1) (Out e.2),
      b_add_right hw0 hw1 (Out d.1) (In e.1) (Out e.2),
      scaled_symmetric hw0 hw1 t d.2 e.2, scaled_symmetric hw0 hw1 t d.1 e.1]
    exact imaginary_cross_cancel _ _ _ _ _ _

private theorem recover (a b : RH) : Scale HalfPow.half (Add (Sub a b) (Add a b)) = a := by
  apply bondValue_injective hw0 hw1
  apply BF4WilsonAllNomeCompletedRealScalar.completed_eq_of_pairings hw0 hw1
  intro z
  simp only [bondValue_smul, bondValue_add, bondValue_sub, completedInner_smul_left,
    completedInner_add_left, completedInner_sub_left]
  refine Quotient.inductionOn₂ (BV (V a) z) (BV (V b) z) ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.add (.var 1) (.neg (.var 2))) (.add (.var 1) (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (by decide)
      (fun | 0 => HalfPow.half | 1 => A.approx n | _ => B'.approx n))
      (ExpNeg.two_halves (A.approx n))))

private theorem joint_injective {d e : Domain} (hp : P d = P e) (hm : M d = M e) : d = e := by
  have h₁ : In d.1 = In e.1 := calc
    In d.1 = Scale HalfPow.half (Add (P d).1 (M d).1) := (recover hw0 hw1 _ _).symm
    _ = Scale HalfPow.half (Add (P e).1 (M e).1) := by rw [hp, hm]
    _ = In e.1 := recover hw0 hw1 _ _
  have h₂ : In d.2 = In e.2 := calc
    In d.2 = Scale HalfPow.half (Add (M d).2 (P d).2) := (recover hw0 hw1 _ _).symm
    _ = Scale HalfPow.half (Add (M e).2 (P e).2) := by rw [hp, hm]
    _ = In e.2 := recover hw0 hw1 _ _
  exact Prod.ext (BF4WilsonAllNomeBondOSDerivative.input_injective hw0 hw1 h₁)
    (BF4WilsonAllNomeBondOSDerivative.input_injective hw0 hw1 h₂)

include ht in
theorem plus_injective {d e : Domain} (h : P d = P e) : d = e := by
  apply joint_injective hw0 hw1 t h
  apply eq_of_pairings hw0 hw1
  intro z
  rw [← minus_right hw0 hw1 t ht z, ← shift_pairing, ← shift_pairing, h]

include ht in
theorem minus_injective {d e : Domain} (h : M d = M e) : d = e := by
  apply joint_injective hw0 hw1 t _ h
  apply eq_of_pairings hw0 hw1
  intro z
  rw [← plus_right hw0 hw1 t ht z, shift_pairing, shift_pairing, h]

theorem plus_left (d : Domain) : plusDomain hw0 hw1 t ht (P d) = d :=
  plus_injective hw0 hw1 t ht (plus_right hw0 hw1 t ht (P d))

theorem minus_left (d : Domain) : minusDomain hw0 hw1 t ht (M d) = d :=
  minus_injective hw0 hw1 t ht (minus_right hw0 hw1 t ht (M d))

/-- Literal Cayley map (I-i*t*A)(I+i*t*A)^(-1) of the original derivative. -/
def cayley (x : H) : H := M (plusDomain hw0 hw1 t ht x)

/-- The opposite shift constructs its actual inverse on every physical class. -/
def inverse (x : H) : H := P (minusDomain hw0 hw1 t ht x)

theorem inverse_right (x : H) : cayley hw0 hw1 t ht (inverse hw0 hw1 t ht x) = x := by
  unfold cayley inverse
  rw [plus_left, minus_right]

theorem inverse_left (x : H) : inverse hw0 hw1 t ht (cayley hw0 hw1 t ht x) = x := by
  unfold cayley inverse
  rw [minus_left, plus_right]

/-- Unitarity is the FULL complex physical pairing, not just a norm estimate. -/
theorem pairing_preserved (x y : H) : I (cayley hw0 hw1 t ht x) (cayley hw0 hw1 t ht y) = I x y := by
  unfold cayley
  rw [← shift_pairing, plus_right, plus_right]

theorem pairing_inverse (x z : H) : I (cayley hw0 hw1 t ht x) z = I x (inverse hw0 hw1 t ht z) := by
  calc
    I (cayley hw0 hw1 t ht x) z = I (cayley hw0 hw1 t ht x)
        (cayley hw0 hw1 t ht (inverse hw0 hw1 t ht z)) :=
      congrArg (fun y => I (cayley hw0 hw1 t ht x) y) (inverse_right hw0 hw1 t ht z).symm
    _ = I x (inverse hw0 hw1 t ht z) := pairing_preserved hw0 hw1 t ht x (inverse hw0 hw1 t ht z)

/-- Original addition is preserved, using only actual surjective pairing tests. -/
theorem cayley_add (x y : H) :
    cayley hw0 hw1 t ht (BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1 x y) =
      BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1 (cayley hw0 hw1 t ht x) (cayley hw0 hw1 t ht y) := by
  apply eq_of_pairings hw0 hw1
  intro z
  rw [pairing_inverse, inner_add_left, inner_add_left, pairing_inverse, pairing_inverse]

/-- Full constructive complex linearity retains BOTH scalar Cauchy witnesses. -/
theorem cayley_smul (s u : CReal) (cs : QCauchy s.approx) (cu : QCauchy u.approx) (x : H) :
    cayley hw0 hw1 t ht (BF4WilsonAllNomeComplexBondOSTime.smul hw0 hw1 s u cs cu x) =
      BF4WilsonAllNomeComplexBondOSTime.smul hw0 hw1 s u cs cu (cayley hw0 hw1 t ht x) := by
  apply eq_of_pairings hw0 hw1
  intro z
  rw [pairing_inverse, inner_smul_left, inner_smul_left, pairing_inverse]

#print axioms shift_pairing
#print axioms plus_injective
#print axioms minus_injective
#print axioms plus_left
#print axioms minus_left
#print axioms cayley
#print axioms inverse
#print axioms inverse_right
#print axioms inverse_left
#print axioms pairing_preserved
#print axioms pairing_inverse
#print axioms cayley_add
#print axioms cayley_smul

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayley
