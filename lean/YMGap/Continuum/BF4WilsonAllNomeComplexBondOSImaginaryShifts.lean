/-
# Constructed imaginary-shift preimages on the ORIGINAL complex bond carrier

Let R=(I+A)^(-1), J=I-R and D=R^2+J^2. The actual denominator inverse
constructs domain preimages for input plus/minus i output on EVERY complex physical
bond class. All domain components are the original positive-resolvent domain
classes; no new analytic field or quotient representative is selected.

These are fixed-nome/width operator constructions in original lattice-time
units, not physical mass calibration, continuum survival or QFT closure.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSResolventDenominator
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSImaginaryShifts

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (BondCompletion bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_inner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_sub)
open YMGap.Continuum.BF4WilsonAllNomeBondOSResolvent
  (resolvent resolventDomain input_resolventDomain)
open YMGap.Continuum.BF4WilsonAllNomeBondOSResolventReflection
  (resolvent_add resolvent_sub graph_sum)
open YMGap.Continuum.BF4WilsonAllNomeBondOSResolventDenominator
  (denominator denominator_resolvent_square_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion (ComplexBondCompletion)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "RH" => BondCompletion hw0 hw1 (width := width)
local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "Domain" => BF4WilsonAllNomeComplexBondOSDerivative.Domain hw0 hw1 (width := width)
local notation "R" => resolvent hw0 hw1 1 (by decide)
local notation "Dom" => resolventDomain hw0 hw1 1 (by decide)
local notation "Add" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "Sub" => BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
local notation "In" => BF4WilsonAllNomeBondOSDerivative.input hw0 hw1
local notation "Out" => BF4WilsonAllNomeBondOSDerivative.output hw0 hw1
local notation "V" => bondValue hw0 hw1
local notation "BV" => completedInner hw0 hw1
local notation "Inv" => BF4WilsonAllNomeBondOSResolventDenominator.inverse hw0 hw1

/-- The complement of the actual positive resolvent, not a time step. -/
def complement (x : RH) : RH := Sub x (R x)

local notation "J" => complement hw0 hw1

private theorem add_sub_cancel (a b c : RH) : Sub (Add a b) (Sub b c) = Add a c := by
  apply bondValue_injective hw0 hw1
  apply completed_eq_of_pairings hw0 hw1
  intro z
  simp only [bondValue_add, bondValue_sub, completedInner_add_left, completedInner_sub_left]
  refine Quotient.inductionOn₃ (BV (V a) z) (BV (V b) z) (BV (V c) z) ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 1) (.neg (.var 2)))))
      (.add (.var 0) (.var 2)) (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

private theorem sub_add_cancel (a b c : RH) : Add (Sub a b) (Add b c) = Add a c := by
  apply bondValue_injective hw0 hw1
  apply completed_eq_of_pairings hw0 hw1
  intro z
  simp only [bondValue_add, bondValue_sub, completedInner_add_left, completedInner_sub_left]
  refine Quotient.inductionOn₃ (BV (V a) z) (BV (V b) z) (BV (V c) z) ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.var 2)))
      (.add (.var 0) (.var 2)) (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

/-- Both terms of the original derivative graph are pinned to R and I-R. -/
theorem output_resolventDomain (x : RH) : Out (Dom x) = J x := by
  apply bondValue_injective hw0 hw1
  apply completed_eq_of_pairings hw0 hw1
  intro z
  have hx := congrArg (fun a => BV (V a) z) (graph_sum hw0 hw1 x)
  dsimp only at hx
  rw [bondValue_add, completedInner_add_left] at hx
  unfold complement
  rw [bondValue_sub, completedInner_sub_left, ← hx]
  refine Quotient.inductionOn₂ (BV (V (R x)) z) (BV (V (Out (Dom x))) z) ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.var 1)
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (by decide)
      (fun | 0 => A.approx n | _ => B.approx n)))

theorem complement_add (x y : RH) : J (Add x y) = Add (J x) (J y) := by
  unfold complement
  rw [resolvent_add]
  apply bondValue_injective hw0 hw1
  apply completed_eq_of_pairings hw0 hw1
  intro z
  simp only [bondValue_add, bondValue_sub, completedInner_add_left, completedInner_sub_left]
  refine Quotient.inductionOn₃ (BV (V x) z) (BV (V y) z) (BV (V (R x)) z) ?_
  intro A B C
  refine Quotient.inductionOn (BV (V (R y)) z) ?_
  intro E
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
      (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
      (by decide) (fun | 0 => A.approx n | 1 => B.approx n | 2 => C.approx n | _ => E.approx n)))

theorem complement_sub (x y : RH) : J (Sub x y) = Sub (J x) (J y) := by
  unfold complement
  rw [resolvent_sub]
  apply bondValue_injective hw0 hw1
  apply completed_eq_of_pairings hw0 hw1
  intro z
  simp only [bondValue_sub, completedInner_sub_left]
  refine Quotient.inductionOn₃ (BV (V x) z) (BV (V y) z) (BV (V (R x)) z) ?_
  intro A B C
  refine Quotient.inductionOn (BV (V (R y)) z) ?_
  intro E
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.neg (.var 3)))))
      (.add (.add (.var 0) (.neg (.var 2))) (.neg (.add (.var 1) (.neg (.var 3)))))
      (by decide) (fun | 0 => A.approx n | 1 => B.approx n | 2 => C.approx n | _ => E.approx n)))

theorem resolvent_complement (x : RH) : R (J x) = J (R x) := by
  unfold complement
  exact resolvent_sub hw0 hw1 x (R x)

/-- input+i output, with i(v1,v2)=(-v2,v1) on the existing complex carrier. -/
def plus (d : Domain) : H := (Sub (In d.1) (Out d.2), Add (In d.2) (Out d.1))

/-- input-i output on the same original physical derivative graph. -/
def minus (d : Domain) : H := (Add (In d.1) (Out d.2), Sub (In d.2) (Out d.1))

/-- The denominator inverse supplies actual original domain witnesses. -/
def plusDomain (x : H) : Domain :=
  (Dom (Add (R (Inv x.1)) (J (Inv x.2))),
   Dom (Sub (R (Inv x.2)) (J (Inv x.1))))

def minusDomain (x : H) : Domain :=
  (Dom (Sub (R (Inv x.1)) (J (Inv x.2))),
   Dom (Add (R (Inv x.2)) (J (Inv x.1))))

/-- Every complex physical class has a computed plus-shift graph preimage. -/
theorem plus_right (x : H) : plus hw0 hw1 (plusDomain hw0 hw1 x) = x := by
  apply Prod.ext
  · change Sub (In (Dom (Add (R (Inv x.1)) (J (Inv x.2)))))
      (Out (Dom (Sub (R (Inv x.2)) (J (Inv x.1))))) = x.1
    rw [input_resolventDomain, output_resolventDomain, resolvent_add, complement_sub,
      ← resolvent_complement, add_sub_cancel]
    change Add (R (R (Inv x.1))) (J (J (Inv x.1))) = x.1
    exact (denominator_resolvent_square_pin hw0 hw1 (Inv x.1)).symm.trans
      (BF4WilsonAllNomeBondOSResolventDenominator.inverse_right hw0 hw1 x.1)
  · change Add (In (Dom (Sub (R (Inv x.2)) (J (Inv x.1)))))
      (Out (Dom (Add (R (Inv x.1)) (J (Inv x.2))))) = x.2
    rw [input_resolventDomain, output_resolventDomain, resolvent_sub, complement_add,
      ← resolvent_complement, sub_add_cancel]
    change Add (R (R (Inv x.2))) (J (J (Inv x.2))) = x.2
    exact (denominator_resolvent_square_pin hw0 hw1 (Inv x.2)).symm.trans
      (BF4WilsonAllNomeBondOSResolventDenominator.inverse_right hw0 hw1 x.2)

/-- Every complex physical class also has the opposite imaginary-shift preimage. -/
theorem minus_right (x : H) : minus hw0 hw1 (minusDomain hw0 hw1 x) = x := by
  apply Prod.ext
  · change Add (In (Dom (Sub (R (Inv x.1)) (J (Inv x.2)))))
      (Out (Dom (Add (R (Inv x.2)) (J (Inv x.1))))) = x.1
    rw [input_resolventDomain, output_resolventDomain, resolvent_sub, complement_add,
      ← resolvent_complement, sub_add_cancel]
    change Add (R (R (Inv x.1))) (J (J (Inv x.1))) = x.1
    exact (denominator_resolvent_square_pin hw0 hw1 (Inv x.1)).symm.trans
      (BF4WilsonAllNomeBondOSResolventDenominator.inverse_right hw0 hw1 x.1)
  · change Sub (In (Dom (Add (R (Inv x.2)) (J (Inv x.1)))))
      (Out (Dom (Sub (R (Inv x.1)) (J (Inv x.2))))) = x.2
    rw [input_resolventDomain, output_resolventDomain, resolvent_add, complement_sub,
      ← resolvent_complement, add_sub_cancel]
    change Add (R (R (Inv x.2))) (J (J (Inv x.2))) = x.2
    exact (denominator_resolvent_square_pin hw0 hw1 (Inv x.2)).symm.trans
      (BF4WilsonAllNomeBondOSResolventDenominator.inverse_right hw0 hw1 x.2)

#print axioms complement
#print axioms output_resolventDomain
#print axioms complement_add
#print axioms complement_sub
#print axioms resolvent_complement
#print axioms plus
#print axioms minus
#print axioms plusDomain
#print axioms minusDomain
#print axioms plus_right
#print axioms minus_right

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSImaginaryShifts
