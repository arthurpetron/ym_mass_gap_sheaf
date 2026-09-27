/-
# A finite rational test for the actual auxiliary reverse energy

The input is an explicit Cauchy representative, not an arbitrary completion
class with a chosen representative. All approximation indices are computed
from the inherited Cauchy moduli. A successful finite rational comparison
implies the SAME completed reverse-energy inequality. No claim is made that
the comparison succeeds, terminates efficiently, or is uniform in parameters.
-/

import YMGap.Continuum.BF4ExactSlabChebyshevRepresentative
import YMGap.Continuum.GNSInnerRationalBracket
import YMGap.Continuum.BF4ExactSlabChebyshevRescale

namespace YMGap.Continuum.BF4ExactSlabChebyshevFiniteTest

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSInnerRationalBracket
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabSweepChebyshev
open YMGap.Continuum.BF4ExactSlabChebyshevRepresentative

private theorem le_of_sub_nonnegative (a b : RC)
    (h : RCnonneg (RCsub b a)) : RCle a b := by
  have hz : RCadd RCzero a = a := by
    refine Quotient.inductionOn a ?_
    intro A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))
  have hc : RCadd (RCsub b a) a = b := by
    refine Quotient.inductionOn₂ b a ?_
    intro B A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.sub_add_cancel_eqv (B.approx n) (A.approx n)))
  have hb := RCadd_le_add h (RCle_refl a)
  rw [hz, hc] at hb
  exact hb

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK

private def forwardRep (c : Q') (X : CauchyGNS F) (n : Nat) : CauchyGNS F :=
  sweepRep hw0 hw1 K extent hK (schedule extent)
    (coupledRep hw0 hw1 K extent hK c X n).2

private def balancedRep (c : Q') (X : CauchyGNS F) (n : Nat) : CauchyGNS F :=
  sweepRep hw0 hw1 K extent hK (schedule extent).reverse
    (forwardRep hw0 hw1 K extent hK c X n)

/-- Explicit representative of `2*||S u||²-c*||S* S u||²` for the actual
second coupled component at step n. -/
def margin (c : Q') (X : CauchyGNS F) (n : Nat) : CReal :=
  let Y := forwardRep hw0 hw1 K extent hK c X n
  let Z := balancedRep hw0 hw1 K extent hK c X n
  CReal.sub (CReal.mul (CReal.ofQ' 2) ((F).cinnerRep Y Y))
    (CReal.mul (CReal.ofQ' c) ((F).cinnerRep Z Z))

/-- Type-level modulus built from the SAME representative inner products. -/
def marginRegularity (c : Q') (X : CauchyGNS F) (n : Nat) :
    InnerRegularity (margin hw0 hw1 K extent hK c X n) :=
  let Y := forwardRep hw0 hw1 K extent hK c X n
  let Z := balancedRep hw0 hw1 K extent hK c X n
  ((innerRegularity F Y Y).scaleLeftSigned 2).add
    (((innerRegularity F Z Z).scaleLeftSigned c).neg)

/-- The finite rational value at the computed error-controlled index. -/
def marginValue (c : Q') (X : CauchyGNS F) (n : Nat) (epsilon : Q') : Q' :=
  bracketValue (margin hw0 hw1 K extent hK c X n)
    (marginRegularity hw0 hw1 K extent hK c X n) epsilon

theorem margin_pin (c : Q') (X : CauchyGNS F) (n : Nat) :
    let x := Quotient.mk (cauchySetoid F) X
    let u := (coupled hw0 hw1 K extent hK c x n).2
    Quotient.mk crealSetoid (margin hw0 hw1 K extent hK c X n) =
      RCsub (RCscale 2 (normSq ((P).sweep (schedule extent) u)))
        (RCscale c (normSq ((P).balanced (schedule extent) u))) := by
  have hu := (coupledRep_pin hw0 hw1 K extent hK c X n).2
  have hy := sweepRep_pin hw0 hw1 K extent hK (schedule extent)
    (coupledRep hw0 hw1 K extent hK c X n).2
  rw [hu] at hy
  have hz : Quotient.mk (cauchySetoid F)
      (balancedRep hw0 hw1 K extent hK c X n) =
      (P).sweep (schedule extent).reverse
        (Quotient.mk (cauchySetoid F) (forwardRep hw0 hw1 K extent hK c X n)) :=
    sweepRep_pin hw0 hw1 K extent hK (schedule extent).reverse
      (forwardRep hw0 hw1 K extent hK c X n)
  have hy' : Quotient.mk (cauchySetoid F)
      (forwardRep hw0 hw1 K extent hK c X n) =
      (P).sweep (schedule extent)
        (coupled hw0 hw1 K extent hK c (Quotient.mk (cauchySetoid F) X) n).2 := hy
  rw [hy'] at hz
  change RCsub
      (RCscale 2 (normSq (Quotient.mk (cauchySetoid F)
        (forwardRep hw0 hw1 K extent hK c X n))))
      (RCscale c (normSq (Quotient.mk (cauchySetoid F)
        (balancedRep hw0 hw1 K extent hK c X n)))) = _
  rw [hy', hz]
  rfl

/-- A positive rational tolerance and its computed lower bracket certify
the original completed reverse energy. There is no assumed real inequality
or assumed modulus in this test. -/
theorem reverse_energy_of_finite_test (c : Q') (X : CauchyGNS F) (n : Nat)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (htest : epsilon ≤ marginValue hw0 hw1 K extent hK c X n epsilon) :
    let x := Quotient.mk (cauchySetoid F) X
    let u := (coupled hw0 hw1 K extent hK c x n).2
    RCle (RCscale c (normSq ((P).balanced (schedule extent) u)))
      (RCscale 2 (normSq ((P).sweep (schedule extent) u))) := by
  have hl := bracket_lower (margin hw0 hw1 K extent hK c X n)
    (marginRegularity hw0 hw1 K extent hK c X n) epsilon hepsilon
  have hq : (0 : Q') ≤ marginValue hw0 hw1 K extent hK c X n epsilon + -epsilon :=
    Q'.sub_nonneg_of_le htest
  have hzero : leEv (CReal.ofQ' 0)
      (CReal.ofQ' (marginValue hw0 hw1 K extent hK c X n epsilon + -epsilon)) :=
    leEv_ofQ'_of_approx_ge (fun _ => hq)
  have hm : RCnonneg (Quotient.mk crealSetoid (margin hw0 hw1 K extent hK c X n)) :=
    leEv_trans hzero hl
  rw [margin_pin hw0 hw1 K extent hK c X n] at hm
  exact le_of_sub_nonnegative _ _ hm

#print axioms margin
#print axioms marginRegularity
#print axioms marginValue
#print axioms margin_pin
#print axioms reverse_energy_of_finite_test

end YMGap.Continuum.BF4ExactSlabChebyshevFiniteTest
