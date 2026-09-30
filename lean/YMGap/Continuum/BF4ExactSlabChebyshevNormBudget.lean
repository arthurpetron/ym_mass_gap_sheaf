/-
# Keep the normalization budget of the ORIGINAL Chebyshev state

Reverse energy >= 0 is sufficient for the old 1/T_n^2 covariance factor,
but is not necessary for a weaker strict factor eta. The exact signed test
here retains c*margin + (eta*T_n^2-1)*||x||^2. A negative reverse margin
is permitted; the action, auxiliary order, and normalization are unchanged.

This constructs a finite rational test, not a successful uniform family of
tests. No strict factor on a scaling trajectory or OS/physical gap is claimed.
-/

import YMGap.Continuum.BF4ExactSlabChebyshevFiniteTest
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4ExactSlabChebyshevNormBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSInnerRationalBracket
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFullActionScalar
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabSweepChebyshev
open YMGap.Continuum.BF4ExactSlabChebyshevPairing
open YMGap.Continuum.BF4ExactSlabChebyshevRescale
open YMGap.Continuum.BF4ExactSlabChebyshevFiniteTest

local infix:50 " ≈ " => Q'.eqv

private theorem norm_smul (S : SmulGNSData) (q : Q')
    (x : GNSCompletionSpace S.toGNSData) :
    normSq (S.cSmul q x) = RCscale (q*q) (normSq x) := by
  unfold normSq
  rw [S.cinnerCompl_cSmul_left, S.cinnerCompl_cSmul_right, RCscale_RCscale]

private theorem budget_rearrange (a b m : RC) (c d : Q')
    (h : RCadd a (RCscale c m) = b) :
    RCadd (RCscale c m) (RCscale (d + -(1 : Q')) b) =
      RCsub (RCscale d b) a := by
  rw [← h]
  refine Quotient.inductionOn₂ a m ?_
  intro A M
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 3))
        (.mul (.add (.var 1) (.neg (.const 1)))
          (.add (.var 2) (.mul (.var 0) (.var 3)))))
      (.add (.mul (.var 1) (.add (.var 2) (.mul (.var 0) (.var 3))))
        (.neg (.var 2))) (by decide)
      (fun | 0 => c | 1 => d | 2 => A.approx n | _ => M.approx n)))

private theorem le_of_deficit_nonnegative (a b : RC)
    (h : RCnonneg (RCsub b a)) : RCle a b := by
  have he : RCadd (RCsub b a) a = b := by
    refine Quotient.inductionOn₂ b a ?_
    intro B A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.sub_add_cancel_eqv (B.approx n) (A.approx n)))
  have hz : RCadd RCzero a = a := by
    refine Quotient.inductionOn a ?_
    intro A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))
  have hh := RCadd_le_add h (RCle_refl a)
  rwa [hz, he] at hh

private theorem reciprocal_budget (t : Q') (ht : (0 : Q') < t) (eta : Q') :
    (Q'.recipPos t ht * Q'.recipPos t ht) * (eta*t*t) ≈ eta := by
  let s := Q'.recipPos t ht
  have hts : t*s ≈ 1 := Q'.mul_recipPos_eqv t ht
  have hgroup : (s*s)*(eta*t*t) ≈ ((t*s)*(t*s))*eta :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0))
        (.mul (.mul (.var 1) (.var 2)) (.var 2)))
      (.mul (.mul (.mul (.var 2) (.var 0)) (.mul (.var 2) (.var 0))) (.var 1))
      (by decide) (fun | 0 => s | 1 => eta | _ => t)
  have hsquare : (t*s)*(t*s) ≈ (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hts)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hts) (by decide))
  exact Q'.eqv_trans _ _ _ hgroup
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hsquare)
      (Q'.one_mul_eqv eta))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "S" => fullScalarData hw0 hw1 K extent hK

/-- Actual signed norm budget. eta is a SQUARED-norm/covariance factor.
No sign is imposed on the reverse margin or on its allowed threshold. -/
def budget (c : Q') (X : CauchyGNS F) (n : Nat) (eta : Q') : CReal :=
  let t := Cheb.T n (c + -(1 : Q'))
  CReal.add (CReal.mul (CReal.ofQ' c)
    (BF4ExactSlabChebyshevFiniteTest.margin hw0 hw1 K extent hK c X n))
    (CReal.mul (CReal.ofQ' (eta*t*t + -(1 : Q'))) ((F).cinnerRep X X))

/-- The existing representative moduli compute the signed budget's cutoff. -/
def budgetRegularity (c : Q') (X : CauchyGNS F) (n : Nat) (eta : Q') :
    InnerRegularity (budget hw0 hw1 K extent hK c X n eta) :=
  let t := Cheb.T n (c + -(1 : Q'))
  ((marginRegularity hw0 hw1 K extent hK c X n).scaleLeftSigned c).add
    ((innerRegularity F X X).scaleLeftSigned (eta*t*t + -(1 : Q')))

def budgetValue (c : Q') (X : CauchyGNS F) (n : Nat) (eta epsilon : Q') : Q' :=
  bracketValue (budget hw0 hw1 K extent hK c X n eta)
    (budgetRegularity hw0 hw1 K extent hK c X n eta) epsilon

/-- Exact SAME-state deficit, not a newly assumed estimate. In particular
the positive normalization allowance is not silently thrown away. -/
theorem budget_pin (c : Q') (X : CauchyGNS F) (n : Nat) (eta : Q') :
    let x := Quotient.mk (cauchySetoid F) X
    let t := Cheb.T n (c + -(1 : Q'))
    Quotient.mk crealSetoid (budget hw0 hw1 K extent hK c X n eta) =
      RCsub (RCscale (eta*t*t) (normSq x))
        (normSq (coupled hw0 hw1 K extent hK c x n).1) := by
  let x := Quotient.mk (cauchySetoid F) X
  let t := Cheb.T n (c + -(1 : Q'))
  change RCadd
    (RCscale c (Quotient.mk crealSetoid
      (BF4ExactSlabChebyshevFiniteTest.margin hw0 hw1 K extent hK c X n)))
    (RCscale (eta*t*t + -(1 : Q')) (normSq x)) = _
  rw [margin_pin]
  exact budget_rearrange _ _ _ c (eta*t*t)
    (coupled_norm_add_margin hw0 hw1 K extent hK c x n)

/-- A computed rational lower bracket certifies the NORMALIZED first-state
bound. The old nonnegative reverse-margin test is not required. -/
theorem normalizedFirst_norm_of_finite_budget (c : Q') (X : CauchyGNS F)
    (n : Nat) (ht : (0 : Q') < Cheb.T n (c + -(1 : Q')))
    (eta epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (htest : epsilon ≤ budgetValue hw0 hw1 K extent hK c X n eta epsilon) :
    let x := Quotient.mk (cauchySetoid F) X
    RCle (normSq (normalizedFirst hw0 hw1 K extent hK c n ht x))
      (RCscale eta (normSq x)) := by
  let x := Quotient.mk (cauchySetoid F) X
  let t := Cheb.T n (c + -(1 : Q'))
  let s := Q'.recipPos t ht
  have hl := bracket_lower (budget hw0 hw1 K extent hK c X n eta)
    (budgetRegularity hw0 hw1 K extent hK c X n eta) epsilon hepsilon
  have hq : (0 : Q') ≤ budgetValue hw0 hw1 K extent hK c X n eta epsilon + -epsilon :=
    Q'.sub_nonneg_of_le htest
  have hz : leEv (CReal.ofQ' 0)
      (CReal.ofQ' (budgetValue hw0 hw1 K extent hK c X n eta epsilon + -epsilon)) :=
    leEv_ofQ'_of_approx_ge (fun _ => hq)
  have hb : RCnonneg (Quotient.mk crealSetoid (budget hw0 hw1 K extent hK c X n eta)) :=
    leEv_trans hz hl
  rw [budget_pin] at hb
  have hn := le_of_deficit_nonnegative _ _ hb
  have hs : (0 : Q') ≤ s*s := SumOfSquares.q_mul_self_nonneg s
  have hscaled := RCscale_mono hs hn
  rw [RCscale_RCscale,
    RCSignedPairBudget.scale_congr (reciprocal_budget t ht eta)] at hscaled
  have hnorm : normSq (normalizedFirst hw0 hw1 K extent hK c n ht x) =
      RCscale (s*s) (normSq (coupled hw0 hw1 K extent hK c x n).1) :=
    norm_smul S s _
  change RCle (normSq (normalizedFirst hw0 hw1 K extent hK c n ht x))
    (RCscale eta (normSq x))
  rw [hnorm]
  exact hscaled

#print axioms budget
#print axioms budgetRegularity
#print axioms budgetValue
#print axioms budget_pin
#print axioms normalizedFirst_norm_of_finite_budget

end YMGap.Continuum.BF4ExactSlabChebyshevNormBudget
