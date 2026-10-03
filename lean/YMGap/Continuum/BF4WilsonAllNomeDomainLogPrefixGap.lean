/-
# Computed finite logarithm coercivity on the ORIGINAL domain

The prefix is the literal finite rational sum of the actual kinetic margin
powers divided by their orders. Its form bound uses original defect moments
and the existing ordinary-log domain limit, on the same vacuum complement.
Already the two-term coefficient strictly improves the one-term margin.
No equality with a scalar real logarithm, uniform physical rate, changing
family estimate or canonical continuum OS identification is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeDomainLogForm
import YMGap.Continuum.BF4WilsonAllNomeDefectMomentGap

namespace YMGap.Continuum.BF4WilsonAllNomeDomainLogPrefixGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RCSignedPairBudget (scale_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixFraction mixFraction_positive)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defectPower)
open YMGap.Continuum.BF4WilsonAllNomeUnregularizedLogPartial (unregularizedLogPartial)
open YMGap.Continuum.BF4WilsonAllNomeDefectMomentGap (defect_moment_geometric_lower)
open YMGap.Continuum.BF4WilsonAllNomeDomainLogForm (domain_logPartial_form_le)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (DomainPoint)

private theorem scale_add (s t : Q') (a : RC) :
    RCscale (s+t) a = RCadd (RCscale s a) (RCscale t a) := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_mul_eqv s t (A.approx n)))

private theorem scale_zero (a : RC) : RCscale 0 a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (A.approx n)))

private theorem lt_add_of_positive (a b : Q') (hb : (0 : Q') < b) :
    a < a+b := by
  show a.num * ((a.den*b.den : Nat) : Int) <
    (a.num*(b.den : Int)+b.num*(a.den : Int))*(a.den : Int)
  have hcast : ((a.den*b.den : Nat) : Int) = (a.den : Int)*(b.den : Int) := by
    push_cast
    rfl
  rw [hcast]
  have ha : (0 : Int) < (a.den : Int) := by exact_mod_cast a.den_pos
  have hpos : (0 : Int) < b.num*(a.den : Int)*(a.den : Int) :=
    Int.mul_pos (Int.mul_pos (Q'.num_pos_of_pos hb) ha) ha
  have he : (a.num*(b.den : Int)+b.num*(a.den : Int))*(a.den : Int) =
      a.num*((a.den : Int)*(b.den : Int))+b.num*(a.den : Int)*(a.den : Int) := by
    rw [Int.add_mul, Int.mul_assoc a.num (b.den : Int) (a.den : Int),
      Int.mul_comm (b.den : Int) (a.den : Int)]
  rw [he]
  omega

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "U" => unregularizedLogPartial hw0 hw1
local notation "DP" => defectPower hw0 hw1
local notation "r" => mixFraction hw0 hw1 width

/-- Explicit finite sum of the original kinetic margin powers. -/
def prefixGap : Nat → Q'
  | 0 => 0
  | n+1 => prefixGap n + Q'.invSucc n * r^(n+1)

/-- Every computed prefix bounds its literal finite original logarithm form. -/
theorem finite_log_prefix_gap (x : V)
    (hx : B x (unitState hw0 hw1 width) = RCzero) (n : Nat) :
    RCle (RCscale (prefixGap hw0 hw1 (width := width) n) (B x x)) (B x (U n x)) := by
  induction n with
  | zero =>
      change RCle (RCscale 0 (B x x)) (B x (completedZero hw0 hw1 width))
      rw [scale_zero, completedInner_zero_right]
      exact RCle_refl _
  | succ n ih =>
      change RCle
        (RCscale (prefixGap hw0 hw1 (width := width) n + Q'.invSucc n*r^(n+1)) (B x x))
        (B x (completedAdd hw0 hw1 (U n x)
          (completedSmul hw0 hw1 (Q'.invSucc n) (DP (n+1) x))))
      rw [scale_add, completedInner_add_right, completedInner_smul_right]
      have hterm := RCscale_mono (Q'.invSucc_nonneg n)
        (defect_moment_geometric_lower hw0 hw1 x hx (n+1))
      rw [RCscale_RCscale] at hterm
      exact RCadd_le_add ih hterm

/-- The SAME domain output dominates every computed prefix on its input. -/
theorem domain_log_prefix_gap (p : DomainPoint hw0 hw1 (width := width))
    (hp : B p.input.val (unitState hw0 hw1 width) = RCzero) (n : Nat) :
    RCle (RCscale (prefixGap hw0 hw1 (width := width) n) (B p.input.val p.input.val))
      (B p.input.val p.output.val) :=
  RCle_trans (finite_log_prefix_gap hw0 hw1 p.input.val hp n)
    (domain_logPartial_form_le hw0 hw1 p n)

/-- The first two terms are exactly r + r^2/2, in rational semantic equality. -/
theorem prefixGap_two :
    Q'.eqv (prefixGap hw0 hw1 (width := width) 2) (r + HalfPow.half*(r*r)) := by
  change Q'.eqv ((0+1*(r*1))+HalfPow.half*(r*(r*1))) (r+HalfPow.half*(r*r))
  exact poly_identity_of_normal_eq
    (.add (.add (.const 0) (.mul (.const 1) (.mul (.var 0) (.const 1))))
      (.mul (.var 1) (.mul (.var 0) (.mul (.var 0) (.const 1)))))
    (.add (.var 0) (.mul (.var 1) (.mul (.var 0) (.var 0)))) (by decide)
    (fun | 0 => r | _ => HalfPow.half)

/-- Strict improvement is scalar and fixed-parameter; it is not a uniform gap. -/
theorem two_term_coefficient_strict : r < r + HalfPow.half*(r*r) := by
  exact lt_add_of_positive r (HalfPow.half*(r*r))
    (ExpNeg.half_mul_pos _ (Q'.mul_pos
      (mixFraction_positive hw0 hw1 width) (mixFraction_positive hw0 hw1 width)))

/-- Explicit two-term coercivity of the identified original domain action. -/
theorem domain_log_two_term_gap (p : DomainPoint hw0 hw1 (width := width))
    (hp : B p.input.val (unitState hw0 hw1 width) = RCzero) :
    RCle (RCscale (r+HalfPow.half*(r*r)) (B p.input.val p.input.val))
      (B p.input.val p.output.val) := by
  have h := domain_log_prefix_gap hw0 hw1 p hp 2
  rwa [scale_congr (prefixGap_two hw0 hw1 (width := width))] at h

#print axioms prefixGap
#print axioms finite_log_prefix_gap
#print axioms domain_log_prefix_gap
#print axioms prefixGap_two
#print axioms two_term_coefficient_strict
#print axioms domain_log_two_term_gap

end YMGap.Continuum.BF4WilsonAllNomeDomainLogPrefixGap
