/-
# Exact rational optimization of an original conditional-kernel test

For the actual signed pairing A=B(f,t) and cost C=B(t,t), construct A/C
when C>0 and zero otherwise. Rational comparison is decidable. In the
null branch Cauchy--Schwarz proves A=0, so the returned value is maximal
among scalar multiples of this test in BOTH branches. The result bounds
the original completed residual, not a surrogate form. Useful uniform
control of the summed gains remains an open analytic problem.
-/

import YMGap.Continuum.BF4ExactSlabStarNormalizedPolynomialTest
import YMGap.Continuum.RationalDualTestOptimization

namespace YMGap.Continuum.BF4ExactSlabStarOptimizedPolynomialTest

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabStarPolynomialResidual
open YMGap.Continuum.BF4ExactSlabStarPolynomialResidualScaling
open YMGap.Continuum.BF4ExactSlabStarNormalizedPolynomialTest
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem rat_mono {a b : Q'} (h : a ≤ b) :
    RCle (Quotient.mk crealSetoid (ofQ' a)) (Quotient.mk crealSetoid (ofQ' b)) :=
  leEv_ofQ'_of_approx_ge (fun _ => h)

private theorem nonnegative_not_positive_zero (C : Q')
    (hn : (0 : Q') ≤ C) (hp : ¬ (0 : Q') < C) : C ≈ 0 := by
  change (0 : Int) * (C.den : Int) ≤ C.num * 1 at hn
  change ¬ (0 : Int) * (C.den : Int) < C.num * 1 at hp
  change C.num * 1 = (0 : Int) * (C.den : Int)
  omega

private theorem value_zero_coefficient (A C : Q') :
    RationalDualTestNormalization.value 0 A C ≈ 0 :=
  poly_identity_of_normal_eq
    (.add (.add (.mul (.const 0) (.var 0)) (.mul (.const 0) (.var 0)))
      (.neg (.mul (.mul (.const 0) (.const 0)) (.var 1))))
    (.const 0) (by decide) (fun | 0 => A | _ => C)

private theorem value_null (a A C : Q') (hA : A ≈ 0) (hC : C ≈ 0) :
    RationalDualTestNormalization.value a A C ≈ 0 := by
  have hm : a*A ≈ 0 := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ hA) (Q'.mul_zero_eqv a)
  have hc : (a*a)*C ≈ 0 := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (a*a) _ _ hC) (Q'.mul_zero_eqv (a*a))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' hm hm) (Q'.neg_eqv_congr _ _ hc))
    (by decide : ((0 : Q') + 0) + -0 ≈ 0)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (i : PhysicalLink extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "A" => pairValue hw0 hw1 K extent hK i
local notation "C" => normCost hw0 hw1 K extent hK i

/-- Null cost forces the signed pairing to vanish on the original form. -/
theorem pairValue_null (p f : (F).V) (hC : ¬ (0 : Q') < C p) : A p f ≈ 0 :=
  (F).radical_form_zero_right f (polynomialResidual hw0 hw1 K extent hK i p)
    (nonnegative_not_positive_zero (C p)
      (normCost_nonnegative hw0 hw1 K extent hK i p) hC)

/-- Total computable scalar choice, including the null-cost branch. -/
def optimizedCoefficient (p f : (F).V) : Q' :=
  if h : (0 : Q') < C p then RationalDualTestOptimization.coefficient (A p f) (C p) h
  else 0

def optimizedGain (p f : (F).V) : Q' :=
  if h : (0 : Q') < C p then RationalDualTestOptimization.gain (A p f) (C p) h
  else 0

def optimizedSeed (p f : (F).V) : (F).V :=
  (F).smul (optimizedCoefficient hw0 hw1 K extent hK i p f) p

theorem optimized_value_identity (p f : (F).V) :
    dualValue hw0 hw1 K extent hK i (optimizedSeed hw0 hw1 K extent hK i p f) f ≈
      optimizedGain hw0 hw1 K extent hK i p f := by
  refine Q'.eqv_trans _ _ _
    (dualValue_smul hw0 hw1 K extent hK i
      (optimizedCoefficient hw0 hw1 K extent hK i p f) p f) ?_
  change RationalDualTestNormalization.value
    (optimizedCoefficient hw0 hw1 K extent hK i p f) (A p f) (C p) ≈ _
  by_cases h : (0 : Q') < C p
  · simp only [optimizedCoefficient, optimizedGain, dif_pos h]
    exact RationalDualTestOptimization.value_identity _ _ h
  · simp only [optimizedCoefficient, optimizedGain, dif_neg h]
    exact value_zero_coefficient _ _

theorem optimizedGain_nonnegative (p f : (F).V) :
    (0 : Q') ≤ optimizedGain hw0 hw1 K extent hK i p f := by
  by_cases h : (0 : Q') < C p
  · simp only [optimizedGain, dif_pos h]
    exact RationalDualTestOptimization.gain_nonnegative _ _ h
  · simp only [optimizedGain, dif_neg h]
    decide

/-- Maximality over every rational scalar multiple of the supplied test. -/
theorem scaled_value_le_optimizedGain (p f : (F).V) (a : Q') :
    dualValue hw0 hw1 K extent hK i ((F).smul a p) f ≤
      optimizedGain hw0 hw1 K extent hK i p f := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (dualValue_smul hw0 hw1 K extent hK i a p f)) ?_
  change RationalDualTestNormalization.value a (A p f) (C p) ≤ _
  by_cases h : (0 : Q') < C p
  · simp only [optimizedGain, dif_pos h]
    exact RationalDualTestOptimization.value_le_gain _ _ a h
  · simp only [optimizedGain, dif_neg h]
    exact Q'.le_of_eqv (value_null a (A p f) (C p)
      (pairValue_null hw0 hw1 K extent hK i p f h)
      (nonnegative_not_positive_zero (C p)
        (normCost_nonnegative hw0 hw1 K extent hK i p) h))

theorem guaranteedGain_le_optimizedGain (p f : (F).V) :
    guaranteedGain hw0 hw1 K extent hK i p f ≤
      optimizedGain hw0 hw1 K extent hK i p f :=
  Q'.le_trans' _ _ _
    (guaranteedGain_le_value hw0 hw1 K extent hK i p f)
    (scaled_value_le_optimizedGain hw0 hw1 K extent hK i p f
      (testCoefficient hw0 hw1 K extent hK i p f))

/-- The exact computed maximum is a lower bound on the SAME completed residual. -/
theorem optimizedGain_lower (p f : (F).V) :
    RCle (Quotient.mk crealSetoid (ofQ' (optimizedGain hw0 hw1 K extent hK i p f)))
      (normSq ((P).residual i (embedV F f))) :=
  RCle_trans
    (rat_mono (Q'.ge_of_eqv
      (optimized_value_identity hw0 hw1 K extent hK i p f)))
    (dualValue_lower hw0 hw1 K extent hK i (optimizedSeed hw0 hw1 K extent hK i p f) f)

#print axioms pairValue_null
#print axioms optimizedCoefficient
#print axioms optimizedSeed
#print axioms optimized_value_identity
#print axioms optimizedGain_nonnegative
#print axioms scaled_value_le_optimizedGain
#print axioms guaranteedGain_le_optimizedGain
#print axioms optimizedGain_lower

end YMGap.Continuum.BF4ExactSlabStarOptimizedPolynomialTest
