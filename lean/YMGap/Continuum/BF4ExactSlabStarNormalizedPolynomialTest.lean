/-
# Actual-cost normalization of original polynomial conditional tests

Given original polynomials p,f, compute t=D*p-J(Np), A=B(f,t), C=B(t,t).
The explicit seed a*p with a=A/(1+C) is an original supported polynomial.
Its exact dual value dominates A^2/(1+C), which bounds the ACTUAL completed
conditional residual energy of f. This uses actual signed pairings and
costs, not a coarse normalizer floor/cap. No global lower estimate follows
without finding tests with suitably controlled gains.
-/

import YMGap.Continuum.BF4ExactSlabStarPolynomialResidualScaling
import YMGap.Continuum.RationalDualTestNormalization

namespace YMGap.Continuum.BF4ExactSlabStarNormalizedPolynomialTest

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

local infix:50 " ≈ " => Q'.eqv

private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

private theorem rat_mono {a b : Q'} (h : a ≤ b) : RCle (rat a) (rat b) :=
  leEv_ofQ'_of_approx_ge (fun _ => h)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (i : PhysicalLink extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "t" p => polynomialResidual hw0 hw1 K extent hK i p

def pairValue (p f : (F).V) : Q' := (F).B f (t p)

def normCost (p : (F).V) : Q' := (F).B (t p) (t p)

def testCoefficient (p f : (F).V) : Q' :=
  RationalDualTestNormalization.coefficient
    (pairValue hw0 hw1 K extent hK i p f) (normCost hw0 hw1 K extent hK i p)

/-- A constructed original supported polynomial, not a completed surrogate. -/
def testSeed (p f : (F).V) : (F).V :=
  (F).smul (testCoefficient hw0 hw1 K extent hK i p f) p

def guaranteedGain (p f : (F).V) : Q' :=
  RationalDualTestNormalization.gain
    (pairValue hw0 hw1 K extent hK i p f) (normCost hw0 hw1 K extent hK i p)

theorem normCost_nonnegative (p : (F).V) :
    (0 : Q') ≤ normCost hw0 hw1 K extent hK i p := (F).self_nonneg (t p)

theorem normalized_value_identity (p f : (F).V) :
    dualValue hw0 hw1 K extent hK i (testSeed hw0 hw1 K extent hK i p f) f ≈
      guaranteedGain hw0 hw1 K extent hK i p f +
        testCoefficient hw0 hw1 K extent hK i p f * testCoefficient hw0 hw1 K extent hK i p f :=
  Q'.eqv_trans _ _ _
    (dualValue_smul hw0 hw1 K extent hK i (testCoefficient hw0 hw1 K extent hK i p f) p f)
    (RationalDualTestNormalization.value_identity _ _ (normCost_nonnegative hw0 hw1 K extent hK i p))

theorem guaranteedGain_nonnegative (p f : (F).V) :
    (0 : Q') ≤ guaranteedGain hw0 hw1 K extent hK i p f :=
  RationalDualTestNormalization.gain_nonnegative _ _

/-- Positive pairing is an explicit finite condition, not a proved global bound. -/
theorem guaranteedGain_positive (p f : (F).V)
    (hA : (0 : Q') < pairValue hw0 hw1 K extent hK i p f) :
    (0 : Q') < guaranteedGain hw0 hw1 K extent hK i p f :=
  RationalDualTestNormalization.gain_positive _ _ hA

theorem guaranteedGain_le_value (p f : (F).V) :
    guaranteedGain hw0 hw1 K extent hK i p f ≤
      dualValue hw0 hw1 K extent hK i (testSeed hw0 hw1 K extent hK i p f) f :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _
      (SumOfSquares.q_mul_self_nonneg (testCoefficient hw0 hw1 K extent hK i p f)))
    (Q'.ge_of_eqv (normalized_value_identity hw0 hw1 K extent hK i p f))

/-- The computed rational gain bounds the original completed residual energy. -/
theorem guaranteedGain_lower (p f : (F).V) :
    RCle (rat (guaranteedGain hw0 hw1 K extent hK i p f))
      (normSq ((P).residual i (embedV F f))) :=
  RCle_trans (rat_mono (guaranteedGain_le_value hw0 hw1 K extent hK i p f))
    (dualValue_lower hw0 hw1 K extent hK i (testSeed hw0 hw1 K extent hK i p f) f)

#print axioms testCoefficient
#print axioms testSeed
#print axioms normalized_value_identity
#print axioms guaranteedGain_nonnegative
#print axioms guaranteedGain_positive
#print axioms guaranteedGain_le_value
#print axioms guaranteedGain_lower

end YMGap.Continuum.BF4ExactSlabStarNormalizedPolynomialTest
