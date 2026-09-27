/-
# Explicit decay of the original small-nome covariance factor

The fixed, volume-independent reverse-energy parameter gives a geometric
factor and a data-level degree modulus. These are fixed-nome estimates, not
a physical-spacing calibration or a thermodynamic-limit construction.
-/

import YMGap.Continuum.BF4ExactSlabSmallNomeChebyshevCovariance
import YMGap.Continuum.ChebyshevGeometricLower
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.EigenvalueShiftBound

namespace YMGap.Continuum.BF4ExactSlabSmallNomeCovarianceRate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4ExactSlabSmallNomeChebyshevCovariance

variable {w : Q'} (hd : heatRemainderBound w < 1)
  (hm : (0 : Q') < BF4ExactSlabConditionalGeneratorMargin.margin hd)

include hm in
theorem argument_gt_one : (1 : Q') < reverseParameter hd + -(1 : Q') := by
  have hc := reverseParameter_gt_two hd hm
  let c := reverseParameter hd
  change (2 : Int) * (c.den : Int) < c.num * (1 : Int) at hc
  change (1 : Int) * ((c.den * 1 : Nat) : Int) <
    (c.num * (1 : Int) + (-1 : Int) * (c.den : Int)) * (1 : Int)
  simp only [Nat.mul_one, Int.one_mul, Int.mul_one, Int.neg_one_mul] at *
  omega

/-- Geometric covariance rate, depending only on the fixed nome. -/
def rate : Q' :=
  ChebyshevGeometricLower.rho (reverseParameter hd + -(1 : Q'))
    (argument_gt_one hd hm)

theorem rate_positive : (0 : Q') < rate hd hm :=
  ChebyshevGeometricLower.rho_positive _ (argument_gt_one hd hm)

theorem rate_lt_one : rate hd hm < (1 : Q') :=
  ChebyshevGeometricLower.rho_lt_one _ (argument_gt_one hd hm)

theorem covarianceFactor_positive (n : Nat) :
    (0 : Q') < covarianceFactor hd hm n := Q'.recipPos_pos _ _

/-- Genuine decay: the old degree-dependent collar loss is absent. -/
theorem covarianceFactor_le_rate_pow (n : Nat) :
    covarianceFactor hd hm n ≤ (rate hd hm) ^ n := by
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv (covarianceFactor hd hm n)))
    (ChebyshevGeometricLower.reciprocal_T_le_pow _ (argument_gt_one hd hm) n)

theorem covarianceFactor_sq_le_rate_pow_sq (n : Nat) :
    covarianceFactor hd hm n * covarianceFactor hd hm n ≤
      (rate hd hm)^n * (rate hd hm)^n :=
  EigenvalueShiftBound.sq_mono (Q'.le_of_lt (covarianceFactor_positive hd hm n))
    (covarianceFactor_le_rate_pow hd hm n)

/-- Explicit degree threshold for the relative covariance coefficient.
No volume, cutoff, observable norm, or chosen quotient representative occurs. -/
def degreeModulus (epsilon : Q') : Nat :=
  HKConvGen.powBaseCutoff (rate hd hm) epsilon

theorem rate_pow_le_of_modulus (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (n : Nat) (hn : degreeModulus hd hm epsilon ≤ n) :
    (rate hd hm)^n ≤ epsilon :=
  Q'.le_trans' _ _ _
    (HKConvGen.pow_base_antitone (Q'.le_of_lt (rate_positive hd hm))
      (Q'.le_of_lt (rate_lt_one hd hm)) hn)
    (HKConvGen.pow_base_le_cutoff (rate_positive hd hm) (rate_lt_one hd hm) hepsilon)

theorem covarianceFactor_le_of_modulus (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (n : Nat)
    (hn : degreeModulus hd hm epsilon ≤ n) :
    covarianceFactor hd hm n ≤ epsilon :=
  Q'.le_trans' _ _ _ (covarianceFactor_le_rate_pow hd hm n)
    (rate_pow_le_of_modulus hd hm epsilon hepsilon n hn)

/-- A concrete rate at the existing nome `1/1024`; all scalar guards are proved. -/
def existingNomeRate : Q' :=
  rate BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    BF4ExactSlabConditionalGeneratorMargin.existingNome_margin_positive

theorem existingNome_rate_window :
    (0 : Q') < existingNomeRate ∧ existingNomeRate < (1 : Q') :=
  ⟨rate_positive _ _, rate_lt_one _ _⟩

#print axioms argument_gt_one
#print axioms rate
#print axioms rate_positive
#print axioms rate_lt_one
#print axioms covarianceFactor_positive
#print axioms covarianceFactor_le_rate_pow
#print axioms covarianceFactor_sq_le_rate_pow_sq
#print axioms degreeModulus
#print axioms rate_pow_le_of_modulus
#print axioms covarianceFactor_le_of_modulus
#print axioms existingNomeRate
#print axioms existingNome_rate_window

end YMGap.Continuum.BF4ExactSlabSmallNomeCovarianceRate
