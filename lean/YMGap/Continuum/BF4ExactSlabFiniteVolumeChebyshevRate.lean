/-
# Rational square-root Chebyshev rate for the original finite covariance

The already constructed reverse-energy coefficient is strictly above two.
The scalar reciprocal-pair estimate gives an explicit geometric upper bound
on its exact Chebyshev normalization factor, without changing the original
finite action, partition, or either diagonal variance. This export is weaker
pointwise than the exact factor, but calibrates the rate to the square-root
margin. The coefficient still depends on nome and extent; no scaling-uniform
or physical mass claim is made.
-/

import YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevCovariance
import YMGap.Continuum.BF4ExactSlabConditionalVariancePositive
import YMGap.Continuum.ChebyshevSqrtRate
import YMGap.Continuum.EigenvalueShiftBound
import YMGap.Continuum.ContinuousTransferCalculus

namespace YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevRate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabConditionalCovariance
open YMGap.Continuum.BF4ExactSlabFiniteVolumeReverseEnergy
open YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevCovariance
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (finiteCovariance)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "c" => reverseCoefficient hw0 hw1 extent
local notation "x" => c + (-(1 : Q'))
local notation "ids" => slabPhysicalFaceEdges extent
local notation "physical" => (fun (id : Nat) (h : id ∈ ids) => h)

/-- The existing strict reverse-energy coefficient gives an argument above one. -/
theorem argument_gt_one : (1 : Q') < x := by
  have hc := reverseCoefficient_gt_two hw0 hw1 extent
  let coefficient := reverseCoefficient hw0 hw1 extent
  change (2 : Int) * (coefficient.den : Int) < coefficient.num * (1 : Int) at hc
  change (1 : Int) * ((coefficient.den * 1 : Nat) : Int) <
    (coefficient.num * (1 : Int) + (-1 : Int) * (coefficient.den : Int)) * (1 : Int)
  simp only [Nat.mul_one, Int.one_mul, Int.mul_one, Int.neg_one_mul] at *
  omega

/-- The rational square-root-calibrated rate at the actual finite-volume
reverse-energy coefficient. It has no late heat-cutoff argument. -/
def rate : Q' := ChebyshevSqrtRate.rate x (argument_gt_one hw0 hw1 extent)

theorem rate_positive : (0 : Q') < rate hw0 hw1 extent :=
  ChebyshevSqrtRate.rate_pos _ (argument_gt_one hw0 hw1 extent)

theorem rate_lt_one : rate hw0 hw1 extent < (1 : Q') :=
  ChebyshevSqrtRate.rate_lt_one _ (argument_gt_one hw0 hw1 extent)

/-- Explicit square-root-margin geometric upper bound on the exact
finite-volume Chebyshev factor, with scalar factor two kept explicitly. -/
theorem covarianceFactor_le_two_rate_pow (n : Nat) :
    covarianceFactor hw0 hw1 extent n ≤ (2 : Q') * (rate hw0 hw1 extent)^n := by
  exact ChebyshevSqrtRate.reciprocal_T_le x
    (argument_gt_one hw0 hw1 extent) n

theorem covarianceFactor_sq_le_two_rate_pow_sq (n : Nat) :
    covarianceFactor hw0 hw1 extent n * covarianceFactor hw0 hw1 extent n ≤
      ((2 : Q') * (rate hw0 hw1 extent)^n) *
        ((2 : Q') * (rate hw0 hw1 extent)^n) :=
  EigenvalueShiftBound.sq_mono
    (Q'.le_of_lt (Q'.recipPos_pos _
      (denominator_positive hw0 hw1 extent n)))
    (covarianceFactor_le_two_rate_pow hw0 hw1 extent n)

/-- Computed scalar degree threshold for this nome and finite extent. -/
def degreeModulus (epsilon : Q') : Nat :=
  ChebyshevSqrtRate.degreeModulus x
    (argument_gt_one hw0 hw1 extent) epsilon

theorem covarianceFactor_le_of_modulus (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (n : Nat)
    (hn : degreeModulus hw0 hw1 extent epsilon ≤ n) :
    covarianceFactor hw0 hw1 extent n ≤ epsilon :=
  ChebyshevSqrtRate.normalization_small x
    (argument_gt_one hw0 hw1 extent) epsilon hepsilon n hn

/-- Geometric-rate export of the existing exact squared covariance bound
on the SAME original finite action. This is a pointwise weaker upper bound;
the two diagonal covariances and the 16*n separation are unchanged. -/
theorem finiteCovariance_sq_rate_bound (n : Nat)
    (support testSupport : List Z4Link) (p q : (F).V)
    (hp : LinkLocal extent support p.val)
    (hq : LinkLocal extent testSupport q.val)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport) :
    RCle
      (RCmul
        (rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage))
        (rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage)))
      (RCscale
        (((2 : Q') * (rate hw0 hw1 extent)^n) *
          ((2 : Q') * (rate hw0 hw1 extent)^n))
        (RCmul
          (rat (finiteCovariance w hw0 hw1 extent ids physical p.val p.val stage))
          (rat (finiteCovariance w hw0 hw1 extent ids physical q.val q.val stage)))) := by
  have hpdiag := BF4ExactSlabConditionalVariancePositive.finiteVariance_nonnegative
    hw0 hw1 extent stage p
  have hqdiag := BF4ExactSlabConditionalVariancePositive.finiteVariance_nonnegative
    hw0 hw1 extent stage q
  have hprod : RCnonneg
      (RCmul
        (rat (finiteCovariance w hw0 hw1 extent ids physical p.val p.val stage))
        (rat (finiteCovariance w hw0 hw1 extent ids physical q.val q.val stage))) :=
    BF4ExactSlabConditionalVariancePositive.product_nonnegative hpdiag hqdiag
  have hbase := BF4ExactSlabFiniteVolumeChebyshevCovariance.finiteCovariance_sq_bound
    hw0 hw1 extent stage n support testSupport p q hp hq hsep
  exact RCle_trans hbase
    (RCscale_scalar_mono (covarianceFactor_sq_le_two_rate_pow_sq
      hw0 hw1 extent n) hprod)

end YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevRate

#print axioms YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevRate.argument_gt_one
#print axioms YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevRate.rate
#print axioms YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevRate.rate_positive
#print axioms YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevRate.rate_lt_one
#print axioms YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevRate.covarianceFactor_le_two_rate_pow
#print axioms YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevRate.covarianceFactor_sq_le_two_rate_pow_sq
#print axioms YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevRate.degreeModulus
#print axioms YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevRate.covarianceFactor_le_of_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevRate.finiteCovariance_sq_rate_bound
