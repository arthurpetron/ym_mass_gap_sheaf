/-
# Original covariance with a fixed small-nome Chebyshev parameter

The proved original centered coercivity supplies reverse energy at the ACTUAL
auxiliary vector. Unlike the earlier local collar coefficient, this parameter
has no extent, cutoff, support-size or recurrence-degree argument. Both original
normalized variances and the existing sixteen-layer separation cone are kept.
No physical time/OS, changing-nome scaling, or continuum gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabSmallNomeUniformCoercivity
import YMGap.Continuum.BF4ExactSlabChebyshevCovarianceBound
import YMGap.Continuum.ChebyshevAboveOne

namespace YMGap.Continuum.BF4ExactSlabSmallNomeChebyshevCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabConditionalCovariance
open YMGap.Continuum.BF4ExactSlabSweepChebyshev
open YMGap.Continuum.BF4ExactSlabSmallNomeUniformCoercivity
open YMGap.Continuum.BF4ExactSlabFiniteVolumeReverseEnergy (geometricCalibration)
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (finiteCovariance)
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

/-- The original reverse-energy parameter; only the nome is an input. -/
def reverseParameter {w : Q'} (hd : heatRemainderBound w < 1) : Q' :=
  2 + geometricCalibration * coefficient hd

theorem reverseParameter_gt_two {w : Q'} (hd : heatRemainderBound w < 1)
    (hm : (0 : Q') < BF4ExactSlabConditionalGeneratorMargin.margin hd) :
    (2 : Q') < reverseParameter hd := reverse_coefficient_gt_two hd hm

theorem reverseParameter_nonnegative {w : Q'} (hd : heatRemainderBound w < 1)
    (hm : (0 : Q') < BF4ExactSlabConditionalGeneratorMargin.margin hd) :
    (0 : Q') ≤ reverseParameter hd :=
  Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 2)
    (Q'.le_of_lt (reverseParameter_gt_two hd hm))

theorem denominator_positive {w : Q'} (hd : heatRemainderBound w < 1)
    (hm : (0 : Q') < BF4ExactSlabConditionalGeneratorMargin.margin hd) (n : Nat) :
    (0 : Q') < Cheb.T n (reverseParameter hd + -(1 : Q')) :=
  ChebyshevAboveOne.T_positive _ (Q'.le_trans' _ _ _
    (by decide : (1 : Q') ≤ (2 : Q') + -(1 : Q'))
    (Q'.add_le_add_right _ _ (-(1 : Q'))
      (Q'.le_of_lt (reverseParameter_gt_two hd hm)))) n

/-- Explicit reciprocal factor with no support, volume, or cutoff dependence. -/
def covarianceFactor {w : Q'} (hd : heatRemainderBound w < 1)
    (hm : (0 : Q') < BF4ExactSlabConditionalGeneratorMargin.margin hd) (n : Nat) : Q' :=
  Q'.recipPos (Cheb.T n (reverseParameter hd + -(1 : Q')))
    (denominator_positive hd hm n)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hm : (0 : Q') < BF4ExactSlabConditionalGeneratorMargin.margin hd)
  (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "ids" => slabPhysicalFaceEdges extent
local notation "physical" => (fun (id : Nat) (h : id ∈ ids) => h)

include hsmall hm in
/-- Constructed reverse energy at the actual auxiliary, for any centered
completed seed and any recurrence degree. No local support budget is paid. -/
theorem auxiliary_reverse_energy (x : GNSCompletionSpace F)
    (hx : Centered hw0 hw1 K extent hK x) (n : Nat) :
    let u := (coupled hw0 hw1 K extent hK (reverseParameter hd) x n).2;
    RCle (RCscale (reverseParameter hd) (normSq ((P).balanced (schedule extent) u)))
      (RCscale 2 (normSq ((P).sweep (schedule extent) u))) :=
  volume_uniform_reverse_energy hw0 hw1 hsmall hd hm extent stage _
    (coupled_centered hw0 hw1 K extent hK (reverseParameter hd) x hx n).2

include hsmall in
/-- Squared original finite covariance controlled by BOTH original variances.
The fixed parameter no longer deteriorates with support size or degree. -/
theorem finiteCovariance_sq_bound (n : Nat)
    (support testSupport : List Z4Link) (p q : (F).V)
    (hp : LinkLocal extent support p.val)
    (hq : LinkLocal extent testSupport q.val)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport) :
    RCle
      (RCmul (rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage))
        (rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage)))
      (RCscale (covarianceFactor hd hm n * covarianceFactor hd hm n)
        (RCmul (rat (finiteCovariance w hw0 hw1 extent ids physical p.val p.val stage))
          (rat (finiteCovariance w hw0 hw1 extent ids physical q.val q.val stage)))) := by
  exact BF4ExactSlabChebyshevCovarianceBound.finiteCovariance_sq_bound hw0 hw1 extent stage
    (reverseParameter hd) (reverseParameter_nonnegative hd hm) n
    (denominator_positive hd hm n) support testSupport p q hp hq hsep
    (auxiliary_reverse_energy hw0 hw1 hsmall hd hm extent stage
      (embedV F (centered hw0 hw1 extent stage p))
      (completed_centered_unit hw0 hw1 extent stage p) n)

#print axioms reverseParameter
#print axioms reverseParameter_gt_two
#print axioms reverseParameter_nonnegative
#print axioms denominator_positive
#print axioms covarianceFactor
#print axioms auxiliary_reverse_energy
#print axioms finiteCovariance_sq_bound

end YMGap.Continuum.BF4ExactSlabSmallNomeChebyshevCovariance
