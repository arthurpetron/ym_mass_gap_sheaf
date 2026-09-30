/-
# Fixed-coupling covariance decay from physical face-patch coercivity

The all-order face-patch reverse-energy bound feeds the existing finite
original-covariance consumer and its fixed-extent cutoff limit. The resulting
geometric Chebyshev rate is independent of extent and cutoff. This is not an
OS-time, thermodynamic, or spacing-uniform gap.
-/

import YMGap.Continuum.BF4ExactSlabSmallNomeChebyshevCovarianceLimit
import YMGap.Continuum.BF4ExactSlabFacePatchUniformCoercivity
import YMGap.Continuum.ChebyshevGeometricLower
import YMGap.Continuum.EigenvalueShiftBound

namespace YMGap.Continuum.BF4ExactSlabFacePatchCovarianceLimit

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
open YMGap.Continuum.BF4ExactSlabChebyshevCovarianceBound
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabFacePatchGeneratorBound
open YMGap.Continuum.BF4ExactSlabFiniteVolumeReverseEnergy (geometricCalibration)
open YMGap.Continuum.BF4ExactSlabFacePatchUniformCoercivity
open YMGap.Continuum.BF4ExactSlabSmallNomeChebyshevCovarianceLimit
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
  (SupportedQuaternionBlocks)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

/-- The Chebyshev parameter calibrated by the face-patch centered energy. -/
def patchParameter {w : Q'} (hd : heatRemainderBound w < 1) : Q' :=
  2 + geometricCalibration * coefficient hd

theorem patchParameter_gt_two {w : Q'} (hd : heatRemainderBound w < 1)
    (hm : (0 : Q') < BF4ExactSlabFacePatchGeneratorBound.margin hd) :
    (2 : Q') < patchParameter hd := by
  unfold patchParameter
  exact BF4ExactSlabFiniteVolumeReverseEnergy.calibrated_coefficient_gt_two
    (coefficient hd) (coefficient_positive hd hm)

theorem patchArgument_gt_one {w : Q'} (hd : heatRemainderBound w < 1)
    (hm : (0 : Q') < BF4ExactSlabFacePatchGeneratorBound.margin hd) :
    (1 : Q') < patchParameter hd + -(1 : Q') := by
  have hc := patchParameter_gt_two hd hm
  let c := patchParameter hd
  change (2 : Int) * (c.den : Int) < c.num * (1 : Int) at hc
  change (1 : Int) * ((c.den * 1 : Nat) : Int) <
    (c.num * (1 : Int) + (-1 : Int) * (c.den : Int)) * (1 : Int)
  simp only [Nat.mul_one, Int.one_mul, Int.mul_one, Int.neg_one_mul] at *
  omega

theorem denominator_positive {w : Q'} (hd : heatRemainderBound w < 1)
    (hm : (0 : Q') < BF4ExactSlabFacePatchGeneratorBound.margin hd) (n : Nat) :
    (0 : Q') < Cheb.T n (patchParameter hd + -(1 : Q')) :=
  ChebyshevAboveOne.T_positive _
    (Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ (2 : Q') + -(1 : Q'))
      (Q'.add_le_add_right _ _ (-(1 : Q'))
        (Q'.le_of_lt (patchParameter_gt_two hd hm)))) n

def patchRate {w : Q'} (hd : heatRemainderBound w < 1)
    (hm : (0 : Q') < BF4ExactSlabFacePatchGeneratorBound.margin hd) : Q' :=
  ChebyshevGeometricLower.rho (patchParameter hd + -(1 : Q'))
    (patchArgument_gt_one hd hm)

theorem patchRate_window {w : Q'} (hd : heatRemainderBound w < 1)
    (hm : (0 : Q') < BF4ExactSlabFacePatchGeneratorBound.margin hd) :
    (0 : Q') < patchRate hd hm ∧ patchRate hd hm < 1 := by
  constructor
  · exact ChebyshevGeometricLower.rho_positive _ (patchArgument_gt_one hd hm)
  · exact ChebyshevGeometricLower.rho_lt_one _ (patchArgument_gt_one hd hm)

def patchFactor {w : Q'} (hd : heatRemainderBound w < 1)
    (hm : (0 : Q') < BF4ExactSlabFacePatchGeneratorBound.margin hd) (n : Nat) : Q' :=
  Q'.recipPos (Cheb.T n (patchParameter hd + -(1 : Q')))
    (denominator_positive hd hm n)

theorem patchFactor_le_rate_pow {w : Q'} (hd : heatRemainderBound w < 1)
    (hm : (0 : Q') < BF4ExactSlabFacePatchGeneratorBound.margin hd) (n : Nat) :
    patchFactor hd hm n ≤ (patchRate hd hm)^n := by
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv (patchFactor hd hm n)))
    (ChebyshevGeometricLower.reciprocal_T_le_pow _ (patchArgument_gt_one hd hm) n)

theorem patchFactor_positive {w : Q'} (hd : heatRemainderBound w < 1)
    (hm : (0 : Q') < BF4ExactSlabFacePatchGeneratorBound.margin hd) (n : Nat) :
    (0 : Q') < patchFactor hd hm n := Q'.recipPos_pos _ _

theorem patchFactor_sq_le_rate_pow_sq {w : Q'} (hd : heatRemainderBound w < 1)
    (hm : (0 : Q') < BF4ExactSlabFacePatchGeneratorBound.margin hd) (n : Nat) :
    patchFactor hd hm n * patchFactor hd hm n ≤
      (patchRate hd hm)^n * (patchRate hd hm)^n :=
  EigenvalueShiftBound.sq_mono
    (Q'.le_of_lt (patchFactor_positive hd hm n)) (patchFactor_le_rate_pow hd hm n)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hm : (0 : Q') < BF4ExactSlabFacePatchGeneratorBound.margin hd)
  (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "ids" => slabPhysicalFaceEdges extent
local notation "physical" => (fun (id : Nat) (h : id ∈ ids) => h)

include hsmall in
/-- Finite-cutoff squared covariance bound for the actual original action and
its own finite partition, using the face-patch all-order reverse energy. -/
theorem finite_patch_covariance_sq_bound (n : Nat)
    (support testSupport : List Z4Link) (p q : (F).V)
    (hp : LinkLocal extent support p.val)
    (hq : LinkLocal extent testSupport q.val)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport) :
    RCle
      (RCmul (rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage))
        (rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage)))
      (RCscale (patchFactor hd hm n * patchFactor hd hm n)
        (RCmul (rat (finiteCovariance w hw0 hw1 extent ids physical p.val p.val stage))
          (rat (finiteCovariance w hw0 hw1 extent ids physical q.val q.val stage)))) := by
  exact BF4ExactSlabChebyshevCovarianceBound.finiteCovariance_sq_bound
    hw0 hw1 extent stage (patchParameter hd)
    (Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 2)
      (Q'.le_of_lt (patchParameter_gt_two hd hm))) n
    (denominator_positive hd hm n) support testSupport p q hp hq hsep
    (coupled_auxiliary_reverse_energy hw0 hw1 hsmall hd hm extent stage
      (embedV F (centered hw0 hw1 extent stage p))
      (completed_centered_unit hw0 hw1 extent stage p) n)

include hsmall in
/-- Cutoff-removed covariance bound at fixed extent, with both original
diagonal variances and the same physical slab observable carrier. -/
theorem patch_covariance_sq_bound
    (n : Nat) (support testSupport : List Z4Link)
    (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hpl : LinkLocal extent support p)
    (hql : LinkLocal extent testSupport q)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport) :
    let C := covariance w hw0 hw1 extent ids physical
    leEv (CReal.mul (C p q) (C p q))
      (CReal.mul (ofQ' (patchFactor hd hm n * patchFactor hd hm n))
        (CReal.mul (C p p) (C q q))) := by
  apply covariance_sq_bound_of_finite hw0 hw1 extent p q
    (patchFactor hd hm n * patchFactor hd hm n)
  intro stage
  have hfin := finite_patch_covariance_sq_bound hw0 hw1 hsmall hd hm
    extent stage n support testSupport
    (⟨p, hp⟩ : (fullData hw0 hw1 (headCutoff w + stage) extent
      (Nat.le_add_right _ _)).V)
    (⟨q, hq⟩ : (fullData hw0 hw1 (headCutoff w + stage) extent
      (Nat.le_add_right _ _)).V) hpl hql hsep
  change leEv
    (CReal.mul
      (ofQ' (finiteCovariance w hw0 hw1 extent ids physical p q stage))
      (ofQ' (finiteCovariance w hw0 hw1 extent ids physical p q stage)))
    (CReal.mul (ofQ' (patchFactor hd hm n * patchFactor hd hm n))
      (CReal.mul
        (ofQ' (finiteCovariance w hw0 hw1 extent ids physical p p stage))
        (ofQ' (finiteCovariance w hw0 hw1 extent ids physical q q stage)))) at hfin
  exact hfin

include hsmall in
/-- Fixed-coupling genuine geometric decay. Its ratio depends on the nome but
not on extent, polynomial degree, or the late heat cutoff. -/
theorem patch_covariance_sq_geometric_bound
    (n : Nat) (support testSupport : List Z4Link)
    (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hpl : LinkLocal extent support p)
    (hql : LinkLocal extent testSupport q)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport) :
    let C := covariance w hw0 hw1 extent ids physical
    leEv (CReal.mul (C p q) (C p q))
      (CReal.mul (ofQ' ((patchRate hd hm)^n * (patchRate hd hm)^n))
        (CReal.mul (C p p) (C q q))) := by
  dsimp only
  let C := covariance w hw0 hw1 extent ids physical
  have hprod : leEv czero (CReal.mul (C p p) (C q q)) :=
    CReal.mul_nonneg
      (covariance_diagonal_nonnegative hw0 hw1 extent p hp)
      (covariance_diagonal_nonnegative hw0 hw1 extent q hq)
  exact CReal.leEv_trans
    (patch_covariance_sq_bound hw0 hw1 hsmall hd hm extent n support testSupport
      p q hp hq hpl hql hsep)
    (CReal.leEv_scalar_mono (patchFactor_sq_le_rate_pow_sq hd hm n) hprod)

/-- Closed specialization at the exact expanded nome `1/40`. -/
theorem expandedNome_patch_covariance_sq_geometric_bound
    (n : Nat) (support testSupport : List Z4Link)
    (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hpl : LinkLocal extent support p)
    (hql : LinkLocal extent testSupport q)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport) :
    let C := covariance expandedNome expandedNome_guards.1 expandedNome_guards.2.1
      extent ids physical
    leEv (CReal.mul (C p q) (C p q))
      (CReal.mul
        (ofQ' ((patchRate expandedNome_guards.2.2.2
          expandedNome_margin_separation.1)^n *
          (patchRate expandedNome_guards.2.2.2
            expandedNome_margin_separation.1)^n))
        (CReal.mul (C p p) (C q q))) :=
  patch_covariance_sq_geometric_bound expandedNome_guards.1 expandedNome_guards.2.1
    expandedNome_guards.2.2.1 expandedNome_guards.2.2.2
    expandedNome_margin_separation.1 extent n support testSupport p q hp hq hpl hql hsep

#print axioms patchParameter
#print axioms patchParameter_gt_two
#print axioms patchArgument_gt_one
#print axioms denominator_positive
#print axioms patchRate
#print axioms patchRate_window
#print axioms patchFactor
#print axioms patchFactor_positive
#print axioms patchFactor_le_rate_pow
#print axioms patchFactor_sq_le_rate_pow_sq
#print axioms finite_patch_covariance_sq_bound
#print axioms patch_covariance_sq_bound
#print axioms patch_covariance_sq_geometric_bound
#print axioms expandedNome_patch_covariance_sq_geometric_bound

end YMGap.Continuum.BF4ExactSlabFacePatchCovarianceLimit
