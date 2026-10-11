/-
# Finite entropy Jensen for an ORIGINAL selected Haar schedule

At a fixed retained unit assignment the numeric Z is the evaluation of the
existing familyProject of W. The SAME scalar tangent is valid at every head
assignment, and its linear term cancels after the original schedule is applied
and evaluated at that retained assignment. No variable-Z polynomial, new
conditional integral, coordinate compression or entropy premise is used.

The finite result needs only the pointwise upper bound W <= 1. Empty and
repeated schedules, signed W, zero Z and partial-sum index zero are included.
Positivity, division, logarithmic limits, localized partition estimates and
response-relative or physical gap conclusions are not asserted here.
-/

import YMGap.Continuum.QuaternionHaarFiniteEntropy
import YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.QuaternionHaarFamilyFiniteEntropy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.Continuum.RingNormaliser (evalMono poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (quaternionBlockIndependent_polyZero quaternionBlockIndependent_polyOne
    quaternionBlockIndependent_polySmul)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder (familyProject_pointwise_mono)
open YMGap.Continuum.RegularizedLogPolynomial (partialSum)
open YMGap.Continuum.RegularizedLogPolynomialConcavity (tangentSlope partial_tangent)
open YMGap.Continuum.QuaternionHaarFiniteEntropy (entropyStage entropyStage_eval)

local infix:50 " ≈ " => Q'.eqv

private theorem weighted_eval (rho : Nat → Q') : ∀ p : RatPoly,
    ratWeightedSum (evalMono rho) p = evalRatPoly rho p
  | [] => rfl
  | t::p => congrArg (fun z => t.2*evalMono rho t.1+z) (weighted_eval rho p)

private theorem eval_congr (rho : Nat → Q') {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    evalRatPoly rho p ≈ evalRatPoly rho q := by
  simpa only [weighted_eval] using h (evalMono rho)

private theorem eval_constant (rho : Nat → Q') (c : Q') :
    evalRatPoly rho (polySmul c polyOne) ≈ c :=
  Q'.eqv_trans _ _ _ (evalRatPoly_smul rho c polyOne)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (evalRatPoly_one rho))
      (Q'.mul_one_eqv c))

/-- The original selected schedule preserves every rational constant. -/
theorem familyProject_constant_eval (ids : List Nat) (c : Q') (rho : Nat → Q') :
    evalRatPoly rho (familyProject ids (polySmul c polyOne)) ≈ c :=
  Q'.eqv_trans _ _ _ (eval_congr rho (familyProject_fixed ids _ (fun i _ =>
    quaternionBlockIndependent_polySmul c (quaternionBlockIndependent_polyOne i))))
    (eval_constant rho c)

/-- Exact coefficient linearity, with no bound or distinctness on the schedule. -/
theorem familyProject_smul (ids : List Nat) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (familyProject ids (polySmul c p))
      (polySmul c (familyProject ids p)) :=
  (familyProject_congr ids (cap_mul_left c p).symm).trans
    ((familyProject_mul_of_independent ids (cap c) p (fun i _ =>
      quaternionBlockIndependent_polySmul c (quaternionBlockIndependent_polyOne i))).trans
      (cap_mul_left c (familyProject ids p)))

/-- Rational scalars pull through the SAME selected projection and evaluation. -/
theorem familyProject_smul_eval (ids : List Nat) (c : Q') (p : RatPoly) (rho : Nat → Q') :
    evalRatPoly rho (familyProject ids (polySmul c p)) ≈
      c*evalRatPoly rho (familyProject ids p) :=
  Q'.eqv_trans _ _ _ (eval_congr rho (familyProject_smul ids c p))
    (evalRatPoly_smul rho c (familyProject ids p))

/-- A constant additive slack is preserved exactly at every retained assignment. -/
theorem familyProject_slack_eval (ids : List Nat) (p : RatPoly) (c : Q') (rho : Nat → Q') :
    evalRatPoly rho (familyProject ids (polyAdd p (polySmul c polyOne))) ≈
      evalRatPoly rho (familyProject ids p)+c := by
  rw [familyProject_add]
  exact Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (familyProject_constant_eval ids c rho))

/-- Every pointwise scalar upper bound survives the original schedule. -/
theorem familyProject_upper_bound (ids : List Nat) (p : RatPoly) (c : Q')
    (hupper : ∀ qs : Nat → UnitNorm, evalRatPoly (environment qs) p ≤ c)
    (qs : Nat → UnitNorm) :
    evalRatPoly (environment qs) (familyProject ids p) ≤ c :=
  Q'.le_trans' _ _ _ (familyProject_pointwise_mono ids p (polySmul c polyOne)
    (fun heads => Q'.le_trans' _ _ _ (hupper heads)
      (Q'.ge_of_eqv (eval_constant (environment heads) c))) qs)
    (Q'.le_of_eqv (familyProject_constant_eval ids c (environment qs)))

private def tangentPolynomial (n : Nat) (W : RatPoly) (Z : Q') : RatPoly :=
  polyAdd (polySmul (partialSum Z (n+1)) polyOne)
    (polySmul (tangentSlope n Z) (polyAdd W (polySmul (-Z) polyOne)))

private theorem tangent_eval (n : Nat) (W : RatPoly) (Z : Q') (rho : Nat → Q') :
    evalRatPoly rho (tangentPolynomial n W Z) ≈
      partialSum Z (n+1)+tangentSlope n Z*(evalRatPoly rho W-Z) :=
  Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
    (Q'.add_eqv_congr' (eval_constant rho _)
      (Q'.eqv_trans _ _ _ (evalRatPoly_smul rho _ _)
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (eval_constant rho (-Z)))))))

private theorem tangent_project_eval (ids : List Nat) (n : Nat) (W : RatPoly)
    (rho : Nat → Q') :
    evalRatPoly rho (familyProject ids
      (tangentPolynomial n W (evalRatPoly rho (familyProject ids W)))) ≈
      partialSum (evalRatPoly rho (familyProject ids W)) (n+1) := by
  let Z := evalRatPoly rho (familyProject ids W)
  have h : evalRatPoly rho (familyProject ids (tangentPolynomial n W Z)) ≈
      partialSum Z (n+1)+tangentSlope n Z*(Z+ -Z) := by
    unfold tangentPolynomial
    rw [familyProject_add]
    exact Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
      (Q'.add_eqv_congr' (familyProject_constant_eval ids _ rho)
        (Q'.eqv_trans _ _ _ (familyProject_smul_eval ids _ _ rho)
          (Q'.mul_eqv_congr_left _ _ _ (familyProject_slack_eval ids W (-Z) rho))))
  exact Q'.eqv_trans _ _ _ h (poly_identity_of_normal_eq
    (.add (.var 0) (.mul (.var 1) (.add (.var 2) (.neg (.var 2)))))
    (.var 0) (by decide) (fun
      | 0 => partialSum Z (n+1)
      | 1 => tangentSlope n Z
      | _ => Z))

/-- Finite Jensen at the OWN selected value Z, including index zero. Only
the global pointwise upper bound is required; no lower floor is assumed. -/
theorem family_partial_jensen (ids : List Nat) (W : RatPoly)
    (hupper : ∀ heads : Nat → UnitNorm, evalRatPoly (environment heads) W ≤ (1 : Q'))
    (qs : Nat → UnitNorm) (n : Nat) :
    evalRatPoly (environment qs) (familyProject ids (entropyStage n W)) ≤
      partialSum (evalRatPoly (environment qs) (familyProject ids W)) n := by
  cases n with
  | zero =>
      have hzero := eval_congr (environment qs)
        (familyProject_fixed ids polyZero (fun i _ => quaternionBlockIndependent_polyZero i))
      exact Q'.le_of_eqv hzero
  | succ n =>
      let Z := evalRatPoly (environment qs) (familyProject ids W)
      have hZ : Z ≤ (1 : Q') := familyProject_upper_bound ids W 1 hupper qs
      have ht : ∀ heads : Nat → UnitNorm,
          evalRatPoly (environment heads) (entropyStage (n+1) W) ≤
            evalRatPoly (environment heads) (tangentPolynomial n W Z) := fun heads =>
        Q'.le_trans' _ _ _ (Q'.le_of_eqv (entropyStage_eval (n+1) W (environment heads)))
          (Q'.le_trans' _ _ _ (partial_tangent n _ Z (hupper heads) hZ)
            (Q'.ge_of_eqv (tangent_eval n W Z (environment heads))))
      exact Q'.le_trans' _ _ _
        (familyProject_pointwise_mono ids _ _ ht qs)
        (Q'.le_of_eqv (tangent_project_eval ids n W (environment qs)))

end YMGap.Continuum.QuaternionHaarFamilyFiniteEntropy

#print axioms YMGap.Continuum.QuaternionHaarFamilyFiniteEntropy.familyProject_constant_eval
#print axioms YMGap.Continuum.QuaternionHaarFamilyFiniteEntropy.familyProject_smul
#print axioms YMGap.Continuum.QuaternionHaarFamilyFiniteEntropy.familyProject_smul_eval
#print axioms YMGap.Continuum.QuaternionHaarFamilyFiniteEntropy.familyProject_slack_eval
#print axioms YMGap.Continuum.QuaternionHaarFamilyFiniteEntropy.familyProject_upper_bound
#print axioms YMGap.Continuum.QuaternionHaarFamilyFiniteEntropy.family_partial_jensen
