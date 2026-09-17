/-
# Exact fundamental fusion residual of the complete finite heat prefix

Multiplication of the original prefix by chi_1 - coeffW(w,1) has a
positive-spin bulk sum and TWO cutoff-boundary terms. All identities are
coefficientwise, for arbitrary rational w and scalar polynomial x; no
positivity, Haar independence, norm estimate or discarded tail is used.
The identity also includes cutoff zero, where the bulk sum is empty.

Consumer: the original transferred connected determinant with its full
retained spatial product and original partition. This algebra alone does
not control the signs of the weighted bulk harmonic responses or prove
an interacting transfer bound.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceHeatMoment

namespace YMGap.Continuum.SU2QuaternionHeatFusionResidual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep (coeffW coeffW_zero)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local infix:50 " ≈ " => Q'.eqv

/-- The coefficient at positive spin j; the bulk below uses only j >= 1. -/
def fusionCoeff (w : Q') (j : Nat) : Q' :=
  (coeffW w (j-1) + coeffW w (j+1)) + -(coeffW w 1 * coeffW w j)

/-- The literal finite sum over spins 1,...,K, represented by a shifted range. -/
def bulkResidual (w : Q') (K : Nat) (x : RatPoly) : RatPoly :=
  finitePolySum (fun i => polySmul (fusionCoeff w (i+1))
    (characterPolynomial x (i+1))) (List.range K)

/-- Both finite-cutoff edge terms, with their original signs. -/
def boundaryResidual (w : Q') (K : Nat) (x : RatPoly) : RatPoly :=
  polyAdd (polySmul (coeffW w K) (characterPolynomial x (K+1)))
    (polyNeg (polySmul (coeffW w (K+1)) (characterPolynomial x K)))

-- This is the same character recurrence used by FaceHeatMoment's private
-- first_mul_succ, reproduced locally without changing that producer's API.
private theorem first_mul_succ (x : RatPoly) (n : Nat) :
    RatPolyCoeffEqv (polyMul (characterPolynomial x 1) (characterPolynomial x (n+1)))
      (polyAdd (characterPolynomial x (n+2)) (characterPolynomial x n)) := by
  let a := polyMul (characterPolynomial x 1) (characterPolynomial x (n+1))
  let b := characterPolynomial x n
  exact (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.mul (.const (-1)) (.var 1))) (.var 1)) (by decide)
    (fun i => if i = 0 then a else b)).trans
    (((RatPolyCoeffEqv.refl a).add (cap_mul_left (-1) b)).add (.refl b))

private theorem weighted_neg (weight : List Nat → Q') : ∀ p : RatPoly,
    ratWeightedSum weight (polyNeg p) ≈ -(ratWeightedSum weight p)
  | [] => by change (0 : Q') ≈ -0; decide
  | term::rest => by
      change (-term.2) * weight term.1 + ratWeightedSum weight (polyNeg rest) ≈
        -(term.2 * weight term.1 + ratWeightedSum weight rest)
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.neg_mul_eqv term.2 (weight term.1)) (weighted_neg weight rest))
        (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem neg_smul (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polyNeg (polySmul c p)) (polySmul (-c) p) := by
  intro weight
  exact Q'.eqv_trans _ _ _ (weighted_neg weight _)
    (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (ratWeightedSum_smul weight c p))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv c (ratWeightedSum weight p)))
        (Q'.eqv_symm (ratWeightedSum_smul weight (-c) p))))

private theorem combine_coefficient (a c e : Q') (p : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyAdd (polySmul a p) (polySmul c p)) (polyNeg (polySmul e p)))
      (polySmul ((a+c) + -e) p) :=
  ((RatPolyCoeffEqv.add_smul_same a c p).add (neg_smul e p)).trans
    (RatPolyCoeffEqv.add_smul_same (a+c) (-e) p)

private theorem residual_term (a b : Q') (s p : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyAdd s (polyNeg (cap a))) (polySmul b p))
      (polyAdd (polySmul b (polyMul s p)) (polyNeg (polySmul (a*b) p))) := by
  have h := coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
    (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
    (by decide) (fun | 0 => s | 1 => cap a | _ => polySmul b p)
  exact h.trans ((RatPolyCoeffEqv.polyMul_smul_right b s p).add
    (RatPolyCoeffEqv.neg
      ((cap_mul_left a (polySmul b p)).trans (RatPolyCoeffEqv.smul_assoc a b p))))

-- The cancellation is abstracted before any heat coefficient is substituted.
-- In particular the normalizer never unfolds a physical prefix or qpow.
private theorem step_recombine (a b c d : Q') (s x y z : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd
        (polyAdd s (polyAdd (polySmul a y) (polyNeg (polySmul b x))))
        (polyAdd (polyAdd (polySmul b z) (polySmul b x))
          (polyNeg (polySmul (d*b) y))))
      (polyAdd
        (polyAdd s (polySmul ((a+c) + -(d*b)) y))
        (polyAdd (polySmul b z) (polyNeg (polySmul c y)))) := by
  have h := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.add (.var 3) (.var 2)) (.neg (.var 4))))
    (.add (.add (.var 0) (.add (.add (.var 1) (.var 5)) (.neg (.var 4))))
      (.add (.var 3) (.neg (.var 5))))
    (by decide) (fun
      | 0 => s | 1 => polySmul a y | 2 => polySmul b x
      | 3 => polySmul b z | 4 => polySmul (d*b) y | _ => polySmul c y)
  exact h.trans (((RatPolyCoeffEqv.refl s).add (combine_coefficient a c (d*b) y)).add
    (RatPolyCoeffEqv.refl _))

private theorem prefix_step (w : Q') (K : Nat) (x : RatPoly) :
    RatPolyCoeffEqv (heatPrefix w (K+1) x)
      (polyAdd (heatPrefix w K x) (polySmul (coeffW w (K+1)) (characterPolynomial x (K+1)))) := by
  unfold heatPrefix
  rw [List.range_succ, PolynomialWeightedSumBounds.sum_append]
  exact (RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_zero _)

private theorem bulk_step (w : Q') (K : Nat) (x : RatPoly) :
    RatPolyCoeffEqv (bulkResidual w (K+1) x)
      (polyAdd (bulkResidual w K x)
        (polySmul (fusionCoeff w (K+1)) (characterPolynomial x (K+1)))) := by
  unfold bulkResidual
  rw [List.range_succ, PolynomialWeightedSumBounds.sum_append]
  exact (RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_zero _)

/-- Exact complete-prefix fusion, including both cutoff-boundary terms.
No positivity or lower-cutoff hypothesis is required; K=0 is included. -/
theorem heat_fusion_residual (w : Q') (K : Nat) (x : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polyAdd (characterPolynomial x 1) (polyNeg (cap (coeffW w 1))))
        (heatPrefix w K x))
      (polyAdd (bulkResidual w K x) (boundaryResidual w K x)) := by
  induction K with
  | zero =>
      have hp : RatPolyCoeffEqv (heatPrefix w 0 x) polyOne := by
        change RatPolyCoeffEqv (polyAdd (polySmul (coeffW w 0) polyOne) polyZero) polyOne
        rw [coeffW_zero]
        exact (RatPolyCoeffEqv.add_zero _).trans (RatPolyCoeffEqv.one_smul _)
      have hb : RatPolyCoeffEqv (polyAdd (bulkResidual w 0 x) (boundaryResidual w 0 x))
          (polyAdd (characterPolynomial x 1) (polyNeg (cap (coeffW w 1)))) := by
        change RatPolyCoeffEqv
          (polyAdd polyZero (polyAdd (polySmul (coeffW w 0) (characterPolynomial x 1))
            (polyNeg (polySmul (coeffW w 1) polyOne)))) _
        rw [coeffW_zero]
        exact (RatPolyCoeffEqv.zero_add _).trans
          ((RatPolyCoeffEqv.one_smul _).add (RatPolyCoeffEqv.refl _))
      exact (hp.mul_left _).trans ((RatPolyCoeffEqv.mul_one _).trans hb.symm)
  | succ K ih =>
      let c := coeffW w 1
      let b := coeffW w (K+1)
      let p := characterPolynomial x (K+1)
      have ht : RatPolyCoeffEqv
          (polyMul (polyAdd (characterPolynomial x 1) (polyNeg (cap c))) (polySmul b p))
          (polyAdd (polyAdd (polySmul b (characterPolynomial x (K+2)))
            (polySmul b (characterPolynomial x K))) (polyNeg (polySmul (c*b) p))) :=
        (residual_term c b (characterPolynomial x 1) p).trans
          ((((first_mul_succ x K).smul b).add (RatPolyCoeffEqv.refl _)).trans
            ((RatPolyCoeffEqv.smul_add b _ _).add (RatPolyCoeffEqv.refl _)))
      have hc := step_recombine (coeffW w K) b (coeffW w (K+2)) c
        (bulkResidual w K x) (characterPolynomial x K) p (characterPolynomial x (K+2))
      have hcoef : fusionCoeff w (K+1) =
          (coeffW w K + coeffW w (K+2)) + -(c*b) := by
        simp only [fusionCoeff, Nat.add_sub_cancel, c, b]
      rw [← hcoef] at hc
      exact ((prefix_step w K x).mul_left _).trans
        ((RatPolyCoeffEqv.mul_add_right _ _ _).trans
          ((ih.add ht).trans
            (hc.trans ((bulk_step w K x).symm.add (RatPolyCoeffEqv.refl _)))))

end YMGap.Continuum.SU2QuaternionHeatFusionResidual

#print axioms YMGap.Continuum.SU2QuaternionHeatFusionResidual.fusionCoeff
#print axioms YMGap.Continuum.SU2QuaternionHeatFusionResidual.bulkResidual
#print axioms YMGap.Continuum.SU2QuaternionHeatFusionResidual.boundaryResidual
#print axioms YMGap.Continuum.SU2QuaternionHeatFusionResidual.heat_fusion_residual
