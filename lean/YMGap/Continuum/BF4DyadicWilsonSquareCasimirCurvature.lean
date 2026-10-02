/-
# Literal Casimir curvature of the original growing fundamental square

The perimeter is P=4*side. The full original slice Casimir sends f^2 to
8P*(f^2-1), and Gamma(f,f) to 8P^2*(1-f^2). A rational constant shift
leaves Cf and Gamma unchanged: C(f-c)=3P*f, not 3P*(f-c).
These are arbitrary-insertion Haar-carrier identities, with no analytic
estimate, source replacement or scaling assertion.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareWardMoments
import YMGap.Continuum.SU2QuaternionCyclicPathCasimir

namespace YMGap.Continuum.BF4DyadicWilsonSquareCasimirCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularDerivative)
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality (blockAngularLaplacian_eq_six)
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct (activeGamma blockGamma activeCasimirPolynomial_mul)
open YMGap.Continuum.SU2QuaternionCyclicPathCasimir (activeCasimirPolynomial_carrier)
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear (six_smul)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredRemainderSquare (blockSquare_shifted)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareVarianceTaylor (paddedSquare_casimir)
open YMGap.Continuum.BF4DyadicWilsonSquareWardMoments (paddedSquare_gamma)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks sourceCharacter

/-- The rational perimeter of the literal growing dyadic square. -/
def perimeter (scale : Nat) : Q' := 4*Q'.ofNat (side scale)

private theorem derivative_affine (i j : Nat) (p : RatPoly) (a b : Q') :
    RatPolyCoeffEqv
      (angularDerivative i j (polyAdd (polySmul a p) (polySmul b polyOne)))
      (polySmul a (angularDerivative i j p)) :=
  (angularDerivative_add i j _ _).trans
    (((angularDerivative_smul i j a p).add
      ((angularDerivative_smul i j b polyOne).trans
        (((angularDerivative_one i j).smul b).trans (RatPolyCoeffEqv.smul_zero b)))).trans
      (RatPolyCoeffEqv.add_zero _))

private theorem secondDerivative_affine (block i j : Nat) (p : RatPoly) (a b : Q') :
    RatPolyCoeffEqv
      (blockAngularDerivative block i j
        (blockAngularDerivative block i j (polyAdd (polySmul a p) (polySmul b polyOne))))
      (polySmul a (blockAngularDerivative block i j (blockAngularDerivative block i j p))) :=
  (angularDerivative_congr (4*block+i) (4*block+j)
    (derivative_affine (4*block+i) (4*block+j) p a b)).trans
    (angularDerivative_smul _ _ a _)

private theorem blockLaplacian_affine (block : Nat) (p : RatPoly) (a b : Q') :
    RatPolyCoeffEqv
      (blockAngularLaplacian block (polyAdd (polySmul a p) (polySmul b polyOne)))
      (polySmul a (blockAngularLaplacian block p)) := by
  have h := secondDerivative_affine block
  exact (blockAngularLaplacian_eq_six block _).trans
    (((h 0 1 p a b).add ((h 0 2 p a b).add ((h 0 3 p a b).add
      ((h 1 2 p a b).add ((h 1 3 p a b).add (h 2 3 p a b)))))).trans
      ((six_smul a _).trans ((blockAngularLaplacian_eq_six block p).symm.smul a)))

private theorem casimir_affine (p : RatPoly) (a b : Q') : ∀ ids : List Nat,
    RatPolyCoeffEqv
      (activeCasimirPolynomial ids (polyAdd (polySmul a p) (polySmul b polyOne)))
      (polySmul a (activeCasimirPolynomial ids p))
  | [] => (RatPolyCoeffEqv.smul_zero a).symm
  | block::rest => by
      have hneg : RatPolyCoeffEqv (polyNeg (polySmul a (blockAngularLaplacian block p)))
          (polySmul a (polyNeg (blockAngularLaplacian block p))) :=
        (neg_smul _).trans ((RatPolyCoeffEqv.smul_assoc (-1) a _).trans
          ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv (-1) a) _).trans
            ((RatPolyCoeffEqv.smul_assoc a (-1) _).symm.trans
              ((neg_smul _).symm.smul a))))
      exact (((RatPolyCoeffEqv.neg (blockLaplacian_affine block p a b)).trans hneg).add
        (casimir_affine p a b rest)).trans (RatPolyCoeffEqv.smul_add a _ _).symm

private theorem weighted_gap (weight : List Nat → Q') (p : RatPoly) :
    ratWeightedSum weight (polyAdd (cap 4) (polyNeg p)) ≈
      4*ratWeightedSum weight polyOne-ratWeightedSum weight p :=
  Q'.eqv_trans _ _ _ (ratWeightedSum_add weight _ _)
    (Q'.add_eqv_congr' (ratWeightedSum_smul weight 4 polyOne)
      (Q'.eqv_trans _ _ _ (neg_smul p weight)
        (Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight (-1) p)
          (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
            (.neg (.var 0)) (by decide) (fun _ => ratWeightedSum weight p)))))

private theorem weighted_difference (weight : List Nat → Q') (p q : RatPoly) :
    ratWeightedSum weight (polyAdd p (polyNeg q)) ≈
      ratWeightedSum weight p-ratWeightedSum weight q :=
  Q'.eqv_trans _ _ _ (ratWeightedSum_add weight _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (neg_smul q weight)
        (Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight (-1) q)
          (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
            (.neg (.var 0)) (by decide) (fun _ => ratWeightedSum weight q)))))

private theorem square_collect (P : Q') (u : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyAdd (polySmul (3*P) u) (polySmul (3*P) u))
        (polySmul (-2) (polySmul P (polyAdd (cap 4) (polyNeg u)))))
      (polySmul (8*P) (polyAdd u (polyNeg polyOne))) := by
  intro weight
  let U := ratWeightedSum weight u
  let O := ratWeightedSum weight polyOne
  have hl : ratWeightedSum weight
      (polyAdd (polyAdd (polySmul (3*P) u) (polySmul (3*P) u))
        (polySmul (-2) (polySmul P (polyAdd (cap 4) (polyNeg u))))) ≈
      (3*P)*U+(3*P)*U+(-2)*(P*(4*O-U)) :=
    Q'.eqv_trans _ _ _ (ratWeightedSum_add weight _ _)
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (ratWeightedSum_add weight _ _)
        (Q'.add_eqv_congr' (ratWeightedSum_smul weight (3*P) u)
          (ratWeightedSum_smul weight (3*P) u)))
      (Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight (-2) _)
        (Q'.mul_eqv_congr_left (-2) _ _
          (Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight P _)
            (Q'.mul_eqv_congr_left P _ _ (weighted_gap weight u))))))
  have hr : ratWeightedSum weight (polySmul (8*P) (polyAdd u (polyNeg polyOne))) ≈
      (8*P)*(U-O) := Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight (8*P) _)
    (Q'.mul_eqv_congr_left (8*P) _ _ (weighted_difference weight u polyOne))
  exact Q'.eqv_trans _ _ _ hl (Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.const 3) (.var 0)) (.var 1))
        (.mul (.mul (.const 3) (.var 0)) (.var 1)))
        (.mul (.const (-2)) (.mul (.var 0) (.add (.mul (.const 4) (.var 2)) (.neg (.var 1))))))
      (.mul (.mul (.const 8) (.var 0)) (.add (.var 1) (.neg (.var 2))))
      (by decide) (fun | 0 => P | 1 => U | _ => O)) hr.symm)

private theorem gamma_affine (P : Q') (u : RatPoly) :
    RatPolyCoeffEqv (polySmul P (polyAdd (cap 4) (polyNeg u)))
      (polyAdd (polySmul (-P) u) (polySmul (4*P) polyOne)) := by
  intro weight
  have hl : ratWeightedSum weight (polySmul P (polyAdd (cap 4) (polyNeg u))) ≈
      P*(4*ratWeightedSum weight polyOne-ratWeightedSum weight u) :=
    Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight P _)
    (Q'.mul_eqv_congr_left P _ _ (weighted_gap weight u))
  have hr : ratWeightedSum weight
      (polyAdd (polySmul (-P) u) (polySmul (4*P) polyOne)) ≈
      (-P)*ratWeightedSum weight u+(4*P)*ratWeightedSum weight polyOne :=
    Q'.eqv_trans _ _ _ (ratWeightedSum_add weight _ _)
    (Q'.add_eqv_congr' (ratWeightedSum_smul weight (-P) u)
      (ratWeightedSum_smul weight (4*P) polyOne))
  exact Q'.eqv_trans _ _ _ hl (Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.mul (.const 4) (.var 2)) (.neg (.var 1))))
      (.add (.mul (.neg (.var 0)) (.var 1)) (.mul (.mul (.const 4) (.var 0)) (.var 2)))
      (by decide) (fun
        | 0 => P
        | 1 => ratWeightedSum weight u
        | _ => ratWeightedSum weight polyOne)) hr.symm)

private theorem curvature_collect (P : Q') (u : RatPoly) :
    RatPolyCoeffEqv (polySmul (-P) (polySmul (8*P) (polyAdd u (polyNeg polyOne))))
      (polySmul (8*(P*P)) (polyAdd polyOne (polyNeg u))) := by
  intro weight
  have hl : ratWeightedSum weight
      (polySmul (-P) (polySmul (8*P) (polyAdd u (polyNeg polyOne)))) ≈
      (-P)*((8*P)*(ratWeightedSum weight u-ratWeightedSum weight polyOne)) :=
    Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight (-P) _)
    (Q'.mul_eqv_congr_left (-P) _ _
      (Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight (8*P) _)
        (Q'.mul_eqv_congr_left (8*P) _ _ (weighted_difference weight u polyOne))))
  have hr : ratWeightedSum weight
      (polySmul (8*(P*P)) (polyAdd polyOne (polyNeg u))) ≈
      (8*(P*P))*(ratWeightedSum weight polyOne-ratWeightedSum weight u) :=
    Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight (8*(P*P)) _)
    (Q'.mul_eqv_congr_left (8*(P*P)) _ _ (weighted_difference weight polyOne u))
  exact Q'.eqv_trans _ _ _ hl (Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.neg (.var 0)) (.mul (.mul (.const 8) (.var 0)) (.add (.var 1) (.neg (.var 2)))))
      (.mul (.mul (.const 8) (.mul (.var 0) (.var 0))) (.add (.var 2) (.neg (.var 1))))
      (by decide) (fun
        | 0 => P
        | 1 => ratWeightedSum weight u
        | _ => ratWeightedSum weight polyOne)) hr.symm)

variable (scale width : Nat) (hwidth : side scale < width)

set_option quotPrecheck false in
local notation "f" => sourceCharacter width (paddedSquare scale width hwidth).edges 1
local notation "C" => activeCasimirPolynomial (List.range (N width))
local notation "P" => perimeter scale

/-- The literal full Casimir sends the uncentered fundamental loop to 3P*f. -/
theorem paddedSquare_perimeter_casimir : HaarCarrierEqv (N width) (C f) (polySmul (3*P) f) :=
  (paddedSquare_casimir scale width hwidth).trans
    (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.smul_coefficient
      (poly_identity_of_normal_eq (.mul (.const 12) (.var 0))
        (.mul (.const 3) (.mul (.const 4) (.var 0)))
        (by decide) (fun _ => Q'.ofNat (side scale))) f))

/-- Full original Casimir of the actual square; every original link remains. -/
theorem paddedSquare_square_casimir :
    HaarCarrierEqv (N width) (C (polyMul f f))
      (polySmul (8*P) (polyAdd (polyMul f f) (polyNeg polyOne))) := by
  have hf := paddedSquare_perimeter_casimir scale width hwidth
  have hleft := (HaarCarrierEqv.mul_right f hf).trans
    (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.polyMul_smul_left (3*P) f f))
  have hright := (HaarCarrierEqv.mul_left f hf).trans
    (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.polyMul_smul_right (3*P) f f))
  exact (RatPolyCoeffEqv.haarCarrier
    (activeCasimirPolynomial_mul (List.range (N width)) f f)).trans
      ((HaarCarrierEqv.add (HaarCarrierEqv.add hleft hright)
        (HaarCarrierEqv.smul (-2) (paddedSquare_gamma scale width hwidth))).trans
          (RatPolyCoeffEqv.haarCarrier (square_collect P (polyMul f f))))

/-- Full signed curvature as 8P^2*(1-f^2), with no favorable sign asserted. -/
theorem paddedSquare_gamma_casimir :
    HaarCarrierEqv (N width) (C (activeGamma (List.range (N width)) f f))
      (polySmul (8*(P*P)) (polyAdd polyOne (polyNeg (polyMul f f)))) := by
  have hgamma := (paddedSquare_gamma scale width hwidth).trans
    (RatPolyCoeffEqv.haarCarrier (gamma_affine P (polyMul f f)))
  exact (activeCasimirPolynomial_carrier (List.range (N width))
    (fun i hi => List.mem_range.mp hi) hgamma).trans
      ((RatPolyCoeffEqv.haarCarrier (casimir_affine (polyMul f f) (-P) (4*P) _)).trans
        ((HaarCarrierEqv.smul (-P) (paddedSquare_square_casimir scale width hwidth)).trans
          (RatPolyCoeffEqv.haarCarrier (curvature_collect P (polyMul f f)))))

/-- A constant shift leaves the literal full Casimir unchanged. -/
theorem paddedSquare_shifted_casimir_eq (c : Q') :
    HaarCarrierEqv (N width) (C (shifted f c)) (C f) :=
  RatPolyCoeffEqv.haarCarrier ((casimir_affine f 1 (-c) _).trans (RatPolyCoeffEqv.one_smul _))

/-- The OWN-centered Casimir is 3P*f; the constant mean is not multiplied. -/
theorem paddedSquare_shifted_casimir (c : Q') :
    HaarCarrierEqv (N width) (C (shifted f c)) (polySmul (3*P) f) :=
  (paddedSquare_shifted_casimir_eq scale width hwidth c).trans
    (paddedSquare_perimeter_casimir scale width hwidth)

private theorem gamma_shifted (p : RatPoly) (c : Q') : ∀ ids : List Nat,
    RatPolyCoeffEqv (activeGamma ids (shifted p c) (shifted p c)) (activeGamma ids p p)
  | [] => RatPolyCoeffEqv.refl polyZero
  | block::rest => (blockSquare_shifted block p c).add (gamma_shifted p c rest)

/-- Constant shifts preserve the complete full-slice angular polynomial. -/
theorem paddedSquare_shifted_gamma (c : Q') :
    HaarCarrierEqv (N width) (activeGamma (List.range (N width)) (shifted f c) (shifted f c))
      (activeGamma (List.range (N width)) f f) :=
  RatPolyCoeffEqv.haarCarrier (gamma_shifted f c _)

/-- The same full signed curvature applies to every rational constant shift. -/
theorem paddedSquare_shifted_gamma_casimir (c : Q') :
    HaarCarrierEqv (N width) (C (activeGamma (List.range (N width)) (shifted f c) (shifted f c)))
      (polySmul (8*(P*P)) (polyAdd polyOne (polyNeg (polyMul f f)))) :=
  (activeCasimirPolynomial_carrier (List.range (N width))
    (fun _ hi => List.mem_range.mp hi) (paddedSquare_shifted_gamma scale width hwidth c)).trans
      (paddedSquare_gamma_casimir scale width hwidth)

#print axioms perimeter
#print axioms paddedSquare_perimeter_casimir
#print axioms paddedSquare_square_casimir
#print axioms paddedSquare_gamma_casimir
#print axioms paddedSquare_shifted_casimir_eq
#print axioms paddedSquare_shifted_casimir
#print axioms paddedSquare_shifted_gamma
#print axioms paddedSquare_shifted_gamma_casimir

end YMGap.Continuum.BF4DyadicWilsonSquareCasimirCurvature
