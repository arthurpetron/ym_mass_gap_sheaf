/-
# Entropy-polynomial Jensen for the original finite Haar functional

Substitute the EXISTING finite regularized-log polynomial into any supported
original rational polynomial W. Its explicit scalar upper tangent, evaluated
at Z = ORIGINAL Haar(W), integrates to the same polynomial evaluated at Z:
the linear tangent term cancels by original Haar linearity and normalization.

The finite inequality includes zero density and needs only W <= 1 pointwise.
Positivity is needed later to normalize by Z or identify the logarithm; neither
is assumed for this finite Jensen theorem. No entropy oracle, SOS certificate,
factor independence, localized partition estimate, or interacting gap is used.
-/

import YMGap.Continuum.RegularizedLogPolynomialConcavity
import YMGap.Continuum.QuaternionHaarFiniteProductOrder
import YMGap.Continuum.QPolyHaarPositiveSubstitution

namespace YMGap.Continuum.QuaternionHaarFiniteEntropy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one supported_add)
open YMGap.Continuum.QPolyHaarPositiveSubstitution (subst eval_subst haar_one)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment haar_upper_bound haar_mono)
open YMGap.Continuum.RegularizedLogPolynomial (partialSum polynomial polynomial_eval)
open YMGap.Continuum.RegularizedLogPolynomialConcavity (tangentSlope partial_tangent)

local infix:50 " ≈ " => Q'.eqv

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem supported_scale {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem supported_subst {blocks : Nat} {W : RatPoly}
    (hW : SupportedQuaternionBlocks blocks W) :
    ∀ p : QPoly.Poly, SupportedQuaternionBlocks blocks (subst W p)
  | [] => by intro t ht; exact False.elim (List.not_mem_nil ht)
  | c::p => supported_add (supported_scale (supported_one blocks) c)
      (supported_polyMul hW (supported_subst hW p))

/-- The literal existing entropy partial sum, substituted into W. -/
def entropyStage (n : Nat) (W : RatPoly) : RatPoly := subst W (polynomial n)

/-- Evaluation is exactly the original entropy partial sum at the actual W value. -/
theorem entropyStage_eval (n : Nat) (W : RatPoly) (rho : Nat → Q') :
    evalRatPoly rho (entropyStage n W) ≈ partialSum (evalRatPoly rho W) n :=
  Q'.eqv_trans _ _ _ (eval_subst rho W (polynomial n))
    (polynomial_eval n (evalRatPoly rho W))

/-- No new coordinates are introduced by the entropy-polynomial substitution. -/
theorem entropyStage_supported {blocks : Nat} {W : RatPoly}
    (hW : SupportedQuaternionBlocks blocks W) (n : Nat) :
    SupportedQuaternionBlocks blocks (entropyStage n W) := supported_subst hW _

private def tangentPolynomial (n : Nat) (W : RatPoly) (Z : Q') : RatPoly :=
  polyAdd (polySmul (partialSum Z (n+1)) polyOne)
    (polySmul (tangentSlope n Z) (polyAdd W (polySmul (-Z) polyOne)))

private theorem eval_constant (rho : Nat → Q') (c : Q') :
    evalRatPoly rho (polySmul c polyOne) ≈ c :=
  Q'.eqv_trans _ _ _ (evalRatPoly_smul rho c polyOne)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (evalRatPoly_one rho)) (Q'.mul_one_eqv c))

private theorem haar_constant (blocks : Nat) (c : Q') :
    quaternionHaar blocks (polySmul c polyOne) ≈ c :=
  Q'.eqv_trans _ _ _ (quaternionHaar_polySmul blocks c polyOne)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (haar_one blocks)) (Q'.mul_one_eqv c))

private theorem tangent_eval (n : Nat) (W : RatPoly) (Z : Q') (rho : Nat → Q') :
    evalRatPoly rho (tangentPolynomial n W Z) ≈
      partialSum Z (n+1)+tangentSlope n Z*(evalRatPoly rho W-Z) :=
  Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
    (Q'.add_eqv_congr' (eval_constant rho _)
      (Q'.eqv_trans _ _ _ (evalRatPoly_smul rho _ _)
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (eval_constant rho (-Z)))))))

private theorem tangent_haar (n blocks : Nat) (W : RatPoly) :
    quaternionHaar blocks (tangentPolynomial n W (quaternionHaar blocks W)) ≈
      partialSum (quaternionHaar blocks W) (n+1) := by
  have h : quaternionHaar blocks (tangentPolynomial n W (quaternionHaar blocks W)) ≈
      partialSum (quaternionHaar blocks W) (n+1)+tangentSlope n (quaternionHaar blocks W)*
        (quaternionHaar blocks W+ -(quaternionHaar blocks W)) :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
    (Q'.add_eqv_congr' (haar_constant blocks _)
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul blocks _ _)
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_constant blocks _))))))
  exact Q'.eqv_trans _ _ _ h (poly_identity_of_normal_eq
    (.add (.var 0) (.mul (.var 1) (.add (.var 2) (.neg (.var 2)))))
    (.var 0) (by decide) (fun
      | 0 => partialSum (quaternionHaar blocks W) (n+1)
      | 1 => tangentSlope n (quaternionHaar blocks W)
      | _ => quaternionHaar blocks W))

/-- Finite Jensen for the ACTUAL original entropy polynomial on the SAME
finite Haar functional. The tangent is based at its OWN Z = Haar(W).
No lower density floor is needed for this finite inequality. -/
theorem haar_partial_jensen (n blocks : Nat) (W : RatPoly)
    (hW : SupportedQuaternionBlocks blocks W)
    (hupper : ∀ qs : Nat → UnitNorm, evalRatPoly (environment qs) W ≤ (1 : Q')) :
    quaternionHaar blocks (entropyStage (n+1) W) ≤
      partialSum (quaternionHaar blocks W) (n+1) := by
  have hZ := haar_upper_bound blocks W hW 1 hupper
  have ht : SupportedQuaternionBlocks blocks (tangentPolynomial n W (quaternionHaar blocks W)) :=
    supported_add (supported_scale (supported_one blocks) _)
      (supported_scale (supported_add hW (supported_scale (supported_one blocks) _)) _)
  have h := haar_mono blocks _ _ (entropyStage_supported hW (n+1)) ht (fun qs =>
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (entropyStage_eval (n+1) W (environment qs)))
      (Q'.le_trans' _ _ _ (partial_tangent n _ _ (hupper qs) hZ)
        (Q'.ge_of_eqv (tangent_eval n W _ (environment qs)))))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (tangent_haar n blocks W))

end YMGap.Continuum.QuaternionHaarFiniteEntropy

#print axioms YMGap.Continuum.QuaternionHaarFiniteEntropy.entropyStage
#print axioms YMGap.Continuum.QuaternionHaarFiniteEntropy.entropyStage_eval
#print axioms YMGap.Continuum.QuaternionHaarFiniteEntropy.entropyStage_supported
#print axioms YMGap.Continuum.QuaternionHaarFiniteEntropy.haar_partial_jensen
