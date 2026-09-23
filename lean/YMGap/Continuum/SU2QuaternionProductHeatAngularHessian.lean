/-
# Upper-half signed angular directions for the product-heat Hessian

Twice integrating by parts identifies the full upper kernel Hessian with
the source-side response, hence minus the same kinetic square. Every signed
cross term and both original endpoint sources remain. This sign theorem is
not a normalized Wilson energy estimate or a physical gap.
-/

import YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse

namespace YMGap.Continuum.SU2QuaternionProductHeatAngularHessian

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionAngularLift
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Shift a signed direction on one slice to the corresponding blocks of the
upper slice in the doubled carrier. -/
def upperTerm {n : Nat} (term : AngularTerm n) : AngularTerm (n+n) where
  block := ⟨n + term.block.val, by omega⟩
  first := term.first
  second := term.second
  coefficient := term.coefficient

def upperTerms {n : Nat} (terms : List (AngularTerm n)) :
    List (AngularTerm (n+n)) := terms.map upperTerm

/-- One shifted upper generator differentiates only the lifted source. -/
theorem applyUpperTerm_source {n : Nat} (term : AngularTerm n)
    (a r : RatPoly) (ha : SupportedQuaternionBlocks n a) :
    RatPolyCoeffEqv
      (applyAngularTerm (upperTerm term) (polyMul a (liftBoundary n r)))
      (polyMul a (liftBoundary n (applyAngularTerm term r))) := by
  have hz := angularDerivative_blockIndependent_zero
    term.first.isLt term.second.isLt
    (supported_upper_independent ha term.block.val)
  have hl := angularDerivative_liftBoundary n
    (4 * term.block.val + term.first.val)
    (4 * term.block.val + term.second.val) r
  rw [show 4*n + (4*term.block.val + term.first.val) =
      4 * (n + term.block.val) + term.first.val by omega,
    show 4*n + (4*term.block.val + term.second.val) =
      4 * (n + term.block.val) + term.second.val by omega] at hl
  refine (RatPolyCoeffEqv.smul term.coefficient
    ((angularDerivative_mul _ _ a (liftBoundary n r)).trans
      ((((hz.mul_right _).trans (RatPolyCoeffEqv.mul_zero_left _)).add
        (hl.mul_left a)).trans (RatPolyCoeffEqv.zero_add _)))).trans ?_
  rw [applyAngularTerm, lift_smul]
  exact (RatPolyCoeffEqv.polyMul_smul_right term.coefficient a _).symm

/-- The complete shifted signed direction leaves the lower source untouched
and applies the original direction to the upper source, with every sign and
mixed direction retained. -/
theorem upperDirection_source {n : Nat} (terms : List (AngularTerm n))
    (a r : RatPoly) (ha : SupportedQuaternionBlocks n a) :
    RatPolyCoeffEqv
      (signedAngularDirection (upperTerms terms) (polyMul a (liftBoundary n r)))
      (polyMul a (liftBoundary n (signedAngularDirection terms r))) := by
  induction terms with
  | nil =>
      simp only [upperTerms, List.map_nil, signedAngularDirection, lift_zero]
      exact (RatPolyCoeffEqv.mul_zero_right a).symm
  | cons term terms ih =>
      simp only [upperTerms, List.map_cons, signedAngularDirection, lift_add]
      exact ((applyUpperTerm_source term a r ha).add ih).trans
        (RatPolyCoeffEqv.mul_add_right a _ _).symm

private theorem direction_congr {n : Nat} (terms : List (AngularTerm n))
    {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (signedAngularDirection terms p) (signedAngularDirection terms q) := by
  induction terms with
  | nil => exact .refl _
  | cons term rest ih => exact ((angularDerivative_congr _ _ h).smul term.coefficient).add ih

/-- Integration by parts for an entire finite signed angular direction,
without a support or sign assumption on either polynomial. -/
theorem signedAngular_haar_pair {n : Nat} (terms : List (AngularTerm n))
    (p q : RatPoly) :
    quaternionHaar n (polyMul p (signedAngularDirection terms q)) ≈
      -(quaternionHaar n (polyMul (signedAngularDirection terms p) q)) := by
  induction terms with
  | nil =>
      exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_zero_right p))
        (by change (0 : Q') ≈ -(0 : Q'); decide)
  | cons term rest ih =>
      let D := angularDerivative (4*term.block.val+term.first.val)
        (4*term.block.val+term.second.val)
      have hs := angular_pair_at term.block.isLt term.first.isLt term.second.isLt p q
      have left : quaternionHaar n
          (polyMul (signedAngularDirection (term::rest) p) q) ≈
          term.coefficient * quaternionHaar n (polyMul (D p) q) +
            quaternionHaar n (polyMul (signedAngularDirection rest p) q) := by
        change quaternionHaar n (polyMul
          (polyAdd (polySmul term.coefficient (D p)) (signedAngularDirection rest p)) q) ≈ _
        rw [polyMul_add_left_exact]
        exact Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
          (Q'.add_eqv_congr'
            (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
              (quaternionHaar_polySmul n _ _)) (Q'.eqv_refl _))
      have right : quaternionHaar n
          (polyMul p (signedAngularDirection (term::rest) q)) ≈
          term.coefficient * quaternionHaar n (polyMul p (D q)) +
            quaternionHaar n (polyMul p (signedAngularDirection rest q)) :=
        Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _))
          (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
            (Q'.add_eqv_congr'
              (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right _ _ _))
                (quaternionHaar_polySmul n _ _)) (Q'.eqv_refl _)))
      exact Q'.eqv_trans _ _ _ right
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ hs) ih)
          (Q'.eqv_trans _ _ _
            (poly_identity_of_normal_eq
              (.add (.mul (.var 0) (.neg (.var 1))) (.neg (.var 2)))
              (.neg (.add (.mul (.var 0) (.var 1)) (.var 2))) (by decide)
              (fun | 0 => term.coefficient
                   | 1 => quaternionHaar n (polyMul (D p) q)
                   | _ => quaternionHaar n (polyMul (signedAngularDirection rest p) q)))
            (Q'.neg_eqv_congr _ _ (Q'.eqv_symm left))))

/-- The integrated second derivative of the ACTUAL product kernel, with
both complete sources retained, is minus the full same-kernel square. -/
theorem productHeat_upperHessian_eq_neg_square
    (n : Nat) (terms : List (AngularTerm n)) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i<n)
    (a : RatPoly) (ha : SupportedQuaternionBlocks n a) :
    quaternionHaar (n+n) (polyMul (polyMul a (liftBoundary n a))
      (signedAngularDirection (upperTerms terms)
        (signedAngularDirection (upperTerms terms) (productHeat n w K ids)))) ≈
      -(kineticPair n w K ids (signedAngularDirection terms a)
        (signedAngularDirection terms a)) := by
  let A := polyMul a (liftBoundary n a)
  let W := productHeat n w K ids
  let U := upperTerms terms
  have h1 := signedAngular_haar_pair U A (signedAngularDirection U W)
  have h2 := signedAngular_haar_pair U (signedAngularDirection U A) W
  have htwice : quaternionHaar (n+n)
      (polyMul A (signedAngularDirection U (signedAngularDirection U W))) ≈
      quaternionHaar (n+n)
        (polyMul (signedAngularDirection U (signedAngularDirection U A)) W) :=
    Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ h2)
      (Q'.neg_neg_eqv _))
  have hsource := (direction_congr U (upperDirection_source terms a a ha)).trans
    (upperDirection_source terms a (signedAngularDirection terms a) ha)
  have hDa := signedAngularDirection_supported terms ha
  have hDDa := signedAngularDirection_supported terms hDa
  exact Q'.eqv_trans _ _ _ htwice
    (Q'.eqv_trans _ _ _ (haar_of_coeff (hsource.mul_right W))
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm (productMap_pairing n w K ids a _))
          (Q'.eqv_trans _ _ _ (kineticPair_symm n w K ids hids _ a hDDa ha)
            (kineticPair_signedAngular_second_eq_neg_square n terms w K ids hids a ha)))))

/-- Whole-direction nonpositivity, with no number-of-blocks or cutoff loss.
This is a sign statement, not a normalized observable variance estimate. -/
theorem productHeat_upperHessian_nonpositive
    (n : Nat) (terms : List (AngularTerm n)) (w : Q') (hw : (0 : Q') ≤ w)
    (K : Nat) (ids : List Nat) (hids : ∀ i, i ∈ ids → i<n)
    (a : RatPoly) (ha : SupportedQuaternionBlocks n a) :
    quaternionHaar (n+n) (polyMul (polyMul a (liftBoundary n a))
      (signedAngularDirection (upperTerms terms)
        (signedAngularDirection (upperTerms terms) (productHeat n w K ids)))) ≤ 0 :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (productHeat_upperHessian_eq_neg_square n terms w K ids hids a ha))
    (Q'.nonpos_neg_of_nonneg (kineticPair_nonnegative n w hw K ids hids _
      (signedAngularDirection_supported terms ha)))

end YMGap.Continuum.SU2QuaternionProductHeatAngularHessian

#print axioms YMGap.Continuum.SU2QuaternionProductHeatAngularHessian.applyUpperTerm_source
#print axioms YMGap.Continuum.SU2QuaternionProductHeatAngularHessian.upperDirection_source
#print axioms YMGap.Continuum.SU2QuaternionProductHeatAngularHessian.signedAngular_haar_pair
#print axioms YMGap.Continuum.SU2QuaternionProductHeatAngularHessian.productHeat_upperHessian_eq_neg_square
#print axioms YMGap.Continuum.SU2QuaternionProductHeatAngularHessian.productHeat_upperHessian_nonpositive
