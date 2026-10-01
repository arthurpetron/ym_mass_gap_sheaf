/-
# Local cancellation of the original mixed quadratic coefficient

For the literal positive Casimir C and its original angular derivative pair
Gamma, the mixed-minus-diagonal quadratic polynomial is exactly
-2*q*(Cq)*Gamma(f,f) - (q*Cf-2*Gamma(q,f))^2.
The negative square is retained. The remaining source-curvature flux is
signed; source positivity alone gives it no useful sign or scaling bound.
The consumer is the existing original finite-cutoff second-order energy.
-/

import YMGap.Continuum.SU2QuaternionActiveCasimirProduct
import YMGap.Continuum.SU2QuaternionCyclicSecondOrder
import YMGap.Continuum.SU2QuaternionLiteralCasimirPairing

namespace YMGap.Continuum.SU2QuaternionSecondOrderCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceEnergy)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor (weightedAngularEnergy)
open YMGap.Continuum.SU2QuaternionLiteralCasimirPairing
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The complete source/observable cross derivative, not separate face terms. -/
def commutatorPolynomial (active : List Nat) (a f : RatPoly) : RatPoly :=
  polyAdd (polyMul a (activeCasimirPolynomial active f))
    (polySmul (-2) (activeGamma active a f))

/-- This flux is not assigned a sign, even for a positive endpoint source. -/
def curvatureFlux (active : List Nat) (a f : RatPoly) : RatPoly :=
  polyMul (polyMul a (activeCasimirPolynomial active a)) (activeGamma active f f)

private theorem product_reflected (active : List Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (activeCasimirPolynomial active (polyMul p q))
      (polyAdd (polyAdd (polyMul (activeCasimirPolynomial active p) q)
        (polyMul p (activeCasimirPolynomial active q)))
        (polyMul (cap (-2)) (activeGamma active p q))) :=
  (activeCasimirPolynomial_mul active p q).trans
    ((RatPolyCoeffEqv.refl _).add (cap_mul_left (-2) _).symm)

/-- Pointwise polynomial cancellation, before Haar integration or estimates.
No support, positivity, stationarity, heat replacement or inverse premise. -/
theorem quadratic_polynomial_cancellation (active : List Nat) (a f : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyMul (activeCasimirPolynomial active a)
        (activeCasimirPolynomial active (polyMul a (polyMul f f))))
        (polyNeg (polyMul (activeCasimirPolynomial active (polyMul a f))
          (activeCasimirPolynomial active (polyMul a f)))))
      (polyAdd (polySmul (-2) (curvatureFlux active a f))
        (polyNeg (polyMul (commutatorPolynomial active a f)
          (commutatorPolynomial active a f)))) := by
  have hdiag := product_reflected active a f
  have hff := product_reflected active f f
  have hgamma := activeGamma_mul_right active a f f
  have hmixed := (product_reflected active a (polyMul f f)).trans
    (((RatPolyCoeffEqv.refl _).add (hff.mul_left a)).add
      (hgamma.mul_left (cap (-2))))
  have hcomm : RatPolyCoeffEqv
      (polyAdd (polyMul a (activeCasimirPolynomial active f))
        (polyMul (cap (-2)) (activeGamma active a f)))
      (commutatorPolynomial active a f) :=
    (RatPolyCoeffEqv.refl _).add (cap_mul_left (-2) _)
  refine ((hmixed.mul_left (activeCasimirPolynomial active a)).add
    (RatPolyCoeffEqv.neg (hdiag.mul hdiag))).trans ?_
  refine (coeffEvalExpr_eqv_of_normalize_eq
    (.add
      (.mul (.var 2)
        (.add
          (.add (.mul (.var 2) (.mul (.var 1) (.var 1)))
            (.mul (.var 0)
              (.add (.add (.mul (.var 3) (.var 1)) (.mul (.var 1) (.var 3)))
                (.mul (.const (-2)) (.var 5)))))
          (.mul (.const (-2))
            (.add (.mul (.var 4) (.var 1)) (.mul (.var 1) (.var 4))))))
      (.neg (.mul
        (.add (.add (.mul (.var 2) (.var 1)) (.mul (.var 0) (.var 3)))
          (.mul (.const (-2)) (.var 4)))
        (.add (.add (.mul (.var 2) (.var 1)) (.mul (.var 0) (.var 3)))
          (.mul (.const (-2)) (.var 4))))))
    (.add (.mul (.const (-2)) (.mul (.mul (.var 0) (.var 2)) (.var 5)))
      (.neg (.mul
        (.add (.mul (.var 0) (.var 3)) (.mul (.const (-2)) (.var 4)))
        (.add (.mul (.var 0) (.var 3)) (.mul (.const (-2)) (.var 4))))))
    (by decide) (fun
      | 0 => a | 1 => f | 2 => activeCasimirPolynomial active a
      | 3 => activeCasimirPolynomial active f
      | 4 => activeGamma active a f | _ => activeGamma active f f)).trans ?_
  exact (cap_mul_left (-2) (curvatureFlux active a f)).add
    (RatPolyCoeffEqv.neg (hcomm.mul hcomm))

private theorem haar_neg (n : Nat) (p : RatPoly) :
    H n (polyNeg p) ≈ -(H n p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (neg_smul p))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-1) p)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
        (.neg (.var 0)) (by decide) (fun _ => H n p)))

/-- The original full-tree quadratic coefficient retains one negative square
and one signed local source flux. All family cross terms remain intact. -/
theorem sourceSecondMoment_cancellation (tail : Nat) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceSecondMoment tail a f ≈
      (-2 : Q')*H (tail+1) (curvatureFlux (List.range (tail+1)) a f) -
        H (tail+1) (polyMul (commutatorPolynomial (List.range (tail+1)) a f)
          (commutatorPolynomial (List.range (tail+1)) a f)) := by
  let active := List.range (tail+1)
  let diag := polyMul (activeCasimirPolynomial active (polyMul a f))
    (activeCasimirPolynomial active (polyMul a f))
  exact Q'.eqv_trans _ _ _ (sourceSecondMoment_literal tail a f ha hf)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_symm (haar_neg (tail+1) diag)))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append (tail+1) _ _))
        (Q'.eqv_trans _ _ _ (haar_of_coeff (quadratic_polynomial_cancellation active a f))
          (Q'.eqv_trans _ _ _ (quaternionHaar_append (tail+1) _ _)
            (Q'.add_eqv_congr' (quaternionHaar_polySmul (tail+1) (-2) _)
              (haar_neg (tail+1) _))))))

/-- The polynomial Gamma is the original finite sum of Haar angular pairs. -/
theorem haar_activeGamma (n : Nat) : ∀ (active : List Nat) (p q : RatPoly),
    H n (activeGamma active p q) ≈
      qListSum (active.map fun block => blockAngularPairValue n block p q)
  | [], _, _ => Q'.eqv_refl _
  | block::active, p, q => by
      have hb : H n (blockGamma block p q) ≈ blockAngularPairValue n block p q :=
        Q'.eqv_trans _ _ _
          (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.one_mul _)))
          (Q'.eqv_trans _ _ _ (haar_six n polyOne _)
            (sixValue_congr _ _ (fun _ _ _ _ =>
              haar_of_coeff (RatPolyCoeffEqv.one_mul _))))
      exact Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
        (Q'.add_eqv_congr' hb (haar_activeGamma n active p q))

/-- Literal Haar integration by parts, with no endpoint stationarity. -/
theorem casimir_pair_gamma (n : Nat) (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) (test p : RatPoly) :
    H n (polyMul test (activeCasimirPolynomial active p)) ≈
      H n (activeGamma active test p) :=
  Q'.eqv_trans _ _ _ (activeCasimirPolynomial_pair n active hactive test p)
    (Q'.eqv_symm (haar_activeGamma n active test p))

/-- One IBP exposes the genuine signed Hessian flux and one positive product. -/
theorem curvatureFlux_ibp (n : Nat) (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) (a f : RatPoly) :
    H n (curvatureFlux active a f) ≈
      H n (polyMul (activeGamma active a a) (activeGamma active f f)) +
        H n (polyMul a (activeGamma active a (activeGamma active f f))) := by
  let g := activeGamma active f f
  have hreorder : RatPolyCoeffEqv (curvatureFlux active a f)
      (polyMul (polyMul a g) (activeCasimirPolynomial active a)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => a | 1 => activeCasimirPolynomial active a | _ => g)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hreorder)
    (Q'.eqv_trans _ _ _ (casimir_pair_gamma n active hactive (polyMul a g) a)
      (Q'.eqv_trans _ _ _ (haar_of_coeff (activeGamma_symm active (polyMul a g) a))
        (Q'.eqv_trans _ _ _ (haar_of_coeff (activeGamma_mul_right active a a g))
          (quaternionHaar_append n _ _))))

/-- Two first derivatives of the endpoint can be moved to the observable's
angular square. The resulting insertion is signed, not discarded. -/
theorem gradientFlux_ibp (n : Nat) (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) (a g : RatPoly) :
    H n (polyMul (polyMul a a) (activeCasimirPolynomial active g)) ≈
      (2 : Q')*H n (polyMul a (activeGamma active a g)) := by
  have hs := activeGamma_symm active g a
  have hprod := (activeGamma_symm active (polyMul a a) g).trans
    ((activeGamma_mul_right active g a a).trans
      ((hs.mul_right a).add (hs.mul_left a)))
  have hdouble : RatPolyCoeffEqv
      (polyAdd (polyMul (activeGamma active a g) a)
        (polyMul a (activeGamma active a g)))
      (polySmul 2 (polyMul a (activeGamma active a g))) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 1) (.var 0)) (.mul (.var 0) (.var 1)))
      (.mul (.const 2) (.mul (.var 0) (.var 1))) (by decide)
      (fun | 0 => a | _ => activeGamma active a g)).trans (cap_mul_left 2 _)
  exact Q'.eqv_trans _ _ _ (casimir_pair_gamma n active hactive (polyMul a a) g)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (hprod.trans hdouble))
      (quaternionHaar_polySmul n 2 _))

/-- Cleared identity avoids introducing a reciprocal of two or a source. -/
theorem curvatureFlux_two_ibp (n : Nat) (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) (a f : RatPoly) :
    (2 : Q')*H n (curvatureFlux active a f) ≈
      (2 : Q')*H n (polyMul (activeGamma active a a) (activeGamma active f f)) +
        H n (polyMul (polyMul a a)
          (activeCasimirPolynomial active (activeGamma active f f))) :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left 2 _ _ (curvatureFlux_ibp n active hactive a f))
    (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv 2 _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_symm (gradientFlux_ibp n active hactive a (activeGamma active f f)))))

/-- Exact second-order split: two nonpositive square terms and one signed
curvature insertion involving derivatives of the observable, not the source. -/
theorem sourceSecondMoment_curvature (tail : Nat) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceSecondMoment tail a f ≈
      -(H (tail+1) (polyMul (commutatorPolynomial (List.range (tail+1)) a f)
        (commutatorPolynomial (List.range (tail+1)) a f))) -
      (2 : Q')*H (tail+1) (polyMul (activeGamma (List.range (tail+1)) a a)
        (activeGamma (List.range (tail+1)) f f)) -
      H (tail+1) (polyMul (polyMul a a)
        (activeCasimirPolynomial (List.range (tail+1))
          (activeGamma (List.range (tail+1)) f f))) := by
  let active := List.range (tail+1)
  have hflux := curvatureFlux_two_ibp (tail+1) active
    (fun i hi => List.mem_range.mp hi) a f
  have hreorder :
      (-2 : Q')*H (tail+1) (curvatureFlux active a f) -
        H (tail+1) (polyMul (commutatorPolynomial active a f)
          (commutatorPolynomial active a f)) ≈
      -(2*H (tail+1) (curvatureFlux active a f)) -
        H (tail+1) (polyMul (commutatorPolynomial active a f)
          (commutatorPolynomial active a f)) :=
    poly_identity_of_normal_eq
      (.add (.mul (.const (-2)) (.var 0)) (.neg (.var 1)))
      (.add (.neg (.mul (.const 2) (.var 0))) (.neg (.var 1)))
      (by decide) (fun
        | 0 => H (tail+1) (curvatureFlux active a f)
        | _ => H (tail+1) (polyMul (commutatorPolynomial active a f)
          (commutatorPolynomial active a f)))
  exact Q'.eqv_trans _ _ _ (sourceSecondMoment_cancellation tail a f ha hf)
    (Q'.eqv_trans _ _ _ hreorder
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.neg_eqv_congr _ _ hflux) (Q'.eqv_refl _))
        (poly_identity_of_normal_eq
          (.add (.neg (.add (.mul (.const 2) (.var 0)) (.var 1))) (.neg (.var 2)))
          (.add (.add (.neg (.var 2)) (.neg (.mul (.const 2) (.var 0)))) (.neg (.var 1)))
          (by decide) (fun
            | 0 => H (tail+1) (polyMul (activeGamma active a a) (activeGamma active f f))
            | 1 => H (tail+1) (polyMul (polyMul a a)
                (activeCasimirPolynomial active (activeGamma active f f)))
            | _ => H (tail+1) (polyMul (commutatorPolynomial active a f)
                (commutatorPolynomial active a f))))))

private theorem commutator_supported {n : Nat} (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) {a f : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks n (commutatorPolynomial active a f) := by
  have hg := activeGamma_supported active hactive ha hf
  have hs : SupportedQuaternionBlocks n (polySmul (-2) (activeGamma active a f)) := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact hg s hs
  exact supported_add
    (supported_polyMul ha (activeCasimirPolynomial_supported active hactive hf)) hs

/-- Both negative terms have constructed square certificates. Only the signed
observable-curvature insertion remains in this original-source upper bound. -/
theorem sourceSecondMoment_le_curvature (tail : Nat) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceSecondMoment tail a f ≤
      -(H (tail+1) (polyMul (polyMul a a)
        (activeCasimirPolynomial (List.range (tail+1))
          (activeGamma (List.range (tail+1)) f f)))) := by
  let active := List.range (tail+1)
  have hrange : ∀ i, i ∈ active → i < tail+1 := fun i hi => List.mem_range.mp hi
  let S := H (tail+1) (polyMul (commutatorPolynomial active a f)
    (commutatorPolynomial active a f))
  let P := H (tail+1) (polyMul (activeGamma active a a) (activeGamma active f f))
  let R := H (tail+1) (polyMul (polyMul a a)
    (activeCasimirPolynomial active (activeGamma active f f)))
  have hs : (0 : Q') ≤ S :=
    (Certificate.square _ (commutator_supported active hrange ha hf)).haar_nonnegative
  have hp : (0 : Q') ≤ P :=
    (Certificate.mul (activeGamma_squareCertificate active hrange ha)
      (activeGamma_squareCertificate active hrange hf)).haar_nonnegative
  have hnonneg : (0 : Q') ≤ S+2*P :=
    Q'.zero_le_add _ _ hs (Q'.mul_nonneg 2 P (by decide) hp)
  have hneg : -(S+2*P) ≤ (0 : Q') :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hnonneg)
      (Q'.le_of_eqv (poly_identity_of_normal_eq (.neg (.const 0)) (.const 0)
        (by decide) (fun _ => (0 : Q'))))
  have hbound : -(S+2*P)-R ≤ -R :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (-R) hneg)
      (Q'.le_of_eqv (QPoly.q_zero_add_eqv (-R)))
  have hreorder : -S-2*P-R ≈ -(S+2*P)-R :=
    poly_identity_of_normal_eq
      (.add (.add (.neg (.var 0)) (.neg (.mul (.const 2) (.var 1)))) (.neg (.var 2)))
      (.add (.neg (.add (.var 0) (.mul (.const 2) (.var 1)))) (.neg (.var 2)))
      (by decide) (fun | 0 => S | 1 => P | _ => R)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (sourceSecondMoment_curvature tail a f ha hf) hreorder))
    hbound

/-- The exact-cutoff energy consumer now needs an observable-curvature
insertion, not absolute bounds on mixed/diagonal source Casimir squares.
The actual cubic and omitted-mode payments remain unchanged. -/
theorem sourceEnergy_le_curvature (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≤
      ((1 : Q')-w)*weightedAngularEnergy tail a f +
        ((HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))) *
          (-(H (tail+1) (polyMul (polyMul a a)
              (activeCasimirPolynomial (List.range (tail+1))
                (activeGamma (List.range (tail+1)) f f)))) +
            weightedAngularEnergy tail a f) +
          sourceErrorBudget tail w K a f) := by
  have hh := Q'.sub_nonneg_of_le hw1
  have hc : (0 : Q') ≤ HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)) :=
    Q'.mul_nonneg _ _ HalfPow.half_nonneg (Q'.mul_nonneg _ _ hh hh)
  have hquad := Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.add_le_add_right _ _ (weightedAngularEnergy tail a f)
      (sourceSecondMoment_le_curvature tail a f ha hf)) hc
  exact Q'.le_trans' _ _ _ (sourceEnergy_le_secondOrder tail hw0 hw1 K a f ha hf)
    (Q'.add_le_add_left _ _ _
      (Q'.add_le_add_right _ _ (sourceErrorBudget tail w K a f) hquad))

#print axioms commutatorPolynomial
#print axioms curvatureFlux
#print axioms quadratic_polynomial_cancellation
#print axioms sourceSecondMoment_cancellation
#print axioms haar_activeGamma
#print axioms casimir_pair_gamma
#print axioms curvatureFlux_ibp
#print axioms gradientFlux_ibp
#print axioms curvatureFlux_two_ibp
#print axioms sourceSecondMoment_curvature
#print axioms sourceSecondMoment_le_curvature
#print axioms sourceEnergy_le_curvature

end YMGap.Continuum.SU2QuaternionSecondOrderCancellation
