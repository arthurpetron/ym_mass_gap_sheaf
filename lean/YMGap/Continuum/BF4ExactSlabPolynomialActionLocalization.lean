/-
# Complete ORIGINAL finite-action polynomial localization

Multiply the produced one-face bounds on ONE shared-link assignment and
pin their product to the existing identity-normalized complete action.
No original factor is dropped, independently integrated, or replaced.
Repeated face identifiers are permitted by this multiplication theorem.
They need a separate incidence tally before a six-incidence bound applies.

The result is pointwise, not yet an integrated localized partition floor,
conditional estimate, entropy/logarithmic theorem, signed response payment,
physical scaling or mass-gap statement.
-/

import YMGap.Continuum.BF4ExactSlabPolynomialHeatLocalization
import YMGap.Constructive.ExpAddConv

namespace YMGap.Continuum.BF4ExactSlabPolynomialActionLocalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half)
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (evalRatPoly evalRatPoly_mul)
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS (evalRatPoly_one evalRatPoly_smul)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (faceHeatPolynomial)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds
  (identityHeat identityHeat_positive normalizingFactor normalizedHeatProduct productCeiling_positive)
open YMGap.Continuum.BF4ExactSlabPolynomialHeatLocalization
open YMGap.Continuum.SU2PointwiseHeatStrictFloor (finiteCutoff)
open YMGap.Continuum.RGTransport (qpow qpow_nonneg)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩

/-- Finite scalar product retaining order and EVERY supplied occurrence. -/
def scalarProduct {A : Type} (f : A → Q') : List A → Q'
  | [] => 1
  | a::as => f a*scalarProduct f as

theorem scalarProduct_nonnegative {A : Type} (f : A → Q') (hf : ∀ a, (0 : Q') ≤ f a) :
    ∀ as, (0 : Q') ≤ scalarProduct f as
  | [] => by change (0 : Q') ≤ 1; decide
  | a::as => Q'.mul_nonneg _ _ (hf a) (scalarProduct_nonnegative f hf as)

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem power_congr {a b : Q'} (h : a ≈ b) : ∀ k : Nat, a^k ≈ b^k
  | 0 => Q'.eqv_refl 1
  | k+1 => mc h (power_congr h k)

private theorem power_one : ∀ k : Nat, (1 : Q')^k ≈ 1
  | 0 => Q'.eqv_refl 1
  | k+1 => Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (power_one k)

private theorem power_mul (a b : Q') : ∀ k : Nat, (a*b)^k ≈ a^k*b^k
  | 0 => by change (1 : Q') ≈ 1*1; decide
  | k+1 => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (power_mul a b k))
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (by decide) (fun | 0 => a | 1 => b | 2 => a^k | _ => b^k))

private theorem reciprocal_cancel {w : Q'} (hw0 : (0 : Q') < w) (K : Nat) :
    reciprocal w hw0 K*identityHeat w K ≈ (1 : Q') :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)

private theorem reciprocal_power {w : Q'} (hw0 : (0 : Q') < w)
    (K : Nat) (ids : List Nat) :
    (reciprocal w hw0 K)^ids.length ≈ normalizingFactor w hw0 K ids := by
  have hr : (reciprocal w hw0 K)^ids.length*(identityHeat w K)^ids.length ≈ (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (power_mul _ _ _))
      (Q'.eqv_trans _ _ _ (power_congr (reciprocal_cancel hw0 K) _) (power_one _))
  apply Q'.mul_left_cancel_of_pos (productCeiling_positive (Q'.le_of_lt hw0) K ids)
  exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (Q'.eqv_trans _ _ _ hr (Q'.eqv_symm (Q'.mul_recipPos_eqv _ _)))

private theorem normalized_product_raw {w : Q'} (hw0 : (0 : Q') < w)
    (K extent : Nat) (qs : Nat → UnitNorm) : ∀ ids,
    scalarProduct (fun id => normalizedFace w hw0 K extent id qs) ids ≈
      (reciprocal w hw0 K)^ids.length*
        evalRatPoly (environment qs) (polynomialProduct (faceHeatPolynomial w K extent) ids)
  | [] => Q'.eqv_trans _ _ _ (Q'.eqv_symm (evalRatPoly_one (environment qs)))
      (Q'.eqv_symm (Q'.one_mul_eqv _))
  | id::ids => by
      have ht := normalized_product_raw hw0 K extent qs ids
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ ht)
        (Q'.eqv_trans _ _ _ ?_ (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_symm (evalRatPoly_mul (environment qs) _ _))))
      exact poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
        (fun | 0 => reciprocal w hw0 K
             | 1 => evalRatPoly (environment qs) (faceHeatPolynomial w K extent id)
             | 2 => (reciprocal w hw0 K)^ids.length
             | _ => evalRatPoly (environment qs) (polynomialProduct (faceHeatPolynomial w K extent) ids))

/-- Exact pin to the existing complete identity-normalized action, including
overlaps, repeated identifiers and the empty action. Not normalization by Z. -/
theorem normalized_product_pin {w : Q'} (hw0 : (0 : Q') < w)
    (K extent : Nat) (ids : List Nat) (qs : Nat → UnitNorm) :
    scalarProduct (fun id => normalizedFace w hw0 K extent id qs) ids ≈
      evalRatPoly (environment qs) (normalizedHeatProduct w hw0 K extent ids) :=
  Q'.eqv_trans _ _ _ (normalized_product_raw hw0 K extent qs ids)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (reciprocal_power hw0 K ids))
      (Q'.eqv_symm (evalRatPoly_smul (environment qs) _ _)))

/-- Product of the actual four-link test weights with the SAME computed M. -/
def localizedProduct (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (qs : Nat → UnitNorm) (ids : List Nat) : Q' :=
  scalarProduct (fun id => half*qpow (faceKernelProduct extent id qs)
    (localizationDegree w hw0 hw1 K)) ids

theorem localizedProduct_nonnegative {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K extent : Nat) (qs : Nat → UnitNorm) (ids : List Nat) :
    (0 : Q') ≤ localizedProduct w hw0 hw1 K extent qs ids :=
  scalarProduct_nonnegative _ (fun id => Q'.mul_nonneg _ _ (by decide)
    (qpow_nonneg _ (faceKernelProduct_bounds extent id qs).1 _)) ids

private theorem product_le_normalized {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K extent : Nat) (qs : Nat → UnitNorm)
    (hK : finiteCutoff w ≤ K+1) : ∀ ids,
    localizedProduct w hw0 hw1 K extent qs ids ≤
      scalarProduct (fun id => normalizedFace w hw0 K extent id qs) ids
  | [] => Q'.le_refl' 1
  | id::ids => HKConv.mul_le_mul'
      (Q'.mul_nonneg _ _ (by decide) (qpow_nonneg _ (faceKernelProduct_bounds extent id qs).1 _))
      (scalarProduct_nonnegative _ (fun i => Q'.le_trans' _ _ _
        (Q'.le_of_lt (eta_positive hw0 hw1 K)) (normalizedFace_floor hw0 hw1 K extent i qs hK)) ids)
      (original_face_localization hw0 hw1 K extent id qs hK)
      (product_le_normalized hw0 hw1 K extent qs hK ids)

/-- The complete original density dominates the multiplied localized tests.
All original factors remain on the SAME environment; no law is conditioned. -/
theorem original_product_localization {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K extent : Nat) (ids : List Nat)
    (qs : Nat → UnitNorm) (hK : finiteCutoff w ≤ K+1) :
    localizedProduct w hw0 hw1 K extent qs ids ≤
      evalRatPoly (environment qs) (normalizedHeatProduct w hw0 K extent ids) :=
  Q'.le_trans' _ _ _ (product_le_normalized hw0 hw1 K extent qs hK ids)
    (Q'.le_of_eqv (normalized_product_pin hw0 K extent ids qs))

#print axioms scalarProduct
#print axioms scalarProduct_nonnegative
#print axioms normalized_product_pin
#print axioms localizedProduct
#print axioms localizedProduct_nonnegative
#print axioms original_product_localization

end YMGap.Continuum.BF4ExactSlabPolynomialActionLocalization
