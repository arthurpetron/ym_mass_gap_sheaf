/-
# Generic local face-factor products on the original Haar carrier

Finite products of arbitrary rational face factors retain their literal link
support.  On disjoint face-link sets, the same-carrier Haar product and mixed
observable moment factorize exactly.  These are algebraic interfaces only;
no coupling path or positivity hypothesis is introduced.
-/

import YMGap.Continuum.BF4ExactSlabFaceLinkLocality

namespace YMGap.Continuum.BF4ExactSlabLocalFactorProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.ClusterCount4DProgress

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

theorem factorProduct_local {f : Nat → RatPoly} {extent : Nat} {ids : List Nat}
    (hlocal : ∀ id, id ∈ ids →
      LinkLocal extent (edgesOf (slabPlaquetteAt extent id)) (f id)) :
    LinkLocal extent (faceLinks extent ids) (polynomialProduct f ids) :=
  BlockLocal.fold _ ids (fun id hi => (hlocal id hi).mono
    (fun _ hl => List.mem_flatMap.mpr ⟨id, hi, hl⟩))

theorem factorProduct_supported {f : Nat → RatPoly} {extent : Nat} {ids : List Nat}
    (hsupport : ∀ id, id ∈ ids → SupportedQuaternionBlocks (blocks extent) (f id)) :
    SupportedQuaternionBlocks (blocks extent) (polynomialProduct f ids) := by
  induction ids with
  | nil => exact supported_one _
  | cons id ids ih =>
      change SupportedQuaternionBlocks (blocks extent)
        (polyMul (f id) (polynomialProduct f ids))
      exact supported_polyMul (hsupport id List.mem_cons_self)
        (ih (fun j hj => hsupport j (List.mem_cons_of_mem id hj)))

theorem partition_factorizes {f : Nat → RatPoly} (extent : Nat) (xs ys : List Nat)
    (hlocalX : ∀ id, id ∈ xs →
      LinkLocal extent (edgesOf (slabPlaquetteAt extent id)) (f id))
    (hlocalY : ∀ id, id ∈ ys →
      LinkLocal extent (edgesOf (slabPlaquetteAt extent id)) (f id))
    (hsupportX : ∀ id, id ∈ xs → SupportedQuaternionBlocks (blocks extent) (f id))
    (hsupportY : ∀ id, id ∈ ys → SupportedQuaternionBlocks (blocks extent) (f id))
    (hd : LinksDisjoint (faceLinks extent xs) (faceLinks extent ys)) :
    quaternionHaar (blocks extent) (polynomialProduct f (xs ++ ys)) ≈
      quaternionHaar (blocks extent) (polynomialProduct f xs) *
        quaternionHaar (blocks extent) (polynomialProduct f ys) := by
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (polynomialProduct_append f xs ys))
    (haar_product
      (factorProduct_supported hsupportX)
      (factorProduct_supported hsupportY)
      (linkLocal_disjoint (factorProduct_local hlocalX)
        (factorProduct_local hlocalY) hd))

def factorMoment (f : Nat → RatPoly) (extent : Nat) (ids : List Nat)
    (p : RatPoly) : Q' :=
  quaternionHaar (blocks extent) (polyMul p (polynomialProduct f ids))

theorem mixed_moment_factorizes {f : Nat → RatPoly} (extent : Nat) (xs ys : List Nat)
    (left right : List Z4Link) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hq : SupportedQuaternionBlocks (blocks extent) q)
    (hlocalX : ∀ id, id ∈ xs →
      LinkLocal extent (edgesOf (slabPlaquetteAt extent id)) (f id))
    (hlocalY : ∀ id, id ∈ ys →
      LinkLocal extent (edgesOf (slabPlaquetteAt extent id)) (f id))
    (hsupportX : ∀ id, id ∈ xs → SupportedQuaternionBlocks (blocks extent) (f id))
    (hsupportY : ∀ id, id ∈ ys → SupportedQuaternionBlocks (blocks extent) (f id))
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (hd : LinksDisjoint (left ++ faceLinks extent xs) (right ++ faceLinks extent ys)) :
    factorMoment f extent (xs ++ ys) (polyMul p q) ≈
      factorMoment f extent xs p * factorMoment f extent ys q := by
  have hprodX := factorProduct_supported hsupportX
  have hprodY := factorProduct_supported hsupportY
  have hlocalPX : LinkLocal extent (left ++ faceLinks extent xs) (polynomialProduct f xs) := (factorProduct_local hlocalX).mono
    (fun _ h => List.mem_append.mpr (Or.inr h))
  have hlocalQY : LinkLocal extent (right ++ faceLinks extent ys) (polynomialProduct f ys) := (factorProduct_local hlocalY).mono
    (fun _ h => List.mem_append.mpr (Or.inr h))
  have hleft : LinkLocal extent (left ++ faceLinks extent xs)
      (polyMul p (polynomialProduct f xs)) :=
    BlockLocal.mul (hl.mono (fun _ h => List.mem_append.mpr (Or.inl h))) hlocalPX
  have hright : LinkLocal extent (right ++ faceLinks extent ys)
      (polyMul q (polynomialProduct f ys)) :=
    BlockLocal.mul (hr.mono (fun _ h => List.mem_append.mpr (Or.inl h))) hlocalQY
  have hdis : BlockDisjoint (blocks extent)
      (polyMul p (polynomialProduct f xs))
      (polyMul q (polynomialProduct f ys)) :=
    linkLocal_disjoint hleft hright hd
  have hcoeff : RatPolyCoeffEqv
      (polyMul (polyMul p q) (polynomialProduct f (xs ++ ys)))
      (polyMul (polyMul p (polynomialProduct f xs))
        (polyMul q (polynomialProduct f ys))) := by
    exact ((RatPolyCoeffEqv.refl _).mul (polynomialProduct_append f xs ys)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
        (fun | 0 => p | 1 => q | 2 => polynomialProduct f xs | _ => polynomialProduct f ys))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hcoeff)
    (haar_product (supported_polyMul hp hprodX) (supported_polyMul hq hprodY) hdis)

end YMGap.Continuum.BF4ExactSlabLocalFactorProduct

#print axioms YMGap.Continuum.BF4ExactSlabLocalFactorProduct.factorProduct_local
#print axioms YMGap.Continuum.BF4ExactSlabLocalFactorProduct.factorProduct_supported
#print axioms YMGap.Continuum.BF4ExactSlabLocalFactorProduct.partition_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabLocalFactorProduct.factorMoment
#print axioms YMGap.Continuum.BF4ExactSlabLocalFactorProduct.mixed_moment_factorizes
