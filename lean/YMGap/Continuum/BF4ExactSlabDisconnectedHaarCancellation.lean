/-
# Disconnected-support cancellation for ORIGINAL interacting moments

The signed remainder activities factor on disjoint literal link supports.
For two original sub-actions in disjoint regions, all four moments in the
connected numerator factor on the SAME Haar carrier. Their partition
factors cancel exactly. No positivity, reciprocal bound, cutoff restriction
or surrogate law is needed for this algebraic identity.

The geometric disjointness premise is explicit. A full interacting slab is
not asserted to split: constructing a connected-selection reorganization
and proving normalized summability remain open.
-/

import YMGap.Continuum.BF4ExactSlabFaceLinkLocality

namespace YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabRemainderExpansion
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

theorem activity_factorizes (w : Q') (K extent : Nat) (xs ys : List Nat)
    (hd : LinksDisjoint (faceLinks extent xs) (faceLinks extent ys)) :
    activity w K extent (xs++ys) ≈ activity w K extent xs * activity w K extent ys :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (polynomialProduct_append _ xs ys))
    (haar_product (remainderProduct_supported w K extent xs) (remainderProduct_supported w K extent ys)
      (linkLocal_disjoint (remainderProduct_local w K extent xs) (remainderProduct_local w K extent ys) hd))

theorem partition_factorizes (w : Q') (K extent : Nat) (xs ys : List Nat)
    (hd : LinksDisjoint (faceLinks extent xs) (faceLinks extent ys)) :
    heatProductHaar w (boundaryCompleteSlabLinks extent).length extent (xs++ys) K ≈
      heatProductHaar w (boundaryCompleteSlabLinks extent).length extent xs K *
      heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ys K :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (polynomialProduct_append _ xs ys))
    (haar_product (heatProduct_supported w K extent xs) (heatProduct_supported w K extent ys)
      (linkLocal_disjoint (heatProduct_local w K extent xs) (heatProduct_local w K extent ys) hd))

private def env4 (p q a b : RatPoly) : Nat → RatPoly
  | 0 => p | 1 => q | 2 => a | _ => b

section Split

variable (w : Q') (K extent : Nat) (xs ys : List Nat) (left right : List Z4Link)
  (hd : LinksDisjoint (left++faceLinks extent xs) (right++faceLinks extent ys))

include hd

/-- Observables may have their own links, including when a sub-action is empty. -/
theorem mixed_moment_factorizes (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q) :
    numerator w (boundaryCompleteSlabLinks extent).length extent (xs++ys) (polyMul p q) K ≈
      numerator w (boundaryCompleteSlabLinks extent).length extent xs p K *
      numerator w (boundaryCompleteSlabLinks extent).length extent ys q K := by
  have he := ((RatPolyCoeffEqv.refl (polyMul p q)).mul (polynomialProduct_append (faceHeatPolynomial w K extent) xs ys)).trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
      (env4 p q (polynomialProduct (faceHeatPolynomial w K extent) xs) (polynomialProduct (faceHeatPolynomial w K extent) ys)))
  have hlp : LinkLocal extent (left++faceLinks extent xs) (polyMul p (polynomialProduct (faceHeatPolynomial w K extent) xs)) :=
    BlockLocal.mul (hl.mono (fun _ h => List.mem_append.mpr (Or.inl h)))
      ((heatProduct_local w K extent xs).mono (fun _ h => List.mem_append.mpr (Or.inr h)))
  have hrq : LinkLocal extent (right++faceLinks extent ys) (polyMul q (polynomialProduct (faceHeatPolynomial w K extent) ys)) :=
    BlockLocal.mul (hr.mono (fun _ h => List.mem_append.mpr (Or.inl h)))
      ((heatProduct_local w K extent ys).mono (fun _ h => List.mem_append.mpr (Or.inr h)))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
    (haar_product (supported_polyMul hp (heatProduct_supported w K extent xs))
      (supported_polyMul hq (heatProduct_supported w K extent ys)) (linkLocal_disjoint hlp hrq hd))

theorem left_moment_factorizes (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p) (hl : LinkLocal extent left p) :
    numerator w (boundaryCompleteSlabLinks extent).length extent (xs++ys) p K ≈
      numerator w (boundaryCompleteSlabLinks extent).length extent xs p K *
      heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ys K :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.mul_one p).symm.mul (RatPolyCoeffEqv.refl _)))
    (Q'.eqv_trans _ _ _ (mixed_moment_factorizes w K extent xs ys left right hd p polyOne hp (supported_one _) hl (BlockLocal.one _ _))
      (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.one_mul _))))

theorem right_moment_factorizes (q : RatPoly)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q) (hr : LinkLocal extent right q) :
    numerator w (boundaryCompleteSlabLinks extent).length extent (xs++ys) q K ≈
      heatProductHaar w (boundaryCompleteSlabLinks extent).length extent xs K *
      numerator w (boundaryCompleteSlabLinks extent).length extent ys q K :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.one_mul q).symm.mul (RatPolyCoeffEqv.refl _)))
    (Q'.eqv_trans _ _ _ (mixed_moment_factorizes w K extent xs ys left right hd polyOne q (supported_one _) hq (BlockLocal.one _ _) hr)
      (Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff (RatPolyCoeffEqv.one_mul _))))

end Split

/-- The ordinary connected numerator N(pq)Z-N(p)N(q) of the original action. -/
def connectedNumerator (w : Q') (K extent : Nat) (ids : List Nat) (p q : RatPoly) : Q' :=
  numerator w (boundaryCompleteSlabLinks extent).length extent ids (polyMul p q) K *
    heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids K +
  -(numerator w (boundaryCompleteSlabLinks extent).length extent ids p K *
    numerator w (boundaryCompleteSlabLinks extent).length extent ids q K)

/-- Exact cancellation includes the original partition factors; no division. -/
theorem connectedNumerator_zero (w : Q') (K extent : Nat) (xs ys : List Nat) (left right : List Z4Link)
    (hd : LinksDisjoint (left++faceLinks extent xs) (right++faceLinks extent ys)) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q) :
    connectedNumerator w K extent (xs++ys) p q ≈ 0 := by
  have hfaces : LinksDisjoint (faceLinks extent xs) (faceLinks extent ys) :=
    fun link hx hy => hd link (List.mem_append.mpr (Or.inr hx)) (List.mem_append.mpr (Or.inr hy))
  have h := Q'.add_eqv_congr'
    (qmul (mixed_moment_factorizes w K extent xs ys left right hd p q hp hq hl hr) (partition_factorizes w K extent xs ys hfaces))
    (Q'.neg_eqv_congr _ _ (qmul (left_moment_factorizes w K extent xs ys left right hd p hp hl)
      (right_moment_factorizes w K extent xs ys left right hd q hq hr)))
  exact Q'.eqv_trans _ _ _ h (poly_identity_of_normal_eq
    (.add (.mul (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))
      (.neg (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))) (.const 0) (by decide)
    (fun i => if i = 0 then numerator w (boundaryCompleteSlabLinks extent).length extent xs p K
      else if i = 1 then heatProductHaar w (boundaryCompleteSlabLinks extent).length extent xs K
      else if i = 2 then heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ys K
      else numerator w (boundaryCompleteSlabLinks extent).length extent ys q K))

end YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation

#print axioms YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation.activity_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation.partition_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation.mixed_moment_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation.left_moment_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation.right_moment_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation.connectedNumerator
#print axioms YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation.connectedNumerator_zero
