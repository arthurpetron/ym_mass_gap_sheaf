/-
# Facewise comparison on the SAME physical crossing interface

Allow a supplied nome and cutoff at each actual crossing face. The old
physical face expansions and overlapping polynomial channels are retained.
The comparison factor is the product of the individual face factors;
unchanged faces can contribute exactly one, regardless of their cutoffs.
The constant profile is exactly the previous interface, not a new model.

This is a finite unnormalized reflected-form comparison. It neither
changes the original bulk dressing nor proves an interacting marginal
identity, thermodynamic coercivity, completed range density or Clay.
-/

import YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity

namespace YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabSquareWeightComparison
open YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def factorProduct {A : Type} (c : A → Q') : List A → Q'
  | [] => 1
  | a::xs => c a * factorProduct c xs

theorem factorProduct_nonnegative {A : Type} (c : A → Q') (hc : ∀ a,(0 : Q') ≤ c a) :
    ∀ xs : List A,(0 : Q') ≤ factorProduct c xs
  | [] => by change (0 : Q') ≤ 1; decide
  | a::xs => Q'.mul_nonneg _ _ (hc a) (factorProduct_nonnegative c hc xs)

/-- Products need no independence: unchanged shared-variable channels stay literal. -/
theorem finiteProduct_factors {A : Type} {half : Nat} (c : A → Q') (hc : ∀ a,(0 : Q') ≤ c a)
    (f g : A → RatPoly) : ∀ xs : List A,
      ∀ P : (a : A) → a ∈ xs → LocalSquareExpansion half (f a),
      ∀ Q : (a : A) → a ∈ xs → LocalSquareExpansion half (g a),
      (∀ a ha,WeightBound (c a) (P a ha).tree (Q a ha).tree) →
      WeightBound (factorProduct c xs) (LocalSquareExpansion.finiteProduct f xs P).tree
        (LocalSquareExpansion.finiteProduct g xs Q).tree
  | [], _, _, _ => .term 1 1 _ (by change (1 : Q')*1 ≤ 1; decide)
  | a::xs, P, Q, h =>
      WeightBound.product (h a List.mem_cons_self)
        (finiteProduct_factors c hc f g xs
          (fun b hb => P b (List.mem_cons_of_mem a hb))
          (fun b hb => Q b (List.mem_cons_of_mem a hb))
          (fun b hb => h b (List.mem_cons_of_mem a hb)))
        (LocalSquareExpansion.finiteProduct f xs (fun b hb => P b (List.mem_cons_of_mem a hb))).weightsNonnegative
        (Q a List.mem_cons_self).weightsNonnegative (factorProduct_nonnegative c hc xs)

def profilePolynomial (w : Nat → Q') (cutoff : Nat → Nat) (half : Nat) : RatPoly :=
  (centralFixedFaceIds half).foldr (fun id p => polyMul (faceHeatPolynomial (w id) (cutoff id) half id) p) polyOne

def profileExpansion (w : Nat → Q') (hw : ∀ id,(0 : Q') ≤ w id) (cutoff : Nat → Nat) (half : Nat) :
    LocalSquareExpansion half (profilePolynomial w cutoff half) :=
  LocalSquareExpansion.finiteProduct _ _ (fun id hi => faceExpansion (hw id) (cutoff id) hi)

def profileForm (w : Nat → Q') (cutoff : Nat → Nat) (half : Nat) (p : RatPoly) : Q' :=
  quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
    (polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) p) (profilePolynomial w cutoff half))

theorem profileForm_constant (w : Q') (K half : Nat) (p : RatPoly) :
    profileForm (fun _ => w) (fun _ => K) half p=interfaceForm w K half p := rfl

def profileReflectedExpansion (w : Nat → Q') (hw : ∀ id,(0 : Q') ≤ w id)
    (cutoff : Nat → Nat) (half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) :=
  (LocalSquareExpansion.reflectedSquare half p hp hl).product (profileExpansion w hw cutoff half)

theorem profileForm_nonnegative (w : Nat → Q') (hw : ∀ id,(0 : Q') ≤ w id)
    (cutoff : Nat → Nat) (half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) : (0 : Q') ≤ profileForm w cutoff half p :=
  (profileReflectedExpansion w hw cutoff half p hp hl).haar_nonnegative

theorem profile_weight_bound (a b c : Nat → Q') (ha : ∀ id,(0 : Q') ≤ a id)
    (hb : ∀ id,(0 : Q') ≤ b id) (hc : ∀ id,(0 : Q') ≤ c id)
    (cutoff : Nat → Nat) (half : Nat)
    (hcoeff : ∀ id,id ∈ centralFixedFaceIds half → ∀ s,s ≤ cutoff id → c id * coeffW (a id) s ≤ coeffW (b id) s) :
    WeightBound (factorProduct c (centralFixedFaceIds half))
      (profileExpansion a ha cutoff half).tree (profileExpansion b hb cutoff half).tree :=
  finiteProduct_factors c hc _ _ _ _ _ (fun id hi =>
    face_weight_bound (a id) (b id) (c id) (ha id) (hb id) (cutoff id) hi (hcoeff id hi))

/-- The SAME lower polynomial, including any full original bulk dressing. -/
theorem profile_form_comparison (a b c : Nat → Q') (ha : ∀ id,(0 : Q') ≤ a id)
    (hb : ∀ id,(0 : Q') ≤ b id) (hc : ∀ id,(0 : Q') ≤ c id)
    (cutoff : Nat → Nat) (half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p)
    (hcoeff : ∀ id,id ∈ centralFixedFaceIds half → ∀ s,s ≤ cutoff id → c id * coeffW (a id) s ≤ coeffW (b id) s) :
    factorProduct c (centralFixedFaceIds half) * profileForm a cutoff half p ≤ profileForm b cutoff half p := by
  let P := profileReflectedExpansion a ha cutoff half p hp hl
  let Q := profileReflectedExpansion b hb cutoff half p hp hl
  let R := LocalSquareExpansion.reflectedSquare half p hp hl
  have hI := profile_weight_bound a b c ha hb hc cutoff half hcoeff
  have hprod := WeightBound.product (WeightBound.refl R.tree) hI
    (profileExpansion a ha cutoff half).weightsNonnegative R.weightsNonnegative
    (factorProduct_nonnegative c hc _)
  have htree : WeightBound (factorProduct c (centralFixedFaceIds half)) P.tree Q.tree :=
    hprod.change_factor (Q'.eqv_symm (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ P.haar_eq_squareValue))
    (Q'.le_trans' _ _ _ (htree.haar_bound _) (Q'.ge_of_eqv Q.haar_eq_squareValue))

end YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison

#print axioms YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison.factorProduct
#print axioms YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison.factorProduct_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison.finiteProduct_factors
#print axioms YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison.profilePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison.profileExpansion
#print axioms YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison.profileForm
#print axioms YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison.profileForm_constant
#print axioms YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison.profileReflectedExpansion
#print axioms YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison.profileForm_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison.profile_weight_bound
#print axioms YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison.profile_form_comparison
