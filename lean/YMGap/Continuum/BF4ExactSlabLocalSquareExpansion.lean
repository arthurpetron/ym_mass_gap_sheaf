/-
# Constructive reflected-square expansions on every odd slab

An expansion stores the actual finite tree, its same-polynomial pin, and
proved carrier support and lower-half locality. Products retain shared
variables. Nonnegative sums retain their original rational weights.

These are inhabited algebraic certificates, not new analytic frontier
assumptions. Their Haar values are explicit weighted squares. The constructors
do not assert that a geometric slab law or a time translation has such an
expansion; concrete applications must supply their literal polynomial pin.
-/

import YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity

namespace YMGap.Continuum.BF4ExactSlabLocalSquareExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabLowerChannelLocality
open YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionBlockLocality

private theorem support_one (blocks : Nat) : SupportedQuaternionBlocks blocks polyOne := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  exact Nat.zero_le _

private theorem support_add {blocks : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    SupportedQuaternionBlocks blocks (polyAdd p q) := by
  intro t ht
  exact (List.mem_append.mp ht).elim (hp t) (hq t)

private theorem support_smul {blocks : Nat} (a : Q') {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polySmul a p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem scale_support {blocks : Nat} (a : Q') : ∀ t : SquareTree,
    SquareTreeSupported blocks t → SquareTreeSupported blocks (t.scale a)
  | .zero, _ => True.intro
  | .term _ _, h => h
  | .add p q, h => ⟨scale_support a p h.1, scale_support a q h.2⟩

private theorem scale_lower {half : Nat} (a : Q') : ∀ t : SquareTree,
    LowerSquareTree half t → LowerSquareTree half (t.scale a)
  | .zero, _ => True.intro
  | .term _ _, h => h
  | .add p q, h => ⟨scale_lower a p h.1, scale_lower a q h.2⟩

/-- Explicit positive local channels for the specified polynomial on the
specified physical odd-slab carrier. No positivity premise is erased. -/
structure LocalSquareExpansion (half : Nat) (polynomial : RatPoly) : Type where
  tree : SquareTree
  image : PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks (centralExtent half)).length
    polynomial (tree.eval (centralExtent half))
  polynomialSupported : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length polynomial
  treeSupported : SquareTreeSupported (boundaryCompleteSlabLinks (centralExtent half)).length tree
  treeLower : LowerSquareTree half tree
  weightsNonnegative : tree.Nonnegative

namespace LocalSquareExpansion

def zero (half : Nat) : LocalSquareExpansion half polyZero where
  tree := .zero
  image := .refl _ _
  polynomialSupported := fun _ h => False.elim (List.not_mem_nil h)
  treeSupported := True.intro
  treeLower := True.intro
  weightsNonnegative := True.intro

def one (half : Nat) : LocalSquareExpansion half polyOne where
  tree := .term 1 polyOne
  image := by
    have h := PaddedPolynomialCoeffEqv.mul (ReflectionImage.one (centralExtent half))
      (PaddedPolynomialCoeffEqv.refl (boundaryCompleteSlabLinks (centralExtent half)).length polyOne)
    exact ((h.smul 1).trans
      (.of_coeff (((RatPolyCoeffEqv.mul_one polyOne).smul 1).trans (RatPolyCoeffEqv.one_smul polyOne)))).symm
  polynomialSupported := support_one _
  treeSupported := support_one _
  treeLower := BlockLocal.one _ _
  weightsNonnegative := show (0 : Q') ≤ 1 by decide

/-- An arbitrary signed lower-half polynomial is retained in its channel.
Its sign is unrelated to the nonnegativity of the stored weight one. -/
def reflectedSquare (half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) :
    LocalSquareExpansion half (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) p) where
  tree := .term 1 p
  image := .of_coeff (RatPolyCoeffEqv.one_smul _).symm
  polynomialSupported := supported_polyMul (reflectCorrectedSlabPolynomial_support _ p) hp
  treeSupported := hp
  treeLower := hl
  weightsNonnegative := show (0 : Q') ≤ 1 by decide

def add {half : Nat} {p q : RatPoly} (P : LocalSquareExpansion half p) (Q : LocalSquareExpansion half q) :
    LocalSquareExpansion half (polyAdd p q) where
  tree := .add P.tree Q.tree
  image := P.image.add Q.image
  polynomialSupported := support_add P.polynomialSupported Q.polynomialSupported
  treeSupported := ⟨P.treeSupported, Q.treeSupported⟩
  treeLower := ⟨P.treeLower, Q.treeLower⟩
  weightsNonnegative := ⟨P.weightsNonnegative, Q.weightsNonnegative⟩

def scale {half : Nat} {p : RatPoly} (a : Q') (ha : (0 : Q') ≤ a) (P : LocalSquareExpansion half p) :
    LocalSquareExpansion half (polySmul a p) where
  tree := P.tree.scale a
  image := (P.image.smul a).trans (SquareTree.eval_scale _ a P.tree)
  polynomialSupported := support_smul a P.polynomialSupported
  treeSupported := scale_support a _ P.treeSupported
  treeLower := scale_lower a _ P.treeLower
  weightsNonnegative := SquareTree.scale_nonnegative a ha _ P.weightsNonnegative

/-- Product closure keeps every overlapping link variable; it assumes no
independence between the two factors. -/
def product {half : Nat} {p q : RatPoly} (P : LocalSquareExpansion half p) (Q : LocalSquareExpansion half q) :
    LocalSquareExpansion half (polyMul p q) where
  tree := P.tree.product Q.tree
  image := (P.image.mul Q.image).trans (SquareTree.eval_product _ P.tree Q.tree)
  polynomialSupported := supported_polyMul P.polynomialSupported Q.polynomialSupported
  treeSupported := squareTree_product_support _ _ P.treeSupported Q.treeSupported
  treeLower := lower_tree_product _ _ P.treeLower Q.treeLower
  weightsNonnegative := SquareTree.product_nonnegative _ _ P.weightsNonnegative Q.weightsNonnegative

def finiteSum {A : Type} {half : Nat} (f : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → LocalSquareExpansion half (f a)) → LocalSquareExpansion half (finitePolySum f xs)
  | [], _ => zero half
  | a :: xs, h => (h a List.mem_cons_self).add
      (finiteSum f xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

def finiteProduct {A : Type} {half : Nat} (f : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → LocalSquareExpansion half (f a)) →
      LocalSquareExpansion half (xs.foldr (fun a p => polyMul (f a) p) polyOne)
  | [], _ => one half
  | a :: xs, h => (h a List.mem_cons_self).product
      (finiteProduct f xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-- The witness is the actual finite weighted sum of squared Haar integrals. -/
def squareValue {half : Nat} {p : RatPoly} (P : LocalSquareExpansion half p) : Q' :=
  haarSquareSum (boundaryCompleteSlabLinks (centralExtent half)).length P.tree

theorem haar_eq_squareValue {half : Nat} {p : RatPoly} (P : LocalSquareExpansion half p) :
    (quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length p).eqv P.squareValue :=
  Q'.eqv_trans _ _ _
    (P.image.haar P.polynomialSupported (squareTree_eval_support _ _ P.treeSupported))
    (treeHaar_eq_squareSum half _ P.treeSupported P.treeLower)

theorem haar_nonnegative {half : Nat} {p : RatPoly} (P : LocalSquareExpansion half p) :
    (0 : Q') ≤ quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length p :=
  Q'.le_trans' _ _ _ (haarSquareSum_nonnegative _ _ P.weightsNonnegative)
    (Q'.le_of_eqv (Q'.eqv_symm P.haar_eq_squareValue))

end LocalSquareExpansion

end YMGap.Continuum.BF4ExactSlabLocalSquareExpansion

#print axioms YMGap.Continuum.BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion
#print axioms YMGap.Continuum.BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion.zero
#print axioms YMGap.Continuum.BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion.one
#print axioms YMGap.Continuum.BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion.reflectedSquare
#print axioms YMGap.Continuum.BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion.add
#print axioms YMGap.Continuum.BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion.scale
#print axioms YMGap.Continuum.BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion.product
#print axioms YMGap.Continuum.BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion.finiteSum
#print axioms YMGap.Continuum.BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion.finiteProduct
#print axioms YMGap.Continuum.BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion.squareValue
#print axioms YMGap.Continuum.BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion.haar_eq_squareValue
#print axioms YMGap.Continuum.BF4ExactSlabLocalSquareExpansion.LocalSquareExpansion.haar_nonnegative
