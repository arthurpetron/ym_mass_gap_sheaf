/-
# SAME original chronological action under the spatial x1/x2 swap

Every original heat character and coefficient is retained. The actual face
list, including its final spatial slice, is permuted, never truncated or
replaced. Polynomial equality uses common padding; Haar removal explicitly
checks support. No positivity or coupling restriction is needed for these
finite identities.

The consumer is SAME original-window expectation invariance, followed by
the reflected-form isometry. This file does not construct a scaling limit,
physical mass calibration or continuum Euclidean covariance.
-/

import YMGap.Continuum.BF4ExactSlabSpatialAxisSwapHaar
import YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction

namespace YMGap.Continuum.BF4ExactSlabSpatialAxisSwapAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry
open YMGap.Continuum.BF4ExactSlabSpatialAxisSwapHaar
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation "nlinks" extent => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

private theorem swap_shifted_perm {faces : List Z4Plaq}
    (h : (faces.map swapPlaquette).Perm faces) (time : Nat) :
    ((faces.map (timeShiftPlaquette time)).map swapPlaquette).Perm
      (faces.map (timeShiftPlaquette time)) := by
  simpa only [List.map_map, swapPlaquette_timeShift_commute] using
    h.map (timeShiftPlaquette time)

theorem swap_chainFaces_perm (width start : Nat) : ∀ steps,
    ((chainFaces width start steps).map swapPlaquette).Perm (chainFaces width start steps)
  | 0 => swap_shifted_perm (swap_spatialFaces_perm width) start
  | steps+1 => by
      simp only [chainFaces, List.map_append]
      exact (swap_shifted_perm (swap_spatialFaces_perm width) start).append
        ((swap_shifted_perm (swap_temporalFaces_perm width) start).append
          (swap_chainFaces_perm width (start+1) steps))

/-- Every actual selected face, including the terminal spatial slice,
is present on the SAME contained original chronological window. -/
theorem swap_originalChainFaces_perm (extent width start steps : Nat)
    (hw : width ≤ extent+1) (ht : start+steps ≤ extent) :
    (((chainIds extent width start steps).map (slabPlaquetteAt extent)).map swapPlaquette).Perm
      ((chainIds extent width start steps).map (slabPlaquetteAt extent)) :=
  ((chainFaces_perm extent width start steps hw ht).symm.map swapPlaquette).trans
    ((swap_chainFaces_perm width start steps).trans
      (chainFaces_perm extent width start steps hw ht))

/-- Literal face heat polynomial, recoded from ID to its actual face.
Coefficients and the complete spin prefix are unchanged. -/
def heatAtFace (w : Q') (K extent : Nat) (face : Z4Plaq) : RatPoly :=
  finitePolySum (fun spin => polySmul (coeffAt (heatKernelPacket K w) spin)
    (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin)) (List.range (K+1))

private theorem sum_support {A : Type} {blocks : Nat} (f : A → RatPoly)
    (hf : ∀ a, SupportedQuaternionBlocks blocks (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks blocks (finitePolySum f xs)
  | [] => fun _ h => False.elim (List.not_mem_nil h)
  | a::xs => supported_add (hf a) (sum_support f hf xs)

private theorem smul_support {blocks : Nat} (c : Q') {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem heatAtFace_support (w : Q') (K extent : Nat) (face : Z4Plaq) :
    SupportedQuaternionBlocks (nlinks extent) (heatAtFace w K extent face) :=
  sum_support _ (fun spin => smul_support _ (original_character_support extent face spin)) _

private theorem swap_sum {A : Type} (extent : Nat) (f : A → RatPoly) : ∀ xs : List A,
    swapPolynomial extent (finitePolySum f xs) =
      finitePolySum (fun a => swapPolynomial extent (f a)) xs
  | [] => rfl
  | a::xs => by
      simp only [finitePolySum, swapPolynomial, reindexQuaternionPolynomial_add]
      exact congrArg (polyAdd (swapPolynomial extent (f a))) (swap_sum extent f xs)

theorem heatAtFace_swap (w : Q') (K extent : Nat) (face : Z4Plaq) :
    PaddedPolynomialCoeffEqv (nlinks extent)
      (swapPolynomial extent (heatAtFace w K extent face))
      (heatAtFace w K extent (swapPlaquette face)) := by
  unfold heatAtFace
  rw [swap_sum]
  apply PaddedPolynomialCoeffEqv.finiteSum
  intro spin _
  rw [swapPolynomial, reindexQuaternionPolynomial_smul]
  exact (plaquette_character_swap extent face spin).smul _

private theorem product_map {A B : Type} (f : B → RatPoly) (g : A → B) : ∀ xs : List A,
    polynomialProduct f (xs.map g) = polynomialProduct (fun a => f (g a)) xs
  | [] => rfl
  | a::xs => by
      change polyMul (f (g a)) (polynomialProduct f (xs.map g)) =
        polyMul (f (g a)) (polynomialProduct (fun b => f (g b)) xs)
      exact congrArg (polyMul (f (g a))) (product_map f g xs)

private theorem product_support {A : Type} {blocks : Nat} (f : A → RatPoly)
    (hf : ∀ a, SupportedQuaternionBlocks blocks (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks blocks (polynomialProduct f xs)
  | [] => supported_one blocks
  | a::xs => supported_polyMul (hf a) (product_support f hf xs)

private theorem swap_product {A : Type} (extent : Nat) (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → PaddedPolynomialCoeffEqv (nlinks extent) (swapPolynomial extent (f a)) (g a)) →
    PaddedPolynomialCoeffEqv (nlinks extent)
      (swapPolynomial extent (polynomialProduct f xs)) (polynomialProduct g xs)
  | [], _ => .of_prefix (swapPolynomial_one_prefix extent)
  | a::xs, h => by
      change PaddedPolynomialCoeffEqv _ (swapPolynomial extent (polyMul (f a) (polynomialProduct f xs))) _
      rw [swapPolynomial, reindexQuaternionPolynomial_mul]
      exact (h a List.mem_cons_self).mul
        (swap_product extent f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem originalChainAction_support (w : Q') (K extent width start steps : Nat) :
    SupportedQuaternionBlocks (nlinks extent) (originalChainAction w K extent width start steps) := by
  unfold originalChainAction
  exact product_support _ (fun id => heatAtFace_support w K extent (slabPlaquetteAt extent id)) _

/-- SAME literal original action, at arbitrary coupling/cutoff and every
contained chronological window. No factor, partition or endpoint changes. -/
theorem originalChainAction_swap (w : Q') (K extent width start steps : Nat)
    (hw : width ≤ extent+1) (ht : start+steps ≤ extent) :
    PaddedPolynomialCoeffEqv (nlinks extent)
      (swapPolynomial extent (originalChainAction w K extent width start steps))
      (originalChainAction w K extent width start steps) := by
  let faces := (chainIds extent width start steps).map (slabPlaquetteAt extent)
  have hprod := swap_product extent (heatAtFace w K extent)
    (fun face => heatAtFace w K extent (swapPlaquette face)) faces
    (fun face _ => heatAtFace_swap w K extent face)
  rw [← product_map (heatAtFace w K extent) swapPlaquette faces] at hprod
  have hp := hprod.trans (PaddedPolynomialCoeffEqv.of_coeff
    (polynomialProduct_perm (heatAtFace w K extent)
      (swap_originalChainFaces_perm extent width start steps hw ht)))
  simpa only [faces, product_map, heatAtFace, faceHeatPolynomial, localFaceTerm,
    originalChainAction] using hp

/-- Full ORIGINAL action-weighted Haar invariance for every supported
insertion. The partition is the SAME action with insertion one. -/
theorem originalChainAction_weighted_haar_swap (w : Q') (K extent width start steps : Nat)
    (hw : width ≤ extent+1) (ht : start+steps ≤ extent)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (nlinks extent) p) :
    quaternionHaar (nlinks extent)
      (polyMul (originalChainAction w K extent width start steps) (swapPolynomial extent p)) ≈
    quaternionHaar (nlinks extent)
      (polyMul (originalChainAction w K extent width start steps) p) := by
  let action := originalChainAction w K extent width start steps
  have ha := originalChainAction_support w K extent width start steps
  have himage : PaddedPolynomialCoeffEqv (nlinks extent)
      (swapPolynomial extent (polyMul action p)) (polyMul action (swapPolynomial extent p)) := by
    rw [swapPolynomial, reindexQuaternionPolynomial_mul]
    exact (originalChainAction_swap w K extent width start steps hw ht).mul
      (PaddedPolynomialCoeffEqv.refl _ _)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (himage.haar
    (swapPolynomial_supported extent _) (supported_polyMul ha (swapPolynomial_supported extent p))))
    (swapPolynomial_haar extent _ (supported_polyMul ha hp))

end YMGap.Continuum.BF4ExactSlabSpatialAxisSwapAction

#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapAction.swap_chainFaces_perm
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapAction.swap_originalChainFaces_perm
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapAction.heatAtFace_support
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapAction.heatAtFace_swap
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapAction.originalChainAction_support
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapAction.originalChainAction_swap
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapAction.originalChainAction_weighted_haar_swap
