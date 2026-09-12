/-
# Global algebraic gluing on the original reflected slab interface

Every crossing heat factor has a concrete reflected-square tree built
from its actual lower spatial-link representation columns and original
heat coefficients. The finite product expands into products of these
channels, without factorizing shared link variables.

The original signed boundary observable is absorbed into the same tree.
The final pin retains explicit common padding. Haar factorization and
reflection positivity are not consequences of this algebraic pin alone.
-/

import YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra

namespace YMGap.Continuum.BF4ExactSlabReflectedSquareGluing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabObservableHaarForm
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RingNormaliser

theorem faceLinkA_spatial (face : Z4Plaq) : (faceLinkA face).2 ≠ .x3 := by
  rcases face with ⟨v, plane⟩
  cases plane <;> simp only [faceLinkA, dirsOf] <;> intro h <;> cases h

theorem faceLinkA_physical {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    faceLinkA face ∈ boundaryCompleteSlabLinks extent :=
  (mem_boundaryCompleteSlabLinks_iff extent _).mpr ⟨face, hf, by simp [faceLinkA, edgesOf]⟩

def faceHeatSquares (w : Q') (K id : Nat) : SquareTree :=
  SquareTree.sum (fun spin =>
    (gramSquares (asRepresentationQuaternion (correctedSlabLinkPolynomial 1
      (faceLinkA (slabPlaquetteAt 1 id)))) spin).scale (coeffAt (heatKernelPacket K w) spin))
    (List.range (K + 1))

theorem faceHeatSquares_image (w : Q') (K : Nat) {id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges 1) :
    PaddedPolynomialCoeffEqv 116 (spatialGramFaceHeatPolynomial w K id) ((faceHeatSquares w K id).eval 1) := by
  have h := PaddedPolynomialCoeffEqv.finiteSum
    (fun spin => polySmul (coeffAt (heatKernelPacket K w) spin)
      (BF4ExactSlabTemporalGaugeFaces.reflectedSpatialLinkGram 1 (faceLinkA (slabPlaquetteAt 1 id)) spin).1)
    (fun spin => ((gramSquares (asRepresentationQuaternion (correctedSlabLinkPolynomial 1
      (faceLinkA (slabPlaquetteAt 1 id)))) spin).scale (coeffAt (heatKernelPacket K w) spin)).eval 1)
    (List.range (K + 1)) (fun spin _ =>
      ((spatial_gram_reflected_squares (faceLinkA_physical (slabPlaquetteAt_mem hi))
        (faceLinkA_spatial _) spin).smul (coeffAt (heatKernelPacket K w) spin)).trans
          (SquareTree.eval_scale 1 _ _))
  rw [correctedSlabLinks_extent_one_length, SquareTree.eval_sum] at h
  exact h

theorem faceHeatSquares_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (K id : Nat) :
    (faceHeatSquares w K id).Nonnegative := by
  apply SquareTree.sum_nonnegative
  intro spin hs
  apply SquareTree.scale_nonnegative
  · rw [coeffAt_heatKernelPacket (List.mem_range.mp hs)]
    exact coeffW_nonneg hw spin
  · exact gramSquares_nonnegative _ _

def interfaceSquares (w : Q') (K : Nat) : SquareTree :=
  (centralFixedFaceIds 0).foldr (fun id t => (faceHeatSquares w K id).product t) (.term 1 polyOne)

private theorem unit_image (extent : Nat) :
    PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
      polyOne ((.term 1 polyOne : SquareTree).eval extent) := by
  have h := PaddedPolynomialCoeffEqv.mul (ReflectionImage.one extent)
    (PaddedPolynomialCoeffEqv.refl (boundaryCompleteSlabLinks extent).length polyOne)
  exact ((h.smul 1).trans
    (.of_coeff (((RatPolyCoeffEqv.mul_one polyOne).smul 1).trans (RatPolyCoeffEqv.one_smul polyOne)))).symm

private theorem fold_image (w : Q') (K : Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges 1) →
      PaddedPolynomialCoeffEqv 116
        (ids.foldr (fun id p => polyMul (spatialGramFaceHeatPolynomial w K id) p) polyOne)
        ((ids.foldr (fun id t => (faceHeatSquares w K id).product t) (.term 1 polyOne)).eval 1)
  | [], _ => by simpa only [correctedSlabLinks_extent_one_length] using unit_image 1
  | id :: ids, h => by
      have hg := SquareTree.eval_product 1 (faceHeatSquares w K id)
        (ids.foldr (fun id t => (faceHeatSquares w K id).product t) (.term 1 polyOne))
      rw [correctedSlabLinks_extent_one_length] at hg
      exact ((faceHeatSquares_image w K (h id List.mem_cons_self)).mul
        (fold_image w K ids (fun j hj => h j (List.mem_cons_of_mem id hj)))).trans hg

theorem interfaceSquares_image (w : Q') (K : Nat) :
    PaddedPolynomialCoeffEqv 116 (spatialGramInterface w K) ((interfaceSquares w K).eval 1) :=
  fold_image w K _ (fun _ h => (mem_centralFixedFaceIds.mp h).1)

private theorem fold_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) : ∀ ids : List Nat,
    ((ids.foldr (fun id t => (faceHeatSquares w K id).product t) (.term 1 polyOne)) : SquareTree).Nonnegative
  | [] => show (0 : Q') ≤ 1 by decide
  | id :: ids => SquareTree.product_nonnegative _ _
      (faceHeatSquares_nonnegative hw K id) (fold_nonnegative hw K ids)

theorem interfaceSquares_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) :
    (interfaceSquares w K).Nonnegative := fold_nonnegative hw K _

/-- The unchanged, possibly signed boundary observable multiplies every
channel. Its sign is not imposed on the positive channel weights. -/
def observableSquares (w : Q') (K : Nat) (c : EdgeLabelling → Q') : SquareTree :=
  (.term 1 (lowerObservable w K c) : SquareTree).product (interfaceSquares w K)

theorem observableSquares_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) (c : EdgeLabelling → Q') :
    (observableSquares w K c).Nonnegative :=
  SquareTree.product_nonnegative _ _ (show (0 : Q') ≤ 1 by decide) (interfaceSquares_nonnegative hw K)

private theorem scalar_rotate (p h r : RatPoly) :
    RatPolyCoeffEqv (polyMul p (polyMul h r)) (polyMul (polyMul r p) h) :=
  coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.mul (.var 2) (.var 0)) (.var 1)) (by decide)
    (fun i => match i with | 0 => p | 1 => h | 2 => r | _ => polyZero)

/-- SAME original Gram-interface integrand, with the full signed
observable retained in every explicit reflected-square channel. -/
theorem observableSquares_image (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    PaddedPolynomialCoeffEqv 116
      (polyMul (lowerObservable w K c) (polyMul (spatialGramInterface w K)
        (reflectCorrectedSlabPolynomial 1 (lowerObservable w K c))))
      ((observableSquares w K c).eval 1) := by
  have h := SquareTree.eval_product 1 (.term 1 (lowerObservable w K c)) (interfaceSquares w K)
  rw [correctedSlabLinks_extent_one_length] at h
  exact (PaddedPolynomialCoeffEqv.of_coeff (scalar_rotate _ _ _)).trans
    (((PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.one_smul _).symm).mul
      (interfaceSquares_image w K)).trans h)

end YMGap.Continuum.BF4ExactSlabReflectedSquareGluing

#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareGluing.faceLinkA_spatial
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareGluing.faceLinkA_physical
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareGluing.faceHeatSquares
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareGluing.faceHeatSquares_image
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareGluing.faceHeatSquares_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareGluing.interfaceSquares
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareGluing.interfaceSquares_image
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareGluing.interfaceSquares_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareGluing.observableSquares
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareGluing.observableSquares_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareGluing.observableSquares_image
