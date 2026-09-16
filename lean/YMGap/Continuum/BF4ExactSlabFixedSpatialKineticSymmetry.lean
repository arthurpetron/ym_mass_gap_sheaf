/-
# Slice-swap symmetry of the actual fixed-spatial kinetic polynomial

Exchange the complete lower and upper source slices. Each original
relative word lower*conj(upper) becomes upper*conj(lower); their scalar
polynomials agree coefficientwise because both are the same quaternion
dot product. Every spin character, signed heat coefficient and temporal
face factor is retained. No commutativity of quaternion multiplication
is assumed. Common padding is recorded explicitly.

There is no positivity, nome, cutoff, nonempty-slice or stationarity
hypothesis. The consumer is symmetry of the actual K/V transfer in the
V-weighted pairing, not symmetry in its unweighted Haar completion.
-/

import YMGap.Continuum.SU2QuaternionTwoSliceSwap
import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialKineticSymmetry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram (faceLinkA)
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (temporalFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionTwoSliceSwap
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)

/-- The actual lower link becomes the corresponding upper link, including fallback one. -/
theorem lowerLink_swap (width : Nat) (link : Z4Link) :
    QuaternionPrefixPolyQuaternionEqv (N width+N width)
      (reindexPolyQuaternion (swap (N width)) (lowerLink width link)) (upperLink width link) := by
  by_cases hm : link ∈ baseLinks width
  · rw [lowerLink, upperLink, if_pos hm, if_pos hm]
    have hi := List.idxOf_lt_length_of_mem hm
    exact reindex_coordinateVariable_prefix (swap (N width)) (by omega)
      (swap_upper (N width) _ hi)
  · rw [lowerLink, upperLink, if_neg hm, if_neg hm]
    exact reindex_polyQuaternionOne_prefix _

/-- The actual upper link becomes the corresponding lower link. -/
theorem upperLink_swap (width : Nat) (link : Z4Link) :
    QuaternionPrefixPolyQuaternionEqv (N width+N width)
      (reindexPolyQuaternion (swap (N width)) (upperLink width link)) (lowerLink width link) := by
  by_cases hm : link ∈ baseLinks width
  · rw [lowerLink, upperLink, if_pos hm, if_pos hm]
    have hi := List.idxOf_lt_length_of_mem hm
    exact reindex_coordinateVariable_prefix (swap (N width)) (by omega)
      (swap_lower (N width) _ hi)
  · rw [lowerLink, upperLink, if_neg hm, if_neg hm]
    exact reindex_polyQuaternionOne_prefix _

private theorem scalar_conj_comm (p q : PolyQuaternion) :
    RatPolyCoeffEqv (PolyQuaternion.mul p (PolyQuaternion.conj q)).scalar
      (PolyQuaternion.mul q (PolyQuaternion.conj p)).scalar := by
  let environment : Nat → RatPoly := fun
    | 0 => p.scalar
    | 1 => p.iPart
    | 2 => p.jPart
    | 3 => p.kPart
    | 4 => q.scalar
    | 5 => q.iPart
    | 6 => q.jPart
    | _ => q.kPart
  simpa only [PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
    PolyQuaternionExpr.coordinate, coeffEvalExpr, environment,
    PolyQuaternion.mul, PolyQuaternion.conj] using
    (coeffEvalExpr_eqv_of_normalize_eq
      (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0)
        (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 4))).scalar
      (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 4)
        (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0))).scalar
      (by decide) environment)

/-- Swap reverses the relative word, but preserves its actual scalar dot product. -/
theorem relative_scalar_swap (width : Nat) (face : Z4Plaq) :
    PaddedPolynomialCoeffEqv (N width+N width)
      (reindexQuaternionPolynomial (swap (N width)) (relative width face).scalar)
      (relative width face).scalar := by
  have hp : QuaternionPrefixPolyQuaternionEqv (N width+N width)
      (reindexPolyQuaternion (swap (N width)) (relative width face))
      (PolyQuaternion.mul (upperLink width (faceLinkA face))
        (PolyQuaternion.conj (lowerLink width (faceLinkA face)))) := by
    rw [relative, reindexPolyQuaternion_mul, reindexPolyQuaternion_conj]
    exact (lowerLink_swap width _).mul (upperLink_swap width _).conj
  exact (PaddedPolynomialCoeffEqv.of_prefix hp.scalar).trans
    (PaddedPolynomialCoeffEqv.of_coeff
      (scalar_conj_comm (upperLink width (faceLinkA face)) (lowerLink width (faceLinkA face))))

/-- All spin characters retain their original scalar argument under the swap. -/
theorem character_swap (width : Nat) (face : Z4Plaq) (spin : Nat) :
    PaddedPolynomialCoeffEqv (N width+N width)
      (reindexQuaternionPolynomial (swap (N width))
        (characterPolynomial (relative width face).scalar spin))
      (characterPolynomial (relative width face).scalar spin) :=
  (PaddedPolynomialCoeffEqv.of_prefix
    (reindexQuaternionPolynomial_character_prefix (swap (N width)) (relative width face).scalar spin)).trans
    ((relative_scalar_swap width face).character spin)

private theorem reindex_sum {A : Type} {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (f : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → PaddedPolynomialCoeffEqv blocks (reindexQuaternionPolynomial s (f a)) (f a)) →
    PaddedPolynomialCoeffEqv blocks
      (reindexQuaternionPolynomial s (finitePolySum f xs)) (finitePolySum f xs)
  | [], _ => PaddedPolynomialCoeffEqv.refl _ _
  | a::xs, h => by
      change PaddedPolynomialCoeffEqv blocks
        (reindexQuaternionPolynomial s (polyAdd (f a) (finitePolySum f xs)))
        (polyAdd (f a) (finitePolySum f xs))
      rw [reindexQuaternionPolynomial_add]
      exact (h a List.mem_cons_self).add
        (reindex_sum s f xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-- The original finite heat weights, not a substituted radial kernel. -/
theorem heatFactor_swap (w : Q') (K width : Nat) (face : Z4Plaq) :
    PaddedPolynomialCoeffEqv (N width+N width)
      (reindexQuaternionPolynomial (swap (N width))
        (factor (fun f spin => characterPolynomial (relative width f).scalar spin)
          (face, heatWeights w K)))
      (factor (fun f spin => characterPolynomial (relative width f).scalar spin)
        (face, heatWeights w K)) := by
  unfold factor
  apply reindex_sum
  intro term _
  rw [reindexQuaternionPolynomial_smul]
  exact (character_swap width face term.1).smul term.2

private theorem reindex_product {A : Type} {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (f : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → PaddedPolynomialCoeffEqv blocks (reindexQuaternionPolynomial s (f a)) (f a)) →
    PaddedPolynomialCoeffEqv blocks
      (reindexQuaternionPolynomial s (polynomialProduct f xs)) (polynomialProduct f xs)
  | [], _ => PaddedPolynomialCoeffEqv.of_prefix (reindex_polyOne_prefix s)
  | a::xs, h => by
      change PaddedPolynomialCoeffEqv blocks
        (reindexQuaternionPolynomial s (polyMul (f a) (polynomialProduct f xs)))
        (polyMul (f a) (polynomialProduct f xs))
      rw [reindexQuaternionPolynomial_mul]
      exact (h a List.mem_cons_self).mul
        (reindex_product s f xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-- Exact symmetry of the SAME kinetic polynomial on the complete two-slice carrier.
All temporal faces and every original heat coefficient are retained. -/
theorem kineticWeight_swap (w : Q') (K width : Nat) :
    PaddedPolynomialCoeffEqv (N width+N width)
      (reindexQuaternionPolynomial (swap (N width)) (kineticWeight w K width))
      (kineticWeight w K width) :=
  reindex_product _ _ (temporalFaces width) (fun face _ => heatFactor_swap w K width face)

end YMGap.Continuum.BF4ExactSlabFixedSpatialKineticSymmetry

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticSymmetry.lowerLink_swap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticSymmetry.upperLink_swap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticSymmetry.relative_scalar_swap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticSymmetry.character_swap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticSymmetry.heatFactor_swap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticSymmetry.kineticWeight_swap
