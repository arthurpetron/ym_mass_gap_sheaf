/-
# Quantified weighted/unweighted ORIGINAL shared-link action comparison

The actual face deficits are telescoped in the same polynomial algebra.
Both weighted and original factors obey the existing cutoff-independent
face bound. A computed product sensitivity rescales the tolerance, and a
finite maximum of face cutoffs supplies the all-later product modulus.

Consequently c(w)^F is below every sufficiently late original Haar action
up to the supplied epsilon. There is no independence or pointwise-to-Haar
limit premise, and the cutoff depends on w, extent, face list and epsilon.
-/

import YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval
import YMGap.Continuum.BF4ExactSlabAllExtentActionLimit

namespace YMGap.Continuum.BF4ExactSlabJacobiProductComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatBound
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabJacobiWeightedHeatPin
open YMGap.Continuum.BF4ExactSlabJacobiWeightRemoval
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.PolynomialProductRemainder
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private def faceCutoffMax (w : Q') (extent : Nat) (δ : Q') : List Nat → Nat
  | [] => 0
  | id :: ids => max (weightRemovalCutoff w extent id δ) (faceCutoffMax w extent δ ids)

private theorem faceCutoffMax_covers (w : Q') (extent : Nat) (δ : Q') :
    ∀ ids : List Nat, ∀ id, id ∈ ids → weightRemovalCutoff w extent id δ ≤ faceCutoffMax w extent δ ids
  | [], _, h => False.elim (List.not_mem_nil h)
  | j :: ids, id, h => by
      rcases List.mem_cons.mp h with he | ht
      · subst id; exact Nat.le_max_left _ _
      · exact Nat.le_trans (faceCutoffMax_covers w extent δ ids id ht) (Nat.le_max_right _ _)

/-- Explicit original representation-cutoff threshold for a product tolerance. -/
def comparisonCutoff (w : Q') (extent : Nat) (ids : List Nat) (ε : Q') : Nat :=
  faceCutoffMax w extent (heatProductTolerance w extent ids ε) ids

/-- Same-variable telescoping error: original K-cutoff minus weighted N=K+1. -/
def productDeficit (w : Q') (K extent : Nat) (ids : List Nat) : RatPoly :=
  productRemainder (weightedFace w (K + 1) extent) (faceHeatPolynomial w K extent)
    (faceDeficit w (K + 1) extent) ids

theorem original_eq_weighted_add_deficit (w : Q') (K extent : Nat) (ids : List Nat) :
    RatPolyCoeffEqv (polynomialProduct (faceHeatPolynomial w K extent) ids)
      (polyAdd (polynomialProduct (weightedFace w (K + 1) extent) ids) (productDeficit w K extent ids)) :=
  polynomialProduct_remainder _ _ _ (faceHeat_eq_weighted_add_deficit w K extent) ids

theorem productDeficit_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat) (ε : Q') (hε : (0 : Q') < ε) (K : Nat)
    (hK : comparisonCutoff w extent ids ε ≤ K) :
    polynomialCoefficientL1 (productDeficit w K extent ids) ≤ ε := by
  have hδ := heatProductTolerance_pos w extent ids hε
  have h := productRemainder_coefficientL1
    (weightedFace w (K + 1) extent) (faceHeatPolynomial w K extent)
    (faceDeficit w (K + 1) extent) (faceHeatBound w extent)
    (faceHeatBound_nonnegative (Q'.le_of_lt hw0) extent)
    (fun id => weightedFace_coefficientL1_bound hw0 hw1 extent id (K + 1))
    (fun id => faceHeat_coefficientL1_bound hw0 hw1 extent id K)
    (heatProductTolerance w extent ids ε) (Q'.le_of_lt hδ) ids
    (fun id hi => faceDeficit_small hw0 hw1 extent id _ hδ (K + 1)
      (Nat.le_trans (faceCutoffMax_covers w extent _ ids id hi)
        (Nat.le_trans hK (Nat.le_succ K))))
  exact Q'.le_trans' _ _ _ h (heatProductTolerance_budget (Q'.le_of_lt hw0) extent ids hε)

theorem productDeficit_haar_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) (ε : Q') (hε : (0 : Q') < ε) (K : Nat)
    (hK : comparisonCutoff w extent ids ε ≤ K) :
    Q'.abs (quaternionHaar blocks (productDeficit w K extent ids)) ≤ ε :=
  Q'.le_trans' _ _ _ (quaternionHaar_abs_le_coefficientL1 _ _) (productDeficit_small hw0 hw1 extent ids ε hε K hK)

/-- Both directions of the ORIGINAL Haar comparison, at every later cutoff. -/
theorem original_weighted_haar_close {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) (ε : Q') (hε : (0 : Q') < ε) (K : Nat)
    (hK : comparisonCutoff w extent ids ε ≤ K) :
    heatProductHaar w blocks extent ids K ≤
        quaternionHaar blocks (polynomialProduct (weightedFace w (K + 1) extent) ids) + ε ∧
      quaternionHaar blocks (polynomialProduct (weightedFace w (K + 1) extent) ids) ≤
        heatProductHaar w blocks extent ids K + ε :=
  close_of_add_remainder
    (Q'.eqv_trans _ _ _ (haar_of_coeff_eqv blocks (original_eq_weighted_add_deficit w K extent ids))
      (quaternionHaar_append blocks _ _))
    (productDeficit_haar_small hw0 hw1 blocks extent ids ε hε K hK)

/-- Strict finite Jacobi floor transferred, with explicit error, to the
ORIGINAL unweighted interacting action on its original link carrier. -/
theorem productFloor_le_original_add {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat) (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (ε : Q') (hε : (0 : Q') < ε) (K : Nat) (hK : comparisonCutoff w extent ids ε ≤ K) :
    BF4ExactSlabJacobiHaarFloor.productFloor w ids ≤
      heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids K + ε :=
  Q'.le_trans' _ _ _ (productFloor_le_weightedHaar hw0 hw1 (K + 1) extent (by omega) ids hids)
    (original_weighted_haar_close hw0 hw1 _ extent ids ε hε K hK).2

end YMGap.Continuum.BF4ExactSlabJacobiProductComparison

#print axioms YMGap.Continuum.BF4ExactSlabJacobiProductComparison.comparisonCutoff
#print axioms YMGap.Continuum.BF4ExactSlabJacobiProductComparison.productDeficit
#print axioms YMGap.Continuum.BF4ExactSlabJacobiProductComparison.original_eq_weighted_add_deficit
#print axioms YMGap.Continuum.BF4ExactSlabJacobiProductComparison.productDeficit_small
#print axioms YMGap.Continuum.BF4ExactSlabJacobiProductComparison.productDeficit_haar_small
#print axioms YMGap.Continuum.BF4ExactSlabJacobiProductComparison.original_weighted_haar_close
#print axioms YMGap.Continuum.BF4ExactSlabJacobiProductComparison.productFloor_le_original_add
