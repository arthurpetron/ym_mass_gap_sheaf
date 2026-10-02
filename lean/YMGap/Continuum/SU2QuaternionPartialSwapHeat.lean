/-
# Partial-slice symmetry of a selected product heat kernel

The selected heat factors are unchanged when precisely their lower and upper
quaternion blocks are exchanged. This is the symmetry needed for a positive
spectator-channel Bessel deficit. No unselected coordinate is heat-evolved.
-/

import YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy
import YMGap.Continuum.SU2QuaternionPartialSliceSwap

namespace YMGap.Continuum.SU2QuaternionPartialSwapHeat

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionPartialSliceSwap

private theorem productHeat_partialSwap_subset (n : Nat) (w : Q') (K : Nat)
    (mask : List Nat) :
    ∀ ids : List Nat,
      (∀ i, i ∈ ids → i < n) →
      (∀ i, i ∈ ids → i ∈ mask) →
      PaddedPolynomialCoeffEqv (n+n)
        (reindexQuaternionPolynomial (swap n mask) (productHeat n w K ids))
        (productHeat n w K ids)
  | [], _, _ => PaddedPolynomialCoeffEqv.of_prefix (reindex_polyOne_prefix _)
  | i::ids, hids, hmask => by
      have hi : i < n := hids i List.mem_cons_self
      have him : i ∈ mask := hmask i List.mem_cons_self
      have hlo : (swap n mask).map i = n+i := by
        rw [swap_lower n mask i hi]
        simp only [if_pos him]
      have hupp : (swap n mask).map (n+i) = i := by
        rw [swap_upper n mask i hi]
        simp only [if_pos him]
      have hp : QuaternionPrefixPolyQuaternionEqv (n+n)
          (reindexPolyQuaternion (swap n mask)
            (PolyQuaternion.mul (PolyQuaternion.coordinateVariable i)
              (PolyQuaternion.conj (PolyQuaternion.coordinateVariable (n+i)))))
          (PolyQuaternion.mul (PolyQuaternion.coordinateVariable (n+i))
            (PolyQuaternion.conj (PolyQuaternion.coordinateVariable i))) := by
        rw [reindexPolyQuaternion_mul, reindexPolyQuaternion_conj]
        exact (reindex_coordinateVariable_prefix (swap n mask) (by omega) hupp).mul
          (reindex_coordinateVariable_prefix (swap n mask) (by omega) hlo).conj
      have hc (spin : Nat) : PaddedPolynomialCoeffEqv (n+n)
          (reindexQuaternionPolynomial (swap n mask)
            (characterPolynomial (scalarAt i (n+i)) spin))
          (characterPolynomial (scalarAt (n+i) i) spin) :=
        (PaddedPolynomialCoeffEqv.of_prefix
          (reindexQuaternionPolynomial_character_prefix (swap n mask) _ spin)).trans
          ((PaddedPolynomialCoeffEqv.of_prefix hp.scalar).character spin)
      have hk : PaddedPolynomialCoeffEqv (n+n)
          (reindexQuaternionPolynomial (swap n mask) (heatAt i (n+i) w K))
          (heatAt i (n+i) w K) := by
        apply PaddedPolynomialCoeffEqv.trans (q := heatAt (n+i) i w K) ?_
          (PaddedPolynomialCoeffEqv.of_coeff (heatAt_symm (n+i) i w K))
        unfold heatAt
        induction List.range (K+1) with
        | nil => exact .refl _ _
        | cons s ss ih =>
            simp only [finitePolySum, reindexQuaternionPolynomial_add,
              reindexQuaternionPolynomial_smul]
            exact ((hc s).smul _).add ih
      change PaddedPolynomialCoeffEqv (n+n)
        (reindexQuaternionPolynomial (swap n mask)
          (polyMul (heatAt i (n+i) w K) (productHeat n w K ids))) _
      rw [reindexQuaternionPolynomial_mul]
      exact hk.mul (productHeat_partialSwap_subset n w K mask ids
        (fun j hj => hids j (List.mem_cons_of_mem i hj))
        (fun j hj => hmask j (List.mem_cons_of_mem i hj)))

/-- The selected kernel is symmetric under exchange of exactly its selected
lower/upper blocks, with every unselected block fixed. -/
theorem productHeat_partialSwap (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n) :
    PaddedPolynomialCoeffEqv (n+n)
      (reindexQuaternionPolynomial (swap n ids) (productHeat n w K ids))
      (productHeat n w K ids) :=
  productHeat_partialSwap_subset n w K ids ids hids (fun _ hi => hi)

/-- Any subset of lower/upper pairs may be exchanged. Factors outside the
mask are FIXED, not erased; factors inside it use exact heat symmetry. -/
theorem productHeat_partialSwap_mask (n : Nat) (w : Q') (K : Nat)
    (mask : List Nat) :
    ∀ ids : List Nat, (∀ i, i ∈ ids → i < n) →
      PaddedPolynomialCoeffEqv (n+n)
        (reindexQuaternionPolynomial (swap n mask) (productHeat n w K ids))
        (productHeat n w K ids)
  | [], _ => PaddedPolynomialCoeffEqv.of_prefix (reindex_polyOne_prefix _)
  | i::ids, hids => by
      have hi : i < n := hids i List.mem_cons_self
      have hk : PaddedPolynomialCoeffEqv (n+n)
          (reindexQuaternionPolynomial (swap n mask) (heatAt i (n+i) w K))
          (heatAt i (n+i) w K) := by
        by_cases hm : i ∈ mask
        · have hs := productHeat_partialSwap_subset n w K mask [i]
            (fun j hj => (List.mem_singleton.mp hj) ▸ hi)
            (fun j hj => (List.mem_singleton.mp hj) ▸ hm)
          have he : RatPolyCoeffEqv (productHeat n w K [i]) (heatAt i (n+i) w K) :=
            RatPolyCoeffEqv.mul_one _
          have hr : PaddedPolynomialCoeffEqv (n+n)
              (reindexQuaternionPolynomial (swap n mask) (productHeat n w K [i]))
              (reindexQuaternionPolynomial (swap n mask) (heatAt i (n+i) w K)) := by
            change PaddedPolynomialCoeffEqv (n+n)
              (reindexQuaternionPolynomial (swap n mask)
                (polyMul (heatAt i (n+i) w K) polyOne)) _
            rw [reindexQuaternionPolynomial_mul]
            exact ((PaddedPolynomialCoeffEqv.refl _ _).mul
              (PaddedPolynomialCoeffEqv.of_prefix (reindex_polyOne_prefix _))).trans
              (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.mul_one _))
          exact hr.symm.trans (hs.trans (PaddedPolynomialCoeffEqv.of_coeff he))
        · have hlo : (swap n mask).map i = i := by
            rw [swap_lower n mask i hi, if_neg hm]
          have hupp : (swap n mask).map (n+i) = n+i := by
            rw [swap_upper n mask i hi, if_neg hm]
          have hp : QuaternionPrefixPolyQuaternionEqv (n+n)
              (reindexPolyQuaternion (swap n mask)
                (PolyQuaternion.mul (PolyQuaternion.coordinateVariable i)
                  (PolyQuaternion.conj (PolyQuaternion.coordinateVariable (n+i)))))
              (PolyQuaternion.mul (PolyQuaternion.coordinateVariable i)
                (PolyQuaternion.conj (PolyQuaternion.coordinateVariable (n+i)))) := by
            rw [reindexPolyQuaternion_mul, reindexPolyQuaternion_conj]
            exact (reindex_coordinateVariable_prefix (swap n mask) (by omega) hlo).mul
              (reindex_coordinateVariable_prefix (swap n mask) (by omega) hupp).conj
          have hc (spin : Nat) : PaddedPolynomialCoeffEqv (n+n)
              (reindexQuaternionPolynomial (swap n mask)
                (characterPolynomial (scalarAt i (n+i)) spin))
              (characterPolynomial (scalarAt i (n+i)) spin) :=
            (PaddedPolynomialCoeffEqv.of_prefix
              (reindexQuaternionPolynomial_character_prefix (swap n mask) _ spin)).trans
              ((PaddedPolynomialCoeffEqv.of_prefix hp.scalar).character spin)
          unfold heatAt
          induction List.range (K+1) with
          | nil => exact .refl _ _
          | cons s ss ih =>
              simp only [finitePolySum, reindexQuaternionPolynomial_add,
                reindexQuaternionPolynomial_smul]
              exact ((hc s).smul _).add ih
      change PaddedPolynomialCoeffEqv (n+n)
        (reindexQuaternionPolynomial (swap n mask)
          (polyMul (heatAt i (n+i) w K) (productHeat n w K ids))) _
      rw [reindexQuaternionPolynomial_mul]
      exact hk.mul (productHeat_partialSwap_mask n w K mask ids
        (fun j hj => hids j (List.mem_cons_of_mem i hj)))

#print axioms productHeat_partialSwap
#print axioms productHeat_partialSwap_mask

end YMGap.Continuum.SU2QuaternionPartialSwapHeat
