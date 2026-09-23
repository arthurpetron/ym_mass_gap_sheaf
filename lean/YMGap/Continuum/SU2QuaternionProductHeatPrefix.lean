/-
# Prefix support and the one-head lift recurrence for product heat

The prefix of the product heat occupies the original source blocks together
with precisely the fresh blocks which it has introduced.  Adjoining a new
head block shifts the previous prefix and exposes the first heat factor.
-/

import YMGap.Continuum.SU2QuaternionProductHeatMarginals
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex
import YMGap.Continuum.QuaternionHaarWordLift

namespace YMGap.Continuum.SU2QuaternionProductHeatPrefix

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWordLift
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

private theorem heatProduct_supported (blocks : Nat) (left right : Nat → Nat)
    (w : Q') (K : Nat) : ∀ ids : List Nat,
    (∀ i, i ∈ ids → left i < blocks) →
    (∀ i, i ∈ ids → right i < blocks) →
    SupportedQuaternionBlocks blocks
      (polynomialProduct (fun i => heatAt (left i) (right i) w K) ids)
  | [], _, _ => supported_one _
  | i :: ids, hl, hr => supported_polyMul
      (heat_supported (hl i List.mem_cons_self) (hr i List.mem_cons_self) w K)
      (heatProduct_supported blocks left right w K ids
        (fun j hj => hl j (List.mem_cons_of_mem i hj))
        (fun j hj => hr j (List.mem_cons_of_mem i hj)))

theorem productHeat_prefix_supported (n : Nat) (w : Q') (K m : Nat) :
    SupportedQuaternionBlocks (n+m) (productHeat n w K (List.range m)) := by
  unfold productHeat
  exact heatProduct_supported (n+m) (fun i => i) (fun i => n+i) w K
    (List.range m)
    (fun i hi => by dsimp; have := List.mem_range.mp hi; omega)
    (fun i hi => by dsimp; have := List.mem_range.mp hi; omega)

private theorem lift_scalarAt (a b : Nat) :
    liftHead (scalarAt a b) = scalarAt (a+1) (b+1) := by
  change (liftQuaternion 1 (PolyQuaternion.mul (PolyQuaternion.coordinateVariable a)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable b)))).scalar = _
  simp only [liftQuaternion_mul, liftQuaternion_conj,
    liftQuaternion_coordinateVariable]
  change scalarAt (1+a) (1+b) = scalarAt (a+1) (b+1)
  rw [Nat.add_comm 1 a, Nat.add_comm 1 b]

private theorem lift_heatAt (blocks a b : Nat) (w : Q') (K : Nat) :
    PaddedPolynomialCoeffEqv blocks (liftHead (heatAt a b w K))
      (heatAt (a+1) (b+1) w K) := by
  unfold heatAt
  change PaddedPolynomialCoeffEqv blocks
    (liftBoundary 1 (finitePolySum _ (List.range (K+1)))) _
  induction List.range (K+1) with
  | nil => exact .refl _ _
  | cons spin spins ih =>
      change PaddedPolynomialCoeffEqv blocks
        (liftBoundary 1 (polyAdd _ _)) (polyAdd _ _)
      rw [lift_add, lift_smul]
      have hs := lift_character blocks 1 (scalarAt a b) spin
      change PaddedPolynomialCoeffEqv blocks
        (liftHead (characterPolynomial (scalarAt a b) spin))
        (characterPolynomial (liftHead (scalarAt a b)) spin) at hs
      rw [lift_scalarAt] at hs
      exact (hs.smul _).add ih

private theorem lift_productHeat_list (blocks n : Nat) (w : Q') (K : Nat) :
    ∀ ids : List Nat,
      PaddedPolynomialCoeffEqv blocks
        (liftHead (polynomialProduct (fun i => heatAt i (n+i) w K) ids))
        (polynomialProduct (fun i => heatAt (i+1) (n+i+1) w K) ids)
  | [] => lift_one blocks 1
  | i :: ids => by
      change PaddedPolynomialCoeffEqv blocks
        (liftHead (polyMul (heatAt i (n+i) w K)
          (polynomialProduct (fun j => heatAt j (n+j) w K) ids))) _
      rw [liftHead_mul]
      exact (lift_heatAt blocks i (n+i) w K).mul
        (lift_productHeat_list blocks n w K ids)

private theorem productHeat_map_succ (n : Nat) (w : Q') (K : Nat) :
    ∀ ids : List Nat,
      polynomialProduct (fun i => heatAt i (n+i) w K) (ids.map Nat.succ) =
        polynomialProduct (fun i => heatAt (i+1) (n+i+1) w K) ids
  | [] => rfl
  | _ :: ids => by
      change polyMul _ (polynomialProduct _ (ids.map Nat.succ)) =
        polyMul _ (polynomialProduct _ ids)
      rw [productHeat_map_succ n w K ids]
      simp only [Nat.add_assoc]

theorem productHeat_prefix_succ_carrier (n : Nat) (w : Q') (K m : Nat) :
    HaarCarrierEqv (n+(m+1))
      (productHeat n w K (List.range (m+1)))
      (polyMul (heatAt 0 n w K)
        (liftHead (productHeat n w K (List.range m)))) := by
  rw [List.range_succ_eq_map]
  unfold productHeat
  change HaarCarrierEqv (n+(m+1))
    (polyMul (heatAt 0 n w K)
      (polynomialProduct (fun i => heatAt i (n+i) w K)
        ((List.range m).map Nat.succ))) _
  rw [productHeat_map_succ]
  have hp := lift_productHeat_list (n+(m+1)) n w K (List.range m)
  have hs : SupportedHaarEqv (n+(m+1))
      (polyMul (heatAt 0 n w K)
        (polynomialProduct (fun i => heatAt (i+1) (n+i+1) w K) (List.range m)))
      (polyMul (heatAt 0 n w K)
        (liftHead (polynomialProduct (fun i => heatAt i (n+i) w K) (List.range m)))) :=
    SupportedHaarEqv.of_padded
      ((PaddedPolynomialCoeffEqv.refl (n+(m+1)) (heatAt 0 n w K)).mul hp.symm)
      (supported_polyMul (heat_supported (by omega) (by omega) w K)
        (heatProduct_supported (n+(m+1)) (fun i => i+1) (fun i => n+i+1) w K
          (List.range m)
          (fun i hi => by dsimp; have := List.mem_range.mp hi; omega)
          (fun i hi => by dsimp; have := List.mem_range.mp hi; omega)))
      (supported_polyMul (heat_supported (by omega) (by omega) w K)
        (lift_supported (productHeat_prefix_supported n w K m) 1))
  exact carrier_of_supported
    (supported_polyMul (heat_supported (by omega) (by omega) w K)
      (heatProduct_supported (n+(m+1)) (fun i => i+1) (fun i => n+i+1) w K
        (List.range m)
        (fun i hi => by dsimp; have := List.mem_range.mp hi; omega)
        (fun i hi => by dsimp; have := List.mem_range.mp hi; omega)))
    (supported_polyMul (heat_supported (by omega) (by omega) w K)
      (lift_supported (productHeat_prefix_supported n w K m) 1)) hs

end YMGap.Continuum.SU2QuaternionProductHeatPrefix

#print axioms YMGap.Continuum.SU2QuaternionProductHeatPrefix.productHeat_prefix_supported
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPrefix.productHeat_prefix_succ_carrier
