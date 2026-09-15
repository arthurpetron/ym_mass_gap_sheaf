/-
# Arbitrary original channel squares with the complete spectator interface

The actual crossing-face list is partitioned by the supplied all-spin
selection. Its retained polynomial is exactly the selected positive heat
weight times a reflected polynomial square times every unselected original
heat factor. Common-padding coefficient equality is removed only after
proving support on the same physical Haar carrier.

The factorized mixed integral is pinned to the original retained pairing,
including both bulk-dressed observables. No independence of the factors,
positive interacting amplitude, normalized lower bound or volume-uniform
separating family is asserted.
-/

import YMGap.Continuum.BF4ExactSlabAllSpinSpectatorHaarForm
import YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization

namespace YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabLocalBilinearChannels
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels
open YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention
open YMGap.Continuum.BF4ExactSlabAllSpinSpectatorHaarForm
open YMGap.Continuum.BF4ExactSlabGrowingChannelPolynomial (facePolynomial_supported)
open YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm (squareFactor)
open YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization (squareFactor_product)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

variable {K half : Nat} (choice : (id : Nat) → Choice half K id)

def selectedIds : List Nat := (centralFixedFaceIds half).filter (fun id => (choice id).isSome)
def spectatorIds : List Nat := (centralFixedFaceIds half).filter (fun id => !(choice id).isSome)

theorem face_partition : (selectedIds choice ++ spectatorIds choice).Perm (centralFixedFaceIds half) :=
  List.filter_append_perm (fun id => (choice id).isSome) _

theorem spectatorIds_unselected {id : Nat} (hi : id ∈ spectatorIds choice) : choice id = none := by
  have h := (List.mem_filter.mp hi).2
  cases hc : choice id with
  | none => rfl
  | some c => simp only [hc, Option.isSome_some, Bool.not_true] at h; cases h

private def chosenPolynomial {id : Nat} : Choice half K id → RatPoly
  | none => polyOne
  | some c => facePolynomial c.val

private def chosenWeight (w : Q') {id : Nat} : Choice half K id → Q'
  | none => 1
  | some c => faceWeight w c.val

private def weightProduct (w : Q') : List Nat → Q'
  | [] => 1
  | id :: ids => chosenWeight w (choice id) * weightProduct w ids

def selectedPolynomial : RatPoly := polynomialProduct (fun id => chosenPolynomial (choice id)) (selectedIds choice)
def selectedWeight (w : Q') : Q' := weightProduct choice w (selectedIds choice)
def spectatorPolynomial (w : Q') : RatPoly := polynomialProduct (faceHeatPolynomial w K half) (spectatorIds choice)

def spectatorExpansion {w : Q'} (hw : (0 : Q') ≤ w) : LocalSquareExpansion half (spectatorPolynomial choice w) :=
  LocalSquareExpansion.finiteProduct _ _ (fun _ hi => faceExpansion hw K (List.mem_filter.mp hi).1)

theorem retained_factorization (w : Q') : RatPolyCoeffEqv (retainedPolynomial (w := w) K half choice)
    (polyMul (polynomialProduct (fun id => faceFactor w K half id (choice id)) (selectedIds choice))
      (spectatorPolynomial choice w)) := by
  let f := fun id => faceFactor w K half id (choice id)
  have hr : polynomialProduct f (spectatorIds choice) = spectatorPolynomial choice w :=
    polynomialProduct_congr _ _ _ (fun id hi => by
      simp only [f, spectatorIds_unselected choice hi, faceFactor])
  have h := (polynomialProduct_perm f (face_partition choice).symm).trans (polynomialProduct_append f _ _)
  rw [hr] at h
  exact h

private theorem selected_product (w : Q') : (ids : List Nat) →
    (∀ id, id ∈ ids → (choice id).isSome = true) →
    PaddedPolynomialCoeffEqv (blocks half)
      (polynomialProduct (fun id => faceFactor w K half id (choice id)) ids)
      (squareFactor half (weightProduct choice w ids) (polynomialProduct (fun id => chosenPolynomial (choice id)) ids))
  | [], _ => (LocalSquareExpansion.one half).image
  | id :: ids, hi => by
      have hh : PaddedPolynomialCoeffEqv (blocks half) (faceFactor w K half id (choice id))
          (squareFactor half (chosenWeight w (choice id)) (chosenPolynomial (choice id))) := by
        have hs := hi id List.mem_cons_self
        cases hc : choice id with
        | none => simp only [hc, Option.isSome_none] at hs; cases hs
        | some c => exact .refl _ _
      exact (hh.mul (selected_product w ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))).trans
        (squareFactor_product half _ _ _ _)

/-- The selected square and all spectators retain their original shared variables. -/
theorem retained_square_factorization (w : Q') : PaddedPolynomialCoeffEqv (blocks half)
    (retainedPolynomial (w := w) K half choice)
    (polyMul (squareFactor half (selectedWeight choice w) (selectedPolynomial choice)) (spectatorPolynomial choice w)) :=
  (PaddedPolynomialCoeffEqv.of_coeff (retained_factorization choice w)).trans
    ((selected_product choice w _ (fun _ hi => (List.mem_filter.mp hi).2)).mul (.refl _ _))

private theorem polynomial_supported : ∀ ids : List Nat,
    SupportedQuaternionBlocks (blocks half) (polynomialProduct (fun id => chosenPolynomial (choice id)) ids)
  | [] => supported_one _
  | id :: ids => by
      have h : SupportedQuaternionBlocks (blocks half) (chosenPolynomial (choice id)) := by
        cases choice id with
        | none => exact supported_one _
        | some c => exact facePolynomial_supported c.val
      exact supported_polyMul h (polynomial_supported ids)

theorem selectedPolynomial_supported : SupportedQuaternionBlocks (blocks half) (selectedPolynomial choice) :=
  polynomial_supported choice _

private theorem weight_positive (w : Q') (hw : (0 : Q') < w) : ∀ ids : List Nat, (0 : Q') < weightProduct choice w ids
  | [] => by change (0 : Q') < 1; decide
  | id :: ids => by
      have h : (0 : Q') < chosenWeight w (choice id) := by
        cases choice id with
        | none => change (0 : Q') < 1; decide
        | some c => exact faceWeight_positive w hw c.val
      exact Q'.mul_pos h (weight_positive w hw ids)

theorem selectedWeight_positive (w : Q') (hw : (0 : Q') < w) : (0 : Q') < selectedWeight choice w :=
  weight_positive choice w hw _

variable {w : Q'} (hw : (0 : Q') ≤ w)

include hw in
theorem factorized_supported : SupportedQuaternionBlocks (blocks half)
    (polyMul (squareFactor half (selectedWeight choice w) (selectedPolynomial choice)) (spectatorPolynomial choice w)) :=
  supported_polyMul (supported_smul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _)
    (selectedPolynomial_supported choice)) _) (spectatorExpansion choice hw).polynomialSupported

theorem factorized_mixed_haar (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks half) p) (hq : SupportedQuaternionBlocks (blocks half) q)
    (hlp : LowerLocal half p) (hlq : LowerLocal half q) :
    quaternionHaar (blocks half) (polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) q)
      (polyMul (squareFactor half (selectedWeight choice w) (selectedPolynomial choice)) (spectatorPolynomial choice w))) ≈
      channelBilinearValue (blocks half) p q (retainedInterface hw K half choice) := by
  have hs := supported_polyMul (reflectCorrectedSlabPolynomial_support (centralExtent half) p) hq
  have hi := ((PaddedPolynomialCoeffEqv.refl (blocks half) _).mul (retained_square_factorization choice w)).haar
    (supported_polyMul hs (retainedExpansion hw K half choice).polynomialSupported)
    (supported_polyMul hs (factorized_supported choice hw))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hi) (retained_mixed_haar hw K half choice p q hp hq hlp hlq)

end YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization

#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization.selectedIds
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization.spectatorIds
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization.face_partition
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization.spectatorIds_unselected
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization.selectedPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization.selectedWeight
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization.spectatorPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization.spectatorExpansion
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization.retained_factorization
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization.retained_square_factorization
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization.selectedPolynomial_supported
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization.selectedWeight_positive
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization.factorized_supported
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorFactorization.factorized_mixed_haar
