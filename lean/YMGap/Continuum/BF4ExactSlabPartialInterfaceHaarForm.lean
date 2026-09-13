/-
# Exact ORIGINAL Haar integrands for partially retained interface tests

Unselected crossing faces keep their full original spatial Gram heat factor.
A selected face contributes its actual weight times the reflected square of
its coefficient-pinned unit/fundamental polynomial. Their product is pinned
to the existing retained tree, with support and lower locality inherited
from the original expansion. Mixed Haar pairings therefore equal the actual
whole-forest test amplitudes and reference energies.

All lower interactions remain in dressedLower. This is a same-object
identity, not a positive local minor or a thermodynamic excitation estimate.
-/

import YMGap.Continuum.BF4ExactSlabPartialInterfaceTests
import YMGap.Continuum.QuaternionHaarUnitScalarSquare

namespace YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabLowerChannelLocality
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabLocalBilinearChannels
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity
open YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels
open YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention
open YMGap.Continuum.BF4ExactSlabPartialInterfaceTests
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.ReflectedSquareTreePruning
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

theorem pruning_supported (blockCount : Nat) : {s t : SquareTree} → Pruning s t →
    SquareTreeSupported blockCount t → SquareTreeSupported blockCount s
  | _, _, .keep _, h => h
  | _, _, .discard _, _ => True.intro
  | _, _, .left p, h => pruning_supported blockCount p h.1
  | _, _, .right p, h => pruning_supported blockCount p h.2
  | _, _, .add p q, h => ⟨pruning_supported blockCount p h.1, pruning_supported blockCount q h.2⟩
  | _, _, .trans p q, h => pruning_supported blockCount p (pruning_supported blockCount q h)

theorem pruning_lower (half : Nat) : {s t : SquareTree} → Pruning s t →
    LowerSquareTree half t → LowerSquareTree half s
  | _, _, .keep _, h => h
  | _, _, .discard _, _ => True.intro
  | _, _, .left p, h => pruning_lower half p h.1
  | _, _, .right p, h => pruning_lower half p h.2
  | _, _, .add p q, h => ⟨pruning_lower half p h.1, pruning_lower half q h.2⟩
  | _, _, .trans p q, h => pruning_lower half p (pruning_lower half q h)

theorem reflected_coeff (extent : Nat) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (reflectCorrectedSlabPolynomial extent p) (reflectCorrectedSlabPolynomial extent q) :=
  signSelectedPolynomial_coeffEqv _ _ (RatPolyCoeffEqv.reindex _ h)

def squareFactor (half : Nat) (weight : Q') (p : RatPoly) : RatPoly :=
  polySmul weight (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) p)

theorem squareFactor_coeff (half : Nat) {p q : RatPoly} {a b : Q'}
    (hp : RatPolyCoeffEqv p q) (hw : a ≈ b) : RatPolyCoeffEqv (squareFactor half a p) (squareFactor half b q) :=
  (((reflected_coeff _ hp).mul hp).smul a).trans (RatPolyCoeffEqv.smul_coefficient hw _)

theorem choice_supported (half id : Nat) (c : CoordinateChoice) :
    SupportedQuaternionBlocks (blocks half) (choicePolynomial half id c) := by
  cases c with
  | none => exact supported_one _
  | some pair =>
      obtain ⟨column, imaginary⟩ := pair
      have h := supported_slabLink (centralExtent half)
        (BF4ExactSlabPlaquettePathGram.faceLinkA (Z4HalfTimeReflectionFaceReindex.slabPlaquetteAt (centralExtent half) id))
      cases column <;> cases imaginary
      · exact h.scalar
      · exact h.iPart
      · exact h.jPart
      · exact h.kPart

def faceFactor (w : Q') (K half id : Nat) : PartialChoice → RatPoly
  | none => faceHeatPolynomial w K half id
  | some c => squareFactor half (choiceWeight w c) (choicePolynomial half id c)

variable {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) (hK : 1 ≤ K)

include hw in
theorem faceFactor_supported {half id : Nat} (hi : id ∈ centralFixedFaceIds half) :
    (c : PartialChoice) → SupportedQuaternionBlocks (blocks half) (faceFactor w K half id c)
  | none => (faceExpansion hw K hi).polynomialSupported
  | some c => supported_smul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) (choice_supported half id c)) _

theorem faceFactor_image {half id : Nat} (hi : id ∈ centralFixedFaceIds half) :
    (c : PartialChoice) → PaddedPolynomialCoeffEqv (blocks half) (faceFactor w K half id c)
      ((faceTree hw K hK hi c).eval (centralExtent half))
  | none => (faceExpansion hw K hi).image
  | some c => .of_coeff (squareFactor_coeff half (faceChoice hw K hK hi c).channel_pin
      (faceChoice hw K hK hi c).weight_pin).symm

theorem product_image (half : Nat) (choice : Nat → PartialChoice) :
    (ids : List Nat) → (hi : ∀ id, id ∈ ids → id ∈ centralFixedFaceIds half) →
    PaddedPolynomialCoeffEqv (blocks half) (polynomialProduct (fun id => faceFactor w K half id (choice id)) ids)
      ((partialProduct hw K hK half choice ids hi).eval (centralExtent half))
  | [], _ => (LocalSquareExpansion.one half).image
  | id :: ids, hi =>
      ((faceFactor_image hw K hK (hi id List.mem_cons_self) (choice id)).mul
        (product_image half choice ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))).trans
          (SquareTree.eval_product _ _ _)

include hw in
theorem product_supported (half : Nat) (choice : Nat → PartialChoice) :
    (ids : List Nat) → (∀ id, id ∈ ids → id ∈ centralFixedFaceIds half) →
    SupportedQuaternionBlocks (blocks half) (polynomialProduct (fun id => faceFactor w K half id (choice id)) ids)
  | [], _ => supported_one _
  | id :: ids, hi => supported_polyMul (faceFactor_supported hw K (hi id List.mem_cons_self) (choice id))
      (product_supported half choice ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

def retainedPolynomial (half : Nat) (choice : Nat → PartialChoice) : RatPoly :=
  polynomialProduct (fun id => faceFactor w K half id (choice id)) (centralFixedFaceIds half)

/-- The tree is definitionally the EXISTING retained interface. -/
def retainedExpansion (half : Nat) (choice : Nat → PartialChoice) :
    LocalSquareExpansion half (retainedPolynomial (w := w) K half choice) where
  tree := retainedInterface hw K hK half choice
  image := product_image hw K hK half choice _ (fun _ hi => hi)
  polynomialSupported := product_supported hw K half choice _ (fun _ hi => hi)
  treeSupported := pruning_supported _ (interfacePruning hw K hK half choice) (interfaceExpansion hw K half).treeSupported
  treeLower := pruning_lower half (interfacePruning hw K hK half choice) (interfaceExpansion hw K half).treeLower
  weightsNonnegative := retainedInterface_nonnegative hw K hK half choice

theorem retained_mixed_haar (half : Nat) (choice : Nat → PartialChoice) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks half) p) (hq : SupportedQuaternionBlocks (blocks half) q)
    (hlp : LowerLocal half p) (hlq : LowerLocal half q) :
    quaternionHaar (blocks half) (polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) q)
      (retainedPolynomial (w := w) K half choice)) ≈
        channelBilinearValue (blocks half) p q (retainedInterface hw K hK half choice) :=
  expansion_mixed_pairing (retainedExpansion hw K hK half choice) p q hp hq hlp hlq

theorem testAmplitude_haar (half : Nat) (choice : Nat → PartialChoice) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (blocks half) q) (hlq : LowerLocal half q) (e : PlaquetteExpression half) :
    testAmplitude hw K hK half choice q e ≈ quaternionHaar (blocks half)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) (dressedLower w K e)) q)
        (retainedPolynomial (w := w) K half choice)) :=
  Q'.eqv_symm (retained_mixed_haar hw K hK half choice _ q (dressedLower_supported w K e) hq
    ((lower_local e).mul (BF4ExactSlabAllExtentReflectionPositivity.lowerObservable_local w K half _)) hlq)

theorem referenceEnergy_haar (half : Nat) (choice : Nat → PartialChoice) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (blocks half) q) (hlq : LowerLocal half q) :
    referenceEnergy hw K hK half choice q ≈ quaternionHaar (blocks half)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) q) q)
        (retainedPolynomial (w := w) K half choice)) :=
  Q'.eqv_symm (retained_mixed_haar hw K hK half choice q q hq hq hlq hlq)

end YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm

#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm.pruning_supported
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm.pruning_lower
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm.reflected_coeff
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm.squareFactor_coeff
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm.choice_supported
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm.faceFactor_supported
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm.faceFactor_image
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm.product_image
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm.product_supported
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm.retainedExpansion
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm.retained_mixed_haar
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm.testAmplitude_haar
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm.referenceEnergy_haar
