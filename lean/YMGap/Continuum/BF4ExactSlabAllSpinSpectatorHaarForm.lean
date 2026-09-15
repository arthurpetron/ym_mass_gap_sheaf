/-
# Actual all-spin full-spectator integrands and original-form bounds

Each selected face contributes its original weighted reflected channel
square; every unselected face retains its full original Gram heat factor.
The product is pinned to the existing all-spin retained interface, with
actual carrier support and lower locality. Bulk interactions remain in
both dressed observables, independently of the crossing cutoff.

The mixed Haar form has its diagonal pinned to the existing original
channel energy. When the bulk cutoff retains the crossing packet, sharp
Cauchy--Schwarz bounds it by the two ORIGINAL full-action quadratic forms.
This is a norm-relative comparison, not a strict transfer contraction,
positive local minor, volume-limit construction or continuum theorem.
-/

import YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention
import YMGap.Continuum.BF4ExactSlabGrowingChannelPolynomial
import YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm

namespace YMGap.Continuum.BF4ExactSlabAllSpinSpectatorHaarForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm
open YMGap.Continuum.BF4ExactSlabLowerChannelLocality
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabLocalBilinearChannels
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels
open YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention
open YMGap.Continuum.BF4ExactSlabGrowingChannelPolynomial
open YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm (squareFactor squareFactor_coeff pruning_supported pruning_lower)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity
open YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit
open YMGap.Continuum.BF4ExactSlabWholePacketNormBound
open YMGap.Continuum.ReflectedSquareTreeTestForm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

def faceFactor (w : Q') (K half id : Nat) : Choice half K id → RatPoly
  | none => faceHeatPolynomial w K half id
  | some c => squareFactor half (faceWeight w c.val) (facePolynomial c.val)

variable {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat)

include hw in
theorem faceFactor_supported {half id : Nat} (hi : id ∈ centralFixedFaceIds half) :
    (c : Choice half K id) → SupportedQuaternionBlocks (blocks half) (faceFactor w K half id c)
  | none => (faceExpansion hw K hi).polynomialSupported
  | some c => supported_smul
      (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) (facePolynomial_supported c.val)) _

theorem faceFactor_image {half id : Nat} (hi : id ∈ centralFixedFaceIds half) :
    (c : Choice half K id) → PaddedPolynomialCoeffEqv (blocks half) (faceFactor w K half id c)
      ((faceTree hw K hi c).eval (centralExtent half))
  | none => (faceExpansion hw K hi).image
  | some c => .of_coeff (squareFactor_coeff half (faceChannel hw K hi c.val c.property).channel_pin
      (faceChannel hw K hi c.val c.property).weight_pin).symm

private theorem product_image (half : Nat) (choice : (id : Nat) → Choice half K id) :
    (ids : List Nat) → (hi : ∀ id, id ∈ ids → id ∈ centralFixedFaceIds half) →
    PaddedPolynomialCoeffEqv (blocks half) (polynomialProduct (fun id => faceFactor w K half id (choice id)) ids)
      ((partialProduct hw K half choice ids hi).eval (centralExtent half))
  | [], _ => (LocalSquareExpansion.one half).image
  | id :: ids, hi => ((faceFactor_image hw K (hi id List.mem_cons_self) (choice id)).mul
      (product_image half choice ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))).trans
        (SquareTree.eval_product _ _ _)

include hw in
private theorem product_supported (half : Nat) (choice : (id : Nat) → Choice half K id) :
    (ids : List Nat) → (∀ id, id ∈ ids → id ∈ centralFixedFaceIds half) →
    SupportedQuaternionBlocks (blocks half) (polynomialProduct (fun id => faceFactor w K half id (choice id)) ids)
  | [], _ => supported_one _
  | id :: ids, hi => supported_polyMul (faceFactor_supported hw K (hi id List.mem_cons_self) (choice id))
      (product_supported half choice ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

def retainedPolynomial (half : Nat) (choice : (id : Nat) → Choice half K id) : RatPoly :=
  polynomialProduct (fun id => faceFactor w K half id (choice id)) (centralFixedFaceIds half)

/-- Definitionally the existing all-spin tree, with its original polynomial pin. -/
def retainedExpansion (half : Nat) (choice : (id : Nat) → Choice half K id) :
    LocalSquareExpansion half (retainedPolynomial (w := w) K half choice) where
  tree := retainedInterface hw K half choice
  image := product_image hw K half choice _ (fun _ hi => hi)
  polynomialSupported := product_supported hw K half choice _ (fun _ hi => hi)
  treeSupported := pruning_supported _ (interfacePruning hw K half choice) (interfaceExpansion hw K half).treeSupported
  treeLower := pruning_lower half (interfacePruning hw K half choice) (interfaceExpansion hw K half).treeLower
  weightsNonnegative := retainedInterface_nonnegative hw K half choice

theorem retained_mixed_haar (half : Nat) (choice : (id : Nat) → Choice half K id) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks half) p) (hq : SupportedQuaternionBlocks (blocks half) q)
    (hlp : LowerLocal half p) (hlq : LowerLocal half q) :
    quaternionHaar (blocks half) (polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) q)
      (retainedPolynomial (w := w) K half choice)) ≈ channelBilinearValue (blocks half) p q (retainedInterface hw K half choice) :=
  expansion_mixed_pairing (retainedExpansion hw K half choice) p q hp hq hlp hlq

variable {half : Nat} (choice : (id : Nat) → Choice half K id)

def bulkPairing (B : Nat) (e f : PlaquetteExpression half) : Q' :=
  channelBilinearValue (blocks half) (dressedLower w B e) (dressedLower w B f) (retainedInterface hw K half choice)

theorem bulkPairing_haar (B : Nat) (e f : PlaquetteExpression half) :
    bulkPairing hw K choice B e f ≈ quaternionHaar (blocks half)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) (dressedLower w B e)) (dressedLower w B f))
        (retainedPolynomial (w := w) K half choice)) :=
  Q'.eqv_symm (retained_mixed_haar hw K half choice _ _ (dressedLower_supported w B e) (dressedLower_supported w B f)
    ((lower_local e).mul (BF4ExactSlabAllExtentReflectionPositivity.lowerObservable_local w B half _))
    ((lower_local f).mul (BF4ExactSlabAllExtentReflectionPositivity.lowerObservable_local w B half _)))

theorem bulkPairing_diagonal (B : Nat) (e : PlaquetteExpression half) :
    bulkPairing hw K choice B e e ≈ energySequence w B half (lower e) (retainedInterface hw K half choice) :=
  Q'.eqv_trans _ _ _ (diagonal_pin (blocks half) (dressedLower w B e) _) (dressed_energy_pin w B e _)

theorem bulkPairing_nonnegative (B : Nat) (e : PlaquetteExpression half) : (0 : Q') ≤ bulkPairing hw K choice B e e :=
  (treeForm (blocks half) _ (retainedInterface_nonnegative hw K half choice)).self_nonneg _

variable (hw0 : (0 : Q') < w)

include hw0 in
theorem bulkPairing_original_bound (B : Nat) (hB : K ≤ B) (e : PlaquetteExpression half) :
    bulkPairing hw K choice B e e ≤ originalQuadratic w B e :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (diagonal_pin (blocks half) (dressedLower w B e) _))
    (Q'.le_trans' _ _ _ ((interfacePruning hw K half choice).dressed_value_le
      (interfaceExpansion hw K half).weightsNonnegative (blocks half) (dressedLower w B e))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (dressed_energy_pin w B e _)) (wholePacket_finite_bound w hw0 e K B hB)))

include hw0 in
/-- Constant one, with both observables measured in the ORIGINAL full action. -/
theorem bulkPairing_squared_bound (B : Nat) (hB : K ≤ B) (e f : PlaquetteExpression half) :
    bulkPairing hw K choice B e f * bulkPairing hw K choice B e f ≤ originalQuadratic w B e * originalQuadratic w B f := by
  have he := bulkPairing_original_bound hw K choice hw0 B hB e
  have hf := bulkPairing_original_bound hw K choice hw0 B hB f
  exact Q'.le_trans' _ _ _ (cauchySchwarz (blocks half) _ (retainedInterface_nonnegative hw K half choice) _ _)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ he (bulkPairing_nonnegative hw K choice B f))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hf (Q'.le_trans' _ _ _ (bulkPairing_nonnegative hw K choice B e) he)))

end YMGap.Continuum.BF4ExactSlabAllSpinSpectatorHaarForm

#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorHaarForm.faceFactor
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorHaarForm.faceFactor_supported
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorHaarForm.faceFactor_image
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorHaarForm.retainedPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorHaarForm.retainedExpansion
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorHaarForm.retained_mixed_haar
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorHaarForm.bulkPairing
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorHaarForm.bulkPairing_haar
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorHaarForm.bulkPairing_diagonal
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorHaarForm.bulkPairing_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorHaarForm.bulkPairing_original_bound
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorHaarForm.bulkPairing_squared_bound
