/-
# Local channel selection with the ORIGINAL spectator interface retained

For each actual crossing face, keep its entire original Gram expansion or
select its existing unit/fundamental-coordinate leaf. The latter uses the
original heat coefficient; the former keeps ALL representation channels
through the supplied cutoff. The dependent face list and all overlapping
lower-action variables are unchanged.

The resulting forest gives a lower bound for the ORIGINAL reflected raw
form, including every rational recentering. Keeping every face restores
that form exactly. This repairs the scope of channel retention needed for
a volume-stable excitation estimate: spectators need not be frozen to
their unit leaves. No local minor floor, normalized volume-uniform bound
or thermodynamic excitation is yet asserted.
-/

import YMGap.Continuum.ReflectedSquareTreePruning
import YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels
import YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor

namespace YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor
open YMGap.Continuum.ReflectedSquareTreePruning
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

/-- Outer none keeps the full face; some none selects only its unit leaf. -/
abbrev PartialChoice := Option CoordinateChoice

variable {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) (hK : 1 ≤ K)

def faceTree {half id : Nat} (hi : id ∈ centralFixedFaceIds half) : PartialChoice → SquareTree
  | none => (faceExpansion hw K hi).tree
  | some c => let l := (faceChoice hw K hK hi c).leaf; .term l.weight l.channel

def facePruning {half id : Nat} (hi : id ∈ centralFixedFaceIds half) : (c : PartialChoice) →
    Pruning (faceTree hw K hK hi c) (faceExpansion hw K hi).tree
  | none => .keep _
  | some c => .ofLeaf (faceChoice hw K hK hi c).leaf

theorem faceTree_unselected {half id : Nat} (hi : id ∈ centralFixedFaceIds half) :
    faceTree hw K hK hi none = (faceExpansion hw K hi).tree := rfl

theorem faceTree_selected {half id : Nat} (hi : id ∈ centralFixedFaceIds half) (c : CoordinateChoice) :
    faceTree hw K hK hi (some c) =
      .term (faceChoice hw K hK hi c).leaf.weight (faceChoice hw K hK hi c).leaf.channel := rfl

def partialProduct (half : Nat) (choice : Nat → PartialChoice) :
    (ids : List Nat) → (∀ id, id ∈ ids → id ∈ centralFixedFaceIds half) → SquareTree
  | [], _ => .term 1 polyOne
  | id :: ids, hi => (faceTree hw K hK (hi id List.mem_cons_self) (choice id)).product
      (partialProduct half choice ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

def productPruning (half : Nat) (choice : Nat → PartialChoice) :
    (ids : List Nat) → (hi : ∀ id, id ∈ ids → id ∈ centralFixedFaceIds half) →
    Pruning (partialProduct hw K hK half choice ids hi)
      (LocalSquareExpansion.finiteProduct (faceHeatPolynomial w K half) ids
        (fun id hid => faceExpansion hw K (hi id hid))).tree
  | [], _ => .keep _
  | id :: ids, hi => (facePruning hw K hK (hi id List.mem_cons_self) (choice id)).product
      (productPruning half choice ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

def retainedInterface (half : Nat) (choice : Nat → PartialChoice) : SquareTree :=
  partialProduct hw K hK half choice (centralFixedFaceIds half) (fun _ hi => hi)

/-- Type-valued retention certificate for the SAME original interface tree. -/
def interfacePruning (half : Nat) (choice : Nat → PartialChoice) :
    Pruning (retainedInterface hw K hK half choice) (interfaceExpansion hw K half).tree :=
  productPruning hw K hK half choice _ (fun _ hi => hi)

theorem retainedInterface_nonnegative (half : Nat) (choice : Nat → PartialChoice) :
    (retainedInterface hw K hK half choice).Nonnegative :=
  (interfacePruning hw K hK half choice).nonnegative (interfaceExpansion hw K half).weightsNonnegative

def retainedValue {half : Nat} (choice : Nat → PartialChoice) (e : PlaquetteExpression half) : Q' :=
  haarSquareSum (boundaryCompleteSlabLinks (centralExtent half)).length
    ((retainedInterface hw K hK half choice).multiplyTerm 1 (dressedLower w K e))

/-- Full original lower heat product retained; no independence or new state. -/
theorem retainedValue_le_rawForm {half : Nat} (choice : Nat → PartialChoice) (e : PlaquetteExpression half) :
    retainedValue hw K hK choice e ≤ rawForm w K e e :=
  Q'.le_trans' _ _ _
    ((interfacePruning hw K hK half choice).dressed_value_le (interfaceExpansion hw K half).weightsNonnegative
      (boundaryCompleteSlabLinks (centralExtent half)).length (dressedLower w K e))
    (Q'.ge_of_eqv (rawForm_eq_dressedSquareSum w hw K half e))

theorem retainedValue_recentered_le {half : Nat} (choice : Nat → PartialChoice)
    (e : PlaquetteExpression half) (c : Q') :
    retainedValue hw K hK choice (recentered half e c) ≤
      rawForm w K (recentered half e c) (recentered half e c) :=
  retainedValue_le_rawForm hw K hK choice _

theorem partialProduct_keepAll (half : Nat) :
    (ids : List Nat) → (hi : ∀ id, id ∈ ids → id ∈ centralFixedFaceIds half) →
    partialProduct hw K hK half (fun _ => none) ids hi =
      (LocalSquareExpansion.finiteProduct (faceHeatPolynomial w K half) ids
        (fun id hid => faceExpansion hw K (hi id hid))).tree
  | [], _ => rfl
  | id :: ids, hi => by
      change (faceExpansion hw K (hi id List.mem_cons_self)).tree.product _ = _
      rw [partialProduct_keepAll half ids (fun j hj => hi j (List.mem_cons_of_mem id hj))]
      rfl

theorem retainedInterface_keepAll (half : Nat) :
    retainedInterface hw K hK half (fun _ => none) = (interfaceExpansion hw K half).tree :=
  partialProduct_keepAll hw K hK half _ (fun _ hi => hi)

/-- The no-selection endpoint is the original reflected numerator exactly. -/
theorem retainedValue_keepAll {half : Nat} (e : PlaquetteExpression half) :
    Q'.eqv (retainedValue hw K hK (fun _ => none) e) (rawForm w K e e) := by
  unfold retainedValue
  rw [retainedInterface_keepAll]
  exact Q'.eqv_symm (rawForm_eq_dressedSquareSum w hw K half e)

end YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention

#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention.faceTree
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention.facePruning
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention.faceTree_unselected
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention.faceTree_selected
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention.partialProduct
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention.productPruning
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention.retainedInterface
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention.interfacePruning
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention.retainedInterface_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention.retainedValue
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention.retainedValue_le_rawForm
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention.retainedValue_recentered_le
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention.partialProduct_keepAll
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention.retainedInterface_keepAll
#print axioms YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention.retainedValue_keepAll
