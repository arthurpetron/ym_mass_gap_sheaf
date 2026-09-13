/-
# A retained ORIGINAL interface channel gives a quantitative action bound

Every actual crossing heat expansion contains the degree-zero real tensor
channel, with original coefficient one. Explicit leaf paths survive all face
products. Discarding other nonnegative channels yields the square of the
original lower observable's Haar integral as a lower bound for the FULL
signed quadratic, at every finite cutoff and odd extent, w >= 0.

For the all-label unit this is Z_K >= (Haar lowerHeatProduct_K)^2, with all
spatial interactions and shared links retained in the lower integral. No
nonzero estimate for that integral, positive limit floor, uniform spectral
bound or physical vacuum stationarity is asserted.
-/

import YMGap.Continuum.ReflectedSquareTreeRetainedChannel
import YMGap.Continuum.BF4ExactSlabAllExtentActionLimit

namespace YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentBoundaryCutoffRecoding
open YMGap.Continuum.BF4ExactSlabAllExtentFiniteBoundaryObservable
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.BondMovingStep

local infix:50 " ≈ " => Q'.eqv

/-- The zero-degree real column is literally one, for every quaternion polynomial. -/
def gramZeroUnit (q : RationalQuaternionRatPoly.RatPolyQuaternion) : UnitLeaf (gramSquares q 0) := by
  change UnitLeaf (.add .zero
    ((SquareTree.add (.term 1 polyOne) (.term 1 polyZero)).scale (basisInverseWeight 0 0)))
  exact UnitLeaf.right ((UnitLeaf.left UnitLeaf.one).scale _ (by decide))

private theorem sum_tree {A : Type} {half : Nat} (f : A → RatPoly) (g : A → SquareTree) :
    (xs : List A) → (h : ∀ a, a ∈ xs → LocalSquareExpansion half (f a)) →
    (hg : ∀ a (ha : a ∈ xs), (h a ha).tree = g a) →
    (LocalSquareExpansion.finiteSum f xs h).tree = SquareTree.sum g xs
  | [], _, _ => rfl
  | a :: xs, h, hg => by
      change SquareTree.add (h a List.mem_cons_self).tree _ = SquareTree.add (g a) _
      rw [hg a List.mem_cons_self,
        sum_tree f g xs (fun b hb => h b (List.mem_cons_of_mem a hb))
          (fun b hb => hg b (List.mem_cons_of_mem a hb))]

/-- The retained degree-zero heat coefficient is the original one, not a lower proxy. -/
def faceUnit {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) {half id : Nat}
    (hi : id ∈ centralFixedFaceIds half) : UnitLeaf (faceExpansion hw K hi).tree := by
  have he : (faceExpansion hw K hi).tree = SquareTree.sum
      (fun spin => (gramSquares (asRepresentationQuaternion (correctedSlabLinkPolynomial (centralExtent half)
        (faceLinkA (slabPlaquetteAt (centralExtent half) id)))) spin).scale
          (SU2CharacterVacuumHaar.coeffAt (heatKernelPacket K w) spin)) (List.range (K + 1)) :=
    sum_tree _ _ _ _ (fun _ _ => rfl)
  rw [he, List.range_succ_eq_map]
  apply UnitLeaf.left
  apply UnitLeaf.scale
  · rw [coeffAt_heatKernelPacket (Nat.succ_pos K), coeffW_zero]
    exact Q'.eqv_refl _
  · exact gramZeroUnit _

def productUnit {A : Type} {half : Nat} (f : A → RatPoly) :
    (xs : List A) → (h : ∀ a, a ∈ xs → LocalSquareExpansion half (f a)) →
    (u : ∀ a (ha : a ∈ xs), UnitLeaf (h a ha).tree) →
    UnitLeaf (LocalSquareExpansion.finiteProduct f xs h).tree
  | [], _, _ => UnitLeaf.one
  | a :: xs, h, u => (u a List.mem_cons_self).product
      (productUnit f xs (fun b hb => h b (List.mem_cons_of_mem a hb))
        (fun b hb => u b (List.mem_cons_of_mem a hb)))

/-- Type-level path to the all-trivial interface channel on the actual face list. -/
def interfaceUnit {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) :
    UnitLeaf (interfaceExpansion hw K half).tree :=
  productUnit _ _ (fun _ hi => faceExpansion hw K hi) (fun _ hi => faceUnit hw K hi)

theorem reflectedInterface_lower_square {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) :
    quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length p *
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length p ≤
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
        (reflectedInterfacePolynomial w K half p) :=
  Q'.le_trans' _ _ _
    ((interfaceUnit hw K half).observable_square_le (interfaceExpansion hw K half).weightsNonnegative _ p)
    (Q'.ge_of_eqv (reflectedInterfaceExpansion hw K half p hp hl).haar_eq_squareValue)

theorem finiteForm_lower_square {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) {half : Nat}
    (a : BoundaryObservable half) :
    quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (lowerObservable w K half a.coefficient) *
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (lowerObservable w K half a.coefficient) ≤
      finiteForm w K a a :=
  Q'.le_trans' _ _ _
    (reflectedInterface_lower_square hw K half _ (lowerObservable_support w K half a.coefficient)
      (lowerObservable_local w K half a.coefficient))
    (Q'.ge_of_eqv (exact_quadratic_eq_reflectedInterfaceHaar hw K half a.coefficient))

def lowerActionValue (w : Q') (K half : Nat) : Q' :=
  quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (lowerHeatProduct w K half)

/-- A genuine finite lower estimate for the ORIGINAL full interacting action. -/
theorem fullAction_lower_square {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) :
    lowerActionValue w K half * lowerActionValue w K half ≤ fullActionValue w K half := by
  have hp := (lowerObservable_extension w (Nat.le_refl K) half (fun _ => 1)).trans (lowerObservable_one w K half)
  have hh := haar_of_coeff_eqv (boundaryCompleteSlabLinks (centralExtent half)).length hp
  have hsq := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hh) (Q'.mul_eqv_congr_left _ _ _ hh)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsq)
    (Q'.le_trans' _ _ _ (finiteForm_lower_square hw K (heatUnitCode K half))
      (Q'.le_of_eqv (heatUnitCode_full_action w K half)))

end YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel.gramZeroUnit
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel.faceUnit
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel.productUnit
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel.interfaceUnit
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel.reflectedInterface_lower_square
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel.finiteForm_lower_square
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel.lowerActionValue
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel.fullAction_lower_square
