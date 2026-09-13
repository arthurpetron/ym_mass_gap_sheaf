/-
# Actual fundamental-coordinate channels in the original interface

Each quaternion coordinate is a coefficient-pinned leaf of the degree-one
representation Gram tree. Every original crossing face therefore contains
that coordinate with its exact original heat weight coeffW w 1 = 2*w^3.
Products construct actual interface leaves for arbitrary coordinate choices
on the physical face list; unselected faces retain their unit channel.

The polynomial and heat weight are independent of the truncation once K>=1.
Positive w makes these weights positive. This is NOT positivity of the
observable/unit amplitude minor: the interacting lower integrals still need
to be evaluated or bounded. No excitation, transfer or gap is asserted.
-/

import YMGap.Continuum.ReflectedSquareTreeRealizedLeaf
import YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel

namespace YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.ReflectedSquareTreeRealizedLeaf
open YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.BondMovingStep

/-- Column and real/imaginary bit enumerate r,i,j,k, respectively. -/
def coordinate (q : RatPolyQuaternion) (column imaginary : Bool) : RatPoly :=
  if column then (if imaginary then q.k else q.j) else (if imaginary then q.i else q.r)

theorem fundamental_column_entry (q : RatPolyQuaternion) (column : Bool) :
    ComplexCoeffEqv (polynomialColumn q 1 (if column then 1 else 0) false)
      (fundamentalMatrixCoefficient q false column) := by
  cases column
  · exact ((mul_one _).add (mul_zero _)).trans (add_zero _)
  · exact ((mul_zero _).add (mul_one _)).trans (zero_add _)

private def tensorEntryLeaf (x : PolyTensor 1) (imaginary : Bool) : Leaf (tensorSquares 1 x) :=
  .left (if imaginary then .right (.here 1 (x false).2) else .left (.here 1 (x false).1))

def gramCoordinateLeaf (q : RatPolyQuaternion) (column imaginary : Bool) : Leaf (gramSquares q 1) := by
  cases column
  · exact .left (.right ((tensorEntryLeaf (polynomialColumn q 1 0) imaginary).scale (basisInverseWeight 1 0)))
  · exact .right ((tensorEntryLeaf (polynomialColumn q 1 1) imaginary).scale (basisInverseWeight 1 1))

theorem gramCoordinateLeaf_weight (q : RatPolyQuaternion) (column imaginary : Bool) :
    (gramCoordinateLeaf q column imaginary).weight.eqv 1 := by
  cases column <;> cases imaginary <;> exact Q'.eqv_refl _

theorem gramCoordinateLeaf_channel (q : RatPolyQuaternion) (column imaginary : Bool) :
    RatPolyCoeffEqv (gramCoordinateLeaf q column imaginary).channel (coordinate q column imaginary) := by
  cases column <;> cases imaginary
  · exact (fundamental_column_entry q false).1
  · exact (fundamental_column_entry q false).2
  · exact (fundamental_column_entry q true).1
  · exact (fundamental_column_entry q true).2

def gramCoordinate (q : RatPolyQuaternion) (column imaginary : Bool) :
    RealizedLeaf (gramSquares q 1) (coordinate q column imaginary) 1 :=
  ⟨gramCoordinateLeaf q column imaginary, gramCoordinateLeaf_weight q column imaginary,
    gramCoordinateLeaf_channel q column imaginary⟩

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

def faceCoordinatePolynomial (half id : Nat) (column imaginary : Bool) : RatPoly :=
  coordinate (asRepresentationQuaternion (correctedSlabLinkPolynomial (centralExtent half)
    (faceLinkA (slabPlaquetteAt (centralExtent half) id)))) column imaginary

/-- The selected degree-one term of the ORIGINAL heat packet, at every K>=1. -/
def faceCoordinate {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) (hK : 1 ≤ K) {half id : Nat}
    (hi : id ∈ centralFixedFaceIds half) (column imaginary : Bool) :
    RealizedLeaf (faceExpansion hw K hi).tree (faceCoordinatePolynomial half id column imaginary) (coeffW w 1) := by
  let q := asRepresentationQuaternion (correctedSlabLinkPolynomial (centralExtent half)
    (faceLinkA (slabPlaquetteAt (centralExtent half) id)))
  let f := fun spin => (gramSquares q spin).scale (SU2CharacterVacuumHaar.coeffAt (heatKernelPacket K w) spin)
  have he : (faceExpansion hw K hi).tree = SquareTree.sum f (List.range (K + 1)) :=
    sum_tree _ _ _ _ (fun _ _ => rfl)
  rw [he]
  have hc := (gramCoordinate q column imaginary).scale (SU2CharacterVacuumHaar.coeffAt (heatKernelPacket K w) 1)
  have hwc : (SU2CharacterVacuumHaar.coeffAt (heatKernelPacket K w) 1 * 1).eqv (coeffW w 1) := by
    rw [coeffAt_heatKernelPacket (by omega : 1 < K + 1)]
    exact Q'.mul_one_eqv _
  exact (hc.reweight hwc).inSum f 1 (List.range (K + 1)) (List.mem_range.mpr (by omega))

abbrev CoordinateChoice := Option (Bool × Bool)

def choicePolynomial (half id : Nat) : CoordinateChoice → RatPoly
  | none => polyOne
  | some (column, imaginary) => faceCoordinatePolynomial half id column imaginary

def choiceWeight (w : Q') : CoordinateChoice → Q'
  | none => 1
  | some _ => coeffW w 1

def faceChoice {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) (hK : 1 ≤ K) {half id : Nat}
    (hi : id ∈ centralFixedFaceIds half) : (c : CoordinateChoice) →
    RealizedLeaf (faceExpansion hw K hi).tree (choicePolynomial half id c) (choiceWeight w c)
  | none => .ofUnit (faceUnit hw K hi)
  | some (column, imaginary) => faceCoordinate hw K hK hi column imaginary

def selectedPolynomial (half : Nat) (choice : Nat → CoordinateChoice) : List Nat → RatPoly
  | [] => polyOne
  | id :: ids => polyMul (choicePolynomial half id (choice id)) (selectedPolynomial half choice ids)

def selectedWeight (w : Q') (choice : Nat → CoordinateChoice) : List Nat → Q'
  | [] => 1
  | id :: ids => choiceWeight w (choice id) * selectedWeight w choice ids

private def productLeaf {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) (hK : 1 ≤ K) (half : Nat)
    (choice : Nat → CoordinateChoice) :
    (ids : List Nat) → (h : ∀ id, id ∈ ids → id ∈ centralFixedFaceIds half) →
    RealizedLeaf (LocalSquareExpansion.finiteProduct
      (faceHeatPolynomial w K half) ids (fun id hi => faceExpansion hw K (h id hi))).tree
      (selectedPolynomial half choice ids) (selectedWeight w choice ids)
  | [], _ => .ofUnit UnitLeaf.one
  | id :: ids, h => (faceChoice hw K hK (h id List.mem_cons_self) (choice id)).product
      (productLeaf hw K hK half choice ids (fun j hj => h j (List.mem_cons_of_mem id hj)))

/-- Literal interface leaf, not a replacement kernel or an assumed span. -/
def interfaceChoice {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) (hK : 1 ≤ K) (half : Nat)
    (choice : Nat → CoordinateChoice) :
    RealizedLeaf (interfaceExpansion hw K half).tree
      (selectedPolynomial half choice (centralFixedFaceIds half))
      (selectedWeight w choice (centralFixedFaceIds half)) :=
  productLeaf hw K hK half choice _ (fun _ h => h)

theorem fundamentalWeight_positive {w : Q'} (hw : (0 : Q') < w) : (0 : Q') < coeffW w 1 := by
  change (0 : Q') < (2 : Q') * (((1 : Q') * w) * w * w)
  exact Q'.mul_pos (by decide) (Q'.mul_pos (Q'.mul_pos (Q'.mul_pos (by decide) hw) hw) hw)

theorem choiceWeight_positive {w : Q'} (hw : (0 : Q') < w) : (c : CoordinateChoice) → (0 : Q') < choiceWeight w c
  | none => show (0 : Q') < 1 by decide
  | some _ => fundamentalWeight_positive hw

theorem selectedWeight_positive {w : Q'} (hw : (0 : Q') < w) (choice : Nat → CoordinateChoice) :
    (ids : List Nat) → (0 : Q') < selectedWeight w choice ids
  | [] => show (0 : Q') < 1 by decide
  | id :: ids => Q'.mul_pos (choiceWeight_positive hw (choice id)) (selectedWeight_positive hw choice ids)

theorem interfaceChoice_weight_positive {w : Q'} (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K) (half : Nat)
    (choice : Nat → CoordinateChoice) :
    (0 : Q') < (interfaceChoice (Q'.le_of_lt hw) K hK half choice).leaf.weight :=
  (interfaceChoice (Q'.le_of_lt hw) K hK half choice).weight_positive (selectedWeight_positive hw choice _)

end YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels

#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.coordinate
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.fundamental_column_entry
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.gramCoordinateLeaf
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.gramCoordinateLeaf_weight
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.gramCoordinateLeaf_channel
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.gramCoordinate
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.faceCoordinatePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.faceCoordinate
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.choicePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.choiceWeight
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.faceChoice
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.selectedPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.selectedWeight
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.interfaceChoice
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.fundamentalWeight_positive
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.choiceWeight_positive
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.selectedWeight_positive
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels.interfaceChoice_weight_positive
