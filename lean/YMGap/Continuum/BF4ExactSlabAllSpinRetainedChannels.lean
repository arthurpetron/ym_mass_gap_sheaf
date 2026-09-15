/-
# Every fixed spin/channel choice persists in the ORIGINAL interface

Each physical crossing face carries an explicitly supplied spin and an
actual leaf of its existing representation Gram tree. Their product gives
an actual interface leaf at every cutoff above the computed maximum spin.
Its polynomial and exact positive heat weight do not depend on that cutoff.

These are finite channel data, not an assumed completeness or nonzero
amplitude statement. Bulk limits, transfer injectivity and Clay are not
concluded here.
-/

import YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels

namespace YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.ReflectedSquareTreeRealizedLeaf
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

private def PositiveWeights : SquareTree → Prop
  | .zero => True
  | .term w _ => (0 : Q') < w
  | .add s t => PositiveWeights s ∧ PositiveWeights t

private theorem positive_leaf : {t : SquareTree} → (l : Leaf t) → PositiveWeights t → (0 : Q') < l.weight
  | _, .here _ _, h => h
  | _, .left l, h => positive_leaf l h.1
  | _, .right l, h => positive_leaf l h.2

private theorem positive_scale (a : Q') (ha : (0 : Q') < a) :
    ∀ t : SquareTree, PositiveWeights t → PositiveWeights (t.scale a)
  | .zero, _ => True.intro
  | .term _ _, h => Q'.mul_pos ha h
  | .add s t, h => ⟨positive_scale a ha s h.1, positive_scale a ha t h.2⟩

private theorem positive_prefix (f : Nat → SquareTree) : ∀ n,
    (∀ i, i < n → PositiveWeights (f i)) → PositiveWeights (SquareTree.prefixSum f n)
  | 0, _ => True.intro
  | n+1, h => ⟨positive_prefix f n (fun i hi => h i (by omega)), h n (by omega)⟩

private theorem positive_tensor : ∀ n (x : PolyTensor n), PositiveWeights (tensorSquares n x)
  | 0, _ => ⟨by change (0 : Q') < 1; decide, by change (0 : Q') < 1; decide⟩
  | n+1, x => ⟨positive_tensor n (x false), positive_tensor n (x true)⟩

theorem gram_leaf_positive (q : RatPolyQuaternion) (spin : Nat) (l : Leaf (gramSquares q spin)) :
    (0 : Q') < l.weight :=
  positive_leaf l (positive_prefix _ _ (fun i _ =>
    positive_scale _ (basisInverseWeight_pos spin i) _ (positive_tensor spin _)))

private theorem power_positive (w : Q') (hw : (0 : Q') < w) : ∀ n, (0 : Q') < qpow w n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos (power_positive w hw n) hw

theorem heat_coefficient_positive (w : Q') (hw : (0 : Q') < w) (spin : Nat) :
    (0 : Q') < coeffW w spin :=
  Q'.mul_pos (Q'.ofNat_succ_pos spin)
    (power_positive w hw (c4 spin))

/-- Actual representation spin and leaf, before inserting slab geometry. -/
structure GramChannel (q : RatPolyQuaternion) where
  spin : Nat
  leaf : Leaf (gramSquares q spin)

/-- The quaternion is pinned to the original physical lower spatial link. -/
abbrev SpinChannel (half id : Nat) := GramChannel (asRepresentationQuaternion
    (correctedSlabLinkPolynomial (centralExtent half)
      (faceLinkA (slabPlaquetteAt (centralExtent half) id))))

def vacuumChannel (half id : Nat) : SpinChannel half id :=
  ⟨0, (gramZeroUnit _).leaf⟩

def facePolynomial {half id : Nat} (c : SpinChannel half id) : RatPoly := c.leaf.channel

def faceWeight (w : Q') {half id : Nat} (c : SpinChannel half id) : Q' :=
  coeffW w c.spin * c.leaf.weight

theorem faceWeight_positive (w : Q') (hw : (0 : Q') < w) {half id : Nat} (c : SpinChannel half id) :
    (0 : Q') < faceWeight w c :=
  Q'.mul_pos (heat_coefficient_positive w hw c.spin) (gram_leaf_positive _ c.spin c.leaf)

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

/-- Original heat coefficient is unchanged once the selected spin is retained. -/
def faceChannel {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) {half id : Nat}
    (hi : id ∈ centralFixedFaceIds half) (c : SpinChannel half id) (hK : c.spin ≤ K) :
    RealizedLeaf (faceExpansion hw K hi).tree (facePolynomial c) (faceWeight w c) := by
  let q := asRepresentationQuaternion (correctedSlabLinkPolynomial (centralExtent half)
    (faceLinkA (slabPlaquetteAt (centralExtent half) id)))
  let f := fun spin => (gramSquares q spin).scale (SU2CharacterVacuumHaar.coeffAt (heatKernelPacket K w) spin)
  have he : (faceExpansion hw K hi).tree = SquareTree.sum f (List.range (K+1)) :=
    sum_tree _ _ _ _ (fun _ _ => rfl)
  rw [he]
  let r : RealizedLeaf (gramSquares q c.spin) (facePolynomial c) c.leaf.weight :=
    ⟨c.leaf, Q'.eqv_refl _, RatPolyCoeffEqv.refl _⟩
  have h := r.scale (SU2CharacterVacuumHaar.coeffAt (heatKernelPacket K w) c.spin)
  have hp : (SU2CharacterVacuumHaar.coeffAt (heatKernelPacket K w) c.spin * c.leaf.weight).eqv (faceWeight w c) := by
    rw [coeffAt_heatKernelPacket (by omega : c.spin < K+1)]
    exact Q'.eqv_refl _
  exact (h.reweight hp).inSum f c.spin (List.range (K+1)) (List.mem_range.mpr (by omega))

def channelPolynomial {half : Nat} (c : (id : Nat) → SpinChannel half id) : List Nat → RatPoly
  | [] => polyOne
  | id :: ids => polyMul (facePolynomial (c id)) (channelPolynomial c ids)

def channelWeight (w : Q') {half : Nat} (c : (id : Nat) → SpinChannel half id) : List Nat → Q'
  | [] => 1
  | id :: ids => faceWeight w (c id) * channelWeight w c ids

def channelCutoff {half : Nat} (c : (id : Nat) → SpinChannel half id) : Nat :=
  ((centralFixedFaceIds half).map (fun id => (c id).spin)).foldr Nat.max 0

private theorem mem_le_max : ∀ (xs : List Nat) (n : Nat), n ∈ xs → n ≤ xs.foldr Nat.max 0
  | [], _, h => False.elim (List.not_mem_nil h)
  | a :: xs, n, h => by
      rcases List.mem_cons.mp h with rfl | hn
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (mem_le_max xs n hn) (Nat.le_max_right _ _)

theorem channelCutoff_spec {half id : Nat} (c : (id : Nat) → SpinChannel half id)
    (hi : id ∈ centralFixedFaceIds half) : (c id).spin ≤ channelCutoff c :=
  mem_le_max _ _ (List.mem_map.mpr ⟨id, hi, rfl⟩)

private def productChannel {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) {half : Nat}
    (c : (id : Nat) → SpinChannel half id) (hK : channelCutoff c ≤ K) :
    (ids : List Nat) → (h : ∀ id, id ∈ ids → id ∈ centralFixedFaceIds half) →
    RealizedLeaf (LocalSquareExpansion.finiteProduct (faceHeatPolynomial w K half) ids
      (fun id hi => faceExpansion hw K (h id hi))).tree (channelPolynomial c ids) (channelWeight w c ids)
  | [], _ => .ofUnit UnitLeaf.one
  | id :: ids, h => (faceChannel hw K (h id List.mem_cons_self) (c id)
      (Nat.le_trans (channelCutoff_spec c (h id List.mem_cons_self)) hK)).product
      (productChannel hw K c hK ids (fun j hj => h j (List.mem_cons_of_mem id hj)))

def interfaceChannel {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) {half : Nat}
    (c : (id : Nat) → SpinChannel half id) (hK : channelCutoff c ≤ K) :
    RealizedLeaf (interfaceExpansion hw K half).tree
      (channelPolynomial c (centralFixedFaceIds half)) (channelWeight w c (centralFixedFaceIds half)) :=
  productChannel hw K c hK _ (fun _ h => h)

theorem channelWeight_positive (w : Q') (hw : (0 : Q') < w) {half : Nat}
    (c : (id : Nat) → SpinChannel half id) : ∀ ids, (0 : Q') < channelWeight w c ids
  | [] => by change (0 : Q') < 1; decide
  | id :: ids => Q'.mul_pos (faceWeight_positive w hw (c id)) (channelWeight_positive w hw c ids)

end YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels

#print axioms YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels.gram_leaf_positive
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels.heat_coefficient_positive
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels.GramChannel
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels.SpinChannel
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels.vacuumChannel
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels.facePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels.faceWeight
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels.faceWeight_positive
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels.faceChannel
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels.channelPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels.channelWeight
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels.channelCutoff
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels.channelCutoff_spec
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels.interfaceChannel
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels.channelWeight_positive
