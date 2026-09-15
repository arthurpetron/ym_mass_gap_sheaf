/-
# Monotone ORIGINAL crossing packets and bounds for every actual leaf

Every retained spin has exactly the same original heat coefficient at
larger cutoffs. The finite square-tree order therefore compares the actual
face expansions and their shared-variable product. An arbitrary actual
packet leaf, not only a selected global spin family, is bounded by the
original full reflected numerator at every larger full-action cutoff.

Strict positivity of every actual leaf weight is proved from the original
Gram weights and heat coefficients. No cutoff/volume-uniform positive floor,
completed coefficient map, transfer kernel or continuum/Clay claim.
-/

import YMGap.Continuum.ReflectedSquareTreePositiveOrder
import YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction

namespace YMGap.Continuum.BF4ExactSlabIntrinsicChannelOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabMixedInterfacePin
open YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity
open YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit
open YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.ReflectedSquareTreePositiveOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

def spinPrefix (w : Q') (K : Nat) (q : RatPolyQuaternion) : SquareTree :=
  SquareTree.sum (fun spin => (gramSquares q spin).scale (coeffW w spin)) (List.range (K+1))

private theorem sum_tree {A : Type} {half : Nat} (f : A → RatPoly) (g : A → SquareTree) :
    (xs : List A) → (h : ∀ a, a ∈ xs → LocalSquareExpansion half (f a)) →
    (∀ a (ha : a ∈ xs), (h a ha).tree = g a) →
    (LocalSquareExpansion.finiteSum f xs h).tree = SquareTree.sum g xs
  | [], _, _ => rfl
  | a :: xs, h, hg => by
      change SquareTree.add (h a List.mem_cons_self).tree _ = SquareTree.add (g a) _
      rw [hg a List.mem_cons_self,
        sum_tree f g xs (fun b hb => h b (List.mem_cons_of_mem a hb))
          (fun b hb => hg b (List.mem_cons_of_mem a hb))]

/-- Exact equality of the ACTUAL tree with the original-coefficient prefix. -/
theorem faceExpansion_tree {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) {half id : Nat}
    (hi : id ∈ centralFixedFaceIds half) :
    (faceExpansion hw K hi).tree = spinPrefix w K (asRepresentationQuaternion
      (correctedSlabLinkPolynomial (centralExtent half) (faceLinkA (slabPlaquetteAt (centralExtent half) id)))) := by
  apply sum_tree
  intro spin hspin
  change (gramSquares _ spin).scale (SU2CharacterVacuumHaar.coeffAt (heatKernelPacket K w) spin) = _
  rw [coeffAt_heatKernelPacket (List.mem_range.mp hspin)]

theorem face_order {w : Q'} (hw : (0 : Q') ≤ w) (N K : Nat) {half id : Nat}
    (hi : id ∈ centralFixedFaceIds half) (hNK : N ≤ K) :
    PositiveOrder (faceExpansion hw N hi).tree (faceExpansion hw K hi).tree := by
  rw [faceExpansion_tree hw N hi, faceExpansion_tree hw K hi]
  exact PositiveOrder.range_mono _ (fun spin =>
    SquareTree.scale_nonnegative _ (coeffW_nonneg hw spin) _ (gramSquares_nonnegative _ spin))
    (N+1) (K+1) (Nat.succ_le_succ hNK)

theorem interface_order {w : Q'} (hw : (0 : Q') ≤ w) (N K half : Nat) (hNK : N ≤ K) :
    PositiveOrder (interfaceExpansion hw N half).tree (interfaceExpansion hw K half).tree := by
  unfold interfaceExpansion
  apply PositiveOrder.finiteProduct
  exact fun _ hi => face_order hw N K hi hNK

private def AllPositive : SquareTree → Prop
  | .zero => True
  | .term v _ => (0 : Q') < v
  | .add s t => AllPositive s ∧ AllPositive t

private theorem positive_of_leaves : (t : SquareTree) → (∀ l : Leaf t, (0 : Q') < l.weight) → AllPositive t
  | .zero, _ => True.intro
  | .term v p, h => h (.here v p)
  | .add s t, h => ⟨positive_of_leaves s (fun l => h (.left l)), positive_of_leaves t (fun l => h (.right l))⟩

private theorem positive_leaf : {t : SquareTree} → AllPositive t → (l : Leaf t) → (0 : Q') < l.weight
  | _, h, .here _ _ => h
  | _, h, .left l => positive_leaf h.1 l
  | _, h, .right l => positive_leaf h.2 l

private theorem positive_scale (a : Q') (ha : (0 : Q') < a) : (t : SquareTree) → AllPositive t → AllPositive (t.scale a)
  | .zero, _ => True.intro
  | .term _ _, h => Q'.mul_pos ha h
  | .add s t, h => ⟨positive_scale a ha s h.1, positive_scale a ha t h.2⟩

private theorem positive_sum {A : Type} (f : A → SquareTree) (hf : ∀ a, AllPositive (f a)) :
    ∀ xs : List A, AllPositive (SquareTree.sum f xs)
  | [] => True.intro
  | a :: xs => ⟨hf a, positive_sum f hf xs⟩

private theorem positive_multiply (a : Q') (ha : (0 : Q') < a) (p : RatPoly) :
    (t : SquareTree) → AllPositive t → AllPositive (t.multiplyTerm a p)
  | .zero, _ => True.intro
  | .term _ _, h => Q'.mul_pos ha h
  | .add s t, h => ⟨positive_multiply a ha p s h.1, positive_multiply a ha p t h.2⟩

private theorem positive_product : (s t : SquareTree) → AllPositive s → AllPositive t → AllPositive (s.product t)
  | .zero, _, _, _ => True.intro
  | .term a p, t, hs, ht => positive_multiply a hs p t ht
  | .add s u, t, hs, ht => ⟨positive_product s t hs.1 ht, positive_product u t hs.2 ht⟩

private theorem positive_finiteProduct {A : Type} {half : Nat} (f : A → RatPoly) :
    (xs : List A) → (P : (a : A) → a ∈ xs → LocalSquareExpansion half (f a)) →
    (∀ a ha, AllPositive (P a ha).tree) → AllPositive (LocalSquareExpansion.finiteProduct f xs P).tree
  | [], _, _ => by change (0 : Q') < 1; decide
  | a :: xs, P, h => positive_product _ _ (h a List.mem_cons_self)
      (positive_finiteProduct f xs (fun b hb => P b (List.mem_cons_of_mem a hb))
        (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-- Strict weight positivity for EVERY intrinsic leaf of the original packet. -/
theorem interface_leaf_positive (w : Q') (hw0 : (0 : Q') < w) (N half : Nat)
    (l : Leaf (interfaceExpansion (Q'.le_of_lt hw0) N half).tree) : (0 : Q') < l.weight := by
  apply positive_leaf _ l
  apply positive_finiteProduct
  intro id hi
  rw [faceExpansion_tree (Q'.le_of_lt hw0) N hi]
  exact positive_sum _ (fun spin => positive_scale _ (heat_coefficient_positive w hw0 spin) _
    (positive_of_leaves _ (gram_leaf_positive _ spin))) _

theorem value_energy (w : Q') (B half : Nat) (p : RatPoly) : ∀ t : SquareTree,
    value (fun q => lowerMoment w B half (polyMul p q) * lowerMoment w B half (polyMul p q)) t =
      energySequence w B half p t
  | .zero => rfl
  | .term _ _ => rfl
  | .add s t => by
      change value _ s + value _ t = energySequence w B half p s + energySequence w B half p t
      rw [value_energy w B half p s, value_energy w B half p t]

theorem energy_order (w : Q') (B half : Nat) (p : RatPoly) {s t : SquareTree} (h : PositiveOrder s t) :
    energySequence w B half p s ≤ energySequence w B half p t := by
  rw [← value_energy w B half p s, ← value_energy w B half p t]
  exact h _ (fun _ => SumOfSquares.q_mul_self_nonneg _)

/-- Bulk nome and cutoff stay fixed while the ORIGINAL crossing cutoff grows. -/
theorem mixed_cutoff_mono (b v : Q') (hv : (0 : Q') ≤ v) (B N K : Nat) {half : Nat}
    (e : PlaquetteExpression half) (hNK : N ≤ K) : mixedQuadratic b v B N e ≤ mixedQuadratic b v B K e :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (mixed_energy_pin b v hv B N e))
    (Q'.le_trans' _ _ _ (energy_order b B half (lower e) (interface_order hv N K half hNK))
      (Q'.ge_of_eqv (mixed_energy_pin b v hv B K e)))

/-- Any intrinsic packet leaf is retained below the full ORIGINAL action
at every later cutoff, with its SAME weight and lower channel polynomial. -/
theorem intrinsic_leaf_finite_bound (w : Q') (hw : (0 : Q') ≤ w) (N K : Nat) {half : Nat}
    (e : PlaquetteExpression half) (l : Leaf (interfaceExpansion hw N half).tree) (hNK : N ≤ K) :
    l.weight * (lowerMoment w K half (polyMul (lower e) l.channel) *
      lowerMoment w K half (polyMul (lower e) l.channel)) ≤ originalQuadratic w K e :=
  Q'.le_trans' _ _ _ (energy_order w K half (lower e)
    (PositiveOrder.leaf l (interfaceExpansion hw N half).weightsNonnegative))
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (mixed_energy_pin w w hw K N e))
      (Q'.le_trans' _ _ _ (mixed_cutoff_mono w w hw K N K e hNK)
        (Q'.le_of_eqv (mixed_original_diagonal w hw K e))))

end YMGap.Continuum.BF4ExactSlabIntrinsicChannelOrder

#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelOrder.spinPrefix
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelOrder.faceExpansion_tree
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelOrder.face_order
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelOrder.interface_order
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelOrder.interface_leaf_positive
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelOrder.value_energy
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelOrder.energy_order
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelOrder.mixed_cutoff_mono
#print axioms YMGap.Continuum.BF4ExactSlabIntrinsicChannelOrder.intrinsic_leaf_finite_bound
