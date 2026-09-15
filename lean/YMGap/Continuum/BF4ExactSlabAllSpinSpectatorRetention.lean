/-
# ORIGINAL all-spin local channels with the complete spectator interface

Any supplied face channel through the retained cutoff may be selected;
every unselected face keeps its ENTIRE original Gram tree. Products retain
shared variables and give explicit pruning of the actual original tree.
The retained packet has its original bulk limit and numerical modulus.
It is nonnegative and bounded by the full original normalized OS norm.

The growing-face consumer uses the actual transported all-spin branch;
added faces remain full spectators, not frozen unit leaves. This removes
that algebraic restriction, but does not supply a volume-uniform positive
packet/amplitude floor, polynomial pullback, thermodynamic coefficient
limit/separation, transfer kernel/range result, or continuum/Clay theorem.
-/

import YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel
import YMGap.Continuum.ReflectedSquareTreePruning

namespace YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels
open YMGap.Continuum.BF4ExactSlabGrowingRetainedChannel
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit
open YMGap.Continuum.BF4ExactSlabOriginalChannelReconstruction
open YMGap.Continuum.BF4ExactSlabIntrinsicChannelOrder
open YMGap.Continuum.BF4ExactSlabWholePacketNormBound
open YMGap.Continuum.ReflectedSquareTreePruning
open YMGap.Continuum.ReflectedSquareTreePositiveOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

private theorem pruning_order : {s t : SquareTree} → Pruning s t → t.Nonnegative → PositiveOrder s t
  | _, _, .keep _, _ => .refl _
  | _, t, .discard _, ht => fun f hf => value_nonnegative f hf t ht
  | _, .add _ t, .left p, ht => fun f hf => Q'.le_trans' _ _ _ (pruning_order p ht.1 f hf)
      (Q'.add_le_self_of_nonneg _ _ (value_nonnegative f hf t ht.2))
  | _, .add s _, .right p, ht => fun f hf => Q'.le_trans' _ _ _ (pruning_order p ht.2 f hf)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (value_nonnegative f hf s ht.1))
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  | _, _, .add p q, ht => (pruning_order p ht.1).add (pruning_order q ht.2)
  | _, _, .trans p q, ht => (pruning_order p (q.nonnegative ht)).trans (pruning_order q ht)

/-- None keeps the full face. Some supplies an actual all-spin leaf and cutoff proof. -/
abbrev Choice (half K id : Nat) := Option {c : SpinChannel half id // c.spin ≤ K}

variable {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat)

def faceTree {half id : Nat} (hi : id ∈ centralFixedFaceIds half) : Choice half K id → SquareTree
  | none => (faceExpansion hw K hi).tree
  | some c => let l := (faceChannel hw K hi c.val c.property).leaf; .term l.weight l.channel

def facePruning {half id : Nat} (hi : id ∈ centralFixedFaceIds half) : (c : Choice half K id) →
    Pruning (faceTree hw K hi c) (faceExpansion hw K hi).tree
  | none => .keep _
  | some c => .ofLeaf (faceChannel hw K hi c.val c.property).leaf

theorem faceTree_unselected {half id : Nat} (hi : id ∈ centralFixedFaceIds half) :
    faceTree hw K hi none = (faceExpansion hw K hi).tree := rfl

def partialProduct (half : Nat) (choice : (id : Nat) → Choice half K id) :
    (ids : List Nat) → (∀ id, id ∈ ids → id ∈ centralFixedFaceIds half) → SquareTree
  | [], _ => .term 1 polyOne
  | id :: ids, hi => (faceTree hw K (hi id List.mem_cons_self) (choice id)).product
      (partialProduct half choice ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

def productPruning (half : Nat) (choice : (id : Nat) → Choice half K id) :
    (ids : List Nat) → (hi : ∀ id, id ∈ ids → id ∈ centralFixedFaceIds half) →
    Pruning (partialProduct hw K half choice ids hi)
      (LocalSquareExpansion.finiteProduct (faceHeatPolynomial w K half) ids
        (fun id hid => faceExpansion hw K (hi id hid))).tree
  | [], _ => .keep _
  | id :: ids, hi => (facePruning hw K (hi id List.mem_cons_self) (choice id)).product
      (productPruning half choice ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

def retainedInterface (half : Nat) (choice : (id : Nat) → Choice half K id) : SquareTree :=
  partialProduct hw K half choice (centralFixedFaceIds half) (fun _ hi => hi)

def interfacePruning (half : Nat) (choice : (id : Nat) → Choice half K id) :
    Pruning (retainedInterface hw K half choice) (interfaceExpansion hw K half).tree :=
  productPruning hw K half choice _ (fun _ hi => hi)

theorem retainedInterface_nonnegative (half : Nat) (choice : (id : Nat) → Choice half K id) :
    (retainedInterface hw K half choice).Nonnegative :=
  (interfacePruning hw K half choice).nonnegative (interfaceExpansion hw K half).weightsNonnegative

private theorem keepAll (half : Nat) :
    (ids : List Nat) → (hi : ∀ id, id ∈ ids → id ∈ centralFixedFaceIds half) →
    partialProduct hw K half (fun _ => none) ids hi =
      (LocalSquareExpansion.finiteProduct (faceHeatPolynomial w K half) ids
        (fun id hid => faceExpansion hw K (hi id hid))).tree
  | [], _ => rfl
  | id :: ids, hi => by
      change (faceExpansion hw K (hi id List.mem_cons_self)).tree.product _ = _
      rw [keepAll half ids (fun j hj => hi j (List.mem_cons_of_mem id hj))]
      rfl

theorem retainedInterface_keepAll (half : Nat) :
    retainedInterface hw K half (fun _ => none) = (interfaceExpansion hw K half).tree :=
  keepAll hw K half _ (fun _ hi => hi)

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}
    (choice : (id : Nat) → Choice half K id) (e : PlaquetteExpression half)

def retainedPacket : CReal :=
  energyLimit w hw0 hw1 half (lower e) (retainedInterface (Q'.le_of_lt hw0) K half choice)

def retainedPacketCauchy : QCauchy (retainedPacket K w hw0 hw1 choice e).approx :=
  energyLimitCauchy w hw0 hw1 half (lower e) (retainedInterface (Q'.le_of_lt hw0) K half choice)

theorem retainedPacket_nonnegative : leEv (ofQ' 0) (retainedPacket K w hw0 hw1 choice e) :=
  leEv_ofQ'_of_approx_ge (energyLimit_nonnegative w hw0 hw1 half (lower e) _
    (retainedInterface_nonnegative (Q'.le_of_lt hw0) K half choice))

/-- Every original bulk interaction is retained when taking this limit. -/
theorem retainedPacket_le_packet : leEv (retainedPacket K w hw0 hw1 choice e) (channelPacket w hw0 hw1 e K) := by
  have ht := (interfaceExpansion (Q'.le_of_lt hw0) K half).weightsNonnegative
  have hp := interfacePruning (Q'.le_of_lt hw0) K half choice
  apply leEv_of_ofQ'_limit_le
    (energy_converges w hw0 hw1 half (lower e) _ (hp.nonnegative ht))
    (energy_converges w hw0 hw1 half (lower e) _ ht)
  intro epsilon he
  exact ⟨0, fun B _ => Q'.le_trans' _ _ _ (energy_order w B half (lower e) (pruning_order hp ht))
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

def normalizedRetainedPacket : CReal :=
  CReal.mul (actionReciprocal w hw0 hw1 half) (retainedPacket K w hw0 hw1 choice e)

theorem normalizedRetainedPacket_bound :
    leEv (normalizedRetainedPacket K w hw0 hw1 choice e) (form w hw0 hw1 e e) :=
  leEv_trans (leEv_mul_nonneg_left (reciprocal_nonnegative w hw0 hw1 half)
    (retainedPacket_le_packet K w hw0 hw1 choice e)) (normalizedPacket_norm_bound w hw0 hw1 e K)

theorem retainedPacket_keepAll :
    retainedPacket K w hw0 hw1 (fun _ => none) e = channelPacket w hw0 hw1 e K := by
  unfold retainedPacket
  rw [retainedInterface_keepAll]
  rfl

/-- Only the physically shifted selected face is pruned; all other faces remain full. -/
def growingChoice {base id : Nat} (padding : Nat) (c : SpinChannel base id) (hK : c.spin ≤ K)
    (j : Nat) : Choice (base+padding) K j :=
  if h : j = bulkFaceId base padding 0 id then by
    subst j
    exact some ⟨shiftedChannel padding c, hK⟩
  else none

theorem growingChoice_selected {base id : Nat} (padding : Nat) (c : SpinChannel base id) (hK : c.spin ≤ K) :
    growingChoice K padding c hK (bulkFaceId base padding 0 id) = some ⟨shiftedChannel padding c,hK⟩ :=
  dif_pos rfl

theorem growingChoice_spectator {base id : Nat} (padding : Nat) (c : SpinChannel base id) (hK : c.spin ≤ K)
    (j : Nat) (hj : j ≠ bulkFaceId base padding 0 id) : growingChoice K padding c hK j = none :=
  dif_neg hj

/-- The target is the original norm; the surrounding crossing action is not frozen. -/
theorem growingSpectatorPacket_bound {base id : Nat} (padding : Nat) (c : SpinChannel base id) (hK : c.spin ≤ K)
    (e : PlaquetteExpression (base+padding)) :
    leEv (normalizedRetainedPacket K w hw0 hw1 (growingChoice K padding c hK) e) (form w hw0 hw1 e e) :=
  normalizedRetainedPacket_bound K w hw0 hw1 (growingChoice K padding c hK) e

end YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention

#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.Choice
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.faceTree
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.facePruning
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.faceTree_unselected
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.partialProduct
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.productPruning
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.retainedInterface
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.interfacePruning
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.retainedInterface_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.retainedInterface_keepAll
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.retainedPacket
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.retainedPacketCauchy
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.retainedPacket_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.retainedPacket_le_packet
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.normalizedRetainedPacket
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.normalizedRetainedPacket_bound
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.retainedPacket_keepAll
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.growingChoice
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.growingChoice_selected
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.growingChoice_spectator
#print axioms YMGap.Continuum.BF4ExactSlabAllSpinSpectatorRetention.growingSpectatorPacket_bound
