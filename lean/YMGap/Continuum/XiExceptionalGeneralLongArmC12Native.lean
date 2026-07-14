/-
# Native token-product normalization for the canonical C12 ear

The generic long-arm carrier has eight C12 long codes.  Unfolding each
eighteen-factor weight directly into `Q'.eqv` makes denominator matching
needlessly expensive.  Here every carrier is first stated as a product of
occurrence-index tokens.  A constructive insertion sort proves products
invariant under token reordering, while `qProd_flatten_eqv` exposes only five
small algebraic chunks.  This gives the three word identities required by
`CanonicalEarWordGeometry` for the standard ordered C12 cycle.

The resulting paid block is also installed in `OwnedPaidResidualFamily`.
Its test deliberately accepts only the one canonical source entry; thus this
is a local C12 interface inhabitant, not a multi-source global allocation.
The separate global allocator module records the additional cross-source
ownership obligation.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmGlobalAllocator
import YMGap.Continuum.XiExceptionalC12MultiReserveRepair

namespace YMGap.Continuum.XiExceptionalGeneralLongArmC12Native

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFourthMixedRepair
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalGeneralLongArmAlgebra
open YMGap.Continuum.XiExceptionalGeneralLongArmCarriers
open YMGap.Continuum.XiExceptionalGeneralLongArmGeometry
open YMGap.Continuum.XiExceptionalGeneralLongArmResidualBridge
open YMGap.Continuum.XiExceptionalGeneralLongArmGlobalAllocator
open YMGap.Continuum.XiExceptionalExternalReserveLimitFence
open YMGap.Continuum.XiExceptionalMultiReserveAlgebra

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

abbrev G := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.Gamma

def tokenActivity (w : Q') (label : TL.Plaquette → Rep) (i : Nat) : Q' :=
  activity w (polyAt G i) label

def tokenProduct (w : Q') (label : TL.Plaquette → Rep)
    (indices : List Nat) : Q' :=
  qProd (indices.map (tokenActivity w label))

theorem qProd_append_eqv : ∀ xs ys : List Q',
    qProd (xs ++ ys) ≈ qProd xs * qProd ys
  | [], ys => by
      simp only [List.nil_append, qProd]
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | x :: xs, ys => by
      simp only [List.cons_append, qProd]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left x _ _ (qProd_append_eqv xs ys)) ?_
      exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

theorem qProd_perm_eqv {xs ys : List Q'} (h : xs.Perm ys) :
    qProd xs ≈ qProd ys := by
  induction h with
  | nil => exact Q'.eqv_refl _
  | cons x h ih =>
      simp only [qProd]
      exact Q'.mul_eqv_congr_left x _ _ ih
  | swap x y l =>
      simp only [qProd]
      calc
        y * (x * qProd l) ≈ (y * x) * qProd l :=
          Q'.eqv_symm (Q'.mul_assoc_eqv y x (qProd l))
        _ ≈ (x * y) * qProd l :=
          Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv y x)
        _ ≈ x * (y * qProd l) := Q'.mul_assoc_eqv x y (qProd l)
  | trans h1 h2 ih1 ih2 => exact Q'.eqv_trans _ _ _ ih1 ih2

theorem qProd_flatten_eqv : ∀ chunks : List (List Q'),
    qProd chunks.flatten ≈ qProd (chunks.map qProd)
  | [] => Q'.eqv_refl _
  | chunk :: chunks => by
      simp only [List.flatten_cons, List.map_cons, qProd]
      refine Q'.eqv_trans _ _ _
        (qProd_append_eqv chunk chunks.flatten) ?_
      exact Q'.mul_eqv_congr_left (qProd chunk) _ _
        (qProd_flatten_eqv chunks)

theorem twoTokenBlocks_native (w : Q') (label : TL.Plaquette → Rep)
    (first second : List Nat) :
    qProd (first.map (tokenActivity w label)) *
        qProd (second.map (tokenActivity w label)) ≈
      tokenProduct w label (first ++ second) := by
  unfold tokenProduct
  rw [List.map_append]
  exact Q'.eqv_symm (qProd_append_eqv _ _)

def insertToken (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
      if decide (x ≤ y) then x :: y :: ys else y :: insertToken x ys

def sortTokens : List Nat → List Nat
  | [] => []
  | x :: xs => insertToken x (sortTokens xs)

theorem insertToken_product (w : Q') (label : TL.Plaquette → Rep)
    (x : Nat) : ∀ xs : List Nat,
    tokenProduct w label (insertToken x xs) ≈
      tokenActivity w label x * tokenProduct w label xs
  | [] => Q'.eqv_refl _
  | y :: ys => by
      unfold insertToken
      split
      next _ => exact Q'.eqv_refl _
      next _ =>
        unfold tokenProduct
        simp only [List.map_cons, qProd]
        refine Q'.eqv_trans _
          (tokenActivity w label y *
            (tokenActivity w label x *
              qProd (List.map (tokenActivity w label) ys))) _
          (Q'.mul_eqv_congr_left (tokenActivity w label y) _ _
            (insertToken_product w label x ys)) ?_
        calc
          tokenActivity w label y *
              (tokenActivity w label x *
                qProd (List.map (tokenActivity w label) ys)) ≈
            (tokenActivity w label y * tokenActivity w label x) *
              qProd (List.map (tokenActivity w label) ys) :=
                Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
          _ ≈ (tokenActivity w label x * tokenActivity w label y) *
              qProd (List.map (tokenActivity w label) ys) :=
                Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)
          _ ≈ tokenActivity w label x *
              (tokenActivity w label y *
                qProd (List.map (tokenActivity w label) ys)) :=
                Q'.mul_assoc_eqv _ _ _

theorem sortTokens_product (w : Q') (label : TL.Plaquette → Rep) :
    ∀ xs : List Nat,
    tokenProduct w label (sortTokens xs) ≈ tokenProduct w label xs
  | [] => Q'.eqv_refl _
  | x :: xs => by
      refine Q'.eqv_trans _
        (tokenActivity w label x * tokenProduct w label (sortTokens xs)) _
        (insertToken_product w label x (sortTokens xs)) ?_
      exact Q'.mul_eqv_congr_left (tokenActivity w label x) _ _
        (sortTokens_product w label xs)

theorem tokenProduct_eqv_of_sorted_eq (w : Q')
    (label : TL.Plaquette → Rep) {xs ys : List Nat}
    (h : sortTokens xs = sortTokens ys) :
    tokenProduct w label xs ≈ tokenProduct w label ys := by
  exact Q'.eqv_trans _ (tokenProduct w label (sortTokens xs)) _
    (Q'.eqv_symm (sortTokens_product w label xs))
    (h ▸ sortTokens_product w label ys)

theorem taggedEvenChunks (a0 a3 tag x : Q') (even odd : List Q') :
    qProd [[a0, a3, tag], even, odd, odd, [x, x, x]].flatten ≈
      (a0 * a3) *
        (tag * ((qProd even * qProd odd) * (qProd odd * qCube x))) := by
  refine Q'.eqv_trans _
    (qProd ([[a0, a3, tag], even, odd, odd, [x, x, x]].map qProd)) _
    (qProd_flatten_eqv _) ?_
  simp only [List.map_cons, List.map_nil, qProd, qCube]
  ring_qeqv

theorem untaggedEvenChunks (a0 a3 x : Q') (even odd : List Q') :
    qProd [[a0, a3], even, odd, odd, [x, x, x]].flatten ≈
      (a0 * a3) *
        ((qProd even * qProd odd) * (qProd odd * qCube x)) := by
  refine Q'.eqv_trans _
    (qProd ([[a0, a3], even, odd, odd, [x, x, x]].map qProd)) _
    (qProd_flatten_eqv _) ?_
  simp only [List.map_cons, List.map_nil, qProd, qCube]
  ring_qeqv

theorem taggedOddChunks (a0 a3 tag x : Q') (even odd : List Q') :
    qProd [[a0, a3, tag], even, odd, even, [x, x, x]].flatten ≈
      (a0 * a3) *
        (tag * ((qProd even * qProd odd) * (qProd even * qCube x))) := by
  refine Q'.eqv_trans _
    (qProd ([[a0, a3, tag], even, odd, even, [x, x, x]].map qProd)) _
    (qProd_flatten_eqv _) ?_
  simp only [List.map_cons, List.map_nil, qProd, qCube]
  ring_qeqv

theorem untaggedOddChunks (a0 a3 x : Q') (even odd : List Q') :
    qProd [[a0, a3], even, odd, even, [x, x, x]].flatten ≈
      (a0 * a3) *
        ((qProd even * qProd odd) * (qProd even * qCube x)) := by
  refine Q'.eqv_trans _
    (qProd ([[a0, a3], even, odd, even, [x, x, x]].map qProd)) _
    (qProd_flatten_eqv _) ?_
  simp only [List.map_cons, List.map_nil, qProd, qCube]
  ring_qeqv

theorem sourceChunks (a0 a3 a1 a2 : Q') (even odd : List Q') :
    qProd [[a0, a3], [a1, a2], even, odd].flatten ≈
      (a0 * a3) * ((a1 * a2) * (qProd even * qProd odd)) := by
  refine Q'.eqv_trans _
    (qProd ([[a0, a3], [a1, a2], even, odd].map qProd)) _
    (qProd_flatten_eqv _) ?_
  simp only [List.map_cons, List.map_nil, qProd]
  ring_qeqv

theorem shortChunks (a0 a3 a1 a2 : Q') :
    qProd [[a0, a3], [a1, a2], [a1, a2]].flatten ≈
      (a0 * a3) * shortSquare a1 a2 := by
  refine Q'.eqv_trans _
    (qProd ([[a0, a3], [a1, a2], [a1, a2]].map qProd)) _
    (qProd_flatten_eqv _) ?_
  simp only [List.map_cons, List.map_nil, qProd, shortSquare]
  ring_qeqv

def chainFromPolyList : List (Polymer TL) → ChainCode TL.Plaquette
  | [] => .terminal []
  | X :: xs => .step X (chainFromPolyList xs)

def even0Erased : CarrierXiCode TL :=
  ((V0, chainFromPolyList
    [V11, V10, V9, V8, V7, V6, V5, V4, V4, V4, V4, V3]),
    [V1, V5, V7, V9, V11])

theorem even0_erasure :
    eraseOccCarrierXiCode G (longCarrierCode G 1 (by rfl) .even 0) =
      even0Erased := by
  rfl

def longWalkTokens : LongParity → Nat → List Nat
  | .even, 0 => [11, 10, 9, 8, 7, 6, 5, 4, 4, 4, 4, 3]
  | .even, 1 => [11, 10, 9, 8, 7, 6, 6, 6, 6, 5, 4, 3]
  | .even, 2 => [11, 10, 9, 8, 8, 8, 8, 7, 6, 5, 4, 3]
  | .even, _ => [11, 10, 10, 10, 10, 9, 8, 7, 6, 5, 4, 3]
  | .odd, 0 => [11, 10, 9, 8, 7, 6, 5, 5, 5, 5, 4, 3]
  | .odd, 1 => [11, 10, 9, 8, 7, 7, 7, 7, 6, 5, 4, 3]
  | .odd, 2 => [11, 10, 9, 9, 9, 9, 8, 7, 6, 5, 4, 3]
  | .odd, _ => [11, 11, 11, 11, 10, 9, 8, 7, 6, 5, 4, 3]

def longExternalTokens : LongParity → Nat → List Nat
  | .even, 0 => [1, 5, 7, 9, 11]
  | .even, _ => [5, 7, 9, 11]
  | .odd, 0 => [2, 4, 6, 8, 10]
  | .odd, _ => [4, 6, 8, 10]

def actualLongTokens (side : LongParity) (i : Nat) : List Nat :=
  0 :: (longWalkTokens side i ++ longExternalTokens side i)

def canonicalLongTokens : LongParity → Nat → List Nat
  | .even, 0 => [0, 3, 1, 4, 6, 8, 10, 5, 7, 9, 11,
      5, 7, 9, 11, 4, 4, 4]
  | .even, 1 => [0, 3, 4, 6, 8, 10, 5, 7, 9, 11,
      5, 7, 9, 11, 6, 6, 6]
  | .even, 2 => [0, 3, 4, 6, 8, 10, 5, 7, 9, 11,
      5, 7, 9, 11, 8, 8, 8]
  | .even, _ => [0, 3, 4, 6, 8, 10, 5, 7, 9, 11,
      5, 7, 9, 11, 10, 10, 10]
  | .odd, 0 => [0, 3, 2, 4, 6, 8, 10, 5, 7, 9, 11,
      4, 6, 8, 10, 5, 5, 5]
  | .odd, 1 => [0, 3, 4, 6, 8, 10, 5, 7, 9, 11,
      4, 6, 8, 10, 7, 7, 7]
  | .odd, 2 => [0, 3, 4, 6, 8, 10, 5, 7, 9, 11,
      4, 6, 8, 10, 9, 9, 9]
  | .odd, _ => [0, 3, 4, 6, 8, 10, 5, 7, 9, 11,
      4, 6, 8, 10, 11, 11, 11]

def erasedLong : LongParity → Nat → CarrierXiCode TL
  | .even, 0 => ((V0, chainFromPolyList
      [V11, V10, V9, V8, V7, V6, V5, V4, V4, V4, V4, V3]),
      [V1, V5, V7, V9, V11])
  | .even, 1 => ((V0, chainFromPolyList
      [V11, V10, V9, V8, V7, V6, V6, V6, V6, V5, V4, V3]),
      [V5, V7, V9, V11])
  | .even, 2 => ((V0, chainFromPolyList
      [V11, V10, V9, V8, V8, V8, V8, V7, V6, V5, V4, V3]),
      [V5, V7, V9, V11])
  | .even, _ => ((V0, chainFromPolyList
      [V11, V10, V10, V10, V10, V9, V8, V7, V6, V5, V4, V3]),
      [V5, V7, V9, V11])
  | .odd, 0 => ((V0, chainFromPolyList
      [V11, V10, V9, V8, V7, V6, V5, V5, V5, V5, V4, V3]),
      [V2, V4, V6, V8, V10])
  | .odd, 1 => ((V0, chainFromPolyList
      [V11, V10, V9, V8, V7, V7, V7, V7, V6, V5, V4, V3]),
      [V4, V6, V8, V10])
  | .odd, 2 => ((V0, chainFromPolyList
      [V11, V10, V9, V9, V9, V9, V8, V7, V6, V5, V4, V3]),
      [V4, V6, V8, V10])
  | .odd, _ => ((V0, chainFromPolyList
      [V11, V11, V11, V11, V10, V9, V8, V7, V6, V5, V4, V3]),
      [V4, V6, V8, V10])

theorem long_erasure (side : LongParity) (i : Nat) (hi : i < 4) :
    eraseOccCarrierXiCode G (longCarrierCode G 1 (by rfl) side i) =
      erasedLong side i := by
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;> cases side <;> rfl

theorem long_even0_native (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (longCarrierCode G 1 (by rfl) .even 0) ≈
      tokenProduct w label [0, 11, 10, 9, 8, 7, 6, 5, 4, 4, 4, 4, 3,
        1, 5, 7, 9, 11] := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (longCarrierCode G 1 (by rfl) .even 0) =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G
            (longCarrierCode G 1 (by rfl) .even 0)) from rfl]
  rw [even0_erasure]
  change
    qProd ([0, 11, 10, 9, 8, 7, 6, 5, 4, 4, 4, 4, 3].map
        (tokenActivity w label)) *
      qProd ([1, 5, 7, 9, 11].map (tokenActivity w label)) ≈
      tokenProduct w label [0, 11, 10, 9, 8, 7, 6, 5, 4, 4, 4, 4, 3,
        1, 5, 7, 9, 11]
  unfold tokenProduct
  change
    qProd ([0, 11, 10, 9, 8, 7, 6, 5, 4, 4, 4, 4, 3].map
        (tokenActivity w label)) *
      qProd ([1, 5, 7, 9, 11].map (tokenActivity w label)) ≈
      qProd
        ([0, 11, 10, 9, 8, 7, 6, 5, 4, 4, 4, 4, 3].map
          (tokenActivity w label) ++
        [1, 5, 7, 9, 11].map (tokenActivity w label))
  exact Q'.eqv_symm (qProd_append_eqv _ _)

theorem long_even1_native (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (longCarrierCode G 1 (by rfl) .even 1) ≈
      tokenProduct w label [0, 11, 10, 9, 8, 7, 6, 6, 6, 6, 5, 4, 3,
        5, 7, 9, 11] := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (longCarrierCode G 1 (by rfl) .even 1) =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G
            (longCarrierCode G 1 (by rfl) .even 1)) from rfl]
  rw [long_erasure .even 1 (by omega)]
  change
    qProd ([0, 11, 10, 9, 8, 7, 6, 6, 6, 6, 5, 4, 3].map
        (tokenActivity w label)) *
      qProd ([5, 7, 9, 11].map (tokenActivity w label)) ≈
      tokenProduct w label [0, 11, 10, 9, 8, 7, 6, 6, 6, 6, 5, 4, 3,
        5, 7, 9, 11]
  exact twoTokenBlocks_native w label _ _

theorem long_even2_native (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (longCarrierCode G 1 (by rfl) .even 2) ≈
      tokenProduct w label [0, 11, 10, 9, 8, 8, 8, 8, 7, 6, 5, 4, 3,
        5, 7, 9, 11] := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (longCarrierCode G 1 (by rfl) .even 2) =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G
            (longCarrierCode G 1 (by rfl) .even 2)) from rfl]
  rw [long_erasure .even 2 (by omega)]
  change
    qProd ([0, 11, 10, 9, 8, 8, 8, 8, 7, 6, 5, 4, 3].map
        (tokenActivity w label)) *
      qProd ([5, 7, 9, 11].map (tokenActivity w label)) ≈
      tokenProduct w label [0, 11, 10, 9, 8, 8, 8, 8, 7, 6, 5, 4, 3,
        5, 7, 9, 11]
  exact twoTokenBlocks_native w label _ _

theorem long_even3_native (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (longCarrierCode G 1 (by rfl) .even 3) ≈
      tokenProduct w label [0, 11, 10, 10, 10, 10, 9, 8, 7, 6, 5, 4, 3,
        5, 7, 9, 11] := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (longCarrierCode G 1 (by rfl) .even 3) =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G
            (longCarrierCode G 1 (by rfl) .even 3)) from rfl]
  rw [long_erasure .even 3 (by omega)]
  change
    qProd ([0, 11, 10, 10, 10, 10, 9, 8, 7, 6, 5, 4, 3].map
        (tokenActivity w label)) *
      qProd ([5, 7, 9, 11].map (tokenActivity w label)) ≈
      tokenProduct w label [0, 11, 10, 10, 10, 10, 9, 8, 7, 6, 5, 4, 3,
        5, 7, 9, 11]
  exact twoTokenBlocks_native w label _ _

theorem long_odd0_native (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (longCarrierCode G 1 (by rfl) .odd 0) ≈
      tokenProduct w label [0, 11, 10, 9, 8, 7, 6, 5, 5, 5, 5, 4, 3,
        2, 4, 6, 8, 10] := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (longCarrierCode G 1 (by rfl) .odd 0) =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G
            (longCarrierCode G 1 (by rfl) .odd 0)) from rfl]
  rw [long_erasure .odd 0 (by omega)]
  change
    qProd ([0, 11, 10, 9, 8, 7, 6, 5, 5, 5, 5, 4, 3].map
        (tokenActivity w label)) *
      qProd ([2, 4, 6, 8, 10].map (tokenActivity w label)) ≈
      tokenProduct w label [0, 11, 10, 9, 8, 7, 6, 5, 5, 5, 5, 4, 3,
        2, 4, 6, 8, 10]
  exact twoTokenBlocks_native w label _ _

theorem long_odd1_native (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (longCarrierCode G 1 (by rfl) .odd 1) ≈
      tokenProduct w label [0, 11, 10, 9, 8, 7, 7, 7, 7, 6, 5, 4, 3,
        4, 6, 8, 10] := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (longCarrierCode G 1 (by rfl) .odd 1) =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G
            (longCarrierCode G 1 (by rfl) .odd 1)) from rfl]
  rw [long_erasure .odd 1 (by omega)]
  change
    qProd ([0, 11, 10, 9, 8, 7, 7, 7, 7, 6, 5, 4, 3].map
        (tokenActivity w label)) *
      qProd ([4, 6, 8, 10].map (tokenActivity w label)) ≈
      tokenProduct w label [0, 11, 10, 9, 8, 7, 7, 7, 7, 6, 5, 4, 3,
        4, 6, 8, 10]
  exact twoTokenBlocks_native w label _ _

theorem long_odd2_native (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (longCarrierCode G 1 (by rfl) .odd 2) ≈
      tokenProduct w label [0, 11, 10, 9, 9, 9, 9, 8, 7, 6, 5, 4, 3,
        4, 6, 8, 10] := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (longCarrierCode G 1 (by rfl) .odd 2) =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G
            (longCarrierCode G 1 (by rfl) .odd 2)) from rfl]
  rw [long_erasure .odd 2 (by omega)]
  change
    qProd ([0, 11, 10, 9, 9, 9, 9, 8, 7, 6, 5, 4, 3].map
        (tokenActivity w label)) *
      qProd ([4, 6, 8, 10].map (tokenActivity w label)) ≈
      tokenProduct w label [0, 11, 10, 9, 9, 9, 9, 8, 7, 6, 5, 4, 3,
        4, 6, 8, 10]
  exact twoTokenBlocks_native w label _ _

theorem long_odd3_native (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (longCarrierCode G 1 (by rfl) .odd 3) ≈
      tokenProduct w label [0, 11, 11, 11, 11, 10, 9, 8, 7, 6, 5, 4, 3,
        4, 6, 8, 10] := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (longCarrierCode G 1 (by rfl) .odd 3) =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G
            (longCarrierCode G 1 (by rfl) .odd 3)) from rfl]
  rw [long_erasure .odd 3 (by omega)]
  change
    qProd ([0, 11, 11, 11, 11, 10, 9, 8, 7, 6, 5, 4, 3].map
        (tokenActivity w label)) *
      qProd ([4, 6, 8, 10].map (tokenActivity w label)) ≈
      tokenProduct w label [0, 11, 11, 11, 11, 10, 9, 8, 7, 6, 5, 4, 3,
        4, 6, 8, 10]
  exact twoTokenBlocks_native w label _ _

theorem long_native (w : Q') (label : TL.Plaquette → Rep)
    (side : LongParity) (i : Nat) (hi : i < 4) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (longCarrierCode G 1 (by rfl) side i) ≈
      tokenProduct w label (actualLongTokens side i) := by
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;> cases side
  all_goals simp only [actualLongTokens, longWalkTokens, longExternalTokens,
    List.cons_append]
  · exact long_even0_native w label
  · exact long_odd0_native w label
  · exact long_even1_native w label
  · exact long_odd1_native w label
  · exact long_even2_native w label
  · exact long_odd2_native w label
  · exact long_even3_native w label
  · exact long_odd3_native w label

theorem actualLongTokens_sorted_eq
    (side : LongParity) (i : Nat) (hi : i < 4) :
    sortTokens (actualLongTokens side i) =
      sortTokens (canonicalLongTokens side i) := by
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;> cases side <;> rfl

theorem longTokenProduct_normalized (w : Q') (label : TL.Plaquette → Rep)
    (side : LongParity) (i : Nat) (hi : i < 4) :
    tokenProduct w label (actualLongTokens side i) ≈
      tokenProduct w label (canonicalLongTokens side i) := by
  exact tokenProduct_eqv_of_sorted_eq w label
    (actualLongTokens_sorted_eq side i hi)

theorem even0_rhs_native (w : Q') (label : TL.Plaquette → Rep) :
    tokenProduct w label (canonicalLongTokens .even 0) ≈
      endpointActivity w G label *
        indexedPayerAt 1
          (shortActivityOne w G label) (shortActivityTwo w G label)
          (qProd (indexValues (longCount 1) (evenLongActivity w G label)))
          (qProd (indexValues (longCount 1) (oddLongActivity w G label)))
          .even 0 (evenLongActivity w G label)
            (oddLongActivity w G label) := by
  change
    qProd [[tokenActivity w label 0, tokenActivity w label 3,
        tokenActivity w label 1],
      [tokenActivity w label 4, tokenActivity w label 6,
        tokenActivity w label 8, tokenActivity w label 10],
      [tokenActivity w label 5, tokenActivity w label 7,
        tokenActivity w label 9, tokenActivity w label 11],
      [tokenActivity w label 5, tokenActivity w label 7,
        tokenActivity w label 9, tokenActivity w label 11],
      [tokenActivity w label 4, tokenActivity w label 4,
        tokenActivity w label 4]].flatten ≈
      (tokenActivity w label 0 * tokenActivity w label 3) *
        (tokenActivity w label 1 *
          ((qProd [tokenActivity w label 4, tokenActivity w label 6,
              tokenActivity w label 8, tokenActivity w label 10] *
            qProd [tokenActivity w label 5, tokenActivity w label 7,
              tokenActivity w label 9, tokenActivity w label 11]) *
          (qProd [tokenActivity w label 5, tokenActivity w label 7,
              tokenActivity w label 9, tokenActivity w label 11] *
            qCube (tokenActivity w label 4))))
  exact taggedEvenChunks _ _ _ _ _ _

theorem even1_rhs_native (w : Q') (label : TL.Plaquette → Rep) :
    tokenProduct w label (canonicalLongTokens .even 1) ≈
      endpointActivity w G label *
        indexedPayerAt 1
          (shortActivityOne w G label) (shortActivityTwo w G label)
          (qProd (indexValues (longCount 1) (evenLongActivity w G label)))
          (qProd (indexValues (longCount 1) (oddLongActivity w G label)))
          .even 1 (evenLongActivity w G label)
            (oddLongActivity w G label) := by
  change
    qProd [[tokenActivity w label 0, tokenActivity w label 3],
      [tokenActivity w label 4, tokenActivity w label 6,
        tokenActivity w label 8, tokenActivity w label 10],
      [tokenActivity w label 5, tokenActivity w label 7,
        tokenActivity w label 9, tokenActivity w label 11],
      [tokenActivity w label 5, tokenActivity w label 7,
        tokenActivity w label 9, tokenActivity w label 11],
      [tokenActivity w label 6, tokenActivity w label 6,
        tokenActivity w label 6]].flatten ≈
      (tokenActivity w label 0 * tokenActivity w label 3) *
        ((qProd [tokenActivity w label 4, tokenActivity w label 6,
            tokenActivity w label 8, tokenActivity w label 10] *
          qProd [tokenActivity w label 5, tokenActivity w label 7,
            tokenActivity w label 9, tokenActivity w label 11]) *
        (qProd [tokenActivity w label 5, tokenActivity w label 7,
            tokenActivity w label 9, tokenActivity w label 11] *
          qCube (tokenActivity w label 6)))
  exact untaggedEvenChunks _ _ _ _ _

theorem even2_rhs_native (w : Q') (label : TL.Plaquette → Rep) :
    tokenProduct w label (canonicalLongTokens .even 2) ≈
      endpointActivity w G label *
        indexedPayerAt 1
          (shortActivityOne w G label) (shortActivityTwo w G label)
          (qProd (indexValues (longCount 1) (evenLongActivity w G label)))
          (qProd (indexValues (longCount 1) (oddLongActivity w G label)))
          .even 2 (evenLongActivity w G label)
            (oddLongActivity w G label) := by
  change
    qProd [[tokenActivity w label 0, tokenActivity w label 3],
      [tokenActivity w label 4, tokenActivity w label 6,
        tokenActivity w label 8, tokenActivity w label 10],
      [tokenActivity w label 5, tokenActivity w label 7,
        tokenActivity w label 9, tokenActivity w label 11],
      [tokenActivity w label 5, tokenActivity w label 7,
        tokenActivity w label 9, tokenActivity w label 11],
      [tokenActivity w label 8, tokenActivity w label 8,
        tokenActivity w label 8]].flatten ≈
      (tokenActivity w label 0 * tokenActivity w label 3) *
        ((qProd [tokenActivity w label 4, tokenActivity w label 6,
            tokenActivity w label 8, tokenActivity w label 10] *
          qProd [tokenActivity w label 5, tokenActivity w label 7,
            tokenActivity w label 9, tokenActivity w label 11]) *
        (qProd [tokenActivity w label 5, tokenActivity w label 7,
            tokenActivity w label 9, tokenActivity w label 11] *
          qCube (tokenActivity w label 8)))
  exact untaggedEvenChunks _ _ _ _ _

theorem even3_rhs_native (w : Q') (label : TL.Plaquette → Rep) :
    tokenProduct w label (canonicalLongTokens .even 3) ≈
      endpointActivity w G label *
        indexedPayerAt 1
          (shortActivityOne w G label) (shortActivityTwo w G label)
          (qProd (indexValues (longCount 1) (evenLongActivity w G label)))
          (qProd (indexValues (longCount 1) (oddLongActivity w G label)))
          .even 3 (evenLongActivity w G label)
            (oddLongActivity w G label) := by
  change
    qProd [[tokenActivity w label 0, tokenActivity w label 3],
      [tokenActivity w label 4, tokenActivity w label 6,
        tokenActivity w label 8, tokenActivity w label 10],
      [tokenActivity w label 5, tokenActivity w label 7,
        tokenActivity w label 9, tokenActivity w label 11],
      [tokenActivity w label 5, tokenActivity w label 7,
        tokenActivity w label 9, tokenActivity w label 11],
      [tokenActivity w label 10, tokenActivity w label 10,
        tokenActivity w label 10]].flatten ≈
      (tokenActivity w label 0 * tokenActivity w label 3) *
        ((qProd [tokenActivity w label 4, tokenActivity w label 6,
            tokenActivity w label 8, tokenActivity w label 10] *
          qProd [tokenActivity w label 5, tokenActivity w label 7,
            tokenActivity w label 9, tokenActivity w label 11]) *
        (qProd [tokenActivity w label 5, tokenActivity w label 7,
            tokenActivity w label 9, tokenActivity w label 11] *
          qCube (tokenActivity w label 10)))
  exact untaggedEvenChunks _ _ _ _ _

theorem odd0_rhs_native (w : Q') (label : TL.Plaquette → Rep) :
    tokenProduct w label (canonicalLongTokens .odd 0) ≈
      endpointActivity w G label *
        indexedPayerAt 1
          (shortActivityOne w G label) (shortActivityTwo w G label)
          (qProd (indexValues (longCount 1) (evenLongActivity w G label)))
          (qProd (indexValues (longCount 1) (oddLongActivity w G label)))
          .odd 0 (evenLongActivity w G label)
            (oddLongActivity w G label) := by
  change
    qProd [[tokenActivity w label 0, tokenActivity w label 3,
        tokenActivity w label 2],
      [tokenActivity w label 4, tokenActivity w label 6,
        tokenActivity w label 8, tokenActivity w label 10],
      [tokenActivity w label 5, tokenActivity w label 7,
        tokenActivity w label 9, tokenActivity w label 11],
      [tokenActivity w label 4, tokenActivity w label 6,
        tokenActivity w label 8, tokenActivity w label 10],
      [tokenActivity w label 5, tokenActivity w label 5,
        tokenActivity w label 5]].flatten ≈
      (tokenActivity w label 0 * tokenActivity w label 3) *
        (tokenActivity w label 2 *
          ((qProd [tokenActivity w label 4, tokenActivity w label 6,
              tokenActivity w label 8, tokenActivity w label 10] *
            qProd [tokenActivity w label 5, tokenActivity w label 7,
              tokenActivity w label 9, tokenActivity w label 11]) *
          (qProd [tokenActivity w label 4, tokenActivity w label 6,
              tokenActivity w label 8, tokenActivity w label 10] *
            qCube (tokenActivity w label 5))))
  exact taggedOddChunks _ _ _ _ _ _

theorem odd1_rhs_native (w : Q') (label : TL.Plaquette → Rep) :
    tokenProduct w label (canonicalLongTokens .odd 1) ≈
      endpointActivity w G label *
        indexedPayerAt 1
          (shortActivityOne w G label) (shortActivityTwo w G label)
          (qProd (indexValues (longCount 1) (evenLongActivity w G label)))
          (qProd (indexValues (longCount 1) (oddLongActivity w G label)))
          .odd 1 (evenLongActivity w G label)
            (oddLongActivity w G label) := by
  change
    qProd [[tokenActivity w label 0, tokenActivity w label 3],
      [tokenActivity w label 4, tokenActivity w label 6,
        tokenActivity w label 8, tokenActivity w label 10],
      [tokenActivity w label 5, tokenActivity w label 7,
        tokenActivity w label 9, tokenActivity w label 11],
      [tokenActivity w label 4, tokenActivity w label 6,
        tokenActivity w label 8, tokenActivity w label 10],
      [tokenActivity w label 7, tokenActivity w label 7,
        tokenActivity w label 7]].flatten ≈
      (tokenActivity w label 0 * tokenActivity w label 3) *
        ((qProd [tokenActivity w label 4, tokenActivity w label 6,
            tokenActivity w label 8, tokenActivity w label 10] *
          qProd [tokenActivity w label 5, tokenActivity w label 7,
            tokenActivity w label 9, tokenActivity w label 11]) *
        (qProd [tokenActivity w label 4, tokenActivity w label 6,
            tokenActivity w label 8, tokenActivity w label 10] *
          qCube (tokenActivity w label 7)))
  exact untaggedOddChunks _ _ _ _ _

theorem odd2_rhs_native (w : Q') (label : TL.Plaquette → Rep) :
    tokenProduct w label (canonicalLongTokens .odd 2) ≈
      endpointActivity w G label *
        indexedPayerAt 1
          (shortActivityOne w G label) (shortActivityTwo w G label)
          (qProd (indexValues (longCount 1) (evenLongActivity w G label)))
          (qProd (indexValues (longCount 1) (oddLongActivity w G label)))
          .odd 2 (evenLongActivity w G label)
            (oddLongActivity w G label) := by
  change
    qProd [[tokenActivity w label 0, tokenActivity w label 3],
      [tokenActivity w label 4, tokenActivity w label 6,
        tokenActivity w label 8, tokenActivity w label 10],
      [tokenActivity w label 5, tokenActivity w label 7,
        tokenActivity w label 9, tokenActivity w label 11],
      [tokenActivity w label 4, tokenActivity w label 6,
        tokenActivity w label 8, tokenActivity w label 10],
      [tokenActivity w label 9, tokenActivity w label 9,
        tokenActivity w label 9]].flatten ≈
      (tokenActivity w label 0 * tokenActivity w label 3) *
        ((qProd [tokenActivity w label 4, tokenActivity w label 6,
            tokenActivity w label 8, tokenActivity w label 10] *
          qProd [tokenActivity w label 5, tokenActivity w label 7,
            tokenActivity w label 9, tokenActivity w label 11]) *
        (qProd [tokenActivity w label 4, tokenActivity w label 6,
            tokenActivity w label 8, tokenActivity w label 10] *
          qCube (tokenActivity w label 9)))
  exact untaggedOddChunks _ _ _ _ _

theorem odd3_rhs_native (w : Q') (label : TL.Plaquette → Rep) :
    tokenProduct w label (canonicalLongTokens .odd 3) ≈
      endpointActivity w G label *
        indexedPayerAt 1
          (shortActivityOne w G label) (shortActivityTwo w G label)
          (qProd (indexValues (longCount 1) (evenLongActivity w G label)))
          (qProd (indexValues (longCount 1) (oddLongActivity w G label)))
          .odd 3 (evenLongActivity w G label)
            (oddLongActivity w G label) := by
  change
    qProd [[tokenActivity w label 0, tokenActivity w label 3],
      [tokenActivity w label 4, tokenActivity w label 6,
        tokenActivity w label 8, tokenActivity w label 10],
      [tokenActivity w label 5, tokenActivity w label 7,
        tokenActivity w label 9, tokenActivity w label 11],
      [tokenActivity w label 4, tokenActivity w label 6,
        tokenActivity w label 8, tokenActivity w label 10],
      [tokenActivity w label 11, tokenActivity w label 11,
        tokenActivity w label 11]].flatten ≈
      (tokenActivity w label 0 * tokenActivity w label 3) *
        ((qProd [tokenActivity w label 4, tokenActivity w label 6,
            tokenActivity w label 8, tokenActivity w label 10] *
          qProd [tokenActivity w label 5, tokenActivity w label 7,
            tokenActivity w label 9, tokenActivity w label 11]) *
        (qProd [tokenActivity w label 4, tokenActivity w label 6,
            tokenActivity w label 8, tokenActivity w label 10] *
          qCube (tokenActivity w label 11)))
  exact untaggedOddChunks _ _ _ _ _

theorem long_rhs_native (w : Q') (label : TL.Plaquette → Rep)
    (side : LongParity) (i : Nat) (hi : i < 4) :
    tokenProduct w label (canonicalLongTokens side i) ≈
      endpointActivity w G label *
        indexedPayerAt 1
          (shortActivityOne w G label) (shortActivityTwo w G label)
          (qProd (indexValues (longCount 1) (evenLongActivity w G label)))
          (qProd (indexValues (longCount 1) (oddLongActivity w G label)))
          side i (evenLongActivity w G label)
            (oddLongActivity w G label) := by
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;> cases side
  · exact even0_rhs_native w label
  · exact odd0_rhs_native w label
  · exact even1_rhs_native w label
  · exact odd1_rhs_native w label
  · exact even2_rhs_native w label
  · exact odd2_rhs_native w label
  · exact even3_rhs_native w label
  · exact odd3_rhs_native w label

theorem c12_long_word (w : Q') (label : TL.Plaquette → Rep)
    (side : LongParity) (i : Nat) (hi : i < longCount 1) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (longCarrierCode G 1 (by rfl) side i) ≈
      endpointActivity w G label *
        indexedPayerAt 1
          (shortActivityOne w G label) (shortActivityTwo w G label)
          (qProd (indexValues (longCount 1) (evenLongActivity w G label)))
          (qProd (indexValues (longCount 1) (oddLongActivity w G label)))
          side i (evenLongActivity w G label)
            (oddLongActivity w G label) := by
  have hi4 : i < 4 := by simpa [longCount] using hi
  exact Q'.eqv_trans _ _ _ (long_native w label side i hi4)
    (Q'.eqv_trans _ _ _ (longTokenProduct_normalized w label side i hi4)
      (long_rhs_native w label side i hi4))

def actualSourceTokens : List Nat :=
  [1, 3, 5, 7, 9, 11, 0, 2, 4, 6, 8, 10]

def canonicalSourceTokens : List Nat :=
  [0, 3, 1, 2, 4, 6, 8, 10, 5, 7, 9, 11]

theorem source_actual_native (w : Q') (label : TL.Plaquette → Rep) :
    occurrencePairWeight w qAll markV0 badV3 G label pair ≈
      tokenProduct w label actualSourceTokens := by
  rw [occurrencePairWeight_eq_source_activity_of_mem
    w qAll markV0 badV3 G label pair pair_mem]
  change
    qProd ([1, 3, 5, 7, 9, 11].map (tokenActivity w label)) *
      qProd ([0, 2, 4, 6, 8, 10].map (tokenActivity w label)) ≈
      tokenProduct w label actualSourceTokens
  unfold actualSourceTokens
  exact twoTokenBlocks_native w label _ _

theorem source_tokens_sorted_eq :
    sortTokens actualSourceTokens = sortTokens canonicalSourceTokens := by
  rfl

theorem source_tokenProduct_normalized
    (w : Q') (label : TL.Plaquette → Rep) :
    tokenProduct w label actualSourceTokens ≈
      tokenProduct w label canonicalSourceTokens := by
  exact tokenProduct_eqv_of_sorted_eq w label source_tokens_sorted_eq

theorem source_rhs_native (w : Q') (label : TL.Plaquette → Rep) :
    tokenProduct w label canonicalSourceTokens ≈
      endpointActivity w G label *
        uniformSource
          (shortActivityOne w G label) (shortActivityTwo w G label)
          (indexValues (longCount 1) (evenLongActivity w G label))
          (indexValues (longCount 1) (oddLongActivity w G label)) := by
  change
    qProd [[tokenActivity w label 0, tokenActivity w label 3],
      [tokenActivity w label 1, tokenActivity w label 2],
      [tokenActivity w label 4, tokenActivity w label 6,
        tokenActivity w label 8, tokenActivity w label 10],
      [tokenActivity w label 5, tokenActivity w label 7,
        tokenActivity w label 9, tokenActivity w label 11]].flatten ≈
      (tokenActivity w label 0 * tokenActivity w label 3) *
        ((tokenActivity w label 1 * tokenActivity w label 2) *
          (qProd [tokenActivity w label 4, tokenActivity w label 6,
              tokenActivity w label 8, tokenActivity w label 10] *
            qProd [tokenActivity w label 5, tokenActivity w label 7,
              tokenActivity w label 9, tokenActivity w label 11]))
  exact sourceChunks _ _ _ _ _ _

theorem c12_source_word (w : Q') (label : TL.Plaquette → Rep) :
    occurrencePairWeight w qAll markV0 badV3 G label entry.1 ≈
      endpointActivity w G label *
        uniformSource
          (shortActivityOne w G label) (shortActivityTwo w G label)
          (indexValues (longCount 1) (evenLongActivity w G label))
          (indexValues (longCount 1) (oddLongActivity w G label)) := by
  exact Q'.eqv_trans _ _ _ (source_actual_native w label)
    (Q'.eqv_trans _ _ _ (source_tokenProduct_normalized w label)
      (source_rhs_native w label))

def shortErased : CarrierXiCode TL :=
  ((V0, chainFromPolyList [V1, V2, V1, V2, V3]), [])

theorem short_erasure :
    eraseOccCarrierXiCode G (shortCarrierCode G 1 (by rfl)) =
      shortErased := by
  rfl

def actualShortTokens : List Nat := [0, 1, 2, 1, 2, 3]
def canonicalShortTokens : List Nat := [0, 3, 1, 2, 1, 2]

theorem short_actual_native (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (shortCarrierCode G 1 (by rfl)) ≈
      tokenProduct w label actualShortTokens := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (shortCarrierCode G 1 (by rfl)) =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G (shortCarrierCode G 1 (by rfl))) from rfl]
  rw [short_erasure]
  change
    qProd ([0, 1, 2, 1, 2, 3].map (tokenActivity w label)) *
      qProd (([] : List Nat).map (tokenActivity w label)) ≈
      tokenProduct w label actualShortTokens
  unfold actualShortTokens
  exact twoTokenBlocks_native w label _ _

theorem short_tokens_sorted_eq :
    sortTokens actualShortTokens = sortTokens canonicalShortTokens := by
  rfl

theorem short_tokenProduct_normalized
    (w : Q') (label : TL.Plaquette → Rep) :
    tokenProduct w label actualShortTokens ≈
      tokenProduct w label canonicalShortTokens := by
  exact tokenProduct_eqv_of_sorted_eq w label short_tokens_sorted_eq

theorem short_rhs_native (w : Q') (label : TL.Plaquette → Rep) :
    tokenProduct w label canonicalShortTokens ≈
      endpointActivity w G label *
        shortSquare (shortActivityOne w G label)
          (shortActivityTwo w G label) := by
  change
    qProd [[tokenActivity w label 0, tokenActivity w label 3],
      [tokenActivity w label 1, tokenActivity w label 2],
      [tokenActivity w label 1, tokenActivity w label 2]].flatten ≈
      (tokenActivity w label 0 * tokenActivity w label 3) *
        shortSquare (tokenActivity w label 1) (tokenActivity w label 2)
  exact shortChunks _ _ _ _

theorem c12_short_word (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (shortCarrierCode G 1 (by rfl)) ≈
      endpointActivity w G label *
        shortSquare (shortActivityOne w G label)
          (shortActivityTwo w G label) := by
  exact Q'.eqv_trans _ _ _ (short_actual_native w label)
    (Q'.eqv_trans _ _ _ (short_tokenProduct_normalized w label)
      (short_rhs_native w label))

def c12Geometry :
    CanonicalEarWordGeometry qAll markV0 badV3 G 1 (by rfl) entry where
  source_word := c12_source_word
  short_word := c12_short_word
  long_word := c12_long_word

def c12PaidResidualBlock : PaidResidualBlock qAll markV0 badV3 G entry :=
  c12Geometry.paidBlock

def c12Test (other : ExceptionalSourceEntry G qAll markV0 badV3) : Bool :=
  decide (other = entry)

theorem c12Test_true_iff
    (other : ExceptionalSourceEntry G qAll markV0 badV3) :
    c12Test other = true ↔ other = entry := by
  constructor
  · exact of_decide_eq_true
  · exact decide_eq_true

def c12OwnedFamily : OwnedPaidResidualFamily qAll markV0 badV3 G where
  test := c12Test
  cert := fun selected =>
    (c12Test_true_iff selected.1).mp selected.2 |>.symm ▸
      c12PaidResidualBlock
  owner := fun _ => entry
  block_owner := by
    intro selected code _
    exact ((c12Test_true_iff selected.1).mp selected.2).symm

def c12GlobalFamily : GlobalPaidResidualFamily qAll markV0 badV3 G :=
  c12OwnedFamily.toGlobal

def c12Allocator : MixedRepairAllocator G qAll markV0 badV3 :=
  c12OwnedFamily.allocator

theorem c12_entry_test_true : c12OwnedFamily.test entry = true := by
  exact (c12Test_true_iff entry).mpr rfl

theorem c12_entry_mem_mixedRepairSource :
    entry ∈ mixedRepairSource c12Allocator := by
  exact tested_entry_mem_mixedRepairSource c12GlobalFamily entry
    entry_mem_threeBranchResidual c12_entry_test_true

theorem c12_entry_not_mem_fourBranchResidual :
    entry ∉ fourBranchResidualSource c12Allocator := by
  exact tested_entry_not_mem_fourBranchResidual c12GlobalFamily entry
    c12_entry_test_true

#print axioms qProd_perm_eqv
#print axioms sortTokens_product
#print axioms tokenProduct_eqv_of_sorted_eq
#print axioms long_native
#print axioms long_rhs_native
#print axioms actualLongTokens_sorted_eq
#print axioms longTokenProduct_normalized
#print axioms source_actual_native
#print axioms source_tokenProduct_normalized
#print axioms short_actual_native
#print axioms short_tokenProduct_normalized
#print axioms c12_long_word
#print axioms c12_source_word
#print axioms c12_short_word
#print axioms c12Geometry
#print axioms c12PaidResidualBlock
#print axioms c12OwnedFamily
#print axioms c12_entry_mem_mixedRepairSource
#print axioms c12_entry_not_mem_fourBranchResidual

end YMGap.Continuum.XiExceptionalGeneralLongArmC12Native
