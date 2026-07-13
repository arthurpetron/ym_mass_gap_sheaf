/-
# Eight sharp C12 omission carriers

The first single-reserve failure has a length-eighteen long square but only
thirteen carrier vertices and four compatible external long-arm slots.  This
module replaces the impossible single square by eight distinct sharp carrier
codes.  Code `omitK` carries two copies of every long-arm activity except
`V_K`.  The `omit4` and `omit5` codes also carry one of the two short-arm
activities.  Together with the short square, their exact weights are the
nine payer monomials of `XiExceptionalMultiReserveAlgebra`.
-/

import YMGap.Continuum.XiExceptionalMultiReserveAlgebra
import YMGap.Continuum.XiExceptionalTraceFuelSharp

namespace YMGap.Continuum.XiExceptionalC12MultiReserveRepair

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalEarPairBounce
open YMGap.Continuum.XiExceptionalEarOccurrenceCarrier
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFourthMixedRepair
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalTraceFuelSharp
open YMGap.Continuum.XiExceptionalExternalReserveLimitFence
open YMGap.Continuum.XiExceptionalMultiReserveAlgebra

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

def allEdge : Nat → Nat → Bool := fun _ _ => true

/-- Build the unique cons-form walk through a prescribed tail.  The endpoint
is retained in the sigma index and computes on every closed tail below. -/
def allWalkFrom : (x : Nat) → (tail : List Nat) →
    Σ y, CWalk allEdge x y
  | x, [] => ⟨x, .single x⟩
  | _, y :: ys =>
      match allWalkFrom y ys with
      | ⟨z, rest⟩ => ⟨z, .cons rfl rest⟩

inductive LongOmission where
  | o4 | o5 | o6 | o7 | o8 | o9 | o10 | o11
deriving DecidableEq

def omissionWalk : LongOmission → CWalk allEdge 0 3
  | .o4 => (allWalkFrom 0 [11, 10, 10, 9, 8, 8, 7, 6, 6, 5, 4, 3]).2
  | .o5 => (allWalkFrom 0 [11, 11, 10, 9, 9, 8, 7, 7, 6, 5, 4, 3]).2
  | .o6 => (allWalkFrom 0 [11, 10, 10, 9, 8, 8, 7, 6, 5, 4, 4, 3]).2
  | .o7 => (allWalkFrom 0 [11, 11, 10, 9, 9, 8, 7, 6, 5, 5, 4, 3]).2
  | .o8 => (allWalkFrom 0 [11, 10, 10, 9, 8, 7, 6, 6, 5, 4, 4, 3]).2
  | .o9 => (allWalkFrom 0 [11, 11, 10, 9, 8, 7, 7, 6, 5, 5, 4, 3]).2
  | .o10 => (allWalkFrom 0 [11, 10, 9, 8, 8, 7, 6, 6, 5, 4, 4, 3]).2
  | .o11 => (allWalkFrom 0 [11, 10, 9, 9, 8, 7, 7, 6, 5, 5, 4, 3]).2

def emptyBits : OccBitVec Gamma.length :=
  bits12 false false false false false false false false false false false false

/-- Opposite-parity reserves are compatible.  `o4` and `o5` additionally
carry, respectively, the compatible short variables `V1` and `V2`. -/
def omissionExternal : LongOmission → OccBitVec Gamma.length
  | .o4 =>
      bits12 false true false false false true false true false true false true
  | .o5 =>
      bits12 false false true false true false true false true false true false
  | .o6 | .o8 | .o10 =>
      bits12 false false false false false true false true false true false true
  | .o7 | .o9 | .o11 =>
      bits12 false false false false true false true false true false true false

def omissionCode (o : LongOmission) : OccCarrierXiCodeAt Gamma :=
  { carrier :=
      { start := 0
        chain := occurrenceChainCodeOfWalk (omissionWalk o) emptyBits }
    external := omissionExternal o }

private theorem edge_symm (i j : Nat)
    (h : incAtDistinct Gamma i j = true) :
    incAtDistinct Gamma j i = true := by
  rw [incAtDistinct_symm Gamma]
  exact h

def shortSquareCode : OccCarrierXiCodeAt Gamma :=
  pairedBounceCarrierCode Gamma shortArc edge_symm emptyBits emptyBits

theorem omissionWalk_length (o : LongOmission) :
    (omissionWalk o).vertices.length = 13 := by
  cases o <;> rfl

theorem omissionWalk_bounds (o : LongOmission) :
    ∀ k, k ∈ (omissionWalk o).vertices → k < Gamma.length := by
  intro k hk
  cases o <;>
    simp only [omissionWalk, allWalkFrom, CWalk.vertices, List.mem_cons,
      List.not_mem_nil, or_false] at hk <;>
    simp only [Gamma, List.length_cons, List.length_nil] <;>
    omega

theorem omissionCode_mem (o : LongOmission) :
    omissionCode o ∈ occurrenceCarrierXiCodes Gamma := by
  unfold omissionCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨omissionExternal o, bitVectors_complete (omissionExternal o), ?_⟩
  apply List.mem_map.mpr
  refine ⟨⟨0, occurrenceChainCodeOfWalk (omissionWalk o) emptyBits⟩, ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨0, occurrenceIndices_complete (by decide), ?_⟩
  apply List.mem_map.mpr
  refine ⟨occurrenceChainCodeOfWalk (omissionWalk o) emptyBits, ?_, rfl⟩
  apply occurrenceChainCodeOfWalk_mem_sharp Gamma emptyBits
    (omissionWalk o) Gamma.length
  · rw [omissionWalk_length]
    decide
  · exact omissionWalk_bounds o

theorem shortSquareCode_mem :
    shortSquareCode ∈ occurrenceCarrierXiCodes Gamma := by
  unfold shortSquareCode
  apply pairedBounceCarrierCode_mem Gamma shortArc edge_symm emptyBits emptyBits
  · decide
  · decide
  · intro k hk
    simp [shortArc, PairedPath.bounceWalk, CWalk.vertices, Gamma] at hk ⊢
    omega

def repairBlock : List (OccCarrierXiCodeAt Gamma) :=
  [shortSquareCode, omissionCode .o4, omissionCode .o5,
    omissionCode .o6, omissionCode .o7, omissionCode .o8,
    omissionCode .o9, omissionCode .o10, omissionCode .o11]

set_option maxRecDepth 1000000 in
theorem repairBlock_nodup : repairBlock.Nodup := by
  decide

theorem repairBlock_mem (code : OccCarrierXiCodeAt Gamma)
    (hcode : code ∈ repairBlock) :
    code ∈ occurrenceCarrierXiCodes Gamma := by
  simp only [repairBlock, List.mem_cons, List.not_mem_nil, or_false] at hcode
  rcases hcode with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact shortSquareCode_mem
  all_goals exact omissionCode_mem _

/-! ## Exact normalization of the nine target codes -/

def commonWeight (w : Q') (label : TL.Plaquette → Rep) : Q' :=
  activity w V0 label * activity w V3 label

def omissionPayer (w : Q') (label : TL.Plaquette → Rep) :
    LongOmission → Q'
  | .o4 => omit4 (activity w V1 label)
      (activity w V4 label) (activity w V5 label)
      (activity w V6 label) (activity w V7 label)
      (activity w V8 label) (activity w V9 label)
      (activity w V10 label) (activity w V11 label)
  | .o5 => omit5 (activity w V2 label)
      (activity w V4 label) (activity w V5 label)
      (activity w V6 label) (activity w V7 label)
      (activity w V8 label) (activity w V9 label)
      (activity w V10 label) (activity w V11 label)
  | .o6 => omit6
      (activity w V4 label) (activity w V5 label)
      (activity w V6 label) (activity w V7 label)
      (activity w V8 label) (activity w V9 label)
      (activity w V10 label) (activity w V11 label)
  | .o7 => omit7
      (activity w V4 label) (activity w V5 label)
      (activity w V6 label) (activity w V7 label)
      (activity w V8 label) (activity w V9 label)
      (activity w V10 label) (activity w V11 label)
  | .o8 => omit8
      (activity w V4 label) (activity w V5 label)
      (activity w V6 label) (activity w V7 label)
      (activity w V8 label) (activity w V9 label)
      (activity w V10 label) (activity w V11 label)
  | .o9 => omit9
      (activity w V4 label) (activity w V5 label)
      (activity w V6 label) (activity w V7 label)
      (activity w V8 label) (activity w V9 label)
      (activity w V10 label) (activity w V11 label)
  | .o10 => omit10
      (activity w V4 label) (activity w V5 label)
      (activity w V6 label) (activity w V7 label)
      (activity w V8 label) (activity w V9 label)
      (activity w V10 label) (activity w V11 label)
  | .o11 => omit11
      (activity w V4 label) (activity w V5 label)
      (activity w V6 label) (activity w V7 label)
      (activity w V8 label) (activity w V9 label)
      (activity w V10 label) (activity w V11 label)

def chainFromList : List (Polymer TL) → ChainCode TL.Plaquette
  | [] => .terminal []
  | X :: xs => .step X (chainFromList xs)

def erasedOmission : LongOmission → CarrierXiCode TL
  | .o4 => ((V0, chainFromList
      [V11, V10, V10, V9, V8, V8, V7, V6, V6, V5, V4, V3]),
      [V1, V5, V7, V9, V11])
  | .o5 => ((V0, chainFromList
      [V11, V11, V10, V9, V9, V8, V7, V7, V6, V5, V4, V3]),
      [V2, V4, V6, V8, V10])
  | .o6 => ((V0, chainFromList
      [V11, V10, V10, V9, V8, V8, V7, V6, V5, V4, V4, V3]),
      [V5, V7, V9, V11])
  | .o7 => ((V0, chainFromList
      [V11, V11, V10, V9, V9, V8, V7, V6, V5, V5, V4, V3]),
      [V4, V6, V8, V10])
  | .o8 => ((V0, chainFromList
      [V11, V10, V10, V9, V8, V7, V6, V6, V5, V4, V4, V3]),
      [V5, V7, V9, V11])
  | .o9 => ((V0, chainFromList
      [V11, V11, V10, V9, V8, V7, V7, V6, V5, V5, V4, V3]),
      [V4, V6, V8, V10])
  | .o10 => ((V0, chainFromList
      [V11, V10, V9, V8, V8, V7, V6, V6, V5, V4, V4, V3]),
      [V5, V7, V9, V11])
  | .o11 => ((V0, chainFromList
      [V11, V10, V9, V9, V8, V7, V7, V6, V5, V5, V4, V3]),
      [V4, V6, V8, V10])

theorem omissionCode_erasure (o : LongOmission) :
    eraseOccCarrierXiCode Gamma (omissionCode o) = erasedOmission o := by
  cases o <;> rfl

theorem shortSquareCode_erasure :
    eraseOccCarrierXiCode Gamma shortSquareCode =
      ((V0, chainFromList [V1, V2, V1, V2, V3]), []) := by
  rfl

private theorem mark_start : markV0 V0 = true := by rfl
private theorem bad_finish : badV3 V3 = true := by rfl
private theorem c01 : compatibleB V0 V1 = false := by rfl
private theorem c12 : compatibleB V1 V2 = false := by rfl
private theorem c21 : compatibleB V2 V1 = false := by rfl
private theorem c23 : compatibleB V2 V3 = false := by rfl
private theorem c0_11 : compatibleB V0 V11 = false := by rfl
private theorem c11_10 : compatibleB V11 V10 = false := by rfl
private theorem c10_9 : compatibleB V10 V9 = false := by rfl
private theorem c9_8 : compatibleB V9 V8 = false := by rfl
private theorem c8_7 : compatibleB V8 V7 = false := by rfl
private theorem c7_6 : compatibleB V7 V6 = false := by rfl
private theorem c6_5 : compatibleB V6 V5 = false := by rfl
private theorem c5_4 : compatibleB V5 V4 = false := by rfl
private theorem c4_3 : compatibleB V4 V3 = false := by rfl
private theorem c11_11 : compatibleB V11 V11 = false := by rfl
private theorem c10_10 : compatibleB V10 V10 = false := by rfl
private theorem c9_9 : compatibleB V9 V9 = false := by rfl
private theorem c8_8 : compatibleB V8 V8 = false := by rfl
private theorem c7_7 : compatibleB V7 V7 = false := by rfl
private theorem c6_6 : compatibleB V6 V6 = false := by rfl
private theorem c5_5 : compatibleB V5 V5 = false := by rfl
private theorem c4_4 : compatibleB V4 V4 = false := by rfl
private theorem external_o4_compatible :
    familyCompatibleB [V1, V5, V7, V9, V11] = true := by rfl
private theorem external_o5_compatible :
    familyCompatibleB [V2, V4, V6, V8, V10] = true := by rfl
private theorem external_odd_compatible :
    familyCompatibleB [V5, V7, V9, V11] = true := by rfl
private theorem external_even_compatible :
    familyCompatibleB [V4, V6, V8, V10] = true := by rfl

theorem omissionCode_weight_eqv
    (w : Q') (label : TL.Plaquette → Rep) (o : LongOmission) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label
        (omissionCode o) ≈
      commonWeight w label * omissionPayer w label o := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label
      (omissionCode o) =
        carrierXiCodeWeight w qAll markV0 badV3 Gamma label
          (eraseOccCarrierXiCode Gamma (omissionCode o)) from rfl]
  rw [omissionCode_erasure]
  cases o <;>
    simp only [erasedOmission, chainFromList, carrierXiCodeWeight,
      carrierCodeWeight, qAll, mark_start, Bool.true_and, if_true,
      chainCodeWeight, c0_11, c11_10, c10_9, c9_8, c8_7, c7_6, c6_5,
      c5_4, c4_3, c11_11, c10_10, c9_9, c8_8, c7_7, c6_6, c5_5,
      c4_4, Bool.not_false, bad_finish, admissibleFamilyWeight,
      List.all_cons, List.all_nil, Bool.and_self, familyCompatibleB_nil,
      external_o4_compatible, external_o5_compatible,
      external_odd_compatible, external_even_compatible,
      familyActivity_cons, familyActivity_nil] <;>
    unfold commonWeight omissionPayer omit4 omit5 omit6 omit7 omit8 omit9
      omit10 omit11 longProduct <;>
    ring_qeqv

theorem shortSquareCode_weight_eqv
    (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label
        shortSquareCode ≈
      commonWeight w label *
        shortSquare (activity w V1 label) (activity w V2 label) := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label
      shortSquareCode =
        carrierXiCodeWeight w qAll markV0 badV3 Gamma label
          (eraseOccCarrierXiCode Gamma shortSquareCode) from rfl]
  rw [shortSquareCode_erasure]
  simp only [chainFromList, carrierXiCodeWeight, carrierCodeWeight, qAll,
    mark_start, Bool.true_and, if_true, chainCodeWeight, c01, c12, c21,
    c23, Bool.not_false, bad_finish, admissibleFamilyWeight, List.all_nil,
    familyCompatibleB_nil, familyActivity_nil]
  unfold commonWeight shortSquare
  ring_qeqv

/-! ## Aggregate payment of the actual C12 source -/

private theorem left_family :
    leftFamily Gamma pair = [V1, V3, V5, V7, V9, V11] := by
  rfl

private theorem right_family :
    rightFamily Gamma pair = [V0, V2, V4, V6, V8, V10] := by
  rfl

theorem source_weight_eqv (w : Q') (label : TL.Plaquette → Rep) :
    occurrencePairWeight w qAll markV0 badV3 Gamma label pair ≈
      commonWeight w label *
        sourceInterior (activity w V1 label) (activity w V2 label)
          (activity w V4 label) (activity w V5 label)
          (activity w V6 label) (activity w V7 label)
          (activity w V8 label) (activity w V9 label)
          (activity w V10 label) (activity w V11 label) := by
  rw [occurrencePairWeight_eq_source_activity_of_mem
    w qAll markV0 badV3 Gamma label pair pair_mem]
  rw [left_family, right_family]
  simp only [familyActivity_cons, familyActivity_nil]
  unfold commonWeight sourceInterior longProduct
  ring_qeqv

theorem repairBlock_weight_eqv (w : Q') (label : TL.Plaquette → Rep) :
    qListSum
        (occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label)
        repairBlock ≈
      commonWeight w label * qListSum id
        (augmentedPayers (activity w V1 label) (activity w V2 label)
          (activity w V4 label) (activity w V5 label)
          (activity w V6 label) (activity w V7 label)
          (activity w V8 label) (activity w V9 label)
          (activity w V10 label) (activity w V11 label)) := by
  simp only [repairBlock, augmentedPayers, qListSum_cons, qListSum_nil,
    id_eq]
  refine Q'.eqv_trans _
    (commonWeight w label *
        shortSquare (activity w V1 label) (activity w V2 label) +
      (commonWeight w label * omissionPayer w label .o4 +
      (commonWeight w label * omissionPayer w label .o5 +
      (commonWeight w label * omissionPayer w label .o6 +
      (commonWeight w label * omissionPayer w label .o7 +
      (commonWeight w label * omissionPayer w label .o8 +
      (commonWeight w label * omissionPayer w label .o9 +
      (commonWeight w label * omissionPayer w label .o10 +
      (commonWeight w label * omissionPayer w label .o11 + 0))))))))) _ ?_ ?_
  · exact add_eqv_congr_both _ _ _ _
      (shortSquareCode_weight_eqv w label)
      (add_eqv_congr_both _ _ _ _
        (omissionCode_weight_eqv w label .o4)
        (add_eqv_congr_both _ _ _ _
          (omissionCode_weight_eqv w label .o5)
          (add_eqv_congr_both _ _ _ _
            (omissionCode_weight_eqv w label .o6)
            (add_eqv_congr_both _ _ _ _
              (omissionCode_weight_eqv w label .o7)
              (add_eqv_congr_both _ _ _ _
                (omissionCode_weight_eqv w label .o8)
                (add_eqv_congr_both _ _ _ _
                  (omissionCode_weight_eqv w label .o9)
                  (add_eqv_congr_both _ _ _ _
                    (omissionCode_weight_eqv w label .o10)
                    (add_eqv_congr_both _ _ _ _
                      (omissionCode_weight_eqv w label .o11)
                      (Q'.eqv_refl _)))))))))
  · simpa only [augmentedPayers, omissionPayer, qListSum_cons,
      qListSum_nil, id_eq] using
      (qListSum_const_mul (commonWeight w label) id
        (augmentedPayers (activity w V1 label) (activity w V2 label)
          (activity w V4 label) (activity w V5 label)
          (activity w V6 label) (activity w V7 label)
          (activity w V8 label) (activity w V9 label)
          (activity w V10 label) (activity w V11 label)))

theorem source_le_repairBlock {w : Q'} (hw : (0 : Q') ≤ w)
    (label : TL.Plaquette → Rep) :
    occurrencePairWeight w qAll markV0 badV3 Gamma label pair ≤
      qListSum
        (occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label)
        repairBlock := by
  have h1 := activity_nonneg hw V1 label
  have h2 := activity_nonneg hw V2 label
  have h4 := activity_nonneg hw V4 label
  have h5 := activity_nonneg hw V5 label
  have h6 := activity_nonneg hw V6 label
  have h7 := activity_nonneg hw V7 label
  have h8 := activity_nonneg hw V8 label
  have h9 := activity_nonneg hw V9 label
  have h10 := activity_nonneg hw V10 label
  have h11 := activity_nonneg hw V11 label
  have hinterior := augmentedPayers_pay
    (activity w V1 label) (activity w V2 label)
    (activity w V4 label) (activity w V5 label)
    (activity w V6 label) (activity w V7 label)
    (activity w V8 label) (activity w V9 label)
    (activity w V10 label) (activity w V11 label)
    h1 h2 h4 h5 h6 h7 h8 h9 h10 h11
  have hcommon : (0 : Q') ≤ commonWeight w label :=
    Q'.mul_nonneg _ _ (activity_nonneg hw V0 label)
      (activity_nonneg hw V3 label)
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (sourceInterior (activity w V1 label) (activity w V2 label)
      (activity w V4 label) (activity w V5 label)
      (activity w V6 label) (activity w V7 label)
      (activity w V8 label) (activity w V9 label)
      (activity w V10 label) (activity w V11 label))
    (qListSum id
      (augmentedPayers (activity w V1 label) (activity w V2 label)
        (activity w V4 label) (activity w V5 label)
        (activity w V6 label) (activity w V7 label)
        (activity w V8 label) (activity w V9 label)
        (activity w V10 label) (activity w V11 label)))
    (commonWeight w label) hinterior hcommon
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (source_weight_eqv w label))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.ge_of_eqv (repairBlock_weight_eqv w label)))

/-! ## Source-decodable keys and the local disjoint allocator -/

def sourceBlockKey
    (other : ExceptionalSourceEntry Gamma qAll markV0 badV3) :
    OccCarrierXiCodeAt Gamma :=
  exceptionalBranchCarrierCode Gamma qAll markV0 badV3 other

theorem sourceBlockKey_mem
    (other : ExceptionalSourceEntry Gamma qAll markV0 badV3) :
    sourceBlockKey other ∈ occurrenceCarrierXiCodes Gamma :=
  exceptionalBranchCarrierCode_mem Gamma qAll markV0 badV3 other

theorem sourceBlockKey_injective
    {a b : ExceptionalSourceEntry Gamma qAll markV0 badV3}
    (hkey : sourceBlockKey a = sourceBlockKey b) : a = b := by
  exact exceptionalBranchCarrierCode_injective Gamma qAll markV0 badV3
    a b hkey

def carriesSourceKeyB
    (other : ExceptionalSourceEntry Gamma qAll markV0 badV3) : Bool :=
  decide (sourceBlockKey other = sourceBlockKey entry)

theorem carriesSourceKeyB_true_iff
    (other : ExceptionalSourceEntry Gamma qAll markV0 badV3) :
    carriesSourceKeyB other = true ↔ other = entry := by
  constructor
  · intro h
    exact sourceBlockKey_injective (of_decide_eq_true h)
  · intro h
    subst other
    exact decide_eq_true rfl

/-- Distinct sources have disjoint singleton key blocks.  This is the raw
cross-source key needed when the local nine-code payload is replicated by a
global allocator. -/
theorem distinct_source_key_blocks_disjoint
    (a b : ExceptionalSourceEntry Gamma qAll markV0 badV3)
    (hne : a ≠ b) :
    ∀ code, code ∈ [sourceBlockKey a] →
      code ∈ [sourceBlockKey b] → False := by
  intro code ha hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  exact hne (sourceBlockKey_injective (ha.symm.trans hb))

def allocator : MixedRepairAllocator Gamma qAll markV0 badV3 where
  test := carriesSourceKeyB
  block := fun _ => repairBlock
  block_nodup := by
    intro _ _
    exact repairBlock_nodup
  block_mem := by
    intro _ _ code hcode
    exact repairBlock_mem code hcode
  blocks_disjoint := by
    intro a ha b hb hab
    have hae : a = entry := (carriesSourceKeyB_true_iff a).mp ha
    have hbe : b = entry := (carriesSourceKeyB_true_iff b).mp hb
    exact False.elim (hab (hae.trans hbe.symm))
  source_le_block := by
    intro w hw label other htest
    have hother : other = entry :=
      (carriesSourceKeyB_true_iff other).mp htest
    subst other
    exact source_le_repairBlock hw label

theorem entry_test_true : allocator.test entry = true :=
  (carriesSourceKeyB_true_iff entry).mpr rfl

theorem entry_mem_mixedRepairSource :
    entry ∈ mixedRepairSource allocator := by
  apply List.mem_filter.mpr
  exact ⟨entry_mem_threeBranchResidual, entry_test_true⟩

#print axioms omissionCode_mem
#print axioms shortSquareCode_mem
#print axioms repairBlock_nodup
#print axioms repairBlock_mem
#print axioms omissionCode_erasure
#print axioms omissionCode_weight_eqv
#print axioms shortSquareCode_weight_eqv
#print axioms source_weight_eqv
#print axioms repairBlock_weight_eqv
#print axioms source_le_repairBlock
#print axioms sourceBlockKey_mem
#print axioms sourceBlockKey_injective
#print axioms carriesSourceKeyB_true_iff
#print axioms distinct_source_key_blocks_disjoint
#print axioms entry_mem_mixedRepairSource

end YMGap.Continuum.XiExceptionalC12MultiReserveRepair
