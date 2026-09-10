/-
# Lift the fine-child activity payment to a complete component word

The preceding local estimate assigns a weight to every literal fine-child
code and bounds the total one-face mass by a number strictly below nine on
the named strong-coupling interval.  This file performs the exact Cartesian
lift to a component of arbitrary size.

For a word of child codes, the product of the local weights is exactly the
single heat factor whose exponent is three times the total activity excess.
For all words of length `S`, the total product mass is exactly the `S`th
power of the one-face mass, and is therefore bounded by `9^S` throughout
`0 <= rate <= 1/400`.

The actual cross-scale component compiles into this word carrier, and its
word weight is exactly the activity-excess factor already present in the
global heat decomposition.  Thus the weighted enumeration consumes existing
SU(2) heat; it does not introduce a new majorant or a beta-uniform claim.

Constructive contract: structural list induction and exact rational
setoid algebra only; no classical choice, proof hole, trusted external
computation, computability escape, enlarged heartbeat budget, or new
axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedComponentChildWeightedEntropy
import YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyCode
import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

namespace YMGap.Continuum.Z4DyadicBinaryConnectedComponentChildWeightedWord

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentChildCode
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentChildWeightedEntropy
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyCode
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_mul_right_local {A : Type}
    (weight : A → Q') (constant : Q') : ∀ items : List A,
    listQSum (fun item => weight item * constant) items ≈
      listQSum weight items * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | head :: tail => by
      change weight head * constant +
          listQSum (fun item => weight item * constant) tail ≈
        (weight head + listQSum weight tail) * constant
      exact Q'.eqv_trans _
        (weight head * constant + listQSum weight tail * constant) _
        (Q'.add_eqv_congr_left _ _ _
          (listQSum_mul_right_local weight constant tail))
        (Q'.eqv_symm
          (Q'.add_mul_eqv (weight head) (listQSum weight tail) constant))

/-! ## 1. Generic weighted words -/

private theorem finiteWordsOfLength_weightedMass_eqv_qpow
    {A : Type} (alphabet : List A) (weight : A → Q') : ∀ length,
    listQSum (fun word => listQProduct weight word)
        (finiteWordsOfLength alphabet length) ≈
      qpow (listQSum weight alphabet) length
  | 0 => Q'.eqv_of_eq (Q'.add_zero' 1)
  | length + 1 => by
      unfold finiteWordsOfLength
      refine Q'.eqv_trans _
        (listQSum
          (fun head =>
            listQSum (fun word => listQProduct weight word)
              ((finiteWordsOfLength alphabet length).map
                fun tail => head :: tail))
          alphabet) _
        (listQSum_flatMap _ _ alphabet) ?_
      refine Q'.eqv_trans _
        (listQSum
          (fun head =>
            listQSum
              (fun tail => weight head * listQProduct weight tail)
              (finiteWordsOfLength alphabet length))
          alphabet) _ ?_ ?_
      · apply listQSum_congr
        intro head
        rw [listQSum_map]
        exact Q'.eqv_refl _
      refine Q'.eqv_trans _
        (listQSum
          (fun head => weight head *
            listQSum (fun tail => listQProduct weight tail)
              (finiteWordsOfLength alphabet length))
          alphabet) _ ?_ ?_
      · apply listQSum_congr
        intro head
        exact listQSum_mul_left (weight head)
          (fun tail => listQProduct weight tail)
          (finiteWordsOfLength alphabet length)
      refine Q'.eqv_trans _
        (listQSum weight alphabet *
          listQSum (fun tail => listQProduct weight tail)
            (finiteWordsOfLength alphabet length)) _
        (listQSum_mul_right_local weight _ alphabet) ?_
      refine Q'.eqv_trans _
        (listQSum weight alphabet *
          qpow (listQSum weight alphabet) length) _
        (Q'.mul_eqv_congr_left _ _ _
          (finiteWordsOfLength_weightedMass_eqv_qpow
            alphabet weight length)) ?_
      exact Q'.eqv_trans _
        (qpow (listQSum weight alphabet) length *
          listQSum weight alphabet) _
        (Q'.mul_comm_eqv _ _)
        (Q'.eqv_refl _)

/-! ## 2. Exact activity-excess weight of one word -/

def finePacketComponentChildWordExcessWeight
    (rate : Q') (word : List FinePacketComponentChildCode) : Q' :=
  listQProduct (finePacketComponentChildExcessWeight rate) word

theorem finePacketComponentChildWordExcessWeight_eqv
    (rate : Q') : ∀ word : List FinePacketComponentChildCode,
    finePacketComponentChildWordExcessWeight rate word ≈
      qpow rate
        (3 * listNatWeight
          (fun code : FinePacketComponentChildCode => code.activity - 1)
          word)
  | [] => Q'.eqv_refl 1
  | head :: tail => by
      change qpow rate (3 * (head.activity - 1)) *
          finePacketComponentChildWordExcessWeight rate tail ≈
        qpow rate
          (3 * ((head.activity - 1) +
            listNatWeight
              (fun code : FinePacketComponentChildCode => code.activity - 1)
              tail))
      refine Q'.eqv_trans _
        (qpow rate (3 * (head.activity - 1)) *
          qpow rate
            (3 * listNatWeight
              (fun code : FinePacketComponentChildCode => code.activity - 1)
              tail)) _
        (Q'.mul_eqv_congr_left _ _ _
          (finePacketComponentChildWordExcessWeight_eqv rate tail)) ?_
      refine Q'.eqv_trans _
        (qpow rate
          (3 * (head.activity - 1) +
            3 * listNatWeight
              (fun code : FinePacketComponentChildCode => code.activity - 1)
              tail)) _
        (Q'.eqv_symm (qpow_add rate _ _)) ?_
      have hexponent :
          3 * (head.activity - 1) +
              3 * listNatWeight
                (fun code : FinePacketComponentChildCode => code.activity - 1)
                tail =
            3 * ((head.activity - 1) +
              listNatWeight
                (fun code : FinePacketComponentChildCode => code.activity - 1)
                tail) := by
        omega
      rw [hexponent]
      exact Q'.eqv_refl _

/-! ## 3. Complete word carrier and its mass -/

def finePacketComponentChildWordExcessMass
    (rate : Q') (componentSize : Nat) : Q' :=
  listQSum (finePacketComponentChildWordExcessWeight rate)
    (finiteWordsOfLength finePacketComponentChildCodes componentSize)

theorem finePacketComponentChildWordExcessMass_eqv_power
    (rate : Q') (componentSize : Nat) :
    finePacketComponentChildWordExcessMass rate componentSize ≈
      qpow (finePacketComponentChildExcessMass rate) componentSize := by
  exact finiteWordsOfLength_weightedMass_eqv_qpow
    finePacketComponentChildCodes
    (finePacketComponentChildExcessWeight rate)
    componentSize

private theorem finePacketComponentChildExcessMass_nonnegative
    {rate : Q'} (hrate0 : (0 : Q') ≤ rate) :
    (0 : Q') ≤ finePacketComponentChildExcessMass rate := by
  unfold finePacketComponentChildExcessMass
  apply listQSum_nonnegative_on
  intro code _hcode
  unfold finePacketComponentChildExcessWeight
  exact qpow_nonneg rate hrate0 _

theorem finePacketComponentChildWordExcessMass_le_nine_power
    {rate : Q'} (hrate0 : (0 : Q') ≤ rate)
    (hrateAnchor : rate ≤ anchorCoupling) (componentSize : Nat) :
    finePacketComponentChildWordExcessMass rate componentSize ≤
      qpow (Q'.ofNat 9) componentSize := by
  have hrate1 : rate ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hrateAnchor (by decide)
  have hlocalLeCeiling :=
    finePacketComponentChildExcessMass_le_ceiling hrate0 hrate1
  have hlocalLeNine : finePacketComponentChildExcessMass rate ≤
      Q'.ofNat 9 :=
    Q'.le_trans' _ _ _ hlocalLeCeiling
      (Q'.le_of_lt
        (finePacketComponentChildExcessCeiling_lt_nine
          hrate0 hrateAnchor))
  have hpower := qpow_mono
    (finePacketComponentChildExcessMass_nonnegative hrate0)
    hlocalLeNine componentSize
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (finePacketComponentChildWordExcessMass_eqv_power
        rate componentSize)) hpower

/-! ## 4. The actual component word -/

theorem finePacketGlobalNonzeroConnectedEntryChildCode_mem_words
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryChildCode
        S orientation observableFaceId entry ∈
      finiteWordsOfLength finePacketComponentChildCodes
        (finePacketGlobalNonzeroConnectedEntryComponentSize
          S orientation observableFaceId entry) := by
  have hword := mem_finiteWordsOfLength_of_all_mem
    finePacketComponentChildCodes
    (finePacketGlobalNonzeroConnectedEntryChildCode
      S orientation observableFaceId entry)
    (fun code hcode =>
      finePacketGlobalNonzeroConnectedEntryChildCode_mem_catalogue
        S hfineCutoff orientation observableFaceId hobservableFace entry
          code hcode)
  simpa only [finePacketGlobalNonzeroConnectedEntryComponentSize,
    finePacketGlobalNonzeroConnectedEntryChildCode, List.length_map]
    using hword

theorem finePacketGlobalNonzeroConnectedEntryChildWordExcessWeight_eqv_heat
    (rate : Q') (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketComponentChildWordExcessWeight rate
        (finePacketGlobalNonzeroConnectedEntryChildCode
          S orientation observableFaceId entry) ≈
      qpow rate
        (finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
          S orientation observableFaceId entry) := by
  refine Q'.eqv_trans _
    (qpow rate
      (3 * listNatWeight
        (fun code : FinePacketComponentChildCode => code.activity - 1)
        (finePacketGlobalNonzeroConnectedEntryChildCode
          S orientation observableFaceId entry))) _
    (finePacketComponentChildWordExcessWeight_eqv rate _) ?_
  rw [finePacketGlobalNonzeroConnectedEntryChildCode_scaledExcess_eq_heat
    S hfineCutoff orientation observableFaceId hobservableFace entry]
  exact Q'.eqv_refl _

/-! ## 5. Axiom audit -/

#print axioms finePacketComponentChildWordExcessWeight
#print axioms finePacketComponentChildWordExcessWeight_eqv
#print axioms finePacketComponentChildWordExcessMass
#print axioms finePacketComponentChildWordExcessMass_eqv_power
#print axioms finePacketComponentChildWordExcessMass_le_nine_power
#print axioms finePacketGlobalNonzeroConnectedEntryChildCode_mem_words
#print axioms finePacketGlobalNonzeroConnectedEntryChildWordExcessWeight_eqv_heat

end YMGap.Continuum.Z4DyadicBinaryConnectedComponentChildWeightedWord
