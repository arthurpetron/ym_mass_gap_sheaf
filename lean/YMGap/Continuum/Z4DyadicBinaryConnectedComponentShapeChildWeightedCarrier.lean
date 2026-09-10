/-
# Combine rooted geometry with the fine-child weighted component word

The connected component has two finite pieces that must be paid together:
its rooted Z4 shape and its literal word of fine-child SU(2) local states.
This file forms their dependent product carrier and sums its complete weight.

For component size `S`, every shape receives the reserved factor `rate^(2S)`
and every child word receives its exact activity-excess product weight.  The
total carrier mass is bounded by

  `625^S * rate^(2S) * 9^S`

and this is exactly the single geometric power

  `(625 * rate^2 * 9)^S`.

At the named anchor the base is `9/256 < 1`.  The actual cross-scale entry
compiles into the carrier, and its carrier weight is exactly the product of
the shape/local entropy heat and local activity-excess heat factors in the
global decomposition.  Exterior labels and normalized recoupling congestion
remain outside this carrier and are not bounded here.

Constructive contract: finite Cartesian summation, structural rational-power
algebra, and the existing deterministic rooted-animal compiler only; no
classical choice, proof hole, trusted external computation, computability
escape, enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedComponentChildWeightedWord

namespace YMGap.Continuum.Z4DyadicBinaryConnectedComponentShapeChildWeightedCarrier

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentChildCode
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentChildWeightedEntropy
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentChildWeightedWord
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyBudget
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyCode
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem mul_four_regroup_local (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d)))
  refine Q'.mul_eqv_congr_left a _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv b c d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ d (Q'.mul_comm_eqv b c)) ?_
  exact Q'.mul_assoc_eqv c b d

private theorem qpow_mul_base_local (a b : Q') : ∀ exponent,
    qpow (a * b) exponent ≈ qpow a exponent * qpow b exponent
  | 0 => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | exponent + 1 => by
      change qpow (a * b) exponent * (a * b) ≈
        (qpow a exponent * a) * (qpow b exponent * b)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (a * b)
          (qpow_mul_base_local a b exponent)) ?_
      exact mul_four_regroup_local
        (qpow a exponent) (qpow b exponent) a b

private theorem qpow_ofNat_eqv_ofNat_pow (base : Nat) : ∀ exponent,
    qpow (Q'.ofNat base) exponent ≈ Q'.ofNat (base ^ exponent)
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      change qpow (Q'.ofNat base) exponent * Q'.ofNat base ≈
        Q'.ofNat (base ^ (exponent + 1))
      refine Q'.eqv_trans _
        (Q'.ofNat (base ^ exponent) * Q'.ofNat base) _
        (Q'.mul_eqv_congr_right _ _ _
          (qpow_ofNat_eqv_ofNat_pow base exponent)) ?_
      refine Q'.eqv_trans _
        (Q'.ofNat (base ^ exponent * base)) _
        (Q'.eqv_symm
          (HeatKernelRGStep.ofNat_mul_eqv (base ^ exponent) base)) ?_
      rw [Nat.pow_succ]
      exact Q'.eqv_refl _

private theorem listQSum_const_local {A : Type} (constant : Q') :
    ∀ items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _head :: tail => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat tail.length * constant) _
        (Q'.add_eqv_congr_left constant _ _
          (listQSum_const_local constant tail)) ?_
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv
          (Q'.ofNat tail.length * constant) constant)

/-! ## 1. Shape-child carrier -/

structure FinePacketConnectedComponentShapeChildCode : Type where
  shape : List (Fin (z4Chain.D + 1))
  childWord : List FinePacketComponentChildCode
deriving DecidableEq

def finePacketConnectedComponentShapeChildCarrier
    (componentSize : Nat) :
    List FinePacketConnectedComponentShapeChildCode :=
  (rootedAnimalPaddedTourCarrier z4Chain componentSize).flatMap fun shape =>
    (finiteWordsOfLength finePacketComponentChildCodes componentSize).map
      fun childWord => { shape := shape, childWord := childWord }

def finePacketConnectedComponentShapeChildWeight
    (rate : Q') (componentSize : Nat)
    (code : FinePacketConnectedComponentShapeChildCode) : Q' :=
  qpow rate (2 * componentSize) *
    finePacketComponentChildWordExcessWeight rate code.childWord

def finePacketConnectedComponentShapeChildMass
    (rate : Q') (componentSize : Nat) : Q' :=
  listQSum
    (finePacketConnectedComponentShapeChildWeight rate componentSize)
    (finePacketConnectedComponentShapeChildCarrier componentSize)

/-! ## 2. Exact full-carrier sum -/

theorem finePacketConnectedComponentShapeChildMass_eqv
    (rate : Q') (componentSize : Nat) :
    finePacketConnectedComponentShapeChildMass rate componentSize ≈
      Q'.ofNat (625 ^ componentSize) *
        (qpow rate (2 * componentSize) *
          finePacketComponentChildWordExcessMass rate componentSize) := by
  unfold finePacketConnectedComponentShapeChildMass
    finePacketConnectedComponentShapeChildCarrier
  refine Q'.eqv_trans _
    (listQSum
      (fun shape =>
        listQSum
          (finePacketConnectedComponentShapeChildWeight rate componentSize)
          ((finiteWordsOfLength finePacketComponentChildCodes componentSize).map
            fun childWord =>
              ({ shape := shape, childWord := childWord } :
                FinePacketConnectedComponentShapeChildCode)))
      (rootedAnimalPaddedTourCarrier z4Chain componentSize)) _
    (listQSum_flatMap _ _ _) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun _shape =>
        qpow rate (2 * componentSize) *
          finePacketComponentChildWordExcessMass rate componentSize)
      (rootedAnimalPaddedTourCarrier z4Chain componentSize)) _ ?_ ?_
  · apply listQSum_congr
    intro shape
    rw [listQSum_map]
    exact listQSum_mul_left (qpow rate (2 * componentSize))
      (finePacketComponentChildWordExcessWeight rate)
      (finiteWordsOfLength finePacketComponentChildCodes componentSize)
  refine Q'.eqv_trans _
    (Q'.ofNat
        (rootedAnimalPaddedTourCarrier z4Chain componentSize).length *
      (qpow rate (2 * componentSize) *
        finePacketComponentChildWordExcessMass rate componentSize)) _
    (listQSum_const_local _ _) ?_
  rw [z4RootedAnimalPaddedTourCarrier_length]
  exact Q'.eqv_refl _

/-! ## 3. Contract the full mass to one geometric base -/

private theorem shapeChildProductBound_eqv_ratioPower
    (rate : Q') (componentSize : Nat) :
    Q'.ofNat (625 ^ componentSize) *
        (qpow rate (2 * componentSize) *
          qpow (Q'.ofNat 9) componentSize) ≈
      qpow (finePacketComponentShapeChildWeightedEntropyRatio rate)
        componentSize := by
  refine Q'.eqv_symm ?_
  unfold finePacketComponentShapeChildWeightedEntropyRatio
  refine Q'.eqv_trans _
    (qpow (Q'.ofNat 625) componentSize *
      qpow (qpow rate 2 * Q'.ofNat 9) componentSize) _
    (qpow_mul_base_local _ _ componentSize) ?_
  refine Q'.eqv_trans _
    (qpow (Q'.ofNat 625) componentSize *
      (qpow (qpow rate 2) componentSize *
        qpow (Q'.ofNat 9) componentSize)) _
    (Q'.mul_eqv_congr_left _ _ _
      (qpow_mul_base_local _ _ componentSize)) ?_
  exact qmul_congr_local
    (qpow_ofNat_eqv_ofNat_pow 625 componentSize)
    (qmul_congr_local
      (HeatKernelRGStep.qpow_qpow rate 2 componentSize)
      (Q'.eqv_refl _))

theorem finePacketConnectedComponentShapeChildMass_le_ratioPower
    {rate : Q'} (hrate0 : (0 : Q') ≤ rate)
    (hrateAnchor : rate ≤ anchorCoupling) (componentSize : Nat) :
    finePacketConnectedComponentShapeChildMass rate componentSize ≤
      qpow (finePacketComponentShapeChildWeightedEntropyRatio rate)
        componentSize := by
  have hword := finePacketComponentChildWordExcessMass_le_nine_power
    hrate0 hrateAnchor componentSize
  have hratePower0 : (0 : Q') ≤ qpow rate (2 * componentSize) :=
    qpow_nonneg rate hrate0 _
  have hinner := Q'.mul_le_mul_of_nonneg_left _ _ _ hword hratePower0
  have hshape0 : (0 : Q') ≤ Q'.ofNat (625 ^ componentSize) :=
    zero_le_ofNat _
  have hproduct := Q'.mul_le_mul_of_nonneg_left _ _ _ hinner hshape0
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (finePacketConnectedComponentShapeChildMass_eqv rate componentSize))
    (Q'.le_trans' _ _ _ hproduct
      (Q'.le_of_eqv
        (shapeChildProductBound_eqv_ratioPower rate componentSize)))

/-- Every nonempty shape-child carrier has total paid mass strictly below
one on the explicitly named strong-coupling interval. -/
theorem finePacketConnectedComponentShapeChildMass_lt_one
    {rate : Q'} (hrate0 : (0 : Q') ≤ rate)
    (hrateAnchor : rate ≤ anchorCoupling)
    {componentSize : Nat} (hcomponentSize : 0 < componentSize) :
    finePacketConnectedComponentShapeChildMass rate componentSize <
      (1 : Q') := by
  let ratio := finePacketComponentShapeChildWeightedEntropyRatio rate
  have hratio0 : (0 : Q') ≤ ratio := by
    unfold ratio finePacketComponentShapeChildWeightedEntropyRatio
    exact Q'.mul_nonneg _ _ (zero_le_ofNat 625)
      (Q'.mul_nonneg _ _ (qpow_nonneg rate hrate0 2) (zero_le_ofNat 9))
  have hratioLt : ratio < (1 : Q') :=
    finePacketComponentShapeChildWeightedEntropyRatio_lt_one
      hrate0 hrateAnchor
  have hpowerLeFirst : qpow ratio componentSize ≤ qpow ratio 1 :=
    qpow_antitone hratio0 (Q'.le_of_lt hratioLt)
      1 componentSize hcomponentSize
  have hfirstLeRatio : qpow ratio 1 ≤ ratio :=
    Q'.le_of_eqv (Q'.one_mul_eqv ratio)
  have hpowerLt : qpow ratio componentSize < (1 : Q') :=
    lt_of_le_of_lt
      (Q'.le_trans' _ _ _ hpowerLeFirst hfirstLeRatio) hratioLt
  exact lt_of_le_of_lt
    (finePacketConnectedComponentShapeChildMass_le_ratioPower
      hrate0 hrateAnchor componentSize) hpowerLt

/-! ## 4. Compile the actual component -/

def finePacketGlobalNonzeroConnectedEntryShapeChildCode
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    FinePacketConnectedComponentShapeChildCode where
  shape := finePacketGlobalNonzeroConnectedEntryShapeCode
    S orientation observableFaceId hobservableFace entry
  childWord := finePacketGlobalNonzeroConnectedEntryChildCode
    S orientation observableFaceId entry

theorem finePacketGlobalNonzeroConnectedEntryShapeChildCode_mem
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace entry ∈
      finePacketConnectedComponentShapeChildCarrier
        (finePacketGlobalNonzeroConnectedEntryComponentSize
          S orientation observableFaceId entry) := by
  unfold finePacketConnectedComponentShapeChildCarrier
    finePacketGlobalNonzeroConnectedEntryShapeChildCode
  apply List.mem_flatMap.mpr
  refine ⟨finePacketGlobalNonzeroConnectedEntryShapeCode
      S orientation observableFaceId hobservableFace entry,
    finePacketGlobalNonzeroConnectedEntryShapeCode_mem
      S orientation observableFaceId hobservableFace entry, ?_⟩
  apply List.mem_map.mpr
  refine ⟨finePacketGlobalNonzeroConnectedEntryChildCode
      S orientation observableFaceId entry, ?_, rfl⟩
  exact finePacketGlobalNonzeroConnectedEntryChildCode_mem_words
    S hfineCutoff orientation observableFaceId hobservableFace entry

theorem finePacketGlobalNonzeroConnectedEntryShapeChildWeight_eqv_heat
    (rate : Q') (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketConnectedComponentShapeChildWeight rate
        (finePacketGlobalNonzeroConnectedEntryComponentSize
          S orientation observableFaceId entry)
        (finePacketGlobalNonzeroConnectedEntryShapeChildCode
          S orientation observableFaceId hobservableFace entry) ≈
      qpow rate
          (finePacketGlobalNonzeroConnectedEntryShapeLocalEntropyHeat
            S orientation observableFaceId entry) *
        qpow rate
          (finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
            S orientation observableFaceId entry) := by
  unfold finePacketConnectedComponentShapeChildWeight
    finePacketGlobalNonzeroConnectedEntryShapeChildCode
    finePacketGlobalNonzeroConnectedEntryShapeLocalEntropyHeat
  exact Q'.mul_eqv_congr_left _ _ _
    (finePacketGlobalNonzeroConnectedEntryChildWordExcessWeight_eqv_heat
      rate S hfineCutoff orientation observableFaceId hobservableFace entry)

/-! ## 5. Axiom audit -/

#print axioms FinePacketConnectedComponentShapeChildCode
#print axioms finePacketConnectedComponentShapeChildCarrier
#print axioms finePacketConnectedComponentShapeChildWeight
#print axioms finePacketConnectedComponentShapeChildMass
#print axioms finePacketConnectedComponentShapeChildMass_eqv
#print axioms finePacketConnectedComponentShapeChildMass_le_ratioPower
#print axioms finePacketConnectedComponentShapeChildMass_lt_one
#print axioms finePacketGlobalNonzeroConnectedEntryShapeChildCode
#print axioms finePacketGlobalNonzeroConnectedEntryShapeChildCode_mem
#print axioms finePacketGlobalNonzeroConnectedEntryShapeChildWeight_eqv_heat

end YMGap.Continuum.Z4DyadicBinaryConnectedComponentShapeChildWeightedCarrier
