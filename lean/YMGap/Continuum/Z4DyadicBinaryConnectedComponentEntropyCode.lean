/-
# A finite entropy code for each cross-scale connected component

The rebalanced heat budget reserves two powers of the strong-coupling rate
for every face of the observable-rooted target-support component.  This file
constructs the exact finite object those powers pay for.

For component size `S`, an actual nonzero connected entry is sent to

* one padded rooted Z4 animal word in a carrier of size `625^S`; and
* its ordered word of cutoff-four local source/target codes in a carrier of
  size `72^S`.

The product carrier therefore has exact length `45000^S`.  Combined with the
preceding module, its one-site entropy ratio is `9/32` at rate `1/400`.

This code intentionally reconstructs only the component support and the four
local labels on its literal ordered face list.  Fine child positions,
off-component labels, and recoupling multiplicities remain in the separately
named complementary reserve/congestion frontier; no injectivity for the full
global connected carrier is claimed here.

Constructive contract: deterministic spanning-tree tours, structural finite
word enumeration, and existing local membership proofs only; no classical
choice, proof hole, trusted external computation, noncomputable declaration,
enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyBudget
import YMGap.Continuum.FiniteRootedAnimalTourCode

namespace YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyCode

set_option autoImplicit false

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyBudget
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentHeatBudget
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentLocalCode
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedGeometry
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedMassFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Exact words over an arbitrary finite alphabet -/

/-- All words of one exact length over a literal finite alphabet. -/
def finiteWordsOfLength {A : Type} (alphabet : List A) :
    Nat → List (List A)
  | 0 => [[]]
  | length + 1 =>
      alphabet.flatMap fun head =>
        (finiteWordsOfLength alphabet length).map fun tail => head :: tail

private theorem flatMap_const_length
    {A B : Type} (items : List A) (block : A → List B) (length : Nat)
    (hlength : ∀ item, item ∈ items → (block item).length = length) :
    (items.flatMap block).length = items.length * length := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [hlength head List.mem_cons_self,
        ih (fun item hitem =>
          hlength item (List.mem_cons_of_mem head hitem))]
      rw [Nat.succ_mul]
      omega

theorem finiteWordsOfLength_length {A : Type} (alphabet : List A) :
    ∀ length,
      (finiteWordsOfLength alphabet length).length = alphabet.length ^ length
  | 0 => rfl
  | length + 1 => by
      unfold finiteWordsOfLength
      rw [flatMap_const_length alphabet
        (fun head =>
          (finiteWordsOfLength alphabet length).map fun tail => head :: tail)
        (alphabet.length ^ length)]
      · rw [Nat.pow_succ, Nat.mul_comm]
      · intro _ _
        rw [List.length_map, finiteWordsOfLength_length alphabet length]

theorem mem_finiteWordsOfLength_of_all_mem
    {A : Type} (alphabet : List A) :
    ∀ word : List A,
      (∀ item, item ∈ word → item ∈ alphabet) →
        word ∈ finiteWordsOfLength alphabet word.length
  | [], _ => List.mem_singleton.mpr rfl
  | head :: tail, hall => by
      unfold finiteWordsOfLength
      apply List.mem_flatMap.mpr
      refine ⟨head, hall head List.mem_cons_self, ?_⟩
      apply List.mem_map.mpr
      refine ⟨tail, mem_finiteWordsOfLength_of_all_mem alphabet tail ?_, rfl⟩
      intro item hitem
      exact hall item (List.mem_cons_of_mem head hitem)

/-! ## 2. The actual target component as rooted animal data -/

/-- Package the projected target-support component of one actual cross-scale
entry as the rooted animal consumed by the deterministic tour compiler. -/
def finePacketGlobalNonzeroConnectedEntryTargetRootedAnimal
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : RootedConnectedAnimal z4Chain where
  root := slabPlaquetteAt S.coarse.extent observableFaceId
  support := finePacketObservableTargetSupportPlaquettes
    S entry.1.targets observableFaceId
  root_mem :=
    slabPlaquetteAt_mem_finePacketObservableTargetSupportPlaquettes
      S entry.1.targets observableFaceId observableFaceId
      (finePacketGlobalConnectedEntry_observable_mem_targetComponent
        S observableFaceId hobservableFace entry.1)
  support_nodup :=
    finePacketObservableTargetSupportPlaquettes_nodup
      S entry.1.targets observableFaceId
  connected :=
    finePacketObservableTargetSupportPlaquettes_connected
      S entry.1.targets observableFaceId hobservableFace
      (finePacketGlobalConnectedEntryPath
        S observableFaceId hobservableFace entry.1).observable_targetStates_ne

/-- The component-size-padded deterministic shape word. -/
def finePacketGlobalNonzeroConnectedEntryShapeCode
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : List (Fin (z4Chain.D + 1)) :=
  rootedAnimalPaddedTourCode
    (finePacketGlobalNonzeroConnectedEntryTargetRootedAnimal
      S orientation observableFaceId hobservableFace entry)
    (finePacketGlobalNonzeroConnectedEntryComponentSize
      S orientation observableFaceId entry)

theorem finePacketGlobalNonzeroConnectedEntryShapeCode_mem
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryShapeCode
        S orientation observableFaceId hobservableFace entry ∈
      rootedAnimalPaddedTourCarrier z4Chain
        (finePacketGlobalNonzeroConnectedEntryComponentSize
          S orientation observableFaceId entry) := by
  apply rootedAnimalPaddedTourCode_mem_carrier
  exact finePacketObservableTargetSupportPlaquettes_length_le_component
    S entry.1.targets observableFaceId

/-! ## 3. Product carrier and production membership -/

structure FinePacketConnectedComponentEntropyCode : Type where
  shape : List (Fin (z4Chain.D + 1))
  localCode : List FinePacketComponentLocalCode
deriving DecidableEq

def finePacketConnectedComponentEntropyCarrier
    (componentSize : Nat) :
    List FinePacketConnectedComponentEntropyCode :=
  (rootedAnimalPaddedTourCarrier z4Chain componentSize).flatMap fun shape =>
    (finiteWordsOfLength finePacketComponentLocalCodes componentSize).map
      fun localCode => { shape := shape, localCode := localCode }

theorem finePacketConnectedComponentEntropyCarrier_length
    (componentSize : Nat) :
    (finePacketConnectedComponentEntropyCarrier componentSize).length =
      finePacketComponentShapeLocalEntropyBase ^ componentSize := by
  unfold finePacketConnectedComponentEntropyCarrier
  rw [flatMap_const_length
    (rootedAnimalPaddedTourCarrier z4Chain componentSize)
    (fun shape =>
      (finiteWordsOfLength finePacketComponentLocalCodes componentSize).map
        fun localCode =>
          ({ shape := shape, localCode := localCode } :
            FinePacketConnectedComponentEntropyCode))
    (72 ^ componentSize)]
  · rw [z4RootedAnimalPaddedTourCarrier_length,
      ← Nat.mul_pow]
    unfold finePacketComponentShapeLocalEntropyBase
    rfl
  · intro _ _
    rw [List.length_map,
      finiteWordsOfLength_length,
      finePacketComponentLocalCodes_length]

/-- The literal product code of an actual connected entry. -/
def finePacketGlobalNonzeroConnectedEntryEntropyCode
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    FinePacketConnectedComponentEntropyCode where
  shape := finePacketGlobalNonzeroConnectedEntryShapeCode
    S orientation observableFaceId hobservableFace entry
  localCode := finePacketGlobalNonzeroConnectedEntryLocalCode
    S orientation observableFaceId entry

theorem finePacketGlobalNonzeroConnectedEntryEntropyCode_mem
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryEntropyCode
        S orientation observableFaceId hobservableFace entry ∈
      finePacketConnectedComponentEntropyCarrier
        (finePacketGlobalNonzeroConnectedEntryComponentSize
          S orientation observableFaceId entry) := by
  unfold finePacketConnectedComponentEntropyCarrier
    finePacketGlobalNonzeroConnectedEntryEntropyCode
  apply List.mem_flatMap.mpr
  refine ⟨finePacketGlobalNonzeroConnectedEntryShapeCode
      S orientation observableFaceId hobservableFace entry,
    finePacketGlobalNonzeroConnectedEntryShapeCode_mem
      S orientation observableFaceId hobservableFace entry, ?_⟩
  apply List.mem_map.mpr
  refine ⟨finePacketGlobalNonzeroConnectedEntryLocalCode
      S orientation observableFaceId entry, ?_, rfl⟩
  have hword := mem_finiteWordsOfLength_of_all_mem
    finePacketComponentLocalCodes
    (finePacketGlobalNonzeroConnectedEntryLocalCode
      S orientation observableFaceId entry)
    (fun code hcode =>
      finePacketGlobalNonzeroConnectedEntryLocalCode_mem_catalogue
        S hfineCutoff orientation observableFaceId hobservableFace entry
          code hcode)
  simpa only [finePacketGlobalNonzeroConnectedEntryComponentSize,
    finePacketGlobalNonzeroConnectedEntryLocalCode, List.length_map]
    using hword

/-! ## 4. What equality of component codes reconstructs -/

/-- Equal aggregate codes force equal projected target-support sets.  This is
the precise geometric reconstruction supplied at this frontier. -/
theorem finePacketGlobalNonzeroConnectedEntryEntropyCode_eq_sameTargetSupport
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (left right : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId)
    (hcode : finePacketGlobalNonzeroConnectedEntryEntropyCode
        S orientation observableFaceId hobservableFace left =
      finePacketGlobalNonzeroConnectedEntryEntropyCode
        S orientation observableFaceId hobservableFace right) :
    sameSupport (L := z4Chain.toLattice)
      (finePacketObservableTargetSupportPlaquettes
        S left.1.targets observableFaceId)
      (finePacketObservableTargetSupportPlaquettes
        S right.1.targets observableFaceId) := by
  have hshape := congrArg FinePacketConnectedComponentEntropyCode.shape hcode
  have hlocal := congrArg
    FinePacketConnectedComponentEntropyCode.localCode hcode
  have hsize :
      finePacketGlobalNonzeroConnectedEntryComponentSize
          S orientation observableFaceId left =
        finePacketGlobalNonzeroConnectedEntryComponentSize
          S orientation observableFaceId right := by
    have hlength := congrArg List.length hlocal
    simpa only [finePacketGlobalNonzeroConnectedEntryEntropyCode,
      finePacketGlobalNonzeroConnectedEntryLocalCode,
      finePacketGlobalNonzeroConnectedEntryComponentSize,
      List.length_map] using hlength
  change rootedAnimalPaddedTourCode
      (finePacketGlobalNonzeroConnectedEntryTargetRootedAnimal
        S orientation observableFaceId hobservableFace left)
      (finePacketGlobalNonzeroConnectedEntryComponentSize
        S orientation observableFaceId left) =
    rootedAnimalPaddedTourCode
      (finePacketGlobalNonzeroConnectedEntryTargetRootedAnimal
        S orientation observableFaceId hobservableFace right)
      (finePacketGlobalNonzeroConnectedEntryComponentSize
        S orientation observableFaceId right) at hshape
  rw [← hsize] at hshape
  exact rootedAnimalPaddedTourCode_eq_sameSupport
    (finePacketGlobalNonzeroConnectedEntryTargetRootedAnimal
      S orientation observableFaceId hobservableFace left)
    (finePacketGlobalNonzeroConnectedEntryTargetRootedAnimal
      S orientation observableFaceId hobservableFace right)
    (finePacketGlobalNonzeroConnectedEntryComponentSize
      S orientation observableFaceId left)
    rfl hshape

/-! ## 5. Axiom audit -/

#print axioms finiteWordsOfLength
#print axioms finiteWordsOfLength_length
#print axioms mem_finiteWordsOfLength_of_all_mem
#print axioms finePacketGlobalNonzeroConnectedEntryTargetRootedAnimal
#print axioms finePacketGlobalNonzeroConnectedEntryShapeCode
#print axioms finePacketGlobalNonzeroConnectedEntryShapeCode_mem
#print axioms FinePacketConnectedComponentEntropyCode
#print axioms finePacketConnectedComponentEntropyCarrier
#print axioms finePacketConnectedComponentEntropyCarrier_length
#print axioms finePacketGlobalNonzeroConnectedEntryEntropyCode
#print axioms finePacketGlobalNonzeroConnectedEntryEntropyCode_mem
#print axioms finePacketGlobalNonzeroConnectedEntryEntropyCode_eq_sameTargetSupport

end YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyCode
