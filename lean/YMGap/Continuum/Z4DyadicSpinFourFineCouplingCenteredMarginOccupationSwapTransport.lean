/-
# Exact occupation transport under a two-replica support swap

The cutoff-one antisymmetric centered-mass determinant has been reduced to a
signed function of the two occupied-face counts.  This module computes exactly
how those counts change under the literal facewise transposition already used
by the paired-support switch.

For an arbitrary Boolean face mask, the new left count is the old right count
inside the mask plus the old left count outside it; the new right count has the
opposite formula.  Hence total pair occupation is invariant.  More sharply,
if `M` is the signed left-minus-right occupation inside the mask, then

  newImbalance + 2*M = oldImbalance.

The final statements specialize these identities to the target-rooted
physical-support component.  Thus the common two-replica heat exponent is
preserved, while the antisymmetric occupation cofactor records one explicit
signed component imbalance.  No cancellation or estimate of that imbalance
is asserted here.

In particular this proves no cutoff- or volume-uniform covariance estimate,
continuum measure, OS/GNS reconstruction, Hamiltonian gap, or Yang--Mills mass
gap.

Constructive contract: structural list recursion, Boolean case analysis, and
Presburger arithmetic only; no `Classical`, choice, `native_decide`, proof
hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
import YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapTransport

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginBinaryHybrid
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionPartition

/-! ## 1. Masked cutoff-one occupation -/

/-- Number of spin-one faces which also satisfy a Boolean face mask. -/
def slabCutoffOneMaskedOccupiedCount
    (selected : Nat → Bool) (physical : EdgeLabelling) :
    List Nat → Nat
  | [] => 0
  | faceId :: rest =>
      (if selected faceId then
        if physical faceId = 1 then 1 else 0
      else 0) +
        slabCutoffOneMaskedOccupiedCount selected physical rest

/-- Selected and unselected occupations partition the complete occupation
count, with multiplicity inherited from the displayed face list. -/
theorem slabCutoffOneOccupiedCount_eq_masked_add_complement
    (selected : Nat → Bool) (physical : EdgeLabelling) :
    ∀ faces : List Nat,
      (slabCutoffOneOccupiedFaces physical faces).length =
        slabCutoffOneMaskedOccupiedCount selected physical faces +
          slabCutoffOneMaskedOccupiedCount
            (fun faceId => !(selected faceId)) physical faces
  | [] => rfl
  | faceId :: rest => by
      have ih :=
        slabCutoffOneOccupiedCount_eq_masked_add_complement
          selected physical rest
      cases hselected : selected faceId <;>
        by_cases hoccupied : physical faceId = 1 <;>
        simp [slabCutoffOneOccupiedFaces,
          slabCutoffOneMaskedOccupiedCount,
          hselected, hoccupied] at ih ⊢ <;>
        omega

/-! ## 2. Exact count transport under an arbitrary facewise swap -/

/-- The swapped left replica takes its selected occupation from the old right
replica and its complementary occupation from the old left replica. -/
theorem slabCutoffOneOccupiedCount_faceSwapLeft
    (selected : Nat → Bool) (left right : EdgeLabelling) :
    ∀ faces : List Nat,
      (slabCutoffOneOccupiedFaces
          (twoReplicaFaceSwapLeft selected left right) faces).length =
        slabCutoffOneMaskedOccupiedCount selected right faces +
          slabCutoffOneMaskedOccupiedCount
            (fun faceId => !(selected faceId)) left faces
  | [] => rfl
  | faceId :: rest => by
      have ih := slabCutoffOneOccupiedCount_faceSwapLeft
        selected left right rest
      cases hselected : selected faceId <;>
        by_cases hleft : left faceId = 1 <;>
        by_cases hright : right faceId = 1 <;>
        simp [slabCutoffOneOccupiedFaces,
          slabCutoffOneMaskedOccupiedCount,
          twoReplicaFaceSwapLeft,
          hselected, hleft, hright] at ih ⊢ <;>
        omega

/-- The swapped right replica takes its selected occupation from the old left
replica and its complementary occupation from the old right replica. -/
theorem slabCutoffOneOccupiedCount_faceSwapRight
    (selected : Nat → Bool) (left right : EdgeLabelling) :
    ∀ faces : List Nat,
      (slabCutoffOneOccupiedFaces
          (twoReplicaFaceSwapRight selected left right) faces).length =
        slabCutoffOneMaskedOccupiedCount selected left faces +
          slabCutoffOneMaskedOccupiedCount
            (fun faceId => !(selected faceId)) right faces
  | [] => rfl
  | faceId :: rest => by
      have ih := slabCutoffOneOccupiedCount_faceSwapRight
        selected left right rest
      cases hselected : selected faceId <;>
        by_cases hleft : left faceId = 1 <;>
        by_cases hright : right faceId = 1 <;>
        simp [slabCutoffOneOccupiedFaces,
          slabCutoffOneMaskedOccupiedCount,
          twoReplicaFaceSwapRight,
          hselected, hleft, hright] at ih ⊢ <;>
        omega

/-- A pointwise transposition preserves the total number of occupied faces in
the two replicas. -/
theorem slabCutoffOneOccupiedCount_pair_faceSwap
    (selected : Nat → Bool) (left right : EdgeLabelling)
    (faces : List Nat) :
    (slabCutoffOneOccupiedFaces
        (twoReplicaFaceSwapLeft selected left right) faces).length +
      (slabCutoffOneOccupiedFaces
        (twoReplicaFaceSwapRight selected left right) faces).length =
    (slabCutoffOneOccupiedFaces left faces).length +
      (slabCutoffOneOccupiedFaces right faces).length := by
  have hswapLeft := slabCutoffOneOccupiedCount_faceSwapLeft
    selected left right faces
  have hswapRight := slabCutoffOneOccupiedCount_faceSwapRight
    selected left right faces
  have hleft := slabCutoffOneOccupiedCount_eq_masked_add_complement
    selected left faces
  have hright := slabCutoffOneOccupiedCount_eq_masked_add_complement
    selected right faces
  omega

/-- Exact signed redistribution law.  Swapping the selected component reverses
its contribution to left-minus-right occupation, while leaving the
complementary contribution fixed. -/
theorem slabCutoffOneOccupiedImbalance_pair_faceSwap
    (selected : Nat → Bool) (left right : EdgeLabelling)
    (faces : List Nat) :
    ((slabCutoffOneOccupiedFaces
          (twoReplicaFaceSwapLeft selected left right) faces).length : Int) -
        (slabCutoffOneOccupiedFaces
          (twoReplicaFaceSwapRight selected left right) faces).length +
      2 *
        ((slabCutoffOneMaskedOccupiedCount selected left faces : Int) -
          slabCutoffOneMaskedOccupiedCount selected right faces) =
    (slabCutoffOneOccupiedFaces left faces).length -
      (slabCutoffOneOccupiedFaces right faces).length := by
  have hswapLeft := slabCutoffOneOccupiedCount_faceSwapLeft
    selected left right faces
  have hswapRight := slabCutoffOneOccupiedCount_faceSwapRight
    selected left right faces
  have hleft := slabCutoffOneOccupiedCount_eq_masked_add_complement
    selected left faces
  have hright := slabCutoffOneOccupiedCount_eq_masked_add_complement
    selected right faces
  omega

/-! ## 3. The target-rooted physical-support specialization -/

/-- The canonical mask selecting the target-rooted union-support component of
a fine physical source pair. -/
def fineCouplingPhysicalSupportSwapMask
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair) : Nat → Bool :=
  slabTwoReplicaSupportSwapMask
    S.fine.extent pair.1 pair.2 targetFaceId

/-- The literal physical source pair obtained by transposing the canonical
target-rooted union-support component. -/
def fineCouplingPhysicalSupportSwappedPair
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair) :
    FineCouplingPhysicalSourcePair :=
  (twoReplicaFaceSwapLeft
      (fineCouplingPhysicalSupportSwapMask S targetFaceId pair)
      pair.1 pair.2,
    twoReplicaFaceSwapRight
      (fineCouplingPhysicalSupportSwapMask S targetFaceId pair)
      pair.1 pair.2)

/-- Occupation of one source restricted to the canonical support component. -/
def fineCouplingPhysicalComponentOccupiedFaceCount
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair)
    (source : EdgeLabelling) : Nat :=
  slabCutoffOneMaskedOccupiedCount
    (fineCouplingPhysicalSupportSwapMask S targetFaceId pair)
    source (slabPhysicalFaceEdges S.fine.extent)

/-- The canonical component swap has the explicit left count formula. -/
theorem fineCouplingPhysicalSupportSwappedPair_left_count
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair) :
    fineCouplingPhysicalOccupiedFaceCount S
        (fineCouplingPhysicalSupportSwappedPair
          S targetFaceId pair).1 =
      fineCouplingPhysicalComponentOccupiedFaceCount
          S targetFaceId pair pair.2 +
        slabCutoffOneMaskedOccupiedCount
          (fun faceId =>
            !(fineCouplingPhysicalSupportSwapMask
              S targetFaceId pair faceId))
          pair.1 (slabPhysicalFaceEdges S.fine.extent) := by
  unfold fineCouplingPhysicalOccupiedFaceCount
    fineCouplingPhysicalSupportSwappedPair
    fineCouplingPhysicalComponentOccupiedFaceCount
  exact slabCutoffOneOccupiedCount_faceSwapLeft
    (fineCouplingPhysicalSupportSwapMask S targetFaceId pair)
    pair.1 pair.2 (slabPhysicalFaceEdges S.fine.extent)

/-- The canonical component swap has the explicit right count formula. -/
theorem fineCouplingPhysicalSupportSwappedPair_right_count
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair) :
    fineCouplingPhysicalOccupiedFaceCount S
        (fineCouplingPhysicalSupportSwappedPair
          S targetFaceId pair).2 =
      fineCouplingPhysicalComponentOccupiedFaceCount
          S targetFaceId pair pair.1 +
        slabCutoffOneMaskedOccupiedCount
          (fun faceId =>
            !(fineCouplingPhysicalSupportSwapMask
              S targetFaceId pair faceId))
          pair.2 (slabPhysicalFaceEdges S.fine.extent) := by
  unfold fineCouplingPhysicalOccupiedFaceCount
    fineCouplingPhysicalSupportSwappedPair
    fineCouplingPhysicalComponentOccupiedFaceCount
  exact slabCutoffOneOccupiedCount_faceSwapRight
    (fineCouplingPhysicalSupportSwapMask S targetFaceId pair)
    pair.1 pair.2 (slabPhysicalFaceEdges S.fine.extent)

/-- The target-rooted support switch preserves total two-replica occupation. -/
theorem fineCouplingPhysicalSupportSwappedPair_total_count
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair) :
    fineCouplingPhysicalOccupiedFaceCount S
          (fineCouplingPhysicalSupportSwappedPair
            S targetFaceId pair).1 +
        fineCouplingPhysicalOccupiedFaceCount S
          (fineCouplingPhysicalSupportSwappedPair
            S targetFaceId pair).2 =
      fineCouplingPhysicalOccupiedFaceCount S pair.1 +
        fineCouplingPhysicalOccupiedFaceCount S pair.2 := by
  unfold fineCouplingPhysicalOccupiedFaceCount
    fineCouplingPhysicalSupportSwappedPair
  exact slabCutoffOneOccupiedCount_pair_faceSwap
    (fineCouplingPhysicalSupportSwapMask S targetFaceId pair)
    pair.1 pair.2 (slabPhysicalFaceEdges S.fine.extent)

/-- The canonical support swap changes total heat exponent zero: at cutoff one
the shared pair exponent `3*(n_left+n_right)` is literally preserved. -/
theorem fineCouplingPhysicalSupportSwappedPair_total_heatExponent
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair) :
    3 * fineCouplingPhysicalOccupiedFaceCount S
          (fineCouplingPhysicalSupportSwappedPair
            S targetFaceId pair).1 +
        3 * fineCouplingPhysicalOccupiedFaceCount S
          (fineCouplingPhysicalSupportSwappedPair
            S targetFaceId pair).2 =
      3 * fineCouplingPhysicalOccupiedFaceCount S pair.1 +
        3 * fineCouplingPhysicalOccupiedFaceCount S pair.2 := by
  have htotal := fineCouplingPhysicalSupportSwappedPair_total_count
    S targetFaceId pair
  omega

/-- The signed occupation imbalance after the canonical component swap differs
from the old imbalance by exactly twice the component's old imbalance. -/
theorem fineCouplingPhysicalSupportSwappedPair_imbalance
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair) :
    (fineCouplingPhysicalOccupiedFaceCount S
          (fineCouplingPhysicalSupportSwappedPair
            S targetFaceId pair).1 : Int) -
        fineCouplingPhysicalOccupiedFaceCount S
          (fineCouplingPhysicalSupportSwappedPair
            S targetFaceId pair).2 +
      2 *
        ((fineCouplingPhysicalComponentOccupiedFaceCount
              S targetFaceId pair pair.1 : Int) -
          fineCouplingPhysicalComponentOccupiedFaceCount
              S targetFaceId pair pair.2) =
    fineCouplingPhysicalOccupiedFaceCount S pair.1 -
      fineCouplingPhysicalOccupiedFaceCount S pair.2 := by
  unfold fineCouplingPhysicalOccupiedFaceCount
    fineCouplingPhysicalSupportSwappedPair
    fineCouplingPhysicalComponentOccupiedFaceCount
  exact slabCutoffOneOccupiedImbalance_pair_faceSwap
    (fineCouplingPhysicalSupportSwapMask S targetFaceId pair)
    pair.1 pair.2 (slabPhysicalFaceEdges S.fine.extent)

#print axioms slabCutoffOneMaskedOccupiedCount
#print axioms slabCutoffOneOccupiedCount_eq_masked_add_complement
#print axioms slabCutoffOneOccupiedCount_faceSwapLeft
#print axioms slabCutoffOneOccupiedCount_faceSwapRight
#print axioms slabCutoffOneOccupiedCount_pair_faceSwap
#print axioms slabCutoffOneOccupiedImbalance_pair_faceSwap
#print axioms fineCouplingPhysicalSupportSwapMask
#print axioms fineCouplingPhysicalSupportSwappedPair
#print axioms fineCouplingPhysicalComponentOccupiedFaceCount
#print axioms fineCouplingPhysicalSupportSwappedPair_left_count
#print axioms fineCouplingPhysicalSupportSwappedPair_right_count
#print axioms fineCouplingPhysicalSupportSwappedPair_total_count
#print axioms fineCouplingPhysicalSupportSwappedPair_total_heatExponent
#print axioms fineCouplingPhysicalSupportSwappedPair_imbalance

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapTransport
