/-
# Common-background invariance under the disconnected component swap

The disconnected component involution fixes every source-local tilt and
reverses the observable sign.  To turn that local antisymmetry into exact
cancellation, the remaining common exterior Gibbs background must be
preserved as a two-replica product.

This file proves that preservation in two stages.  First, the agreement-face
multiplicity is a commutative finite product and is invariant under arbitrary
facewise transposition.  Second, the canonical support component has one
Boolean choice at every actual slab link.  Hence each complete incident SU(2)
spin list is taken wholly from one original replica, so the two explicit link
multiplicities are transposed rather than changed.  The link identity folds
over the boundary-complete slab, combines with the already proved heat-face
factor identity, and yields invariance of the paired physical terms and of the
full common exterior Gibbs background.

The complete pair-term sign reversal and finite-sum cancellation are left to
the next module.  No activity estimate, uniform response bound, completed
spectral gap, continuum construction, or mass gap is asserted here.

Constructive contract: structural finite products, literal incident-spin
lists, and exact rational equivalence only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, trusted external
computation, enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsDisconnectedComponentSwap
import YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsComponentSwapBackground

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsDisconnectedComponentSwap
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveComponentEndpoints
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseActiveCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseDeterminant
open YMGap.Continuum.Z4DyadicSpinFourLoweringKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

private theorem natListProduct_pair_eq_of_pointwise
    {A : Type} (swappedLeft swappedRight left right : A → Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items →
        swappedLeft item * swappedRight item =
          left item * right item) →
      natListProduct swappedLeft items *
          natListProduct swappedRight items =
        natListProduct left items * natListProduct right items
  | [], _ => rfl
  | head :: tail, hpoint => by
      have hhead := hpoint head List.mem_cons_self
      have htail := natListProduct_pair_eq_of_pointwise
        swappedLeft swappedRight left right tail
        (fun item hmem => hpoint item (List.mem_cons_of_mem head hmem))
      simp only [natListProduct]
      calc
        (swappedLeft head * natListProduct swappedLeft tail) *
            (swappedRight head * natListProduct swappedRight tail) =
          (swappedLeft head * swappedRight head) *
            (natListProduct swappedLeft tail *
              natListProduct swappedRight tail) := by ac_rfl
        _ = (left head * right head) *
            (natListProduct left tail * natListProduct right tail) := by
          rw [hhead, htail]
        _ = (left head * natListProduct left tail) *
            (right head * natListProduct right tail) := by ac_rfl

private theorem qmul_congr_local
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' := by
  exact Q'.eqv_trans _ (a' * b) _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem ofNat_pairProduct_eqv_local
    (swappedLeft swappedRight left right : Nat)
    (hproduct : swappedLeft * swappedRight = left * right) :
    Q'.ofNat swappedLeft * Q'.ofNat swappedRight ≈
      Q'.ofNat left * Q'.ofNat right := by
  exact Q'.eqv_trans _ (Q'.ofNat (swappedLeft * swappedRight)) _
    (Q'.eqv_symm (ofNat_mul_eqv swappedLeft swappedRight))
    (Q'.eqv_trans _ (Q'.ofNat (left * right)) _
      (Q'.eqv_of_eq (congrArg Q'.ofNat hproduct))
      (ofNat_mul_eqv left right))

private def positiveEitherOfNatNe
    (left right : Nat) (hne : left ≠ right) :
    0 < left ∨ 0 < right := by
  cases left with
  | zero =>
      cases right with
      | zero => exact False.elim (hne rfl)
      | succ value => exact Or.inr (Nat.zero_lt_succ value)
  | succ value => exact Or.inl (Nat.zero_lt_succ value)

/-! ## 1. Agreement-face multiplicity product -/

/-- The two agreement-carrier multiplicity products are invariant under the
canonical facewise transposition.  This part uses only commutativity of
natural-number multiplication. -/
theorem finePacketCommonExteriorMultiplicityProduct_pair_componentSwap
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) :
    finePacketCommonExteriorMultiplicityProduct S first second
          (finePacketObservableComponentSwapLeft
            S observableFaceId targetPair) *
        finePacketCommonExteriorMultiplicityProduct S first second
          (finePacketObservableComponentSwapRight
            S observableFaceId targetPair) =
      finePacketCommonExteriorMultiplicityProduct S first second targetPair.1 *
        finePacketCommonExteriorMultiplicityProduct S first second
          targetPair.2 := by
  unfold finePacketCommonExteriorMultiplicityProduct
    spinFourLoweringMultiplicityProductOn
  apply natListProduct_pair_eq_of_pointwise
  intro faceId _hface
  cases hmask : finePacketObservableComponentSwapMask
      S observableFaceId targetPair faceId with
  | false =>
      simp [finePacketObservableComponentSwapLeft,
        finePacketObservableComponentSwapRight,
        twoReplicaFaceSwapLeft, twoReplicaFaceSwapRight, hmask]
  | true =>
      simp [finePacketObservableComponentSwapLeft,
        finePacketObservableComponentSwapRight,
        twoReplicaFaceSwapLeft, twoReplicaFaceSwapRight,
        hmask, Nat.mul_comm]

/-! ## 2. One complete SU(2) link multiplicity -/

private theorem slabExplicitLinkMultiplicity_eq_of_eq_on_incident
    {K extent : Nat} {left right : SlabLabelling} {link : SlabLink}
    (heq : ∀ faceId, faceId ∈ slabIncidentPlaqIds extent link →
      left faceId = right faceId) :
    slabExplicitLinkMultiplicity K extent left link =
      slabExplicitLinkMultiplicity K extent right link := by
  have hspins :
      (slabIncidentPlaqIds extent link).map left =
        (slabIncidentPlaqIds extent link).map right := by
    apply List.map_congr_left
    intro faceId hface
    exact heq faceId hface
  unfold slabExplicitLinkMultiplicity
  rw [hspins]

/-- At one actual slab link, the first support-swapped replica has exactly
the original link multiplicity selected by the canonical link bit. -/
theorem slabExplicitLinkMultiplicity_supportSwapLeft
    {K extent targetFaceId : Nat} {left right : SlabLabelling}
    {link : SlabLink}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges extent)
    (htargetSupport : 0 < left targetFaceId ∨ 0 < right targetFaceId)
    (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    slabExplicitLinkMultiplicity K extent
        (twoReplicaFaceSwapLeft
          (slabTwoReplicaSupportSwapMask
            extent left right targetFaceId) left right) link =
      if slabTwoReplicaSupportLinkSwapB
          extent left right targetFaceId link then
        slabExplicitLinkMultiplicity K extent right link
      else slabExplicitLinkMultiplicity K extent left link := by
  cases hbit : slabTwoReplicaSupportLinkSwapB
      extent left right targetFaceId link with
  | false =>
      rw [if_neg Bool.false_ne_true]
      apply slabExplicitLinkMultiplicity_eq_of_eq_on_incident
      intro faceId hface
      have hat := twoReplicaSupportSwapLeft_at_incident
        htarget htargetSupport hlink hface
      rw [hbit] at hat
      exact hat
  | true =>
      rw [if_pos rfl]
      apply slabExplicitLinkMultiplicity_eq_of_eq_on_incident
      intro faceId hface
      have hat := twoReplicaSupportSwapLeft_at_incident
        htarget htargetSupport hlink hface
      rw [hbit] at hat
      exact hat

/-- The complementary support-swapped replica takes the other original link
multiplicity. -/
theorem slabExplicitLinkMultiplicity_supportSwapRight
    {K extent targetFaceId : Nat} {left right : SlabLabelling}
    {link : SlabLink}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges extent)
    (htargetSupport : 0 < left targetFaceId ∨ 0 < right targetFaceId)
    (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    slabExplicitLinkMultiplicity K extent
        (twoReplicaFaceSwapRight
          (slabTwoReplicaSupportSwapMask
            extent left right targetFaceId) left right) link =
      if slabTwoReplicaSupportLinkSwapB
          extent left right targetFaceId link then
        slabExplicitLinkMultiplicity K extent left link
      else slabExplicitLinkMultiplicity K extent right link := by
  cases hbit : slabTwoReplicaSupportLinkSwapB
      extent left right targetFaceId link with
  | false =>
      rw [if_neg Bool.false_ne_true]
      apply slabExplicitLinkMultiplicity_eq_of_eq_on_incident
      intro faceId hface
      have hat := twoReplicaSupportSwapRight_at_incident
        htarget htargetSupport hlink hface
      rw [hbit] at hat
      exact hat
  | true =>
      rw [if_pos rfl]
      apply slabExplicitLinkMultiplicity_eq_of_eq_on_incident
      intro faceId hface
      have hat := twoReplicaSupportSwapRight_at_incident
        htarget htargetSupport hlink hface
      rw [hbit] at hat
      exact hat

/-- Thus the product of the two explicit multiplicities at one actual link
is unchanged.  This is the load-bearing whole-link non-abelian step. -/
theorem slabExplicitLinkMultiplicity_pair_supportSwap
    {K extent targetFaceId : Nat} {left right : SlabLabelling}
    {link : SlabLink}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges extent)
    (htargetSupport : 0 < left targetFaceId ∨ 0 < right targetFaceId)
    (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    slabExplicitLinkMultiplicity K extent
          (twoReplicaFaceSwapLeft
            (slabTwoReplicaSupportSwapMask
              extent left right targetFaceId) left right) link *
        slabExplicitLinkMultiplicity K extent
          (twoReplicaFaceSwapRight
            (slabTwoReplicaSupportSwapMask
              extent left right targetFaceId) left right) link =
      slabExplicitLinkMultiplicity K extent left link *
        slabExplicitLinkMultiplicity K extent right link := by
  rw [slabExplicitLinkMultiplicity_supportSwapLeft
      htarget htargetSupport hlink,
    slabExplicitLinkMultiplicity_supportSwapRight
      htarget htargetSupport hlink]
  cases hbit : slabTwoReplicaSupportLinkSwapB
      extent left right targetFaceId link <;>
    simp [Nat.mul_comm]

/-! ## 3. The full explicit-link product -/

/-- The pointwise whole-link transposition folds to the product over every
boundary-complete slab link. -/
theorem slabExplicitLinkMultiplicityProduct_pair_supportSwap
    {K extent targetFaceId : Nat} {left right : SlabLabelling}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges extent)
    (htargetSupport : 0 < left targetFaceId ∨ 0 < right targetFaceId) :
    slabExplicitLinkMultiplicityProduct K extent
          (twoReplicaFaceSwapLeft
            (slabTwoReplicaSupportSwapMask
              extent left right targetFaceId) left right) *
        slabExplicitLinkMultiplicityProduct K extent
          (twoReplicaFaceSwapRight
            (slabTwoReplicaSupportSwapMask
              extent left right targetFaceId) left right) =
      slabExplicitLinkMultiplicityProduct K extent left *
        slabExplicitLinkMultiplicityProduct K extent right := by
  unfold slabExplicitLinkMultiplicityProduct
  apply natListProduct_pair_eq_of_pointwise
  intro link hlink
  exact slabExplicitLinkMultiplicity_pair_supportSwap
    htarget htargetSupport hlink

/-! ## 4. Paired physical term -/

/-- Combining the arbitrary face-factor transposition with the canonical
whole-link multiplicity transposition preserves the product of the two full
corrected-slab SU(2) summands. -/
theorem slabParametricKPhysicalTerm_pair_supportSwap
    (coupling : Q') {K extent targetFaceId : Nat}
    {left right : SlabLabelling}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges extent)
    (htargetSupport : 0 < left targetFaceId ∨ 0 < right targetFaceId) :
    slabParametricKPhysicalTerm coupling K extent
          (twoReplicaFaceSwapLeft
            (slabTwoReplicaSupportSwapMask
              extent left right targetFaceId) left right) *
        slabParametricKPhysicalTerm coupling K extent
          (twoReplicaFaceSwapRight
            (slabTwoReplicaSupportSwapMask
              extent left right targetFaceId) left right) ≈
      slabParametricKPhysicalTerm coupling K extent left *
        slabParametricKPhysicalTerm coupling K extent right := by
  let selected := slabTwoReplicaSupportSwapMask
    extent left right targetFaceId
  let swappedLeft := twoReplicaFaceSwapLeft selected left right
  let swappedRight := twoReplicaFaceSwapRight selected left right
  let faceSwappedLeft := slabParametricKPhysicalFaceFactor
    coupling K extent swappedLeft
  let faceSwappedRight := slabParametricKPhysicalFaceFactor
    coupling K extent swappedRight
  let faceLeft := slabParametricKPhysicalFaceFactor
    coupling K extent left
  let faceRight := slabParametricKPhysicalFaceFactor
    coupling K extent right
  let linkSwappedLeft := slabExplicitLinkMultiplicityProduct
    K extent swappedLeft
  let linkSwappedRight := slabExplicitLinkMultiplicityProduct
    K extent swappedRight
  let linkLeft := slabExplicitLinkMultiplicityProduct K extent left
  let linkRight := slabExplicitLinkMultiplicityProduct K extent right
  have hface : faceSwappedLeft * faceSwappedRight ≈
      faceLeft * faceRight := by
    exact slabParametricKPhysicalFaceFactor_pair_faceSwap
      coupling K extent selected left right
  have hlinkNat : linkSwappedLeft * linkSwappedRight =
      linkLeft * linkRight := by
    exact slabExplicitLinkMultiplicityProduct_pair_supportSwap
      htarget htargetSupport
  have hlink : Q'.ofNat linkSwappedLeft * Q'.ofNat linkSwappedRight ≈
      Q'.ofNat linkLeft * Q'.ofNat linkRight :=
    ofNat_pairProduct_eqv_local _ _ _ _ hlinkNat
  change (faceSwappedLeft * Q'.ofNat linkSwappedLeft) *
      (faceSwappedRight * Q'.ofNat linkSwappedRight) ≈
    (faceLeft * Q'.ofNat linkLeft) *
      (faceRight * Q'.ofNat linkRight)
  refine Q'.eqv_trans _
    ((faceSwappedLeft * faceSwappedRight) *
      (Q'.ofNat linkSwappedLeft * Q'.ofNat linkSwappedRight)) _ ?_ ?_
  · ring_qeqv
  refine Q'.eqv_trans _
    ((faceLeft * faceRight) *
      (Q'.ofNat linkLeft * Q'.ofNat linkRight)) _ ?_ ?_
  · exact qmul_congr_local hface hlink
  · ring_qeqv

/-- Specialization of the full physical-term identity to the canonical
coarse target-pair component swap. -/
theorem coarsePhysicalTerm_pair_componentSwap
    (S : SlabScalePair) (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hobservableSupport : 0 < targetPair.1 observableFaceId ∨
      0 < targetPair.2 observableFaceId) :
    S.coarse.physicalTerm
          (finePacketObservableComponentSwapLeft
            S observableFaceId targetPair) *
        S.coarse.physicalTerm
          (finePacketObservableComponentSwapRight
            S observableFaceId targetPair) ≈
      S.coarse.physicalTerm targetPair.1 *
        S.coarse.physicalTerm targetPair.2 := by
  unfold SlabPhysicalData.physicalTerm
    finePacketObservableComponentSwapLeft
    finePacketObservableComponentSwapRight
    finePacketObservableComponentSwapMask
  exact slabParametricKPhysicalTerm_pair_supportSwap
    S.coarse.coupling hobservableFace hobservableSupport

/-! ## 5. Full common exterior Gibbs background -/

/-- For every active one-face target pair, the complete common background
product is invariant under the observable-component swap. -/
theorem finePacketCommonExteriorGibbsWeight_pair_componentSwap
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hactive : finePacketLocalizedResponsePairActiveB S first second
      (slabPhysicalFacePositiveB observableFaceId) targetPair = true) :
    finePacketCommonExteriorGibbsWeight S first second
          (finePacketObservableComponentSwapLeft
            S observableFaceId targetPair) *
        finePacketCommonExteriorGibbsWeight S first second
          (finePacketObservableComponentSwapRight
            S observableFaceId targetPair) ≈
      finePacketCommonExteriorGibbsWeight S first second targetPair.1 *
        finePacketCommonExteriorGibbsWeight S first second targetPair.2 := by
  have hne := activePair_facePositive_targetStates_ne
    S first second observableFaceId targetPair hactive
  have hsupport := positiveEitherOfNatNe
    (targetPair.1 observableFaceId) (targetPair.2 observableFaceId) hne
  let exteriorSwappedLeft := finePacketCommonExteriorMultiplicityProduct
    S first second
      (finePacketObservableComponentSwapLeft
        S observableFaceId targetPair)
  let exteriorSwappedRight := finePacketCommonExteriorMultiplicityProduct
    S first second
      (finePacketObservableComponentSwapRight
        S observableFaceId targetPair)
  let exteriorLeft := finePacketCommonExteriorMultiplicityProduct
    S first second targetPair.1
  let exteriorRight := finePacketCommonExteriorMultiplicityProduct
    S first second targetPair.2
  let physicalSwappedLeft := S.coarse.physicalTerm
    (finePacketObservableComponentSwapLeft
      S observableFaceId targetPair)
  let physicalSwappedRight := S.coarse.physicalTerm
    (finePacketObservableComponentSwapRight
      S observableFaceId targetPair)
  let physicalLeft := S.coarse.physicalTerm targetPair.1
  let physicalRight := S.coarse.physicalTerm targetPair.2
  have hexteriorNat : exteriorSwappedLeft * exteriorSwappedRight =
      exteriorLeft * exteriorRight := by
    exact finePacketCommonExteriorMultiplicityProduct_pair_componentSwap
      S first second observableFaceId targetPair
  have hexterior : Q'.ofNat exteriorSwappedLeft *
        Q'.ofNat exteriorSwappedRight ≈
      Q'.ofNat exteriorLeft * Q'.ofNat exteriorRight :=
    ofNat_pairProduct_eqv_local _ _ _ _ hexteriorNat
  have hphysical : physicalSwappedLeft * physicalSwappedRight ≈
      physicalLeft * physicalRight := by
    exact coarsePhysicalTerm_pair_componentSwap
      S observableFaceId hobservableFace targetPair hsupport
  change (Q'.ofNat exteriorSwappedLeft * physicalSwappedLeft) *
      (Q'.ofNat exteriorSwappedRight * physicalSwappedRight) ≈
    (Q'.ofNat exteriorLeft * physicalLeft) *
      (Q'.ofNat exteriorRight * physicalRight)
  refine Q'.eqv_trans _
    ((Q'.ofNat exteriorSwappedLeft * Q'.ofNat exteriorSwappedRight) *
      (physicalSwappedLeft * physicalSwappedRight)) _ ?_ ?_
  · ring_qeqv
  refine Q'.eqv_trans _
    ((Q'.ofNat exteriorLeft * Q'.ofNat exteriorRight) *
      (physicalLeft * physicalRight)) _ ?_ ?_
  · exact qmul_congr_local hexterior hphysical
  · ring_qeqv

/-! ## 6. Axiom audit -/

#print axioms finePacketCommonExteriorMultiplicityProduct_pair_componentSwap
#print axioms slabExplicitLinkMultiplicity_supportSwapLeft
#print axioms slabExplicitLinkMultiplicity_supportSwapRight
#print axioms slabExplicitLinkMultiplicity_pair_supportSwap
#print axioms slabExplicitLinkMultiplicityProduct_pair_supportSwap
#print axioms slabParametricKPhysicalTerm_pair_supportSwap
#print axioms coarsePhysicalTerm_pair_componentSwap
#print axioms finePacketCommonExteriorGibbsWeight_pair_componentSwap

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsComponentSwapBackground
