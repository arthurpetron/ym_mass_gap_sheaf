/-
# The parity ground state of every cutoff-one production row

The all-source lowering law identifies the support of a positive cutoff-one
production row as a pointwise parity-preserving downset.  The geometric
mod-two pushforward already constructs a physical coarse state with exactly
the required face parity.  This file proves that this state is the pointwise
minimal element of the lowering downset.

The local multiplicity at that ground spin is one for packet totals zero,
one, and two, and two for packet totals three and four.  Their finite product
therefore gives an explicit positive summand in every source-dependent tilted
Gibbs partition.  In particular, the complete row denominator is bounded
below by this literal ground summand.

This is an exact finite-volume denominator certificate.  It does not yet
bound the total mass of the excited targets relative to the ground term.

Constructive contract: finite exact-rational sums/products and five-case
decidable SU(2) arithmetic only; no `Classical`, choice, `native_decide`,
proof hole, noncomputable declaration, trusted external computation, or new
axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
import YMGap.Continuum.CompactDualCutoffOneParitySlabTarget
import YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure

namespace YMGap.Continuum.Z4DyadicBinarySourceParityGroundState

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualCutoffOneParitySlabTarget
open YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt
open YMGap.Continuum.Z4DyadicSpinFourLoweringKernel
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact local ground multiplicity -/

/-- Closed table for the multiplicity of the smallest parity-compatible
retained spin below a binary packet total. -/
def spinFourParityGroundMultiplicity : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | _ => 0

/-- The local lowering multiplicity at the parity ground spin is given by
the closed five-entry table. -/
theorem spinFourLoweringMultiplicity_parityGround
    {sourceSpin : Nat} (hsource : sourceSpin ≤ 4) :
    spinFourLoweringMultiplicity sourceSpin (sourceSpin % 2) =
      spinFourParityGroundMultiplicity sourceSpin := by
  have hs : sourceSpin = 0 ∨ sourceSpin = 1 ∨ sourceSpin = 2 ∨
      sourceSpin = 3 ∨ sourceSpin = 4 := by
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Every admissible local parity-ground channel has positive integer
multiplicity. -/
theorem spinFourParityGroundMultiplicity_pos
    {sourceSpin : Nat} (hsource : sourceSpin ≤ 4) :
    0 < spinFourParityGroundMultiplicity sourceSpin := by
  have hs : sourceSpin = 0 ∨ sourceSpin = 1 ∨ sourceSpin = 2 ∨
      sourceSpin = 3 ∨ sourceSpin = 4 := by
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The only local reward carried by the parity ground channel is one or
two. -/
theorem spinFourParityGroundMultiplicity_le_two
    {sourceSpin : Nat} (hsource : sourceSpin ≤ 4) :
    spinFourParityGroundMultiplicity sourceSpin ≤ 2 := by
  have hs : sourceSpin = 0 ∨ sourceSpin = 1 ∨ sourceSpin = 2 ∨
      sourceSpin = 3 ∨ sourceSpin = 4 := by
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## 2. The geometric parity state is the lowering ground state -/

/-- On every physical coarse face, the geometric parity pushforward equals
the total number of fine fundamental strands modulo two. -/
theorem cutoffOneCoarseParityState_face_eq_total_mod_two
    (S : SlabScalePair) {fineState : EdgeLabelling}
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    {faceId : Nat} (hface : faceId ∈ S.coarse.faceEdges) :
    cutoffOneCoarseParityState S fineState faceId =
      wholeSlabFinePacketTotalLabelling S fineState faceId % 2 := by
  rw [cutoffOneCoarseParityState_face_eq_channel
    hfineCutoff hfineMem hface]
  rfl

/-- The geometric parity pushforward is a physical member of the exact
pointwise lowering carrier for every cutoff-one fine physical source. -/
theorem cutoffOneCoarseParityState_mem_totalLoweringTargets
    (S : SlabScalePair) {fineState : EdgeLabelling}
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineMem : fineState ∈ S.fine.physicalLabellings) :
    cutoffOneCoarseParityState S fineState ∈
      spinFourLoweringTargets S
        (wholeSlabFinePacketTotalLabelling S fineState) := by
  apply (mem_spinFourLoweringTargets_iff S _ _).mpr
  refine ⟨cutoffOneCoarseParityState_mem hfineCutoff fineState, ?_⟩
  intro faceId hface
  rw [cutoffOneCoarseParityState_face_eq_total_mod_two
    S hfineCutoff hfineMem hface]
  have hsource := wholeSlabFinePacketTotalLabelling_le_four
    S hfineCutoff hfineMem faceId hface
  have hs :
      wholeSlabFinePacketTotalLabelling S fineState faceId = 0 ∨
      wholeSlabFinePacketTotalLabelling S fineState faceId = 1 ∨
      wholeSlabFinePacketTotalLabelling S fineState faceId = 2 ∨
      wholeSlabFinePacketTotalLabelling S fineState faceId = 3 ∨
      wholeSlabFinePacketTotalLabelling S fineState faceId = 4 := by
    omega
  rcases hs with hs | hs | hs | hs | hs <;> rw [hs] <;> decide

/-! ## 3. The explicit global ground multiplier -/

/-- Product of the local parity-ground fusion rewards over the complete
coarse face carrier. -/
def spinFourParityGroundMultiplicityProduct
    (S : SlabScalePair) (sourceState : EdgeLabelling) : Nat :=
  natListProduct
    (fun faceId => spinFourParityGroundMultiplicity (sourceState faceId))
    S.coarse.faceEdges

/-- At the geometric ground target, the all-face lowering multiplier is
exactly the product of the local parity-ground rewards. -/
theorem spinFourLoweringMultiplicityProduct_parityGround
    (S : SlabScalePair) {fineState : EdgeLabelling}
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineMem : fineState ∈ S.fine.physicalLabellings) :
    spinFourLoweringMultiplicityProduct S
        (wholeSlabFinePacketTotalLabelling S fineState)
        (cutoffOneCoarseParityState S fineState) =
      spinFourParityGroundMultiplicityProduct S
        (wholeSlabFinePacketTotalLabelling S fineState) := by
  unfold spinFourLoweringMultiplicityProduct
    spinFourParityGroundMultiplicityProduct
  apply natListProduct_congr
  intro faceId hface
  rw [cutoffOneCoarseParityState_face_eq_total_mod_two
    S hfineCutoff hfineMem hface]
  exact spinFourLoweringMultiplicity_parityGround
    (wholeSlabFinePacketTotalLabelling_le_four
      S hfineCutoff hfineMem faceId hface)

private theorem natListProduct_pos_of_pointwise_local {A : Type}
    (value : A → Nat) : ∀ items : List A,
    (∀ item, item ∈ items → 0 < value item) →
      0 < natListProduct value items
  | [], _ => by
      change 0 < 1
      decide
  | head :: tail, hpositive => by
      simp only [natListProduct]
      exact Nat.mul_pos
        (hpositive head List.mem_cons_self)
        (natListProduct_pos_of_pointwise_local value tail
          (fun item hmem =>
            hpositive item (List.mem_cons_of_mem head hmem)))

/-- The complete parity-ground fusion reward is a positive integer. -/
theorem spinFourParityGroundMultiplicityProduct_pos
    (S : SlabScalePair) {fineState : EdgeLabelling}
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineMem : fineState ∈ S.fine.physicalLabellings) :
    0 < spinFourParityGroundMultiplicityProduct S
      (wholeSlabFinePacketTotalLabelling S fineState) := by
  unfold spinFourParityGroundMultiplicityProduct
  apply natListProduct_pos_of_pointwise_local
  intro faceId hface
  exact spinFourParityGroundMultiplicity_pos
    (wholeSlabFinePacketTotalLabelling_le_four
      S hfineCutoff hfineMem faceId hface)

/-! ## 4. A literal positive denominator term -/

/-- The exact tilted-Gibbs mass of the source's geometric parity ground
state. -/
def positivePhysicalSourceParityGroundMass
    (S : SlabScalePair) (source : PositivePhysicalSource S) : Q' :=
  Q'.ofNat
      (spinFourLoweringMultiplicityProduct S
        (wholeSlabFinePacketTotalLabelling S source.1)
        (cutoffOneCoarseParityState S source.1)) *
    S.coarse.physicalTerm
      (cutoffOneCoarseParityState S source.1)

/-- The literal globally glued raw entry at the parity state is exactly the
displayed ground summand. -/
theorem wholeSlabRecouplingRawWeight_positivePhysicalSource_eqv_parityGroundMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (source : PositivePhysicalSource S) :
    wholeSlabRecouplingRawWeight S source.1
        (cutoffOneCoarseParityState S source.1) ≈
      positivePhysicalSourceParityGroundMass S source := by
  refine Q'.eqv_trans _
    (spinFourLoweringWholeSlabRawWeight S
      (wholeSlabFinePacketTotalLabelling S source.1)
      (cutoffOneCoarseParityState S source.1)) _ ?_ ?_
  · exact wholeSlabRecouplingRawWeight_eqv_totalLoweringWeight
      S source.1 (cutoffOneCoarseParityState S source.1)
        hfineCutoff source.2.1
        (cutoffOneCoarseParityState_mem hfineCutoff source.1)
  · exact spinFourLoweringWholeSlabRawWeight_eqv_multiplicity_mul_physicalTerm
      S (wholeSlabFinePacketTotalLabelling S source.1)
        (cutoffOneCoarseParityState S source.1)
        (cutoffOneCoarseParityState_mem hfineCutoff source.1)

/-- The parity ground summand is strictly positive for every positive fine
source and positive coarse coupling. -/
theorem positivePhysicalSourceParityGroundMass_pos
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : PositivePhysicalSource S) :
    (0 : Q') < positivePhysicalSourceParityGroundMass S source := by
  have heven :=
    positiveCutoffOnePhysicalTerm_fineOddSupport_even
      hfineCutoff source.2.1 source.2.2
  have hraw :=
    cutoffOneCoarseParityState_rawWeight_pos
      hfineCutoff source.2.1 heven hcoarseCoupling
  exact Q'.pos_of_lt_of_le hraw
    (Q'.le_of_eqv
      (wholeSlabRecouplingRawWeight_positivePhysicalSource_eqv_parityGroundMass
        S hfineCutoff source))

/-- The source-dependent row denominator contains the parity ground summand
literally and is therefore bounded below by it. -/
theorem positivePhysicalSourceParityGroundMass_le_rowMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : PositivePhysicalSource S) :
    positivePhysicalSourceParityGroundMass S source ≤
      positivePhysicalSourceTiltedGibbsRowMass S source := by
  unfold positivePhysicalSourceParityGroundMass
    positivePhysicalSourceTiltedGibbsRowMass
  exact
    YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure.listQSum_member_le
      (fun targetState =>
        Q'.ofNat
            (spinFourLoweringMultiplicityProduct S
              (wholeSlabFinePacketTotalLabelling S source.1)
              targetState) *
          S.coarse.physicalTerm targetState)
      (fun targetState =>
        Q'.mul_nonneg _ _
          (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _)
          (slabParametricKPhysicalTerm_nonnegative
            (Q'.le_of_lt hcoarseCoupling) S.coarse.cutoff
              S.coarse.extent targetState))
      (spinFourLoweringTargets S
        (wholeSlabFinePacketTotalLabelling S source.1))
      (cutoffOneCoarseParityState_mem_totalLoweringTargets
        S hfineCutoff source.2.1)

/-- Consequently the actual production kernel assigns strictly positive
mass to its source-dependent parity ground state. -/
theorem physicalKernel_positivePhysicalSource_parityGround_pos
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : PositivePhysicalSource S) :
    (0 : Q') <
      (physicalKernel S hfineCutoff hcoarseCoupling).kernel source.1
        (cutoffOneCoarseParityState S source.1) := by
  have htargetMem :=
    cutoffOneCoarseParityState_mem hfineCutoff source.1
  have heq := physicalKernel_positivePhysicalSource_eqv_tiltedGibbs
    S hfineCutoff hcoarseCoupling source
      (cutoffOneCoarseParityState S source.1) htargetMem
  have hratio : (0 : Q') <
      Q'.divPos
        (positivePhysicalSourceParityGroundMass S source)
        (positivePhysicalSourceTiltedGibbsRowMass S source)
        (positivePhysicalSourceTiltedGibbsRowMass_pos
          S hfineCutoff hcoarseCoupling source) :=
    Q'.divPos_pos _ _
      (positivePhysicalSourceTiltedGibbsRowMass_pos
        S hfineCutoff hcoarseCoupling source)
      (positivePhysicalSourceParityGroundMass_pos
        S hfineCutoff hcoarseCoupling source)
  exact Q'.pos_of_lt_of_le hratio
    (Q'.le_of_eqv (Q'.eqv_symm heq))

/-! ## 5. Axiom audit -/

#print axioms spinFourLoweringMultiplicity_parityGround
#print axioms cutoffOneCoarseParityState_face_eq_total_mod_two
#print axioms cutoffOneCoarseParityState_mem_totalLoweringTargets
#print axioms spinFourLoweringMultiplicityProduct_parityGround
#print axioms spinFourParityGroundMultiplicityProduct_pos
#print axioms wholeSlabRecouplingRawWeight_positivePhysicalSource_eqv_parityGroundMass
#print axioms positivePhysicalSourceParityGroundMass_pos
#print axioms positivePhysicalSourceParityGroundMass_le_rowMass
#print axioms physicalKernel_positivePhysicalSource_parityGround_pos

end YMGap.Continuum.Z4DyadicBinarySourceParityGroundState
