/-
# Coarsen profiled terminal codes to the load-bearing summary fiber

The faithful terminal code retains every source coordinate.  Its summand,
however, depends only on the finite keys of the two physical source rows, the
total profile mass, and the finite keys of the fine and coarse accepted
terminals.  This file compiles to exactly that decidable summary.

Equal summaries reconstruct equal raw source rows and terminal states, so the
profile-weighted terminal summand is constant on every summary fiber.  Exact
finite Fubini therefore rewrites the remaining mass as

  sum summary,
    fiberCardinality summary * fiberRepresentativeWeight summary.

The representative is selected by structural recursion from the literal
finite fiber, with zero used only for an empty fiber.  Thus the next frontier
is one explicit cardinality estimate; none is assumed or claimed here.

Constructive contract: exact finite-support recoding, duplicate-free image
enumeration, deterministic-kernel Fubini, and rational finite sums only; no
classical choice, proof hole, trusted external computation, computability
escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalCodeMass

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSummaryFiber

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalCompiler
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalCodeMass
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem filteredEraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) :
    ∀ predicate : A → Bool, (items.filter predicate).eraseDups.Nodup := by
  induction items with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons head tail ih =>
      intro predicate
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr ⟨?_, ih _⟩
        intro hmem
        have hfiltered := List.mem_eraseDups.mp hmem
        have hfalse := (List.mem_filter.mp hfiltered).2
        have hself : (head == head) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact ih _

private theorem filterTrueLocal {A : Type} : ∀ items : List A,
    items.filter (fun _ => true) = items
  | [] => rfl
  | head :: tail => congrArg (List.cons head) (filterTrueLocal tail)

private theorem eraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) : items.eraseDups.Nodup := by
  have h := filteredEraseDupsNodupLocal items (fun _ => true)
  rw [filterTrueLocal] at h
  exact h

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

private def firstListWeight {A : Type}
    (weight : A → Q') : List A → Q'
  | [] => 0
  | head :: _ => weight head

private theorem listQSum_eqv_length_mul_first_of_constant_on
    {A : Type} (weight : A → Q') (items : List A)
    (hconstant : ∀ left, left ∈ items → ∀ right, right ∈ items →
      weight left ≈ weight right) :
    listQSum weight items ≈
      Q'.ofNat items.length * firstListWeight weight items := by
  cases items with
  | nil =>
      exact Q'.eqv_symm (Q'.zero_mul_eqv 0)
  | cons head tail =>
      have hagree :
          listQSum weight (head :: tail) ≈
            listQSum (fun _ => weight head) (head :: tail) := by
        apply listQSum_congr_on
        intro item hitem
        exact hconstant item hitem head List.mem_cons_self
      exact Q'.eqv_trans _ _ _ hagree
        (listQSum_const_local (weight head) (head :: tail))

private def finiteFiberCardinality {A B : Type} [DecidableEq B]
    (source : List A) (code : A → B) (target : B) : Nat :=
  (source.filter (fun item => decide (target = code item))).length

private def finiteFiberRepresentativeWeight {A B : Type} [DecidableEq B]
    (source : List A) (weight : A → Q') (code : A → B)
    (target : B) : Q' :=
  firstListWeight weight
    (source.filter (fun item => decide (target = code item)))

private theorem fiberWeight_eqv_cardinality_mul_representative_of_constant
    {A B : Type} [DecidableEq B]
    (source : List A) (weight : A → Q') (code : A → B)
    (target : B)
    (hconstant : ∀ left, left ∈ source → ∀ right, right ∈ source →
      target = code left → target = code right →
        weight left ≈ weight right) :
    fiberWeight source weight code target ≈
      Q'.ofNat (finiteFiberCardinality source code target) *
        finiteFiberRepresentativeWeight source weight code target := by
  unfold fiberWeight finiteFiberCardinality finiteFiberRepresentativeWeight
  apply listQSum_eqv_length_mul_first_of_constant_on
  intro left hleft right hright
  have hleftParts := List.mem_filter.mp hleft
  have hrightParts := List.mem_filter.mp hright
  exact hconstant left hleftParts.1 right hrightParts.1
    (of_decide_eq_true hleftParts.2)
    (of_decide_eq_true hrightParts.2)

/-! ## 1. The decidable terminal summary -/

structure FinePacketConnectedRateProfiledTerminalSummaryCode : Type where
  leftSource : List Nat
  rightSource : List Nat
  profileMass : Nat
  fineLeftTerminal : SlabExpandedFineTargetKey
  fineRightTerminal : SlabExpandedFineTargetKey
  coarseLeftTerminal : SlabExpandedFineTargetKey
  coarseRightTerminal : SlabExpandedFineTargetKey
  weight : Q'
deriving DecidableEq

def finePacketConnectedRateProfiledTerminalSummaryCompiler
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (code :
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0) :
    FinePacketConnectedRateProfiledTerminalSummaryCode where
  leftSource := positivePhysicalSourceFiniteKey S code.1.1
  rightSource := positivePhysicalSourceFiniteKey S code.1.2
  profileMass :=
    finePacketConnectedFourEntryRateProfiledCompilerCodeMass code
  fineLeftTerminal := code.2.2.2.1.1.1.1.key
  fineRightTerminal := code.2.2.2.1.1.1.2.key
  coarseLeftTerminal := code.2.2.2.1.2.1.1.key
  coarseRightTerminal := code.2.2.2.1.2.1.2.key
  weight := finePacketConnectedRateProfiledTerminalCodeWeight
    S hfineCutoff hcoarseCoupling rate hrate0 code

/-- The full profile-weighted summand factors through the finite summary.
This is the load-bearing reason the next fiber contributes only a cardinality
factor. -/
theorem finePacketConnectedRateProfiledTerminalCodeWeight_eqv_of_summary_eq
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (left right :
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0)
    (hsummary :
      finePacketConnectedRateProfiledTerminalSummaryCompiler
          S hfineCutoff hcoarseCoupling rate hrate0 left =
        finePacketConnectedRateProfiledTerminalSummaryCompiler
          S hfineCutoff hcoarseCoupling rate hrate0 right) :
    finePacketConnectedRateProfiledTerminalCodeWeight
        S hfineCutoff hcoarseCoupling rate hrate0 left ≈
      finePacketConnectedRateProfiledTerminalCodeWeight
        S hfineCutoff hcoarseCoupling rate hrate0 right := by
  exact Q'.eqv_of_eq
    (congrArg FinePacketConnectedRateProfiledTerminalSummaryCode.weight hsummary)

/-! ## 2. The realized summary carrier and exact Fubini -/

def finePacketConnectedRateProfiledTerminalSummaries
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    List FinePacketConnectedRateProfiledTerminalSummaryCode :=
  ((finePacketConnectedRateProfiledNormalizedTerminalCodes
      S rate hrate0 orientation observableFaceId hobservableFace).map
    (finePacketConnectedRateProfiledTerminalSummaryCompiler
      S hfineCutoff hcoarseCoupling rate hrate0)).eraseDups

theorem finePacketConnectedRateProfiledTerminalSummaries_nodup
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    (finePacketConnectedRateProfiledTerminalSummaries
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace).Nodup := by
  unfold finePacketConnectedRateProfiledTerminalSummaries
  exact eraseDupsNodupLocal _

theorem finePacketConnectedRateProfiledTerminalSummary_mem
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code :
      FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
        S rate hrate0)
    (hcode : code ∈
      finePacketConnectedRateProfiledNormalizedTerminalCodes
        S rate hrate0 orientation observableFaceId hobservableFace) :
    finePacketConnectedRateProfiledTerminalSummaryCompiler
        S hfineCutoff hcoarseCoupling rate hrate0 code ∈
      finePacketConnectedRateProfiledTerminalSummaries
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace := by
  apply List.mem_eraseDups.mpr
  exact List.mem_map.mpr ⟨code, hcode, rfl⟩

theorem finePacketConnectedRateProfiledTerminalSummaryFiber_total
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    listQSum
        (fiberWeight
          (finePacketConnectedRateProfiledNormalizedTerminalCodes
            S rate hrate0 orientation observableFaceId hobservableFace)
          (finePacketConnectedRateProfiledTerminalCodeWeight
            S hfineCutoff hcoarseCoupling rate hrate0)
          (finePacketConnectedRateProfiledTerminalSummaryCompiler
            S hfineCutoff hcoarseCoupling rate hrate0))
        (finePacketConnectedRateProfiledTerminalSummaries
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace) ≈
      finePacketConnectedRateProfiledTerminalCodeMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace := by
  exact fiberWeight_total
    (finePacketConnectedRateProfiledNormalizedTerminalCodes
      S rate hrate0 orientation observableFaceId hobservableFace)
    (finePacketConnectedRateProfiledTerminalCodeWeight
      S hfineCutoff hcoarseCoupling rate hrate0)
    (finePacketConnectedRateProfiledTerminalSummaryCompiler
      S hfineCutoff hcoarseCoupling rate hrate0)
    (finePacketConnectedRateProfiledTerminalSummaries
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    (finePacketConnectedRateProfiledTerminalSummaries_nodup
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    (fun code hcode =>
      finePacketConnectedRateProfiledTerminalSummary_mem
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace code hcode)

/-! ## 3. Expose the sole remaining multiplicity -/

def finePacketConnectedRateProfiledTerminalSummaryFiberCodes
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (summary : FinePacketConnectedRateProfiledTerminalSummaryCode) :
    List (FinePacketConnectedFourEntryRateProfiledNormalizedTerminalCompilerCode
      S rate hrate0) :=
  (finePacketConnectedRateProfiledNormalizedTerminalCodes
      S rate hrate0 orientation observableFaceId hobservableFace).filter
    (fun code => decide
      (summary =
        finePacketConnectedRateProfiledTerminalSummaryCompiler
          S hfineCutoff hcoarseCoupling rate hrate0 code))

def finePacketConnectedRateProfiledTerminalSummaryFiberCardinality
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (summary : FinePacketConnectedRateProfiledTerminalSummaryCode) : Nat :=
  finiteFiberCardinality
    (finePacketConnectedRateProfiledNormalizedTerminalCodes
      S rate hrate0 orientation observableFaceId hobservableFace)
    (finePacketConnectedRateProfiledTerminalSummaryCompiler
      S hfineCutoff hcoarseCoupling rate hrate0)
    summary

def finePacketConnectedRateProfiledTerminalSummaryRepresentativeWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (summary : FinePacketConnectedRateProfiledTerminalSummaryCode) : Q' :=
  finiteFiberRepresentativeWeight
    (finePacketConnectedRateProfiledNormalizedTerminalCodes
      S rate hrate0 orientation observableFaceId hobservableFace)
    (finePacketConnectedRateProfiledTerminalCodeWeight
      S hfineCutoff hcoarseCoupling rate hrate0)
    (finePacketConnectedRateProfiledTerminalSummaryCompiler
      S hfineCutoff hcoarseCoupling rate hrate0)
    summary

theorem finePacketConnectedRateProfiledTerminalSummaryFiberWeight_eqv_cardinality_mul_representative
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (summary : FinePacketConnectedRateProfiledTerminalSummaryCode) :
    fiberWeight
        (finePacketConnectedRateProfiledNormalizedTerminalCodes
          S rate hrate0 orientation observableFaceId hobservableFace)
        (finePacketConnectedRateProfiledTerminalCodeWeight
          S hfineCutoff hcoarseCoupling rate hrate0)
        (finePacketConnectedRateProfiledTerminalSummaryCompiler
          S hfineCutoff hcoarseCoupling rate hrate0)
        summary ≈
      Q'.ofNat
          (finePacketConnectedRateProfiledTerminalSummaryFiberCardinality
            S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
              hobservableFace summary) *
        finePacketConnectedRateProfiledTerminalSummaryRepresentativeWeight
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace summary := by
  unfold finePacketConnectedRateProfiledTerminalSummaryFiberCardinality
    finePacketConnectedRateProfiledTerminalSummaryRepresentativeWeight
  exact fiberWeight_eqv_cardinality_mul_representative_of_constant
    (finePacketConnectedRateProfiledNormalizedTerminalCodes
      S rate hrate0 orientation observableFaceId hobservableFace)
    (finePacketConnectedRateProfiledTerminalCodeWeight
      S hfineCutoff hcoarseCoupling rate hrate0)
    (finePacketConnectedRateProfiledTerminalSummaryCompiler
      S hfineCutoff hcoarseCoupling rate hrate0)
    summary
    (by
      intro left _ right _ hleftSummary hrightSummary
      exact
        finePacketConnectedRateProfiledTerminalCodeWeight_eqv_of_summary_eq
          S hfineCutoff hcoarseCoupling rate hrate0 left right
            (hleftSummary.symm.trans hrightSummary))

def finePacketConnectedRateProfiledTerminalSummaryMultiplicityMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (fun summary =>
      Q'.ofNat
          (finePacketConnectedRateProfiledTerminalSummaryFiberCardinality
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace summary) *
        finePacketConnectedRateProfiledTerminalSummaryRepresentativeWeight
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace summary)
    (finePacketConnectedRateProfiledTerminalSummaries
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)

theorem finePacketConnectedRateProfiledTerminalCodeMass_eqv_summaryMultiplicityMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketConnectedRateProfiledTerminalCodeMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace ≈
      finePacketConnectedRateProfiledTerminalSummaryMultiplicityMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace := by
  refine Q'.eqv_trans _
    (listQSum
      (fiberWeight
        (finePacketConnectedRateProfiledNormalizedTerminalCodes
          S rate hrate0 orientation observableFaceId hobservableFace)
        (finePacketConnectedRateProfiledTerminalCodeWeight
          S hfineCutoff hcoarseCoupling rate hrate0)
        (finePacketConnectedRateProfiledTerminalSummaryCompiler
          S hfineCutoff hcoarseCoupling rate hrate0))
      (finePacketConnectedRateProfiledTerminalSummaries
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace)) _ ?_ ?_
  · exact Q'.eqv_symm
      (finePacketConnectedRateProfiledTerminalSummaryFiber_total
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace)
  unfold finePacketConnectedRateProfiledTerminalSummaryMultiplicityMass
  apply listQSum_congr
  intro summary
  exact
    finePacketConnectedRateProfiledTerminalSummaryFiberWeight_eqv_cardinality_mul_representative
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace summary

/-- The connected mass is now bounded by a sum whose only hidden
combinatorics is the displayed summary-fiber cardinality. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateProfiledTerminalSummaryMultiplicityMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') < rate)
    (hrate1 : rate < (1 : Q'))
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (hrateAnchor : rate ≤ anchorCoupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
    finePacketGlobalNonzeroConnectedExpandedWitnessMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace ≤
      finePacketConnectedRateProfiledTerminalSummaryMultiplicityMass
        S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
          hobservableFace := by
  let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
  exact Q'.le_trans' _ _ _
    (finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateProfiledTerminalCodeMass
      S hfineCutoff hcoarseCoupling rate hrate0 hrate1 hcoarseRate hrateAnchor
        orientation observableFaceId hobservableFace)
    (Q'.le_of_eqv
      (finePacketConnectedRateProfiledTerminalCodeMass_eqv_summaryMultiplicityMass
        S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
          hobservableFace))

#print axioms FinePacketConnectedRateProfiledTerminalSummaryCode
#print axioms finePacketConnectedRateProfiledTerminalSummaryCompiler
#print axioms finePacketConnectedRateProfiledTerminalCodeWeight_eqv_of_summary_eq
#print axioms finePacketConnectedRateProfiledTerminalSummaries
#print axioms finePacketConnectedRateProfiledTerminalSummaries_nodup
#print axioms finePacketConnectedRateProfiledTerminalSummary_mem
#print axioms finePacketConnectedRateProfiledTerminalSummaryFiber_total
#print axioms finePacketConnectedRateProfiledTerminalSummaryFiberCodes
#print axioms finePacketConnectedRateProfiledTerminalSummaryFiberCardinality
#print axioms finePacketConnectedRateProfiledTerminalSummaryRepresentativeWeight
#print axioms finePacketConnectedRateProfiledTerminalSummaryFiberWeight_eqv_cardinality_mul_representative
#print axioms finePacketConnectedRateProfiledTerminalSummaryMultiplicityMass
#print axioms finePacketConnectedRateProfiledTerminalCodeMass_eqv_summaryMultiplicityMass
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateProfiledTerminalSummaryMultiplicityMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSummaryFiber
