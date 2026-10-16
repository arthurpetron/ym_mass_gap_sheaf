/-
# Analytic split of the all-cutoff original-action blocking remainder

The all-cutoff physical block law has two literal components: coherent
recoupling rows and the explicit null-completion fallback on positive
incoherent rows.  This module compares the coherent component with the coarse
Wilson law and proves

  full remainderL1 <= coherent mismatch L1 + incoherent source probability.

The fallback contribution has no carrier-cardinality loss: its target `L1`
mass is exactly the normalized source probability of positive incoherent
rows.  Applying the one-step split along the finite matched trajectories from
the preceding module turns the complete iteration budget into the sum of
these two concrete analytic producers.

No decay or summability of either producer is asserted.  In particular, the
known cutoff-two positive-incoherent counterexample prevents silently deleting
the fallback term.

Constructive contract: exact finite rational sums and triangle inequalities
only; no choice, `Classical`, `native_decide`, `sorry`, noncomputable
declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration

namespace YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingRemainderSplit

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration.AllCutoffOriginalActionTrajectory
open YMGap.Continuum.CompactDualAllCutoffPhysicalPushforward
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_mono_local {A : Type} (lower upper : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → lower item ≤ upper item) →
      listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hbound =>
      Q'.add_le_add
        (hbound head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem =>
            hbound item (List.mem_cons_of_mem head hitem)))

/-! ## 1. One-step coherent/fallback split -/

/-- Signed mismatch between the coherent recoupling pushforward and the
normalized coarse Wilson law. -/
def coherentWilsonRemainder
    (S : SlabScalePair) (target : EdgeLabelling) : Q' :=
  coherentRecouplingBlockedMass S target +
    -(S.coarse.normalizedMass target)

/-- Total variation of the coherent recoupling component from the normalized
coarse Wilson law. -/
def coherentWilsonRemainderL1 (S : SlabScalePair) : Q' :=
  listQSum (fun target => Q'.abs (coherentWilsonRemainder S target))
    S.coarse.physicalLabellings

/-- Targetwise, the complete pushed-law remainder is the coherent-to-Wilson
mismatch plus the nonnegative fallback column. -/
theorem allCutoffPhysicalRemainder_eqv_coherentWilson_add_fallback
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (target : EdgeLabelling) :
    (allCutoffPhysicalKernel S hfineCutoff).remainder target ≈
      coherentWilsonRemainder S target +
        positiveIncoherentFallbackBlockedMass S target := by
  let coherent := coherentRecouplingBlockedMass S target
  let fallback := positiveIncoherentFallbackBlockedMass S target
  let coarse := S.coarse.normalizedMass target
  unfold SlabScalePair.FiniteSlabKernel.remainder
    coherentWilsonRemainder
  refine Q'.eqv_trans _ ((coherent + fallback) + (-coarse)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ (-coarse)
      (blockedMass_eq_coherent_add_incoherent
        S hfineCutoff target)
  refine Q'.eqv_trans _ (coherent + (fallback + (-coarse))) _
    (Q'.add_assoc_eqv coherent fallback (-coarse)) ?_
  refine Q'.eqv_trans _ (coherent + ((-coarse) + fallback)) _
    (Q'.add_eqv_congr_left coherent _ _
      (Q'.add_comm_eqv fallback (-coarse))) ?_
  exact Q'.eqv_symm
    (Q'.add_assoc_eqv coherent (-coarse) fallback)

private theorem allCutoffPhysicalRemainder_abs_le_coherent_add_fallback
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (target : EdgeLabelling) :
    Q'.abs ((allCutoffPhysicalKernel S hfineCutoff).remainder target) ≤
      Q'.abs (coherentWilsonRemainder S target) +
        positiveIncoherentFallbackBlockedMass S target := by
  refine Q'.le_trans' _
    (Q'.abs
      (coherentWilsonRemainder S target +
        positiveIncoherentFallbackBlockedMass S target)) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (allCutoffPhysicalRemainder_eqv_coherentWilson_add_fallback
          S hfineCutoff target))
  refine Q'.le_trans' _
    (Q'.abs (coherentWilsonRemainder S target) +
      Q'.abs (positiveIncoherentFallbackBlockedMass S target)) _
    (Q'.abs_add_le' _ _) ?_
  exact Q'.le_of_eqv
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_of_eq
        (ExpNeg.abs_of_nonneg
          (positiveIncoherentFallbackBlockedMass_nonnegative S target))))

/-- The full physical pushforward defect has exactly two finite analytic
producers: coherent recoupling mismatch and positive-incoherent source mass. -/
theorem allCutoffPhysicalRemainderL1_le_coherentWilson_add_incoherent
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff) :
    (allCutoffPhysicalKernel S hfineCutoff).remainderL1 ≤
      coherentWilsonRemainderL1 S +
        positiveIncoherentRecouplingMass S := by
  refine Q'.le_trans' _
    (listQSum
      (fun target =>
        Q'.abs (coherentWilsonRemainder S target) +
          positiveIncoherentFallbackBlockedMass S target)
      S.coarse.physicalLabellings) _ ?_ ?_
  · unfold SlabScalePair.FiniteSlabKernel.remainderL1
    apply listQSum_mono_local
    intro target _htarget
    exact allCutoffPhysicalRemainder_abs_le_coherent_add_fallback
      S hfineCutoff target
  refine Q'.le_of_eqv (Q'.eqv_trans _
    (coherentWilsonRemainderL1 S +
      listQSum (positiveIncoherentFallbackBlockedMass S)
        S.coarse.physicalLabellings) _ ?_ ?_)
  · unfold coherentWilsonRemainderL1
    exact listQSum_add
      (fun target => Q'.abs (coherentWilsonRemainder S target))
      (positiveIncoherentFallbackBlockedMass S)
      S.coarse.physicalLabellings
  · exact Q'.add_eqv_congr_left _ _ _
      (positiveIncoherentFallbackBlockedMass_total
        S hfineCutoff)

/-! ## 2. Finite-trajectory analytic budget -/

namespace AllCutoffOriginalActionTrajectory

/-- Sum along the trajectory of the coherent mismatch and the exact
positive-incoherent source probability. -/
def splitBudget : AllCutoffOriginalActionTrajectory → Q'
  | .single step =>
      coherentWilsonRemainderL1 step.pair +
        positiveIncoherentRecouplingMass step.pair
  | .append prior next =>
      splitBudget prior +
        (coherentWilsonRemainderL1 next.pair +
          positiveIncoherentRecouplingMass next.pair)

/-- The literal sum of one-step total-variation remainders is bounded by the
sum of the two explicit analytic producers. -/
theorem remainderBudget_le_splitBudget
    (trajectory : AllCutoffOriginalActionTrajectory) :
    remainderBudget trajectory ≤ splitBudget trajectory := by
  induction trajectory with
  | single step =>
      unfold remainderBudget splitBudget
      exact allCutoffPhysicalRemainderL1_le_coherentWilson_add_incoherent
        step.pair step.fineCutoff
  | append prior next ih =>
      unfold remainderBudget splitBudget
      exact Q'.add_le_add ih
        (allCutoffPhysicalRemainderL1_le_coherentWilson_add_incoherent
          next.pair next.fineCutoff)

/-- A matched finite trajectory is controlled by the split analytic budget. -/
theorem defectL1_le_splitBudget
    (trajectory : AllCutoffOriginalActionTrajectory)
    (hmatched : Matched trajectory) :
    defectL1 trajectory ≤ splitBudget trajectory := by
  exact Q'.le_trans' _ _ _
    (defectL1_le_remainderBudget trajectory hmatched)
    (remainderBudget_le_splitBudget trajectory)

/-- Every unit-bounded final observable is controlled by the same split
analytic budget. -/
theorem expectation_defect_le_splitBudget
    (trajectory : AllCutoffOriginalActionTrajectory)
    (hmatched : Matched trajectory)
    (observable : EdgeLabelling → Q')
    (hbound : ∀ state,
      state ∈ (lastStep trajectory).pair.coarse.physicalLabellings →
        Q'.abs (observable state) ≤ (1 : Q')) :
    Q'.abs
        (blockedExpectation trajectory observable +
          -(coarseWilsonExpectation trajectory observable)) ≤
      splitBudget trajectory := by
  exact Q'.le_trans' _ _ _
    (expectation_defect_le_remainderBudget
      trajectory hmatched observable hbound)
    (remainderBudget_le_splitBudget trajectory)

end AllCutoffOriginalActionTrajectory

/-! ## Axiom audit -/

#print axioms coherentWilsonRemainder
#print axioms coherentWilsonRemainderL1
#print axioms allCutoffPhysicalRemainder_eqv_coherentWilson_add_fallback
#print axioms allCutoffPhysicalRemainderL1_le_coherentWilson_add_incoherent
#print axioms AllCutoffOriginalActionTrajectory.splitBudget
#print axioms AllCutoffOriginalActionTrajectory.remainderBudget_le_splitBudget
#print axioms AllCutoffOriginalActionTrajectory.defectL1_le_splitBudget
#print axioms AllCutoffOriginalActionTrajectory.expectation_defect_le_splitBudget

end YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingRemainderSplit
