/-
# The all-cutoff four-preimage pushforward has genuine positive fallback mass

The all-cutoff total kernel makes every incoherent positive row explicit.
The previously constructed cutoff-two collar state is such a row: its fine
SU(2) Gibbs weight is strictly positive, but its complete four-preimage
recoupling row has no positive target.

This module joins those facts.  The collar state's normalized Gibbs mass is
strictly positive, its incoherent-row weight is strictly positive, and hence
the total incoherent probability and the exact fallback `L1` cost are both
strictly positive.  Therefore the old four-preimage target carrier cannot be
an exact all-cutoff physical RG trajectory; a corrected trajectory must
retain the missing fine intertwiner/collar information.

No quantitative lower bound uniform in coupling or volume, no spectral gap,
continuum limit, or Clay theorem is claimed.

## Axiom gate

Finite exact-rational algebra and the explicit cutoff-two certificate only.
No classical choice, placeholder, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffPhysicalPushforward
import YMGap.Continuum.BF4SU2OuterRawRowMassCounterexample

namespace
  YMGap.Continuum.CompactDualAllCutoffPhysicalPushforwardCounterexample

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2OuterBinaryLayerCounterexample
open YMGap.Continuum.BF4SU2OuterJointCarrierRawRowMass
open YMGap.Continuum.BF4SU2OuterRawRowMassCounterexample
open YMGap.Continuum.CompactDualAllCutoffPhysicalPushforward
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

theorem collarState_wholeSlabRawRowPartition_not_pos :
    ¬ (0 : Q') <
      wholeSlabRawRowPartition counterScalePair collarState := by
  simpa only [wholeSlabRawRowPartition,
    wholeSlabJointRawRowMass] using
      collarState_rawRowMass_not_pos

theorem collarState_normalizedMass_pos :
    (0 : Q') < counterScalePair.fine.normalizedMass collarState := by
  unfold SlabPhysicalData.normalizedMass
  exact Q'.divPos_pos _ _
    (slabParametricKPhysicalPartition_pos
      counterScalePair.fine.coupling_nonnegative
      counterScalePair.fine.cutoff
      counterScalePair.fine.extent)
    collarState_physicalTerm_pos

theorem collarState_positiveIncoherentRecouplingRowWeight_pos :
    (0 : Q') <
      positiveIncoherentRecouplingRowWeight
        counterScalePair collarState := by
  unfold positiveIncoherentRecouplingRowWeight
  rw [if_pos collarState_physicalTerm_pos]
  rw [if_neg collarState_wholeSlabRawRowPartition_not_pos]
  exact collarState_normalizedMass_pos

private theorem listQSum_member_le_nonnegative
    {A : Type} (value : A -> Q')
    (hvalue : ∀ item, (0 : Q') <= value item) :
    ∀ (items : List A) {selected : A},
      selected ∈ items -> value selected <= listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, selected, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst selected
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on value tail
            (fun item _ => hvalue item))
      · have ih := listQSum_member_le_nonnegative
          value hvalue tail htail
        have htailLe : listQSum value tail <=
            value head + listQSum value tail := by
          have hadd := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hadd
        exact Q'.le_trans' _ _ _ ih htailLe

/-- The bad row has positive normalized probability, so the full fallback
sector is genuinely nonempty in measure, not only in support. -/
theorem counter_positiveIncoherentRecouplingMass_pos :
    (0 : Q') < positiveIncoherentRecouplingMass counterScalePair := by
  unfold positiveIncoherentRecouplingMass
  exact Q'.pos_of_lt_of_le
    collarState_positiveIncoherentRecouplingRowWeight_pos
    (listQSum_member_le_nonnegative
      (positiveIncoherentRecouplingRowWeight counterScalePair)
      (positiveIncoherentRecouplingRowWeight_nonnegative counterScalePair)
      counterScalePair.fine.physicalLabellings collarState_mem)

/-- The total kernel really does use its null completion on the positive
collar row. -/
theorem counter_allCutoffWholeSlabKernel_eq_null
    (target : EdgeLabelling) :
    allCutoffWholeSlabKernel counterScalePair collarState target =
      nullCompletionKernel counterScalePair collarState target := by
  exact allCutoffWholeSlabKernel_eq_null_of_raw_partition_not_positive
    counterScalePair collarState_mem collarState_physicalTerm_pos
      collarState_wholeSlabRawRowPartition_not_pos target

/-- The exact `L1` distance from the coherent four-preimage pushforward is
strictly positive on the explicit cutoff-two SU(2) datum. -/
theorem counter_coherenceFallbackL1_pos :
    (0 : Q') < coherenceFallbackL1 counterScalePair (by decide) := by
  exact Q'.pos_of_lt_of_le
    counter_positiveIncoherentRecouplingMass_pos
    (Q'.ge_of_eqv
      (coherenceFallbackL1_eqv_positiveIncoherentRecouplingMass
        counterScalePair (by decide)))

/-! ## Axiom audit -/

#print axioms collarState_wholeSlabRawRowPartition_not_pos
#print axioms collarState_normalizedMass_pos
#print axioms collarState_positiveIncoherentRecouplingRowWeight_pos
#print axioms counter_positiveIncoherentRecouplingMass_pos
#print axioms counter_allCutoffWholeSlabKernel_eq_null
#print axioms counter_coherenceFallbackL1_pos

end
  YMGap.Continuum.CompactDualAllCutoffPhysicalPushforwardCounterexample
