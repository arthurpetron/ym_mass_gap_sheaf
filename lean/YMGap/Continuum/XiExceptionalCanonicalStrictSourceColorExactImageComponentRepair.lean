/-
# Component repair of the exact-image cross conflict

The four-occurrence exact-image fence defeats the path-local router because
its unsafe-left and right residual occurrences conflict after both are put in
the external slot.  It does not defeat the residual-component router.  The
right residual of that same source is entirely path-safe, which is the exact
branch invariant used by component switching.

This module links the reconstructed fence entry to that existing mechanism.
The component carrier is a genuine member of the unchanged occurrence target,
has exactly the source weight for every coupling and label, and therefore
allocates the single incompatible source term into
`connectingChainMajorant * XiR`.  Thus the explicit cross-side conflict needs
component rewiring, not a longer endpoint-return ear.
-/

import YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorExactImagePathSafeFence
import YMGap.Continuum.XiExceptionalComponentSummation

namespace YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorExactImageComponentRepair

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalComponentCarrier
open YMGap.Continuum.XiExceptionalComponentExactWeight
open YMGap.Continuum.XiExceptionalComponentSummation
open YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorExactImagePathSafeFence
open YMGap.Continuum.XiExceptionalCrossDetourRightPivotFence

local infix:50 " ≈ " => Q'.eqv

/-! ## The stronger branch invariant holds on the exact fence -/

theorem cross_componentRightSafe :
    componentRightSafe _ _ _ _ entry := by
  simpa [componentRightSafe,
    YMGap.Continuum.XiExceptionalRoutedExternalSplit.routedRightResidual]
    using every_right_residual_occurrence_path_safe

theorem cross_componentCarrier_mem :
    exceptionalComponentCarrierCode _ _ _ _ entry ∈
      occurrenceCarrierXiCodes _ := by
  exact exceptionalComponentCarrierCode_mem _ _ _ _ entry

/-! ## A repaired certificate extending the reconstructed failure -/

structure ExactImageComponentRepair where
  fence : ExactImagePathSafeCounterexample
  componentRightSafe :
    @componentRightSafe fence.L fence.inst fence.Gamma
      fence.qP fence.b1 fence.b2 fence.entry

def crossRepair : ExactImageComponentRepair :=
  { fence := crossDetourExactImagePathSafeCounterexample
    componentRightSafe := cross_componentRightSafe }

theorem exact_image_pathSafe_failure_has_component_repair :
    Nonempty ExactImageComponentRepair :=
  ⟨crossRepair⟩

def repairedComponentCode (repair : ExactImageComponentRepair) :
    @OccCarrierXiCodeAt repair.fence.L repair.fence.Gamma :=
  @exceptionalComponentCarrierCode repair.fence.L repair.fence.inst
    repair.fence.Gamma repair.fence.qP repair.fence.b1 repair.fence.b2
    repair.fence.entry

theorem repairedComponentCode_mem (repair : ExactImageComponentRepair) :
    repairedComponentCode repair ∈
      @occurrenceCarrierXiCodes repair.fence.L repair.fence.Gamma := by
  exact @exceptionalComponentCarrierCode_mem
    repair.fence.L repair.fence.inst repair.fence.Gamma
    repair.fence.qP repair.fence.b1 repair.fence.b2 repair.fence.entry

/-! ## Exact weight and accepted-budget payment -/

theorem repairedComponentCode_weight_eqv_source
    (repair : ExactImageComponentRepair) (w : Q')
    (label : repair.fence.L.Plaquette → Rep) :
    @occurrenceCarrierXiCodeWeight repair.fence.L repair.fence.inst
        w repair.fence.qP repair.fence.b1 repair.fence.b2
        repair.fence.Gamma label (repairedComponentCode repair) ≈
      @occurrencePairWeight repair.fence.L repair.fence.inst
        w repair.fence.qP repair.fence.b1 repair.fence.b2
        repair.fence.Gamma label repair.fence.entry.1 := by
  exact @exceptionalComponentCarrierCode_weight_eqv_source
    repair.fence.L repair.fence.inst w repair.fence.qP repair.fence.b1
    repair.fence.b2 repair.fence.Gamma label repair.fence.entry
    repair.componentRightSafe

theorem repairedSourceTerm_le_targetSum
    (repair : ExactImageComponentRepair) {w : Q'} (hw : (0 : Q') ≤ w)
    (label : repair.fence.L.Plaquette → Rep) :
    @occurrencePairWeight repair.fence.L repair.fence.inst
        w repair.fence.qP repair.fence.b1 repair.fence.b2
        repair.fence.Gamma label repair.fence.entry.1 ≤
      qListSum
        (@occurrenceCarrierXiCodeWeight repair.fence.L repair.fence.inst
          w repair.fence.qP repair.fence.b1 repair.fence.b2
          repair.fence.Gamma label)
        (@occurrenceCarrierXiCodes repair.fence.L repair.fence.Gamma) := by
  have h := @componentRightSafe_region_global_bound
    repair.fence.L repair.fence.inst w hw repair.fence.Gamma
    repair.fence.qP repair.fence.b1 repair.fence.b2 label
    [repair.fence.entry] (by simp)
    (by
      intro other hother
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hother
      subst other
      exact repair.componentRightSafe)
  simp only [componentSourceWeight, qListSum_cons, qListSum_nil,
    Q'.add_zero'] at h
  exact h

theorem repairedSourceTerm_le_chain_mul_XiR
    (repair : ExactImageComponentRepair) {w : Q'} (hw : (0 : Q') ≤ w)
    (label : repair.fence.L.Plaquette → Rep) :
    @occurrencePairWeight repair.fence.L repair.fence.inst
        w repair.fence.qP repair.fence.b1 repair.fence.b2
        repair.fence.Gamma label repair.fence.entry.1 ≤
      @connectingChainMajorant repair.fence.L repair.fence.inst
          w repair.fence.qP repair.fence.b1 repair.fence.b2
          repair.fence.Gamma label *
        @XiR repair.fence.L repair.fence.inst
          w repair.fence.qP repair.fence.Gamma label := by
  exact Q'.le_trans' _ _ _
    (repairedSourceTerm_le_targetSum repair hw label)
    (Q'.le_of_eqv
      (@occurrenceCarrierXiCodes_sum_eqv_carrier_mul_XiR
        repair.fence.L repair.fence.inst w repair.fence.qP repair.fence.b1
        repair.fence.b2 repair.fence.Gamma label))

#print axioms cross_componentRightSafe
#print axioms cross_componentCarrier_mem
#print axioms crossRepair
#print axioms exact_image_pathSafe_failure_has_component_repair
#print axioms repairedComponentCode_mem
#print axioms repairedComponentCode_weight_eqv_source
#print axioms repairedSourceTerm_le_targetSum
#print axioms repairedSourceTerm_le_chain_mul_XiR

end YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorExactImageComponentRepair
