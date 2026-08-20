/-
# Terminal scalar lemmas for the cutoff-two vacuum-column trace

The final scalar is decomposed into small kernel checks so elaboration does
not compare the fully unfolded 24-step factor expression at once.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep23

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTerminal

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep22
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep23
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

theorem step23Result_zero_eqv_expected :
    step23Result.value
        YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling ≈
      cutoffTwoVacuumExpectedScalar := by
  decide

private theorem factorOutside_eq_nil_of_all_contains
    (coordinate : Nat) : ∀ factors : List ScopedQFactor,
    factors.all (fun factor => decide (coordinate ∈ factor.scope)) = true →
      factorOutside coordinate factors = []
  | [], _ => rfl
  | factor :: rest, hall => by
      have hparts :
          decide (coordinate ∈ factor.scope) = true ∧
            rest.all (fun item => decide (coordinate ∈ item.scope)) = true :=
        (Bool.and_eq_true _ _).mp hall
      have hmem : coordinate ∈ factor.scope :=
        of_decide_eq_true hparts.1
      simp only [factorOutside, List.filter_cons, hmem, decide_false,
        Bool.false_eq_true, ↓reduceIte]
      exact factorOutside_eq_nil_of_all_contains coordinate rest hparts.2

theorem factors23_all_contain_48 :
    factors23.all (fun factor => decide (48 ∈ factor.scope)) = true := by
  decide

theorem step23_outside_empty :
    factorOutside 48 factors23 = [] := by
  exact factorOutside_eq_nil_of_all_contains
    48 factors23 factors23_all_contain_48

theorem factors24_eq_singleton :
    factors24 = [step23Result] := by
  unfold factors24 CheckedScopedEliminationStep.afterFactors
  change step23Result :: factorOutside 48 factors23 = [step23Result]
  rw [step23_outside_empty]

theorem elimination_order_drop_24_empty :
    cutoffTwoVacuumEliminationFaceOrder.drop 24 = [] := by
  decide

theorem singleton_terminal_partitionSum_eqv_expected :
    scopedFactorPartitionSum 2 [] [step23Result] ≈
      cutoffTwoVacuumExpectedScalar := by
  decide

theorem terminal_partitionSum_eqv_expected :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 24) factors24 ≈
      cutoffTwoVacuumExpectedScalar := by
  rw [elimination_order_drop_24_empty, factors24_eq_singleton]
  exact singleton_terminal_partitionSum_eqv_expected

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTerminal

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTerminal.step23Result_zero_eqv_expected
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTerminal.factors23_all_contain_48
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTerminal.step23_outside_empty
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTerminal.factors24_eq_singleton
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTerminal.singleton_terminal_partitionSum_eqv_expected
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTerminal.terminal_partitionSum_eqv_expected
