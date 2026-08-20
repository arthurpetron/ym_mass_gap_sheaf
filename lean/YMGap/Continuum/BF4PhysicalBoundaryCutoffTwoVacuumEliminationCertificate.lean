/-
# Complete exact cutoff-two vacuum-column elimination certificate

This module composes the independently checked sparse elimination steps and
checks the terminal empty-scope scalar against the exact rational emitted by
the external certificate producer.  The producer is not trusted: every local
table equation and the final scalar reduction are checked by Lean.

This remains one finite cutoff and one finite volume.  It makes no
cutoff-uniform, volume-uniform, or continuum claim.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationPrefix
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardE
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardF

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardA
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationPrefix
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardE
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardF
open YMGap.Continuum.FiniteScopedFactorTableCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Composition of all six shards from the named initial factor alias. -/
theorem factors0_partitionSum_eqv_expected :
    YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep.scopedFactorPartitionSum
        2 cutoffTwoVacuumEliminationFaceOrder factors0 ≈
      cutoffTwoVacuumExpectedScalar := by
  exact Q'.eqv_trans _ _ _ prefix_partitionSum_eqv
    (Q'.eqv_trans _ _ _
      shardE_partitionSum_eqv shardF_partitionSum_eqv_expected)

/-- Kernel-checked exact value of the complete 72-factor cutoff-two graph. -/
theorem cutoffTwoVacuumFactorGraphPartitionSum_eqv_expected :
    YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep.scopedFactorPartitionSum
        2 cutoffTwoVacuumEliminationFaceOrder
        cutoffTwoVacuumInitialFactors ≈
      cutoffTwoVacuumExpectedScalar := by
  simpa only [factors0] using factors0_partitionSum_eqv_expected

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationCertificate.factors0_partitionSum_eqv_expected
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationCertificate.cutoffTwoVacuumFactorGraphPartitionSum_eqv_expected
