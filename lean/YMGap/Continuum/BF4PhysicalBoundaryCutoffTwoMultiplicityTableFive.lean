/-
# Kernel audit of the cutoff-two arity-five multiplicity table

The interface contraction uses a literal producer table for fast lookup.
This module recomputes all `3^5` entries from the production SU(2) fusion
definition and checks exact equality once.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableFive

set_option maxRecDepth 300000
set_option maxHeartbeats 30000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.CayleyPruferInjection

theorem cutoffTwoMultiplicityTableFive_checked :
    (allSeqs 3 5).map cutoffTwoActiveMultiplicity =
      cutoffTwoExpectedMultiplicityTableFive := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableFive

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableFive.cutoffTwoMultiplicityTableFive_checked
