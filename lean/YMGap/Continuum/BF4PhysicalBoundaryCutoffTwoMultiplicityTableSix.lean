/-
# Chunked kernel audit data for the cutoff-two arity-six table

This module defines the computed and literal lists.  Nine child modules
independently compare 81-entry slices; a final constructive certificate
composes those slice equalities.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableFive

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSix

set_option maxRecDepth 300000
set_option maxHeartbeats 10000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.CayleyPruferInjection

def cutoffTwoMultiplicityTableSixComputed : List Nat :=
  (allSeqs 3 6).map cutoffTwoActiveMultiplicity

def cutoffTwoMultiplicityTableSixLiteral : List Nat :=
  cutoffTwoExpectedMultiplicityTableSix

def cutoffTwoMultiplicityTableSixChunkSize : Nat := 81

def cutoffTwoMultiplicityTableSixComputedTail (index : Nat) : List Nat :=
  ((allSeqs 3 6).drop
    (index * cutoffTwoMultiplicityTableSixChunkSize)).map
      cutoffTwoActiveMultiplicity

def cutoffTwoMultiplicityTableSixLiteralTail (index : Nat) : List Nat :=
  cutoffTwoMultiplicityTableSixLiteral.drop
    (index * cutoffTwoMultiplicityTableSixChunkSize)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSix
