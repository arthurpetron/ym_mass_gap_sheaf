/- Shared executable definitions for cutoff-two elimination step 11. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

local infix:50 " ≈ " => Q'.eqv

def step11Result : ScopedQFactor :=
  (cutoffTwoVacuumEliminationDatum 11).factor 2

def step11Bucket : List ScopedQFactor := factorBucket 28 factors11

def step11Predicate
    (labelling :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) : Bool :=
  decide (step11Result.value labelling ≈
    eliminatedBucketValue 2 28 step11Bucket labelling)

def step11Assignments : List
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling :=
  boundedEdgeLabellings 2 step11Result.scope

def step11ChunkSize : Nat := 729

def step11Tail : Nat → List
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling
  | 0 => step11Assignments
  | index + 1 => (step11Tail index).drop step11ChunkSize

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11

