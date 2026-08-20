/- Shared executable definitions for cutoff-two elimination step 15. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

local infix:50 " ≈ " => Q'.eqv

def step15Result : ScopedQFactor :=
  (cutoffTwoVacuumEliminationDatum 15).factor 2

def step15Bucket : List ScopedQFactor := factorBucket 57 factors15

def step15Predicate
    (labelling :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) : Bool :=
  decide (step15Result.value labelling ≈
    eliminatedBucketValue 2 57 step15Bucket labelling)

def step15Assignments : List
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling :=
  boundedEdgeLabellings 2 step15Result.scope

def step15ChunkSize : Nat := 729

def step15Tail : Nat → List
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling
  | 0 => step15Assignments
  | index + 1 => (step15Tail index).drop step15ChunkSize

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15
