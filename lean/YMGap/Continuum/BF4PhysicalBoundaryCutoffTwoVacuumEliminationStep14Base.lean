/- Shared executable definitions for cutoff-two elimination step 14. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardD

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

local infix:50 " ≈ " => Q'.eqv

def step14Result : ScopedQFactor := (cutoffTwoVacuumEliminationDatum 14).factor 2
def step14Bucket : List ScopedQFactor := factorBucket 19 factors14

def step14Predicate
    (labelling : YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) : Bool :=
  decide (step14Result.value labelling ≈
    eliminatedBucketValue 2 19 step14Bucket labelling)

def step14Assignments : List
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling :=
  boundedEdgeLabellings 2 step14Result.scope

def step14ChunkSize : Nat := 729

def step14Tail : Nat → List
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling
  | 0 => step14Assignments
  | index + 1 => (step14Tail index).drop step14ChunkSize

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

