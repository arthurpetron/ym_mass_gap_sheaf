/- Shared executable definitions for the widest cutoff-two elimination step 13. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardC

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

local infix:50 " ≈ " => Q'.eqv

def step13Result : ScopedQFactor :=
  (cutoffTwoVacuumEliminationDatum 13).factor 2

def step13Bucket : List ScopedQFactor := factorBucket 21 factors13

def step13Predicate
    (labelling :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) : Bool :=
  decide (step13Result.value labelling ≈
    eliminatedBucketValue 2 21 step13Bucket labelling)

def step13Assignments : List
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling :=
  boundedEdgeLabellings 2 step13Result.scope

def step13ChunkSize : Nat := 729

def step13Tail : Nat → List
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling
  | 0 => step13Assignments
  | index + 1 => (step13Tail index).drop step13ChunkSize

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

