/- Shared executable definitions for cutoff-two elimination step 12. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

local infix:50 " ≈ " => Q'.eqv

def step12Result : ScopedQFactor :=
  (cutoffTwoVacuumEliminationDatum 12).factor 2

def step12Bucket : List ScopedQFactor := factorBucket 27 factors12

def step12Predicate
    (labelling :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) : Bool :=
  decide (step12Result.value labelling ≈
    eliminatedBucketValue 2 27 step12Bucket labelling)

def step12Assignments : List
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling :=
  boundedEdgeLabellings 2 step12Result.scope

def step12ChunkSize : Nat := 729

def step12Tail : Nat → List
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling
  | 0 => step12Assignments
  | index + 1 => (step12Tail index).drop step12ChunkSize

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12

