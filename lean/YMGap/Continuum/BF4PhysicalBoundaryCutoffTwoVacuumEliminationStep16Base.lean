/- Shared executable definitions for cutoff-two elimination step 16. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep16

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

local infix:50 " ≈ " => Q'.eqv

def step16Result : ScopedQFactor :=
  (cutoffTwoVacuumEliminationDatum 16).factor 2

def step16Bucket : List ScopedQFactor := factorBucket 55 factors16

def step16Predicate
    (labelling :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) : Bool :=
  decide (step16Result.value labelling ≈
    eliminatedBucketValue 2 55 step16Bucket labelling)

def step16Assignments : List
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling :=
  boundedEdgeLabellings 2 step16Result.scope

def step16ChunkSize : Nat := 729

def step16Tail : Nat → List
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling
  | 0 => step16Assignments
  | index + 1 => (step16Tail index).drop step16ChunkSize

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep16
