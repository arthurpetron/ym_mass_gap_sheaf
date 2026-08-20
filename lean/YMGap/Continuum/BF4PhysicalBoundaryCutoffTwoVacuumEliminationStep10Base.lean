/-
# Cutoff-two vacuum-column elimination, step-10 chunk base

Shared executable definitions for independent chunk modules.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardB

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardB
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

local infix:50 " ≈ " => Q'.eqv

def step10Result : ScopedQFactor :=
  (cutoffTwoVacuumEliminationDatum 10).factor 2

def step10Bucket : List ScopedQFactor := factorBucket 0 factors10

def step10Predicate
    (labelling :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) : Bool :=
  decide (step10Result.value labelling ≈
    eliminatedBucketValue 2 0 step10Bucket labelling)

def step10Assignments : List
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling :=
  boundedEdgeLabellings 2 step10Result.scope

def step10ChunkSize : Nat := 729

def step10Tail : Nat → List
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling
  | 0 => step10Assignments
  | index + 1 => (step10Tail index).drop step10ChunkSize

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10

