/-
# Complete checked state-link transport for the second adjacent axis swap

All 65 state-dependent 48-factor certificates are assembled here.  The
fundamental cube uses its dedicated theorem; the 64 doubled subsets come from
the independently compiled shards.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard08
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard09
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard10
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard11
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard12

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12AllStateTransport

set_option maxRecDepth 500000
set_option maxHeartbeats 500000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CommonFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CubeSourceFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

theorem axisSwap12AllStateLinkTransport : ∀ sourceIndex : Fin 65,
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename
      (axisSwap12StateSourceFactors sourceIndex)
      (axisSwap12StateMatchedTargetFactors
        (axisSwap12SectorTargetIndex sourceIndex)) := by
  intro sourceIndex
  by_cases hzero : sourceIndex = 0
  · subst sourceIndex
    change FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12CubeSourceFactors
      axisSwap12MatchedCubeSourceFactors
    exact axisSwap12CubeSourceFactorListTransport
  by_cases h05 : sourceIndex.val ≤ 5
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
    change axisSwap12StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard00.axisSwap12Shard00AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard00.axisSwap12Shard00Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h10 : sourceIndex.val ≤ 10
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
    change axisSwap12StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard01.axisSwap12Shard01AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard01.axisSwap12Shard01Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h15 : sourceIndex.val ≤ 15
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
    change axisSwap12StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard02.axisSwap12Shard02AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard02.axisSwap12Shard02Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h20 : sourceIndex.val ≤ 20
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
    change axisSwap12StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard03.axisSwap12Shard03AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard03.axisSwap12Shard03Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h25 : sourceIndex.val ≤ 25
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
    change axisSwap12StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard04.axisSwap12Shard04AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard04.axisSwap12Shard04Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h30 : sourceIndex.val ≤ 30
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
    change axisSwap12StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard05.axisSwap12Shard05AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard05.axisSwap12Shard05Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h35 : sourceIndex.val ≤ 35
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
    change axisSwap12StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard06.axisSwap12Shard06AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard06.axisSwap12Shard06Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h40 : sourceIndex.val ≤ 40
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
    change axisSwap12StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard07.axisSwap12Shard07AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard07.axisSwap12Shard07Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h45 : sourceIndex.val ≤ 45
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
    change axisSwap12StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard08.axisSwap12Shard08AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard08.axisSwap12Shard08Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h50 : sourceIndex.val ≤ 50
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
    change axisSwap12StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard09.axisSwap12Shard09AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard09.axisSwap12Shard09Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h55 : sourceIndex.val ≤ 55
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
    change axisSwap12StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard10.axisSwap12Shard10AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard10.axisSwap12Shard10Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h60 : sourceIndex.val ≤ 60
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
    change axisSwap12StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard11.axisSwap12Shard11AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard11.axisSwap12Shard11Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
    change axisSwap12StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard12.axisSwap12Shard12AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard12.axisSwap12Shard12Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12AllStateTransport

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12AllStateTransport.axisSwap12AllStateLinkTransport
