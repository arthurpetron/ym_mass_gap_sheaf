/-
# Complete checked state-link transport for the first axis swap

All 65 state-dependent 48-factor certificates are assembled here.  The
fundamental cube uses its dedicated theorem; the 64 doubled subsets come from
the independently compiled shards.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard08
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard10
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard11
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapAllStateTransport

set_option maxRecDepth 500000
set_option maxHeartbeats 500000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCommonFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCubeSourceFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

theorem axisSwap01AllStateLinkTransport : ∀ sourceIndex : Fin 65,
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors sourceIndex)
      (axisSwap01StateMatchedTargetFactors
        (axisSwap01SectorTargetIndex sourceIndex)) := by
  intro sourceIndex
  by_cases hzero : sourceIndex = 0
  · subst sourceIndex
    change FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01CubeSourceFactors
      axisSwap01MatchedCubeSourceFactors
    exact axisSwap01CubeSourceFactorListTransport
  by_cases h05 : sourceIndex.val ≤ 5
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
    change axisSwap01StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard00.axisSwap01Shard00AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard00.axisSwap01Shard00Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h10 : sourceIndex.val ≤ 10
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
    change axisSwap01StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard01.axisSwap01Shard01AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard01.axisSwap01Shard01Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h15 : sourceIndex.val ≤ 15
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
    change axisSwap01StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard02.axisSwap01Shard02AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard02.axisSwap01Shard02Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h20 : sourceIndex.val ≤ 20
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
    change axisSwap01StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03.axisSwap01Shard03AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03.axisSwap01Shard03Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h25 : sourceIndex.val ≤ 25
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
    change axisSwap01StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04.axisSwap01Shard04AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04.axisSwap01Shard04Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h30 : sourceIndex.val ≤ 30
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
    change axisSwap01StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard05.axisSwap01Shard05AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard05.axisSwap01Shard05Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h35 : sourceIndex.val ≤ 35
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
    change axisSwap01StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06.axisSwap01Shard06AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06.axisSwap01Shard06Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h40 : sourceIndex.val ≤ 40
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
    change axisSwap01StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard07.axisSwap01Shard07AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard07.axisSwap01Shard07Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h45 : sourceIndex.val ≤ 45
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
    change axisSwap01StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard08.axisSwap01Shard08AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard08.axisSwap01Shard08Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h50 : sourceIndex.val ≤ 50
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
    change axisSwap01StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09.axisSwap01Shard09AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09.axisSwap01Shard09Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h55 : sourceIndex.val ≤ 55
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
    change axisSwap01StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard10.axisSwap01Shard10AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard10.axisSwap01Shard10Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h60 : sourceIndex.val ≤ 60
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
    change axisSwap01StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard11.axisSwap01Shard11AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard11.axisSwap01Shard11Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  · apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
    change axisSwap01StateLinkTransportCheckAt sourceIndex = true
    exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12.axisSwap01Shard12AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12.axisSwap01Shard12Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapAllStateTransport

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapAllStateTransport.axisSwap01AllStateLinkTransport
