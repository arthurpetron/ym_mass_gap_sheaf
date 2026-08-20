/-
# Interface-partition invariance under the first spatial-axis swap

The already checked common-factor and all-state source-factor transports are
assembled here and lifted through the finite coordinate change-of-variables
theorem.  The result holds for an arbitrary pair of the 65 cutoff-two sector
states; no interface contraction is recomputed in this module.

This is a finite cutoff-two theorem only.  It supplies one generator for the
cube-symmetry quotient and makes no uniform-cutoff or continuum claim.
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

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapInterfaceInvariance

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCommonFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCubeSourceFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.FiniteScopedFactorCoordinateReindex
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

def axisSwap01PairSourceFactors
    (left right : Fin 65) : List ScopedQFactor :=
  cutoffTwoSectorCommonFactors ++
    (axisSwap01StateSourceFactors left ++
      axisSwap01StateSourceFactors right)

def axisSwap01PairTargetFactors
    (left right : Fin 65) : List ScopedQFactor :=
  cutoffTwoSectorCommonFactors ++
    (axisSwap01StateSourceFactors
        (axisSwap01SectorTargetIndex left) ++
      axisSwap01StateSourceFactors
        (axisSwap01SectorTargetIndex right))

theorem axisSwap01BoundaryRename_involutive (id : Nat) :
    axisSwap01BoundaryRename (axisSwap01BoundaryRename id) = id := by
  simp [axisSwap01BoundaryRename]

theorem axisSwap01BoundaryRename_injective :
    InjectiveOnCoordinates (centralFixedFaceIds 0)
      axisSwap01BoundaryRename := by
  intro left _ right _ heq
  calc
    left = axisSwap01BoundaryRename (axisSwap01BoundaryRename left) :=
      (axisSwap01BoundaryRename_involutive left).symm
    _ = axisSwap01BoundaryRename (axisSwap01BoundaryRename right) :=
      congrArg axisSwap01BoundaryRename heq
    _ = right := axisSwap01BoundaryRename_involutive right

theorem axisSwap01BoundaryCarrier_perm :
    ((centralFixedFaceIds 0).map axisSwap01BoundaryRename).Perm
      (centralFixedFaceIds 0) := by
  apply natListPerm_of_check
  decide

private theorem q_mul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem listQProduct_append_local
    {Item : Type} (value : Item → Q') : ∀ left right,
    listQProduct value (left ++ right) ≈
      listQProduct value left * listQProduct value right
  | [], right => Q'.eqv_symm (Q'.one_mul_eqv _)
  | head :: tail, right => by
      simp only [List.cons_append, listQProduct]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (listQProduct_append_local value tail right))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

/-- Consume a checked list transport without exposing its recursively
constructed proof at the concrete call site. -/
private theorem scopedFactorProduct_eqv_of_check_perm
    {K : Nat} {coordinates : List Nat} {rename inverse : Nat → Nat}
    {sourceFactors matchedTargetFactors targetFactors : List ScopedQFactor}
    (hcheck : factorListTransportCheck K coordinates rename inverse
      sourceFactors matchedTargetFactors = true)
    (hperm : matchedTargetFactors.Perm targetFactors)
    (source target : EdgeLabelling)
    (hagree : LabellingsAgreeUnder coordinates rename source target)
    (hbounded : ∀ id, id ∈ coordinates → source id < K + 1) :
    scopedFactorProduct sourceFactors source ≈
      scopedFactorProduct targetFactors target := by
  exact scopedFactorProduct_eqv_of_listTransport_perm
    (factorListTransport_of_check K coordinates rename inverse
      sourceFactors matchedTargetFactors hcheck)
    hperm source target hagree hbounded

theorem axisSwap01NonzeroStateLinkTransportCheck
    (sourceIndex : Fin 65) (hzero : sourceIndex ≠ 0) :
    axisSwap01StateLinkTransportCheckAt sourceIndex = true := by
  by_cases h05 : sourceIndex.val ≤ 5
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard00.axisSwap01Shard00AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard00.axisSwap01Shard00Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h10 : sourceIndex.val ≤ 10
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard01.axisSwap01Shard01AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard01.axisSwap01Shard01Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h15 : sourceIndex.val ≤ 15
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard02.axisSwap01Shard02AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard02.axisSwap01Shard02Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h20 : sourceIndex.val ≤ 20
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03.axisSwap01Shard03AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03.axisSwap01Shard03Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h25 : sourceIndex.val ≤ 25
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04.axisSwap01Shard04AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04.axisSwap01Shard04Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h30 : sourceIndex.val ≤ 30
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard05.axisSwap01Shard05AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard05.axisSwap01Shard05Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h35 : sourceIndex.val ≤ 35
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06.axisSwap01Shard06AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06.axisSwap01Shard06Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h40 : sourceIndex.val ≤ 40
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard07.axisSwap01Shard07AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard07.axisSwap01Shard07Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h45 : sourceIndex.val ≤ 45
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard08.axisSwap01Shard08AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard08.axisSwap01Shard08Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h50 : sourceIndex.val ≤ 50
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09.axisSwap01Shard09AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09.axisSwap01Shard09Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h55 : sourceIndex.val ≤ 55
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard10.axisSwap01Shard10AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard10.axisSwap01Shard10Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h60 : sourceIndex.val ≤ 60
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard11.axisSwap01Shard11AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard11.axisSwap01Shard11Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12.axisSwap01Shard12AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12.axisSwap01Shard12Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)

theorem axisSwap01StateProduct_eqv
    (sourceIndex : Fin 65)
    (source target : EdgeLabelling)
    (hagree : LabellingsAgreeUnder (centralFixedFaceIds 0)
      axisSwap01BoundaryRename source target)
    (hbounded : ∀ id, id ∈ centralFixedFaceIds 0 → source id < 3) :
    scopedFactorProduct (axisSwap01StateSourceFactors sourceIndex) source ≈
      scopedFactorProduct
        (axisSwap01StateSourceFactors
          (axisSwap01SectorTargetIndex sourceIndex)) target := by
  by_cases hzero : sourceIndex = 0
  · subst sourceIndex
    change scopedFactorProduct axisSwap01CubeSourceFactors source ≈
      scopedFactorProduct axisSwap01CubeSourceFactors target
    exact axisSwap01CubeSourceProduct_eqv source target hagree hbounded
  · exact scopedFactorProduct_eqv_of_check_perm
      (axisSwap01NonzeroStateLinkTransportCheck sourceIndex hzero)
      (axisSwap01StateMatchedTargetFactors_perm
        (axisSwap01SectorTargetIndex sourceIndex))
      source target hagree hbounded

theorem axisSwap01PairProduct_eqv
    (left right : Fin 65)
    (source target : EdgeLabelling)
    (hagree : LabellingsAgreeUnder (centralFixedFaceIds 0)
      axisSwap01BoundaryRename source target)
    (hbounded : ∀ id, id ∈ centralFixedFaceIds 0 → source id < 3) :
    scopedFactorProduct (axisSwap01PairSourceFactors left right) source ≈
      scopedFactorProduct (axisSwap01PairTargetFactors left right) target := by
  exact Q'.eqv_trans _ _ _
    (listQProduct_append_local
      (fun factor : ScopedQFactor => factor.value source)
      cutoffTwoSectorCommonFactors
      (axisSwap01StateSourceFactors left ++
        axisSwap01StateSourceFactors right))
    (Q'.eqv_trans _ _ _
      (q_mul_congr
        (axisSwap01CommonProduct_eqv source target hagree hbounded)
        (Q'.eqv_trans _ _ _
          (listQProduct_append_local
            (fun factor : ScopedQFactor => factor.value source)
            (axisSwap01StateSourceFactors left)
            (axisSwap01StateSourceFactors right))
          (Q'.eqv_trans _ _ _
            (q_mul_congr
              (axisSwap01StateProduct_eqv left
                source target hagree hbounded)
              (axisSwap01StateProduct_eqv right
                source target hagree hbounded))
            (Q'.eqv_symm
              (listQProduct_append_local
                (fun factor : ScopedQFactor => factor.value target)
                (axisSwap01StateSourceFactors
                  (axisSwap01SectorTargetIndex left))
                (axisSwap01StateSourceFactors
                  (axisSwap01SectorTargetIndex right)))))))
      (Q'.eqv_symm
        (listQProduct_append_local
          (fun factor : ScopedQFactor => factor.value target)
          cutoffTwoSectorCommonFactors
          (axisSwap01StateSourceFactors
              (axisSwap01SectorTargetIndex left) ++
            axisSwap01StateSourceFactors
              (axisSwap01SectorTargetIndex right)))))

theorem axisSwap01PairPartitionSum_eqv
    (left right : Fin 65) :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (axisSwap01PairSourceFactors left right) ≈
      scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (axisSwap01PairTargetFactors left right) := by
  exact scopedFactorPartitionSum_coordinate_reindex
    2 (centralFixedFaceIds 0) (centralFixedFaceIds 0)
    axisSwap01BoundaryRename
    (axisSwap01PairSourceFactors left right)
    (axisSwap01PairTargetFactors left right)
    (by decide)
    axisSwap01BoundaryRename_injective
    axisSwap01BoundaryCarrier_perm
    (axisSwap01PairProduct_eqv left right)

theorem cutoffTwoSectorPairInterface_axisSwap01_eqv
    (left right : Fin 65) :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors
          (cutoffTwoSectorStateAt left)
          (cutoffTwoSectorStateAt right)) ≈
      scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors
          (cutoffTwoSectorStateAt (axisSwap01SectorTargetIndex left))
          (cutoffTwoSectorStateAt
            (axisSwap01SectorTargetIndex right))) := by
  simpa [axisSwap01PairSourceFactors, axisSwap01PairTargetFactors,
    cutoffTwoSectorCommonFactors, axisSwap01StateSourceFactors,
    cutoffTwoSectorPairInterfaceFactors, List.append_assoc] using
      axisSwap01PairPartitionSum_eqv left right

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapInterfaceInvariance

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapInterfaceInvariance.cutoffTwoSectorPairInterface_axisSwap01_eqv
