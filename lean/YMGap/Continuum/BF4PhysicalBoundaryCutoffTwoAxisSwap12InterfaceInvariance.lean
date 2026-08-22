/-
# Interface-partition invariance under the second spatial-axis swap

The already checked common-factor and all-state source-factor transports are
assembled here and lifted through the finite coordinate change-of-variables
theorem.  The result holds for an arbitrary pair of the 65 cutoff-two sector
states; no interface contraction is recomputed in this module.

This is a finite cutoff-two theorem only.  It supplies one generator for the
cube-symmetry quotient and makes no uniform-cutoff or continuum claim.
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

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12InterfaceInvariance

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CommonFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CubeSourceFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.FiniteScopedFactorCoordinateReindex
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

def axisSwap12PairSourceFactors
    (left right : Fin 65) : List ScopedQFactor :=
  cutoffTwoSectorCommonFactors ++
    (axisSwap12StateSourceFactors left ++
      axisSwap12StateSourceFactors right)

def axisSwap12PairTargetFactors
    (left right : Fin 65) : List ScopedQFactor :=
  cutoffTwoSectorCommonFactors ++
    (axisSwap12StateSourceFactors
        (axisSwap12SectorTargetIndex left) ++
      axisSwap12StateSourceFactors
        (axisSwap12SectorTargetIndex right))

theorem axisSwap12BoundaryRename_involutive (id : Nat) :
    axisSwap12BoundaryRename (axisSwap12BoundaryRename id) = id := by
  by_cases h4 : id = 4
  · subst id
    rfl
  by_cases h5 : id = 5
  · subst id
    rfl
  by_cases h11 : id = 11
  · subst id
    rfl
  by_cases h13 : id = 13
  · subst id
    rfl
  by_cases h14 : id = 14
  · subst id
    rfl
  by_cases h20 : id = 20
  · subst id
    rfl
  by_cases h22 : id = 22
  · subst id
    rfl
  by_cases h23 : id = 23
  · subst id
    rfl
  by_cases h40 : id = 40
  · subst id
    rfl
  by_cases h41 : id = 41
  · subst id
    rfl
  by_cases h47 : id = 47
  · subst id
    rfl
  by_cases h49 : id = 49
  · subst id
    rfl
  by_cases h50 : id = 50
  · subst id
    rfl
  by_cases h56 : id = 56
  · subst id
    rfl
  by_cases h58 : id = 58
  · subst id
    rfl
  by_cases h59 : id = 59
  · subst id
    rfl
  · simp [axisSwap12BoundaryRename]

theorem axisSwap12BoundaryRename_injective :
    InjectiveOnCoordinates (centralFixedFaceIds 0)
      axisSwap12BoundaryRename := by
  intro left _ right _ heq
  calc
    left = axisSwap12BoundaryRename (axisSwap12BoundaryRename left) :=
      (axisSwap12BoundaryRename_involutive left).symm
    _ = axisSwap12BoundaryRename (axisSwap12BoundaryRename right) :=
      congrArg axisSwap12BoundaryRename heq
    _ = right := axisSwap12BoundaryRename_involutive right

theorem axisSwap12BoundaryCarrier_perm :
    ((centralFixedFaceIds 0).map axisSwap12BoundaryRename).Perm
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

theorem axisSwap12NonzeroStateLinkTransportCheck
    (sourceIndex : Fin 65) (hzero : sourceIndex ≠ 0) :
    axisSwap12StateLinkTransportCheckAt sourceIndex = true := by
  by_cases h05 : sourceIndex.val ≤ 5
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard00.axisSwap12Shard00AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard00.axisSwap12Shard00Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h10 : sourceIndex.val ≤ 10
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard01.axisSwap12Shard01AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard01.axisSwap12Shard01Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h15 : sourceIndex.val ≤ 15
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard02.axisSwap12Shard02AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard02.axisSwap12Shard02Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h20 : sourceIndex.val ≤ 20
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard03.axisSwap12Shard03AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard03.axisSwap12Shard03Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h25 : sourceIndex.val ≤ 25
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard04.axisSwap12Shard04AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard04.axisSwap12Shard04Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h30 : sourceIndex.val ≤ 30
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard05.axisSwap12Shard05AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard05.axisSwap12Shard05Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h35 : sourceIndex.val ≤ 35
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard06.axisSwap12Shard06AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard06.axisSwap12Shard06Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h40 : sourceIndex.val ≤ 40
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard07.axisSwap12Shard07AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard07.axisSwap12Shard07Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h45 : sourceIndex.val ≤ 45
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard08.axisSwap12Shard08AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard08.axisSwap12Shard08Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h50 : sourceIndex.val ≤ 50
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard09.axisSwap12Shard09AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard09.axisSwap12Shard09Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h55 : sourceIndex.val ≤ 55
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard10.axisSwap12Shard10AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard10.axisSwap12Shard10Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  by_cases h60 : sourceIndex.val ≤ 60
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard11.axisSwap12Shard11AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard11.axisSwap12Shard11Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)
  · exact List.all_eq_true.mp
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard12.axisSwap12Shard12AllChecked
      sourceIndex (by
        unfold YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard12.axisSwap12Shard12Indices
        simp only [List.mem_cons, List.mem_singleton]
        omega)

theorem axisSwap12StateProduct_eqv
    (sourceIndex : Fin 65)
    (source target : EdgeLabelling)
    (hagree : LabellingsAgreeUnder (centralFixedFaceIds 0)
      axisSwap12BoundaryRename source target)
    (hbounded : ∀ id, id ∈ centralFixedFaceIds 0 → source id < 3) :
    scopedFactorProduct (axisSwap12StateSourceFactors sourceIndex) source ≈
      scopedFactorProduct
        (axisSwap12StateSourceFactors
          (axisSwap12SectorTargetIndex sourceIndex)) target := by
  by_cases hzero : sourceIndex = 0
  · subst sourceIndex
    change scopedFactorProduct axisSwap12CubeSourceFactors source ≈
      scopedFactorProduct axisSwap12CubeSourceFactors target
    exact axisSwap12CubeSourceProduct_eqv source target hagree hbounded
  · exact scopedFactorProduct_eqv_of_check_perm
      (axisSwap12NonzeroStateLinkTransportCheck sourceIndex hzero)
      (axisSwap12StateMatchedTargetFactors_perm
        (axisSwap12SectorTargetIndex sourceIndex))
      source target hagree hbounded

theorem axisSwap12PairProduct_eqv
    (left right : Fin 65)
    (source target : EdgeLabelling)
    (hagree : LabellingsAgreeUnder (centralFixedFaceIds 0)
      axisSwap12BoundaryRename source target)
    (hbounded : ∀ id, id ∈ centralFixedFaceIds 0 → source id < 3) :
    scopedFactorProduct (axisSwap12PairSourceFactors left right) source ≈
      scopedFactorProduct (axisSwap12PairTargetFactors left right) target := by
  exact Q'.eqv_trans _ _ _
    (listQProduct_append_local
      (fun factor : ScopedQFactor => factor.value source)
      cutoffTwoSectorCommonFactors
      (axisSwap12StateSourceFactors left ++
        axisSwap12StateSourceFactors right))
    (Q'.eqv_trans _ _ _
      (q_mul_congr
        (axisSwap12CommonProduct_eqv source target hagree hbounded)
        (Q'.eqv_trans _ _ _
          (listQProduct_append_local
            (fun factor : ScopedQFactor => factor.value source)
            (axisSwap12StateSourceFactors left)
            (axisSwap12StateSourceFactors right))
          (Q'.eqv_trans _ _ _
            (q_mul_congr
              (axisSwap12StateProduct_eqv left
                source target hagree hbounded)
              (axisSwap12StateProduct_eqv right
                source target hagree hbounded))
            (Q'.eqv_symm
              (listQProduct_append_local
                (fun factor : ScopedQFactor => factor.value target)
                (axisSwap12StateSourceFactors
                  (axisSwap12SectorTargetIndex left))
                (axisSwap12StateSourceFactors
                  (axisSwap12SectorTargetIndex right)))))))
      (Q'.eqv_symm
        (listQProduct_append_local
          (fun factor : ScopedQFactor => factor.value target)
          cutoffTwoSectorCommonFactors
          (axisSwap12StateSourceFactors
              (axisSwap12SectorTargetIndex left) ++
            axisSwap12StateSourceFactors
              (axisSwap12SectorTargetIndex right)))))

theorem axisSwap12PairPartitionSum_eqv
    (left right : Fin 65) :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (axisSwap12PairSourceFactors left right) ≈
      scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (axisSwap12PairTargetFactors left right) := by
  exact scopedFactorPartitionSum_coordinate_reindex
    2 (centralFixedFaceIds 0) (centralFixedFaceIds 0)
    axisSwap12BoundaryRename
    (axisSwap12PairSourceFactors left right)
    (axisSwap12PairTargetFactors left right)
    (by decide)
    axisSwap12BoundaryRename_injective
    axisSwap12BoundaryCarrier_perm
    (axisSwap12PairProduct_eqv left right)

theorem cutoffTwoSectorPairInterface_axisSwap12_eqv
    (left right : Fin 65) :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors
          (cutoffTwoSectorStateAt left)
          (cutoffTwoSectorStateAt right)) ≈
      scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors
          (cutoffTwoSectorStateAt (axisSwap12SectorTargetIndex left))
          (cutoffTwoSectorStateAt
            (axisSwap12SectorTargetIndex right))) := by
  simpa [axisSwap12PairSourceFactors, axisSwap12PairTargetFactors,
    cutoffTwoSectorCommonFactors, axisSwap12StateSourceFactors,
    cutoffTwoSectorPairInterfaceFactors, List.append_assoc] using
      axisSwap12PairPartitionSum_eqv left right

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12InterfaceInvariance

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12InterfaceInvariance.cutoffTwoSectorPairInterface_axisSwap12_eqv
