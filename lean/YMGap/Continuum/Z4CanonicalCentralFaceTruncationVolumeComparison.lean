/-
# Receding-volume comparison for one central face truncation

Fix a truncation floor `m` and place its complete size-`<m` pinned chart in a
centered source box of radius `r >= m`.  Uniform padding from radius `r` to a
larger radius preserves that exact chart: the canonical-root shift is a
semigroup, and both root lists are the image of the same fixed size-`m`
source list.

For the finite probability comparison, choose the common pinned central face
as the marked start of every target root.  It lies in a protected core of
width `r-m`, independent of the component.  The existing uniform-shift
connected-carrier estimate then yields a volume error with explicit decay
`half^(r-m)` and no appeal to an arbitrary root-list head.
-/

import YMGap.Continuum.Z4CanonicalCentralFaceTruncationNesting
import YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

namespace YMGap.Continuum.Z4CanonicalCentralFaceTruncationVolumeComparison

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalCentralFaceFixedCylinder
open YMGap.Continuum.Z4CanonicalCentralFaceTruncationNesting
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalFaceEventCylinderCompiler
open YMGap.Continuum.Z4CanonicalFaceEventPinnedTail
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4ShiftedSubboxCarrierTail
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge
open YMGap.Continuum.Z4UniformShiftCylinderSwitchSummation
open YMGap.Continuum.Z4UniformShiftEmbeddedCylinder
open YMGap.Continuum.Z4UniformShiftEmbeddedRegion
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open YMGap.Continuum.Z4UniformShiftTargetCylinderStability
open YMGap.Continuum.SepLatticeZ4Linf
open Dir4

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The uniform-shift semigroup and the common chart -/

private theorem sameSupport_map_local
    {left right : List Z4Plaq} (reindex : Z4Plaq → Z4Plaq)
    (hsupport : sameSupport (L := z4Chain.toLattice) left right) :
    sameSupport (L := z4Chain.toLattice)
      (left.map reindex) (right.map reindex) := by
  constructor
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr
      ⟨source, hsupport.1 source hsource, rfl⟩
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr
      ⟨source, hsupport.2 source hsource, rfl⟩

private theorem sameSupport_right_eq_local
    {left right target : List Z4Plaq}
    (hsupport : sameSupport (L := z4Chain.toLattice) left right)
    (heq : right = target) :
    sameSupport (L := z4Chain.toLattice) left target := by
  cases heq
  exact hsupport

theorem uniformShiftCanonicalRoot_add_face
    {base : Nat} (first second : Nat) {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    uniformShiftCanonicalRoot second (uniformPaddedBase first base)
        (uniformShiftCanonicalRoot first base root) =
      uniformShiftCanonicalRoot (first + second) base root := by
  have hfirstCanonical := uniformShiftCanonicalRoot_canonical
    (padding := first) hroot
  have hleftCanonical := uniformShiftCanonicalRoot_canonical
    (padding := second) hfirstCanonical
  have hrightCanonical := uniformShiftCanonicalRoot_canonical
    (padding := first + second) hroot
  have hbaseEq :
      uniformPaddedBase second (uniformPaddedBase first base) =
        uniformPaddedBase (first + second) base := by
    unfold uniformPaddedBase
    omega
  rw [← hbaseEq] at hrightCanonical
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport
    hleftCanonical hrightCanonical
  have hsecondSupport := uniformShiftCanonicalRoot_sameSupport
    (padding := second) hfirstCanonical
  have hfirstSupport := uniformShiftCanonicalRoot_sameSupport
    (padding := first) hroot
  have hnested := sameSupport_trans hsecondSupport
    (sameSupport_map_local (uniformShiftPlaquette second) hfirstSupport)
  have hmapEq :
      ((geometricPolymer base root).map
          (uniformShiftPlaquette first)).map
          (uniformShiftPlaquette second) =
        (geometricPolymer base root).map
          (uniformShiftPlaquette (first + second)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro plaquette _
    simp only [Function.comp_apply]
    exact uniformShiftPlaquette_comp first second plaquette
  have hnestedCommon := sameSupport_right_eq_local hnested hmapEq
  have hdirect := uniformShiftCanonicalRoot_sameSupport
    (padding := first + second) hroot
  rw [← hbaseEq] at hdirect
  exact sameSupport_trans hnestedCommon (sameSupport_symm hdirect)

theorem mem_pinnedFaceCommonSmallRoots_iff
    {sizeFloor boxRadius : Nat} (hfloor : sizeFloor ≤ boxRadius)
    {root : List Nat} :
    root ∈ pinnedFaceCommonSmallRoots sizeFloor boxRadius ↔
      root ∈ canonicalSurfacePolymers
          (pinnedFaceSourceBase boxRadius) ∧
        pinnedFaceId boxRadius 0 ∈ root ∧
        root.length < sizeFloor := by
  unfold pinnedFaceCommonSmallRoots
  rw [mem_pinnedFaceStageRoots_iff]
  rw [pinnedFaceStageBase_floorPadding hfloor,
    pinnedFaceId_floorPadding hfloor]
  exact mem_canonicalPinnedBelowSizePolymers_iff

theorem pinnedFaceCommonSmallRoots_canonical
    {sizeFloor boxRadius : Nat} (hfloor : sizeFloor ≤ boxRadius) :
    ∀ root, root ∈ pinnedFaceCommonSmallRoots sizeFloor boxRadius →
      root ∈ canonicalSurfacePolymers
        (pinnedFaceSourceBase boxRadius) := by
  intro root hroot
  exact (mem_pinnedFaceCommonSmallRoots_iff hfloor).mp hroot |>.1

theorem pinnedFaceSourceBase_uniformPadding
    {earlierRadius laterRadius : Nat}
    (hradius : earlierRadius ≤ laterRadius) :
    uniformPaddedBase (laterRadius - earlierRadius)
        (pinnedFaceSourceBase earlierRadius) =
      pinnedFaceSourceBase laterRadius := by
  unfold uniformPaddedBase pinnedFaceSourceBase
  omega

/-- Exact semigroup transport of the size-truncated central chart. -/
theorem pinnedFaceCommonSmallRoots_uniformShift
    {sizeFloor earlierRadius laterRadius : Nat}
    (hfloor : sizeFloor ≤ earlierRadius)
    (hradius : earlierRadius ≤ laterRadius) :
    (pinnedFaceCommonSmallRoots sizeFloor earlierRadius).map
        (uniformShiftCanonicalRoot (laterRadius - earlierRadius)
          (pinnedFaceSourceBase earlierRadius)) =
      pinnedFaceCommonSmallRoots sizeFloor laterRadius := by
  unfold pinnedFaceCommonSmallRoots pinnedFaceStageRoots
    pinnedFaceFloorPadding
  rw [List.map_map]
  apply List.map_congr_left
  intro root hroot
  simp only [Function.comp_apply]
  have hcanonical :=
    (mem_canonicalPinnedBelowSizePolymers_iff.mp hroot).1
  have hbase : uniformPaddedBase (earlierRadius - sizeFloor)
      (pinnedFaceSourceBase sizeFloor) =
      pinnedFaceSourceBase earlierRadius :=
    pinnedFaceStageBase_floorPadding hfloor
  rw [← hbase]
  rw [uniformShiftCanonicalRoot_add_face
    (earlierRadius - sizeFloor) (laterRadius - earlierRadius) hcanonical]
  congr 2
  omega

theorem pinnedFaceCommonSmallEvent_uniformShift
    {sizeFloor earlierRadius laterRadius : Nat}
    (hfloor : sizeFloor ≤ earlierRadius)
    (hradius : earlierRadius ≤ laterRadius) :
    uniformShiftTargetCylinderEvent (laterRadius - earlierRadius)
        (pinnedFaceSourceBase earlierRadius)
        (pinnedFaceCommonSmallRoots sizeFloor earlierRadius)
        canonicalFaceCylinderPredicate =
      pinnedFaceCommonSmallEvent sizeFloor laterRadius := by
  unfold uniformShiftTargetCylinderEvent uniformShiftedCylinderRoots
    pinnedFaceCommonSmallEvent sourceCylinderEvent
  rw [pinnedFaceCommonSmallRoots_uniformShift hfloor hradius]

/-! ## 2. The pinned face supplies the growing protected core -/

theorem pinnedFaceCommonShiftedTarget_allPinned
    {sizeFloor earlierRadius laterRadius : Nat}
    (hfloor : sizeFloor ≤ earlierRadius)
    (hradius : earlierRadius ≤ laterRadius) :
    let padding := laterRadius - earlierRadius
    let roots := pinnedFaceCommonSmallRoots sizeFloor earlierRadius
    let hroots := pinnedFaceCommonSmallRoots_canonical hfloor
    ∀ target,
      target ∈ uniformShiftCylinderCanonicalAtoms
        padding (pinnedFaceSourceBase earlierRadius) roots hroots →
      pinnedFaceId laterRadius 0 ∈ target.val := by
  intro padding roots hroots target htarget
  have hvalue : target.val ∈
      (uniformShiftCylinderCanonicalAtoms padding
        (pinnedFaceSourceBase earlierRadius) roots hroots).map
        Subtype.val :=
    List.mem_map.mpr ⟨target, htarget, rfl⟩
  rw [uniformShiftCylinderCanonicalAtoms_values] at hvalue
  have htransport := pinnedFaceCommonSmallRoots_uniformShift
    hfloor hradius
  unfold uniformShiftedCylinderRoots at hvalue
  rw [htransport] at hvalue
  exact (mem_pinnedFaceCommonSmallRoots_iff
    (Nat.le_trans hfloor hradius)).mp hvalue |>.2.1

theorem pinnedFaceCommonShiftedTarget_core
    {sizeFloor earlierRadius laterRadius : Nat}
    (hfloor : sizeFloor ≤ earlierRadius)
    (hradius : earlierRadius ≤ laterRadius) :
    let padding := laterRadius - earlierRadius
    insideShiftedBoxB
      (addUniform (uniformShiftCellLower padding)
        (earlierRadius - sizeFloor))
      (pinnedFaceSourceBase sizeFloor)
      (boxPlaquetteAt
        (uniformPaddedBase padding
          (pinnedFaceSourceBase earlierRadius))
        (pinnedFaceId laterRadius 0)) = true := by
  intro padding
  dsimp only [padding]
  have hbase := pinnedFaceSourceBase_uniformPadding hradius
  rw [hbase]
  have hstageZero : pinnedFaceStageBase laterRadius 0 =
      pinnedFaceSourceBase laterRadius := by
    unfold pinnedFaceStageBase uniformPaddedBase
    omega
  rw [← hstageZero, boxPlaquetteAt_pinnedFaceId]
  rw [insideShiftedBoxB_true_iff]
  simp only [uniformShiftCellLower,
    pinnedFacePlaquette, pinnedFaceSourceBase, addUniform, cPlaq, vComp]
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

/-! ## 3. The explicit finite-volume comparison -/

theorem couplingParametricKPinnedFaceCommonVolume_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (cutoff : Nat) {sizeFloor earlierRadius laterRadius : Nat}
    (hfloor : sizeFloor ≤ earlierRadius)
    (hradius : earlierRadius ≤ laterRadius) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (pinnedFaceSourceBase laterRadius)
            (pinnedFaceCommonSmallEvent sizeFloor laterRadius) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (pinnedFaceSourceBase earlierRadius)
            (pinnedFaceCommonSmallEvent sizeFloor earlierRadius)) ≤
      uniformShiftSpinSummedCylinderBoundaryEpsilon
        (pinnedFaceCommonSmallRoots sizeFloor earlierRadius).length
        (earlierRadius - sizeFloor) := by
  let padding := laterRadius - earlierRadius
  let sourceBase := pinnedFaceSourceBase earlierRadius
  let roots := pinnedFaceCommonSmallRoots sizeFloor earlierRadius
  let hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers sourceBase :=
    pinnedFaceCommonSmallRoots_canonical hfloor
  let targetRoots := uniformShiftCylinderCanonicalAtoms
    padding sourceBase roots hroots
  have htargetInside : ∀ target, target ∈ targetRoots →
      targetRootInsideUniformShiftB padding sourceBase target.val = true :=
    uniformShiftCylinderCanonicalAtoms_inside
      padding sourceBase roots hroots
  let targetFace := pinnedFaceId laterRadius 0
  have htargetFace : ∀ target, target ∈ targetRoots →
      targetFace ∈ target.val := by
    dsimp only [targetRoots, targetFace, padding, sourceBase, roots, hroots]
    exact pinnedFaceCommonShiftedTarget_allPinned hfloor hradius
  let distance := earlierRadius - sizeFloor
  let inner := pinnedFaceSourceBase sizeFloor
  have hside : inner + distance + distance = sourceBase := by
    dsimp only [inner, distance, sourceBase, pinnedFaceSourceBase]
    omega
  have hcore : ∀ target, target ∈ targetRoots →
      insideShiftedBoxB
        (addUniform (uniformShiftCellLower padding) distance) inner
        (boxPlaquetteAt (uniformPaddedBase padding sourceBase)
          targetFace) = true := by
    intro target _htarget
    dsimp only [padding, distance, inner, sourceBase, targetFace]
    exact pinnedFaceCommonShiftedTarget_core hfloor hradius
  have hbound := uniformShiftTargetCylinderStabilityBound_of_anchor
    hcoupling hle
  have htargetBound := hbound cutoff padding sourceBase targetRoots
    canonicalFaceCylinderPredicate htargetInside
    (fun _target => targetFace) htargetFace
    (uniformShiftCellLower padding) inner distance hcore
    (fun plaquette hplaquette =>
      outside_uniformShiftCell_of_not_mem_of_side_eq
        hside hplaquette)
  have hevent : uniformShiftMarkedCylinderEvent targetRoots
      canonicalFaceCylinderPredicate =
      uniformShiftTargetCylinderEvent padding sourceBase roots
        canonicalFaceCylinderPredicate :=
    uniformShiftMarkedCylinderEvent_canonicalAtoms
      padding sourceBase roots hroots canonicalFaceCylinderPredicate
  rw [hevent] at htargetBound
  have hsource :=
    couplingParametricKCompatibleCylinderProbability_eqv_embedded_uniformShift
      coupling hcoupling cutoff (padding := padding) (base := sourceBase)
      hroots canonicalFaceCylinderPredicate
  let fullProbability :=
    couplingParametricKCompatibleSupportEventProbability
      coupling hcoupling cutoff (uniformPaddedBase padding sourceBase)
      (uniformShiftTargetCylinderEvent padding sourceBase roots
        canonicalFaceCylinderPredicate)
  let sourceProbability :=
    couplingParametricKCompatibleSupportEventProbability
      coupling hcoupling cutoff sourceBase
      (sourceCylinderEvent roots canonicalFaceCylinderPredicate)
  let embeddedProbability :=
    couplingParametricKUniformShiftEmbeddedTargetEventProbability
      coupling hcoupling cutoff padding sourceBase
      (uniformShiftTargetCylinderEvent padding sourceBase roots
        canonicalFaceCylinderPredicate)
  have hdifference :
      (fullProbability - sourceProbability) ≈
        (fullProbability - embeddedProbability) :=
    Q'.add_eqv_congr_left fullProbability
      (-sourceProbability) (-embeddedProbability)
      (Q'.neg_eqv_congr sourceProbability embeddedProbability hsource)
  have habs : Q'.abs (fullProbability - sourceProbability) ≤
      uniformShiftSpinSummedCylinderBoundaryEpsilon
        targetRoots.length distance :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference)) htargetBound
  have hlength : targetRoots.length = roots.length :=
    uniformShiftCylinderCanonicalAtoms_length
      padding sourceBase roots hroots
  rw [hlength] at habs
  have hbase := pinnedFaceSourceBase_uniformPadding hradius
  have heventTarget := pinnedFaceCommonSmallEvent_uniformShift
    hfloor hradius
  dsimp only [fullProbability, sourceProbability, padding, sourceBase,
    roots] at habs
  rw [hbase, heventTarget] at habs
  simpa only [distance] using habs

#print axioms uniformShiftCanonicalRoot_add_face
#print axioms mem_pinnedFaceCommonSmallRoots_iff
#print axioms pinnedFaceCommonSmallRoots_uniformShift
#print axioms pinnedFaceCommonSmallEvent_uniformShift
#print axioms pinnedFaceCommonShiftedTarget_core
#print axioms couplingParametricKPinnedFaceCommonVolume_abs_sub_le

end YMGap.Continuum.Z4CanonicalCentralFaceTruncationVolumeComparison
