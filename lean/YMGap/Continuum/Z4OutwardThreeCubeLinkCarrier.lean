/-
# Face-disjoint outward three-cube carriers

The adjacent central/outward cube construction cannot retain an interface
query after gauge cancellation.  The replacement uses the three cubes based
at the positive x, y, and z offsets.  These outward cube boundaries are
pairwise face-disjoint and touch only along lattice links.  Consequently any
nonempty union retains its selected central-interface faces, is closed mod
two, and has a strictly positive derived cutoff-one activity.

This module establishes the parity/amplitude half of that construction.  The
component-query truth table and normalized all-eight mass theorem are built
on these carriers downstream.
-/

import YMGap.Continuum.Z4AdjacentCubeCancellationCarrier

namespace YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4EvenIncidenceCanonicalActivityPositive
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

/-! ## 1. Translation and finite-union parity calculus -/

theorem axisShiftLink_injective (offset : AxisOffset) :
    Function.Injective (axisShiftLink offset) := by
  intro left right heq
  apply Prod.ext
  · apply axisShiftVertex_injective offset
    simpa only [axisShiftLink] using congrArg Prod.fst heq
  · simpa only [axisShiftLink] using congrArg Prod.snd heq

theorem flatMap_edgesOf_axisShiftPlaquette
    (offset : AxisOffset) : ∀ support : List Z4Plaq,
    (support.map (axisShiftPlaquette offset)).flatMap edgesOf =
      (support.flatMap edgesOf).map (axisShiftLink offset)
  | [] => rfl
  | plaquette :: rest => by
      simp only [List.map_cons, List.flatMap_cons, List.map_append,
        edgesOf_axisShiftPlaquette]
      rw [flatMap_edgesOf_axisShiftPlaquette offset rest]

theorem occurrenceCount_axisShiftLink_image
    (offset : AxisOffset) (source : Z4Link) : ∀ links : List Z4Link,
    occurrenceCount (axisShiftLink offset source)
        (links.map (axisShiftLink offset)) =
      occurrenceCount source links
  | [] => rfl
  | head :: rest => by
      simp only [List.map_cons, occurrenceCount]
      by_cases hhead : head = source
      · subst head
        rw [if_pos rfl, if_pos rfl,
          occurrenceCount_axisShiftLink_image offset source rest]
      · have hshift : axisShiftLink offset head ≠
            axisShiftLink offset source := by
          intro heq
          exact hhead (axisShiftLink_injective offset heq)
        rw [if_neg hshift, if_neg hhead,
          occurrenceCount_axisShiftLink_image offset source rest]

/-- Positive-coordinate translation preserves every mod-two link-incidence
equation. -/
theorem axisShift_evenFaceIncidence
    (offset : AxisOffset) {support : List Z4Plaq}
    (hclosed : EvenFaceIncidence support) :
    EvenFaceIncidence (support.map (axisShiftPlaquette offset)) := by
  intro target
  rw [← occurrenceCount_flatMap_edgesOf,
    flatMap_edgesOf_axisShiftPlaquette]
  by_cases hmem : target ∈
      (support.flatMap edgesOf).map (axisShiftLink offset)
  · obtain ⟨source, _, heq⟩ := List.mem_map.mp hmem
    rw [← heq, occurrenceCount_axisShiftLink_image,
      occurrenceCount_flatMap_edgesOf]
    exact hclosed source
  · rw [occurrenceCount_eq_zero_of_not_mem target _ hmem]

theorem faceIncidenceCount_append (link : Z4Link) :
    ∀ left right : List Z4Plaq,
      faceIncidenceCount link (left ++ right) =
        faceIncidenceCount link left + faceIncidenceCount link right
  | [], right => by simp [faceIncidenceCount]
  | plaquette :: rest, right => by
      simp only [List.cons_append, faceIncidenceCount]
      rw [faceIncidenceCount_append link rest right]
      omega

theorem evenFaceIncidence_append
    {left right : List Z4Plaq}
    (hleft : EvenFaceIncidence left)
    (hright : EvenFaceIncidence right) :
    EvenFaceIncidence (left ++ right) := by
  intro link
  rw [faceIncidenceCount_append, Nat.add_mod,
    hleft link, hright link]

theorem refinedUnitCubeSurface_evenFaceIncidence :
    EvenFaceIncidence refinedUnitCubeSurface := by
  intro link
  rw [← occurrenceCount_flatMap_edgesOf]
  exact refinedUnitCubeBoundaryMultiplicity_even link

/-! ## 2. The three outward cube surfaces -/

def zAxisOffset : AxisOffset := ⟨0, 0, 1, 0⟩

def outwardXSurface : List Z4Plaq := axisCubeSurface xAxisOffset
def outwardYSurface : List Z4Plaq := axisCubeSurface yAxisOffset
def outwardZSurface : List Z4Plaq := axisCubeSurface zAxisOffset

def outwardXYSurface : List Z4Plaq :=
  outwardXSurface ++ outwardYSurface

def outwardXZSurface : List Z4Plaq :=
  outwardXSurface ++ outwardZSurface

def outwardYZSurface : List Z4Plaq :=
  outwardYSurface ++ outwardZSurface

def outwardXYZSurface : List Z4Plaq :=
  outwardXSurface ++ outwardYSurface ++ outwardZSurface

theorem outwardXSurface_evenFaceIncidence :
    EvenFaceIncidence outwardXSurface := by
  exact axisShift_evenFaceIncidence xAxisOffset
    unitCubeSurface_evenFaceIncidence

theorem outwardYSurface_evenFaceIncidence :
    EvenFaceIncidence outwardYSurface := by
  exact axisShift_evenFaceIncidence yAxisOffset
    unitCubeSurface_evenFaceIncidence

theorem outwardZSurface_evenFaceIncidence :
    EvenFaceIncidence outwardZSurface := by
  exact axisShift_evenFaceIncidence zAxisOffset
    unitCubeSurface_evenFaceIncidence

theorem outwardXYSurface_evenFaceIncidence :
    EvenFaceIncidence outwardXYSurface :=
  evenFaceIncidence_append outwardXSurface_evenFaceIncidence
    outwardYSurface_evenFaceIncidence

theorem outwardXZSurface_evenFaceIncidence :
    EvenFaceIncidence outwardXZSurface :=
  evenFaceIncidence_append outwardXSurface_evenFaceIncidence
    outwardZSurface_evenFaceIncidence

theorem outwardYZSurface_evenFaceIncidence :
    EvenFaceIncidence outwardYZSurface :=
  evenFaceIncidence_append outwardYSurface_evenFaceIncidence
    outwardZSurface_evenFaceIncidence

theorem outwardXYZSurface_evenFaceIncidence :
    EvenFaceIncidence outwardXYZSurface :=
  evenFaceIncidence_append
    (evenFaceIncidence_append outwardXSurface_evenFaceIncidence
      outwardYSurface_evenFaceIncidence)
    outwardZSurface_evenFaceIncidence

/-! ## 3. Face-disjointness and exact support sizes -/

theorem outwardXSurface_nodup : outwardXSurface.Nodup := by decide
theorem outwardYSurface_nodup : outwardYSurface.Nodup := by decide
theorem outwardZSurface_nodup : outwardZSurface.Nodup := by decide

theorem outwardXYSurface_nodup : outwardXYSurface.Nodup := by decide
theorem outwardXZSurface_nodup : outwardXZSurface.Nodup := by decide
theorem outwardYZSurface_nodup : outwardYZSurface.Nodup := by decide
theorem outwardXYZSurface_nodup : outwardXYZSurface.Nodup := by decide

theorem outwardXYSurface_length : outwardXYSurface.length = 12 := by rfl
theorem outwardXZSurface_length : outwardXZSurface.length = 12 := by rfl
theorem outwardYZSurface_length : outwardYZSurface.length = 12 := by rfl
theorem outwardXYZSurface_length : outwardXYZSurface.length = 18 := by rfl

/-! ## 4. Link-touching connectivity -/

private def z4ChainInTrans {support : List Z4Plaq} :
    {first middle last : Z4Plaq} →
      PolymerModel.ChainIn z4Chain.toLattice support first middle →
      PolymerModel.ChainIn z4Chain.toLattice support middle last →
      PolymerModel.ChainIn z4Chain.toLattice support first last
  | _, _, _, .refl _, right => right
  | _, _, _, .step adjacent hnext rest, right =>
      .step adjacent hnext (z4ChainInTrans rest right)

private def z4ChainInMono {small large : List Z4Plaq}
    (hsubset : ∀ plaquette, plaquette ∈ small → plaquette ∈ large) :
    {first last : Z4Plaq} →
      PolymerModel.ChainIn z4Chain.toLattice small first last →
      PolymerModel.ChainIn z4Chain.toLattice large first last
  | _, _, .refl plaquette => .refl plaquette
  | _, _, .step adjacent hnext rest =>
      .step adjacent (hsubset _ hnext) (z4ChainInMono hsubset rest)

/-- Two internally connected face supports remain internally connected after
append when one displayed face from each side shares a lattice link. -/
def connectedIn_append_of_bridge
    {left right : List Z4Plaq}
    (hleft : PolymerModel.connectedIn (L := z4Chain.toLattice) left)
    (hright : PolymerModel.connectedIn (L := z4Chain.toLattice) right)
    {leftBridge rightBridge : Z4Plaq}
    (hleftBridge : leftBridge ∈ left)
    (hrightBridge : rightBridge ∈ right)
    (hbridge : z4Chain.toLattice.Adjacent leftBridge rightBridge) :
    PolymerModel.connectedIn (L := z4Chain.toLattice) (left ++ right) := by
  intro first last hfirst hlast
  by_cases hfirstLeft : first ∈ left
  · by_cases hlastLeft : last ∈ left
    · exact z4ChainInMono
        (fun plaquette hplaquette =>
          List.mem_append.mpr (Or.inl hplaquette))
        (hleft first last hfirstLeft hlastLeft)
    · have hlastRight : last ∈ right :=
        (List.mem_append.mp hlast).resolve_left hlastLeft
      exact z4ChainInTrans
        (z4ChainInMono
          (fun plaquette hplaquette =>
            List.mem_append.mpr (Or.inl hplaquette))
          (hleft first leftBridge hfirstLeft hleftBridge))
        (.step hbridge (List.mem_append.mpr (Or.inr hrightBridge))
          (z4ChainInMono
            (fun plaquette hplaquette =>
              List.mem_append.mpr (Or.inr hplaquette))
            (hright rightBridge last hrightBridge hlastRight)))
  · have hfirstRight : first ∈ right :=
      (List.mem_append.mp hfirst).resolve_left hfirstLeft
    by_cases hlastLeft : last ∈ left
    · exact z4ChainInTrans
        (z4ChainInMono
          (fun plaquette hplaquette =>
            List.mem_append.mpr (Or.inr hplaquette))
          (hright first rightBridge hfirstRight hrightBridge))
        (.step (YMGap.Continuum.AdjSpanningBuild.adjacentSymm hbridge)
          (List.mem_append.mpr (Or.inl hleftBridge))
          (z4ChainInMono
            (fun plaquette hplaquette =>
              List.mem_append.mpr (Or.inl hplaquette))
            (hleft leftBridge last hleftBridge hlastLeft)))
    · have hlastRight : last ∈ right :=
        (List.mem_append.mp hlast).resolve_left hlastLeft
      exact z4ChainInMono
        (fun plaquette hplaquette =>
          List.mem_append.mpr (Or.inr hplaquette))
        (hright first last hfirstRight hlastRight)

def outwardXYAdjacent : z4Chain.toLattice.Adjacent
    (axisShiftPlaquette xAxisOffset (cubeFace .backXZ))
    (axisShiftPlaquette yAxisOffset (cubeFace .rightYZ)) := by
  refine { link := ((1, 1, 0, 0), .x2), on_p := ?_, on_q := ?_ }
  · rfl
  · rfl

def outwardXZAdjacent : z4Chain.toLattice.Adjacent
    (axisShiftPlaquette xAxisOffset (cubeFace .topXY))
    (axisShiftPlaquette zAxisOffset (cubeFace .rightYZ)) := by
  refine { link := ((1, 0, 1, 0), .x1), on_p := ?_, on_q := ?_ }
  · rfl
  · rfl

def outwardYZAdjacent : z4Chain.toLattice.Adjacent
    (axisShiftPlaquette yAxisOffset (cubeFace .topXY))
    (axisShiftPlaquette zAxisOffset (cubeFace .backXZ)) := by
  refine { link := ((0, 1, 1, 0), .x0), on_p := ?_, on_q := ?_ }
  · rfl
  · rfl

theorem outwardXBridge_mem :
    axisShiftPlaquette xAxisOffset (cubeFace .backXZ) ∈
      outwardXSurface := by
  exact List.mem_map.mpr
    ⟨cubeFace .backXZ, cubeFace_mem_unitCubeSurface .backXZ, rfl⟩

theorem outwardYBridge_mem :
    axisShiftPlaquette yAxisOffset (cubeFace .rightYZ) ∈
      outwardYSurface := by
  exact List.mem_map.mpr
    ⟨cubeFace .rightYZ, cubeFace_mem_unitCubeSurface .rightYZ, rfl⟩

theorem outwardXTopBridge_mem :
    axisShiftPlaquette xAxisOffset (cubeFace .topXY) ∈
      outwardXSurface := by
  exact List.mem_map.mpr
    ⟨cubeFace .topXY, cubeFace_mem_unitCubeSurface .topXY, rfl⟩

theorem outwardYTopBridge_mem :
    axisShiftPlaquette yAxisOffset (cubeFace .topXY) ∈
      outwardYSurface := by
  exact List.mem_map.mpr
    ⟨cubeFace .topXY, cubeFace_mem_unitCubeSurface .topXY, rfl⟩

theorem outwardZRightBridge_mem :
    axisShiftPlaquette zAxisOffset (cubeFace .rightYZ) ∈
      outwardZSurface := by
  exact List.mem_map.mpr
    ⟨cubeFace .rightYZ, cubeFace_mem_unitCubeSurface .rightYZ, rfl⟩

theorem outwardZBackBridge_mem :
    axisShiftPlaquette zAxisOffset (cubeFace .backXZ) ∈
      outwardZSurface := by
  exact List.mem_map.mpr
    ⟨cubeFace .backXZ, cubeFace_mem_unitCubeSurface .backXZ, rfl⟩

def outwardXSurface_connected :
    PolymerModel.connectedIn (L := z4Chain.toLattice) outwardXSurface :=
  axisCubeSurface_connected xAxisOffset

def outwardYSurface_connected :
    PolymerModel.connectedIn (L := z4Chain.toLattice) outwardYSurface :=
  axisCubeSurface_connected yAxisOffset

def outwardZSurface_connected :
    PolymerModel.connectedIn (L := z4Chain.toLattice) outwardZSurface :=
  axisCubeSurface_connected zAxisOffset

def outwardXYSurface_connected :
    PolymerModel.connectedIn (L := z4Chain.toLattice) outwardXYSurface :=
  connectedIn_append_of_bridge outwardXSurface_connected
    outwardYSurface_connected outwardXBridge_mem outwardYBridge_mem
    outwardXYAdjacent

def outwardXZSurface_connected :
    PolymerModel.connectedIn (L := z4Chain.toLattice) outwardXZSurface :=
  connectedIn_append_of_bridge outwardXSurface_connected
    outwardZSurface_connected outwardXTopBridge_mem outwardZRightBridge_mem
    outwardXZAdjacent

def outwardYZSurface_connected :
    PolymerModel.connectedIn (L := z4Chain.toLattice) outwardYZSurface :=
  connectedIn_append_of_bridge outwardYSurface_connected
    outwardZSurface_connected outwardYTopBridge_mem outwardZBackBridge_mem
    outwardYZAdjacent

def outwardXYZSurface_connected :
    PolymerModel.connectedIn (L := z4Chain.toLattice) outwardXYZSurface :=
  connectedIn_append_of_bridge outwardXYSurface_connected
    outwardZSurface_connected
    (List.mem_append.mpr (Or.inl outwardXTopBridge_mem))
    outwardZRightBridge_mem outwardXZAdjacent

/-! ## 5. Box embedding and positive encoded activities -/

theorem outwardZSurface_subset_box_six :
    ∀ plaquette, plaquette ∈ outwardZSurface →
      plaquette ∈ boxPlaquettes 6 := by
  intro plaquette hplaquette
  obtain ⟨source, hsource, rfl⟩ :=
    decodeMapMember (axisShiftPlaquette zAxisOffset)
      unitCubeSurface plaquette hplaquette
  exact boxPlaquettes_mono (by simp [zAxisOffset])
    (axisShiftPlaquette_mem_extended_box zAxisOffset
      (unitCubeSurface_subset_box_two source hsource))

theorem outwardXSurface_subset_box_six :
    ∀ plaquette, plaquette ∈ outwardXSurface →
      plaquette ∈ boxPlaquettes 6 :=
  axisCubeSurface_subset_box_six xAxisOffset
    (Or.inr (Or.inl rfl))

theorem outwardYSurface_subset_box_six :
    ∀ plaquette, plaquette ∈ outwardYSurface →
      plaquette ∈ boxPlaquettes 6 :=
  axisCubeSurface_subset_box_six yAxisOffset
    (Or.inr (Or.inr rfl))

theorem outwardXYSurface_subset_box_six :
    ∀ plaquette, plaquette ∈ outwardXYSurface →
      plaquette ∈ boxPlaquettes 6 := by
  intro plaquette hplaquette
  rcases List.mem_append.mp hplaquette with hx | hy
  · exact outwardXSurface_subset_box_six plaquette hx
  · exact outwardYSurface_subset_box_six plaquette hy

theorem outwardXZSurface_subset_box_six :
    ∀ plaquette, plaquette ∈ outwardXZSurface →
      plaquette ∈ boxPlaquettes 6 := by
  intro plaquette hplaquette
  rcases List.mem_append.mp hplaquette with hx | hz
  · exact outwardXSurface_subset_box_six plaquette hx
  · exact outwardZSurface_subset_box_six plaquette hz

theorem outwardYZSurface_subset_box_six :
    ∀ plaquette, plaquette ∈ outwardYZSurface →
      plaquette ∈ boxPlaquettes 6 := by
  intro plaquette hplaquette
  rcases List.mem_append.mp hplaquette with hy | hz
  · exact outwardYSurface_subset_box_six plaquette hy
  · exact outwardZSurface_subset_box_six plaquette hz

theorem outwardXYZSurface_subset_box_six :
    ∀ plaquette, plaquette ∈ outwardXYZSurface →
      plaquette ∈ boxPlaquettes 6 := by
  intro plaquette hplaquette
  simp only [outwardXYZSurface, List.mem_append] at hplaquette
  rcases hplaquette with hxy | hz
  · rcases hxy with hx | hy
    · exact axisCubeSurface_subset_box_six xAxisOffset
        (Or.inr (Or.inl rfl)) plaquette hx
    · exact axisCubeSurface_subset_box_six yAxisOffset
        (Or.inr (Or.inr rfl)) plaquette hy
  · exact outwardZSurface_subset_box_six plaquette hz

def outwardXRoot : List Nat := geometricSupportIds 6 outwardXSurface
def outwardYRoot : List Nat := geometricSupportIds 6 outwardYSurface
def outwardZRoot : List Nat := geometricSupportIds 6 outwardZSurface
def outwardXYRoot : List Nat := geometricSupportIds 6 outwardXYSurface
def outwardXZRoot : List Nat := geometricSupportIds 6 outwardXZSurface
def outwardYZRoot : List Nat := geometricSupportIds 6 outwardYZSurface
def outwardXYZRoot : List Nat := geometricSupportIds 6 outwardXYZSurface

theorem outwardXRoot_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 outwardXRoot) outwardXSurface := by
  exact geometricSupportIds_sameSupport outwardXSurface_subset_box_six

theorem outwardYRoot_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 outwardYRoot) outwardYSurface := by
  exact geometricSupportIds_sameSupport outwardYSurface_subset_box_six

theorem outwardZRoot_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 outwardZRoot) outwardZSurface := by
  exact geometricSupportIds_sameSupport outwardZSurface_subset_box_six

theorem outwardXYRoot_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 outwardXYRoot) outwardXYSurface := by
  exact geometricSupportIds_sameSupport outwardXYSurface_subset_box_six

theorem outwardXZRoot_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 outwardXZRoot) outwardXZSurface := by
  exact geometricSupportIds_sameSupport outwardXZSurface_subset_box_six

theorem outwardYZRoot_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 outwardYZRoot) outwardYZSurface := by
  exact geometricSupportIds_sameSupport outwardYZSurface_subset_box_six

theorem outwardXYZRoot_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 outwardXYZRoot) outwardXYZSurface := by
  exact geometricSupportIds_sameSupport outwardXYZSurface_subset_box_six

private theorem geometricRoot_mem_canonical
    {support : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hnonempty : Σ' plaquette : Z4Plaq, plaquette ∈ support)
    (hconnected : PolymerModel.connectedIn
      (L := z4Chain.toLattice) support) :
    geometricSupportIds 6 support ∈ canonicalSurfacePolymers 6 := by
  apply connectedFaceSupport_mem_canonicalSurfacePolymers
  · exact geometricSupportIds_mem_cutoffOneFaceSupports 6 support
  · obtain ⟨plaquette, hplaquette⟩ := hnonempty
    have hdecoded : plaquette ∈
        geometricPolymer 6 (geometricSupportIds 6 support) :=
      (geometricSupportIds_sameSupport hbox).2 plaquette hplaquette
    obtain ⟨identifier, hidentifier, _⟩ :=
      decodeMapMember (boxPlaquetteAt 6)
        (geometricSupportIds 6 support) plaquette hdecoded
    exact ⟨identifier, hidentifier⟩
  · exact geometricSupportIds_connected hbox hconnected

private def outwardXSurface_nonempty :
    Σ' plaquette : Z4Plaq, plaquette ∈ outwardXSurface :=
  ⟨axisShiftPlaquette xAxisOffset (cubeFace .bottomXY),
    List.mem_map.mpr
      ⟨cubeFace .bottomXY, cubeFace_mem_unitCubeSurface .bottomXY, rfl⟩⟩

private def outwardYSurface_nonempty :
    Σ' plaquette : Z4Plaq, plaquette ∈ outwardYSurface :=
  ⟨axisShiftPlaquette yAxisOffset (cubeFace .bottomXY),
    List.mem_map.mpr
      ⟨cubeFace .bottomXY, cubeFace_mem_unitCubeSurface .bottomXY, rfl⟩⟩

private def outwardZSurface_nonempty :
    Σ' plaquette : Z4Plaq, plaquette ∈ outwardZSurface :=
  ⟨axisShiftPlaquette zAxisOffset (cubeFace .bottomXY),
    List.mem_map.mpr
      ⟨cubeFace .bottomXY, cubeFace_mem_unitCubeSurface .bottomXY, rfl⟩⟩

theorem outwardXRoot_mem_canonical :
    outwardXRoot ∈ canonicalSurfacePolymers 6 := by
  exact geometricRoot_mem_canonical outwardXSurface_subset_box_six
    outwardXSurface_nonempty outwardXSurface_connected

theorem outwardYRoot_mem_canonical :
    outwardYRoot ∈ canonicalSurfacePolymers 6 := by
  exact geometricRoot_mem_canonical outwardYSurface_subset_box_six
    outwardYSurface_nonempty outwardYSurface_connected

theorem outwardZRoot_mem_canonical :
    outwardZRoot ∈ canonicalSurfacePolymers 6 := by
  exact geometricRoot_mem_canonical outwardZSurface_subset_box_six
    outwardZSurface_nonempty outwardZSurface_connected

theorem outwardXYRoot_mem_canonical :
    outwardXYRoot ∈ canonicalSurfacePolymers 6 := by
  exact geometricRoot_mem_canonical outwardXYSurface_subset_box_six
    ⟨outwardXSurface_nonempty.1,
      List.mem_append.mpr (Or.inl outwardXSurface_nonempty.2)⟩
    outwardXYSurface_connected

theorem outwardXZRoot_mem_canonical :
    outwardXZRoot ∈ canonicalSurfacePolymers 6 := by
  exact geometricRoot_mem_canonical outwardXZSurface_subset_box_six
    ⟨outwardXSurface_nonempty.1,
      List.mem_append.mpr (Or.inl outwardXSurface_nonempty.2)⟩
    outwardXZSurface_connected

theorem outwardYZRoot_mem_canonical :
    outwardYZRoot ∈ canonicalSurfacePolymers 6 := by
  exact geometricRoot_mem_canonical outwardYZSurface_subset_box_six
    ⟨outwardYSurface_nonempty.1,
      List.mem_append.mpr (Or.inl outwardYSurface_nonempty.2)⟩
    outwardYZSurface_connected

theorem outwardXYZRoot_mem_canonical :
    outwardXYZRoot ∈ canonicalSurfacePolymers 6 := by
  exact geometricRoot_mem_canonical outwardXYZSurface_subset_box_six
    ⟨outwardXSurface_nonempty.1,
      List.mem_append.mpr
        (Or.inl (List.mem_append.mpr
          (Or.inl outwardXSurface_nonempty.2)))⟩
    outwardXYZSurface_connected

/-- The seven nonempty Boolean carriers are all genuine canonical connected
polymers, not merely cutoff-one supports. -/
theorem outwardNonemptyRoots_mem_canonical :
    outwardXRoot ∈ canonicalSurfacePolymers 6 ∧
    outwardYRoot ∈ canonicalSurfacePolymers 6 ∧
    outwardZRoot ∈ canonicalSurfacePolymers 6 ∧
    outwardXYRoot ∈ canonicalSurfacePolymers 6 ∧
    outwardXZRoot ∈ canonicalSurfacePolymers 6 ∧
    outwardYZRoot ∈ canonicalSurfacePolymers 6 ∧
    outwardXYZRoot ∈ canonicalSurfacePolymers 6 :=
  ⟨outwardXRoot_mem_canonical, outwardYRoot_mem_canonical,
    outwardZRoot_mem_canonical, outwardXYRoot_mem_canonical,
    outwardXZRoot_mem_canonical, outwardYZRoot_mem_canonical,
    outwardXYZRoot_mem_canonical⟩

private theorem evenFaceIncidence_geometricSupportIds
    {support : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hnodup : support.Nodup)
    (hclosed : EvenFaceIncidence support) :
    EvenFaceIncidence
      (geometricPolymer 6 (geometricSupportIds 6 support)) := by
  intro link
  have hids : geometricSupportIds 6 support ∈
      cutoffOneFaceSupports 6 :=
    geometricSupportIds_mem_cutoffOneFaceSupports 6 support
  have hsame := geometricSupportIds_sameSupport hbox
  have hfiltered := geometricIncidentPlaquettes_sameSupport hsame link
  have hlength := sameSupport_length_eq_of_nodup hfiltered
    (List.filter_sublist.nodup (geometricPolymer_nodup hids))
    (List.filter_sublist.nodup hnodup)
  have hcount : faceIncidenceCount link
        (geometricPolymer 6 (geometricSupportIds 6 support)) =
      faceIncidenceCount link support :=
    Eq.trans
      (geometricIncidentPlaquettes_length_eq_faceIncidenceCount _ _).symm
      (Eq.trans hlength
        (geometricIncidentPlaquettes_length_eq_faceIncidenceCount _ _))
  rw [hcount]
  exact hclosed link

private theorem geometricRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling)
    {support : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hnodup : support.Nodup)
    (hclosed : EvenFaceIncidence support) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      (geometricSupportIds 6 support) := by
  apply canonicalSurfaceActivity_pos_of_evenIncidence hcoupling
    (geometricSupportIds_mem_cutoffOneFaceSupports 6 support)
  exact evenFaceIncidence_geometricSupportIds hbox hnodup hclosed

theorem outwardXYZRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      outwardXYZRoot := by
  exact geometricRoot_activity_pos hcoupling
    outwardXYZSurface_subset_box_six
    outwardXYZSurface_nodup
    outwardXYZSurface_evenFaceIncidence

theorem outwardXRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      outwardXRoot := by
  exact geometricRoot_activity_pos hcoupling
    outwardXSurface_subset_box_six
    outwardXSurface_nodup
    outwardXSurface_evenFaceIncidence

theorem outwardYRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      outwardYRoot := by
  exact geometricRoot_activity_pos hcoupling
    outwardYSurface_subset_box_six
    outwardYSurface_nodup
    outwardYSurface_evenFaceIncidence

theorem outwardZRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      outwardZRoot := by
  exact geometricRoot_activity_pos hcoupling
    outwardZSurface_subset_box_six
    outwardZSurface_nodup
    outwardZSurface_evenFaceIncidence

theorem outwardXYRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      outwardXYRoot := by
  exact geometricRoot_activity_pos hcoupling
    outwardXYSurface_subset_box_six
    outwardXYSurface_nodup
    outwardXYSurface_evenFaceIncidence

theorem outwardXZRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      outwardXZRoot := by
  exact geometricRoot_activity_pos hcoupling
    outwardXZSurface_subset_box_six
    outwardXZSurface_nodup
    outwardXZSurface_evenFaceIncidence

theorem outwardYZRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      outwardYZRoot := by
  exact geometricRoot_activity_pos hcoupling
    outwardYZSurface_subset_box_six
    outwardYZSurface_nodup
    outwardYZSurface_evenFaceIncidence

/-- Every nonempty outward Boolean carrier has a strictly positive exact
activity.  This is the amplitude half of the eventual seven-pattern witness
family. -/
theorem outwardNonemptyRoots_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6 outwardXRoot ∧
    (0 : Q') < canonicalSurfaceActivity coupling 6 outwardYRoot ∧
    (0 : Q') < canonicalSurfaceActivity coupling 6 outwardZRoot ∧
    (0 : Q') < canonicalSurfaceActivity coupling 6 outwardXYRoot ∧
    (0 : Q') < canonicalSurfaceActivity coupling 6 outwardXZRoot ∧
    (0 : Q') < canonicalSurfaceActivity coupling 6 outwardYZRoot ∧
    (0 : Q') < canonicalSurfaceActivity coupling 6 outwardXYZRoot := by
  exact ⟨outwardXRoot_activity_pos hcoupling,
    outwardYRoot_activity_pos hcoupling,
    outwardZRoot_activity_pos hcoupling,
    outwardXYRoot_activity_pos hcoupling,
    outwardXZRoot_activity_pos hcoupling,
    outwardYZRoot_activity_pos hcoupling,
    outwardXYZRoot_activity_pos hcoupling⟩

#print axioms axisShift_evenFaceIncidence
#print axioms evenFaceIncidence_append
#print axioms outwardXSurface_evenFaceIncidence
#print axioms outwardYSurface_evenFaceIncidence
#print axioms outwardZSurface_evenFaceIncidence
#print axioms outwardXYZSurface_nodup
#print axioms outwardXYZSurface_evenFaceIncidence
#print axioms connectedIn_append_of_bridge
#print axioms outwardXYZSurface_connected
#print axioms outwardXYZRoot_sameSupport
#print axioms outwardNonemptyRoots_mem_canonical
#print axioms outwardXYZRoot_activity_pos
#print axioms outwardNonemptyRoots_activity_pos

end YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
