/-
# Refined outward three-cube carriers

The seven coarse outward carriers have literal dyadic refinements.  This
module builds those fine supports in the same volume-six box and proves the
geometric facts needed before any probabilistic blocking comparison: closure,
face-disjointness, link connectivity, canonical encoding, and exact root
refinement.
-/

import YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier

namespace YMGap.Continuum.Z4OutwardThreeCubeFineCarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4EvenIncidenceCanonicalActivityPositive
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4ThreeBlockPhysicalCubeLeakage
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

/-! ## 1. Seven literal fine supports -/

def outwardXFineSurface : List Z4Plaq :=
  axisFineCubeSurface xAxisOffset

def outwardYFineSurface : List Z4Plaq :=
  axisFineCubeSurface yAxisOffset

def outwardZFineSurface : List Z4Plaq :=
  axisFineCubeSurface zAxisOffset

def outwardXYFineSurface : List Z4Plaq :=
  outwardXFineSurface ++ outwardYFineSurface

def outwardXZFineSurface : List Z4Plaq :=
  outwardXFineSurface ++ outwardZFineSurface

def outwardYZFineSurface : List Z4Plaq :=
  outwardYFineSurface ++ outwardZFineSurface

def outwardXYZFineSurface : List Z4Plaq :=
  outwardXFineSurface ++ outwardYFineSurface ++ outwardZFineSurface

theorem outwardXFineSurface_evenFaceIncidence :
    EvenFaceIncidence outwardXFineSurface := by
  unfold outwardXFineSurface axisFineCubeSurface axisCubeSurface
  rw [dyadicSupportCells_axisShift]
  exact axisShift_evenFaceIncidence (doubleAxisOffset xAxisOffset)
    refinedUnitCubeSurface_evenFaceIncidence

theorem outwardYFineSurface_evenFaceIncidence :
    EvenFaceIncidence outwardYFineSurface := by
  unfold outwardYFineSurface axisFineCubeSurface axisCubeSurface
  rw [dyadicSupportCells_axisShift]
  exact axisShift_evenFaceIncidence (doubleAxisOffset yAxisOffset)
    refinedUnitCubeSurface_evenFaceIncidence

theorem outwardZFineSurface_evenFaceIncidence :
    EvenFaceIncidence outwardZFineSurface := by
  unfold outwardZFineSurface axisFineCubeSurface axisCubeSurface
  rw [dyadicSupportCells_axisShift]
  exact axisShift_evenFaceIncidence (doubleAxisOffset zAxisOffset)
    refinedUnitCubeSurface_evenFaceIncidence

theorem outwardXYFineSurface_evenFaceIncidence :
    EvenFaceIncidence outwardXYFineSurface :=
  evenFaceIncidence_append outwardXFineSurface_evenFaceIncidence
    outwardYFineSurface_evenFaceIncidence

theorem outwardXZFineSurface_evenFaceIncidence :
    EvenFaceIncidence outwardXZFineSurface :=
  evenFaceIncidence_append outwardXFineSurface_evenFaceIncidence
    outwardZFineSurface_evenFaceIncidence

theorem outwardYZFineSurface_evenFaceIncidence :
    EvenFaceIncidence outwardYZFineSurface :=
  evenFaceIncidence_append outwardYFineSurface_evenFaceIncidence
    outwardZFineSurface_evenFaceIncidence

theorem outwardXYZFineSurface_evenFaceIncidence :
    EvenFaceIncidence outwardXYZFineSurface :=
  evenFaceIncidence_append
    (evenFaceIncidence_append outwardXFineSurface_evenFaceIncidence
      outwardYFineSurface_evenFaceIncidence)
    outwardZFineSurface_evenFaceIncidence

theorem outwardXFineSurface_nodup : outwardXFineSurface.Nodup := by decide
theorem outwardYFineSurface_nodup : outwardYFineSurface.Nodup := by decide
theorem outwardZFineSurface_nodup : outwardZFineSurface.Nodup := by decide
theorem outwardXYFineSurface_nodup : outwardXYFineSurface.Nodup := by decide
theorem outwardXZFineSurface_nodup : outwardXZFineSurface.Nodup := by decide
theorem outwardYZFineSurface_nodup : outwardYZFineSurface.Nodup := by decide
theorem outwardXYZFineSurface_nodup : outwardXYZFineSurface.Nodup := by decide

/-! ## 2. Common finite box -/

theorem outwardXFineSurface_subset_box_six :
    ∀ plaquette, plaquette ∈ outwardXFineSurface →
      plaquette ∈ boxPlaquettes 6 := by
  exact axisFineCubeSurface_subset_box_six xAxisOffset
    (Or.inr (Or.inl rfl))

theorem outwardYFineSurface_subset_box_six :
    ∀ plaquette, plaquette ∈ outwardYFineSurface →
      plaquette ∈ boxPlaquettes 6 := by
  exact axisFineCubeSurface_subset_box_six yAxisOffset
    (Or.inr (Or.inr rfl))

private theorem outwardZSurface_subset_box_three :
    ∀ plaquette, plaquette ∈ outwardZSurface →
      plaquette ∈ boxPlaquettes 3 := by
  intro plaquette hplaquette
  obtain ⟨source, hsource, rfl⟩ :=
    decodeMapMember (axisShiftPlaquette zAxisOffset)
      unitCubeSurface plaquette hplaquette
  simpa [zAxisOffset] using
    axisShiftPlaquette_mem_extended_box zAxisOffset
      (unitCubeSurface_subset_box_two source hsource)

theorem outwardZFineSurface_subset_box_six :
    ∀ plaquette, plaquette ∈ outwardZFineSurface →
      plaquette ∈ boxPlaquettes 6 := by
  exact dyadicSupportCells_subset_double_box
    outwardZSurface_subset_box_three

theorem outwardXYFineSurface_subset_box_six :
    ∀ plaquette, plaquette ∈ outwardXYFineSurface →
      plaquette ∈ boxPlaquettes 6 := by
  intro plaquette hplaquette
  rcases List.mem_append.mp hplaquette with hx | hy
  · exact outwardXFineSurface_subset_box_six plaquette hx
  · exact outwardYFineSurface_subset_box_six plaquette hy

theorem outwardXZFineSurface_subset_box_six :
    ∀ plaquette, plaquette ∈ outwardXZFineSurface →
      plaquette ∈ boxPlaquettes 6 := by
  intro plaquette hplaquette
  rcases List.mem_append.mp hplaquette with hx | hz
  · exact outwardXFineSurface_subset_box_six plaquette hx
  · exact outwardZFineSurface_subset_box_six plaquette hz

theorem outwardYZFineSurface_subset_box_six :
    ∀ plaquette, plaquette ∈ outwardYZFineSurface →
      plaquette ∈ boxPlaquettes 6 := by
  intro plaquette hplaquette
  rcases List.mem_append.mp hplaquette with hy | hz
  · exact outwardYFineSurface_subset_box_six plaquette hy
  · exact outwardZFineSurface_subset_box_six plaquette hz

theorem outwardXYZFineSurface_subset_box_six :
    ∀ plaquette, plaquette ∈ outwardXYZFineSurface →
      plaquette ∈ boxPlaquettes 6 := by
  intro plaquette hplaquette
  simp only [outwardXYZFineSurface, List.mem_append] at hplaquette
  rcases hplaquette with hxy | hz
  · rcases hxy with hx | hy
    · exact outwardXFineSurface_subset_box_six plaquette hx
    · exact outwardYFineSurface_subset_box_six plaquette hy
  · exact outwardZFineSurface_subset_box_six plaquette hz

/-! ## 3. Link-touching connectivity -/

private theorem fineCell_mem_axisFineCubeSurface
    (offset : AxisOffset) (face : CubeFaceIndex)
    (index : DyadicCellIndex) :
    dyadicCell (axisShiftPlaquette offset (cubeFace face)) index ∈
      axisFineCubeSurface offset := by
  unfold axisFineCubeSurface
  apply (mem_dyadicSupportCells_iff _ _).mpr
  exact ⟨axisShiftPlaquette offset (cubeFace face),
    List.mem_map.mpr
      ⟨cubeFace face, cubeFace_mem_unitCubeSurface face, rfl⟩,
    dyadicCell_mem_cells _ _⟩

def outwardXYFineAdjacent : z4Chain.toLattice.Adjacent
    (dyadicCell
      (axisShiftPlaquette xAxisOffset (cubeFace .backXZ)) .origin)
    (dyadicCell
      (axisShiftPlaquette yAxisOffset (cubeFace .rightYZ)) .origin) := by
  refine { link := ((2, 2, 0, 0), .x2), on_p := ?_, on_q := ?_ }
  · rfl
  · rfl

def outwardXZFineAdjacent : z4Chain.toLattice.Adjacent
    (dyadicCell
      (axisShiftPlaquette xAxisOffset (cubeFace .topXY)) .origin)
    (dyadicCell
      (axisShiftPlaquette zAxisOffset (cubeFace .rightYZ)) .origin) := by
  refine { link := ((2, 0, 2, 0), .x1), on_p := ?_, on_q := ?_ }
  · rfl
  · rfl

def outwardYZFineAdjacent : z4Chain.toLattice.Adjacent
    (dyadicCell
      (axisShiftPlaquette yAxisOffset (cubeFace .topXY)) .origin)
    (dyadicCell
      (axisShiftPlaquette zAxisOffset (cubeFace .backXZ)) .origin) := by
  refine { link := ((0, 2, 2, 0), .x0), on_p := ?_, on_q := ?_ }
  · rfl
  · rfl

theorem outwardXBackFineBridge_mem :
    dyadicCell
      (axisShiftPlaquette xAxisOffset (cubeFace .backXZ)) .origin ∈
      outwardXFineSurface :=
  fineCell_mem_axisFineCubeSurface xAxisOffset .backXZ .origin

theorem outwardYRightFineBridge_mem :
    dyadicCell
      (axisShiftPlaquette yAxisOffset (cubeFace .rightYZ)) .origin ∈
      outwardYFineSurface :=
  fineCell_mem_axisFineCubeSurface yAxisOffset .rightYZ .origin

theorem outwardXTopFineBridge_mem :
    dyadicCell
      (axisShiftPlaquette xAxisOffset (cubeFace .topXY)) .origin ∈
      outwardXFineSurface :=
  fineCell_mem_axisFineCubeSurface xAxisOffset .topXY .origin

theorem outwardYTopFineBridge_mem :
    dyadicCell
      (axisShiftPlaquette yAxisOffset (cubeFace .topXY)) .origin ∈
      outwardYFineSurface :=
  fineCell_mem_axisFineCubeSurface yAxisOffset .topXY .origin

theorem outwardZRightFineBridge_mem :
    dyadicCell
      (axisShiftPlaquette zAxisOffset (cubeFace .rightYZ)) .origin ∈
      outwardZFineSurface :=
  fineCell_mem_axisFineCubeSurface zAxisOffset .rightYZ .origin

theorem outwardZBackFineBridge_mem :
    dyadicCell
      (axisShiftPlaquette zAxisOffset (cubeFace .backXZ)) .origin ∈
      outwardZFineSurface :=
  fineCell_mem_axisFineCubeSurface zAxisOffset .backXZ .origin

def outwardXFineSurface_connected :
    PolymerModel.connectedIn (L := z4Chain.toLattice)
      outwardXFineSurface :=
  axisFineCubeSurface_connected xAxisOffset

def outwardYFineSurface_connected :
    PolymerModel.connectedIn (L := z4Chain.toLattice)
      outwardYFineSurface :=
  axisFineCubeSurface_connected yAxisOffset

def outwardZFineSurface_connected :
    PolymerModel.connectedIn (L := z4Chain.toLattice)
      outwardZFineSurface :=
  axisFineCubeSurface_connected zAxisOffset

def outwardXYFineSurface_connected :
    PolymerModel.connectedIn (L := z4Chain.toLattice)
      outwardXYFineSurface :=
  connectedIn_append_of_bridge outwardXFineSurface_connected
    outwardYFineSurface_connected outwardXBackFineBridge_mem
    outwardYRightFineBridge_mem outwardXYFineAdjacent

def outwardXZFineSurface_connected :
    PolymerModel.connectedIn (L := z4Chain.toLattice)
      outwardXZFineSurface :=
  connectedIn_append_of_bridge outwardXFineSurface_connected
    outwardZFineSurface_connected outwardXTopFineBridge_mem
    outwardZRightFineBridge_mem outwardXZFineAdjacent

def outwardYZFineSurface_connected :
    PolymerModel.connectedIn (L := z4Chain.toLattice)
      outwardYZFineSurface :=
  connectedIn_append_of_bridge outwardYFineSurface_connected
    outwardZFineSurface_connected outwardYTopFineBridge_mem
    outwardZBackFineBridge_mem outwardYZFineAdjacent

def outwardXYZFineSurface_connected :
    PolymerModel.connectedIn (L := z4Chain.toLattice)
      outwardXYZFineSurface :=
  connectedIn_append_of_bridge outwardXYFineSurface_connected
    outwardZFineSurface_connected
    (List.mem_append.mpr (Or.inl outwardXTopFineBridge_mem))
    outwardZRightFineBridge_mem outwardXZFineAdjacent

/-! ## 4. Exact dyadic refinement of all seven coarse roots -/

def outwardXFineRoot : List Nat :=
  geometricSupportIds 6 outwardXFineSurface

def outwardYFineRoot : List Nat :=
  geometricSupportIds 6 outwardYFineSurface

def outwardZFineRoot : List Nat :=
  geometricSupportIds 6 outwardZFineSurface

def outwardXYFineRoot : List Nat :=
  geometricSupportIds 6 outwardXYFineSurface

def outwardXZFineRoot : List Nat :=
  geometricSupportIds 6 outwardXZFineSurface

def outwardYZFineRoot : List Nat :=
  geometricSupportIds 6 outwardYZFineSurface

def outwardXYZFineRoot : List Nat :=
  geometricSupportIds 6 outwardXYZFineSurface

private theorem dyadicSupportCells_append
    (left right : List Z4Plaq) :
    dyadicSupportCells (left ++ right) =
      dyadicSupportCells left ++ dyadicSupportCells right := by
  unfold dyadicSupportCells
  exact List.flatMap_append

theorem outwardXFineSurface_eq_dyadic :
    outwardXFineSurface = dyadicSupportCells outwardXSurface := rfl

theorem outwardYFineSurface_eq_dyadic :
    outwardYFineSurface = dyadicSupportCells outwardYSurface := rfl

theorem outwardZFineSurface_eq_dyadic :
    outwardZFineSurface = dyadicSupportCells outwardZSurface := rfl

theorem outwardXYFineSurface_eq_dyadic :
    outwardXYFineSurface = dyadicSupportCells outwardXYSurface := by
  unfold outwardXYFineSurface outwardXYSurface
  rw [dyadicSupportCells_append]
  rfl

theorem outwardXZFineSurface_eq_dyadic :
    outwardXZFineSurface = dyadicSupportCells outwardXZSurface := by
  unfold outwardXZFineSurface outwardXZSurface
  rw [dyadicSupportCells_append]
  rfl

theorem outwardYZFineSurface_eq_dyadic :
    outwardYZFineSurface = dyadicSupportCells outwardYZSurface := by
  unfold outwardYZFineSurface outwardYZSurface
  rw [dyadicSupportCells_append]
  rfl

theorem outwardXYZFineSurface_eq_dyadic :
    outwardXYZFineSurface = dyadicSupportCells outwardXYZSurface := by
  unfold outwardXYZFineSurface outwardXYZSurface
  rw [dyadicSupportCells_append, dyadicSupportCells_append]
  rfl

private theorem dyadicSupportCells_sameSupport
    {left right : List Z4Plaq}
    (hsupport : sameSupport (L := z4Chain.toLattice) left right) :
    sameSupport (L := z4Chain.toLattice)
      (dyadicSupportCells left) (dyadicSupportCells right) := by
  constructor
  · intro cell hcell
    obtain ⟨plaquette, hplaquette, hlocal⟩ :=
      (mem_dyadicSupportCells_iff left cell).mp hcell
    exact (mem_dyadicSupportCells_iff right cell).mpr
      ⟨plaquette, hsupport.1 plaquette hplaquette, hlocal⟩
  · intro cell hcell
    obtain ⟨plaquette, hplaquette, hlocal⟩ :=
      (mem_dyadicSupportCells_iff right cell).mp hcell
    exact (mem_dyadicSupportCells_iff left cell).mpr
      ⟨plaquette, hsupport.2 plaquette hplaquette, hlocal⟩

private theorem geometricFineRoot_refines
    {coarseSupport fineSupport : List Z4Plaq}
    (hcoarseBox : ∀ plaquette, plaquette ∈ coarseSupport →
      plaquette ∈ boxPlaquettes 6)
    (hfineBox : ∀ plaquette, plaquette ∈ fineSupport →
      plaquette ∈ boxPlaquettes 6)
    (hrefine : fineSupport = dyadicSupportCells coarseSupport) :
    DyadicRootRefines 6
      (geometricSupportIds 6 coarseSupport)
      (geometricSupportIds 6 fineSupport) := by
  unfold DyadicRootRefines
  refine sameSupport_trans
    (geometricSupportIds_sameSupport hfineBox) ?_
  rw [hrefine]
  exact sameSupport_symm
    (dyadicSupportCells_sameSupport
      (geometricSupportIds_sameSupport hcoarseBox))

theorem outwardXRoot_refines_fine :
    DyadicRootRefines 6 outwardXRoot outwardXFineRoot := by
  exact geometricFineRoot_refines outwardXSurface_subset_box_six
    outwardXFineSurface_subset_box_six outwardXFineSurface_eq_dyadic

theorem outwardYRoot_refines_fine :
    DyadicRootRefines 6 outwardYRoot outwardYFineRoot := by
  exact geometricFineRoot_refines outwardYSurface_subset_box_six
    outwardYFineSurface_subset_box_six outwardYFineSurface_eq_dyadic

theorem outwardZRoot_refines_fine :
    DyadicRootRefines 6 outwardZRoot outwardZFineRoot := by
  exact geometricFineRoot_refines outwardZSurface_subset_box_six
    outwardZFineSurface_subset_box_six outwardZFineSurface_eq_dyadic

theorem outwardXYRoot_refines_fine :
    DyadicRootRefines 6 outwardXYRoot outwardXYFineRoot := by
  exact geometricFineRoot_refines outwardXYSurface_subset_box_six
    outwardXYFineSurface_subset_box_six outwardXYFineSurface_eq_dyadic

theorem outwardXZRoot_refines_fine :
    DyadicRootRefines 6 outwardXZRoot outwardXZFineRoot := by
  exact geometricFineRoot_refines outwardXZSurface_subset_box_six
    outwardXZFineSurface_subset_box_six outwardXZFineSurface_eq_dyadic

theorem outwardYZRoot_refines_fine :
    DyadicRootRefines 6 outwardYZRoot outwardYZFineRoot := by
  exact geometricFineRoot_refines outwardYZSurface_subset_box_six
    outwardYZFineSurface_subset_box_six outwardYZFineSurface_eq_dyadic

theorem outwardXYZRoot_refines_fine :
    DyadicRootRefines 6 outwardXYZRoot outwardXYZFineRoot := by
  exact geometricFineRoot_refines outwardXYZSurface_subset_box_six
    outwardXYZFineSurface_subset_box_six outwardXYZFineSurface_eq_dyadic

/-- Every nonempty coarse outward pattern has its literal encoded dyadic
refinement in the same volume-six box. -/
theorem outwardNonemptyRoots_refine_fine :
    DyadicRootRefines 6 outwardXRoot outwardXFineRoot ∧
    DyadicRootRefines 6 outwardYRoot outwardYFineRoot ∧
    DyadicRootRefines 6 outwardZRoot outwardZFineRoot ∧
    DyadicRootRefines 6 outwardXYRoot outwardXYFineRoot ∧
    DyadicRootRefines 6 outwardXZRoot outwardXZFineRoot ∧
    DyadicRootRefines 6 outwardYZRoot outwardYZFineRoot ∧
    DyadicRootRefines 6 outwardXYZRoot outwardXYZFineRoot :=
  ⟨outwardXRoot_refines_fine, outwardYRoot_refines_fine,
    outwardZRoot_refines_fine, outwardXYRoot_refines_fine,
    outwardXZRoot_refines_fine, outwardYZRoot_refines_fine,
    outwardXYZRoot_refines_fine⟩

/-! ## 5. Canonical encoding and positive exact activities -/

private theorem fineGeometricRoot_mem_canonical
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

private def outwardXFineSurface_nonempty :
    Σ' plaquette : Z4Plaq, plaquette ∈ outwardXFineSurface :=
  ⟨dyadicCell
      (axisShiftPlaquette xAxisOffset (cubeFace .bottomXY)) .origin,
    fineCell_mem_axisFineCubeSurface xAxisOffset .bottomXY .origin⟩

private def outwardYFineSurface_nonempty :
    Σ' plaquette : Z4Plaq, plaquette ∈ outwardYFineSurface :=
  ⟨dyadicCell
      (axisShiftPlaquette yAxisOffset (cubeFace .bottomXY)) .origin,
    fineCell_mem_axisFineCubeSurface yAxisOffset .bottomXY .origin⟩

private def outwardZFineSurface_nonempty :
    Σ' plaquette : Z4Plaq, plaquette ∈ outwardZFineSurface :=
  ⟨dyadicCell
      (axisShiftPlaquette zAxisOffset (cubeFace .bottomXY)) .origin,
    fineCell_mem_axisFineCubeSurface zAxisOffset .bottomXY .origin⟩

theorem outwardXFineRoot_mem_canonical :
    outwardXFineRoot ∈ canonicalSurfacePolymers 6 := by
  exact fineGeometricRoot_mem_canonical
    outwardXFineSurface_subset_box_six outwardXFineSurface_nonempty
    outwardXFineSurface_connected

theorem outwardYFineRoot_mem_canonical :
    outwardYFineRoot ∈ canonicalSurfacePolymers 6 := by
  exact fineGeometricRoot_mem_canonical
    outwardYFineSurface_subset_box_six outwardYFineSurface_nonempty
    outwardYFineSurface_connected

theorem outwardZFineRoot_mem_canonical :
    outwardZFineRoot ∈ canonicalSurfacePolymers 6 := by
  exact fineGeometricRoot_mem_canonical
    outwardZFineSurface_subset_box_six outwardZFineSurface_nonempty
    outwardZFineSurface_connected

theorem outwardXYFineRoot_mem_canonical :
    outwardXYFineRoot ∈ canonicalSurfacePolymers 6 := by
  exact fineGeometricRoot_mem_canonical
    outwardXYFineSurface_subset_box_six
    ⟨outwardXFineSurface_nonempty.1,
      List.mem_append.mpr (Or.inl outwardXFineSurface_nonempty.2)⟩
    outwardXYFineSurface_connected

theorem outwardXZFineRoot_mem_canonical :
    outwardXZFineRoot ∈ canonicalSurfacePolymers 6 := by
  exact fineGeometricRoot_mem_canonical
    outwardXZFineSurface_subset_box_six
    ⟨outwardXFineSurface_nonempty.1,
      List.mem_append.mpr (Or.inl outwardXFineSurface_nonempty.2)⟩
    outwardXZFineSurface_connected

theorem outwardYZFineRoot_mem_canonical :
    outwardYZFineRoot ∈ canonicalSurfacePolymers 6 := by
  exact fineGeometricRoot_mem_canonical
    outwardYZFineSurface_subset_box_six
    ⟨outwardYFineSurface_nonempty.1,
      List.mem_append.mpr (Or.inl outwardYFineSurface_nonempty.2)⟩
    outwardYZFineSurface_connected

theorem outwardXYZFineRoot_mem_canonical :
    outwardXYZFineRoot ∈ canonicalSurfacePolymers 6 := by
  exact fineGeometricRoot_mem_canonical
    outwardXYZFineSurface_subset_box_six
    ⟨outwardXFineSurface_nonempty.1,
      List.mem_append.mpr
        (Or.inl (List.mem_append.mpr
          (Or.inl outwardXFineSurface_nonempty.2)))⟩
    outwardXYZFineSurface_connected

theorem outwardNonemptyFineRoots_mem_canonical :
    outwardXFineRoot ∈ canonicalSurfacePolymers 6 ∧
    outwardYFineRoot ∈ canonicalSurfacePolymers 6 ∧
    outwardZFineRoot ∈ canonicalSurfacePolymers 6 ∧
    outwardXYFineRoot ∈ canonicalSurfacePolymers 6 ∧
    outwardXZFineRoot ∈ canonicalSurfacePolymers 6 ∧
    outwardYZFineRoot ∈ canonicalSurfacePolymers 6 ∧
    outwardXYZFineRoot ∈ canonicalSurfacePolymers 6 :=
  ⟨outwardXFineRoot_mem_canonical, outwardYFineRoot_mem_canonical,
    outwardZFineRoot_mem_canonical, outwardXYFineRoot_mem_canonical,
    outwardXZFineRoot_mem_canonical, outwardYZFineRoot_mem_canonical,
    outwardXYZFineRoot_mem_canonical⟩

private theorem fineEvenFaceIncidence_geometricSupportIds
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

private theorem fineGeometricRoot_activity_pos
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
  exact fineEvenFaceIncidence_geometricSupportIds hbox hnodup hclosed

theorem outwardXFineRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      outwardXFineRoot := by
  exact fineGeometricRoot_activity_pos hcoupling
    outwardXFineSurface_subset_box_six outwardXFineSurface_nodup
    outwardXFineSurface_evenFaceIncidence

theorem outwardYFineRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      outwardYFineRoot := by
  exact fineGeometricRoot_activity_pos hcoupling
    outwardYFineSurface_subset_box_six outwardYFineSurface_nodup
    outwardYFineSurface_evenFaceIncidence

theorem outwardZFineRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      outwardZFineRoot := by
  exact fineGeometricRoot_activity_pos hcoupling
    outwardZFineSurface_subset_box_six outwardZFineSurface_nodup
    outwardZFineSurface_evenFaceIncidence

theorem outwardXYFineRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      outwardXYFineRoot := by
  exact fineGeometricRoot_activity_pos hcoupling
    outwardXYFineSurface_subset_box_six outwardXYFineSurface_nodup
    outwardXYFineSurface_evenFaceIncidence

theorem outwardXZFineRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      outwardXZFineRoot := by
  exact fineGeometricRoot_activity_pos hcoupling
    outwardXZFineSurface_subset_box_six outwardXZFineSurface_nodup
    outwardXZFineSurface_evenFaceIncidence

theorem outwardYZFineRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      outwardYZFineRoot := by
  exact fineGeometricRoot_activity_pos hcoupling
    outwardYZFineSurface_subset_box_six outwardYZFineSurface_nodup
    outwardYZFineSurface_evenFaceIncidence

theorem outwardXYZFineRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      outwardXYZFineRoot := by
  exact fineGeometricRoot_activity_pos hcoupling
    outwardXYZFineSurface_subset_box_six outwardXYZFineSurface_nodup
    outwardXYZFineSurface_evenFaceIncidence

theorem outwardNonemptyFineRoots_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6 outwardXFineRoot ∧
    (0 : Q') < canonicalSurfaceActivity coupling 6 outwardYFineRoot ∧
    (0 : Q') < canonicalSurfaceActivity coupling 6 outwardZFineRoot ∧
    (0 : Q') < canonicalSurfaceActivity coupling 6 outwardXYFineRoot ∧
    (0 : Q') < canonicalSurfaceActivity coupling 6 outwardXZFineRoot ∧
    (0 : Q') < canonicalSurfaceActivity coupling 6 outwardYZFineRoot ∧
    (0 : Q') < canonicalSurfaceActivity coupling 6 outwardXYZFineRoot :=
  ⟨outwardXFineRoot_activity_pos hcoupling,
    outwardYFineRoot_activity_pos hcoupling,
    outwardZFineRoot_activity_pos hcoupling,
    outwardXYFineRoot_activity_pos hcoupling,
    outwardXZFineRoot_activity_pos hcoupling,
    outwardYZFineRoot_activity_pos hcoupling,
    outwardXYZFineRoot_activity_pos hcoupling⟩

#print axioms outwardXFineSurface_evenFaceIncidence
#print axioms outwardZFineSurface_subset_box_six
#print axioms outwardXYZFineSurface_nodup
#print axioms outwardXYZFineSurface_connected
#print axioms outwardNonemptyRoots_refine_fine
#print axioms outwardNonemptyFineRoots_mem_canonical
#print axioms outwardNonemptyFineRoots_activity_pos

end YMGap.Continuum.Z4OutwardThreeCubeFineCarrier
