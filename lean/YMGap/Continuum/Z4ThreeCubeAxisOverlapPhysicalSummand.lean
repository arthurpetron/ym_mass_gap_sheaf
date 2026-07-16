/-
# A genuine three-cube mixed physical summand

The one-cube three-face projector has only the diagonal patterns `000` and
`111`.  This module passes to the smallest closed-surface enlargement: three
unit-cube boundaries based at `(1,0,0)`, `(0,1,0)`, and `(0,0,0)`.  After
dyadic refinement the first and third cubes share an entire `YZ` face, the
second and third share an entire `XZ` face, and the first two share a literal
`z`-link.  All six roots are canonical in one volume-six box and the three
fine roots are exact dyadic refinements of the coarse roots.

For the mixed `001` summand we use the component labelling of the unshifted
right cube.  Its exact positive activity is already known; transport to the
common volume preserves it.  The two translated cube roots are distinct from
the right root, so their occurrence bits are false while the right bit is
true.  This constructs the previously abstract fine/coarse physical summand
input without an assumed amplitude.
-/

import YMGap.Continuum.Z4ThreeBlockPhysicalCubeLeakage
import YMGap.Continuum.Z4CoarseUnitCubeActivity

namespace YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand

set_option maxRecDepth 100000
set_option maxHeartbeats 500000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CoarseUnitCubeActivity
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricCanonicalRootOccurrence
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeBlockPhysicalCubeLeakage
open YMGap.Continuum.Z4UnitCubeBareCouplingShift
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Coordinatewise positive translations -/

structure AxisOffset where
  x : Nat
  y : Nat
  z : Nat
  t : Nat
deriving DecidableEq

def axisShiftVertex (offset : AxisOffset) : Z4Vertex → Z4Vertex
  | (a, b, c, d) =>
      (a + offset.x, b + offset.y, c + offset.z, d + offset.t)

def axisShiftLink (offset : AxisOffset) (link : Z4Link) : Z4Link :=
  (axisShiftVertex offset link.1, link.2)

def axisShiftPlaquette (offset : AxisOffset) (plaquette : Z4Plaq) : Z4Plaq :=
  (axisShiftVertex offset plaquette.1, plaquette.2)

def doubleAxisOffset (offset : AxisOffset) : AxisOffset :=
  ⟨2 * offset.x, 2 * offset.y, 2 * offset.z, 2 * offset.t⟩

def zeroAxisOffset : AxisOffset := ⟨0, 0, 0, 0⟩
def xAxisOffset : AxisOffset := ⟨1, 0, 0, 0⟩
def yAxisOffset : AxisOffset := ⟨0, 1, 0, 0⟩

theorem axisShiftVertex_injective (offset : AxisOffset) :
    Function.Injective (axisShiftVertex offset) := by
  intro left right heq
  obtain ⟨a, b, c, d⟩ := left
  obtain ⟨a', b', c', d'⟩ := right
  simp only [axisShiftVertex, Prod.mk.injEq] at heq ⊢
  exact ⟨Nat.add_right_cancel heq.1,
    Nat.add_right_cancel heq.2.1,
    Nat.add_right_cancel heq.2.2.1,
    Nat.add_right_cancel heq.2.2.2⟩

theorem axisShiftPlaquette_injective (offset : AxisOffset) :
    Function.Injective (axisShiftPlaquette offset) := by
  intro left right heq
  apply Prod.ext
  · apply axisShiftVertex_injective offset
    simpa only [axisShiftPlaquette] using congrArg Prod.fst heq
  · simpa only [axisShiftPlaquette] using congrArg Prod.snd heq

theorem axisShiftVertex_addE
    (offset : AxisOffset) (vertex : Z4Vertex) (direction : Dir4) :
    axisShiftVertex offset (addE vertex direction) =
      addE (axisShiftVertex offset vertex) direction := by
  obtain ⟨a, b, c, d⟩ := vertex
  cases direction <;> simp [axisShiftVertex, addE] <;> omega

theorem edgesOf_axisShiftPlaquette
    (offset : AxisOffset) (plaquette : Z4Plaq) :
    edgesOf (axisShiftPlaquette offset plaquette) =
      (edgesOf plaquette).map (axisShiftLink offset) := by
  simp [edgesOf, axisShiftPlaquette, axisShiftLink,
    axisShiftVertex_addE]

def axisShiftAdjacent (offset : AxisOffset) {left right : Z4Plaq}
    (adjacent : z4Chain.toLattice.Adjacent left right) :
    z4Chain.toLattice.Adjacent
      (axisShiftPlaquette offset left)
      (axisShiftPlaquette offset right) := by
  refine {
    link := axisShiftLink offset adjacent.link
    on_p := ?_
    on_q := ?_
  }
  · change z4Boundary (axisShiftPlaquette offset left)
      (axisShiftLink offset adjacent.link) = true
    unfold z4Boundary
    rw [edgesOf_axisShiftPlaquette]
    apply decide_eq_true
    exact List.mem_map.mpr
      ⟨adjacent.link, of_decide_eq_true adjacent.on_p, rfl⟩
  · change z4Boundary (axisShiftPlaquette offset right)
      (axisShiftLink offset adjacent.link) = true
    unfold z4Boundary
    rw [edgesOf_axisShiftPlaquette]
    apply decide_eq_true
    exact List.mem_map.mpr
      ⟨adjacent.link, of_decide_eq_true adjacent.on_q, rfl⟩

def axisShiftChain (offset : AxisOffset) {support : List Z4Plaq} :
    {first last : Z4Plaq} →
      ChainIn z4Chain.toLattice support first last →
      ChainIn z4Chain.toLattice
        (support.map (axisShiftPlaquette offset))
        (axisShiftPlaquette offset first)
        (axisShiftPlaquette offset last)
  | _, _, .refl _ => .refl _
  | _, _, .step adjacent hnext rest =>
      .step (axisShiftAdjacent offset adjacent)
        (List.mem_map.mpr ⟨_, hnext, rfl⟩)
        (axisShiftChain offset rest)

def axisShiftConnected (offset : AxisOffset) {support : List Z4Plaq}
    (hconnected : connectedIn (L := z4Chain.toLattice) support) :
    connectedIn (L := z4Chain.toLattice)
      (support.map (axisShiftPlaquette offset)) := by
  intro first last hfirst hlast
  obtain ⟨sourceFirst, hsourceFirst, rfl⟩ :=
    decodeMapMember (axisShiftPlaquette offset) support first hfirst
  obtain ⟨sourceLast, hsourceLast, rfl⟩ :=
    decodeMapMember (axisShiftPlaquette offset) support last hlast
  exact axisShiftChain offset
    (hconnected sourceFirst sourceLast hsourceFirst hsourceLast)

theorem axisShiftPlaquette_mem_extended_box
    {base : Nat} (offset : AxisOffset) {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes base) :
    axisShiftPlaquette offset plaquette ∈
      boxPlaquettes (base + offset.x + offset.y + offset.z + offset.t) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  rw [mem_boxPlaquettes] at hplaquette ⊢
  change a < base ∧ b < base ∧ c < base ∧ d < base at hplaquette
  simp only [axisShiftPlaquette, axisShiftVertex]
  exact ⟨by omega, by omega, by omega, by omega⟩

/-! ## 2. Translation commutes with dyadic refinement -/

theorem axisShiftPlaquette_dyadicCell
    (offset : AxisOffset) (plaquette : Z4Plaq)
    (index : DyadicCellIndex) :
    axisShiftPlaquette (doubleAxisOffset offset)
        (dyadicCell plaquette index) =
      dyadicCell (axisShiftPlaquette offset plaquette) index := by
  obtain ⟨ox, oy, oz, ot⟩ := offset
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  cases index <;> cases plane <;>
    simp [axisShiftPlaquette, axisShiftVertex, doubleAxisOffset,
      dyadicCell, dyadicVertex, addE, dirsOf, Nat.mul_add,
      Nat.add_comm, Nat.add_left_comm]

theorem dyadicPlaquetteCells_axisShift
    (offset : AxisOffset) (plaquette : Z4Plaq) :
    dyadicPlaquetteCells (axisShiftPlaquette offset plaquette) =
      (dyadicPlaquetteCells plaquette).map
        (axisShiftPlaquette (doubleAxisOffset offset)) := by
  unfold dyadicPlaquetteCells
  simp only [List.map_map]
  apply List.map_congr_left
  intro index hindex
  exact (axisShiftPlaquette_dyadicCell offset plaquette index).symm

theorem dyadicSupportCells_axisShift
    (offset : AxisOffset) : ∀ support : List Z4Plaq,
    dyadicSupportCells
        (support.map (axisShiftPlaquette offset)) =
      (dyadicSupportCells support).map
        (axisShiftPlaquette (doubleAxisOffset offset))
  | [] => rfl
  | plaquette :: rest => by
      unfold dyadicSupportCells
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [dyadicPlaquetteCells_axisShift]
      congr 1
      exact dyadicSupportCells_axisShift offset rest

/-! ## 3. The three coarse and fine supports in one box -/

def axisCubeSurface (offset : AxisOffset) : List Z4Plaq :=
  unitCubeSurface.map (axisShiftPlaquette offset)

def axisFineCubeSurface (offset : AxisOffset) : List Z4Plaq :=
  dyadicSupportCells (axisCubeSurface offset)

def axisCoarseRoot (offset : AxisOffset) : List Nat :=
  geometricSupportIds 6 (axisCubeSurface offset)

def axisFineRoot (offset : AxisOffset) : List Nat :=
  geometricSupportIds 6 (axisFineCubeSurface offset)

def threeAxisCoarseRoots : PhysicalCubeRootTriple :=
  (axisCoarseRoot xAxisOffset,
    axisCoarseRoot yAxisOffset, axisCoarseRoot zeroAxisOffset)

def threeAxisFineRoots : PhysicalCubeRootTriple :=
  (axisFineRoot xAxisOffset,
    axisFineRoot yAxisOffset, axisFineRoot zeroAxisOffset)

theorem axisCubeSurface_subset_box_six
    (offset : AxisOffset)
    (hoffset : offset = zeroAxisOffset ∨
      offset = xAxisOffset ∨ offset = yAxisOffset) :
    ∀ plaquette, plaquette ∈ axisCubeSurface offset →
      plaquette ∈ boxPlaquettes 6 := by
  intro plaquette hplaquette
  obtain ⟨source, hsource, rfl⟩ :=
    decodeMapMember (axisShiftPlaquette offset)
      unitCubeSurface plaquette hplaquette
  rcases hoffset with rfl | rfl | rfl
  · exact boxPlaquettes_mono (by simp [zeroAxisOffset])
      (axisShiftPlaquette_mem_extended_box zeroAxisOffset
        (unitCubeSurface_subset_box_two source hsource))
  · exact boxPlaquettes_mono (by simp [xAxisOffset])
      (axisShiftPlaquette_mem_extended_box xAxisOffset
        (unitCubeSurface_subset_box_two source hsource))
  · exact boxPlaquettes_mono (by simp [yAxisOffset])
      (axisShiftPlaquette_mem_extended_box yAxisOffset
        (unitCubeSurface_subset_box_two source hsource))

theorem axisCubeSurface_subset_box_three
    (offset : AxisOffset)
    (hoffset : offset = zeroAxisOffset ∨
      offset = xAxisOffset ∨ offset = yAxisOffset) :
    ∀ plaquette, plaquette ∈ axisCubeSurface offset →
      plaquette ∈ boxPlaquettes 3 := by
  intro plaquette hplaquette
  obtain ⟨source, hsource, rfl⟩ :=
    decodeMapMember (axisShiftPlaquette offset)
      unitCubeSurface plaquette hplaquette
  rcases hoffset with rfl | rfl | rfl
  · exact boxPlaquettes_mono (by simp [zeroAxisOffset])
      (axisShiftPlaquette_mem_extended_box zeroAxisOffset
        (unitCubeSurface_subset_box_two source hsource))
  · simpa using axisShiftPlaquette_mem_extended_box xAxisOffset
      (unitCubeSurface_subset_box_two source hsource)
  · simpa using axisShiftPlaquette_mem_extended_box yAxisOffset
      (unitCubeSurface_subset_box_two source hsource)

theorem axisFineCubeSurface_subset_box_six
    (offset : AxisOffset)
    (hoffset : offset = zeroAxisOffset ∨
      offset = xAxisOffset ∨ offset = yAxisOffset) :
    ∀ plaquette, plaquette ∈ axisFineCubeSurface offset →
      plaquette ∈ boxPlaquettes 6 := by
  exact dyadicSupportCells_subset_double_box
    (axisCubeSurface_subset_box_three offset hoffset)

def axisCubeSurface_connected (offset : AxisOffset) :
    connectedIn (L := z4Chain.toLattice) (axisCubeSurface offset) :=
  axisShiftConnected offset unitCubeSurface_connected

def axisFineCubeSurface_connected (offset : AxisOffset) :
    connectedIn (L := z4Chain.toLattice)
      (axisFineCubeSurface offset) := by
  unfold axisFineCubeSurface axisCubeSurface
  rw [dyadicSupportCells_axisShift]
  exact axisShiftConnected (doubleAxisOffset offset)
    refinedUnitCubeSurface_connected

private theorem geometricRoot_mem_canonical
    {support : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes 6)
    (hnonempty : Σ' plaquette : Z4Plaq, plaquette ∈ support)
    (hconnected : connectedIn (L := z4Chain.toLattice) support) :
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

theorem axisCoarseRoot_mem_canonical
    (offset : AxisOffset)
    (hoffset : offset = zeroAxisOffset ∨
      offset = xAxisOffset ∨ offset = yAxisOffset) :
    axisCoarseRoot offset ∈ canonicalSurfacePolymers 6 := by
  unfold axisCoarseRoot
  apply geometricRoot_mem_canonical
    (axisCubeSurface_subset_box_six offset hoffset)
  · exact ⟨axisShiftPlaquette offset (cubeFace .bottomXY),
      List.mem_map.mpr
        ⟨cubeFace .bottomXY,
          cubeFace_mem_unitCubeSurface .bottomXY, rfl⟩⟩
  · exact axisCubeSurface_connected offset

theorem axisFineRoot_mem_canonical
    (offset : AxisOffset)
    (hoffset : offset = zeroAxisOffset ∨
      offset = xAxisOffset ∨ offset = yAxisOffset) :
    axisFineRoot offset ∈ canonicalSurfacePolymers 6 := by
  unfold axisFineRoot
  apply geometricRoot_mem_canonical
    (axisFineCubeSurface_subset_box_six offset hoffset)
  · refine ⟨dyadicCell
        (axisShiftPlaquette offset (cubeFace .bottomXY)) .origin, ?_⟩
    unfold axisFineCubeSurface
    apply (mem_dyadicSupportCells_iff _ _).mpr
    exact ⟨axisShiftPlaquette offset (cubeFace .bottomXY),
      List.mem_map.mpr
        ⟨cubeFace .bottomXY,
          cubeFace_mem_unitCubeSurface .bottomXY, rfl⟩,
      dyadicCell_mem_cells _ _⟩
  · exact axisFineCubeSurface_connected offset

theorem axisCoarseRoot_sameSupport
    (offset : AxisOffset)
    (hoffset : offset = zeroAxisOffset ∨
      offset = xAxisOffset ∨ offset = yAxisOffset) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 (axisCoarseRoot offset))
      (axisCubeSurface offset) := by
  unfold axisCoarseRoot
  exact geometricSupportIds_sameSupport
    (axisCubeSurface_subset_box_six offset hoffset)

theorem axisFineRoot_sameSupport
    (offset : AxisOffset)
    (hoffset : offset = zeroAxisOffset ∨
      offset = xAxisOffset ∨ offset = yAxisOffset) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 (axisFineRoot offset))
      (axisFineCubeSurface offset) := by
  unfold axisFineRoot
  exact geometricSupportIds_sameSupport
    (axisFineCubeSurface_subset_box_six offset hoffset)

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

theorem axisRoot_refines
    (offset : AxisOffset)
    (hoffset : offset = zeroAxisOffset ∨
      offset = xAxisOffset ∨ offset = yAxisOffset) :
    DyadicRootRefines 6 (axisCoarseRoot offset) (axisFineRoot offset) := by
  unfold DyadicRootRefines
  refine sameSupport_trans
    (axisFineRoot_sameSupport offset hoffset) ?_
  unfold axisFineCubeSurface
  exact sameSupport_symm
    (dyadicSupportCells_sameSupport
      (axisCoarseRoot_sameSupport offset hoffset))

/-! ## 4. Three literal fine-support overlaps -/

theorem axisFineCell_mem_geometricRoot
    (offset : AxisOffset)
    (hoffset : offset = zeroAxisOffset ∨
      offset = xAxisOffset ∨ offset = yAxisOffset)
    (face : CubeFaceIndex) (index : DyadicCellIndex) :
    dyadicCell (axisShiftPlaquette offset (cubeFace face)) index ∈
      geometricPolymer 6 (axisFineRoot offset) := by
  apply (axisFineRoot_sameSupport offset hoffset).2
  unfold axisFineCubeSurface
  apply (mem_dyadicSupportCells_iff _ _).mpr
  exact ⟨axisShiftPlaquette offset (cubeFace face),
    List.mem_map.mpr
      ⟨cubeFace face, cubeFace_mem_unitCubeSurface face, rfl⟩,
    dyadicCell_mem_cells _ _⟩

/-- The x-shifted and y-shifted refined cubes meet on the literal z-link
`((2,2,0,0), x2)`. -/
theorem fineXAxisYAxis_shareProductionLink :
    CanonicalRootsShareProductionLink 6
      (axisFineRoot xAxisOffset) (axisFineRoot yAxisOffset) := by
  let leftFace : Z4Plaq :=
    dyadicCell
      (axisShiftPlaquette xAxisOffset (cubeFace .leftYZ)) .first
  let rightFace : Z4Plaq :=
    dyadicCell
      (axisShiftPlaquette yAxisOffset (cubeFace .frontXZ)) .first
  let sharedLink : Z4Link := ((2, 2, 0, 0), .x2)
  refine ⟨leftFace, ?_, rightFace, ?_, sharedLink, ?_, ?_⟩
  · exact axisFineCell_mem_geometricRoot xAxisOffset
      (Or.inr (Or.inl rfl)) .leftYZ .first
  · exact axisFineCell_mem_geometricRoot yAxisOffset
      (Or.inr (Or.inr rfl)) .frontXZ .first
  · simp [leftFace, sharedLink, axisShiftPlaquette, axisShiftVertex,
      xAxisOffset, cubeFace, dyadicCell, dyadicVertex, dirsOf, addE, edgesOf]
  · simp [rightFace, sharedLink, axisShiftPlaquette, axisShiftVertex,
      yAxisOffset, cubeFace, dyadicCell, dyadicVertex, dirsOf, addE, edgesOf]

/-- The x-shifted and unshifted refined cubes share the complete face at
`x = 2`; this records one of its y-links. -/
theorem fineXAxisZero_shareProductionLink :
    CanonicalRootsShareProductionLink 6
      (axisFineRoot xAxisOffset) (axisFineRoot zeroAxisOffset) := by
  let leftFace : Z4Plaq :=
    dyadicCell
      (axisShiftPlaquette xAxisOffset (cubeFace .leftYZ)) .origin
  let rightFace : Z4Plaq :=
    dyadicCell
      (axisShiftPlaquette zeroAxisOffset (cubeFace .rightYZ)) .origin
  let sharedLink : Z4Link := ((2, 0, 0, 0), .x1)
  refine ⟨leftFace, ?_, rightFace, ?_, sharedLink, ?_, ?_⟩
  · exact axisFineCell_mem_geometricRoot xAxisOffset
      (Or.inr (Or.inl rfl)) .leftYZ .origin
  · exact axisFineCell_mem_geometricRoot zeroAxisOffset
      (Or.inl rfl) .rightYZ .origin
  · simp [leftFace, sharedLink, axisShiftPlaquette, axisShiftVertex,
      xAxisOffset, cubeFace, dyadicCell, dyadicVertex, dirsOf, addE, edgesOf]
  · simp [rightFace, sharedLink, axisShiftPlaquette, axisShiftVertex,
      zeroAxisOffset, cubeFace, dyadicCell, dyadicVertex, dirsOf, addE,
      edgesOf]

/-- The y-shifted and unshifted refined cubes share the complete face at
`y = 2`; this records one of its x-links. -/
theorem fineYAxisZero_shareProductionLink :
    CanonicalRootsShareProductionLink 6
      (axisFineRoot yAxisOffset) (axisFineRoot zeroAxisOffset) := by
  let leftFace : Z4Plaq :=
    dyadicCell
      (axisShiftPlaquette yAxisOffset (cubeFace .frontXZ)) .origin
  let rightFace : Z4Plaq :=
    dyadicCell
      (axisShiftPlaquette zeroAxisOffset (cubeFace .backXZ)) .origin
  let sharedLink : Z4Link := ((0, 2, 0, 0), .x0)
  refine ⟨leftFace, ?_, rightFace, ?_, sharedLink, ?_, ?_⟩
  · exact axisFineCell_mem_geometricRoot yAxisOffset
      (Or.inr (Or.inr rfl)) .frontXZ .origin
  · exact axisFineCell_mem_geometricRoot zeroAxisOffset
      (Or.inl rfl) .backXZ .origin
  · simp [leftFace, sharedLink, axisShiftPlaquette, axisShiftVertex,
      yAxisOffset, cubeFace, dyadicCell, dyadicVertex, dirsOf, addE, edgesOf]
  · simp [rightFace, sharedLink, axisShiftPlaquette, axisShiftVertex,
      zeroAxisOffset, cubeFace, dyadicCell, dyadicVertex, dirsOf, addE,
      edgesOf]

/-- The actual six-root volume-six witness required by the physical leakage
interface.  Root order is x-shifted, y-shifted, unshifted. -/
def axisCubeBlockRootData
    (left shared right : AxisOffset)
    (hleft : left = zeroAxisOffset ∨
      left = xAxisOffset ∨ left = yAxisOffset)
    (hshared : shared = zeroAxisOffset ∨
      shared = xAxisOffset ∨ shared = yAxisOffset)
    (hright : right = zeroAxisOffset ∨
      right = xAxisOffset ∨ right = yAxisOffset)
    (hleftShared : CanonicalRootsShareProductionLink 6
      (axisFineRoot left) (axisFineRoot shared))
    (hleftRight : CanonicalRootsShareProductionLink 6
      (axisFineRoot left) (axisFineRoot right))
    (hsharedRight : CanonicalRootsShareProductionLink 6
      (axisFineRoot shared) (axisFineRoot right)) :
    ThreeCubeBlockRootData 6 where
  coarseRoots :=
    (axisCoarseRoot left, axisCoarseRoot shared, axisCoarseRoot right)
  fineRoots :=
    (axisFineRoot left, axisFineRoot shared, axisFineRoot right)
  coarseLeftCanonical := axisCoarseRoot_mem_canonical left hleft
  coarseSharedCanonical := axisCoarseRoot_mem_canonical shared hshared
  coarseRightCanonical := axisCoarseRoot_mem_canonical right hright
  fineLeftCanonical := axisFineRoot_mem_canonical left hleft
  fineSharedCanonical := axisFineRoot_mem_canonical shared hshared
  fineRightCanonical := axisFineRoot_mem_canonical right hright
  leftRefines := axisRoot_refines left hleft
  sharedRefines := axisRoot_refines shared hshared
  rightRefines := axisRoot_refines right hright
  fineLeftSharedOverlap := hleftShared
  fineLeftRightOverlap := hleftRight
  fineSharedRightOverlap := hsharedRight

def threeAxisCubeBlockRootData : ThreeCubeBlockRootData 6 :=
  axisCubeBlockRootData xAxisOffset yAxisOffset zeroAxisOffset
    (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inl rfl)
    fineXAxisYAxis_shareProductionLink
    fineXAxisZero_shareProductionLink
    fineYAxisZero_shareProductionLink

/-! ## 5. The two shifted bits are false on the unshifted component label -/

theorem axisCubeSurface_zero_eq :
    axisCubeSurface zeroAxisOffset = unitCubeSurface := by
  rfl

theorem axisFineCubeSurface_zero_eq :
    axisFineCubeSurface zeroAxisOffset = refinedUnitCubeSurface := by
  rfl

def xOuterCoarseFace : Z4Plaq :=
  axisShiftPlaquette xAxisOffset (cubeFace .rightYZ)

def yOuterCoarseFace : Z4Plaq :=
  axisShiftPlaquette yAxisOffset (cubeFace .backXZ)

theorem xOuterCoarseFace_mem_x :
    xOuterCoarseFace ∈ axisCubeSurface xAxisOffset := by
  exact List.mem_map.mpr
    ⟨cubeFace .rightYZ, cubeFace_mem_unitCubeSurface .rightYZ, rfl⟩

theorem yOuterCoarseFace_mem_y :
    yOuterCoarseFace ∈ axisCubeSurface yAxisOffset := by
  exact List.mem_map.mpr
    ⟨cubeFace .backXZ, cubeFace_mem_unitCubeSurface .backXZ, rfl⟩

theorem xOuterCoarseFace_not_mem_zero :
    xOuterCoarseFace ∉ axisCubeSurface zeroAxisOffset := by
  simp [xOuterCoarseFace, axisCubeSurface, unitCubeSurface,
    axisShiftPlaquette, axisShiftVertex, xAxisOffset, zeroAxisOffset,
    cubeFace]

theorem yOuterCoarseFace_not_mem_zero :
    yOuterCoarseFace ∉ axisCubeSurface zeroAxisOffset := by
  simp [yOuterCoarseFace, axisCubeSurface, unitCubeSurface,
    axisShiftPlaquette, axisShiftVertex, yAxisOffset, zeroAxisOffset,
    cubeFace]

private theorem dyadicOrigin_not_mem_of_parent_not_mem
    {plaquette : Z4Plaq} {support : List Z4Plaq}
    (hnot : plaquette ∉ support) :
    dyadicCell plaquette .origin ∉ dyadicSupportCells support := by
  intro hcell
  obtain ⟨source, hsource, hlocal⟩ :=
    (mem_dyadicSupportCells_iff support _).mp hcell
  unfold dyadicPlaquetteCells at hlocal
  obtain ⟨index, _, heq⟩ := List.mem_map.mp hlocal
  have hparents : plaquette = source :=
    (dyadicCell_injective heq.symm).1
  exact hnot (hparents.symm ▸ hsource)

private theorem roots_ne_of_geometric_witness
    {left right : List Nat} {leftSupport rightSupport : List Z4Plaq}
    (hleft : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 left) leftSupport)
    (hright : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 right) rightSupport)
    (face : Z4Plaq) (hface : face ∈ leftSupport)
    (hnot : face ∉ rightSupport) : left ≠ right := by
  intro heq
  have hdecoded := hleft.2 face hface
  rw [heq] at hdecoded
  exact hnot (hright.1 face hdecoded)

theorem coarseXAxisRoot_ne_zeroRoot :
    axisCoarseRoot xAxisOffset ≠ axisCoarseRoot zeroAxisOffset :=
  roots_ne_of_geometric_witness
    (axisCoarseRoot_sameSupport xAxisOffset (Or.inr (Or.inl rfl)))
    (axisCoarseRoot_sameSupport zeroAxisOffset (Or.inl rfl))
    xOuterCoarseFace xOuterCoarseFace_mem_x
    xOuterCoarseFace_not_mem_zero

theorem coarseYAxisRoot_ne_zeroRoot :
    axisCoarseRoot yAxisOffset ≠ axisCoarseRoot zeroAxisOffset :=
  roots_ne_of_geometric_witness
    (axisCoarseRoot_sameSupport yAxisOffset (Or.inr (Or.inr rfl)))
    (axisCoarseRoot_sameSupport zeroAxisOffset (Or.inl rfl))
    yOuterCoarseFace yOuterCoarseFace_mem_y
    yOuterCoarseFace_not_mem_zero

theorem fineXAxisRoot_ne_zeroRoot :
    axisFineRoot xAxisOffset ≠ axisFineRoot zeroAxisOffset := by
  apply roots_ne_of_geometric_witness
    (axisFineRoot_sameSupport xAxisOffset (Or.inr (Or.inl rfl)))
    (axisFineRoot_sameSupport zeroAxisOffset (Or.inl rfl))
    (dyadicCell xOuterCoarseFace .origin)
  · unfold axisFineCubeSurface
    exact (mem_dyadicSupportCells_iff _ _).mpr
      ⟨xOuterCoarseFace, xOuterCoarseFace_mem_x,
        dyadicCell_mem_cells _ _⟩
  · unfold axisFineCubeSurface
    exact dyadicOrigin_not_mem_of_parent_not_mem
      xOuterCoarseFace_not_mem_zero

theorem fineYAxisRoot_ne_zeroRoot :
    axisFineRoot yAxisOffset ≠ axisFineRoot zeroAxisOffset := by
  apply roots_ne_of_geometric_witness
    (axisFineRoot_sameSupport yAxisOffset (Or.inr (Or.inr rfl)))
    (axisFineRoot_sameSupport zeroAxisOffset (Or.inl rfl))
    (dyadicCell yOuterCoarseFace .origin)
  · unfold axisFineCubeSurface
    exact (mem_dyadicSupportCells_iff _ _).mpr
      ⟨yOuterCoarseFace, yOuterCoarseFace_mem_y,
        dyadicCell_mem_cells _ _⟩
  · unfold axisFineCubeSurface
    exact dyadicOrigin_not_mem_of_parent_not_mem
      yOuterCoarseFace_not_mem_zero

/-! ## 6. Exact orientation of the mixed component label -/

private theorem nil_mem_sublists_local {A : Type} :
    ∀ ambient : List A, [] ∈ sublists ambient
  | [] => List.mem_cons_self
  | _ :: tail => by
      rw [sublists_cons']
      exact List.mem_append_left _ (nil_mem_sublists_local tail)

private theorem singleton_mem_sublists_of_mem_local {A : Type}
    (ambient : List A) (item : A) (hitem : item ∈ ambient) :
    [item] ∈ sublists ambient := by
  induction ambient with
  | nil => exact absurd hitem List.not_mem_nil
  | cons head tail ih =>
      rw [sublists_cons']
      rcases List.mem_cons.mp hitem with rfl | htail
      · apply List.mem_append_right
        exact List.mem_map.mpr
          ⟨[], nil_mem_sublists_local tail, rfl⟩
      · exact List.mem_append_left _ (ih htail)

private theorem singleton_mem_compatibleAmbient
    {n : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers n) :
    [root] ∈ canonicalCompatibleAmbientFamilies n := by
  unfold canonicalCompatibleAmbientFamilies
  apply List.mem_filter.mpr
  exact ⟨singleton_mem_sublists_of_mem_local
      (canonicalSurfacePolymers n) root hroot, rfl⟩

/-- A connected canonical root's literal component label decodes to exactly
the singleton family containing that root. -/
theorem componentLabelAmbientFamily_eq_singleton
    {n : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers n) :
    physicalCanonicalAmbientFamily n (componentLabel root) = [root] := by
  have hfamily := singleton_mem_compatibleAmbient hroot
  have hordered := compatibleAmbientFamily_eq_unionAmbientOrdered hfamily
  rw [familyUnionSupport_singleton_eq hroot] at hordered
  have hsupport := canonicalSurfacePolymer_mem_faceSupports hroot
  rw [physicalCanonicalAmbientFamily_componentLabel hsupport]
  exact hordered

theorem componentLabel_rootOccurrence_false_of_ne
    {n : Nat} {candidate root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers n)
    (hne : candidate ≠ root) :
    physicalRootOccurrenceEvent n candidate (componentLabel root) = false := by
  unfold physicalRootOccurrenceEvent cutoffOneLiftedFamilyEvent
  rw [componentLabelAmbientFamily_eq_singleton hroot]
  simp [familyContainsPolymerB, hne]

theorem componentLabel_rootOccurrence_true
    {n : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers n) :
    physicalRootOccurrenceEvent n root (componentLabel root) = true := by
  unfold physicalRootOccurrenceEvent cutoffOneLiftedFamilyEvent
  rw [componentLabelAmbientFamily_eq_singleton hroot]
  simp [familyContainsPolymerB]

/-- A small projection lemma keeps the enormous physical state-space fields
opaque when reading the three event coordinates. -/
theorem normalizedPhysicalThreeRootPattern_eq
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (roots : PhysicalCubeRootTriple)
    (physical : EdgeLabelling) :
    threeBlockPattern
        (normalizedPhysicalThreeRootLaw coupling hcoupling
          cutoff volume roots) physical =
      (physicalRootTripleLeftEvent volume roots physical,
        physicalRootTripleSharedEvent volume roots physical,
        physicalRootTripleRightEvent volume roots physical) := by
  rfl

/-- The orientation is explicit: the first (x-shifted) and second
(y-shifted) roots are false, and the third (unshifted) root is true. -/
theorem componentLabel_threeRootPattern_001
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat)
    (left shared right : List Nat)
    (hright : right ∈ canonicalSurfacePolymers n)
    (hleft : left ≠ right) (hshared : shared ≠ right) :
    threeBlockPattern
        (normalizedPhysicalThreeRootLaw coupling hcoupling cutoff n
          (left, shared, right))
        (componentLabel right) = (false, false, true) := by
  rw [normalizedPhysicalThreeRootPattern_eq]
  change
    (physicalRootOccurrenceEvent n left (componentLabel right),
      physicalRootOccurrenceEvent n shared (componentLabel right),
      physicalRootOccurrenceEvent n right (componentLabel right)) =
        (false, false, true)
  rw [componentLabel_rootOccurrence_false_of_ne hright hleft,
    componentLabel_rootOccurrence_false_of_ne hright hshared,
    componentLabel_rootOccurrence_true hright]

/-! ## 7. Exact positive unshifted fine/coarse summands -/

theorem zeroAxisCoarseRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      (axisCoarseRoot zeroAxisOffset) := by
  have htarget := axisCoarseRoot_sameSupport zeroAxisOffset (Or.inl rfl)
  rw [axisCubeSurface_zero_eq] at htarget
  have hsame := sameSupport_trans coarseUnitCubeSupportIds_sameSupport
    (sameSupport_symm htarget)
  have hcross := canonicalSurfaceActivity_cross_volume coupling
    coarseUnitCubeSupportIds_mem_cutoffOneFaceSupports
    (canonicalSurfacePolymer_mem_faceSupports
      (axisCoarseRoot_mem_canonical zeroAxisOffset (Or.inl rfl)))
    hsame
  exact Q'.pos_of_lt_of_le
    (coarseUnitCube_canonicalSurfaceActivity_pos hcoupling)
    (Q'.le_of_eqv hcross)

theorem zeroAxisFineRoot_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 6
      (axisFineRoot zeroAxisOffset) := by
  have htarget := axisFineRoot_sameSupport zeroAxisOffset (Or.inl rfl)
  rw [axisFineCubeSurface_zero_eq] at htarget
  have hsame := sameSupport_trans dyadicUnitCubeSupportIds_sameSupport
    (sameSupport_symm htarget)
  have hcross := canonicalSurfaceActivity_cross_volume coupling
    dyadicUnitCubeSupportIds_mem_cutoffOneFaceSupports
    (canonicalSurfacePolymer_mem_faceSupports
      (axisFineRoot_mem_canonical zeroAxisOffset (Or.inl rfl)))
    hsame
  exact Q'.pos_of_lt_of_le
    (dyadicUnitCube_canonicalSurfaceActivity_pos hcoupling)
    (Q'.le_of_eqv hcross)

theorem canonicalRootComponentPhysicalTerm_pos
    {coupling : Q'} {cutoff n : Nat} (hcutoff : 1 ≤ cutoff)
    {root : List Nat} (hroot : root ∈ canonicalSurfacePolymers n)
    (hactivity : (0 : Q') < canonicalSurfaceActivity coupling n root) :
    (0 : Q') < parametricKPhysicalTerm coupling cutoff n
      (componentLabel root) := by
  have heq := canonicalSurfaceActivity_eqv_componentLabelPhysicalTerm
    coupling hcutoff hroot
  exact Q'.pos_of_lt_of_le hactivity (Q'.le_of_eqv heq)

/-- Generic exact producer for a `001` mixed summand.  The physical state is
the component label of `right`; the two inequalities orient the two false
bits and the singleton decoder supplies the true right bit. -/
def componentLabelMixedSummandCertificate
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (hcutoff : 1 ≤ cutoff)
    (left shared right : List Nat)
    (hright : right ∈ canonicalSurfacePolymers n)
    (hleft : left ≠ right) (hshared : shared ≠ right)
    (hactivity : (0 : Q') < canonicalSurfaceActivity coupling n right) :
    MixedPatternPhysicalSummandCertificate coupling hcoupling cutoff n
      (normalizedPhysicalThreeRootLaw coupling hcoupling cutoff n
        (left, shared, right)) where
  physical := componentLabel right
  physical_mem := componentLabel_mem_bounded_of_one_le hcutoff
    (canonicalSurfacePolymer_mem_faceSupports hright)
  mixed_pattern := componentLabel_threeRootPattern_001
    coupling hcoupling cutoff n left shared right hright hleft hshared
  raw_character_fusion_weight_pos :=
    canonicalRootComponentPhysicalTerm_pos hcutoff hright hactivity

/-- Fine summand: the unshifted 24-face cube label has bits
`x-shifted = false`, `y-shifted = false`, `unshifted = true`. -/
def threeAxisFineMixedSummandCertificate
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling) :
    MixedPatternPhysicalSummandCertificate fineCoupling
      (Q'.le_of_lt hfine) 1 6
      (activityMatchedFineThreeRootLaw fineCoupling
        (Q'.le_of_lt hfine) 1 6 threeAxisFineRoots) := by
  exact componentLabelMixedSummandCertificate fineCoupling
    (Q'.le_of_lt hfine) 1 6 (by omega)
    (axisFineRoot xAxisOffset) (axisFineRoot yAxisOffset)
    (axisFineRoot zeroAxisOffset)
    (axisFineRoot_mem_canonical zeroAxisOffset (Or.inl rfl))
    fineXAxisRoot_ne_zeroRoot fineYAxisRoot_ne_zeroRoot
    (zeroAxisFineRoot_activity_pos hfine)

/-- Coarse summand: at the derived activity-matched coupling, the unshifted
6-face cube label has the same explicitly oriented `001` bits. -/
def threeAxisCoarseMixedSummandCertificate
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling) :
    MixedPatternPhysicalSummandCertificate
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine)) 1 6
      (activityMatchedCoarseThreeRootLaw fineCoupling
        (Q'.le_of_lt hfine) 1 6 threeAxisCoarseRoots) := by
  exact componentLabelMixedSummandCertificate
    (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine))
    1 6 (by omega)
    (axisCoarseRoot xAxisOffset) (axisCoarseRoot yAxisOffset)
    (axisCoarseRoot zeroAxisOffset)
    (axisCoarseRoot_mem_canonical zeroAxisOffset (Or.inl rfl))
    coarseXAxisRoot_ne_zeroRoot coarseYAxisRoot_ne_zeroRoot
    (zeroAxisCoarseRoot_activity_pos (unitCubeBlockCoupling_pos hfine))

/-- Both exact physical summands packaged against the same actual
`ThreeCubeBlockRootData` witness. -/
def threeAxisFineCoarseMixedSummandInput
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling) :
    ThreeCubeFineCoarseMixedSummandInput fineCoupling
      (Q'.le_of_lt hfine) 1 6 threeAxisCubeBlockRootData where
  fine := by
    change MixedPatternPhysicalSummandCertificate fineCoupling
      (Q'.le_of_lt hfine) 1 6
      (activityMatchedFineThreeRootLaw fineCoupling
        (Q'.le_of_lt hfine) 1 6 threeAxisFineRoots)
    exact threeAxisFineMixedSummandCertificate fineCoupling hfine
  coarse := by
    change MixedPatternPhysicalSummandCertificate
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative (Q'.le_of_lt hfine)) 1 6
      (activityMatchedCoarseThreeRootLaw fineCoupling
        (Q'.le_of_lt hfine) 1 6 threeAxisCoarseRoots)
    exact threeAxisCoarseMixedSummandCertificate fineCoupling hfine

/-- The actual normalized fine and activity-matched coarse laws both assign
strictly positive mass to the mixed cell `001`. -/
theorem threeAxisFineCoarseMixedPatternMass_pos
    (fineCoupling : Q') (hfine : (0 : Q') < fineCoupling) :
    (0 : Q') < threeBlockPatternMass
        (activityMatchedFineThreeRootLaw fineCoupling
          (Q'.le_of_lt hfine) 1 6 threeAxisFineRoots)
        (false, false, true) ∧
      (0 : Q') < threeBlockPatternMass
        (activityMatchedCoarseThreeRootLaw fineCoupling
          (Q'.le_of_lt hfine) 1 6 threeAxisCoarseRoots)
        (false, false, true) := by
  exact threeCubeFineCoarseMixedPatternMass_pos fineCoupling
    (Q'.le_of_lt hfine) 1 6 threeAxisCubeBlockRootData
    (threeAxisFineCoarseMixedSummandInput fineCoupling hfine)

/-! ## Dependency gates -/

#print axioms axisShiftPlaquette_dyadicCell
#print axioms axisRoot_refines
#print axioms fineXAxisYAxis_shareProductionLink
#print axioms fineXAxisZero_shareProductionLink
#print axioms fineYAxisZero_shareProductionLink
#print axioms threeAxisCubeBlockRootData
#print axioms coarseXAxisRoot_ne_zeroRoot
#print axioms coarseYAxisRoot_ne_zeroRoot
#print axioms fineXAxisRoot_ne_zeroRoot
#print axioms fineYAxisRoot_ne_zeroRoot
#print axioms componentLabelAmbientFamily_eq_singleton
#print axioms componentLabel_threeRootPattern_001
#print axioms zeroAxisCoarseRoot_activity_pos
#print axioms zeroAxisFineRoot_activity_pos
#print axioms canonicalRootComponentPhysicalTerm_pos
#print axioms componentLabelMixedSummandCertificate
#print axioms threeAxisFineMixedSummandCertificate
#print axioms threeAxisCoarseMixedSummandCertificate
#print axioms threeAxisFineCoarseMixedSummandInput
#print axioms threeAxisFineCoarseMixedPatternMass_pos

end YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
