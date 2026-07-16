/-
# A concrete dyadic plaquette blocking geometry on the finite Z4 boxes

A coarse unit plaquette becomes a `2 x 2` square of fine plaquettes after one
dyadic refinement.  This module defines the four fine cells directly in the
existing corner-anchored Z4 geometry and proves that the encoding is
collision-free, duplicate-free, and maps box `n` into box `2*n`.

This is geometric blocking data only: it does not assert that the interacting
Yang--Mills law is invariant under the block map.  The latter is the analytic
renormalization step to be derived on top of this exact carrier.
-/

import YMGap.Continuum.Z4CanonicalPolymerTransport

namespace YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.AdjSpanningBuild
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.SepLatticeZ4Linf

/-- The four offsets in a dyadically refined plaquette. -/
inductive DyadicCellIndex
  | origin
  | first
  | second
  | diagonal
  deriving DecidableEq

def dyadicCellIndices : List DyadicCellIndex :=
  [.origin, .first, .second, .diagonal]

theorem dyadicCellIndices_nodup : dyadicCellIndices.Nodup := by decide

/-- Coordinatewise dilation by two. -/
def dyadicVertex : Z4Vertex → Z4Vertex
  | (a, b, c, d) => (2 * a, 2 * b, 2 * c, 2 * d)

/-- One of the four fine plaquettes tiling a dyadically refined coarse
plaquette.  `first` and `second` refer to the canonical ordered directions of
the plaquette plane. -/
def dyadicCell (plaquette : Z4Plaq) : DyadicCellIndex → Z4Plaq
  | .origin => (dyadicVertex plaquette.1, plaquette.2)
  | .first =>
      (addE (dyadicVertex plaquette.1) (dirsOf plaquette.2).1,
        plaquette.2)
  | .second =>
      (addE (dyadicVertex plaquette.1) (dirsOf plaquette.2).2,
        plaquette.2)
  | .diagonal =>
      (addE
        (addE (dyadicVertex plaquette.1) (dirsOf plaquette.2).1)
        (dirsOf plaquette.2).2,
        plaquette.2)

def dyadicPlaquetteCells (plaquette : Z4Plaq) : List Z4Plaq :=
  dyadicCellIndices.map (dyadicCell plaquette)

theorem dyadicCell_plane (plaquette : Z4Plaq) (index : DyadicCellIndex) :
    (dyadicCell plaquette index).2 = plaquette.2 := by
  cases index <;> rfl

theorem dyadicPlaquetteCells_length (plaquette : Z4Plaq) :
    (dyadicPlaquetteCells plaquette).length = 4 := by
  rfl

theorem dyadicCell_mem_cells (plaquette : Z4Plaq)
    (index : DyadicCellIndex) :
    dyadicCell plaquette index ∈ dyadicPlaquetteCells plaquette := by
  unfold dyadicPlaquetteCells
  apply List.mem_map.mpr
  refine ⟨index, ?_, rfl⟩
  cases index <;> simp [dyadicCellIndices]

/-- The fine cell determines both its coarse plaquette and its offset.  This
is the exact non-overlap fact for the half-open dyadic tiling. -/
theorem dyadicCell_injective
    {left right : Z4Plaq} {i j : DyadicCellIndex}
    (h : dyadicCell left i = dyadicCell right j) :
    left = right ∧ i = j := by
  obtain ⟨⟨a, b, c, d⟩, P⟩ := left
  obtain ⟨⟨a', b', c', d'⟩, P'⟩ := right
  have hplane : P = P' := by
    simpa only [dyadicCell_plane] using congrArg Prod.snd h
  subst P'
  have hvertex := congrArg Prod.fst h
  have h0 := congrArg (fun v : Z4Vertex => v.1) hvertex
  have h1 := congrArg (fun v : Z4Vertex => v.2.1) hvertex
  have h2 := congrArg (fun v : Z4Vertex => v.2.2.1) hvertex
  have h3 := congrArg (fun v : Z4Vertex => v.2.2.2) hvertex
  cases i <;> cases j <;> cases P <;>
    simp only [dyadicCell, dyadicVertex, addE, dirsOf] at h0 h1 h2 h3
  all_goals
    first
    | exfalso; omega
    | have e0 : a = a' := by omega
      have e1 : b = b' := by omega
      have e2 : c = c' := by omega
      have e3 : d = d' := by omega
      subst a'
      subst b'
      subst c'
      subst d'
      exact ⟨rfl, rfl⟩

private theorem nodup_map_of_injective_local {A B : Type}
    (f : A → B) (hf : ∀ {x y}, f x = f y → x = y) :
    ∀ {xs : List A}, xs.Nodup → (xs.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
      have hparts := List.nodup_cons.mp h
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_map_of_injective_local f hf hparts.2⟩
      intro hmem
      obtain ⟨y, hy, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hf heq) ▸ hy)

theorem dyadicPlaquetteCells_nodup (plaquette : Z4Plaq) :
    (dyadicPlaquetteCells plaquette).Nodup := by
  unfold dyadicPlaquetteCells
  exact nodup_map_of_injective_local (dyadicCell plaquette)
    (fun hij => (dyadicCell_injective hij).2)
    dyadicCellIndices_nodup

/-- Distinct coarse plaquettes have disjoint dyadic fine-cell footprints. -/
theorem dyadicPlaquetteCells_disjoint_of_ne
    {left right : Z4Plaq} (hne : left ≠ right) :
    ∀ cell, cell ∈ dyadicPlaquetteCells left →
      cell ∈ dyadicPlaquetteCells right → False := by
  intro cell hleft hright
  unfold dyadicPlaquetteCells at hleft hright
  obtain ⟨i, hi, hcellLeft⟩ := List.mem_map.mp hleft
  obtain ⟨j, hj, hcellRight⟩ := List.mem_map.mp hright
  have heq : dyadicCell left i = dyadicCell right j :=
    hcellLeft.trans hcellRight.symm
  exact hne (dyadicCell_injective heq).1

/-- Every dyadic cell of a plaquette in box `n` lies in the refined box
`2*n`. -/
theorem dyadicCell_mem_double_box
    {n : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes n)
    (index : DyadicCellIndex) :
    dyadicCell plaquette index ∈ boxPlaquettes (2 * n) := by
  rw [mem_boxPlaquettes] at hplaquette ⊢
  rcases hplaquette with ⟨h0, h1, h2, h3⟩
  obtain ⟨⟨a, b, c, d⟩, P⟩ := plaquette
  change a < n at h0
  change b < n at h1
  change c < n at h2
  change d < n at h3
  cases index <;> cases P <;>
    simp only [dyadicCell, dyadicVertex, addE, dirsOf]
  all_goals
    exact ⟨by omega, by omega, by omega, by omega⟩

theorem dyadicPlaquetteCells_subset_double_box
    {n : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes n) :
    ∀ cell, cell ∈ dyadicPlaquetteCells plaquette →
      cell ∈ boxPlaquettes (2 * n) := by
  intro cell hcell
  unfold dyadicPlaquetteCells at hcell
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp hcell
  exact dyadicCell_mem_double_box hplaquette index

/-! ## Connectedness of a single dyadic block -/

private theorem z4Boundary_true_of_mem_local
    {plaquette : Z4Plaq} {link : Z4Link}
    (hlink : link ∈ edgesOf plaquette) :
    z4Boundary plaquette link = true := by
  simpa only [z4Boundary, decide_eq_true_eq] using hlink

/-- The origin and first-offset cells share the internal edge parallel to the
second plaquette direction. -/
def dyadicOriginFirstAdjacent (plaquette : Z4Plaq) :
    z4Chain.toLattice.Adjacent
      (dyadicCell plaquette .origin) (dyadicCell plaquette .first) := by
  refine {
    link :=
      (addE (dyadicVertex plaquette.1) (dirsOf plaquette.2).1,
        (dirsOf plaquette.2).2)
    on_p := ?_
    on_q := ?_
  }
  · apply z4Boundary_true_of_mem_local
    unfold dyadicCell edgesOf
    exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))
  · apply z4Boundary_true_of_mem_local
    unfold dyadicCell edgesOf
    exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The origin and second-offset cells share the internal edge parallel to
the first plaquette direction. -/
def dyadicOriginSecondAdjacent (plaquette : Z4Plaq) :
    z4Chain.toLattice.Adjacent
      (dyadicCell plaquette .origin) (dyadicCell plaquette .second) := by
  refine {
    link :=
      (addE (dyadicVertex plaquette.1) (dirsOf plaquette.2).2,
        (dirsOf plaquette.2).1)
    on_p := ?_
    on_q := ?_
  }
  · apply z4Boundary_true_of_mem_local
    unfold dyadicCell edgesOf
    exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)
  · apply z4Boundary_true_of_mem_local
    unfold dyadicCell edgesOf
    exact List.mem_cons_self

/-- The first-offset and diagonal cells share their internal edge parallel to
the first plaquette direction. -/
def dyadicFirstDiagonalAdjacent (plaquette : Z4Plaq) :
    z4Chain.toLattice.Adjacent
      (dyadicCell plaquette .first) (dyadicCell plaquette .diagonal) := by
  refine {
    link :=
      (addE
        (addE (dyadicVertex plaquette.1) (dirsOf plaquette.2).1)
        (dirsOf plaquette.2).2,
        (dirsOf plaquette.2).1)
    on_p := ?_
    on_q := ?_
  }
  · apply z4Boundary_true_of_mem_local
    unfold dyadicCell edgesOf
    exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)
  · apply z4Boundary_true_of_mem_local
    unfold dyadicCell edgesOf
    exact List.mem_cons_self

/-- Explicit internal paths between every pair of fine cells in one dyadic
plaquette block. -/
def dyadicCellChain (plaquette : Z4Plaq) :
    ∀ sourceIndex targetIndex : DyadicCellIndex,
      ChainIn z4Chain.toLattice (dyadicPlaquetteCells plaquette)
        (dyadicCell plaquette sourceIndex) (dyadicCell plaquette targetIndex)
  | .origin, .origin => ChainIn.refl _
  | .origin, .first =>
      ChainIn.step (dyadicOriginFirstAdjacent plaquette)
        (dyadicCell_mem_cells plaquette .first) (ChainIn.refl _)
  | .origin, .second =>
      ChainIn.step (dyadicOriginSecondAdjacent plaquette)
        (dyadicCell_mem_cells plaquette .second) (ChainIn.refl _)
  | .origin, .diagonal =>
      ChainIn.step (dyadicOriginFirstAdjacent plaquette)
        (dyadicCell_mem_cells plaquette .first)
        (ChainIn.step (dyadicFirstDiagonalAdjacent plaquette)
          (dyadicCell_mem_cells plaquette .diagonal) (ChainIn.refl _))
  | .first, .origin =>
      ChainIn.step (adjacentSymm (dyadicOriginFirstAdjacent plaquette))
        (dyadicCell_mem_cells plaquette .origin) (ChainIn.refl _)
  | .first, .first => ChainIn.refl _
  | .first, .second =>
      ChainIn.step (adjacentSymm (dyadicOriginFirstAdjacent plaquette))
        (dyadicCell_mem_cells plaquette .origin)
        (ChainIn.step (dyadicOriginSecondAdjacent plaquette)
          (dyadicCell_mem_cells plaquette .second) (ChainIn.refl _))
  | .first, .diagonal =>
      ChainIn.step (dyadicFirstDiagonalAdjacent plaquette)
        (dyadicCell_mem_cells plaquette .diagonal) (ChainIn.refl _)
  | .second, .origin =>
      ChainIn.step (adjacentSymm (dyadicOriginSecondAdjacent plaquette))
        (dyadicCell_mem_cells plaquette .origin) (ChainIn.refl _)
  | .second, .first =>
      ChainIn.step (adjacentSymm (dyadicOriginSecondAdjacent plaquette))
        (dyadicCell_mem_cells plaquette .origin)
        (ChainIn.step (dyadicOriginFirstAdjacent plaquette)
          (dyadicCell_mem_cells plaquette .first) (ChainIn.refl _))
  | .second, .second => ChainIn.refl _
  | .second, .diagonal =>
      ChainIn.step (adjacentSymm (dyadicOriginSecondAdjacent plaquette))
        (dyadicCell_mem_cells plaquette .origin)
        (ChainIn.step (dyadicOriginFirstAdjacent plaquette)
          (dyadicCell_mem_cells plaquette .first)
          (ChainIn.step (dyadicFirstDiagonalAdjacent plaquette)
            (dyadicCell_mem_cells plaquette .diagonal) (ChainIn.refl _)))
  | .diagonal, .origin =>
      ChainIn.step (adjacentSymm (dyadicFirstDiagonalAdjacent plaquette))
        (dyadicCell_mem_cells plaquette .first)
        (ChainIn.step (adjacentSymm (dyadicOriginFirstAdjacent plaquette))
          (dyadicCell_mem_cells plaquette .origin) (ChainIn.refl _))
  | .diagonal, .first =>
      ChainIn.step (adjacentSymm (dyadicFirstDiagonalAdjacent plaquette))
        (dyadicCell_mem_cells plaquette .first) (ChainIn.refl _)
  | .diagonal, .second =>
      ChainIn.step (adjacentSymm (dyadicFirstDiagonalAdjacent plaquette))
        (dyadicCell_mem_cells plaquette .first)
        (ChainIn.step (adjacentSymm (dyadicOriginFirstAdjacent plaquette))
          (dyadicCell_mem_cells plaquette .origin)
          (ChainIn.step (dyadicOriginSecondAdjacent plaquette)
            (dyadicCell_mem_cells plaquette .second) (ChainIn.refl _)))
  | .diagonal, .diagonal => ChainIn.refl _

/-- The four fine cells tiling a coarse plaquette form one genuine
shared-link connected polymer. -/
def dyadicPlaquetteCells_connected (plaquette : Z4Plaq) :
    connectedIn (L := z4Chain.toLattice)
      (dyadicPlaquetteCells plaquette) := by
  intro source target hsource htarget
  unfold dyadicPlaquetteCells at hsource htarget
  obtain ⟨sourceIndex, _, hsourceEq⟩ :=
    YMGap.Continuum.Z4CanonicalConnectedSurfaceGas.decodeMapMember
      (dyadicCell plaquette) dyadicCellIndices source hsource
  obtain ⟨targetIndex, _, htargetEq⟩ :=
    YMGap.Continuum.Z4CanonicalConnectedSurfaceGas.decodeMapMember
      (dyadicCell plaquette) dyadicCellIndices target htarget
  rw [← hsourceEq, ← htargetEq]
  exact dyadicCellChain plaquette sourceIndex targetIndex

theorem dyadicBoundaryLink_mem_origin (plaquette : Z4Plaq) :
    (dyadicVertex plaquette.1, (dirsOf plaquette.2).1) ∈
      edgesOf (dyadicCell plaquette .origin) := by
  unfold dyadicCell edgesOf
  exact List.mem_cons_self

private theorem vComp_addE_self_local (vertex : Z4Vertex) (direction : Dir4) :
    vComp (addE vertex direction) direction =
      vComp vertex direction + 1 := by
  obtain ⟨a, b, c, d⟩ := vertex
  cases direction <;> rfl

private theorem vComp_addE_ne_local
    (vertex : Z4Vertex) (step coordinate : Dir4)
    (hne : step ≠ coordinate) :
    vComp (addE vertex step) coordinate = vComp vertex coordinate := by
  obtain ⟨a, b, c, d⟩ := vertex
  cases step <;> cases coordinate <;> simp_all [vComp, addE]

private theorem baseLink_not_mem_shiftedPlaquette
    (vertex : Z4Vertex) (linkDirection shift : Dir4) (plane : Z4Plane) :
    (vertex, linkDirection) ∉
      edgesOf ((addE vertex shift, plane) : Z4Plaq) := by
  intro hmem
  have hwindow := edge_base_comp hmem shift
  have hshift := vComp_addE_self_local vertex shift
  simp only [cPlaq] at hwindow
  omega

private theorem baseLink_not_mem_doubleShiftedPlaquette
    (vertex : Z4Vertex) (linkDirection first second : Dir4)
    (plane : Z4Plane) (hne : first ≠ second) :
    (vertex, linkDirection) ∉
      edgesOf ((addE (addE vertex first) second, plane) : Z4Plaq) := by
  intro hmem
  have hwindow := edge_base_comp hmem second
  have hsecond := vComp_addE_self_local (addE vertex first) second
  have hfirst := vComp_addE_ne_local vertex first second hne
  simp only [cPlaq] at hwindow
  omega

theorem dyadicBoundaryLink_not_mem_first (plaquette : Z4Plaq) :
    (dyadicVertex plaquette.1, (dirsOf plaquette.2).1) ∉
      edgesOf (dyadicCell plaquette .first) := by
  exact baseLink_not_mem_shiftedPlaquette
    (dyadicVertex plaquette.1) (dirsOf plaquette.2).1
    (dirsOf plaquette.2).1 plaquette.2

theorem dyadicBoundaryLink_not_mem_second (plaquette : Z4Plaq) :
    (dyadicVertex plaquette.1, (dirsOf plaquette.2).1) ∉
      edgesOf (dyadicCell plaquette .second) := by
  exact baseLink_not_mem_shiftedPlaquette
    (dyadicVertex plaquette.1) (dirsOf plaquette.2).1
    (dirsOf plaquette.2).2 plaquette.2

theorem dyadicBoundaryLink_not_mem_diagonal (plaquette : Z4Plaq) :
    (dyadicVertex plaquette.1, (dirsOf plaquette.2).1) ∉
      edgesOf (dyadicCell plaquette .diagonal) := by
  exact baseLink_not_mem_doubleShiftedPlaquette
    (dyadicVertex plaquette.1) (dirsOf plaquette.2).1
    (dirsOf plaquette.2).1 (dirsOf plaquette.2).2 plaquette.2
    (dirsOf_ne plaquette.2)

/-- A planar four-cell dyadic patch is connected but not closed: the lower
edge parallel to the first plaquette direction occurs on the origin cell and
on none of the other three cells.  This permanently fences the tempting but
vacuous use of one refined plaquette patch as a gauge-closed block observable;
closed cube boundaries are the next carrier. -/
theorem dyadicPlaquetteCells_has_unpaired_boundary
    (plaquette : Z4Plaq) :
    let boundaryLink : Z4Link :=
      (dyadicVertex plaquette.1, (dirsOf plaquette.2).1)
    boundaryLink ∈ edgesOf (dyadicCell plaquette .origin) ∧
      boundaryLink ∉ edgesOf (dyadicCell plaquette .first) ∧
      boundaryLink ∉ edgesOf (dyadicCell plaquette .second) ∧
      boundaryLink ∉ edgesOf (dyadicCell plaquette .diagonal) := by
  exact ⟨dyadicBoundaryLink_mem_origin plaquette,
    dyadicBoundaryLink_not_mem_first plaquette,
    dyadicBoundaryLink_not_mem_second plaquette,
    dyadicBoundaryLink_not_mem_diagonal plaquette⟩

/-! ## Finite-support dyadic blocking -/

/-- Refine every plaquette of a finite geometric support into its four dyadic
cells. -/
def dyadicSupportCells (support : List Z4Plaq) : List Z4Plaq :=
  support.flatMap dyadicPlaquetteCells

theorem mem_dyadicSupportCells_iff
    (support : List Z4Plaq) (cell : Z4Plaq) :
    cell ∈ dyadicSupportCells support ↔
      ∃ plaquette, plaquette ∈ support ∧
        cell ∈ dyadicPlaquetteCells plaquette := by
  unfold dyadicSupportCells
  constructor
  · intro hcell
    obtain ⟨plaquette, hplaquette, hlocal⟩ :=
      List.mem_flatMap.mp hcell
    exact ⟨plaquette, hplaquette, hlocal⟩
  · rintro ⟨plaquette, hplaquette, hlocal⟩
    exact List.mem_flatMap.mpr ⟨plaquette, hplaquette, hlocal⟩

/-- A dyadic refinement has exactly four fine plaquettes per coarse
plaquette, including multiplicity for a non-`Nodup` input list. -/
theorem dyadicSupportCells_length (support : List Z4Plaq) :
    (dyadicSupportCells support).length = support.length * 4 := by
  unfold dyadicSupportCells
  induction support with
  | nil => rfl
  | cons plaquette tail ih =>
      rw [List.flatMap_cons, List.length_append,
        dyadicPlaquetteCells_length, ih, List.length_cons]
      omega

private theorem dyadicSupportCells_nodup_local :
    ∀ support : List Z4Plaq, support.Nodup →
      (dyadicSupportCells support).Nodup
  | [], _ => List.nodup_nil
  | plaquette :: tail, hsupport => by
      have hparts := List.nodup_cons.mp hsupport
      unfold dyadicSupportCells
      rw [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨dyadicPlaquetteCells_nodup plaquette,
        dyadicSupportCells_nodup_local tail hparts.2, ?_⟩
      intro cell hcell other hother heq
      have hcellTail : cell ∈ dyadicSupportCells tail := by
        unfold dyadicSupportCells
        rw [heq]
        exact hother
      obtain ⟨otherPlaquette, hotherPlaquette, hcellOther⟩ :=
        (mem_dyadicSupportCells_iff tail cell).mp hcellTail
      have hne : plaquette ≠ otherPlaquette := by
        intro heqPlaquette
        subst otherPlaquette
        exact hparts.1 hotherPlaquette
      exact dyadicPlaquetteCells_disjoint_of_ne hne cell hcell hcellOther

/-- A duplicate-free coarse support refines to a duplicate-free fine
support.  The stronger pointwise injectivity theorem rules out collisions
both within one coarse plaquette and between distinct coarse plaquettes. -/
theorem dyadicSupportCells_nodup
    {support : List Z4Plaq} (hsupport : support.Nodup) :
    (dyadicSupportCells support).Nodup :=
  dyadicSupportCells_nodup_local support hsupport

/-- Refining a support contained in box `n` produces a support contained in
box `2*n`. -/
theorem dyadicSupportCells_subset_double_box
    {n : Nat} {support : List Z4Plaq}
    (hsupport : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes n) :
    ∀ cell, cell ∈ dyadicSupportCells support →
      cell ∈ boxPlaquettes (2 * n) := by
  intro cell hcell
  obtain ⟨plaquette, hplaquette, hlocal⟩ :=
    (mem_dyadicSupportCells_iff support cell).mp hcell
  exact dyadicPlaquetteCells_subset_double_box
    (hsupport plaquette hplaquette) cell hlocal

/-- Canonical refined-box identifiers for an arbitrary finite coarse
geometric support. -/
def dyadicSupportIds (n : Nat) (support : List Z4Plaq) : List Nat :=
  geometricSupportIds (2 * n) (dyadicSupportCells support)

theorem dyadicSupportIds_sameSupport
    {n : Nat} {support : List Z4Plaq}
    (hsupport : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes n) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (2 * n) (dyadicSupportIds n support))
      (dyadicSupportCells support) := by
  unfold dyadicSupportIds
  exact geometricSupportIds_sameSupport
    (dyadicSupportCells_subset_double_box hsupport)

/-- The numerical refined support has exactly four identifiers per coarse
plaquette whenever the coarse geometric list has no duplicates. -/
theorem dyadicSupportIds_length
    {n : Nat} {support : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes n)
    (hnodup : support.Nodup) :
    (dyadicSupportIds n support).length = support.length * 4 := by
  have hsame := dyadicSupportIds_sameSupport hbox
  have hlength := sameSupport_length_eq_of_nodup hsame
    (geometricPolymer_nodup
      (geometricSupportIds_mem_cutoffOneFaceSupports
        (2 * n) (dyadicSupportCells support)))
    (dyadicSupportCells_nodup hnodup)
  rw [geometricPolymer_length_eq_support_length] at hlength
  exact hlength.trans (dyadicSupportCells_length support)

/-- The collision-free four-cell footprint re-encoded in the physical
plaquette identifiers of the refined box. -/
def dyadicPlaquetteSupportIds (n : Nat) (plaquette : Z4Plaq) : List Nat :=
  geometricSupportIds (2 * n) (dyadicPlaquetteCells plaquette)

theorem dyadicPlaquetteSupportIds_sameSupport
    {n : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes n) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (2 * n)
        (dyadicPlaquetteSupportIds n plaquette))
      (dyadicPlaquetteCells plaquette) := by
  unfold dyadicPlaquetteSupportIds
  exact geometricSupportIds_sameSupport
    (dyadicPlaquetteCells_subset_double_box hplaquette)

/-- A refined coarse plaquette is not merely a four-cell list: its canonical
identifier support is an actual connected polymer of the refined finite-box
gas. -/
theorem dyadicPlaquetteSupportIds_mem_canonicalSurfacePolymers
    {n : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes n) :
    dyadicPlaquetteSupportIds n plaquette ∈
      canonicalSurfacePolymers (2 * n) := by
  apply connectedFaceSupport_mem_canonicalSurfacePolymers
  · exact geometricSupportIds_mem_cutoffOneFaceSupports
      (2 * n) (dyadicPlaquetteCells plaquette)
  · have hsame := dyadicPlaquetteSupportIds_sameSupport hplaquette
    have hcell : dyadicCell plaquette .origin ∈
        geometricPolymer (2 * n)
          (dyadicPlaquetteSupportIds n plaquette) :=
      hsame.2 _ (dyadicCell_mem_cells plaquette .origin)
    obtain ⟨identifier, hidentifier, _⟩ :=
      YMGap.Continuum.Z4CanonicalConnectedSurfaceGas.decodeMapMember
        (boxPlaquetteAt (2 * n))
        (dyadicPlaquetteSupportIds n plaquette)
        (dyadicCell plaquette .origin) hcell
    exact ⟨identifier, hidentifier⟩
  · unfold dyadicPlaquetteSupportIds
    exact geometricSupportIds_connected
      (dyadicPlaquetteCells_subset_double_box hplaquette)
      (dyadicPlaquetteCells_connected plaquette)

#print axioms dyadicCell_injective
#print axioms dyadicCell_plane
#print axioms dyadicPlaquetteCells_nodup
#print axioms dyadicPlaquetteCells_disjoint_of_ne
#print axioms dyadicCell_mem_double_box
#print axioms dyadicOriginFirstAdjacent
#print axioms dyadicOriginSecondAdjacent
#print axioms dyadicFirstDiagonalAdjacent
#print axioms dyadicPlaquetteCells_connected
#print axioms dyadicBoundaryLink_not_mem_first
#print axioms dyadicBoundaryLink_not_mem_second
#print axioms dyadicBoundaryLink_not_mem_diagonal
#print axioms dyadicPlaquetteCells_has_unpaired_boundary
#print axioms dyadicSupportCells_nodup
#print axioms dyadicSupportCells_subset_double_box
#print axioms dyadicSupportIds_sameSupport
#print axioms dyadicSupportIds_length
#print axioms dyadicPlaquetteSupportIds_sameSupport
#print axioms dyadicPlaquetteSupportIds_mem_canonicalSurfacePolymers

end YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
