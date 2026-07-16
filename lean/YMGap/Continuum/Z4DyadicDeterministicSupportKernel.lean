/-
# A deterministic finite-support kernel for dyadic Z4 blocking

This module puts an actual source-dependent map underneath the previously
constructed two-point observable kernels.  A fine plaquette is sent to its
unique half-coordinate parent, and a finite fine support is coarsened by
retaining, in canonical finite-box order, precisely those coarse plaquettes
which have at least one occupied fine child.

The induced Dirac kernel on the finite list of coarse supports is everywhere
nonnegative and exactly row-normalized.  On a literal dyadic refinement the
coarsening recovers the original support, and in particular the 24-face
side-two cube boundary maps to the six-face unit-cube boundary.  The cutoff-one
face indicator attached to that support is consequently the canonical coarse
cube indicator.

This is configuration geometry and finite stochastic normalization only.  No
claim is made that an interacting Yang--Mills measure is pushed forward by
this map, or that its activity is preserved.
-/

import YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry

namespace YMGap.Continuum.Z4DyadicDeterministicSupportKernel

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.AdjSpanningBuild
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4UnitCubeEnumerationParity
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The literal fine-to-coarse carrier -/

/-- Boolean local occupation test: a coarse plaquette is occupied exactly
when the source support contains one of its four literal dyadic children.
This finite incidence formulation avoids importing division or choice into
the constructive carrier. -/
def hasDyadicParentB (fineSupport : List Z4Plaq)
    (coarsePlaquette : Z4Plaq) : Bool :=
  fineSupport.any
    (fun finePlaquette =>
      decide (finePlaquette ∈ dyadicPlaquetteCells coarsePlaquette))

/-- Canonical source-dependent coarsening in box `n`.  Filtering the fixed box
order makes the output a genuine enumerated state, independent of the order or
multiplicity in the source list. -/
def dyadicCoarsenSupport (n : Nat)
    (fineSupport : List Z4Plaq) : List Z4Plaq :=
  (boxPlaquettes n).filter (hasDyadicParentB fineSupport)

theorem mem_dyadicCoarsenSupport_iff
    (n : Nat) (fineSupport : List Z4Plaq) (coarsePlaquette : Z4Plaq) :
    coarsePlaquette ∈ dyadicCoarsenSupport n fineSupport ↔
      coarsePlaquette ∈ boxPlaquettes n ∧
        ∃ finePlaquette, finePlaquette ∈ fineSupport ∧
          finePlaquette ∈ dyadicPlaquetteCells coarsePlaquette := by
  unfold dyadicCoarsenSupport hasDyadicParentB
  rw [List.mem_filter]
  constructor
  · rintro ⟨hbox, hany⟩
    obtain ⟨finePlaquette, hfine, hparent⟩ := List.any_eq_true.mp hany
    exact ⟨hbox, finePlaquette, hfine, by simpa using hparent⟩
  · rintro ⟨hbox, finePlaquette, hfine, hparent⟩
    refine ⟨hbox, List.any_eq_true.mpr ⟨finePlaquette, hfine, ?_⟩⟩
    simp [hparent]

theorem dyadicCoarsenSupport_mem_stateSpace
    (n : Nat) (fineSupport : List Z4Plaq) :
    dyadicCoarsenSupport n fineSupport ∈ sublists (boxPlaquettes n) := by
  unfold dyadicCoarsenSupport
  exact filter_mem_sublists _ _

theorem dyadicCoarsenSupport_nodup
    (n : Nat) (fineSupport : List Z4Plaq) :
    (dyadicCoarsenSupport n fineSupport).Nodup := by
  unfold dyadicCoarsenSupport
  exact List.filter_sublist.nodup (boxPlaquettes_nodup n)

/-! ## 2. Exact recovery on literal dyadic refinements -/

/-- Coarsening a literal refinement recovers exactly the original geometric
support, provided the original lies in the declared coarse box. -/
theorem mem_dyadicCoarsenSupport_dyadicSupportCells_iff
    {n : Nat} {support : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes n)
    (coarsePlaquette : Z4Plaq) :
    coarsePlaquette ∈
        dyadicCoarsenSupport n (dyadicSupportCells support) ↔
      coarsePlaquette ∈ support := by
  constructor
  · intro hcoarse
    obtain ⟨_, finePlaquette, hfine, hcoarseCell⟩ :=
      (mem_dyadicCoarsenSupport_iff n
        (dyadicSupportCells support) coarsePlaquette).mp hcoarse
    obtain ⟨sourcePlaquette, hsource, hsourceCell⟩ :=
      (mem_dyadicSupportCells_iff support finePlaquette).mp hfine
    unfold dyadicPlaquetteCells at hsourceCell hcoarseCell
    obtain ⟨sourceIndex, _, hsourceEq⟩ := List.mem_map.mp hsourceCell
    obtain ⟨coarseIndex, _, hcoarseEq⟩ := List.mem_map.mp hcoarseCell
    have hchildren :
        dyadicCell sourcePlaquette sourceIndex =
          dyadicCell coarsePlaquette coarseIndex :=
      hsourceEq.trans hcoarseEq.symm
    have : sourcePlaquette = coarsePlaquette :=
      (dyadicCell_injective hchildren).1
    simpa only [this] using hsource
  · intro hcoarse
    apply (mem_dyadicCoarsenSupport_iff n
      (dyadicSupportCells support) coarsePlaquette).mpr
    refine ⟨hbox coarsePlaquette hcoarse,
      dyadicCell coarsePlaquette .origin, ?_,
      dyadicCell_mem_cells coarsePlaquette .origin⟩
    apply (mem_dyadicSupportCells_iff support _).mpr
    exact ⟨coarsePlaquette, hcoarse,
      dyadicCell_mem_cells coarsePlaquette .origin⟩

theorem dyadicCoarsenSupport_dyadicSupportCells_sameSupport
    {n : Nat} {support : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes n) :
    sameSupport (L := z4Chain.toLattice)
      (dyadicCoarsenSupport n (dyadicSupportCells support)) support := by
  constructor
  · intro plaquette hplaquette
    exact (mem_dyadicCoarsenSupport_dyadicSupportCells_iff
      hbox plaquette).mp hplaquette
  · intro plaquette hplaquette
    exact (mem_dyadicCoarsenSupport_dyadicSupportCells_iff
      hbox plaquette).mpr hplaquette

/-- If the coarse support is already written in canonical finite-box order,
coarsening its literal dyadic refinement recovers the same list, not merely
the same element set. -/
theorem dyadicCoarsenSupport_dyadicSupportCells_eq_of_mem_stateSpace
    {n : Nat} {support : List Z4Plaq}
    (hstate : support ∈ sublists (boxPlaquettes n)) :
    dyadicCoarsenSupport n (dyadicSupportCells support) = support := by
  have hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes n := by
    intro plaquette hplaquette
    exact mem_of_mem_sublists
      (boxPlaquettes n) support hstate plaquette hplaquette
  apply sublists_eq_of_mem_iff
    (boxPlaquettes n)
    (dyadicCoarsenSupport n (dyadicSupportCells support)) support
    (boxPlaquettes_nodup n)
    (dyadicCoarsenSupport_mem_stateSpace n (dyadicSupportCells support))
    hstate
  intro plaquette
  exact mem_dyadicCoarsenSupport_dyadicSupportCells_iff hbox plaquette

/-- The exact cylinder-root geometry: all 24 fine faces of the side-two cube
coarsen to precisely the six faces of the unit cube. -/
theorem dyadicCoarsen_refinedUnitCube_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (dyadicCoarsenSupport 2 refinedUnitCubeSurface)
      unitCubeSurface := by
  unfold refinedUnitCubeSurface
  exact dyadicCoarsenSupport_dyadicSupportCells_sameSupport
    unitCubeSurface_subset_box_two

/-- Occurrence of the complete refined cube in an arbitrary source support
forces occurrence of every coarse cube face after blocking.  Only this sound
direction is claimed: one occupied child per face already triggers the coarse
event, so the converse would be false. -/
theorem refinedUnitCube_occurrence_implies_coarseUnitCube_occurrence
    {fineSupport : List Z4Plaq}
    (hfine : ∀ finePlaquette,
      finePlaquette ∈ refinedUnitCubeSurface →
        finePlaquette ∈ fineSupport) :
    ∀ coarsePlaquette, coarsePlaquette ∈ unitCubeSurface →
      coarsePlaquette ∈ dyadicCoarsenSupport 2 fineSupport := by
  intro coarsePlaquette hcoarse
  apply (mem_dyadicCoarsenSupport_iff 2 fineSupport coarsePlaquette).mpr
  refine ⟨unitCubeSurface_subset_box_two coarsePlaquette hcoarse,
    dyadicCell coarsePlaquette .origin, ?_,
    dyadicCell_mem_cells coarsePlaquette .origin⟩
  apply hfine
  unfold refinedUnitCubeSurface
  apply (mem_dyadicSupportCells_iff unitCubeSurface _).mpr
  exact ⟨coarsePlaquette, hcoarse,
    dyadicCell_mem_cells coarsePlaquette .origin⟩

/-- One child per cube face is enough to trigger the six-face coarse event. -/
def originChildUnitCubeSupport : List Z4Plaq :=
  unitCubeSurface.map (fun plaquette => dyadicCell plaquette .origin)

theorem originChildUnitCubeSupport_triggers_coarseUnitCube :
    ∀ coarsePlaquette, coarsePlaquette ∈ unitCubeSurface →
      coarsePlaquette ∈
        dyadicCoarsenSupport 2 originChildUnitCubeSupport := by
  intro coarsePlaquette hcoarse
  apply (mem_dyadicCoarsenSupport_iff 2
    originChildUnitCubeSupport coarsePlaquette).mpr
  refine ⟨unitCubeSurface_subset_box_two coarsePlaquette hcoarse,
    dyadicCell coarsePlaquette .origin, ?_,
    dyadicCell_mem_cells coarsePlaquette .origin⟩
  unfold originChildUnitCubeSupport
  exact List.mem_map.mpr ⟨coarsePlaquette, hcoarse, rfl⟩

theorem bottomFirstChild_not_mem_originChildUnitCubeSupport :
    dyadicCell (cubeFace .bottomXY) .first ∉
      originChildUnitCubeSupport := by
  intro hmem
  unfold originChildUnitCubeSupport at hmem
  obtain ⟨sourcePlaquette, _, hcell⟩ := List.mem_map.mp hmem
  have hindices :
      DyadicCellIndex.origin = DyadicCellIndex.first :=
    (dyadicCell_injective hcell).2
  cases hindices

/-- A kernel-checked fence around the invalid converse cylinder claim.  The
six origin children trigger all coarse cube faces, while the first-offset
child of the bottom face is absent, even though that child belongs to the
24-face refined event. -/
theorem coarseUnitCube_occurrence_does_not_force_refinedUnitCube_occurrence :
    (∀ coarsePlaquette, coarsePlaquette ∈ unitCubeSurface →
      coarsePlaquette ∈
        dyadicCoarsenSupport 2 originChildUnitCubeSupport) ∧
    ¬(∀ finePlaquette, finePlaquette ∈ refinedUnitCubeSurface →
      finePlaquette ∈ originChildUnitCubeSupport) := by
  refine ⟨originChildUnitCubeSupport_triggers_coarseUnitCube, ?_⟩
  intro hfalse
  exact bottomFirstChild_not_mem_originChildUnitCubeSupport
    (hfalse (dyadicCell (cubeFace .bottomXY) .first)
      (refinedCubeCell_mem .bottomXY .first))

/-- The configuration map is not a disguised constant kernel: the empty
source and the literal refined cube have different coarse images. -/
theorem dyadicCoarsenSupport_source_dependent :
    dyadicCoarsenSupport 2 [] ≠
      dyadicCoarsenSupport 2 refinedUnitCubeSurface := by
  intro heq
  have hface : cubeFace .bottomXY ∈
      dyadicCoarsenSupport 2 refinedUnitCubeSurface :=
    dyadicCoarsen_refinedUnitCube_sameSupport.2 _
      (cubeFace_mem_unitCubeSurface .bottomXY)
  have hempty : cubeFace .bottomXY ∈ dyadicCoarsenSupport 2 [] := by
    rw [heq]
    exact hface
  obtain ⟨_, finePlaquette, hfine, _⟩ :=
    (mem_dyadicCoarsenSupport_iff 2 [] (cubeFace .bottomXY)).mp hempty
  exact absurd hfine List.not_mem_nil

/-! ## 3. Gauge-closure audit -/

/-- The geometric even-incidence condition imposed by cutoff-one gauge
closure. -/
def EvenFaceIncidence (support : List Z4Plaq) : Prop :=
  ∀ link, faceIncidenceCount link support % 2 = 0

theorem unitCubeSurface_evenFaceIncidence :
    EvenFaceIncidence unitCubeSurface := by
  intro link
  exact unitCubeFaceIncidenceCount_even link

/-- A precise sufficient closure hypothesis: for a canonical coarse support,
literal four-cell refinement followed by this coarsening is the identity and
therefore preserves every even-incidence equation. -/
theorem dyadicCoarsenSupport_preserves_evenFaceIncidence_on_refinements
    {n : Nat} {support : List Z4Plaq}
    (hstate : support ∈ sublists (boxPlaquettes n))
    (hclosed : EvenFaceIncidence support) :
    EvenFaceIncidence
      (dyadicCoarsenSupport n (dyadicSupportCells support)) := by
  rw [dyadicCoarsenSupport_dyadicSupportCells_eq_of_mem_stateSpace hstate]
  exact hclosed

/-- A boundary link which becomes unpaired after blocking a fine unit cube
by the one-child occupation rule. -/
def coarsenedFineUnitCubeFenceLink : Z4Link :=
  ((0, 1, 0, 0), .x0)

theorem coarsenedFineUnitCubeFenceLink_incidence_one :
    faceIncidenceCount coarsenedFineUnitCubeFenceLink
      (dyadicCoarsenSupport 2 unitCubeSurface) = 1 := by
  rfl

/-- Gauge-closure fence: the fine unit-cube boundary is closed at every link,
but its deterministic one-child coarse image has odd incidence at the
displayed link.  Thus this positive normalized kernel is not, by itself, a
kernel on the closed-surface subspace. -/
theorem dyadicCoarsenSupport_does_not_preserve_evenFaceIncidence :
    EvenFaceIncidence unitCubeSurface ∧
      ¬ EvenFaceIncidence (dyadicCoarsenSupport 2 unitCubeSurface) := by
  refine ⟨unitCubeSurface_evenFaceIncidence, ?_⟩
  intro hclosed
  have heven := hclosed coarsenedFineUnitCubeFenceLink
  rw [coarsenedFineUnitCubeFenceLink_incidence_one] at heven
  cases heven

/-! ## 4. The induced cutoff-one indicator labelling -/

def dyadicCoarsenSupportIds (n : Nat)
    (fineSupport : List Z4Plaq) : List Nat :=
  geometricSupportIds n (dyadicCoarsenSupport n fineSupport)

def dyadicCoarsenIndicatorLabel (n : Nat)
    (fineSupport : List Z4Plaq) : EdgeLabelling :=
  componentLabel (dyadicCoarsenSupportIds n fineSupport)

theorem dyadicCoarsenSupportIds_mem_cutoffOneFaceSupports
    (n : Nat) (fineSupport : List Z4Plaq) :
    dyadicCoarsenSupportIds n fineSupport ∈ cutoffOneFaceSupports n := by
  unfold dyadicCoarsenSupportIds
  exact geometricSupportIds_mem_cutoffOneFaceSupports n _

/-- The indicator is a cutoff-one label supported on the enumerated physical
faces.  This bounded-support membership is not a gauge-closure claim; the
preceding counterexample shows that arbitrary inputs need not satisfy the
even-incidence constraint after blocking. -/
theorem dyadicCoarsenIndicatorLabel_mem_explicitPhysicalLabellings
    (n : Nat) (fineSupport : List Z4Plaq) :
    dyadicCoarsenIndicatorLabel n fineSupport ∈
      explicitPhysicalLabellings 1 n := by
  unfold dyadicCoarsenIndicatorLabel
  apply componentLabel_mem_physical_of_subset
  intro edge hedge
  exact mem_of_mem_sublists
    (physicalFaceEdges n) (dyadicCoarsenSupportIds n fineSupport)
    (dyadicCoarsenSupportIds_mem_cutoffOneFaceSupports n fineSupport)
    edge hedge

private theorem componentLabel_eq_of_mem_iff
    {left right : List Nat}
    (hmem : ∀ edge, edge ∈ left ↔ edge ∈ right) :
    componentLabel left = componentLabel right := by
  funext edge
  unfold componentLabel
  by_cases hleft : edge ∈ left
  · have hright : edge ∈ right := (hmem edge).mp hleft
    simp [hleft, hright]
  · have hright : edge ∉ right := by
      intro hright
      exact hleft ((hmem edge).mpr hright)
    simp [hleft, hright]

/-- At the physical spin-labelling level, the blocked refined cube is exactly
the canonical six-face coarse-cube indicator. -/
theorem dyadicCoarsenIndicatorLabel_refinedUnitCube :
    dyadicCoarsenIndicatorLabel 2 refinedUnitCubeSurface =
      componentLabel coarseUnitCubeSupportIds := by
  unfold dyadicCoarsenIndicatorLabel dyadicCoarsenSupportIds
  unfold coarseUnitCubeSupportIds
  apply componentLabel_eq_of_mem_iff
  intro edge
  rw [mem_geometricSupportIds_iff, mem_geometricSupportIds_iff]
  constructor
  · rintro ⟨hphysical, hcoarse⟩
    exact ⟨hphysical,
      dyadicCoarsen_refinedUnitCube_sameSupport.1 _ hcoarse⟩
  · rintro ⟨hphysical, hcoarse⟩
    exact ⟨hphysical,
      dyadicCoarsen_refinedUnitCube_sameSupport.2 _ hcoarse⟩

/-! ## 5. A positive normalized finite Dirac kernel -/

/-- The finite state space of canonical geometric supports in coarse box
`n`. -/
def coarseSupportStateSpace (n : Nat) : List (List Z4Plaq) :=
  sublists (boxPlaquettes n)

theorem coarseSupportStateSpace_nodup (n : Nat) :
    (coarseSupportStateSpace n).Nodup := by
  unfold coarseSupportStateSpace
  exact sublists_nodup (boxPlaquettes n) (boxPlaquettes_nodup n)

/-- Dirac transition mass concentrated at the deterministic blocked source. -/
def dyadicSupportKernel (n : Nat)
    (fineSupport coarseSupport : List Z4Plaq) : Q' :=
  if coarseSupport = dyadicCoarsenSupport n fineSupport then 1 else 0

theorem dyadicSupportKernel_nonnegative
    (n : Nat) (fineSupport coarseSupport : List Z4Plaq) :
    (0 : Q') ≤ dyadicSupportKernel n fineSupport coarseSupport := by
  unfold dyadicSupportKernel
  by_cases h : coarseSupport = dyadicCoarsenSupport n fineSupport
  · rw [if_pos h]
    exact Q'.zero_le_one
  · rw [if_neg h]
    exact Q'.le_refl' 0

theorem dyadicSupportKernel_on_image
    (n : Nat) (fineSupport : List Z4Plaq) :
    dyadicSupportKernel n fineSupport
      (dyadicCoarsenSupport n fineSupport) = 1 := by
  simp [dyadicSupportKernel]

theorem dyadicSupportKernel_off_image
    {n : Nat} {fineSupport coarseSupport : List Z4Plaq}
    (hne : coarseSupport ≠ dyadicCoarsenSupport n fineSupport) :
    dyadicSupportKernel n fineSupport coarseSupport = 0 := by
  simp [dyadicSupportKernel, hne]

private theorem listQSum_dirac_zero_of_not_mem
    {A : Type} [DecidableEq A] (target : A) :
    ∀ states : List A, target ∉ states →
      listQSum (fun state => if state = target then (1 : Q') else 0)
        states ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hnot => by
      have hhead : head ≠ target := by
        intro heq
        subst head
        exact hnot List.mem_cons_self
      have htail : target ∉ tail := by
        intro hmem
        exact hnot (List.mem_cons_of_mem head hmem)
      simp only [listQSum, if_neg hhead]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl 0)
          (listQSum_dirac_zero_of_not_mem target tail htail))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem listQSum_dirac_one_of_mem_nodup
    {A : Type} [DecidableEq A] (target : A) :
    ∀ states : List A, states.Nodup → target ∈ states →
      listQSum (fun state => if state = target then (1 : Q') else 0)
        states ≈ 1
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [listQSum, if_true]
        have hzero := listQSum_dirac_zero_of_not_mem target tail hparts.1
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl 1) hzero)
          (Q'.eqv_of_eq (Q'.add_zero' 1))
      · have hheadNe : head ≠ target := by
          intro heq
          subst head
          exact hparts.1 htail
        simp only [listQSum, if_neg hheadNe]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl 0)
            (listQSum_dirac_one_of_mem_nodup target tail hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' 1))

/-- Every row of the finite configuration kernel has total mass exactly one. -/
theorem dyadicSupportKernel_row_normalized
    (n : Nat) (fineSupport : List Z4Plaq) :
    listQSum (dyadicSupportKernel n fineSupport)
      (coarseSupportStateSpace n) ≈ 1 := by
  change listQSum
    (fun coarseSupport =>
      if coarseSupport = dyadicCoarsenSupport n fineSupport then
        (1 : Q') else 0)
    (coarseSupportStateSpace n) ≈ 1
  exact listQSum_dirac_one_of_mem_nodup
    (dyadicCoarsenSupport n fineSupport)
    (coarseSupportStateSpace n)
    (coarseSupportStateSpace_nodup n)
    (dyadicCoarsenSupport_mem_stateSpace n fineSupport)

/-! ## Axiom gates -/

#print axioms mem_dyadicCoarsenSupport_iff
#print axioms dyadicCoarsenSupport_mem_stateSpace
#print axioms dyadicCoarsenSupport_nodup
#print axioms mem_dyadicCoarsenSupport_dyadicSupportCells_iff
#print axioms dyadicCoarsenSupport_dyadicSupportCells_sameSupport
#print axioms dyadicCoarsenSupport_dyadicSupportCells_eq_of_mem_stateSpace
#print axioms dyadicCoarsen_refinedUnitCube_sameSupport
#print axioms refinedUnitCube_occurrence_implies_coarseUnitCube_occurrence
#print axioms originChildUnitCubeSupport_triggers_coarseUnitCube
#print axioms bottomFirstChild_not_mem_originChildUnitCubeSupport
#print axioms coarseUnitCube_occurrence_does_not_force_refinedUnitCube_occurrence
#print axioms dyadicCoarsenSupport_source_dependent
#print axioms unitCubeSurface_evenFaceIncidence
#print axioms dyadicCoarsenSupport_preserves_evenFaceIncidence_on_refinements
#print axioms coarsenedFineUnitCubeFenceLink_incidence_one
#print axioms dyadicCoarsenSupport_does_not_preserve_evenFaceIncidence
#print axioms dyadicCoarsenSupportIds_mem_cutoffOneFaceSupports
#print axioms dyadicCoarsenIndicatorLabel_mem_explicitPhysicalLabellings
#print axioms dyadicCoarsenIndicatorLabel_refinedUnitCube
#print axioms coarseSupportStateSpace_nodup
#print axioms dyadicSupportKernel_nonnegative
#print axioms dyadicSupportKernel_on_image
#print axioms dyadicSupportKernel_off_image
#print axioms dyadicSupportKernel_row_normalized

end YMGap.Continuum.Z4DyadicDeterministicSupportKernel
