/-
# An exact adjacent-time unit-cube cylinder in the physical Z4 law

The dyadic unit-cube boundary is translated by one genuine lattice step in
the fourth coordinate.  Shared-link chains are transported through the
actual Z4 incidence relation, and both time-zero and time-one carriers are
re-encoded as canonical polymers in a common finite box.

The resulting two-bit cylinder is evaluated in the arbitrary-coupling
physical spin-foam law.  Its four atoms have exact rational probabilities,
their marginals and normalization are proved by finite additivity, and the
ordinary L2 square form is nonnegative.

This is deliberately not called Osterwalder--Schrader positivity.  A final
exact two-point table shows that nonnegative normalized symmetric joint data
alone can have a negative reflection quadratic form.  A genuine reflection
action on configurations, with invariance/factorization of the physical
weight, remains necessary.
-/

import YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.Z4AdjacentTimeUnitCubeCylinder

set_option maxRecDepth 100000
set_option maxHeartbeats 500000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponents

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A genuine one-step translate in the fourth coordinate -/

def euclideanTimeTranslateVertex (vertex : Z4Vertex) : Z4Vertex :=
  addE vertex .x3

def euclideanTimeTranslateLink (link : Z4Link) : Z4Link :=
  (euclideanTimeTranslateVertex link.1, link.2)

def euclideanTimeTranslatePlaquette (plaquette : Z4Plaq) : Z4Plaq :=
  (euclideanTimeTranslateVertex plaquette.1, plaquette.2)

theorem euclideanTimeTranslateVertex_addE
    (vertex : Z4Vertex) (direction : Dir4) :
    euclideanTimeTranslateVertex (addE vertex direction) =
      addE (euclideanTimeTranslateVertex vertex) direction := by
  obtain ⟨a, b, c, d⟩ := vertex
  cases direction <;> rfl

theorem edgesOf_euclideanTimeTranslatePlaquette
    (plaquette : Z4Plaq) :
    edgesOf (euclideanTimeTranslatePlaquette plaquette) =
      (edgesOf plaquette).map euclideanTimeTranslateLink := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  cases plane <;> rfl

def euclideanTimeTranslateAdjacent {left right : Z4Plaq}
    (adjacent : z4Chain.toLattice.Adjacent left right) :
    z4Chain.toLattice.Adjacent
      (euclideanTimeTranslatePlaquette left)
      (euclideanTimeTranslatePlaquette right) := by
  refine {
    link := euclideanTimeTranslateLink adjacent.link
    on_p := ?_
    on_q := ?_
  }
  · change z4Boundary (euclideanTimeTranslatePlaquette left)
      (euclideanTimeTranslateLink adjacent.link) = true
    unfold z4Boundary
    rw [edgesOf_euclideanTimeTranslatePlaquette]
    apply decide_eq_true
    exact List.mem_map.mpr
      ⟨adjacent.link, of_decide_eq_true adjacent.on_p, rfl⟩
  · change z4Boundary (euclideanTimeTranslatePlaquette right)
      (euclideanTimeTranslateLink adjacent.link) = true
    unfold z4Boundary
    rw [edgesOf_euclideanTimeTranslatePlaquette]
    apply decide_eq_true
    exact List.mem_map.mpr
      ⟨adjacent.link, of_decide_eq_true adjacent.on_q, rfl⟩

def euclideanTimeTranslateChain {support : List Z4Plaq} :
    {first last : Z4Plaq} →
      ChainIn z4Chain.toLattice support first last →
      ChainIn z4Chain.toLattice
        (support.map euclideanTimeTranslatePlaquette)
        (euclideanTimeTranslatePlaquette first)
        (euclideanTimeTranslatePlaquette last)
  | _, _, .refl plaquette => .refl _
  | _, _, .step adjacent hnext rest =>
      .step (euclideanTimeTranslateAdjacent adjacent)
        (List.mem_map.mpr ⟨_, hnext, rfl⟩)
        (euclideanTimeTranslateChain rest)

/-- The same side-two cube boundary one Euclidean-time lattice step later. -/
def adjacentTimeRefinedUnitCubeSurface : List Z4Plaq :=
  refinedUnitCubeSurface.map euclideanTimeTranslatePlaquette

def adjacentTimeRefinedUnitCubeSurface_connected :
    connectedIn (L := z4Chain.toLattice)
      adjacentTimeRefinedUnitCubeSurface := by
  intro first last hfirst hlast
  obtain ⟨sourceFirst, hsourceFirst, hfirstEq⟩ :=
    decodeMapMember euclideanTimeTranslatePlaquette
      refinedUnitCubeSurface first hfirst
  obtain ⟨sourceLast, hsourceLast, hlastEq⟩ :=
    decodeMapMember euclideanTimeTranslatePlaquette
      refinedUnitCubeSurface last hlast
  rw [← hfirstEq, ← hlastEq]
  exact euclideanTimeTranslateChain
    (refinedUnitCubeSurface_connected
      sourceFirst sourceLast hsourceFirst hsourceLast)

theorem adjacentTimeRefinedUnitCubeSurface_subset_box_five :
  ∀ plaquette, plaquette ∈ adjacentTimeRefinedUnitCubeSurface →
      plaquette ∈ boxPlaquettes 5 := by
  intro plaquette hplaquette
  obtain ⟨source, hsource, hsourceEq⟩ :=
    decodeMapMember euclideanTimeTranslatePlaquette
      refinedUnitCubeSurface plaquette hplaquette
  rw [← hsourceEq]
  have hbox := refinedUnitCubeSurface_subset_box_four source hsource
  rw [mem_boxPlaquettes] at hbox ⊢
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := source
  simp only [euclideanTimeTranslatePlaquette,
    euclideanTimeTranslateVertex, addE] at *
  exact ⟨Nat.lt_of_lt_of_le hbox.1 (by decide),
    Nat.lt_of_lt_of_le hbox.2.1 (by decide),
    Nat.lt_of_lt_of_le hbox.2.2.1 (by decide),
    Nat.succ_lt_succ hbox.2.2.2⟩

/-! ## 2. Canonical roots at times zero and one -/

def adjacentTimeUnitCubeSupportIds : List Nat :=
  geometricSupportIds 5 adjacentTimeRefinedUnitCubeSurface

theorem adjacentTimeUnitCubeSupportIds_sameSupport :
    sameSupport
      (geometricPolymer 5 adjacentTimeUnitCubeSupportIds)
      adjacentTimeRefinedUnitCubeSurface := by
  unfold adjacentTimeUnitCubeSupportIds
  exact geometricSupportIds_sameSupport
    adjacentTimeRefinedUnitCubeSurface_subset_box_five

theorem adjacentTimeUnitCubeSupportIds_mem_canonicalSurfacePolymers :
    adjacentTimeUnitCubeSupportIds ∈ canonicalSurfacePolymers 5 := by
  apply connectedFaceSupport_mem_canonicalSurfacePolymers
  · unfold adjacentTimeUnitCubeSupportIds
    exact geometricSupportIds_mem_cutoffOneFaceSupports
      5 adjacentTimeRefinedUnitCubeSurface
  · have hsame := adjacentTimeUnitCubeSupportIds_sameSupport
    have htranslatedHub :
        euclideanTimeTranslatePlaquette refinedCubeHub ∈
          adjacentTimeRefinedUnitCubeSurface := by
      unfold adjacentTimeRefinedUnitCubeSurface
      exact List.mem_map.mpr
        ⟨refinedCubeHub, refinedCubeCell_mem .bottomXY .origin, rfl⟩
    have hhub : euclideanTimeTranslatePlaquette refinedCubeHub ∈
        geometricPolymer 5 adjacentTimeUnitCubeSupportIds :=
      hsame.2 _ htranslatedHub
    obtain ⟨identifier, hidentifier, _⟩ :=
      decodeMapMember (boxPlaquetteAt 5)
        adjacentTimeUnitCubeSupportIds
        (euclideanTimeTranslatePlaquette refinedCubeHub) hhub
    exact ⟨identifier, hidentifier⟩
  · unfold adjacentTimeUnitCubeSupportIds
    exact geometricSupportIds_connected
      adjacentTimeRefinedUnitCubeSurface_subset_box_five
      adjacentTimeRefinedUnitCubeSurface_connected

def timeZeroUnitCubeSupportIds : List Nat :=
  transportPolymer 4 5 dyadicUnitCubeSupportIds

theorem timeZeroUnitCubeSupportIds_canonical :
    timeZeroUnitCubeSupportIds ∈ canonicalSurfacePolymers 5 := by
  unfold timeZeroUnitCubeSupportIds
  exact transportPolymer_mem_canonicalSurfacePolymers (by decide)
    dyadicUnitCubeSupportIds_mem_canonicalSurfacePolymers

def timeZeroUnitCubeRootAt (volume : Nat) : List Nat :=
  transportPolymer 5 volume timeZeroUnitCubeSupportIds

def timeOneUnitCubeRootAt (volume : Nat) : List Nat :=
  transportPolymer 5 volume adjacentTimeUnitCubeSupportIds

theorem timeZeroUnitCubeRootAt_canonical
    {volume : Nat} (hvolume : 5 ≤ volume) :
    timeZeroUnitCubeRootAt volume ∈ canonicalSurfacePolymers volume := by
  unfold timeZeroUnitCubeRootAt
  exact transportPolymer_mem_canonicalSurfacePolymers hvolume
    timeZeroUnitCubeSupportIds_canonical

theorem timeOneUnitCubeRootAt_canonical
    {volume : Nat} (hvolume : 5 ≤ volume) :
    timeOneUnitCubeRootAt volume ∈ canonicalSurfacePolymers volume := by
  unfold timeOneUnitCubeRootAt
  exact transportPolymer_mem_canonicalSurfacePolymers hvolume
    adjacentTimeUnitCubeSupportIds_mem_canonicalSurfacePolymers

/-! ## 3. Exact separation of the two time slices -/

theorem refinedUnitCubeSurface_timeCoordinate_zero
    {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ refinedUnitCubeSurface) :
    plaquette.1.2.2.2 = 0 := by
  have hrefined :=
    (mem_dyadicSupportCells_iff unitCubeSurface plaquette).mp hplaquette
  obtain ⟨coarse, hcoarse, hcell⟩ := hrefined
  obtain ⟨index, _, hcellEq⟩ :=
    decodeMapMember (dyadicCell coarse) dyadicCellIndices plaquette hcell
  rw [← hcellEq]
  simp only [unitCubeSurface, List.mem_cons, List.not_mem_nil,
    or_false] at hcoarse
  rcases hcoarse with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases index <;> rfl

theorem refinedUnitCubeSurface_spatialPlane
    {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ refinedUnitCubeSurface) :
    plaquette.2 = .p01 ∨ plaquette.2 = .p02 ∨
      plaquette.2 = .p12 := by
  have hrefined :=
    (mem_dyadicSupportCells_iff unitCubeSurface plaquette).mp hplaquette
  obtain ⟨coarse, hcoarse, hcell⟩ := hrefined
  obtain ⟨index, _, hcellEq⟩ :=
    decodeMapMember (dyadicCell coarse) dyadicCellIndices plaquette hcell
  rw [← hcellEq, dyadicCell_plane]
  simp only [unitCubeSurface, List.mem_cons, List.not_mem_nil,
    or_false] at hcoarse
  rcases hcoarse with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp

theorem adjacentTimeRefinedUnitCubeSurface_timeCoordinate_one
    {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ adjacentTimeRefinedUnitCubeSurface) :
    plaquette.1.2.2.2 = 1 := by
  obtain ⟨source, hsource, hsourceEq⟩ :=
    decodeMapMember euclideanTimeTranslatePlaquette
      refinedUnitCubeSurface plaquette hplaquette
  rw [← hsourceEq]
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := source
  have htime := refinedUnitCubeSurface_timeCoordinate_zero hsource
  simp only [euclideanTimeTranslatePlaquette,
    euclideanTimeTranslateVertex, addE] at htime ⊢
  rw [htime]

theorem adjacentTimeRefinedUnitCubeSurface_spatialPlane
    {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ adjacentTimeRefinedUnitCubeSurface) :
    plaquette.2 = .p01 ∨ plaquette.2 = .p02 ∨
      plaquette.2 = .p12 := by
  obtain ⟨source, hsource, hsourceEq⟩ :=
    decodeMapMember euclideanTimeTranslatePlaquette
      refinedUnitCubeSurface plaquette hplaquette
  rw [← hsourceEq]
  simpa only [euclideanTimeTranslatePlaquette] using
    (refinedUnitCubeSurface_spatialPlane hsource)

theorem spatialPlaquette_edge_timeCoordinate
    {plaquette : Z4Plaq} {link : Z4Link}
    (hplane : plaquette.2 = .p01 ∨ plaquette.2 = .p02 ∨
      plaquette.2 = .p12)
    (hlink : link ∈ edgesOf plaquette) :
    link.1.2.2.2 = plaquette.1.2.2.2 := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  rcases hplane with rfl | rfl | rfl <;>
    simp only [edgesOf, dirsOf, addE, List.mem_cons,
      List.not_mem_nil, or_false] at hlink <;>
    rcases hlink with rfl | rfl | rfl | rfl <;> rfl

/-- The two cube boundaries share no actual lattice link. -/
theorem adjacentTimeRefinedUnitCubeSurfaces_linkDisjoint
    {first second : Z4Plaq} {link : Z4Link}
    (hfirst : first ∈ refinedUnitCubeSurface)
    (hsecond : second ∈ adjacentTimeRefinedUnitCubeSurface)
    (hlinkFirst : link ∈ edgesOf first)
    (hlinkSecond : link ∈ edgesOf second) : False := by
  have hfirstLink := spatialPlaquette_edge_timeCoordinate
    (refinedUnitCubeSurface_spatialPlane hfirst) hlinkFirst
  have hsecondLink := spatialPlaquette_edge_timeCoordinate
    (adjacentTimeRefinedUnitCubeSurface_spatialPlane hsecond) hlinkSecond
  rw [refinedUnitCubeSurface_timeCoordinate_zero hfirst] at hfirstLink
  rw [adjacentTimeRefinedUnitCubeSurface_timeCoordinate_one hsecond]
    at hsecondLink
  exact Nat.zero_ne_one (hfirstLink.symm.trans hsecondLink)

theorem adjacentTimeRefinedUnitCubeSurfaces_disjoint :
    SupportsDisjoint refinedUnitCubeSurface
      adjacentTimeRefinedUnitCubeSurface := by
  intro plaquette hfirst hsecond
  have hzero := refinedUnitCubeSurface_timeCoordinate_zero hfirst
  have hone := adjacentTimeRefinedUnitCubeSurface_timeCoordinate_one hsecond
  exact Nat.zero_ne_one (hzero.symm.trans hone)

theorem timeZeroUnitCubeSupportIds_sameSupport :
    sameSupport (geometricPolymer 5 timeZeroUnitCubeSupportIds)
      refinedUnitCubeSurface := by
  unfold timeZeroUnitCubeSupportIds
  exact sameSupport_trans
    (sameSupport_symm
      (transportPolymer_sameSupport (by decide)
        dyadicUnitCubeSupportIds_mem_cutoffOneFaceSupports))
    dyadicUnitCubeSupportIds_sameSupport

theorem timeSliceSupportIds_disjoint :
    SupportsDisjoint timeZeroUnitCubeSupportIds
      adjacentTimeUnitCubeSupportIds := by
  intro face hzero hone
  have hzeroGeom : boxPlaquetteAt 5 face ∈
      geometricPolymer 5 timeZeroUnitCubeSupportIds :=
    List.mem_map.mpr ⟨face, hzero, rfl⟩
  have honeGeom : boxPlaquetteAt 5 face ∈
      geometricPolymer 5 adjacentTimeUnitCubeSupportIds :=
    List.mem_map.mpr ⟨face, hone, rfl⟩
  exact adjacentTimeRefinedUnitCubeSurfaces_disjoint
    _ (timeZeroUnitCubeSupportIds_sameSupport.1 _ hzeroGeom)
    (adjacentTimeUnitCubeSupportIds_sameSupport.1 _ honeGeom)

theorem timeSliceSupportIds_separated :
    SupportsSeparated (faceLinkAdjacentB 5)
      timeZeroUnitCubeSupportIds adjacentTimeUnitCubeSupportIds := by
  intro first hfirst second hsecond
  cases hadj : faceLinkAdjacentB 5 first second with
  | false => rfl
  | true =>
      have hactual := actualAdjacentOfFaceLinkAdjacent hadj
      have hfirstGeom : boxPlaquetteAt 5 first ∈
          geometricPolymer 5 timeZeroUnitCubeSupportIds :=
        List.mem_map.mpr ⟨first, hfirst, rfl⟩
      have hsecondGeom : boxPlaquetteAt 5 second ∈
          geometricPolymer 5 adjacentTimeUnitCubeSupportIds :=
        List.mem_map.mpr ⟨second, hsecond, rfl⟩
      have hfirstSurface := timeZeroUnitCubeSupportIds_sameSupport.1
        _ hfirstGeom
      have hsecondSurface :=
        adjacentTimeUnitCubeSupportIds_sameSupport.1 _ hsecondGeom
      have hleft := hactual.on_p
      have hright := hactual.on_q
      change z4Boundary (boxPlaquetteAt 5 first) hactual.link = true at hleft
      change z4Boundary (boxPlaquetteAt 5 second) hactual.link = true at hright
      exact False.elim
        (adjacentTimeRefinedUnitCubeSurfaces_linkDisjoint
          hfirstSurface hsecondSurface
          (of_decide_eq_true hleft) (of_decide_eq_true hright))

theorem timeSliceRoots_compatible
    {volume : Nat} (hvolume : 5 ≤ volume) :
    canonicalPolymerCompatibleB volume
      (timeZeroUnitCubeRootAt volume)
      (timeOneUnitCubeRootAt volume) = true := by
  apply canonicalPolymerCompatibleB_true_of
  · exact supportsDisjoint_transport hvolume
      (canonicalSurfacePolymer_mem_faceSupports
        timeZeroUnitCubeSupportIds_canonical)
      (canonicalSurfacePolymer_mem_faceSupports
        adjacentTimeUnitCubeSupportIds_mem_canonicalSurfacePolymers)
      timeSliceSupportIds_disjoint
  · exact supportsSeparated_transport hvolume
      (canonicalSurfacePolymer_mem_faceSupports
        timeZeroUnitCubeSupportIds_canonical)
      (canonicalSurfacePolymer_mem_faceSupports
        adjacentTimeUnitCubeSupportIds_mem_canonicalSurfacePolymers)
      timeSliceSupportIds_separated

theorem timeSliceRoots_distinct
    {volume : Nat} (hvolume : 5 ≤ volume) :
    timeZeroUnitCubeRootAt volume ≠ timeOneUnitCubeRootAt volume := by
  intro heq
  have hcompatible := timeSliceRoots_compatible hvolume
  have hinvariants := canonicalPolymerCompatibleB_true_invariants hcompatible
  obtain ⟨face, hface⟩ := canonicalSurfacePolymers_allNonempty volume
    (timeZeroUnitCubeRootAt volume)
    (timeZeroUnitCubeRootAt_canonical hvolume)
  exact hinvariants.1 face hface (heq ▸ hface)

/-! ## 4. Exact finite additivity for the arbitrary-coupling physical law -/

private theorem listQSum_filter_or_disjoint_local {A : Type}
    (weight : A → Q') (first second : A → Bool) :
    ∀ source : List A,
      (∀ item, item ∈ source → first item = true →
        second item = false) →
      listQSum weight
          (source.filter (fun item => first item || second item)) ≈
        listQSum weight (source.filter first) +
          listQSum weight (source.filter second)
  | [], _ => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))
  | head :: tail, hdisjoint => by
      have htail := listQSum_filter_or_disjoint_local
        weight first second tail
        (fun item hitem =>
          hdisjoint item (List.mem_cons_of_mem head hitem))
      cases hfirst : first head <;> cases hsecond : second head
      · simpa [hfirst, hsecond] using htail
      · simp only [List.filter_cons, hfirst, hsecond, Bool.false_or,
          ↓reduceIte, listQSum]
        refine Q'.eqv_trans _
          (weight head +
            (listQSum weight (tail.filter first) +
              listQSum weight (tail.filter second))) _
          (Q'.add_eqv_congr_left (weight head) _ _ htail) ?_
        refine Q'.eqv_trans _
          ((weight head + listQSum weight (tail.filter first)) +
            listQSum weight (tail.filter second)) _
          (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
        refine Q'.eqv_trans _
          ((listQSum weight (tail.filter first) + weight head) +
            listQSum weight (tail.filter second)) _
          (Q'.add_eqv_congr_right _ _ _
            (Q'.add_comm_eqv _ _)) ?_
        exact Q'.add_assoc_eqv _ _ _
      · simp only [List.filter_cons, hfirst, hsecond, Bool.true_or,
          ↓reduceIte, listQSum]
        refine Q'.eqv_trans _
          (weight head +
            (listQSum weight (tail.filter first) +
              listQSum weight (tail.filter second))) _
          (Q'.add_eqv_congr_left (weight head) _ _ htail) ?_
        exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
      · have hfalse := hdisjoint head List.mem_cons_self hfirst
        simp_all

theorem couplingParametricKCompatibleEventProbability_union_eqv_add
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat)
    (first second : List (List Nat) → Bool)
    (hdisjoint : ∀ family, first family = true →
      second family = false) :
    couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff volume
        (fun family => first family || second family) ≈
      couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff volume first +
        couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff volume second := by
  have hnumerator :
      couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff volume
          (fun family => first family || second family) ≈
        couplingParametricKCompatibleSupportEventNumerator
            coupling cutoff volume first +
          couplingParametricKCompatibleSupportEventNumerator
            coupling cutoff volume second := by
    unfold couplingParametricKCompatibleSupportEventNumerator
    exact listQSum_filter_or_disjoint_local
      (couplingParametricKSupportFamilyActivity
        coupling cutoff volume)
      first second (canonicalCompatibleAmbientFamilies volume)
      (fun family _ => hdisjoint family)
  unfold couplingParametricKCompatibleSupportEventProbability Q'.divPos
  refine Q'.eqv_trans _
    ((couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff volume first +
        couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff volume second) *
      Q'.recipPos
        (couplingParametricKCompatibleSupportGasPartition
          coupling cutoff volume)
        (couplingParametricKCompatibleSupportGasPartition_pos
          hcoupling cutoff volume)) _
    (Q'.mul_eqv_congr_right _ _ _ hnumerator) ?_
  exact Q'.add_mul_eqv _ _ _

theorem couplingKFamilyEventProbability_union_eqv_add
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat)
    (first second : List (List Nat) → Bool)
    (hdisjoint : ∀ family, first family = true →
      second family = false) :
    couplingKFamilyEventProbability coupling hcoupling cutoff volume
        (fun family => first family || second family) ≈
      couplingKFamilyEventProbability coupling hcoupling cutoff volume first +
        couplingKFamilyEventProbability
          coupling hcoupling cutoff volume second := by
  have hunion := couplingParametricKCompatibleEventProbability_union_eqv_add
    coupling hcoupling cutoff volume first second hdisjoint
  have hall := couplingKFamilyEventProbability_eqv_compatible
    coupling hcoupling cutoff volume
      (fun family => first family || second family)
  have hfirst := couplingKFamilyEventProbability_eqv_compatible
    coupling hcoupling cutoff volume first
  have hsecond := couplingKFamilyEventProbability_eqv_compatible
    coupling hcoupling cutoff volume second
  exact Q'.eqv_trans _ _ _ hall
    (Q'.eqv_trans _ _ _ hunion
      (Q'.eqv_symm (Q'.add_eqv_congr' hfirst hsecond)))

theorem couplingKFamilyEventProbability_true_eqv_one
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    couplingKFamilyEventProbability coupling hcoupling cutoff volume
        (fun _ => true) ≈ (1 : Q') := by
  unfold couplingKFamilyEventProbability
    parametricKEventNumerator parametricKEventTerm
    cutoffOneLiftedFamilyEvent parametricKPhysicalPartition Q'.divPos
  simp only [if_true]
  exact Q'.mul_recipPos_eqv _
    (couplingKPhysicalPartition_pos hcoupling cutoff volume)

/-! ## 4. The adjacent-time two-bit law and exact marginals -/

def boolOutcomeMatches (observed outcome : Bool) : Bool :=
  if outcome then observed else !observed

def unitCubeOutcomeEvent (root : List Nat) (outcome : Bool)
    (family : List (List Nat)) : Bool :=
  boolOutcomeMatches (familyContainsPolymerB root family) outcome

def adjacentTimeOutcomeEvent (volume : Nat)
    (firstOutcome secondOutcome : Bool)
    (family : List (List Nat)) : Bool :=
  unitCubeOutcomeEvent (timeZeroUnitCubeRootAt volume)
      firstOutcome family &&
    unitCubeOutcomeEvent (timeOneUnitCubeRootAt volume)
      secondOutcome family

def adjacentTimeJointProbability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat)
    (firstOutcome secondOutcome : Bool) : Q' :=
  couplingKFamilyEventProbability coupling hcoupling cutoff volume
    (adjacentTimeOutcomeEvent volume firstOutcome secondOutcome)

def timeZeroMarginalProbability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (outcome : Bool) : Q' :=
  couplingKFamilyEventProbability coupling hcoupling cutoff volume
    (unitCubeOutcomeEvent (timeZeroUnitCubeRootAt volume) outcome)

def timeOneMarginalProbability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (outcome : Bool) : Q' :=
  couplingKFamilyEventProbability coupling hcoupling cutoff volume
    (unitCubeOutcomeEvent (timeOneUnitCubeRootAt volume) outcome)

theorem adjacentTimeJointProbability_nonnegative
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (firstOutcome secondOutcome : Bool) :
    (0 : Q') ≤ adjacentTimeJointProbability
      coupling hcoupling cutoff volume firstOutcome secondOutcome :=
  couplingKFamilyEventProbability_nonnegative
    coupling hcoupling cutoff volume _

theorem adjacentTimeJointProbability_le_one
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (firstOutcome secondOutcome : Bool) :
    adjacentTimeJointProbability coupling hcoupling cutoff volume
        firstOutcome secondOutcome ≤ (1 : Q') :=
  couplingKFamilyEventProbability_le_one
    coupling hcoupling cutoff volume _

theorem adjacentTime_first_partition
    (volume : Nat) (firstOutcome : Bool) (family : List (List Nat)) :
    (adjacentTimeOutcomeEvent volume firstOutcome false family ||
        adjacentTimeOutcomeEvent volume firstOutcome true family) =
      unitCubeOutcomeEvent (timeZeroUnitCubeRootAt volume)
        firstOutcome family := by
  unfold adjacentTimeOutcomeEvent unitCubeOutcomeEvent boolOutcomeMatches
  cases firstOutcome <;>
    cases familyContainsPolymerB (timeZeroUnitCubeRootAt volume) family <;>
    cases familyContainsPolymerB (timeOneUnitCubeRootAt volume) family <;>
    rfl

theorem adjacentTime_second_partition
    (volume : Nat) (secondOutcome : Bool) (family : List (List Nat)) :
    (adjacentTimeOutcomeEvent volume false secondOutcome family ||
        adjacentTimeOutcomeEvent volume true secondOutcome family) =
      unitCubeOutcomeEvent (timeOneUnitCubeRootAt volume)
        secondOutcome family := by
  unfold adjacentTimeOutcomeEvent unitCubeOutcomeEvent boolOutcomeMatches
  cases secondOutcome <;>
    cases familyContainsPolymerB (timeZeroUnitCubeRootAt volume) family <;>
    cases familyContainsPolymerB (timeOneUnitCubeRootAt volume) family <;>
    rfl

theorem adjacentTime_first_atoms_disjoint
    (volume : Nat) (firstOutcome : Bool) (family : List (List Nat))
    (hfirst : adjacentTimeOutcomeEvent
      volume firstOutcome false family = true) :
    adjacentTimeOutcomeEvent volume firstOutcome true family = false := by
  unfold adjacentTimeOutcomeEvent unitCubeOutcomeEvent
    boolOutcomeMatches at *
  cases firstOutcome <;>
    cases hzero : familyContainsPolymerB
      (timeZeroUnitCubeRootAt volume) family <;>
    cases hone : familyContainsPolymerB
      (timeOneUnitCubeRootAt volume) family <;>
    simp_all

theorem adjacentTime_second_atoms_disjoint
    (volume : Nat) (secondOutcome : Bool) (family : List (List Nat))
    (hfirst : adjacentTimeOutcomeEvent
      volume false secondOutcome family = true) :
    adjacentTimeOutcomeEvent volume true secondOutcome family = false := by
  unfold adjacentTimeOutcomeEvent unitCubeOutcomeEvent
    boolOutcomeMatches at *
  cases secondOutcome <;>
    cases hzero : familyContainsPolymerB
      (timeZeroUnitCubeRootAt volume) family <;>
    cases hone : familyContainsPolymerB
      (timeOneUnitCubeRootAt volume) family <;>
    simp_all

theorem timeZeroMarginal_eqv_joint_sum
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (firstOutcome : Bool) :
    timeZeroMarginalProbability coupling hcoupling cutoff volume
        firstOutcome ≈
      adjacentTimeJointProbability coupling hcoupling cutoff volume
          firstOutcome false +
        adjacentTimeJointProbability coupling hcoupling cutoff volume
          firstOutcome true := by
  have hadd := couplingKFamilyEventProbability_union_eqv_add
    coupling hcoupling cutoff volume
    (adjacentTimeOutcomeEvent volume firstOutcome false)
    (adjacentTimeOutcomeEvent volume firstOutcome true)
    (adjacentTime_first_atoms_disjoint volume firstOutcome)
  unfold timeZeroMarginalProbability adjacentTimeJointProbability
  rw [show
    (fun family =>
      adjacentTimeOutcomeEvent volume firstOutcome false family ||
        adjacentTimeOutcomeEvent volume firstOutcome true family) =
      unitCubeOutcomeEvent (timeZeroUnitCubeRootAt volume) firstOutcome
    from funext (adjacentTime_first_partition volume firstOutcome)] at hadd
  exact hadd

theorem timeOneMarginal_eqv_joint_sum
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (secondOutcome : Bool) :
    timeOneMarginalProbability coupling hcoupling cutoff volume
        secondOutcome ≈
      adjacentTimeJointProbability coupling hcoupling cutoff volume
          false secondOutcome +
        adjacentTimeJointProbability coupling hcoupling cutoff volume
          true secondOutcome := by
  have hadd := couplingKFamilyEventProbability_union_eqv_add
    coupling hcoupling cutoff volume
    (adjacentTimeOutcomeEvent volume false secondOutcome)
    (adjacentTimeOutcomeEvent volume true secondOutcome)
    (adjacentTime_second_atoms_disjoint volume secondOutcome)
  unfold timeOneMarginalProbability adjacentTimeJointProbability
  rw [show
    (fun family =>
      adjacentTimeOutcomeEvent volume false secondOutcome family ||
        adjacentTimeOutcomeEvent volume true secondOutcome family) =
      unitCubeOutcomeEvent (timeOneUnitCubeRootAt volume) secondOutcome
    from funext (adjacentTime_second_partition volume secondOutcome)] at hadd
  exact hadd

theorem timeZeroMarginals_normalized
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    timeZeroMarginalProbability coupling hcoupling cutoff volume false +
        timeZeroMarginalProbability coupling hcoupling cutoff volume true ≈
      (1 : Q') := by
  have hadd := couplingKFamilyEventProbability_union_eqv_add
    coupling hcoupling cutoff volume
    (unitCubeOutcomeEvent (timeZeroUnitCubeRootAt volume) false)
    (unitCubeOutcomeEvent (timeZeroUnitCubeRootAt volume) true)
    (by
      intro family hfalse
      unfold unitCubeOutcomeEvent boolOutcomeMatches at *
      cases hvalue : familyContainsPolymerB
        (timeZeroUnitCubeRootAt volume) family <;> simp_all)
  have hall :
      (fun family =>
        unitCubeOutcomeEvent (timeZeroUnitCubeRootAt volume) false family ||
          unitCubeOutcomeEvent
            (timeZeroUnitCubeRootAt volume) true family) =
        (fun _ => true) := by
    funext family
    unfold unitCubeOutcomeEvent boolOutcomeMatches
    cases familyContainsPolymerB
      (timeZeroUnitCubeRootAt volume) family <;> rfl
  unfold timeZeroMarginalProbability
  rw [hall] at hadd
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hadd)
    (couplingKFamilyEventProbability_true_eqv_one
      coupling hcoupling cutoff volume)

def adjacentTimeJointTotal
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) : Q' :=
  (adjacentTimeJointProbability coupling hcoupling cutoff volume false false +
    adjacentTimeJointProbability coupling hcoupling cutoff volume false true) +
  (adjacentTimeJointProbability coupling hcoupling cutoff volume true false +
    adjacentTimeJointProbability coupling hcoupling cutoff volume true true)

theorem adjacentTimeJointTotal_eqv_one
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    adjacentTimeJointTotal coupling hcoupling cutoff volume ≈ (1 : Q') := by
  unfold adjacentTimeJointTotal
  exact Q'.eqv_trans _
    (timeZeroMarginalProbability coupling hcoupling cutoff volume false +
      timeZeroMarginalProbability coupling hcoupling cutoff volume true) _
    (Q'.add_eqv_congr'
      (Q'.eqv_symm (timeZeroMarginal_eqv_joint_sum
        coupling hcoupling cutoff volume false))
      (Q'.eqv_symm (timeZeroMarginal_eqv_joint_sum
        coupling hcoupling cutoff volume true)))
    (timeZeroMarginals_normalized coupling hcoupling cutoff volume)

/-! ## 5. Honest L2 positivity and the reflection-positivity fence -/

def adjacentTimeOutcomeSquareForm
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (coefficient : Bool → Bool → Q') : Q' :=
  (adjacentTimeJointProbability coupling hcoupling cutoff volume false false *
      (coefficient false false * coefficient false false) +
    adjacentTimeJointProbability coupling hcoupling cutoff volume false true *
      (coefficient false true * coefficient false true)) +
  (adjacentTimeJointProbability coupling hcoupling cutoff volume true false *
      (coefficient true false * coefficient true false) +
    adjacentTimeJointProbability coupling hcoupling cutoff volume true true *
      (coefficient true true * coefficient true true))

theorem adjacentTimeOutcomeSquareForm_nonnegative
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (coefficient : Bool → Bool → Q') :
    (0 : Q') ≤ adjacentTimeOutcomeSquareForm
      coupling hcoupling cutoff volume coefficient := by
  unfold adjacentTimeOutcomeSquareForm
  apply Q'.zero_le_add
  · apply Q'.zero_le_add
    · exact Q'.mul_nonneg _ _
        (adjacentTimeJointProbability_nonnegative
          coupling hcoupling cutoff volume false false)
        (SumOfSquares.q_mul_self_nonneg (coefficient false false))
    · exact Q'.mul_nonneg _ _
        (adjacentTimeJointProbability_nonnegative
          coupling hcoupling cutoff volume false true)
        (SumOfSquares.q_mul_self_nonneg (coefficient false true))
  · apply Q'.zero_le_add
    · exact Q'.mul_nonneg _ _
        (adjacentTimeJointProbability_nonnegative
          coupling hcoupling cutoff volume true false)
        (SumOfSquares.q_mul_self_nonneg (coefficient true false))
    · exact Q'.mul_nonneg _ _
        (adjacentTimeJointProbability_nonnegative
          coupling hcoupling cutoff volume true true)
        (SumOfSquares.q_mul_self_nonneg (coefficient true true))

/-- The symmetric, normalized anti-diagonal two-point law. -/
def antiDiagonalBoolJoint : Bool → Bool → Q'
  | false, true => Q'.mkPos 1 2 (by decide)
  | true, false => Q'.mkPos 1 2 (by decide)
  | _, _ => 0

theorem antiDiagonalBoolJoint_nonnegative (first second : Bool) :
    (0 : Q') ≤ antiDiagonalBoolJoint first second := by
  cases first <;> cases second <;> decide

theorem antiDiagonalBoolJoint_symmetric (first second : Bool) :
    antiDiagonalBoolJoint first second =
      antiDiagonalBoolJoint second first := by
  cases first <;> cases second <;> rfl

theorem antiDiagonalBoolJoint_normalized :
    (antiDiagonalBoolJoint false false +
      antiDiagonalBoolJoint false true) +
    (antiDiagonalBoolJoint true false +
      antiDiagonalBoolJoint true true) ≈ (1 : Q') := by
  decide

def boolReflectionQuadraticForm
    (joint : Bool → Bool → Q')
    (coefficient : Bool → Q') : Q' :=
  (joint false false *
      (coefficient false * coefficient false) +
    joint false true *
      (coefficient false * coefficient true)) +
  (joint true false *
      (coefficient true * coefficient false) +
    joint true true *
      (coefficient true * coefficient true))

def antiDiagonalWitnessCoefficient : Bool → Q'
  | false => 1
  | true => -1

/-- Nonnegative, normalized, symmetric two-time data do not by themselves
imply reflection/Gram positivity. -/
theorem antiDiagonal_reflectionQuadraticForm_negative :
    boolReflectionQuadraticForm antiDiagonalBoolJoint
      antiDiagonalWitnessCoefficient < (0 : Q') := by
  decide

#print axioms edgesOf_euclideanTimeTranslatePlaquette
#print axioms adjacentTimeRefinedUnitCubeSurface_connected
#print axioms adjacentTimeRefinedUnitCubeSurface_subset_box_five
#print axioms adjacentTimeUnitCubeSupportIds_sameSupport
#print axioms adjacentTimeUnitCubeSupportIds_mem_canonicalSurfacePolymers
#print axioms adjacentTimeRefinedUnitCubeSurfaces_linkDisjoint
#print axioms timeSliceSupportIds_disjoint
#print axioms timeSliceSupportIds_separated
#print axioms timeSliceRoots_compatible
#print axioms timeSliceRoots_distinct
#print axioms couplingKFamilyEventProbability_union_eqv_add
#print axioms timeZeroMarginal_eqv_joint_sum
#print axioms timeOneMarginal_eqv_joint_sum
#print axioms adjacentTimeJointTotal_eqv_one
#print axioms adjacentTimeOutcomeSquareForm_nonnegative
#print axioms antiDiagonal_reflectionQuadraticForm_negative

end YMGap.Continuum.Z4AdjacentTimeUnitCubeCylinder
