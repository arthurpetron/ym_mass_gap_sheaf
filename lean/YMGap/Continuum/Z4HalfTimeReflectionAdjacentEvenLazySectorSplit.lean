/-
# Reflection-sector split for adjacent-even lazy quaternion features

The global rational-polynomial SOS is kept lazy: one selected term is a list
of face-feature polynomials on a common physical-link coordinate carrier.  To
turn such a selected feature into two half-amplitudes, the geometric split
must happen before any raw polynomial product is expanded.

This leaf records that split at the list level.  First, the complete
boundary-link carrier is partitioned into negative-time, reflection-plane,
and positive-time blocks, with the existing active-link carrier identified
exactly as the plane block.  Second, a finite list of selected face features
`(plaquette, localTerm)` is stably partitioned by the side of its plaquette.
Mapping each selection to its shared-link polynomial gives an exact
permutation of raw factor lists and hence an exact multiplicative evaluation
split.

For the production fixed-face family the negative and positive face sectors
are literally empty: every selected polynomial is a plane factor.  Its square
is therefore represented by two identical lazy copies, one for each half;
this statement does not claim reflection covariance of an individual
polynomial or identify the resulting Haar contraction with the spin kernel.

No slab list, packed term family, or raw polynomial product is evaluated in
this file.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionLazyGlobalSOS
import YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenLazySectorSplit

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPoly
open YMGap.Continuum.SU2QuaternionLazyGlobalSOS
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceDensitySOS
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The complete link carrier, split at the reflection plane -/

/-- Negative-time links in the complete adjacent-even slab carrier. -/
def adjacentEvenNegativeSlabLinks (radius : Nat) : List Z4Link :=
  (adjacentEvenSlabLinkParts radius).1

/-- Links lying on the adjacent-even reflection plane. -/
def adjacentEvenPlaneSlabLinks (radius : Nat) : List Z4Link :=
  (adjacentEvenSlabLinkParts radius).2.1

/-- Positive-time links in the complete adjacent-even slab carrier. -/
def adjacentEvenPositiveSlabLinks (radius : Nat) : List Z4Link :=
  (adjacentEvenSlabLinkParts radius).2.2

/-- The three stable link sectors reindex the complete deduplicated slab-link
carrier exactly. -/
theorem adjacentEvenSlabLinkSectors_perm (radius : Nat) :
    (adjacentEvenNegativeSlabLinks radius ++
      adjacentEvenPlaneSlabLinks radius ++
      adjacentEvenPositiveSlabLinks radius).Perm
        (boundaryCompleteSlabLinks (adjacentEvenExtent radius)) := by
  exact adjacentEvenSlabLinkParts_perm radius

/-- The plane sector is not a new carrier: it is definitionally the existing
active-link carrier used by every globally substituted fixed-face feature. -/
theorem adjacentEvenPlaneSlabLinks_eq_activeLinks (radius : Nat) :
    adjacentEvenPlaneSlabLinks radius =
      adjacentEvenActiveLinks radius := rfl

theorem mem_adjacentEvenNegativeSlabLinks
    {radius : Nat} {link : Z4Link} :
    link ∈ adjacentEvenNegativeSlabLinks radius ↔
      link ∈ boundaryCompleteSlabLinks (adjacentEvenExtent radius) ∧
      adjacentEvenLinkSide radius link = .lower := by
  exact mem_partitionBySide_lower _ _ _

theorem mem_adjacentEvenPlaneSlabLinks
    {radius : Nat} {link : Z4Link} :
    link ∈ adjacentEvenPlaneSlabLinks radius ↔
      link ∈ boundaryCompleteSlabLinks (adjacentEvenExtent radius) ∧
      adjacentEvenLinkSide radius link = .fixed := by
  exact mem_partitionBySide_fixed _ _ _

theorem mem_adjacentEvenPositiveSlabLinks
    {radius : Nat} {link : Z4Link} :
    link ∈ adjacentEvenPositiveSlabLinks radius ↔
      link ∈ boundaryCompleteSlabLinks (adjacentEvenExtent radius) ∧
      adjacentEvenLinkSide radius link = .upper := by
  exact mem_partitionBySide_upper _ _ _

/-- Scalar quaternion-coordinate counts split additively across the three
link sectors.  This is the numerical reindexing boundary needed by blockwise
product Haar; no coordinate environment is evaluated. -/
theorem adjacentEvenSlabLinkSector_coordinateCount
    (radius : Nat) :
    4 * (boundaryCompleteSlabLinks
          (adjacentEvenExtent radius)).length =
      4 * (adjacentEvenNegativeSlabLinks radius).length +
        4 * (adjacentEvenPlaneSlabLinks radius).length +
        4 * (adjacentEvenPositiveSlabLinks radius).length := by
  have hlength := (adjacentEvenSlabLinkSectors_perm radius).length_eq
  simp only [List.length_append] at hlength
  omega

/-! ## 2. Stable sectors of selected face features -/

/-- One selected term of one face packet, still tagged by its physical
plaquette. -/
abbrev SelectedAnchorFaceFeature : Type := Z4Plaq × Nat

/-- Stable negative/plane/positive partition of selected face features. -/
def adjacentEvenSelectedFaceFeatureParts
    (radius : Nat) (selected : List SelectedAnchorFaceFeature) :
    List SelectedAnchorFaceFeature ×
      List SelectedAnchorFaceFeature ×
      List SelectedAnchorFaceFeature :=
  partitionBySide
    (fun entry => adjacentEvenPlaquetteSide radius entry.1)
    selected

def adjacentEvenNegativeSelectedFaceFeatures
    (radius : Nat) (selected : List SelectedAnchorFaceFeature) :
    List SelectedAnchorFaceFeature :=
  (adjacentEvenSelectedFaceFeatureParts radius selected).1

def adjacentEvenPlaneSelectedFaceFeatures
    (radius : Nat) (selected : List SelectedAnchorFaceFeature) :
    List SelectedAnchorFaceFeature :=
  (adjacentEvenSelectedFaceFeatureParts radius selected).2.1

def adjacentEvenPositiveSelectedFaceFeatures
    (radius : Nat) (selected : List SelectedAnchorFaceFeature) :
    List SelectedAnchorFaceFeature :=
  (adjacentEvenSelectedFaceFeatureParts radius selected).2.2

theorem adjacentEvenSelectedFaceFeatureSectors_perm
    (radius : Nat) (selected : List SelectedAnchorFaceFeature) :
    (adjacentEvenNegativeSelectedFaceFeatures radius selected ++
      adjacentEvenPlaneSelectedFaceFeatures radius selected ++
      adjacentEvenPositiveSelectedFaceFeatures radius selected).Perm
        selected := by
  exact partitionBySide_perm _ _

theorem mem_adjacentEvenNegativeSelectedFaceFeatures
    {radius : Nat} {selected : List SelectedAnchorFaceFeature}
    {entry : SelectedAnchorFaceFeature} :
    entry ∈ adjacentEvenNegativeSelectedFaceFeatures radius selected ↔
      entry ∈ selected ∧
        adjacentEvenPlaquetteSide radius entry.1 = .lower := by
  exact mem_partitionBySide_lower _ _ _

theorem mem_adjacentEvenPlaneSelectedFaceFeatures
    {radius : Nat} {selected : List SelectedAnchorFaceFeature}
    {entry : SelectedAnchorFaceFeature} :
    entry ∈ adjacentEvenPlaneSelectedFaceFeatures radius selected ↔
      entry ∈ selected ∧
        adjacentEvenPlaquetteSide radius entry.1 = .fixed := by
  exact mem_partitionBySide_fixed _ _ _

theorem mem_adjacentEvenPositiveSelectedFaceFeatures
    {radius : Nat} {selected : List SelectedAnchorFaceFeature}
    {entry : SelectedAnchorFaceFeature} :
    entry ∈ adjacentEvenPositiveSelectedFaceFeatures radius selected ↔
      entry ∈ selected ∧
        adjacentEvenPlaquetteSide radius entry.1 = .upper := by
  exact mem_partitionBySide_upper _ _ _

/-! ## 3. Exact lazy polynomial-factor split -/

/-- Map selected face terms to their substituted polynomials in one common
physical-link carrier.  This maps a list; it never multiplies its entries. -/
def selectedGlobalAnchorFaceFactors
    (cutoff : Nat) (links : List Z4Link)
    (selected : List SelectedAnchorFaceFeature) : List RatPoly :=
  selected.map (fun entry =>
    globalAnchorFaceFeaturePolynomial cutoff links entry.1 entry.2)

def adjacentEvenNegativeGlobalFaceFactors
    (cutoff radius : Nat) (links : List Z4Link)
    (selected : List SelectedAnchorFaceFeature) : List RatPoly :=
  selectedGlobalAnchorFaceFactors cutoff links
    (adjacentEvenNegativeSelectedFaceFeatures radius selected)

def adjacentEvenPlaneGlobalFaceFactors
    (cutoff radius : Nat) (links : List Z4Link)
    (selected : List SelectedAnchorFaceFeature) : List RatPoly :=
  selectedGlobalAnchorFaceFactors cutoff links
    (adjacentEvenPlaneSelectedFaceFeatures radius selected)

def adjacentEvenPositiveGlobalFaceFactors
    (cutoff radius : Nat) (links : List Z4Link)
    (selected : List SelectedAnchorFaceFeature) : List RatPoly :=
  selectedGlobalAnchorFaceFactors cutoff links
    (adjacentEvenPositiveSelectedFaceFeatures radius selected)

/-- Reindexing selected faces by geometric sector gives an exact permutation
of the corresponding unexpanded polynomial factors. -/
theorem adjacentEvenGlobalFaceFactorSectors_perm
    (cutoff radius : Nat) (links : List Z4Link)
    (selected : List SelectedAnchorFaceFeature) :
    (adjacentEvenNegativeGlobalFaceFactors
        cutoff radius links selected ++
      adjacentEvenPlaneGlobalFaceFactors
        cutoff radius links selected ++
      adjacentEvenPositiveGlobalFaceFactors
        cutoff radius links selected).Perm
      (selectedGlobalAnchorFaceFactors cutoff links selected) := by
  unfold adjacentEvenNegativeGlobalFaceFactors
    adjacentEvenPlaneGlobalFaceFactors
    adjacentEvenPositiveGlobalFaceFactors
    selectedGlobalAnchorFaceFactors
  simpa only [List.map_append] using
    (adjacentEvenSelectedFaceFeatureSectors_perm
      radius selected).map (fun entry =>
        globalAnchorFaceFeaturePolynomial cutoff links entry.1 entry.2)

/-- Lazy factor evaluation is invariant under every finite permutation. -/
theorem evalRatPolyFactors_perm (rho : Nat → Q') :
    ∀ {left right : List RatPoly}, left.Perm right →
      evalRatPolyFactors rho left ≈ evalRatPolyFactors rho right
  | _, _, List.Perm.nil => Q'.eqv_refl 1
  | _, _, List.Perm.cons _ hperm =>
      Q'.mul_eqv_congr_left _ _ _
        (evalRatPolyFactors_perm rho hperm)
  | _, _, List.Perm.swap first second rest => by
      change
        evalRatPoly rho second *
            (evalRatPoly rho first * evalRatPolyFactors rho rest) ≈
          evalRatPoly rho first *
            (evalRatPoly rho second * evalRatPolyFactors rho rest)
      refine Q'.eqv_trans _
        ((evalRatPoly rho second * evalRatPoly rho first) *
          evalRatPolyFactors rho rest) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((evalRatPoly rho first * evalRatPoly rho second) *
          evalRatPolyFactors rho rest) _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
  | _, _, List.Perm.trans hleft hright =>
      Q'.eqv_trans _ _ _
        (evalRatPolyFactors_perm rho hleft)
        (evalRatPolyFactors_perm rho hright)

/-- **Exact reflection-sector factorization.**  Evaluation of a selected lazy
global feature is the negative-sector value times the plane-sector value
times the positive-sector value.  The association is chosen to match the
right-recursive factor-list evaluator. -/
theorem eval_selectedGlobalAnchorFaceFactors_sector_split
    (cutoff radius : Nat) (links : List Z4Link)
    (selected : List SelectedAnchorFaceFeature) (rho : Nat → Q') :
    evalRatPolyFactors rho
        (selectedGlobalAnchorFaceFactors cutoff links selected) ≈
      evalRatPolyFactors rho
          (adjacentEvenNegativeGlobalFaceFactors
            cutoff radius links selected) *
        (evalRatPolyFactors rho
            (adjacentEvenPlaneGlobalFaceFactors
              cutoff radius links selected) *
          evalRatPolyFactors rho
            (adjacentEvenPositiveGlobalFaceFactors
              cutoff radius links selected)) := by
  let negative := adjacentEvenNegativeGlobalFaceFactors
    cutoff radius links selected
  let plane := adjacentEvenPlaneGlobalFaceFactors
    cutoff radius links selected
  let positive := adjacentEvenPositiveGlobalFaceFactors
    cutoff radius links selected
  have hperm : (negative ++ plane ++ positive).Perm
      (selectedGlobalAnchorFaceFactors cutoff links selected) := by
    exact adjacentEvenGlobalFaceFactorSectors_perm
      cutoff radius links selected
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (evalRatPolyFactors_perm rho hperm)) ?_
  refine Q'.eqv_trans _ _ _
    (evalRatPolyFactors_append rho (negative ++ plane) positive) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (evalRatPolyFactors_append rho negative plane)) ?_
  exact Q'.mul_assoc_eqv _ _ _

/-! ## 4. Shared-field semantics without polynomial expansion -/

/-- Physical value of a selected list of existing face-SOS features. -/
def selectedLatticeAnchorFaceFeatureProduct
    (cutoff : Nat) (field : RationalUnitQuaternionGaugeField) :
    List SelectedAnchorFaceFeature → Q'
  | [] => 1
  | entry :: tail =>
      (latticeAnchorFaceHolonomySOS cutoff entry.1).feature entry.2 field *
        selectedLatticeAnchorFaceFeatureProduct cutoff field tail

/-- The selected lazy factor list evaluates to the corresponding physical
feature product on one shared gauge field. -/
theorem eval_selectedGlobalAnchorFaceFactors
    (cutoff : Nat) (links : List Z4Link)
    (field : RationalUnitQuaternionGaugeField) :
    ∀ (selected : List SelectedAnchorFaceFeature),
      (∀ entry, entry ∈ selected →
        ∀ link, link ∈ edgesOf entry.1 → link ∈ links) →
      evalRatPolyFactors (globalLinkEnvironment links field)
          (selectedGlobalAnchorFaceFactors cutoff links selected) ≈
        selectedLatticeAnchorFaceFeatureProduct cutoff field selected
  | [], _ => Q'.eqv_refl 1
  | entry :: tail, hsupport => by
      change
        evalRatPoly (globalLinkEnvironment links field)
            (globalAnchorFaceFeaturePolynomial
              cutoff links entry.1 entry.2) *
            evalRatPolyFactors (globalLinkEnvironment links field)
              (selectedGlobalAnchorFaceFactors cutoff links tail) ≈
          (latticeAnchorFaceHolonomySOS cutoff entry.1).feature
              entry.2 field *
            selectedLatticeAnchorFaceFeatureProduct cutoff field tail
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (eval_globalAnchorFaceFeaturePolynomial
            cutoff links entry.1 entry.2 field
            (fun link hlink =>
              hsupport entry List.mem_cons_self link hlink)))
        (Q'.mul_eqv_congr_left _ _ _
          (eval_selectedGlobalAnchorFaceFactors cutoff links field tail
            (fun source hsource link hlink =>
              hsupport source
                (List.mem_cons_of_mem entry hsource) link hlink)))

/-! ## 5. The production fixed-face family is entirely on the plane -/

/-- Select one local feature term for every production fixed face while
preserving the established face order. -/
def adjacentEvenFixedFaceFeatureSelection
    (radius : Nat) (term : Z4Plaq → Nat) :
    List SelectedAnchorFaceFeature :=
  (adjacentEvenFixedFacePlaquettes radius).map
    (fun plaquette => (plaquette, term plaquette))

private theorem partitionBySide_all_fixed
    {A : Type} (side : A → CrossPlaneSide) :
    ∀ (items : List A),
      (∀ item, item ∈ items → side item = .fixed) →
      partitionBySide side items = ([], items, [])
  | [], _ => rfl
  | head :: tail, hfixed => by
      have hhead : side head = .fixed :=
        hfixed head List.mem_cons_self
      have htail : partitionBySide side tail = ([], tail, []) :=
        partitionBySide_all_fixed side tail
          (fun item hitem =>
            hfixed item (List.mem_cons_of_mem head hitem))
      simp [partitionBySide, hhead, htail]

theorem adjacentEvenFixedFacePlaquette_side
    {radius : Nat} {plaquette : Z4Plaq}
    (hplaquette :
      plaquette ∈ adjacentEvenFixedFacePlaquettes radius) :
    adjacentEvenPlaquetteSide radius plaquette = .fixed := by
  obtain ⟨id, hid, heq⟩ := List.mem_map.mp hplaquette
  rw [← heq]
  exact (mem_adjacentEvenFixedFaceIds.mp hid).2

/-- The exact face-sector split of every selected production fixed-face
feature: no action factor has silently been moved into either open half. -/
theorem adjacentEvenFixedFaceFeatureSelection_parts
    (radius : Nat) (term : Z4Plaq → Nat) :
    adjacentEvenSelectedFaceFeatureParts radius
        (adjacentEvenFixedFaceFeatureSelection radius term) =
      ([], adjacentEvenFixedFaceFeatureSelection radius term, []) := by
  apply partitionBySide_all_fixed
  intro entry hentry
  obtain ⟨plaquette, hplaquette, heq⟩ := List.mem_map.mp hentry
  rw [← heq]
  exact adjacentEvenFixedFacePlaquette_side hplaquette

/-- Consequently the selected global polynomial list has empty negative and
positive face sectors and an unchanged plane sector. -/
theorem adjacentEvenFixedFaceGlobalFactors_plane_only
    (cutoff radius : Nat) (term : Z4Plaq → Nat) :
    adjacentEvenNegativeGlobalFaceFactors cutoff radius
        (adjacentEvenActiveLinks radius)
        (adjacentEvenFixedFaceFeatureSelection radius term) = [] ∧
      adjacentEvenPlaneGlobalFaceFactors cutoff radius
          (adjacentEvenActiveLinks radius)
          (adjacentEvenFixedFaceFeatureSelection radius term) =
        selectedGlobalAnchorFaceFactors cutoff
          (adjacentEvenActiveLinks radius)
          (adjacentEvenFixedFaceFeatureSelection radius term) ∧
      adjacentEvenPositiveGlobalFaceFactors cutoff radius
          (adjacentEvenActiveLinks radius)
          (adjacentEvenFixedFaceFeatureSelection radius term) = [] := by
  have hparts := adjacentEvenFixedFaceFeatureSelection_parts radius term
  simp [adjacentEvenNegativeGlobalFaceFactors,
    adjacentEvenPlaneGlobalFaceFactors,
    adjacentEvenPositiveGlobalFaceFactors,
    adjacentEvenNegativeSelectedFaceFeatures,
    adjacentEvenPlaneSelectedFaceFeatures,
    adjacentEvenPositiveSelectedFaceFeatures, hparts,
    selectedGlobalAnchorFaceFactors]

/-- Lazy square of one selected production plane feature.  The two copies are
the exact algebraic inputs for the two half-amplitudes; their reflection
identification remains a separate theorem. -/
def adjacentEvenFixedFaceSelectedSquareFactors
    (cutoff radius : Nat) (term : Z4Plaq → Nat) : List RatPoly :=
  let half := selectedGlobalAnchorFaceFactors cutoff
    (adjacentEvenActiveLinks radius)
    (adjacentEvenFixedFaceFeatureSelection radius term)
  half ++ half

theorem eval_adjacentEvenFixedFaceSelectedSquareFactors
    (cutoff radius : Nat) (term : Z4Plaq → Nat) (rho : Nat → Q') :
    evalRatPolyFactors rho
        (adjacentEvenFixedFaceSelectedSquareFactors
          cutoff radius term) ≈
      let half := selectedGlobalAnchorFaceFactors cutoff
        (adjacentEvenActiveLinks radius)
        (adjacentEvenFixedFaceFeatureSelection radius term)
      evalRatPolyFactors rho half * evalRatPolyFactors rho half := by
  unfold adjacentEvenFixedFaceSelectedSquareFactors
  exact evalRatPolyFactors_append _ _ _

#print axioms adjacentEvenSlabLinkSectors_perm
#print axioms adjacentEvenPlaneSlabLinks_eq_activeLinks
#print axioms adjacentEvenSlabLinkSector_coordinateCount
#print axioms adjacentEvenSelectedFaceFeatureSectors_perm
#print axioms adjacentEvenGlobalFaceFactorSectors_perm
#print axioms evalRatPolyFactors_perm
#print axioms eval_selectedGlobalAnchorFaceFactors_sector_split
#print axioms eval_selectedGlobalAnchorFaceFactors
#print axioms adjacentEvenFixedFacePlaquette_side
#print axioms adjacentEvenFixedFaceFeatureSelection_parts
#print axioms adjacentEvenFixedFaceGlobalFactors_plane_only
#print axioms eval_adjacentEvenFixedFaceSelectedSquareFactors

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenLazySectorSplit
