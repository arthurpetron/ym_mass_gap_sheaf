/-
# Binary corrected-slab supports as physical link-coherent labellings

The cellular dyadic map produces a duplicate-free geometric plaquette
support, whereas the corrected-slab Gibbs carrier is indexed by numerical
face identifiers.  This module supplies the exact bridge between those two
presentations.

A geometric support contained in the boundary-complete slab is encoded as
the zero-one `EdgeLabelling` on the slab's physical face identifiers.  The
encoding occurs in every Cartesian physical state space of cutoff at least
one.  At each slab link, the sum of the resulting numerical external word is
exactly the geometric face-incidence count of the support.  Consequently an
even-incidence support has strictly positive production link multiplicity at
every auxiliary cutoff allowed by the cutoff-one link door.

No Gibbs pushforward or RG estimate is asserted here.
-/

import YMGap.Continuum.CompactDualCutoffOneCoarseLinkDoor
import YMGap.Continuum.Z4DyadicModTwoCellularKernel
import YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

namespace YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence

set_option maxRecDepth 30000
set_option maxHeartbeats 6000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualCutoffOneCoarseLinkDoor
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4UnitCubeEnumerationParity
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-- The zero-one numerical face labelling represented by a geometric
corrected-slab support.  The explicit outer support test forces all
nonphysical numerical identifiers to zero. -/
def slabBinarySupportLabelling
    (extent : Nat) (support : List Z4Plaq) : EdgeLabelling :=
  fun id =>
    if id ∈ slabPhysicalFaceEdges extent then
      if slabPlaquetteAt extent id ∈ support then 1 else 0
    else 0

theorem slabBinarySupportLabelling_eq_indicator
    {extent : Nat} {support : List Z4Plaq} {id : Nat}
    (hid : id ∈ slabPhysicalFaceEdges extent) :
    slabBinarySupportLabelling extent support id =
      if slabPlaquetteAt extent id ∈ support then 1 else 0 := by
  unfold slabBinarySupportLabelling
  rw [if_pos hid]

theorem slabBinarySupportLabelling_le_one
    (extent : Nat) (support : List Z4Plaq) (id : Nat) :
    slabBinarySupportLabelling extent support id ≤ 1 := by
  unfold slabBinarySupportLabelling
  by_cases hphysical : id ∈ slabPhysicalFaceEdges extent
  · rw [if_pos hphysical]
    split <;> omega
  · rw [if_neg hphysical]
    omega

theorem slabBinarySupportLabelling_eq_zero_of_not_physical
    {extent : Nat} {support : List Z4Plaq} {id : Nat}
    (hid : id ∉ slabPhysicalFaceEdges extent) :
    slabBinarySupportLabelling extent support id = 0 := by
  unfold slabBinarySupportLabelling
  rw [if_neg hid]

/-- Every binary slab support is literally present in the bounded Cartesian
physical state list at any cutoff at least one. -/
theorem slabBinarySupportLabelling_mem
    {K extent : Nat} (hK : 1 ≤ K) (support : List Z4Plaq) :
    slabBinarySupportLabelling extent support ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges extent) := by
  apply boundedEdgeLabellings_complete
  · intro id hid
    have hle := slabBinarySupportLabelling_le_one extent support id
    omega
  · intro id hid
    exact slabBinarySupportLabelling_eq_zero_of_not_physical hid

private theorem natListSum_boolIndicator :
    ∀ {A : Type} (predicate : A → Bool) (entries : List A),
      natListSum (entries.map fun entry => (predicate entry).toNat) =
        (entries.filter predicate).length
  | _, _, [] => rfl
  | A, predicate, head :: tail => by
      cases hhead : predicate head <;>
        simp [natListSum, hhead, natListSum_boolIndicator predicate tail,
          Nat.add_comm]

private theorem nodup_map_of_injective_on {A B : Type}
    (f : A → B) :
    ∀ (entries : List A), entries.Nodup →
      (∀ first, first ∈ entries → ∀ second, second ∈ entries →
        f first = f second → first = second) →
      (entries.map f).Nodup
  | [], _, _ => List.nodup_nil
  | head :: tail, hnodup, hinjective => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨source, hsource, hequal⟩ := List.mem_map.mp hmem
        have hsourceEq : head = source :=
          hinjective head List.mem_cons_self source
            (List.mem_cons_of_mem head hsource) hequal.symm
        exact hparts.1 (hsourceEq ▸ hsource)
      · exact nodup_map_of_injective_on f tail hparts.2
          (fun first hfirst second hsecond =>
            hinjective first (List.mem_cons_of_mem head hfirst)
              second (List.mem_cons_of_mem head hsecond))

private theorem slabIncidentSelectedPlaquettes_perm
    {extent : Nat} {support : List Z4Plaq}
    (hsubset : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boundaryCompleteSlabPlaquettes extent)
    (hsupport : support.Nodup) (link : Z4Link) :
    (((slabIncidentPlaqIds extent link).filter fun id =>
        decide (slabPlaquetteAt extent id ∈ support)).map
      (slabPlaquetteAt extent)).Perm
        (support.filter fun plaquette => decide (link ∈ edgesOf plaquette)) := by
  apply perm_of_nodup_mem_iff
  · apply nodup_map_of_injective_on
      (slabPlaquetteAt extent)
      ((slabIncidentPlaqIds extent link).filter fun id =>
        decide (slabPlaquetteAt extent id ∈ support))
      (List.filter_sublist.nodup
        (slabIncidentPlaqIds_nodup extent link))
    intro first hfirst second hsecond hequal
    exact slabPlaquetteAt_injective_on_physical
      (slabIncidentPlaqId_physical
        (List.mem_filter.mp hfirst).1)
      (slabIncidentPlaqId_physical
        (List.mem_filter.mp hsecond).1)
      hequal
  · exact List.filter_sublist.nodup hsupport
  · intro plaquette
    constructor
    · intro hmem
      obtain ⟨id, hid, hidPlaquette⟩ := List.mem_map.mp hmem
      have hparts := List.mem_filter.mp hid
      have hincident :=
        (mem_slabIncidentPlaqIds.mp hparts.1)
      obtain ⟨source, hsourceIndexed, hsourceIncident⟩ := hincident
      have hlookup :
          slabPlaquetteAt extent id = source :=
        enumerate_getD_of_mem fallbackPlaquette hsourceIndexed
      rw [← hidPlaquette]
      apply List.mem_filter.mpr
      constructor
      · simpa only [decide_eq_true_eq] using hparts.2
      · rw [hlookup]
        simpa only [decide_eq_true_eq] using hsourceIncident
    · intro hmem
      have hparts := List.mem_filter.mp hmem
      have hslab := hsubset plaquette hparts.1
      obtain ⟨id, hidIndexed⟩ := exists_mem_enumerate hslab
      have hidPhysical : id ∈ slabPhysicalFaceEdges extent := by
        unfold slabPhysicalFaceEdges
        exact List.mem_range.mpr (enumerate_index_lt hidIndexed)
      have hlookup :
          slabPlaquetteAt extent id = plaquette :=
        enumerate_getD_of_mem fallbackPlaquette hidIndexed
      apply List.mem_map.mpr
      refine ⟨id, List.mem_filter.mpr ⟨?_, ?_⟩, hlookup⟩
      · apply mem_slabIncidentPlaqIds.mpr
        exact ⟨plaquette, hidIndexed,
          by simpa only [decide_eq_true_eq] using hparts.2⟩
      · simpa only [decide_eq_true_eq, hlookup] using hparts.1

private theorem filter_incident_length_eq_faceIncidenceCount
    (link : Z4Link) :
    ∀ support : List Z4Plaq,
      (support.filter fun plaquette =>
        decide (link ∈ edgesOf plaquette)).length =
      faceIncidenceCount link support
  | [] => rfl
  | head :: tail => by
      by_cases hincident : link ∈ edgesOf head
      · simp [faceIncidenceCount, hincident,
          filter_incident_length_eq_faceIncidenceCount link tail,
          Nat.add_comm]
      · simp [faceIncidenceCount, hincident,
          filter_incident_length_eq_faceIncidenceCount link tail]

private theorem natListSum_slabBinarySupportLabelling
    {extent : Nat} {support : List Z4Plaq}
    (hsubset : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boundaryCompleteSlabPlaquettes extent)
    (hsupport : support.Nodup) (link : Z4Link) :
    natListSum
        ((slabIncidentPlaqIds extent link).map
          (slabBinarySupportLabelling extent support)) =
      faceIncidenceCount link support := by
  have hvalues :
      (slabIncidentPlaqIds extent link).map
          (slabBinarySupportLabelling extent support) =
        (slabIncidentPlaqIds extent link).map
          (fun id =>
            (decide (slabPlaquetteAt extent id ∈ support)).toNat) := by
    apply List.map_congr_left
    intro id hid
    rw [slabBinarySupportLabelling_eq_indicator
      (slabIncidentPlaqId_physical hid)]
    by_cases hmem : slabPlaquetteAt extent id ∈ support
    · simp [hmem]
    · simp [hmem]
  rw [hvalues, natListSum_boolIndicator]
  have hperm :=
    slabIncidentSelectedPlaquettes_perm hsubset hsupport link
  have hlength := hperm.length_eq
  simp only [List.length_map] at hlength
  rw [hlength]
  exact filter_incident_length_eq_faceIncidenceCount link support

private theorem localExternalSpinSum_externalSpinsOfList
    (spins : List Nat) :
    localExternalSpinSum spins.length (externalSpinsOfList spins) =
      natListSum spins := by
  induction spins with
  | nil => rfl
  | cons head tail ih =>
      change
        natListSum
            ((List.range (tail.length + 1)).map
              (externalSpinsOfList (head :: tail))) =
          natListSum (head :: tail)
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, natListSum, List.map_map]
      change head +
          natListSum
            ((List.range tail.length).map
              (externalSpinsOfList tail)) =
        head + natListSum tail
      unfold localExternalSpinSum at ih
      rw [ih]

/-- The numerical external word at a corrected-slab link has exactly the
geometric support's incidence parity. -/
theorem slabBinarySupport_localExternalSpinSum
    {extent : Nat} {support : List Z4Plaq}
    (hsubset : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boundaryCompleteSlabPlaquettes extent)
    (hsupport : support.Nodup) (link : Z4Link) :
    localExternalSpinSum
        (slabIncidentPlaqIds extent link).length
        (externalSpinsOfList
          ((slabIncidentPlaqIds extent link).map
            (slabBinarySupportLabelling extent support))) =
      faceIncidenceCount link support := by
  have hsum := localExternalSpinSum_externalSpinsOfList
    ((slabIncidentPlaqIds extent link).map
      (slabBinarySupportLabelling extent support))
  simp only [List.length_map] at hsum
  rw [hsum]
  exact natListSum_slabBinarySupportLabelling hsubset hsupport link

/-- Even geometric incidence supplies a strictly positive production
multiplicity at every corrected-slab link. -/
theorem slabBinarySupport_linkMultiplicity_pos
    {K extent : Nat} (hK : 1 ≤ K)
    {support : List Z4Plaq}
    (hsubset : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boundaryCompleteSlabPlaquettes extent)
    (hsupport : support.Nodup)
    (heven : EvenFaceIncidence support)
    (link : Z4Link) :
    0 < slabExplicitLinkMultiplicity K extent
      (slabBinarySupportLabelling extent support) link := by
  unfold slabExplicitLinkMultiplicity
  apply binaryEvenExplicitValenceMultiplicity_pos_of_cutoff
  · unfold linkAuxiliaryCutoff linkIncidenceBound
    omega
  · simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six extent link
  · intro position hposition
    let spins :=
      (slabIncidentPlaqIds extent link).map
        (slabBinarySupportLabelling extent support)
    have hposition' : position < spins.length := by
      simpa only [spins, List.length_map] using hposition
    change spins.getD position 0 ≤ 1
    rw [← List.getElem_eq_getD (l := spins)
      (i := position) (h := hposition') 0]
    have hmem : spins[position] ∈ spins :=
      List.getElem_mem hposition'
    obtain ⟨id, _, hvalue⟩ := List.mem_map.mp hmem
    rw [← hvalue]
    exact slabBinarySupportLabelling_le_one extent support id
  · have hsum :=
      slabBinarySupport_localExternalSpinSum hsubset hsupport link
    simp only [List.length_map]
    rw [hsum]
    exact heven link

/-- The complete corrected-slab link product is strictly positive for an
even binary geometric support. -/
theorem slabBinarySupport_linkMultiplicityProduct_pos
    {K extent : Nat} (hK : 1 ≤ K)
    {support : List Z4Plaq}
    (hsubset : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boundaryCompleteSlabPlaquettes extent)
    (hsupport : support.Nodup)
    (heven : EvenFaceIncidence support) :
    0 < slabExplicitLinkMultiplicityProduct K extent
      (slabBinarySupportLabelling extent support) := by
  unfold slabExplicitLinkMultiplicityProduct
  generalize boundaryCompleteSlabLinks extent = links
  induction links with
  | nil =>
      change 0 < 1
      omega
  | cons head tail ih =>
      simp only [natListProduct]
      exact Nat.mul_pos
        (slabBinarySupport_linkMultiplicity_pos
          hK hsubset hsupport heven head)
        ih

#print axioms slabBinarySupportLabelling_mem
#print axioms slabBinarySupport_localExternalSpinSum
#print axioms slabBinarySupport_linkMultiplicity_pos
#print axioms slabBinarySupport_linkMultiplicityProduct_pos

end YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
