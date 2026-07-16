/-
# Fixed-external-label link multiplicities in canonical coordinates

The global spin-foam formula leaves one exact natural-number multiplicity at
each physical lattice link.  This file removes the remaining dependence of
that local number on the production edge identifiers.  At fixed physical
plaquette spins, the actual private-coordinate Cartesian count is transported
to the consecutive canonical `fuseLabels` chain.

This is an exact constructive reindexing, not an appeal to representation
theory: the physical coordinates retain their prescribed values, the vacuum
terminator remains forced to spin zero, and the internal carriers retain the
full `6*K` window.  The successor layer can therefore unfold only seven
canonical cases (valences zero through six) into literal fusion-path sums.
-/

import YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization

namespace YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActualLinkUsedPacketBridge
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FuseChainIdentifierTransport
open YMGap.Continuum.Z4GraphIdentifierCartesianTransport
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4LinkIdentifierFreshness

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The canonical fixed-external constraint -/

/-- In canonical coordinates the open-link vacuum terminator is the
coordinate equal to the valence.  Every other used auxiliary coordinate is
an unrestricted internal fusion carrier. -/
def canonicalAuxiliaryEdgeAllowedB (degree : Nat)
    (label : EdgeLabelling) (edge : Nat) : Bool :=
  if edge = degree then decide (label edge = 0) else true

/-- The consecutive-identifier version of one link's conditional fusion
constraint.  `external` supplies already-fixed spins on positions
`0, ..., degree-1`; `auxiliary` supplies only the private channel labels. -/
def canonicalLinkConditionalAllowedB (degree : Nat)
    (external auxiliary : EdgeLabelling) : Bool :=
  let label := overlayOn (List.range degree) external auxiliary
  verticesAdmissibleB
      (fuseLabels degree (degree + 1) (List.range degree)) label &&
    (canonicalUsedAuxiliaryCoordinates degree).all
      (canonicalAuxiliaryEdgeAllowedB degree label)

/-- Exact rational indicator sum in canonical consecutive coordinates. -/
def canonicalLinkAuxiliaryMultiplicity (cutoff degree : Nat)
    (external : EdgeLabelling) : Q' :=
  listQSum
    (fun auxiliary =>
      if canonicalLinkConditionalAllowedB degree external auxiliary
        then 1 else 0)
    (boundedEdgeLabellings cutoff
      (canonicalUsedAuxiliaryCoordinates degree))

/-- The same canonical sum as a literal natural cardinality. -/
def canonicalLinkInvariantMultiplicityCount (cutoff degree : Nat)
    (external : EdgeLabelling) : Nat :=
  ((boundedEdgeLabellings cutoff
      (canonicalUsedAuxiliaryCoordinates degree)).filter
    (canonicalLinkConditionalAllowedB degree external)).length

theorem canonicalLinkAuxiliaryMultiplicity_eq_count
    (cutoff degree : Nat) (external : EdgeLabelling) :
    canonicalLinkAuxiliaryMultiplicity cutoff degree external ≈
      Q'.ofNat
        (canonicalLinkInvariantMultiplicityCount cutoff degree external) := by
  unfold canonicalLinkAuxiliaryMultiplicity
    canonicalLinkInvariantMultiplicityCount
  exact listQSum_boolIndicator_eq_count
    (canonicalLinkConditionalAllowedB degree external)
    (boundedEdgeLabellings cutoff
      (canonicalUsedAuxiliaryCoordinates degree))

/-! ## 2. Pointwise preservation under the production renaming -/

/-- The full canonical and actual overlay labellings agree on every
coordinate read by the local resolver. -/
theorem localOverlayLabelsAgreeOnRename
    {n i : Nat} {ell : Z4Link} (physical : EdgeLabelling)
    (canonicalAuxiliary actualAuxiliary : EdgeLabelling)
    (hagree : LabelsAgreeOnRename
      (localIdentifierRename (incidentPlaqIds n ell) (linkBlockBase n i))
      (canonicalUsedAuxiliaryCoordinates (incidentPlaqIds n ell).length)
      canonicalAuxiliary actualAuxiliary) :
    LabelsAgreeOnRename
      (localIdentifierRename (incidentPlaqIds n ell) (linkBlockBase n i))
      (canonicalUsedCoordinates (incidentPlaqIds n ell).length)
      (overlayOn (List.range (incidentPlaqIds n ell).length)
        (fun edge => physical
          (localIdentifierRename (incidentPlaqIds n ell)
            (linkBlockBase n i) edge))
        canonicalAuxiliary)
      (overlayOn (List.range (plaquetteEdgeCount n))
        physical actualAuxiliary) := by
  let labels := incidentPlaqIds n ell
  let degree := labels.length
  let base := linkBlockBase n i
  let rename := localIdentifierRename labels base
  have hdegree : degree ≤ linkIncidenceBound := by
    dsimp [degree, labels]
    exact incidentPlaqIds_length_le_six n ell
  intro edge hedge
  rw [canonicalUsedCoordinates_eq_range_append_auxiliary hdegree] at hedge
  rcases List.mem_append.mp hedge with hphysical | hauxiliary
  · have hmapped : rename edge ∈ labels := by
      rw [← map_localIdentifierRename_range labels base]
      exact List.mem_map.mpr ⟨edge, hphysical, rfl⟩
    have hmappedRange : rename edge ∈
        List.range (plaquetteEdgeCount n) :=
      List.mem_range.mpr (incidentPlaqId_lt_count hmapped)
    rw [overlayOn_apply_of_mem hmappedRange,
      overlayOn_apply_of_mem hphysical]
  · have hmappedAuxiliary : rename edge ∈
        actualLinkAuxiliaryCoordinates n i ell := by
      unfold actualLinkAuxiliaryCoordinates
      dsimp only [labels, degree, base, rename]
      exact List.mem_map.mpr ⟨edge, hauxiliary, rfl⟩
    obtain ⟨offset, hmappedEq, _⟩ :=
      actualLinkAuxiliary_coordinate_shape hmappedAuxiliary
    have hmappedNotPhysical : rename edge ∉
        List.range (plaquetteEdgeCount n) := by
      intro hmem
      have hlt := List.mem_range.mp hmem
      have hbase := linkBlockBase_ge_count n i
      have hge : plaquetteEdgeCount n ≤ rename edge := by
        rw [hmappedEq]
        omega
      omega
    obtain ⟨offset', hedgeEq, _⟩ :=
      canonicalUsedAuxiliary_coordinate_shape hdegree hauxiliary
    have hedgeNotPhysical : edge ∉ List.range degree := by
      intro hmem
      have hlt := List.mem_range.mp hmem
      omega
    rw [overlayOn_apply_of_not_mem hmappedNotPhysical,
      overlayOn_apply_of_not_mem hedgeNotPhysical]
    exact hagree edge hauxiliary

/-- The actual auxiliary packet guard is exactly the canonical
vacuum-terminator guard on every used private coordinate. -/
theorem auxiliaryEdgeAllowedB_rename
    {n i : Nat} {ell : Z4Link}
    (hindexed : (i, ell) ∈ enumerate (distinctBoxLinks n))
    (physical canonicalAuxiliary actualAuxiliary : EdgeLabelling)
    (hagree : LabelsAgreeOnRename
      (localIdentifierRename (incidentPlaqIds n ell) (linkBlockBase n i))
      (canonicalUsedAuxiliaryCoordinates (incidentPlaqIds n ell).length)
      canonicalAuxiliary actualAuxiliary) :
    ∀ edge,
      edge ∈ canonicalUsedAuxiliaryCoordinates
        (incidentPlaqIds n ell).length →
      auxiliaryEdgeAllowedB n
          (overlayOn (List.range (plaquetteEdgeCount n))
            physical actualAuxiliary)
          (localIdentifierRename (incidentPlaqIds n ell)
            (linkBlockBase n i) edge) =
        canonicalAuxiliaryEdgeAllowedB (incidentPlaqIds n ell).length
          (overlayOn (List.range (incidentPlaqIds n ell).length)
            (fun position => physical
              (localIdentifierRename (incidentPlaqIds n ell)
                (linkBlockBase n i) position))
            canonicalAuxiliary) edge := by
  let labels := incidentPlaqIds n ell
  let degree := labels.length
  let base := linkBlockBase n i
  let rename := localIdentifierRename labels base
  have hdegree : degree ≤ linkIncidenceBound := by
    dsimp [degree, labels]
    exact incidentPlaqIds_length_le_six n ell
  intro edge hedge
  obtain ⟨offset, rfl, hoffset⟩ :=
    canonicalUsedAuxiliary_coordinate_shape hdegree hedge
  change auxiliaryEdgeAllowedB n
      (overlayOn (List.range (plaquetteEdgeCount n))
        physical actualAuxiliary) (rename (degree + offset)) =
    canonicalAuxiliaryEdgeAllowedB degree
      (overlayOn (List.range degree)
        (fun position => physical (rename position)) canonicalAuxiliary)
      (degree + offset)
  have hrename : rename (degree + offset) = base + offset := by
    dsimp [rename, degree, base]
    exact localIdentifierRename_length_add labels (linkBlockBase n i) offset
  have hcanonicalNotPhysical :
      degree + offset ∉ List.range degree := by
    intro hmem
    have hlt := List.mem_range.mp hmem
    omega
  have hactualNotPhysical :
      base + offset ∉ List.range (plaquetteEdgeCount n) := by
    intro hmem
    have hlt := List.mem_range.mp hmem
    have hge := linkBlockBase_ge_count n i
    dsimp [base] at hlt hge
    omega
  by_cases hoffsetZero : offset = 0
  · subst offset
    simp only [Nat.add_zero] at hrename hcanonicalNotPhysical hactualNotPhysical hedge ⊢
    have hvacuum : base ∈ vacuumBaseEdgeIds n := by
      dsimp [base]
      exact linkBlockBase_mem_vacuumBaseEdgeIds hindexed
    have hlabel : actualAuxiliary (rename degree) =
        canonicalAuxiliary degree := hagree degree hedge
    rw [hrename] at hlabel
    unfold auxiliaryEdgeAllowedB canonicalAuxiliaryEdgeAllowedB
    rw [hrename, if_pos hvacuum,
      if_pos rfl,
      overlayOn_apply_of_not_mem hactualNotPhysical,
      overlayOn_apply_of_not_mem hcanonicalNotPhysical,
      hlabel]
  · have hnotVacuum : base + offset ∉ vacuumBaseEdgeIds n := by
      dsimp [base]
      exact linkBlockBase_add_not_mem_vacuumBaseEdgeIds
        hoffsetZero hoffset
    have hnotDegree : degree + offset ≠ degree := by omega
    unfold auxiliaryEdgeAllowedB canonicalAuxiliaryEdgeAllowedB
    rw [hrename, if_neg hnotVacuum, if_neg hnotDegree]

/-- Pointwise equality of the actual and canonical local Boolean constraints
for related private-channel labellings. -/
theorem linkConditionalAuxiliaryAllowedB_rename
    {n i : Nat} {ell : Z4Link}
    (hindexed : (i, ell) ∈ enumerate (distinctBoxLinks n))
    (physical canonicalAuxiliary actualAuxiliary : EdgeLabelling)
    (hagree : LabelsAgreeOnRename
      (localIdentifierRename (incidentPlaqIds n ell) (linkBlockBase n i))
      (canonicalUsedAuxiliaryCoordinates (incidentPlaqIds n ell).length)
      canonicalAuxiliary actualAuxiliary) :
    linkConditionalAuxiliaryAllowedB n physical actualAuxiliary (i, ell) =
      canonicalLinkConditionalAllowedB (incidentPlaqIds n ell).length
        (fun edge => physical
          (localIdentifierRename (incidentPlaqIds n ell)
            (linkBlockBase n i) edge))
        canonicalAuxiliary := by
  let labels := incidentPlaqIds n ell
  let degree := labels.length
  let base := linkBlockBase n i
  let rename := localIdentifierRename labels base
  let canonicalVertices :=
    fuseLabels degree (degree + 1) (List.range degree)
  let canonicalLabel := overlayOn (List.range degree)
    (fun edge => physical (rename edge)) canonicalAuxiliary
  let actualLabel := overlayOn (List.range (plaquetteEdgeCount n))
    physical actualAuxiliary
  have hdegree : degree ≤ linkIncidenceBound := by
    dsimp [degree, labels]
    exact incidentPlaqIds_length_le_six n ell
  have hcover : VerticesCoveredBy
      (canonicalUsedCoordinates degree) canonicalVertices :=
    canonicalUsed_verticesCovered hdegree
  have hfullAgree : LabelsAgreeOnRename rename
      (canonicalUsedCoordinates degree) canonicalLabel actualLabel := by
    dsimp [rename, canonicalLabel, actualLabel, degree, labels, base]
    exact localOverlayLabelsAgreeOnRename physical
      canonicalAuxiliary actualAuxiliary hagree
  have hvertices :
      verticesAdmissibleB (linkResolutionVertices n i ell) actualLabel =
        verticesAdmissibleB canonicalVertices canonicalLabel := by
    have hmap := canonical_linkResolutionVertices_map n i ell
    dsimp only [labels, degree, base, rename, canonicalVertices] at hmap
    rw [← hmap]
    exact verticesAdmissibleB_rename rename
      (canonicalUsedCoordinates degree) canonicalVertices
      canonicalLabel actualLabel hcover hfullAgree
  have hauxiliary :
      (actualLinkAuxiliaryCoordinates n i ell).all
          (auxiliaryEdgeAllowedB n actualLabel) =
        (canonicalUsedAuxiliaryCoordinates degree).all
          (canonicalAuxiliaryEdgeAllowedB degree canonicalLabel) := by
    unfold actualLinkAuxiliaryCoordinates
    dsimp only [labels, degree, base, rename]
    rw [List.all_map]
    apply list_all_congr_on
    intro edge hedge
    dsimp [actualLabel, canonicalLabel, rename, degree, labels, base]
    exact auxiliaryEdgeAllowedB_rename hindexed physical
      canonicalAuxiliary actualAuxiliary hagree edge hedge
  unfold linkConditionalAuxiliaryAllowedB
    canonicalLinkConditionalAllowedB
  dsimp only [labels, degree, base, rename, canonicalVertices,
    canonicalLabel, actualLabel] at hvertices hauxiliary ⊢
  rw [hvertices, hauxiliary]

/-! ## 3. Equality of the actual and canonical natural counts -/

theorem linkAuxiliaryMultiplicity_eq_canonical
    {K n i : Nat} {ell : Z4Link}
    (hindexed : (i, ell) ∈ enumerate (distinctBoxLinks n))
    (physical : EdgeLabelling) :
    linkAuxiliaryMultiplicity K n physical (i, ell) ≈
      canonicalLinkAuxiliaryMultiplicity (linkAuxiliaryCutoff K)
        (incidentPlaqIds n ell).length
        (fun edge => physical
          (localIdentifierRename (incidentPlaqIds n ell)
            (linkBlockBase n i) edge)) := by
  let labels := incidentPlaqIds n ell
  let degree := labels.length
  let base := linkBlockBase n i
  let rename := localIdentifierRename labels base
  let edges := canonicalUsedAuxiliaryCoordinates degree
  unfold linkAuxiliaryMultiplicity canonicalLinkAuxiliaryMultiplicity
  change listQSum
      (fun auxiliary =>
        if linkConditionalAuxiliaryAllowedB n physical auxiliary (i, ell)
          then 1 else 0)
      (boundedEdgeLabellings (linkAuxiliaryCutoff K) (edges.map rename)) ≈
    listQSum
      (fun auxiliary =>
        if canonicalLinkConditionalAllowedB degree
            (fun edge => physical (rename edge)) auxiliary
          then 1 else 0)
      (boundedEdgeLabellings (linkAuxiliaryCutoff K) edges)
  apply listQSum_bounded_rename (linkAuxiliaryCutoff K) rename edges
  · apply injectiveOnList_of_map_nodup
    change (actualLinkAuxiliaryCoordinates n i ell).Nodup
    exact actualLinkAuxiliaryCoordinates_nodup n i ell
  · intro canonical actual hagree
    rw [linkConditionalAuxiliaryAllowedB_rename hindexed physical
      canonical actual hagree]
    exact Q'.eqv_refl _

private theorem ofNat_eqv_injective {left right : Nat}
    (h : Q'.ofNat left ≈ Q'.ofNat right) : left = right := by
  unfold Q'.eqv Q'.ofNat Q'.den at h
  simpa using (Int.ofNat.inj h)

/-- **Canonical fixed-external multiplicity theorem.**  For every actual
enumerated link, the natural cardinality appearing in the global spin-foam
formula is exactly the consecutive-coordinate fusion-chain cardinality. -/
theorem linkInvariantMultiplicityCount_eq_canonical
    {K n i : Nat} {ell : Z4Link}
    (hindexed : (i, ell) ∈ enumerate (distinctBoxLinks n))
    (physical : EdgeLabelling) :
    linkInvariantMultiplicityCount K n physical (i, ell) =
      canonicalLinkInvariantMultiplicityCount (linkAuxiliaryCutoff K)
        (incidentPlaqIds n ell).length
        (fun edge => physical
          (localIdentifierRename (incidentPlaqIds n ell)
            (linkBlockBase n i) edge)) := by
  apply ofNat_eqv_injective
  exact Q'.eqv_trans _
    (linkAuxiliaryMultiplicity K n physical (i, ell)) _
    (Q'.eqv_symm
      (linkAuxiliaryMultiplicity_eq_invariantCount K n physical (i, ell)))
    (Q'.eqv_trans _
      (canonicalLinkAuxiliaryMultiplicity (linkAuxiliaryCutoff K)
        (incidentPlaqIds n ell).length
        (fun edge => physical
          (localIdentifierRename (incidentPlaqIds n ell)
            (linkBlockBase n i) edge))) _
      (linkAuxiliaryMultiplicity_eq_canonical hindexed physical)
      (canonicalLinkAuxiliaryMultiplicity_eq_count
        (linkAuxiliaryCutoff K) (incidentPlaqIds n ell).length
        (fun edge => physical
          (localIdentifierRename (incidentPlaqIds n ell)
            (linkBlockBase n i) edge))))

end YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.localOverlayLabelsAgreeOnRename
#print axioms YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.auxiliaryEdgeAllowedB_rename
#print axioms YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.linkConditionalAuxiliaryAllowedB_rename
#print axioms YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.linkAuxiliaryMultiplicity_eq_canonical
#print axioms YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.linkInvariantMultiplicityCount_eq_canonical
