/-
# Partition of production auxiliary coordinates into link-local blocks

The counted spin-foam formula still enumerates one deduplicated global list
of auxiliary identifiers.  This module identifies that list, up to an exact
constructive permutation, with the flat concatenation of the private
auxiliary coordinates used by each enumerated physical link.

Every local block lies in its reserved half-open interval
`[plaquetteEdgeCount + 8*i, plaquetteEdgeCount + 8*(i+1))`.  Hence the blocks
are duplicate-free and pairwise disjoint.  This is the identifier-level
input needed to factor the conditional multiplicity over links without ever
separating the shared physical plaquette labelling.
-/

import YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity

namespace YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActualLinkUsedPacketBridge
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumFloor
open YMGap.Continuum.Z4FuseChainIdentifierTransport
open YMGap.Continuum.Z4GraphIdentifierCartesianTransport
open YMGap.Continuum.Z4LinkIdentifierFreshness

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact physical/auxiliary split inside one resolver -/

/-- Canonical coordinates read by auxiliary resolver edges, after the
physical prefix of length `degree` is removed. -/
def canonicalUsedAuxiliaryCoordinates (degree : Nat) : List Nat :=
  (canonicalUsedCoordinates degree).drop degree

theorem canonicalUsedCoordinates_eq_range_append_auxiliary
    {degree : Nat} (hdegree : degree ≤ linkIncidenceBound) :
    canonicalUsedCoordinates degree =
      List.range degree ++ canonicalUsedAuxiliaryCoordinates degree := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Actual private auxiliary identifiers used by one enumerated resolver. -/
def actualLinkAuxiliaryCoordinates (n i : Nat) (ell : Z4Link) : List Nat :=
  let labels := incidentPlaqIds n ell
  (canonicalUsedAuxiliaryCoordinates labels.length).map
    (localIdentifierRename labels (linkBlockBase n i))

/-- The reduced actual coordinate list is the incident physical plaquette
list followed by the resolver's private auxiliary coordinates. -/
theorem actualLinkUsedCoordinates_eq_incident_append_auxiliary
    (n i : Nat) (ell : Z4Link) :
    actualLinkUsedCoordinates n i ell =
      incidentPlaqIds n ell ++ actualLinkAuxiliaryCoordinates n i ell := by
  let labels := incidentPlaqIds n ell
  let degree := labels.length
  let base := linkBlockBase n i
  let rename := localIdentifierRename labels base
  have hdegree : degree ≤ linkIncidenceBound := by
    dsimp [degree, labels]
    exact incidentPlaqIds_length_le_six n ell
  unfold actualLinkUsedCoordinates actualLinkAuxiliaryCoordinates
  dsimp only [labels, degree, base, rename]
  rw [canonicalUsedCoordinates_eq_range_append_auxiliary hdegree,
    List.map_append, map_localIdentifierRename_range]

/-- Every canonical auxiliary coordinate is a bounded offset from the
reserved base. -/
theorem canonicalUsedAuxiliary_coordinate_shape
    {degree edge : Nat} (hdegree : degree ≤ linkIncidenceBound)
    (hedge : edge ∈ canonicalUsedAuxiliaryCoordinates degree) :
    ∃ j, edge = degree + j ∧ j < 8 := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [canonicalUsedAuxiliaryCoordinates,
      canonicalUsedCoordinates] at hedge
  · refine ⟨0, ?_, by omega⟩
    simpa [canonicalUsedAuxiliaryCoordinates,
      canonicalUsedCoordinates] using hedge
  · refine ⟨0, ?_, by omega⟩
    simpa [canonicalUsedAuxiliaryCoordinates,
      canonicalUsedCoordinates] using hedge
  · simp [canonicalUsedAuxiliaryCoordinates,
      canonicalUsedCoordinates] at hedge
  · simp [canonicalUsedAuxiliaryCoordinates,
      canonicalUsedCoordinates] at hedge
    rcases hedge with rfl
    exact ⟨1, by omega, by omega⟩
  · simp [canonicalUsedAuxiliaryCoordinates,
      canonicalUsedCoordinates] at hedge
    rcases hedge with rfl | rfl
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨2, by omega, by omega⟩
  · simp [canonicalUsedAuxiliaryCoordinates,
      canonicalUsedCoordinates] at hedge
    rcases hedge with rfl | rfl | rfl
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨2, by omega, by omega⟩
    · exact ⟨3, by omega, by omega⟩

/-- Actual auxiliary identifiers lie in the link's private reserved block. -/
theorem actualLinkAuxiliary_coordinate_shape
    {n i : Nat} {ell : Z4Link} {edge : Nat}
    (hedge : edge ∈ actualLinkAuxiliaryCoordinates n i ell) :
    ∃ j, edge = linkBlockBase n i + j ∧ j < 8 := by
  let labels := incidentPlaqIds n ell
  let degree := labels.length
  let base := linkBlockBase n i
  let rename := localIdentifierRename labels base
  change edge ∈
    (canonicalUsedAuxiliaryCoordinates degree).map rename at hedge
  obtain ⟨canonical, hcanonical, rfl⟩ := List.mem_map.mp hedge
  have hdegree : degree ≤ linkIncidenceBound := by
    dsimp [degree, labels]
    exact incidentPlaqIds_length_le_six n ell
  obtain ⟨j, rfl, hj⟩ :=
    canonicalUsedAuxiliary_coordinate_shape hdegree hcanonical
  refine ⟨j, ?_, hj⟩
  dsimp [rename, degree, labels, base]
  exact localIdentifierRename_length_add labels (linkBlockBase n i) j

theorem canonicalUsedAuxiliaryCoordinates_nodup
    {degree : Nat} (hdegree : degree ≤ linkIncidenceBound) :
    (canonicalUsedAuxiliaryCoordinates degree).Nodup := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem map_nodup_of_injective_on {A B : Type}
    (f : A → B) : ∀ xs : List A,
    xs.Nodup →
    (∀ x, x ∈ xs → ∀ y, y ∈ xs → f x = f y → x = y) →
    (xs.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hnodup, hinjective => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hmem
        have heq := hinjective x List.mem_cons_self y
          (List.mem_cons_of_mem x hy) hxy.symm
        subst y
        exact hparts.1 hy
      · exact map_nodup_of_injective_on f xs hparts.2
          (fun a ha b hb hab => hinjective a
            (List.mem_cons_of_mem x ha) b
            (List.mem_cons_of_mem x hb) hab)

theorem actualLinkAuxiliaryCoordinates_nodup
    (n i : Nat) (ell : Z4Link) :
    (actualLinkAuxiliaryCoordinates n i ell).Nodup := by
  let labels := incidentPlaqIds n ell
  let degree := labels.length
  let base := linkBlockBase n i
  let rename := localIdentifierRename labels base
  change ((canonicalUsedAuxiliaryCoordinates degree).map rename).Nodup
  have hdegree : degree ≤ linkIncidenceBound := by
    dsimp [degree, labels]
    exact incidentPlaqIds_length_le_six n ell
  apply map_nodup_of_injective_on rename
    (canonicalUsedAuxiliaryCoordinates degree)
    (canonicalUsedAuxiliaryCoordinates_nodup hdegree)
  intro x hx y hy hxy
  obtain ⟨jx, hxshape, hjx⟩ :=
    canonicalUsedAuxiliary_coordinate_shape hdegree hx
  obtain ⟨jy, hyshape, hjy⟩ :=
    canonicalUsedAuxiliary_coordinate_shape hdegree hy
  subst x
  subst y
  have hxrename : rename (degree + jx) = base + jx := by
    dsimp [rename, degree, labels, base]
    exact localIdentifierRename_length_add labels (linkBlockBase n i) jx
  have hyrename : rename (degree + jy) = base + jy := by
    dsimp [rename, degree, labels, base]
    exact localIdentifierRename_length_add labels (linkBlockBase n i) jy
  rw [hxrename, hyrename] at hxy
  omega

/-! ## 2. The flat list of private link blocks -/

def productionLinkAuxiliaryEdges (n : Nat) : List Nat :=
  (enumerate (distinctBoxLinks n)).flatMap fun indexed =>
    actualLinkAuxiliaryCoordinates n indexed.1 indexed.2

private theorem productionLinkAuxiliaryEdgesFrom_nodup (n : Nat) :
    ∀ (start : Nat) (links : List Z4Link),
    ((enumerateFrom start links).flatMap fun indexed =>
      actualLinkAuxiliaryCoordinates n indexed.1 indexed.2).Nodup
  | _, [] => List.nodup_nil
  | start, ell :: rest => by
      simp only [enumerateFrom, List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨actualLinkAuxiliaryCoordinates_nodup n start ell,
        productionLinkAuxiliaryEdgesFrom_nodup n (start + 1) rest, ?_⟩
      intro left hleft right hright heq
      obtain ⟨leftOffset, hleftEq, hleftLt⟩ :=
        actualLinkAuxiliary_coordinate_shape hleft
      obtain ⟨indexed, hindexed, hrightLocal⟩ :=
        List.mem_flatMap.mp hright
      obtain ⟨rightOffset, hrightEq, hrightLt⟩ :=
        actualLinkAuxiliary_coordinate_shape hrightLocal
      have hindexGe : start + 1 ≤ indexed.1 :=
        YMGap.Continuum.Z4LinkIdentifierFreshness.enumerateFrom_index_ge
          hindexed
      unfold linkBlockBase at hleftEq hrightEq
      omega

theorem productionLinkAuxiliaryEdges_nodup (n : Nat) :
    (productionLinkAuxiliaryEdges n).Nodup := by
  unfold productionLinkAuxiliaryEdges enumerate
  exact productionLinkAuxiliaryEdgesFrom_nodup n 0 (distinctBoxLinks n)

/-! ## 3. Equality with the deduplicated production auxiliary list -/

theorem actualLinkAuxiliaryCoordinate_mem_usedAuxiliaryEdges
    {n i : Nat} {ell : Z4Link}
    (hindexed : (i, ell) ∈ enumerate (distinctBoxLinks n))
    {edge : Nat}
    (hedge : edge ∈ actualLinkAuxiliaryCoordinates n i ell) :
    edge ∈ usedAuxiliaryEdges n := by
  have hlocalUsed : edge ∈ actualLinkUsedCoordinates n i ell := by
    rw [actualLinkUsedCoordinates_eq_incident_append_auxiliary]
    exact List.mem_append_right _ hedge
  have hglobal := actualLinkUsedCoordinates_mem_usedResolutionEdges
    hindexed edge hlocalUsed
  unfold usedResolutionEdges at hglobal
  rcases List.mem_append.mp hglobal with hphysical | hauxiliary
  · have hlt := List.mem_range.mp hphysical
    obtain ⟨j, hedgeEq, hj⟩ :=
      actualLinkAuxiliary_coordinate_shape hedge
    unfold linkBlockBase at hedgeEq
    omega
  · exact hauxiliary

theorem productionLinkAuxiliaryEdge_mem_usedAuxiliaryEdges
    {n edge : Nat} (hedge : edge ∈ productionLinkAuxiliaryEdges n) :
    edge ∈ usedAuxiliaryEdges n := by
  unfold productionLinkAuxiliaryEdges at hedge
  obtain ⟨indexed, hindexed, hlocal⟩ := List.mem_flatMap.mp hedge
  exact actualLinkAuxiliaryCoordinate_mem_usedAuxiliaryEdges
    hindexed hlocal

/-- Every edge read by one actual resolver occurs in its reduced coordinate
list. -/
theorem linkResolutionVertexEdge_mem_actualLinkUsedCoordinates
    {n i : Nat} {ell : Z4Link} {v : TrivalentVertex}
    (hv : v ∈ linkResolutionVertices n i ell)
    {edge : Nat} (hedge : edge ∈ vertexEdgeIds v) :
    edge ∈ actualLinkUsedCoordinates n i ell := by
  let labels := incidentPlaqIds n ell
  let degree := labels.length
  let base := linkBlockBase n i
  let rename := localIdentifierRename labels base
  let canonicalVertices :=
    fuseLabels degree (degree + 1) (List.range degree)
  have hvertices := canonical_linkResolutionVertices_map n i ell
  dsimp only at hvertices
  change canonicalVertices.map (mapTrivalentVertex rename) =
      linkResolutionVertices n i ell at hvertices
  rw [← hvertices] at hv
  obtain ⟨canonical, hcanonical, rfl⟩ := List.mem_map.mp hv
  have hdegree : degree ≤ linkIncidenceBound := by
    dsimp [degree, labels]
    exact incidentPlaqIds_length_le_six n ell
  have hcover := canonicalUsed_verticesCovered hdegree
  change edge ∈
    [rename canonical.1, rename canonical.2.1, rename canonical.2.2] at hedge
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hedge
  change edge ∈ (canonicalUsedCoordinates degree).map rename
  rcases hedge with rfl | rfl | rfl
  · exact List.mem_map.mpr
      ⟨canonical.1,
        hcover canonical hcanonical canonical.1 (Or.inl rfl), rfl⟩
  · exact List.mem_map.mpr
      ⟨canonical.2.1,
        hcover canonical hcanonical canonical.2.1
          (Or.inr (Or.inl rfl)), rfl⟩
  · exact List.mem_map.mpr
      ⟨canonical.2.2,
        hcover canonical hcanonical canonical.2.2
          (Or.inr (Or.inr rfl)), rfl⟩

theorem usedAuxiliaryEdge_mem_productionLinkAuxiliaryEdges
    {n edge : Nat} (hedge : edge ∈ usedAuxiliaryEdges n) :
    edge ∈ productionLinkAuxiliaryEdges n := by
  unfold usedAuxiliaryEdges at hedge
  have hfiltered := List.mem_filter.mp (List.mem_eraseDups.mp hedge)
  obtain ⟨v, hvglobal, hedgeVertex⟩ :=
    List.mem_flatMap.mp hfiltered.1
  unfold resolutionVertices at hvglobal
  obtain ⟨indexed, hindexed, hvlocal⟩ :=
    List.mem_flatMap.mp hvglobal
  have hlocalUsed :=
    linkResolutionVertexEdge_mem_actualLinkUsedCoordinates
      hvlocal hedgeVertex
  rw [actualLinkUsedCoordinates_eq_incident_append_auxiliary] at hlocalUsed
  rcases List.mem_append.mp hlocalUsed with hphysical | hauxiliary
  · have hlt := incidentPlaqId_lt_count hphysical
    have hge : plaquetteEdgeCount n ≤ edge := by
      simpa only [decide_eq_true_eq] using hfiltered.2
    omega
  · unfold productionLinkAuxiliaryEdges
    exact List.mem_flatMap.mpr ⟨indexed, hindexed, hauxiliary⟩

theorem productionLinkAuxiliaryEdges_mem_iff_used
    (n edge : Nat) :
    edge ∈ productionLinkAuxiliaryEdges n ↔
      edge ∈ usedAuxiliaryEdges n :=
  ⟨productionLinkAuxiliaryEdge_mem_usedAuxiliaryEdges,
    usedAuxiliaryEdge_mem_productionLinkAuxiliaryEdges⟩

theorem usedAuxiliaryEdges_nodup (n : Nat) :
    (usedAuxiliaryEdges n).Nodup := by
  have h := usedResolutionEdges_nodup n
  unfold usedResolutionEdges at h
  exact (List.nodup_append.mp h).2.1

private theorem nat_perm_of_nodup_mem_iff :
    ∀ (xs ys : List Nat), xs.Nodup → ys.Nodup →
      (∀ a, a ∈ xs ↔ a ∈ ys) → xs.Perm ys
  | [], [], _, _, _ => List.Perm.nil
  | [], y :: ys, _, _, hmem => by
      have hy : y ∈ ([] : List Nat) := (hmem y).mpr List.mem_cons_self
      cases hy
  | x :: xs, ys, hxs, hys, hmem => by
      have hparts := List.nodup_cons.mp hxs
      have hxys : x ∈ ys := (hmem x).mp List.mem_cons_self
      obtain ⟨as, bs, hsplit⟩ := List.append_of_mem hxys
      subst ys
      have hmiddle : (x :: (as ++ bs)).Perm (as ++ x :: bs) :=
        List.perm_middle.symm
      have hmiddleNodup : (x :: (as ++ bs)).Nodup :=
        hmiddle.symm.nodup hys
      have hrestParts := List.nodup_cons.mp hmiddleNodup
      have htailMem : ∀ a, a ∈ xs ↔ a ∈ as ++ bs := by
        intro a
        constructor
        · intro haxs
          have hax : a ≠ x := by
            intro hax
            subst a
            exact hparts.1 haxs
          have hay := (hmem a).mp (List.mem_cons_of_mem x haxs)
          rcases List.mem_append.mp hay with haas | htail
          · exact List.mem_append_left bs haas
          · have habs := (List.mem_cons.mp htail).resolve_left hax
            exact List.mem_append_right as habs
        · intro harest
          have hax : a ≠ x := by
            intro hax
            subst a
            exact hrestParts.1 harest
          have hay : a ∈ as ++ x :: bs := by
            rcases List.mem_append.mp harest with haas | habs
            · exact List.mem_append_left (x :: bs) haas
            · exact List.mem_append_right as
                (List.mem_cons_of_mem x habs)
          exact (List.mem_cons.mp ((hmem a).mpr hay)).resolve_left hax
      have htailPerm := nat_perm_of_nodup_mem_iff xs (as ++ bs)
        hparts.2 hrestParts.2 htailMem
      exact (List.Perm.cons x htailPerm).trans hmiddle

/-- The global production auxiliary list is exactly the concatenation of
private enumerated-link blocks, up to finite edge order. -/
theorem productionLinkAuxiliaryEdges_perm_usedAuxiliaryEdges (n : Nat) :
    (productionLinkAuxiliaryEdges n).Perm (usedAuxiliaryEdges n) := by
  apply nat_perm_of_nodup_mem_iff
  · exact productionLinkAuxiliaryEdges_nodup n
  · exact usedAuxiliaryEdges_nodup n
  · exact productionLinkAuxiliaryEdges_mem_iff_used n

/-! ## 4. The conditional sum in link-block order -/

def conditionalAuxiliaryMultiplicityByLinkBlocks (K n : Nat)
    (physical : EdgeLabelling) : Q' :=
  listQSum
    (conditionalAuxiliaryMultiplicityTerm n physical)
    (boundedEdgeLabellings (linkAuxiliaryCutoff K)
      (productionLinkAuxiliaryEdges n))

theorem conditionalAuxiliaryMultiplicity_eq_byLinkBlocks
    (K n : Nat) (physical : EdgeLabelling) :
    conditionalAuxiliaryMultiplicity K n physical ≈
      conditionalAuxiliaryMultiplicityByLinkBlocks K n physical := by
  unfold conditionalAuxiliaryMultiplicity
    conditionalAuxiliaryMultiplicityByLinkBlocks
  exact Q'.eqv_symm
    (listQSum_bounded_perm (linkAuxiliaryCutoff K)
      (conditionalAuxiliaryMultiplicityTerm n physical)
      (productionLinkAuxiliaryEdges_perm_usedAuxiliaryEdges n))

/-! ## 5. The global constraint is the conjunction of local constraints -/

theorem list_all_append {A : Type} (allowed : A → Bool) :
    ∀ xs ys : List A,
    (xs ++ ys).all allowed = (xs.all allowed && ys.all allowed)
  | [], ys => by simp
  | x :: xs, ys => by
      simp only [List.cons_append, List.all_cons]
      rw [list_all_append allowed xs ys]
      cases allowed x <;> cases xs.all allowed <;>
        cases ys.all allowed <;> rfl

theorem list_all_flatMap {A B : Type}
    (block : A → List B) (allowed : B → Bool) :
    ∀ xs : List A,
    (xs.flatMap block).all allowed =
      xs.all (fun x => (block x).all allowed)
  | [] => rfl
  | x :: xs => by
      simp only [List.flatMap_cons, List.all_cons]
      rw [list_all_append, list_all_flatMap block allowed xs]

theorem list_all_and {A : Type} (left right : A → Bool) :
    ∀ xs : List A,
    (xs.all left && xs.all right) =
      xs.all (fun x => left x && right x)
  | [] => rfl
  | x :: xs => by
      simp only [List.all_cons]
      rw [← list_all_and left right xs]
      cases left x <;> cases right x <;>
        cases xs.all left <;> cases xs.all right <;> rfl

theorem list_all_perm {A : Type} (allowed : A → Bool)
    {xs ys : List A} (hperm : xs.Perm ys) :
    xs.all allowed = ys.all allowed := by
  induction hperm with
  | nil => rfl
  | cons x h ih =>
      simp only [List.all_cons]
      rw [ih]
  | swap x y rest =>
      simp only [List.all_cons]
      cases allowed x <;> cases allowed y <;>
        cases rest.all allowed <;> rfl
  | trans hxy hyz ihxy ihyz => rw [ihxy, ihyz]

/-- Local fusion and terminator-vacuum constraint for one enumerated link,
evaluated in the common physical/auxiliary overlay labelling. -/
def linkConditionalAuxiliaryAllowedB (n : Nat)
    (physical auxiliary : EdgeLabelling)
    (indexed : Nat × Z4Link) : Bool :=
  let label := overlayOn (List.range (plaquetteEdgeCount n))
    physical auxiliary
  verticesAdmissibleB
      (linkResolutionVertices n indexed.1 indexed.2) label &&
    (actualLinkAuxiliaryCoordinates n indexed.1 indexed.2).all
      (auxiliaryEdgeAllowedB n label)

/-- The full conditional Boolean constraint is exactly the conjunction of
the local constraints over the enumerated physical links.  Every conjunct
is evaluated at the same fixed physical plaquette labelling. -/
theorem conditionalAuxiliaryAllowedB_eq_link_all
    (n : Nat) (physical auxiliary : EdgeLabelling) :
    conditionalAuxiliaryAllowedB n physical auxiliary =
      (enumerate (distinctBoxLinks n)).all
        (linkConditionalAuxiliaryAllowedB n physical auxiliary) := by
  let label := overlayOn (List.range (plaquetteEdgeCount n))
    physical auxiliary
  unfold conditionalAuxiliaryAllowedB auxiliaryPacketAllowedB
  dsimp only [label]
  rw [resolutionVertices_admissible_factor]
  have hauxPerm :
      (usedAuxiliaryEdges n).all (auxiliaryEdgeAllowedB n label) =
        (productionLinkAuxiliaryEdges n).all
          (auxiliaryEdgeAllowedB n label) :=
    (list_all_perm (auxiliaryEdgeAllowedB n label)
      (productionLinkAuxiliaryEdges_perm_usedAuxiliaryEdges n)).symm
  rw [hauxPerm]
  unfold productionLinkAuxiliaryEdges
  rw [list_all_flatMap, list_all_and]
  rfl

/-! ## 6. Each local constraint depends only on its private block -/

theorem verticesAdmissibleB_congr_on
    (left right : EdgeLabelling) :
    ∀ vertices : List TrivalentVertex,
      (∀ v, v ∈ vertices → ∀ edge,
        VertexContains edge v → left edge = right edge) →
      verticesAdmissibleB vertices left =
        verticesAdmissibleB vertices right
  | [], _ => rfl
  | v :: rest, hagree => by
      have hfirst := hagree v List.mem_cons_self v.1 (Or.inl rfl)
      have hsecond := hagree v List.mem_cons_self v.2.1
        (Or.inr (Or.inl rfl))
      have hthird := hagree v List.mem_cons_self v.2.2
        (Or.inr (Or.inr rfl))
      have hrest := verticesAdmissibleB_congr_on left right rest
        (fun w hw edge hedge =>
          hagree w (List.mem_cons_of_mem v hw) edge hedge)
      simp only [verticesAdmissibleB]
      rw [hfirst, hsecond, hthird]
      cases fusionOK (right v.1) (right v.2.1) (right v.2.2) <;>
        simp [hrest]

theorem list_all_congr_on {A : Type} (left right : A → Bool) :
    ∀ xs : List A,
      (∀ x, x ∈ xs → left x = right x) →
      xs.all left = xs.all right
  | [], _ => rfl
  | x :: xs, hagree => by
      simp only [List.all_cons]
      rw [hagree x List.mem_cons_self,
        list_all_congr_on left right xs
          (fun y hy => hagree y (List.mem_cons_of_mem x hy))]

private theorem vertexContains_mem_vertexEdgeIds
    {edge : Nat} {v : TrivalentVertex}
    (hedge : VertexContains edge v) : edge ∈ vertexEdgeIds v := by
  unfold VertexContains at hedge
  rcases hedge with rfl | rfl | rfl <;> simp [vertexEdgeIds]

private theorem actualAuxiliary_not_physical
    {n i : Nat} {ell : Z4Link} {edge : Nat}
    (hedge : edge ∈ actualLinkAuxiliaryCoordinates n i ell) :
    edge ∉ List.range (plaquetteEdgeCount n) := by
  intro hphysical
  have hlt := List.mem_range.mp hphysical
  obtain ⟨j, hedgeEq, hj⟩ :=
    actualLinkAuxiliary_coordinate_shape hedge
  unfold linkBlockBase at hedgeEq
  omega

/-- Changing auxiliary labels outside one link's private block cannot change
that link's local conditional constraint. -/
theorem linkConditionalAuxiliaryAllowedB_congr_on
    (n : Nat) (physical left right : EdgeLabelling)
    (indexed : Nat × Z4Link)
    (hagree : ∀ edge,
      edge ∈ actualLinkAuxiliaryCoordinates n indexed.1 indexed.2 →
        left edge = right edge) :
    linkConditionalAuxiliaryAllowedB n physical left indexed =
      linkConditionalAuxiliaryAllowedB n physical right indexed := by
  let physicalEdges := List.range (plaquetteEdgeCount n)
  let leftLabel := overlayOn physicalEdges physical left
  let rightLabel := overlayOn physicalEdges physical right
  have hlabelAux : ∀ edge,
      edge ∈ actualLinkAuxiliaryCoordinates n indexed.1 indexed.2 →
        leftLabel edge = rightLabel edge := by
    intro edge hedge
    have hnot := actualAuxiliary_not_physical hedge
    dsimp [leftLabel, rightLabel, physicalEdges]
    rw [overlayOn_apply_of_not_mem hnot,
      overlayOn_apply_of_not_mem hnot]
    exact hagree edge hedge
  have hvertices :
      verticesAdmissibleB
          (linkResolutionVertices n indexed.1 indexed.2) leftLabel =
        verticesAdmissibleB
          (linkResolutionVertices n indexed.1 indexed.2) rightLabel := by
    apply verticesAdmissibleB_congr_on
    intro v hv edge hedge
    have hcoordinate :=
      linkResolutionVertexEdge_mem_actualLinkUsedCoordinates hv
        (vertexContains_mem_vertexEdgeIds hedge)
    rw [actualLinkUsedCoordinates_eq_incident_append_auxiliary]
      at hcoordinate
    rcases List.mem_append.mp hcoordinate with hphysical | hauxiliary
    · have hlt := incidentPlaqId_lt_count hphysical
      have hmem : edge ∈ physicalEdges := by
        dsimp [physicalEdges]
        exact List.mem_range.mpr hlt
      dsimp [leftLabel, rightLabel]
      rw [overlayOn_apply_of_mem hmem,
        overlayOn_apply_of_mem hmem]
    · exact hlabelAux edge hauxiliary
  have hallowed :
      (actualLinkAuxiliaryCoordinates n indexed.1 indexed.2).all
          (auxiliaryEdgeAllowedB n leftLabel) =
        (actualLinkAuxiliaryCoordinates n indexed.1 indexed.2).all
          (auxiliaryEdgeAllowedB n rightLabel) := by
    apply list_all_congr_on
    intro edge hedge
    unfold auxiliaryEdgeAllowedB
    by_cases hvacuum : edge ∈ vacuumBaseEdgeIds n
    · rw [if_pos hvacuum, if_pos hvacuum,
        hlabelAux edge hedge]
    · rw [if_neg hvacuum, if_neg hvacuum]
  unfold linkConditionalAuxiliaryAllowedB
  dsimp only [leftLabel, rightLabel, physicalEdges] at hvertices hallowed ⊢
  rw [hvertices, hallowed]

theorem actualLinkAuxiliaryCoordinates_disjoint_of_index_lt
    {n i j : Nat} {leftLink rightLink : Z4Link} (hij : i < j) :
    ∀ edge,
      edge ∈ actualLinkAuxiliaryCoordinates n i leftLink →
      edge ∉ actualLinkAuxiliaryCoordinates n j rightLink := by
  intro edge hleft hright
  obtain ⟨leftOffset, hleftEq, hleftLt⟩ :=
    actualLinkAuxiliary_coordinate_shape hleft
  obtain ⟨rightOffset, hrightEq, hrightLt⟩ :=
    actualLinkAuxiliary_coordinate_shape hright
  unfold linkBlockBase at hleftEq hrightEq
  omega

end YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition.canonicalUsedCoordinates_eq_range_append_auxiliary
#print axioms YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition.actualLinkUsedCoordinates_eq_incident_append_auxiliary
#print axioms YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition.actualLinkAuxiliary_coordinate_shape
#print axioms YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition.actualLinkAuxiliaryCoordinates_nodup
#print axioms YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition.productionLinkAuxiliaryEdges_nodup
#print axioms YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition.actualLinkAuxiliaryCoordinate_mem_usedAuxiliaryEdges
#print axioms YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition.linkResolutionVertexEdge_mem_actualLinkUsedCoordinates
#print axioms YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition.usedAuxiliaryEdge_mem_productionLinkAuxiliaryEdges
#print axioms YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition.productionLinkAuxiliaryEdges_perm_usedAuxiliaryEdges
#print axioms YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition.conditionalAuxiliaryMultiplicity_eq_byLinkBlocks
#print axioms YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition.conditionalAuxiliaryAllowedB_eq_link_all
#print axioms YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition.linkConditionalAuxiliaryAllowedB_congr_on
#print axioms YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition.actualLinkAuxiliaryCoordinates_disjoint_of_index_lt
