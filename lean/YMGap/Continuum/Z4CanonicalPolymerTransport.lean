/-
# Canonical transport of cutoff-one polymers between finite Z4 boxes

A numerical plaquette identifier depends on the ambient box.  This module
gives a deterministic re-encoding of a geometric plaquette support in any
larger box, proves that the re-encoding has exactly the same geometric
support, and transports complete family activities and finite partition sums.

The result is an exact algebraic specification: the full smaller-box ensemble
has a weight-preserving copy written in the coordinates of every larger box.
Identifying that copy with the corresponding internal subensemble of the full
larger-box measure, and bounding the remaining boundary-connected clusters,
are separate subsequent steps.
-/

import YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure

namespace YMGap.Continuum.Z4CanonicalPolymerTransport

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphComponentUniqueness
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4PhysicalSurfaceComponentUniqueness
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeEnumerationParity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Deterministic geometric support IDs -/

/-- Re-encode a geometric plaquette list using the numerical identifiers of
box `n`, in the canonical physical-face order. -/
def geometricSupportIds (n : Nat) (support : List Z4Plaq) : List Nat :=
  (physicalFaceEdges n).filter
    (fun id => decide (boxPlaquetteAt n id ∈ support))

theorem mem_geometricSupportIds_iff
    (n : Nat) (support : List Z4Plaq) (id : Nat) :
    id ∈ geometricSupportIds n support ↔
      id ∈ physicalFaceEdges n ∧ boxPlaquetteAt n id ∈ support := by
  unfold geometricSupportIds
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]

theorem geometricSupportIds_mem_cutoffOneFaceSupports
    (n : Nat) (support : List Z4Plaq) :
    geometricSupportIds n support ∈ cutoffOneFaceSupports n := by
  unfold geometricSupportIds cutoffOneFaceSupports
  exact filter_mem_sublists _ _

theorem boxPlaquetteAt_mem_boxPlaquettes_of_physical
    {n id : Nat} (hid : id ∈ physicalFaceEdges n) :
    boxPlaquetteAt n id ∈ boxPlaquettes n := by
  have hindexed := boxPlaquetteAt_mem_enumerate (physicalFaceId_lt hid)
  have hmap : boxPlaquetteAt n id ∈
      (enumerate (boxPlaquettes n)).map Prod.snd :=
    List.mem_map.mpr
      ⟨(id, boxPlaquetteAt n id), hindexed, rfl⟩
  rw [enumerate_map_snd] at hmap
  exact hmap

/-- If every plaquette of `support` lies in box `n`, decoding its canonical
identifier list recovers exactly that geometric support. -/
theorem geometricSupportIds_sameSupport
    {n : Nat} {support : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes n) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer n (geometricSupportIds n support)) support := by
  constructor
  · intro plaquette hp
    obtain ⟨id, hid, hidEq⟩ := List.mem_map.mp hp
    have hparts := (mem_geometricSupportIds_iff n support id).mp hid
    simpa only [← hidEq] using hparts.2
  · intro plaquette hp
    have hpBox := hbox plaquette hp
    obtain ⟨id, hindexed⟩ := exists_mem_enumerate hpBox
    have hidPhysical : id ∈ physicalFaceEdges n := by
      unfold physicalFaceEdges plaquetteEdgeCount
      exact List.mem_range.mpr (enumerate_index_lt hindexed)
    have hidEq : boxPlaquetteAt n id = plaquette :=
      boxPlaquetteAt_eq_of_enumerate hindexed
    unfold geometricPolymer
    apply List.mem_map.mpr
    refine ⟨id, (mem_geometricSupportIds_iff n support id).mpr ?_, hidEq⟩
    exact ⟨hidPhysical, by simpa only [hidEq] using hp⟩

theorem geometricPolymer_subset_box
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    ∀ plaquette, plaquette ∈ geometricPolymer n support →
      plaquette ∈ boxPlaquettes n := by
  intro plaquette hp
  obtain ⟨id, hid, hidEq⟩ := List.mem_map.mp hp
  have hidPhysical := mem_of_mem_sublists
    (physicalFaceEdges n) support hsupport id hid
  rw [← hidEq]
  exact boxPlaquetteAt_mem_boxPlaquettes_of_physical hidPhysical

/-! ## 2. Transport of one polymer -/

def transportPolymer (n m : Nat) (support : List Nat) : List Nat :=
  geometricSupportIds m (geometricPolymer n support)

theorem transportPolymer_mem_cutoffOneFaceSupports
    (n m : Nat) (support : List Nat) :
    transportPolymer n m support ∈ cutoffOneFaceSupports m :=
  geometricSupportIds_mem_cutoffOneFaceSupports m
    (geometricPolymer n support)

theorem transportPolymer_sameSupport
    {n m : Nat} (hnm : n ≤ m) {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer n support)
      (geometricPolymer m (transportPolymer n m support)) := by
  apply sameSupport_symm
  apply geometricSupportIds_sameSupport
  intro plaquette hp
  exact boxPlaquettes_mono hnm
    (geometricPolymer_subset_box hsupport plaquette hp)

theorem transportPolymer_length_eq
    {n m : Nat} (hnm : n ≤ m) {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    (transportPolymer n m support).length = support.length := by
  have hright := transportPolymer_mem_cutoffOneFaceSupports n m support
  exact (numericalSupport_length_eq_of_geometric_sameSupport
    hsupport hright (transportPolymer_sameSupport hnm hsupport)).symm

/-- A transported polymer has exactly the same complete canonical activity in
the larger box. -/
theorem canonicalSurfaceActivity_transport
    (w : Q') {n m : Nat} (hnm : n ≤ m) {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    (canonicalSurfaceActivity w n support).eqv
      (canonicalSurfaceActivity w m (transportPolymer n m support)) :=
  canonicalSurfaceActivity_cross_volume w hsupport
    (transportPolymer_mem_cutoffOneFaceSupports n m support)
    (transportPolymer_sameSupport hnm hsupport)

/-! ## 3. Transport preserves connected canonical polymers -/

/-- Geometric shared-link adjacency implies the numerical adjacency test for
any two physical identifiers of the same finite box. -/
theorem faceLinkAdjacentB_true_of_actualAdjacent
    {n left right : Nat}
    (hleft : left ∈ physicalFaceEdges n)
    (hright : right ∈ physicalFaceEdges n)
    (hadj : z4Chain.toLattice.Adjacent
      (boxPlaquetteAt n left) (boxPlaquetteAt n right)) :
    faceLinkAdjacentB n left right = true := by
  let link : Z4Link := hadj.link
  have hleftEdge : link ∈ edgesOf (boxPlaquetteAt n left) := by
    have hon := hadj.on_p
    change z4Boundary (boxPlaquetteAt n left) link = true at hon
    simpa only [z4Boundary, decide_eq_true_eq] using hon
  have hrightEdge : link ∈ edgesOf (boxPlaquetteAt n right) := by
    have hon := hadj.on_q
    change z4Boundary (boxPlaquetteAt n right) link = true at hon
    simpa only [z4Boundary, decide_eq_true_eq] using hon
  have hleftEnum := boxPlaquetteAt_mem_enumerate (physicalFaceId_lt hleft)
  have hrightEnum := boxPlaquetteAt_mem_enumerate (physicalFaceId_lt hright)
  have hlinkBox : link ∈ distinctBoxLinks n := by
    unfold distinctBoxLinks
    apply List.mem_eraseDups.mpr
    exact boundary_mem_boxLinks
      (boxPlaquetteAt_mem_boxPlaquettes_of_physical hleft) hleftEdge
  apply faceLinkAdjacentB_true_of_link hlinkBox
  · exact mem_incidentPlaqIds.mpr
      ⟨boxPlaquetteAt n left, hleftEnum, hleftEdge⟩
  · exact mem_incidentPlaqIds.mpr
      ⟨boxPlaquetteAt n right, hrightEnum, hrightEdge⟩

/-- Decode a geometric chain into the canonical numerical IDs of the same
support.  This is Type-valued and therefore supplies actual connectivity data,
not propositional reachability. -/
def geometricChainToNumerical
    {n : Nat} {support : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes n) :
    {p q : Z4Plaq} →
    (chain : PolymerModel.ChainIn z4Chain.toLattice support p q) →
    {left right : Nat} →
    (hleft : left ∈ geometricSupportIds n support) →
    (hleftEq : boxPlaquetteAt n left = p) →
    (hright : right ∈ geometricSupportIds n support) →
    (hrightEq : boxPlaquetteAt n right = q) →
    FiniteBoolGraphComponents.ChainIn
      (faceLinkAdjacentB n) (geometricSupportIds n support) left right
  | _, _, PolymerModel.ChainIn.refl point,
      left, right, hleft, hleftEq, hright, hrightEq => by
      have hleftPhysical :=
        (mem_geometricSupportIds_iff n support left).mp hleft |>.1
      have hrightPhysical :=
        (mem_geometricSupportIds_iff n support right).mp hright |>.1
      have hidEq : left = right :=
        boxPlaquetteAt_injective_on_physical hleftPhysical hrightPhysical
          (hleftEq.trans hrightEq.symm)
      subst right
      exact FiniteBoolGraphComponents.ChainIn.refl left
  | _, _, PolymerModel.ChainIn.step (r := next) hadj hnext rest,
      left, right, hleft, hleftEq, hright, hrightEq => by
      have hsame := geometricSupportIds_sameSupport hbox
      have hnextGeom : next ∈
          geometricPolymer n (geometricSupportIds n support) :=
        hsame.2 next hnext
      obtain ⟨nextId, hnextId, hnextEq⟩ :=
        decodeMapMember (boxPlaquetteAt n)
          (geometricSupportIds n support) next hnextGeom
      have hleftPhysical :=
        (mem_geometricSupportIds_iff n support left).mp hleft |>.1
      have hnextPhysical :=
        (mem_geometricSupportIds_iff n support nextId).mp hnextId |>.1
      have hadjNumerical : faceLinkAdjacentB n left nextId = true := by
        apply faceLinkAdjacentB_true_of_actualAdjacent
          hleftPhysical hnextPhysical
        rw [hleftEq, hnextEq]
        exact hadj
      exact FiniteBoolGraphComponents.ChainIn.step
        hadjNumerical hnextId
        (geometricChainToNumerical hbox rest
          hnextId hnextEq hright hrightEq)

def geometricSupportIds_connected
    {n : Nat} {support : List Z4Plaq}
    (hbox : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boxPlaquettes n)
    (hconnected : PolymerModel.connectedIn
      (L := z4Chain.toLattice) support) :
    FiniteBoolGraphComponents.InternallyConnected
      (faceLinkAdjacentB n) (geometricSupportIds n support) := by
  intro left right hleft hright
  have hsame := geometricSupportIds_sameSupport hbox
  have hleftGeom : boxPlaquetteAt n left ∈
      geometricPolymer n (geometricSupportIds n support) :=
    List.mem_map.mpr ⟨left, hleft, rfl⟩
  have hrightGeom : boxPlaquetteAt n right ∈
      geometricPolymer n (geometricSupportIds n support) :=
    List.mem_map.mpr ⟨right, hright, rfl⟩
  exact geometricChainToNumerical hbox
    (hconnected (boxPlaquetteAt n left) (boxPlaquetteAt n right)
      (hsame.1 _ hleftGeom) (hsame.1 _ hrightGeom))
    hleft rfl hright rfl

/-- Every nonempty internally connected cutoff-one face support is one of the
canonical polymers; the canonical component resolver introduces no hidden
extra restriction. -/
theorem connectedFaceSupport_mem_canonicalSurfacePolymers
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hnonempty : Σ' face : Nat, face ∈ support)
    (hconnected : FiniteBoolGraphComponents.InternallyConnected
      (faceLinkAdjacentB n) support) :
    support ∈ canonicalSurfacePolymers n := by
  have hcover : FiniteBoolGraphComponents.Covers support [support] := by
    intro face
    simp
  have hallConnected : FiniteBoolGraphComponents.AllConnected
      (faceLinkAdjacentB n) [support] := by
    intro component hcomponent
    have heq : component = support := List.mem_singleton.mp hcomponent
    subst component
    exact hconnected
  have hallNonempty : FiniteBoolGraphComponents.AllNonempty [support] := by
    intro component hcomponent
    have heq : component = support := List.mem_singleton.mp hcomponent
    subst component
    exact hnonempty
  have hseparated : FiniteBoolGraphComponents.DistinctSeparated
      (faceLinkAdjacentB n) [support] := by
    intro left hleft right hright hne
    have hleftEq : left = support := List.mem_singleton.mp hleft
    have hrightEq : right = support := List.mem_singleton.mp hright
    subst left
    subst right
    exact absurd rfl hne
  have hcomponents := surfaceComponents_unique_up_to_support n
    (componentLabel support) (by
      rw [excitedPlaquetteIds_componentLabel_eq_support hsupport]
      exact hcover)
    hallConnected hallNonempty hseparated
  obtain ⟨raw, hraw, hsame⟩ :=
    hcomponents.2 support List.mem_cons_self
  have hrawSubset : ∀ {face}, face ∈ raw →
      face ∈ physicalFaceEdges n :=
    surfaceComponent_subset_physicalFaceEdges hraw
  have hcanonical : canonicalFaceSupport n raw = support := by
    apply sublists_eq_of_mem_iff (physicalFaceEdges n)
      (canonicalFaceSupport n raw) support
      (physicalFaceEdges_nodup n)
      (canonicalFaceSupport_mem_cutoffOneFaceSupports n raw)
      hsupport
    intro face
    rw [mem_canonicalFaceSupport_iff hrawSubset face]
    exact (hsame face).symm
  apply mem_canonicalSurfacePolymers_iff.mpr
  refine ⟨canonicalSurfaceFamily n support, ?_, ?_⟩
  · unfold canonicalConnectedSurfaceGas
    exact List.mem_map.mpr ⟨support, hsupport, rfl⟩
  · unfold canonicalSurfaceFamily
    exact List.mem_map.mpr ⟨raw, hraw, hcanonical⟩

def transportPolymer_connected
    {n m : Nat} (hnm : n ≤ m) {support : List Nat}
    (hpolymer : support ∈ canonicalSurfacePolymers n) :
    FiniteBoolGraphComponents.InternallyConnected
      (faceLinkAdjacentB m) (transportPolymer n m support) := by
  unfold transportPolymer
  apply geometricSupportIds_connected
  · intro plaquette hp
    exact boxPlaquettes_mono hnm
      (geometricPolymer_subset_box
        (canonicalSurfacePolymer_mem_faceSupports hpolymer) plaquette hp)
  · exact numericalConnectedToGeometric
      ((canonicalSurfacePolymers_allConnected n) support hpolymer)

def transportPolymer_nonempty
    {n m : Nat} (hnm : n ≤ m) {support : List Nat}
    (hpolymer : support ∈ canonicalSurfacePolymers n) :
    Σ' face : Nat, face ∈ transportPolymer n m support := by
  obtain ⟨sourceId, hsourceId⟩ :=
    canonicalSurfacePolymers_allNonempty n support hpolymer
  have hsourceGeom : boxPlaquetteAt n sourceId ∈
      geometricPolymer n support :=
    List.mem_map.mpr ⟨sourceId, hsourceId, rfl⟩
  have htargetGeom :=
    (transportPolymer_sameSupport hnm
      (canonicalSurfacePolymer_mem_faceSupports hpolymer)).1
      (boxPlaquetteAt n sourceId) hsourceGeom
  obtain ⟨targetId, htargetId, _⟩ :=
    decodeMapMember (boxPlaquetteAt m)
      (transportPolymer n m support) (boxPlaquetteAt n sourceId)
      htargetGeom
  exact ⟨targetId, htargetId⟩

/-- Canonical connected polymers remain canonical connected polymers after
transport to a larger box. -/
theorem transportPolymer_mem_canonicalSurfacePolymers
    {n m : Nat} (hnm : n ≤ m) {support : List Nat}
    (hpolymer : support ∈ canonicalSurfacePolymers n) :
    transportPolymer n m support ∈ canonicalSurfacePolymers m :=
  connectedFaceSupport_mem_canonicalSurfacePolymers
    (transportPolymer_mem_cutoffOneFaceSupports n m support)
    (transportPolymer_nonempty hnm hpolymer)
    (transportPolymer_connected hnm hpolymer)

/-- Every face of a transported support has a constructive source identifier
in the smaller box that denotes exactly the same geometric plaquette. -/
def transportPolymerMemberSource
    {n m : Nat} (hnm : n ≤ m) {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    {targetFace : Nat}
    (htarget : targetFace ∈ transportPolymer n m support) :
    Σ' sourceFace : Nat,
      (sourceFace ∈ support) ×'
        (boxPlaquetteAt n sourceFace = boxPlaquetteAt m targetFace) := by
  have htargetGeom : boxPlaquetteAt m targetFace ∈
      geometricPolymer m (transportPolymer n m support) :=
    List.mem_map.mpr ⟨targetFace, htarget, rfl⟩
  have hsourceGeom :=
    (transportPolymer_sameSupport hnm hsupport).2
      (boxPlaquetteAt m targetFace) htargetGeom
  exact decodeMapMember (boxPlaquetteAt n) support
    (boxPlaquetteAt m targetFace) hsourceGeom

/-- Every source face has a constructive target identifier denoting the same
geometric plaquette. -/
def transportPolymerMemberTarget
    {n m : Nat} (hnm : n ≤ m) {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    {sourceFace : Nat}
    (hsource : sourceFace ∈ support) :
    Σ' targetFace : Nat,
      (targetFace ∈ transportPolymer n m support) ×'
        (boxPlaquetteAt n sourceFace = boxPlaquetteAt m targetFace) := by
  have hsourceGeom : boxPlaquetteAt n sourceFace ∈
      geometricPolymer n support :=
    List.mem_map.mpr ⟨sourceFace, hsource, rfl⟩
  have htargetGeom :=
    (transportPolymer_sameSupport hnm hsupport).1
      (boxPlaquetteAt n sourceFace) hsourceGeom
  obtain ⟨targetFace, htargetFace, htargetEq⟩ :=
    decodeMapMember (boxPlaquetteAt m)
      (transportPolymer n m support)
      (boxPlaquetteAt n sourceFace) htargetGeom
  exact ⟨targetFace, htargetFace, htargetEq.symm⟩

/-- Disjoint geometric supports remain disjoint after re-encoding in a larger
box. -/
theorem supportsDisjoint_transport
    {n m : Nat} (hnm : n ≤ m) {left right : List Nat}
    (hleftSupport : left ∈ cutoffOneFaceSupports n)
    (hrightSupport : right ∈ cutoffOneFaceSupports n)
    (hdisjoint : FiniteBoolGraphComponents.SupportsDisjoint left right) :
    FiniteBoolGraphComponents.SupportsDisjoint
      (transportPolymer n m left) (transportPolymer n m right) := by
  intro targetFace htargetLeft htargetRight
  obtain ⟨sourceLeft, hsourceLeft, hleftEq⟩ :=
    transportPolymerMemberSource hnm hleftSupport htargetLeft
  obtain ⟨sourceRight, hsourceRight, hrightEq⟩ :=
    transportPolymerMemberSource hnm hrightSupport htargetRight
  have hleftPhysical : sourceLeft ∈ physicalFaceEdges n :=
    mem_of_mem_sublists (physicalFaceEdges n) left hleftSupport
      sourceLeft hsourceLeft
  have hrightPhysical : sourceRight ∈ physicalFaceEdges n :=
    mem_of_mem_sublists (physicalFaceEdges n) right hrightSupport
      sourceRight hsourceRight
  have hsourceEq : sourceLeft = sourceRight :=
    boxPlaquetteAt_injective_on_physical hleftPhysical hrightPhysical
      (hleftEq.trans hrightEq.symm)
  subst sourceRight
  exact hdisjoint sourceLeft hsourceLeft hsourceRight

/-- Link separation is geometric and is therefore invariant under transport
to a larger box. -/
theorem supportsSeparated_transport
    {n m : Nat} (hnm : n ≤ m) {left right : List Nat}
    (hleftSupport : left ∈ cutoffOneFaceSupports n)
    (hrightSupport : right ∈ cutoffOneFaceSupports n)
    (hseparated : FiniteBoolGraphComponents.SupportsSeparated
      (faceLinkAdjacentB n) left right) :
    FiniteBoolGraphComponents.SupportsSeparated
      (faceLinkAdjacentB m)
      (transportPolymer n m left) (transportPolymer n m right) := by
  intro targetLeft htargetLeft targetRight htargetRight
  cases hadjTarget : faceLinkAdjacentB m targetLeft targetRight with
  | false => rfl
  | true =>
      obtain ⟨sourceLeft, hsourceLeft, hleftEq⟩ :=
        transportPolymerMemberSource hnm hleftSupport htargetLeft
      obtain ⟨sourceRight, hsourceRight, hrightEq⟩ :=
        transportPolymerMemberSource hnm hrightSupport htargetRight
      have hleftPhysical : sourceLeft ∈ physicalFaceEdges n :=
        mem_of_mem_sublists (physicalFaceEdges n) left hleftSupport
          sourceLeft hsourceLeft
      have hrightPhysical : sourceRight ∈ physicalFaceEdges n :=
        mem_of_mem_sublists (physicalFaceEdges n) right hrightSupport
          sourceRight hsourceRight
      have hadjSourceActual : z4Chain.toLattice.Adjacent
          (boxPlaquetteAt n sourceLeft) (boxPlaquetteAt n sourceRight) := by
        simpa only [hleftEq, hrightEq] using
          (actualAdjacentOfFaceLinkAdjacent hadjTarget)
      have hadjSourceTrue :
          faceLinkAdjacentB n sourceLeft sourceRight = true :=
        faceLinkAdjacentB_true_of_actualAdjacent
          hleftPhysical hrightPhysical hadjSourceActual
      have hadjSourceFalse :
          faceLinkAdjacentB n sourceLeft sourceRight = false :=
        hseparated sourceLeft hsourceLeft sourceRight hsourceRight
      have hbad : false = true := by
        simpa only [hadjSourceFalse] using hadjSourceTrue
      exact False.elim (Bool.false_ne_true hbad)

/-- Conversely, disjointness of the transported supports reflects back to the
source box. -/
theorem supportsDisjoint_of_transport
    {n m : Nat} (hnm : n ≤ m) {left right : List Nat}
    (hleftSupport : left ∈ cutoffOneFaceSupports n)
    (hrightSupport : right ∈ cutoffOneFaceSupports n)
    (hdisjoint : FiniteBoolGraphComponents.SupportsDisjoint
      (transportPolymer n m left) (transportPolymer n m right)) :
    FiniteBoolGraphComponents.SupportsDisjoint left right := by
  intro sourceFace hsourceLeft hsourceRight
  obtain ⟨targetLeft, htargetLeft, hleftEq⟩ :=
    transportPolymerMemberTarget hnm hleftSupport hsourceLeft
  obtain ⟨targetRight, htargetRight, hrightEq⟩ :=
    transportPolymerMemberTarget hnm hrightSupport hsourceRight
  have hleftPhysical : targetLeft ∈ physicalFaceEdges m :=
    mem_of_mem_sublists (physicalFaceEdges m)
      (transportPolymer n m left)
      (transportPolymer_mem_cutoffOneFaceSupports n m left)
      targetLeft htargetLeft
  have hrightPhysical : targetRight ∈ physicalFaceEdges m :=
    mem_of_mem_sublists (physicalFaceEdges m)
      (transportPolymer n m right)
      (transportPolymer_mem_cutoffOneFaceSupports n m right)
      targetRight htargetRight
  have htargetEq : targetLeft = targetRight :=
    boxPlaquetteAt_injective_on_physical hleftPhysical hrightPhysical
      (hleftEq.symm.trans hrightEq)
  subst targetRight
  exact hdisjoint targetLeft htargetLeft htargetRight

/-- Link separation of transported supports likewise reflects back to the
source numerical encoding. -/
theorem supportsSeparated_of_transport
    {n m : Nat} (hnm : n ≤ m) {left right : List Nat}
    (hleftSupport : left ∈ cutoffOneFaceSupports n)
    (hrightSupport : right ∈ cutoffOneFaceSupports n)
    (hseparated : FiniteBoolGraphComponents.SupportsSeparated
      (faceLinkAdjacentB m)
      (transportPolymer n m left) (transportPolymer n m right)) :
    FiniteBoolGraphComponents.SupportsSeparated
      (faceLinkAdjacentB n) left right := by
  intro sourceLeft hsourceLeft sourceRight hsourceRight
  cases hadjSource : faceLinkAdjacentB n sourceLeft sourceRight with
  | false => rfl
  | true =>
      obtain ⟨targetLeft, htargetLeft, hleftEq⟩ :=
        transportPolymerMemberTarget hnm hleftSupport hsourceLeft
      obtain ⟨targetRight, htargetRight, hrightEq⟩ :=
        transportPolymerMemberTarget hnm hrightSupport hsourceRight
      have hleftPhysical : targetLeft ∈ physicalFaceEdges m :=
        mem_of_mem_sublists (physicalFaceEdges m)
          (transportPolymer n m left)
          (transportPolymer_mem_cutoffOneFaceSupports n m left)
          targetLeft htargetLeft
      have hrightPhysical : targetRight ∈ physicalFaceEdges m :=
        mem_of_mem_sublists (physicalFaceEdges m)
          (transportPolymer n m right)
          (transportPolymer_mem_cutoffOneFaceSupports n m right)
          targetRight htargetRight
      have hadjTargetActual : z4Chain.toLattice.Adjacent
          (boxPlaquetteAt m targetLeft) (boxPlaquetteAt m targetRight) := by
        simpa only [← hleftEq, ← hrightEq] using
          (actualAdjacentOfFaceLinkAdjacent hadjSource)
      have hadjTargetTrue :
          faceLinkAdjacentB m targetLeft targetRight = true :=
        faceLinkAdjacentB_true_of_actualAdjacent
          hleftPhysical hrightPhysical hadjTargetActual
      have hadjTargetFalse :
          faceLinkAdjacentB m targetLeft targetRight = false :=
        hseparated targetLeft htargetLeft targetRight htargetRight
      have hbad : false = true := by
        simpa only [hadjTargetFalse] using hadjTargetTrue
      exact False.elim (Bool.false_ne_true hbad)

/-- Transport is injective on canonical polymers: a geometric connected
support cannot acquire a second canonical numerical name in the larger box. -/
theorem transportPolymer_injective_on_canonical
    {n m : Nat} (hnm : n ≤ m) {left right : List Nat}
    (hleft : left ∈ canonicalSurfacePolymers n)
    (hright : right ∈ canonicalSurfacePolymers n)
    (heq : transportPolymer n m left = transportPolymer n m right) :
    left = right := by
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport hleft hright
  have hleftTransport := transportPolymer_sameSupport hnm
    (canonicalSurfacePolymer_mem_faceSupports hleft)
  have hrightTransport := transportPolymer_sameSupport hnm
    (canonicalSurfacePolymer_mem_faceSupports hright)
  rw [heq] at hleftTransport
  exact sameSupport_trans hleftTransport
    (sameSupport_symm hrightTransport)

/-! ## 4. Transport of compatible families and their exact weights -/

def transportFamily (n m : Nat) (family : List (List Nat)) :
    List (List Nat) :=
  family.map (transportPolymer n m)

/-- Put a transported family back into the canonical polymer order of the
larger box.  This is the representative that can literally occur in the
larger box's `sublists` enumeration. -/
def embeddedTransportFamily (n m : Nat) (family : List (List Nat)) :
    List (List Nat) :=
  ambientOrderedFamily m (transportFamily n m family)

theorem mem_embeddedTransportFamily_iff
    {n m : Nat} (hnm : n ≤ m)
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n)
    (target : List Nat) :
    target ∈ embeddedTransportFamily n m family ↔
      ∃ source, source ∈ family ∧
        target = transportPolymer n m source := by
  unfold embeddedTransportFamily
  rw [mem_ambientOrderedFamily_iff]
  constructor
  · intro htarget
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp htarget.2
    exact ⟨source, hsource, heq.symm⟩
  · rintro ⟨source, hsource, rfl⟩
    constructor
    · exact transportPolymer_mem_canonicalSurfacePolymers hnm
        (compatibleAmbientFamily_member_ambient hfamily hsource)
    · unfold transportFamily
      exact List.mem_map.mpr ⟨source, hsource, rfl⟩

theorem embeddedTransportFamily_invariants
    {n m : Nat} (hnm : n ≤ m)
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    FiniteBoolGraphComponents.DistinctDisjoint
        (embeddedTransportFamily n m family) ∧
      FiniteBoolGraphComponents.DistinctSeparated
        (faceLinkAdjacentB m) (embeddedTransportFamily n m family) := by
  have hsource := compatibleAmbientFamily_invariants hfamily
  constructor
  · intro targetLeft htargetLeft targetRight htargetRight hne
    obtain ⟨sourceLeft, hsourceLeft, hleftEq⟩ :=
      (mem_embeddedTransportFamily_iff hnm hfamily targetLeft).mp
        htargetLeft
    obtain ⟨sourceRight, hsourceRight, hrightEq⟩ :=
      (mem_embeddedTransportFamily_iff hnm hfamily targetRight).mp
        htargetRight
    have hsourceNe : sourceLeft ≠ sourceRight := by
      intro heq
      subst sourceRight
      exact hne (hleftEq.trans hrightEq.symm)
    rw [hleftEq, hrightEq]
    exact supportsDisjoint_transport hnm
      (compatibleAmbientFamily_member_faceSupport hfamily hsourceLeft)
      (compatibleAmbientFamily_member_faceSupport hfamily hsourceRight)
      (hsource.1 sourceLeft hsourceLeft sourceRight hsourceRight hsourceNe)
  · intro targetLeft htargetLeft targetRight htargetRight hne
    obtain ⟨sourceLeft, hsourceLeft, hleftEq⟩ :=
      (mem_embeddedTransportFamily_iff hnm hfamily targetLeft).mp
        htargetLeft
    obtain ⟨sourceRight, hsourceRight, hrightEq⟩ :=
      (mem_embeddedTransportFamily_iff hnm hfamily targetRight).mp
        htargetRight
    have hsourceNe : sourceLeft ≠ sourceRight := by
      intro heq
      subst sourceRight
      exact hne (hleftEq.trans hrightEq.symm)
    rw [hleftEq, hrightEq]
    exact supportsSeparated_transport hnm
      (compatibleAmbientFamily_member_faceSupport hfamily hsourceLeft)
      (compatibleAmbientFamily_member_faceSupport hfamily hsourceRight)
      (hsource.2 sourceLeft hsourceLeft sourceRight hsourceRight hsourceNe)

/-- The canonical reordering of every smaller compatible family is an actual
member of the larger compatible-family ensemble. -/
theorem embeddedTransportFamily_mem_compatible
    {n m : Nat} (hnm : n ≤ m)
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    embeddedTransportFamily n m family ∈
      canonicalCompatibleAmbientFamilies m := by
  unfold canonicalCompatibleAmbientFamilies
  apply List.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · unfold embeddedTransportFamily ambientOrderedFamily
    exact filter_mem_sublists _ _
  · exact canonicalFamilyCompatibleB_true m
      (embeddedTransportFamily n m family)
      (ambientOrderedFamily_nodup m (transportFamily n m family))
      (embeddedTransportFamily_invariants hnm hfamily).1
      (embeddedTransportFamily_invariants hnm hfamily).2

theorem transportFamily_nodup
    {n m : Nat} (hnm : n ≤ m)
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    (transportFamily n m family).Nodup := by
  unfold transportFamily
  apply nodup_map_of_injOn (transportPolymer n m) family
    (compatibleAmbientFamily_nodup hfamily)
  intro left hleft right hright heq
  exact transportPolymer_injective_on_canonical hnm
    (compatibleAmbientFamily_member_ambient hfamily hleft)
    (compatibleAmbientFamily_member_ambient hfamily hright) heq

theorem transportFamily_perm_embedded
    {n m : Nat} (hnm : n ≤ m)
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    (transportFamily n m family).Perm
      (embeddedTransportFamily n m family) := by
  apply perm_of_nodup_mem_iff
    (transportFamily n m family) (embeddedTransportFamily n m family)
    (transportFamily_nodup hnm hfamily)
    (ambientOrderedFamily_nodup m (transportFamily n m family))
  intro target
  unfold embeddedTransportFamily
  rw [mem_ambientOrderedFamily_iff]
  constructor
  · intro htarget
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp htarget
    rw [← heq]
    exact ⟨transportPolymer_mem_canonicalSurfacePolymers hnm
      (compatibleAmbientFamily_member_ambient hfamily hsource),
      List.mem_map.mpr ⟨source, hsource, rfl⟩⟩
  · exact fun htarget => htarget.2

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem canonicalSurfaceFamilyActivity_transport
    (w : Q') {n m : Nat} (hnm : n ≤ m) :
    ∀ family : List (List Nat),
    (∀ support, support ∈ family →
      support ∈ cutoffOneFaceSupports n) →
    (canonicalSurfaceFamilyActivity w n family).eqv
      (canonicalSurfaceFamilyActivity w m
        (transportFamily n m family))
  | [], _ => Q'.eqv_refl _
  | support :: rest, hmembers => by
      change (canonicalSurfaceActivity w n support *
          canonicalSurfaceFamilyActivity w n rest).eqv
        (canonicalSurfaceActivity w m (transportPolymer n m support) *
          canonicalSurfaceFamilyActivity w m (transportFamily n m rest))
      exact qmul_congr_local
        (canonicalSurfaceActivity_transport w hnm
          (hmembers support List.mem_cons_self))
        (canonicalSurfaceFamilyActivity_transport w hnm rest
          (fun item hitem =>
            hmembers item (List.mem_cons_of_mem support hitem)))

theorem compatibleFamilyActivity_transport
    (w : Q') {n m : Nat} (hnm : n ≤ m)
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    (canonicalSurfaceFamilyActivity w n family).eqv
      (canonicalSurfaceFamilyActivity w m
        (transportFamily n m family)) := by
  apply canonicalSurfaceFamilyActivity_transport w hnm family
  intro support hsupport
  exact compatibleAmbientFamily_member_faceSupport hfamily hsupport

/-- Exact family activity is unchanged after transport and the canonical
reordering required by the larger ambient enumeration. -/
theorem compatibleFamilyActivity_embedded_transport
    (w : Q') {n m : Nat} (hnm : n ≤ m)
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    canonicalSurfaceFamilyActivity w n family ≈
      canonicalSurfaceFamilyActivity w m
        (embeddedTransportFamily n m family) :=
  Q'.eqv_trans _ _ _
    (compatibleFamilyActivity_transport w hnm hfamily)
    (canonicalSurfaceFamilyActivity_perm w m
      (transportFamily_perm_embedded hnm hfamily))

/-! ## 4. The exact transported finite partition -/

def transportedCompatibleFamilies (n m : Nat) :
    List (List (List Nat)) :=
  (canonicalCompatibleAmbientFamilies n).map (transportFamily n m)

def transportedAnchorPartition (n m : Nat) : Q' :=
  listQSum (canonicalSurfaceFamilyActivity anchorCoupling m)
    (transportedCompatibleFamilies n m)

/-- The weight-preserving image written as literal members of the larger
compatible-family enumeration. -/
def embeddedCompatibleFamilies (n m : Nat) :
    List (List (List Nat)) :=
  (canonicalCompatibleAmbientFamilies n).map
    (embeddedTransportFamily n m)

def embeddedAnchorPartition (n m : Nat) : Q' :=
  listQSum (canonicalSurfaceFamilyActivity anchorCoupling m)
    (embeddedCompatibleFamilies n m)

theorem embeddedCompatibleFamilies_member_target
    {n m : Nat} (hnm : n ≤ m) {targetFamily : List (List Nat)}
    (htarget : targetFamily ∈ embeddedCompatibleFamilies n m) :
    targetFamily ∈ canonicalCompatibleAmbientFamilies m := by
  obtain ⟨sourceFamily, hsource, heq⟩ := List.mem_map.mp htarget
  rw [← heq]
  exact embeddedTransportFamily_mem_compatible hnm hsource

/-- Canonical transport is injective on compatible families. -/
theorem embeddedTransportFamily_injective_on_compatible
    {n m : Nat} (hnm : n ≤ m)
    {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (heq : embeddedTransportFamily n m left =
      embeddedTransportFamily n m right) :
    left = right := by
  apply sublists_eq_of_mem_iff (canonicalSurfacePolymers n) left right
    (canonicalSurfacePolymers_nodup n)
    (compatibleAmbientFamily_sublist hleft)
    (compatibleAmbientFamily_sublist hright)
  intro source
  constructor
  · intro hsource
    have htarget : transportPolymer n m source ∈
        embeddedTransportFamily n m left :=
      (mem_embeddedTransportFamily_iff hnm hleft
        (transportPolymer n m source)).2 ⟨source, hsource, rfl⟩
    rw [heq] at htarget
    obtain ⟨other, hother, htransport⟩ :=
      (mem_embeddedTransportFamily_iff hnm hright
        (transportPolymer n m source)).1 htarget
    have hsourceEq : source = other :=
      transportPolymer_injective_on_canonical hnm
        (compatibleAmbientFamily_member_ambient hleft hsource)
        (compatibleAmbientFamily_member_ambient hright hother)
        htransport
    rw [hsourceEq]
    exact hother
  · intro hsource
    have htarget : transportPolymer n m source ∈
        embeddedTransportFamily n m right :=
      (mem_embeddedTransportFamily_iff hnm hright
        (transportPolymer n m source)).2 ⟨source, hsource, rfl⟩
    rw [← heq] at htarget
    obtain ⟨other, hother, htransport⟩ :=
      (mem_embeddedTransportFamily_iff hnm hleft
        (transportPolymer n m source)).1 htarget
    have hsourceEq : source = other :=
      transportPolymer_injective_on_canonical hnm
        (compatibleAmbientFamily_member_ambient hright hsource)
        (compatibleAmbientFamily_member_ambient hleft hother)
        htransport
    rw [hsourceEq]
    exact hother

theorem embeddedCompatibleFamilies_nodup
    {n m : Nat} (hnm : n ≤ m) :
    (embeddedCompatibleFamilies n m).Nodup := by
  unfold embeddedCompatibleFamilies
  apply nodup_map_of_injOn (embeddedTransportFamily n m)
    (canonicalCompatibleAmbientFamilies n)
    (canonicalCompatibleAmbientFamilies_nodup n)
  intro left hleft right hright heq
  exact embeddedTransportFamily_injective_on_compatible
    hnm hleft hright heq

/-- The embedded ensemble as a literal filter of the target enumeration. -/
def embeddedTargetFamilies (n m : Nat) : List (List (List Nat)) :=
  (canonicalCompatibleAmbientFamilies m).filter
    (fun family => decide (family ∈ embeddedCompatibleFamilies n m))

theorem embeddedCompatibleFamilies_perm_target
    {n m : Nat} (hnm : n ≤ m) :
    (embeddedCompatibleFamilies n m).Perm (embeddedTargetFamilies n m) := by
  apply perm_of_nodup_mem_iff
    (embeddedCompatibleFamilies n m) (embeddedTargetFamilies n m)
    (embeddedCompatibleFamilies_nodup hnm)
  · unfold embeddedTargetFamilies
    exact List.filter_sublist.nodup
      (canonicalCompatibleAmbientFamilies_nodup m)
  · intro family
    unfold embeddedTargetFamilies
    rw [List.mem_filter]
    simp only [decide_eq_true_eq]
    constructor
    · intro hfamily
      exact ⟨embeddedCompatibleFamilies_member_target hnm hfamily,
        hfamily⟩
    · exact fun hfamily => hfamily.2

private theorem listQSum_map_eqv_transport {A B : Type}
    (f : A → Q') (g : B → Q') (reindex : A → B) :
    ∀ xs : List A,
    (∀ item, item ∈ xs → (f item).eqv (g (reindex item))) →
      (listQSum f xs).eqv (listQSum g (xs.map reindex))
  | [], _ => Q'.eqv_refl _
  | head :: rest, h =>
      Q'.add_eqv_congr'
        (h head List.mem_cons_self)
        (listQSum_map_eqv_transport f g reindex rest
          (fun item hitem =>
            h item (List.mem_cons_of_mem head hitem)))

/-- Rewriting every smaller-box family in larger-box coordinates preserves
the entire exact finite partition. -/
theorem anchorCanonicalPartition_eqv_transported
    {n m : Nat} (hnm : n ≤ m) :
    anchorCanonicalPartition n ≈ transportedAnchorPartition n m := by
  unfold anchorCanonicalPartition transportedAnchorPartition
    transportedCompatibleFamilies
    parametricCanonicalCompatibleAmbientPartition
  apply listQSum_map_eqv_transport
  intro family hfamily
  exact compatibleFamilyActivity_transport anchorCoupling hnm hfamily

/-- The complete smaller-box partition is exactly the weight of a genuine
finite subensemble of the larger-box gas. -/
theorem anchorCanonicalPartition_eqv_embedded
    {n m : Nat} (hnm : n ≤ m) :
    anchorCanonicalPartition n ≈ embeddedAnchorPartition n m := by
  unfold anchorCanonicalPartition embeddedAnchorPartition
    embeddedCompatibleFamilies parametricCanonicalCompatibleAmbientPartition
  apply listQSum_map_eqv_transport
  intro family hfamily
  exact compatibleFamilyActivity_embedded_transport
    anchorCoupling hnm hfamily

/-- The positive weight of the embedded ensemble is bounded by the full
larger-box partition. -/
theorem embeddedAnchorPartition_le_target
    {n m : Nat} (hnm : n ≤ m) :
    embeddedAnchorPartition n m ≤ anchorCanonicalPartition m := by
  have hperm := listQSum_perm
    (canonicalSurfaceFamilyActivity anchorCoupling m)
    (embeddedCompatibleFamilies_perm_target hnm)
  have hfilter : listQSum
      (canonicalSurfaceFamilyActivity anchorCoupling m)
      (embeddedTargetFamilies n m) ≤
      listQSum (canonicalSurfaceFamilyActivity anchorCoupling m)
        (canonicalCompatibleAmbientFamilies m) := by
    unfold embeddedTargetFamilies
    exact listQSum_filter_le
      (canonicalSurfaceFamilyActivity anchorCoupling m)
      (fun family => decide
        (family ∈ embeddedCompatibleFamilies n m))
      (canonicalSurfaceFamilyActivity_nonnegative m)
      (canonicalCompatibleAmbientFamilies m)
  unfold embeddedAnchorPartition anchorCanonicalPartition
    parametricCanonicalCompatibleAmbientPartition
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hperm) hfilter

/-- Exact finite-volume partition monotonicity under box inclusion. -/
theorem anchorCanonicalPartition_mono
    {n m : Nat} (hnm : n ≤ m) :
    anchorCanonicalPartition n ≤ anchorCanonicalPartition m :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (anchorCanonicalPartition_eqv_embedded hnm))
    (embeddedAnchorPartition_le_target hnm)

end YMGap.Continuum.Z4CanonicalPolymerTransport

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalPolymerTransport.geometricSupportIds_sameSupport
#print axioms YMGap.Continuum.Z4CanonicalPolymerTransport.transportPolymer_sameSupport
#print axioms YMGap.Continuum.Z4CanonicalPolymerTransport.transportPolymer_length_eq
#print axioms YMGap.Continuum.Z4CanonicalPolymerTransport.canonicalSurfaceActivity_transport
#print axioms YMGap.Continuum.Z4CanonicalPolymerTransport.faceLinkAdjacentB_true_of_actualAdjacent
#print axioms YMGap.Continuum.Z4CanonicalPolymerTransport.geometricSupportIds_connected
#print axioms YMGap.Continuum.Z4CanonicalPolymerTransport.connectedFaceSupport_mem_canonicalSurfacePolymers
#print axioms YMGap.Continuum.Z4CanonicalPolymerTransport.transportPolymer_mem_canonicalSurfacePolymers
#print axioms YMGap.Continuum.Z4CanonicalPolymerTransport.supportsDisjoint_transport
#print axioms YMGap.Continuum.Z4CanonicalPolymerTransport.supportsSeparated_transport
#print axioms YMGap.Continuum.Z4CanonicalPolymerTransport.embeddedTransportFamily_mem_compatible
#print axioms YMGap.Continuum.Z4CanonicalPolymerTransport.canonicalSurfaceFamilyActivity_transport
#print axioms YMGap.Continuum.Z4CanonicalPolymerTransport.anchorCanonicalPartition_eqv_transported
#print axioms YMGap.Continuum.Z4CanonicalPolymerTransport.anchorCanonicalPartition_eqv_embedded
#print axioms YMGap.Continuum.Z4CanonicalPolymerTransport.embeddedAnchorPartition_le_target
#print axioms YMGap.Continuum.Z4CanonicalPolymerTransport.anchorCanonicalPartition_mono
