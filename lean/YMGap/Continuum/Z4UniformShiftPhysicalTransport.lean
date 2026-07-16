/-
# Uniform affine transport into a four-sided padded Z4 box

The existing affine transport moves a finite physical labelling only in
Euclidean time.  A centered thermodynamic exhaustion needs the marked region
to recede from every face of the corner box.  This file translates all four
coordinates by the same nonnegative padding and embeds a source box of side
`base` into the box of side `base + 2 * padding`.

The translation preserves incidence and connectedness.  Canonical supports
are re-encoded exactly, and bounded physical labellings are read on the
translated plaquette list and extended by the vacuum label elsewhere.  The
map is injective on the finite physical enumeration and transports the exact
excited support.  This is configuration/support transport only: preservation
of the complete spin-foam summand and normalized boundary stability are
separate required layers.
-/

import YMGap.Continuum.Z4TimeShiftedPhysicalTransport

namespace YMGap.Continuum.Z4UniformShiftPhysicalTransport

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4TimeShiftedPhysicalTransport
open YMGap.Continuum.Z4UnitCubeEnumerationParity

/-! ## 1. Uniform translation geometry -/

def uniformPaddedBase (padding base : Nat) : Nat :=
  base + padding + padding

def uniformShiftVertex (padding : Nat) : Z4Vertex → Z4Vertex
  | (a, b, c, d) =>
      (a + padding, b + padding, c + padding, d + padding)

def uniformShiftLink (padding : Nat) (link : Z4Link) : Z4Link :=
  (uniformShiftVertex padding link.1, link.2)

def uniformShiftPlaquette (padding : Nat) (plaquette : Z4Plaq) : Z4Plaq :=
  (uniformShiftVertex padding plaquette.1, plaquette.2)

theorem uniformShiftVertex_injective (padding : Nat) :
    Function.Injective (uniformShiftVertex padding) := by
  intro left right heq
  obtain ⟨a, b, c, d⟩ := left
  obtain ⟨a', b', c', d'⟩ := right
  simp only [uniformShiftVertex, Prod.mk.injEq] at heq ⊢
  exact ⟨Nat.add_right_cancel heq.1,
    Nat.add_right_cancel heq.2.1,
    Nat.add_right_cancel heq.2.2.1,
    Nat.add_right_cancel heq.2.2.2⟩

theorem uniformShiftPlaquette_injective (padding : Nat) :
    Function.Injective (uniformShiftPlaquette padding) := by
  intro left right heq
  apply Prod.ext
  · apply uniformShiftVertex_injective padding
    simpa only [uniformShiftPlaquette] using congrArg Prod.fst heq
  · simpa only [uniformShiftPlaquette] using congrArg Prod.snd heq

theorem uniformShiftVertex_addE
    (padding : Nat) (vertex : Z4Vertex) (direction : Dir4) :
    uniformShiftVertex padding (addE vertex direction) =
      addE (uniformShiftVertex padding vertex) direction := by
  obtain ⟨a, b, c, d⟩ := vertex
  cases direction <;> simp [uniformShiftVertex, addE] <;> omega

theorem edgesOf_uniformShiftPlaquette
    (padding : Nat) (plaquette : Z4Plaq) :
    edgesOf (uniformShiftPlaquette padding plaquette) =
      (edgesOf plaquette).map (uniformShiftLink padding) := by
  simp [edgesOf, uniformShiftPlaquette, uniformShiftLink,
    uniformShiftVertex_addE]

def uniformShiftAdjacent (padding : Nat) {left right : Z4Plaq}
    (adjacent : z4Chain.toLattice.Adjacent left right) :
    z4Chain.toLattice.Adjacent
      (uniformShiftPlaquette padding left)
      (uniformShiftPlaquette padding right) := by
  refine {
    link := uniformShiftLink padding adjacent.link
    on_p := ?_
    on_q := ?_
  }
  · change z4Boundary (uniformShiftPlaquette padding left)
      (uniformShiftLink padding adjacent.link) = true
    unfold z4Boundary
    rw [edgesOf_uniformShiftPlaquette]
    apply decide_eq_true
    exact List.mem_map.mpr
      ⟨adjacent.link, of_decide_eq_true adjacent.on_p, rfl⟩
  · change z4Boundary (uniformShiftPlaquette padding right)
      (uniformShiftLink padding adjacent.link) = true
    unfold z4Boundary
    rw [edgesOf_uniformShiftPlaquette]
    apply decide_eq_true
    exact List.mem_map.mpr
      ⟨adjacent.link, of_decide_eq_true adjacent.on_q, rfl⟩

def uniformShiftChain (padding : Nat) {support : List Z4Plaq} :
    {first last : Z4Plaq} →
      ChainIn z4Chain.toLattice support first last →
      ChainIn z4Chain.toLattice
        (support.map (uniformShiftPlaquette padding))
        (uniformShiftPlaquette padding first)
        (uniformShiftPlaquette padding last)
  | _, _, .refl plaquette => .refl _
  | _, _, .step adjacent hnext rest =>
      .step (uniformShiftAdjacent padding adjacent)
        (List.mem_map.mpr ⟨_, hnext, rfl⟩)
        (uniformShiftChain padding rest)

def uniformShiftConnected (padding : Nat) {support : List Z4Plaq}
    (hconnected : connectedIn (L := z4Chain.toLattice) support) :
    connectedIn (L := z4Chain.toLattice)
      (support.map (uniformShiftPlaquette padding)) := by
  intro first last hfirst hlast
  obtain ⟨sourceFirst, hsourceFirst, hfirstEq⟩ :=
    decodeMapMember (uniformShiftPlaquette padding) support first hfirst
  obtain ⟨sourceLast, hsourceLast, hlastEq⟩ :=
    decodeMapMember (uniformShiftPlaquette padding) support last hlast
  rw [← hfirstEq, ← hlastEq]
  exact uniformShiftChain padding
    (hconnected sourceFirst sourceLast hsourceFirst hsourceLast)

theorem uniformShiftPlaquette_mem_padded_box
    {padding base : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes base) :
    uniformShiftPlaquette padding plaquette ∈
      boxPlaquettes (uniformPaddedBase padding base) := by
  rw [mem_boxPlaquettes] at hplaquette ⊢
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  simp only [uniformShiftPlaquette, uniformShiftVertex]
  have extend : ∀ coordinate : Nat, coordinate < base →
      coordinate + padding < uniformPaddedBase padding base := by
    intro coordinate hcoordinate
    unfold uniformPaddedBase
    exact Nat.lt_of_lt_of_le
      (Nat.add_lt_add_right hcoordinate padding)
      (Nat.le_add_right (base + padding) padding)
  exact ⟨extend a hplaquette.1,
    extend b hplaquette.2.1,
    extend c hplaquette.2.2.1,
    extend d hplaquette.2.2.2⟩

/-! ## 2. Canonical re-encoding in the padded target -/

def uniformShiftCanonicalRoot (padding base : Nat)
    (root : List Nat) : List Nat :=
  geometricSupportIds (uniformPaddedBase padding base)
    ((geometricPolymer base root).map
      (uniformShiftPlaquette padding))

theorem uniformShiftCanonicalRoot_sameSupport
    {padding base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (uniformPaddedBase padding base)
        (uniformShiftCanonicalRoot padding base root))
      ((geometricPolymer base root).map
        (uniformShiftPlaquette padding)) := by
  unfold uniformShiftCanonicalRoot
  apply geometricSupportIds_sameSupport
  intro plaquette hplaquette
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
  exact uniformShiftPlaquette_mem_padded_box
    (geometricPolymer_subset_box
      (canonicalSurfacePolymer_mem_faceSupports hroot) source hsource)

def uniformShiftCanonicalRoot_nonempty
    {padding base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    Σ' face : Nat, face ∈ uniformShiftCanonicalRoot padding base root := by
  obtain ⟨sourceFace, hsourceFace⟩ :=
    canonicalSurfacePolymers_allNonempty base root hroot
  have hsource : boxPlaquetteAt base sourceFace ∈
      geometricPolymer base root :=
    List.mem_map.mpr ⟨sourceFace, hsourceFace, rfl⟩
  have htranslated :
      uniformShiftPlaquette padding (boxPlaquetteAt base sourceFace) ∈
        (geometricPolymer base root).map
          (uniformShiftPlaquette padding) :=
    List.mem_map.mpr ⟨boxPlaquetteAt base sourceFace, hsource, rfl⟩
  have hencoded := (uniformShiftCanonicalRoot_sameSupport hroot).2
    _ htranslated
  obtain ⟨targetFace, htargetFace, _⟩ :=
    decodeMapMember (boxPlaquetteAt (uniformPaddedBase padding base))
      (uniformShiftCanonicalRoot padding base root)
      (uniformShiftPlaquette padding (boxPlaquetteAt base sourceFace))
      hencoded
  exact ⟨targetFace, htargetFace⟩

def uniformShiftCanonicalRoot_connected
    {padding base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    InternallyConnected
      (faceLinkAdjacentB (uniformPaddedBase padding base))
      (uniformShiftCanonicalRoot padding base root) := by
  unfold uniformShiftCanonicalRoot
  apply geometricSupportIds_connected
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact uniformShiftPlaquette_mem_padded_box
      (geometricPolymer_subset_box
        (canonicalSurfacePolymer_mem_faceSupports hroot) source hsource)
  · exact uniformShiftConnected padding
      (numericalConnectedToGeometric
        ((canonicalSurfacePolymers_allConnected base) root hroot))

theorem uniformShiftCanonicalRoot_canonical
    {padding base : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    uniformShiftCanonicalRoot padding base root ∈
      canonicalSurfacePolymers (uniformPaddedBase padding base) :=
  connectedFaceSupport_mem_canonicalSurfacePolymers
    (geometricSupportIds_mem_cutoffOneFaceSupports
      (uniformPaddedBase padding base)
      ((geometricPolymer base root).map
        (uniformShiftPlaquette padding)))
    (uniformShiftCanonicalRoot_nonempty hroot)
    (uniformShiftCanonicalRoot_connected hroot)

theorem uniformShiftCanonicalRoot_injective_on_canonical
    {padding base : Nat} {left right : List Nat}
    (hleft : left ∈ canonicalSurfacePolymers base)
    (hright : right ∈ canonicalSurfacePolymers base)
    (heq : uniformShiftCanonicalRoot padding base left =
      uniformShiftCanonicalRoot padding base right) :
    left = right := by
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport hleft hright
  have hleftShift := uniformShiftCanonicalRoot_sameSupport
    (padding := padding) hleft
  have hrightShift := uniformShiftCanonicalRoot_sameSupport
    (padding := padding) hright
  rw [heq] at hleftShift
  have hmapped := sameSupport_trans
    (sameSupport_symm hleftShift) hrightShift
  constructor
  · intro plaquette hplaquette
    have htranslated : uniformShiftPlaquette padding plaquette ∈
        (geometricPolymer base left).map
          (uniformShiftPlaquette padding) :=
      List.mem_map.mpr ⟨plaquette, hplaquette, rfl⟩
    obtain ⟨source, hsource, heqSource⟩ :=
      List.mem_map.mp (hmapped.1 _ htranslated)
    have : source = plaquette :=
      uniformShiftPlaquette_injective padding heqSource
    simpa only [this] using hsource
  · intro plaquette hplaquette
    have htranslated : uniformShiftPlaquette padding plaquette ∈
        (geometricPolymer base right).map
          (uniformShiftPlaquette padding) :=
      List.mem_map.mpr ⟨plaquette, hplaquette, rfl⟩
    obtain ⟨source, hsource, heqSource⟩ :=
      List.mem_map.mp (hmapped.2 _ htranslated)
    have : source = plaquette :=
      uniformShiftPlaquette_injective padding heqSource
    simpa only [this] using hsource

/-! ## 3. Vacuum extension of finite physical labellings -/

def uniformShiftedPlaquetteList (padding base : Nat) : List Z4Plaq :=
  (boxPlaquettes base).map (uniformShiftPlaquette padding)

theorem uniformShiftedPlaquetteList_nodup (padding base : Nat) :
    (uniformShiftedPlaquetteList padding base).Nodup := by
  unfold uniformShiftedPlaquetteList
  exact nodup_map_of_injOn (uniformShiftPlaquette padding)
    (boxPlaquettes base) (boxPlaquettes_nodup base)
    (fun _ _ _ _ heq => uniformShiftPlaquette_injective padding heq)

def uniformShiftedGeometricSpin (padding base : Nat)
    (physical : EdgeLabelling) (plaquette : Z4Plaq) : Nat :=
  lookupLabelFrom physical 0
    (uniformShiftedPlaquetteList padding base) plaquette

theorem uniformShiftedGeometricSpin_recover
    (padding base : Nat) (physical : EdgeLabelling)
    (plaquette : Z4Plaq) :
    uniformShiftedGeometricSpin padding base physical
        (uniformShiftPlaquette padding plaquette) =
      geometricSpinOfPhysical base physical plaquette := by
  unfold uniformShiftedGeometricSpin uniformShiftedPlaquetteList
    geometricSpinOfPhysical
  exact lookupLabelFrom_map_injective physical
    (uniformShiftPlaquette padding)
    (uniformShiftPlaquette_injective padding)
    0 (boxPlaquettes base) plaquette

theorem uniformShiftedGeometricSpin_zero_of_not_mem
    (padding base : Nat) (physical : EdgeLabelling) {plaquette : Z4Plaq}
    (hnot : plaquette ∉ uniformShiftedPlaquetteList padding base) :
    uniformShiftedGeometricSpin padding base physical plaquette = 0 := by
  unfold uniformShiftedGeometricSpin
  exact lookupLabelFrom_zero_of_not_mem physical 0
    (uniformShiftedPlaquetteList padding base) plaquette hnot

theorem uniformShiftedGeometricSpin_le_of_bounded
    {K padding base : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount base)))
    (plaquette : Z4Plaq) :
    uniformShiftedGeometricSpin padding base physical plaquette ≤ K := by
  by_cases hmem : plaquette ∈ uniformShiftedPlaquetteList padding base
  · obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hmem
    rw [uniformShiftedGeometricSpin_recover]
    exact geometricSpinOfPhysical_le_of_bounded hphysical source
  · rw [uniformShiftedGeometricSpin_zero_of_not_mem
      padding base physical hmem]
    exact Nat.zero_le K

def uniformShiftTransportPhysical (padding base : Nat)
    (physical : EdgeLabelling) : EdgeLabelling :=
  fun targetId =>
    if targetId < plaquetteEdgeCount (uniformPaddedBase padding base) then
      uniformShiftedGeometricSpin padding base physical
        (boxPlaquetteAt (uniformPaddedBase padding base) targetId)
    else 0

theorem uniformShiftTransportPhysical_eq_on_enumerate
    {padding base targetId : Nat} {physical : EdgeLabelling}
    {plaquette : Z4Plaq}
    (hindexed : (targetId, plaquette) ∈
      enumerate (boxPlaquettes (uniformPaddedBase padding base))) :
    uniformShiftTransportPhysical padding base physical targetId =
      uniformShiftedGeometricSpin padding base physical plaquette := by
  have hlt : targetId <
      plaquetteEdgeCount (uniformPaddedBase padding base) := by
    unfold plaquetteEdgeCount
    exact enumerate_index_lt hindexed
  unfold uniformShiftTransportPhysical
  rw [if_pos hlt, boxPlaquetteAt_eq_of_enumerate hindexed]

theorem uniformShiftTransportPhysical_zero_outside
    (padding base : Nat) (physical : EdgeLabelling) {targetId : Nat}
    (hnot : targetId ∉ List.range
      (plaquetteEdgeCount (uniformPaddedBase padding base))) :
    uniformShiftTransportPhysical padding base physical targetId = 0 := by
  unfold uniformShiftTransportPhysical
  rw [if_neg (by
    intro hlt
    exact hnot (List.mem_range.mpr hlt))]

theorem geometricSpinOfUniformShiftTransport_eq_of_mem_box
    {padding base : Nat} {physical : EdgeLabelling}
    {plaquette : Z4Plaq}
    (hmem : plaquette ∈
      boxPlaquettes (uniformPaddedBase padding base)) :
    geometricSpinOfPhysical (uniformPaddedBase padding base)
        (uniformShiftTransportPhysical padding base physical) plaquette =
      uniformShiftedGeometricSpin padding base physical plaquette := by
  obtain ⟨targetId, hindexed⟩ := exists_mem_enumerate hmem
  rw [geometricSpinOfPhysical_eq_of_enumerate hindexed,
    uniformShiftTransportPhysical_eq_on_enumerate hindexed]

theorem uniformShiftTransportPhysical_mem_bounded
    {K padding base : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount base))) :
    uniformShiftTransportPhysical padding base physical ∈
      boundedEdgeLabellings K
        (List.range
          (plaquetteEdgeCount (uniformPaddedBase padding base))) := by
  apply boundedEdgeLabellings_complete K
  · intro targetId htarget
    have hlt := List.mem_range.mp htarget
    unfold uniformShiftTransportPhysical
    rw [if_pos hlt]
    have hle := uniformShiftedGeometricSpin_le_of_bounded
      (padding := padding) hphysical
      (boxPlaquetteAt (uniformPaddedBase padding base) targetId)
    omega
  · intro targetId hnot
    exact uniformShiftTransportPhysical_zero_outside
      padding base physical hnot

theorem uniformShiftTransportPhysical_injective_on
    {K padding base : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount base)))
    (hright : right ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount base)))
    (heq : uniformShiftTransportPhysical padding base left =
      uniformShiftTransportPhysical padding base right) :
    left = right := by
  funext sourceId
  by_cases hsource : sourceId ∈
      List.range (plaquetteEdgeCount base)
  · have hsourceBox : boxPlaquetteAt base sourceId ∈
        boxPlaquettes base :=
      boxPlaquetteAt_mem_boxPlaquettes_of_physical hsource
    have htargetBox :
        uniformShiftPlaquette padding (boxPlaquetteAt base sourceId) ∈
          boxPlaquettes (uniformPaddedBase padding base) :=
      uniformShiftPlaquette_mem_padded_box hsourceBox
    obtain ⟨targetId, htargetIndexed⟩ :=
      exists_mem_enumerate htargetBox
    have hsourceIndexed :
        (sourceId, boxPlaquetteAt base sourceId) ∈
          enumerate (boxPlaquettes base) :=
      boxPlaquetteAt_mem_enumerate (physicalFaceId_lt hsource)
    have hleftRecover :
        uniformShiftTransportPhysical padding base left targetId =
          left sourceId := by
      rw [uniformShiftTransportPhysical_eq_on_enumerate htargetIndexed,
        uniformShiftedGeometricSpin_recover,
        geometricSpinOfPhysical_eq_of_enumerate hsourceIndexed]
    have hrightRecover :
        uniformShiftTransportPhysical padding base right targetId =
          right sourceId := by
      rw [uniformShiftTransportPhysical_eq_on_enumerate htargetIndexed,
        uniformShiftedGeometricSpin_recover,
        geometricSpinOfPhysical_eq_of_enumerate hsourceIndexed]
    have hcoordinate := congrFun heq targetId
    rw [hleftRecover, hrightRecover] at hcoordinate
    exact hcoordinate
  · have hleftSound := boundedEdgeLabellings_sound K
      (List.range (plaquetteEdgeCount base)) left hleft
    have hrightSound := boundedEdgeLabellings_sound K
      (List.range (plaquetteEdgeCount base)) right hright
    rw [hleftSound.2 sourceId hsource,
      hrightSound.2 sourceId hsource]

/-! ## 4. Exact excited-support transport -/

theorem uniformShiftedGeometricSpin_positive_iff_mem
    (padding base : Nat) (physical : EdgeLabelling)
    (plaquette : Z4Plaq) :
    1 ≤ uniformShiftedGeometricSpin padding base physical plaquette ↔
      plaquette ∈
        (geometricPolymer base
          (excitedPlaquetteIds base physical)).map
            (uniformShiftPlaquette padding) := by
  constructor
  · intro hpositive
    by_cases hmem : plaquette ∈ uniformShiftedPlaquetteList padding base
    · obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hmem
      rw [← heq, uniformShiftedGeometricSpin_recover] at hpositive
      have hsourceExcited :=
        (geometricSpin_positive_iff_mem_geometricSupport
          base physical source).1 hpositive
      exact List.mem_map.mpr ⟨source, hsourceExcited, heq⟩
    · rw [uniformShiftedGeometricSpin_zero_of_not_mem
          padding base physical hmem] at hpositive
      omega
  · intro hmem
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hmem
    rw [← heq, uniformShiftedGeometricSpin_recover]
    exact (geometricSpin_positive_iff_mem_geometricSupport
      base physical source).2 hsource

private theorem filter_eq_of_agree_local {A : Type}
    (left right : A → Bool) :
    ∀ items : List A, (∀ item, item ∈ items → left item = right item) →
      items.filter left = items.filter right
  | [], _ => rfl
  | head :: tail, hagree => by
      have hhead := hagree head List.mem_cons_self
      have htail : ∀ item, item ∈ tail → left item = right item :=
        fun item hitem => hagree item (List.mem_cons_of_mem head hitem)
      simp only [List.filter_cons, hhead]
      rw [filter_eq_of_agree_local left right tail htail]

theorem excitedPlaquetteIds_uniformShiftTransportPhysical
    (padding base : Nat) (physical : EdgeLabelling) :
    excitedPlaquetteIds (uniformPaddedBase padding base)
        (uniformShiftTransportPhysical padding base physical) =
      uniformShiftCanonicalRoot padding base
        (excitedPlaquetteIds base physical) := by
  unfold excitedPlaquetteIds uniformShiftCanonicalRoot
    geometricSupportIds physicalFaceEdges
  apply filter_eq_of_agree_local
  intro targetId htarget
  have hlt := List.mem_range.mp htarget
  have htransport :
      uniformShiftTransportPhysical padding base physical targetId =
        uniformShiftedGeometricSpin padding base physical
          (boxPlaquetteAt (uniformPaddedBase padding base) targetId) := by
    unfold uniformShiftTransportPhysical
    rw [if_pos hlt]
  rw [htransport]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using
    (uniformShiftedGeometricSpin_positive_iff_mem
      padding base physical
      (boxPlaquetteAt (uniformPaddedBase padding base) targetId))

theorem uniformShiftTransportPhysical_mem_supportFiber
    {cutoff padding base : Nat} {support : List Nat}
    {physical : EdgeLabelling}
    (hphysical : physical ∈
      physicalLabellingsWithSupport cutoff base support) :
    uniformShiftTransportPhysical padding base physical ∈
      physicalLabellingsWithSupport cutoff
        (uniformPaddedBase padding base)
        (uniformShiftCanonicalRoot padding base support) := by
  have hparts := mem_physicalLabellingsWithSupport_iff.mp hphysical
  apply mem_physicalLabellingsWithSupport_iff.mpr
  constructor
  · exact uniformShiftTransportPhysical_mem_bounded hparts.1
  · rw [excitedPlaquetteIds_uniformShiftTransportPhysical, hparts.2]

def uniformShiftTransportedPhysicalFiber
    (cutoff padding base : Nat) (support : List Nat) :
    List EdgeLabelling :=
  (physicalLabellingsWithSupport cutoff base support).map
    (uniformShiftTransportPhysical padding base)

theorem uniformShiftTransportedPhysicalFiber_mem_target
    {cutoff padding base : Nat} {support : List Nat}
    {target : EdgeLabelling}
    (htarget : target ∈ uniformShiftTransportedPhysicalFiber
      cutoff padding base support) :
    target ∈ physicalLabellingsWithSupport cutoff
      (uniformPaddedBase padding base)
      (uniformShiftCanonicalRoot padding base support) := by
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp htarget
  exact uniformShiftTransportPhysical_mem_supportFiber hsource

theorem uniformShiftTransportedPhysicalFiber_nodup
    {cutoff padding base : Nat} (support : List Nat) :
    (uniformShiftTransportedPhysicalFiber
      cutoff padding base support).Nodup := by
  unfold uniformShiftTransportedPhysicalFiber
  apply nodup_map_of_injOn
    (uniformShiftTransportPhysical padding base)
    (physicalLabellingsWithSupport cutoff base support)
    (physicalLabellingsWithSupport_nodup cutoff base support)
  intro left hleft right hright heq
  exact uniformShiftTransportPhysical_injective_on
    (mem_physicalLabellingsWithSupport_iff.mp hleft).1
    (mem_physicalLabellingsWithSupport_iff.mp hright).1 heq

#print axioms uniformShiftVertex_injective
#print axioms uniformShiftVertex_addE
#print axioms edgesOf_uniformShiftPlaquette
#print axioms uniformShiftAdjacent
#print axioms uniformShiftConnected
#print axioms uniformShiftPlaquette_mem_padded_box
#print axioms uniformShiftCanonicalRoot_canonical
#print axioms uniformShiftCanonicalRoot_injective_on_canonical
#print axioms uniformShiftedGeometricSpin_recover
#print axioms uniformShiftTransportPhysical_mem_bounded
#print axioms uniformShiftTransportPhysical_injective_on
#print axioms excitedPlaquetteIds_uniformShiftTransportPhysical
#print axioms uniformShiftTransportedPhysicalFiber_nodup

end YMGap.Continuum.Z4UniformShiftPhysicalTransport
