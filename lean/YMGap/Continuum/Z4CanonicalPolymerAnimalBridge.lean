/-
# Canonical finite-box polymers as genuine Z4 lattice animals

The exact cutoff-one polymer partition is indexed by numerical plaquette
identifiers.  The bounded-degree lattice-animal count, however, is stated for
actual `Z4Plaq` supports.  This module supplies the missing constructive
bridge: it decodes every valid numerical identifier into the corresponding
finite-box plaquette, transports the exact shared-link chains to genuine
`z4Chain` adjacency chains, and packages every canonical polymer as a real
internally connected, duplicate-free Z4 lattice animal of the same size.
-/

import YMGap.Continuum.Z4CanonicalPolymerRange
import YMGap.Continuum.AdjSpanningBuild

namespace YMGap.Continuum.Z4CanonicalPolymerAnimalBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4PhysicalSurfaceComponents

/-! ## 1. Choice-free decoding of a numerical plaquette identifier -/

def fallbackPlaquette : Z4Plaq := (v0, .p01)

def boxPlaquetteAt (n i : Nat) : Z4Plaq :=
  (boxPlaquettes n).getD i fallbackPlaquette

private theorem enumerateFrom_getD_of_mem {A : Type}
    (fallback : A) (start : Nat) :
    ∀ {xs : List A} {i : Nat} {x : A},
      (i, x) ∈ enumerateFrom start xs →
        xs.getD (i - start) fallback = x
  | [], _, _, h => absurd h List.not_mem_nil
  | head :: tail, i, x, h => by
      simp only [enumerateFrom, List.mem_cons] at h
      rcases h with h | h
      · have hi : i = start := congrArg Prod.fst h
        have hx : x = head := congrArg Prod.snd h
        rw [hi, hx]
        simp only [Nat.sub_self, List.getD_cons_zero]
      · have hge : start + 1 ≤ i :=
          YMGap.Continuum.Z4UnitCubeEnumerationParity.enumerateFrom_index_ge h
        have ih := enumerateFrom_getD_of_mem fallback (start + 1) h
        have hidx : i - start = (i - (start + 1)) + 1 := by omega
        rw [hidx, List.getD_cons_succ]
        exact ih

theorem enumerate_getD_of_mem {A : Type} (fallback : A)
    {xs : List A} {i : Nat} {x : A}
    (h : (i, x) ∈ enumerate xs) : xs.getD i fallback = x := by
  have key := enumerateFrom_getD_of_mem fallback 0 h
  simpa only [Nat.sub_zero] using key

theorem boxPlaquetteAt_eq_of_enumerate
    {n i : Nat} {p : Z4Plaq}
    (h : (i, p) ∈ enumerate (boxPlaquettes n)) :
    boxPlaquetteAt n i = p :=
  enumerate_getD_of_mem fallbackPlaquette h

theorem physicalFaceId_lt {n i : Nat}
    (hi : i ∈ physicalFaceEdges n) : i < (boxPlaquettes n).length := by
  unfold physicalFaceEdges plaquetteEdgeCount at hi
  exact List.mem_range.mp hi

theorem boxPlaquetteAt_injective_on_physical
    {n i j : Nat}
    (hi : i ∈ physicalFaceEdges n)
    (hj : j ∈ physicalFaceEdges n)
    (heq : boxPlaquetteAt n i = boxPlaquetteAt n j) : i = j := by
  have hi' := physicalFaceId_lt hi
  have hj' := physicalFaceId_lt hj
  apply List.getElem?_inj hi' (YMGap.Continuum.Z4UnitCubeEnumerationParity.boxPlaquettes_nodup n)
  rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj']
  have hleft := List.getElem_eq_getD (l := boxPlaquettes n)
    (i := i) (h := hi') fallbackPlaquette
  have hright := List.getElem_eq_getD (l := boxPlaquettes n)
    (i := j) (h := hj') fallbackPlaquette
  change some ((boxPlaquettes n)[i]) = some ((boxPlaquettes n)[j])
  congr 1
  rw [hleft, hright]
  exact heq

/-! ## 2. A true numerical adjacency carries a genuine shared link -/

def shareListedPhysicalLinkWitness (n left right : Nat) :
    ∀ (links : List Z4Link),
      shareListedPhysicalLinkB n left right links = true →
        Σ' link : Z4Link,
          (link ∈ links) ×'
            (left ∈ incidentPlaqIds n link) ×'
              (right ∈ incidentPlaqIds n link)
  | [], h => by cases h
  | link :: rest, h => by
      by_cases hleft : left ∈ incidentPlaqIds n link
      · by_cases hright : right ∈ incidentPlaqIds n link
        · exact ⟨link, List.mem_cons_self, hleft, hright⟩
        · have hrest :
              shareListedPhysicalLinkB n left right rest = true := by
              simpa [shareListedPhysicalLinkB, hleft, hright] using h
          obtain ⟨found, hmem, hl, hr⟩ :=
            shareListedPhysicalLinkWitness n left right rest hrest
          exact ⟨found, List.mem_cons_of_mem link hmem, hl, hr⟩
      · have hrest :
            shareListedPhysicalLinkB n left right rest = true := by
            simpa [shareListedPhysicalLinkB, hleft] using h
        obtain ⟨found, hmem, hl, hr⟩ :=
          shareListedPhysicalLinkWitness n left right rest hrest
        exact ⟨found, List.mem_cons_of_mem link hmem, hl, hr⟩

def decodeIncidentPlaqId {n i : Nat} {link : Z4Link}
    (hi : i ∈ incidentPlaqIds n link) :
    Σ' p : Z4Plaq,
      ((i, p) ∈ enumerate (boxPlaquettes n)) ×'
        (link ∈ edgesOf p) := by
  unfold incidentPlaqIds at hi
  obtain ⟨indexed, hindexed, hid⟩ :=
    decodeMapMember Prod.fst
      ((enumerate (boxPlaquettes n)).filter
        (fun ip => decide (link ∈ edgesOf ip.2))) i hi
  obtain ⟨j, p⟩ := indexed
  have hpair : (j, p) ∈ enumerate (boxPlaquettes n) :=
    (List.mem_filter.mp hindexed).1
  have hedge : link ∈ edgesOf p := by
    exact of_decide_eq_true (List.mem_filter.mp hindexed).2
  dsimp only at hid
  subst j
  exact ⟨p, hpair, hedge⟩

def actualAdjacentOfFaceLinkAdjacent
    {n left right : Nat}
    (hadj : faceLinkAdjacentB n left right = true) :
    z4Chain.toLattice.Adjacent
      (boxPlaquetteAt n left) (boxPlaquetteAt n right) := by
  unfold faceLinkAdjacentB at hadj
  obtain ⟨link, _, hleft, hright⟩ :=
    shareListedPhysicalLinkWitness n left right (distinctBoxLinks n) hadj
  obtain ⟨leftPlaq, hleftEnum, hleftEdge⟩ := decodeIncidentPlaqId hleft
  obtain ⟨rightPlaq, hrightEnum, hrightEdge⟩ := decodeIncidentPlaqId hright
  have hleftEq : boxPlaquetteAt n left = leftPlaq :=
    boxPlaquetteAt_eq_of_enumerate hleftEnum
  have hrightEq : boxPlaquetteAt n right = rightPlaq :=
    boxPlaquetteAt_eq_of_enumerate hrightEnum
  refine {
    link := link
    on_p := ?_
    on_q := ?_
  }
  · change z4Boundary (boxPlaquetteAt n left) link = true
    rw [hleftEq]
    simpa only [z4Boundary, decide_eq_true_eq] using hleftEdge
  · change z4Boundary (boxPlaquetteAt n right) link = true
    rw [hrightEq]
    simpa only [z4Boundary, decide_eq_true_eq] using hrightEdge

/-! ## 3. Transporting numerical internal chains -/

def geometricPolymer (n : Nat) (support : List Nat) :
    Polymer z4Chain.toLattice :=
  support.map (boxPlaquetteAt n)

def numericalChainToGeometric
    {n : Nat} {support : List Nat} :
    {left right : Nat} →
      YMGap.Continuum.FiniteBoolGraphComponents.ChainIn
        (faceLinkAdjacentB n) support left right →
        left ∈ support →
          ChainIn z4Chain.toLattice (geometricPolymer n support)
            (boxPlaquetteAt n left) (boxPlaquetteAt n right)
  | _, _, YMGap.Continuum.FiniteBoolGraphComponents.ChainIn.refl _, _ =>
      ChainIn.refl _
  | _left, _right,
      YMGap.Continuum.FiniteBoolGraphComponents.ChainIn.step
        (b := next) hadj hnext rest, _hleft =>
      ChainIn.step
        (actualAdjacentOfFaceLinkAdjacent hadj)
        (List.mem_map.mpr ⟨next, hnext, rfl⟩)
        (numericalChainToGeometric rest hnext)

def numericalConnectedToGeometric
    {n : Nat} {support : List Nat}
    (hconnected :
      YMGap.Continuum.FiniteBoolGraphComponents.InternallyConnected
        (faceLinkAdjacentB n) support) :
    connectedIn (geometricPolymer n support) := by
  intro leftPlaq rightPlaq hleftPlaq hrightPlaq
  obtain ⟨left, hleft, hleftEq⟩ :=
    decodeMapMember (boxPlaquetteAt n) support leftPlaq hleftPlaq
  obtain ⟨right, hright, hrightEq⟩ :=
    decodeMapMember (boxPlaquetteAt n) support rightPlaq hrightPlaq
  have chain := numericalChainToGeometric
    (hconnected left right hleft hright) hleft
  rw [hleftEq, hrightEq] at chain
  exact chain

theorem geometricPolymer_nodup
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    (geometricPolymer n support).Nodup := by
  have hsupport' : support ∈ sublists (physicalFaceEdges n) := hsupport
  have hnodup : support.Nodup :=
    Z4CanonicalPolymerRange.nodup_of_mem_sublists
      (physicalFaceEdges n) support (physicalFaceEdges_nodup n) hsupport'
  apply nodup_map_of_injOn (boxPlaquetteAt n) support hnodup
  intro left hleft right hright heq
  exact boxPlaquetteAt_injective_on_physical
    (mem_of_mem_sublists (physicalFaceEdges n) support hsupport'
      left hleft)
    (mem_of_mem_sublists (physicalFaceEdges n) support hsupport'
      right hright)
    heq

theorem canonicalSurfacePolymer_eq_of_geometric_sameSupport
    {n : Nat} {left right : List Nat}
    (hleft : left ∈ canonicalSurfacePolymers n)
    (hright : right ∈ canonicalSurfacePolymers n)
    (hsupport : sameSupport (geometricPolymer n left)
      (geometricPolymer n right)) :
    left = right := by
  have hleftSub : left ∈ sublists (physicalFaceEdges n) :=
    canonicalSurfacePolymer_mem_faceSupports hleft
  have hrightSub : right ∈ sublists (physicalFaceEdges n) :=
    canonicalSurfacePolymer_mem_faceSupports hright
  apply sublists_eq_of_mem_iff (physicalFaceEdges n) left right
    (physicalFaceEdges_nodup n) hleftSub hrightSub
  intro face
  constructor
  · intro hface
    have hactual : boxPlaquetteAt n face ∈ geometricPolymer n left := by
      unfold geometricPolymer
      exact List.mem_map.mpr ⟨face, hface, rfl⟩
    have hrightActual := hsupport.1 _ hactual
    obtain ⟨rightFace, hrightFace, heq⟩ :=
      List.mem_map.mp hrightActual
    have hid : rightFace = face :=
      boxPlaquetteAt_injective_on_physical
        (mem_of_mem_sublists (physicalFaceEdges n) right hrightSub
          rightFace hrightFace)
        (mem_of_mem_sublists (physicalFaceEdges n) left hleftSub
          face hface)
        heq
    rw [← hid]
    exact hrightFace
  · intro hface
    have hactual : boxPlaquetteAt n face ∈ geometricPolymer n right := by
      unfold geometricPolymer
      exact List.mem_map.mpr ⟨face, hface, rfl⟩
    have hleftActual := hsupport.2 _ hactual
    obtain ⟨leftFace, hleftFace, heq⟩ :=
      List.mem_map.mp hleftActual
    have hid : leftFace = face :=
      boxPlaquetteAt_injective_on_physical
        (mem_of_mem_sublists (physicalFaceEdges n) left hleftSub
          leftFace hleftFace)
        (mem_of_mem_sublists (physicalFaceEdges n) right hrightSub
          face hface)
        heq
    rw [← hid]
    exact hleftFace

theorem canonicalSurfacePolymerAnimalAt
    {n rootId : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n)
    (hroot : rootId ∈ polymer) :
    IsClusterThroughIn z4Chain (boxPlaquetteAt n rootId)
      polymer.length (geometricPolymer n polymer) := by
  have hsupport : polymer ∈ cutoffOneFaceSupports n :=
    canonicalSurfacePolymer_mem_faceSupports hpolymer
  unfold IsClusterThroughIn IsClusterThrough
  refine ⟨?_, ?_, geometricPolymer_nodup hsupport, ?_⟩
  · unfold Polymer.size geometricPolymer
    simp only [List.length_map]
  · unfold geometricPolymer
    exact List.mem_map.mpr ⟨rootId, hroot, rfl⟩
  · exact ⟨numericalConnectedToGeometric
      ((canonicalSurfacePolymers_allConnected n)
        polymer hpolymer)⟩

def canonicalSurfacePolymerAnimal
    {n : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    Σ' root : z4Chain.toLattice.Plaquette,
      IsClusterThroughIn z4Chain root polymer.length
        (geometricPolymer n polymer) := by
  obtain ⟨rootId, hrootId⟩ :=
    canonicalSurfacePolymers_allNonempty n polymer hpolymer
  exact ⟨boxPlaquetteAt n rootId,
    canonicalSurfacePolymerAnimalAt hpolymer hrootId⟩

theorem canonicalSurfacePolymer_overcountedAt
    {n rootId : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n)
    (hroot : rootId ∈ polymer) :
    ∃ Y,
      Y ∈ enumPolys z4Chain (boxPlaquetteAt n rootId) polymer.length ∧
        sameSupport (geometricPolymer n polymer) Y := by
  exact (ClusterCount4DProgress.z4ClusterCountBound_animal
      (boxPlaquetteAt n rootId)).2
    polymer.length (geometricPolymer n polymer)
    (canonicalSurfacePolymerAnimalAt hpolymer hroot)

theorem canonicalSurfacePolymer_overcounted
    {n : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    ∃ root Y,
      Y ∈ enumPolys z4Chain root polymer.length ∧
        sameSupport (geometricPolymer n polymer) Y := by
  obtain ⟨root, hanimal⟩ := canonicalSurfacePolymerAnimal hpolymer
  obtain ⟨Y, hY, hsupp⟩ :=
    (ClusterCount4DProgress.z4ClusterCountBound_animal root).2
      polymer.length (geometricPolymer n polymer) hanimal
  exact ⟨root, Y, hY, hsupp⟩

end YMGap.Continuum.Z4CanonicalPolymerAnimalBridge

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalPolymerAnimalBridge.boxPlaquetteAt_injective_on_physical
#print axioms YMGap.Continuum.Z4CanonicalPolymerAnimalBridge.actualAdjacentOfFaceLinkAdjacent
#print axioms YMGap.Continuum.Z4CanonicalPolymerAnimalBridge.numericalConnectedToGeometric
#print axioms YMGap.Continuum.Z4CanonicalPolymerAnimalBridge.geometricPolymer_nodup
#print axioms YMGap.Continuum.Z4CanonicalPolymerAnimalBridge.canonicalSurfacePolymer_eq_of_geometric_sameSupport
#print axioms YMGap.Continuum.Z4CanonicalPolymerAnimalBridge.canonicalSurfacePolymerAnimalAt
#print axioms YMGap.Continuum.Z4CanonicalPolymerAnimalBridge.canonicalSurfacePolymerAnimal
#print axioms YMGap.Continuum.Z4CanonicalPolymerAnimalBridge.canonicalSurfacePolymer_overcountedAt
#print axioms YMGap.Continuum.Z4CanonicalPolymerAnimalBridge.canonicalSurfacePolymer_overcounted
