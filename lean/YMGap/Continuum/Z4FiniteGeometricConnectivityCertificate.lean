/-
# Finite spanning-order certificates for geometric plaquette connectivity

For a literal plaquette list, connectivity can be certified by ordering its
faces so that every head shares a boundary link with some face in its tail.
This file turns that finite Boolean certificate into the witness-bearing
`PolymerModel.connectedIn` type used by canonical surface polymers.
-/

import YMGap.Continuum.Z4CanonicalPolymerTransport

namespace YMGap.Continuum.Z4FiniteGeometricConnectivityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PolymerModel

/-- Decidable geometric adjacency: two plaquettes share at least one literal
boundary link. -/
def geometricFaceAdjacentB (left right : Z4Plaq) : Bool :=
  (edgesOf left).any (fun link => decide (link ∈ edgesOf right))

private def firstSharedLink (fallback : Z4Link) (right : Z4Plaq) :
    List Z4Link → Z4Link
  | [] => fallback
  | link :: rest =>
      if decide (link ∈ edgesOf right) then link
      else firstSharedLink fallback right rest

private theorem firstSharedLink_spec
    (fallback : Z4Link) (right : Z4Plaq) : ∀ links : List Z4Link,
    links.any (fun link => decide (link ∈ edgesOf right)) = true →
    firstSharedLink fallback right links ∈ links ∧
      firstSharedLink fallback right links ∈ edgesOf right
  | [], h => by cases h
  | link :: rest, h => by
      by_cases hlink : link ∈ edgesOf right
      · simp [firstSharedLink, hlink]
      · have hrest :
            rest.any (fun item => decide (item ∈ edgesOf right)) = true := by
          simpa [hlink] using h
        have hspec := firstSharedLink_spec fallback right rest hrest
        exact ⟨by
          simp only [firstSharedLink, decide_eq_false hlink]
          exact List.mem_cons_of_mem link hspec.1,
          by simpa only [firstSharedLink, decide_eq_false hlink] using hspec.2⟩

def actualAdjacent_of_geometricFaceAdjacentB
    {left right : Z4Plaq}
    (hadj : geometricFaceAdjacentB left right = true) :
    z4Chain.toLattice.Adjacent left right := by
  unfold geometricFaceAdjacentB at hadj
  let fallback : Z4Link := (left.1, (dirsOf left.2).1)
  let link := firstSharedLink fallback right (edgesOf left)
  have hspec := firstSharedLink_spec fallback right (edgesOf left) hadj
  refine { link := link, on_p := ?_, on_q := ?_ }
  · change z4Boundary left link = true
    exact decide_eq_true hspec.1
  · change z4Boundary right link = true
    exact decide_eq_true hspec.2

/-- The last face is a root.  Every earlier face must share a link with some
later face. -/
def tailBridgeConnectedB : List Z4Plaq → Bool
  | [] => false
  | [_] => true
  | head :: second :: rest =>
      (second :: rest).any (geometricFaceAdjacentB head) &&
        tailBridgeConnectedB (second :: rest)

private def firstAdjacentFace (fallback head : Z4Plaq) :
    List Z4Plaq → Z4Plaq
  | [] => fallback
  | plaquette :: rest =>
      if geometricFaceAdjacentB head plaquette then plaquette
      else firstAdjacentFace fallback head rest

private theorem firstAdjacentFace_spec
    (fallback head : Z4Plaq) : ∀ tail : List Z4Plaq,
    tail.any (geometricFaceAdjacentB head) = true →
    firstAdjacentFace fallback head tail ∈ tail ∧
      geometricFaceAdjacentB head
        (firstAdjacentFace fallback head tail) = true
  | [], h => by cases h
  | plaquette :: rest, h => by
      cases hcurrent : geometricFaceAdjacentB head plaquette with
      | true => simp [firstAdjacentFace, hcurrent]
      | false =>
          have hrest : rest.any (geometricFaceAdjacentB head) = true := by
            simpa [hcurrent] using h
          have hspec := firstAdjacentFace_spec fallback head rest hrest
          exact ⟨by
            simp only [firstAdjacentFace, hcurrent]
            exact List.mem_cons_of_mem plaquette hspec.1,
            by simpa only [firstAdjacentFace, hcurrent] using hspec.2⟩

private def chainInMono {small large : List Z4Plaq}
    (hsubset : ∀ plaquette, plaquette ∈ small → plaquette ∈ large) :
    {first last : Z4Plaq} →
      ChainIn z4Chain.toLattice small first last →
      ChainIn z4Chain.toLattice large first last
  | _, _, .refl plaquette => .refl plaquette
  | _, _, .step adjacent hnext rest =>
      .step adjacent (hsubset _ hnext) (chainInMono hsubset rest)

private def chainInTrans {support : List Z4Plaq} :
    {first middle last : Z4Plaq} →
      ChainIn z4Chain.toLattice support first middle →
      ChainIn z4Chain.toLattice support middle last →
      ChainIn z4Chain.toLattice support first last
  | _, _, _, .refl _, right => right
  | _, _, _, .step adjacent hnext rest, right =>
      .step adjacent hnext (chainInTrans rest right)

private def connectedIn_cons_of_tail_bridge
    {head parent : Z4Plaq} {tail : List Z4Plaq}
    (htail : connectedIn (L := z4Chain.toLattice) tail)
    (hparent : parent ∈ tail)
    (hadj : z4Chain.toLattice.Adjacent head parent) :
    connectedIn (L := z4Chain.toLattice) (head :: tail) := by
  intro first last hfirst hlast
  by_cases hfirstHead : first = head
  · subst first
    by_cases hlastHead : last = head
    · subst last
      exact @ChainIn.refl z4Chain.toLattice (head :: tail) head
    · have hlastTail : last ∈ tail :=
        (List.mem_cons.mp hlast).resolve_left hlastHead
      exact .step hadj (List.mem_cons_of_mem head hparent)
        (chainInMono
          (fun plaquette hplaquette =>
            List.mem_cons_of_mem head hplaquette)
          (htail parent last hparent hlastTail))
  · have hfirstTail : first ∈ tail :=
      (List.mem_cons.mp hfirst).resolve_left hfirstHead
    by_cases hlastHead : last = head
    · subst last
      exact chainInTrans
        (chainInMono
          (fun plaquette hplaquette =>
            List.mem_cons_of_mem head hplaquette)
          (htail first parent hfirstTail hparent))
        (.step
          (YMGap.Continuum.AdjSpanningBuild.adjacentSymm hadj)
          List.mem_cons_self
          (@ChainIn.refl z4Chain.toLattice (head :: tail) head))
    · have hlastTail : last ∈ tail :=
        (List.mem_cons.mp hlast).resolve_left hlastHead
      exact chainInMono
        (fun plaquette hplaquette =>
          List.mem_cons_of_mem head hplaquette)
        (htail first last hfirstTail hlastTail)

/-- A successful finite tail-bridge check produces actual witness-bearing
geometric connectivity. -/
def connectedIn_of_tailBridgeConnectedB : ∀ support : List Z4Plaq,
    tailBridgeConnectedB support = true →
    connectedIn (L := z4Chain.toLattice) support
  | [], h => by cases h
  | [plaquette], _ =>
      @connectedIn_singleton z4Chain.toLattice plaquette
  | head :: second :: rest, h => by
      change ((second :: rest).any (geometricFaceAdjacentB head) &&
        tailBridgeConnectedB (second :: rest)) = true at h
      have hparts := (Bool.and_eq_true _ _).mp h
      let parent := firstAdjacentFace second head (second :: rest)
      have hspec := firstAdjacentFace_spec second head
        (second :: rest) hparts.1
      exact connectedIn_cons_of_tail_bridge
        (connectedIn_of_tailBridgeConnectedB (second :: rest) hparts.2)
        hspec.1 (actualAdjacent_of_geometricFaceAdjacentB hspec.2)

#print axioms actualAdjacent_of_geometricFaceAdjacentB
#print axioms connectedIn_of_tailBridgeConnectedB

end YMGap.Continuum.Z4FiniteGeometricConnectivityCertificate
