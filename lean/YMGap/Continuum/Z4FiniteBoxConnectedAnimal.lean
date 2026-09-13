/-
# A constructed connected carrier for every finite plaquette box

The literal six-plane box is connected by shared links. Paths first change
plane at one vertex, then move a p01 anchor one coordinate at a time;
orthogonal moves use p02 or p03 as a two-step bridge. Every intermediate
face remains in the SAME finite box. The resulting rooted animal covers
all box-link occurrences and has the existing exact length 6*n^4.

This is geometric data for finite observable supports, not a counting or
analytic assumption. The box may include faces outside a physical slab;
the probe carrier only needs genuine global plaquette incidence.
-/

import YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
import YMGap.Continuum.Z4UnitCubeEnumerationParity

namespace YMGap.Continuum.Z4FiniteBoxConnectedAnimal

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4UnitCubeEnumerationParity
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open Dir4 Z4Plane

def originFace : Z4Plaq := ((0,0,0,0), p01)

def pathTrans {X : List Z4Plaq} : {a b c : Z4Plaq} →
    ChainIn z4Lattice X a b → ChainIn z4Lattice X b c → ChainIn z4Lattice X a c
  | _, _, _, .refl _, right => right
  | _, _, _, .step adj hb rest, right => .step adj hb (pathTrans rest right)

def pathReverse {X : List Z4Plaq} : {a b : Z4Plaq} →
    ChainIn z4Lattice X a b → a ∈ X → ChainIn z4Lattice X b a
  | _, _, .refl a, _ => .refl a
  | a, _, .step adj hb rest, ha =>
      pathTrans (pathReverse rest hb) (.step ⟨adj.link, adj.on_q, adj.on_p⟩ ha
        (ChainIn.refl (L := z4Lattice) a))

private def edge (p q : Z4Plaq) (link : Z4Link)
    (hp : link ∈ edgesOf p) (hq : link ∈ edgesOf q) : z4Lattice.Adjacent p q :=
  ⟨link, decide_eq_true hp, decide_eq_true hq⟩

theorem withPlane {n : Nat} {v : Z4Vertex} {P : Z4Plane}
    (h : (v,P) ∈ boxPlaquettes n) (Q : Z4Plane) : (v,Q) ∈ boxPlaquettes n :=
  (mem_boxPlaquettes (v,Q) n).mpr ((mem_boxPlaquettes (v,P) n).mp h)

def planeToAnchor {n : Nat} (v : Z4Vertex) (hv : (v,p01) ∈ boxPlaquettes n) :
    (P : Z4Plane) → ChainIn z4Lattice (boxPlaquettes n) (v,P) (v,p01)
  | p01 => .refl _
  | p02 => .step (edge _ _ (v,x0) (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf])) hv (.refl _)
  | p03 => .step (edge _ _ (v,x0) (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf])) hv (.refl _)
  | p12 => .step (edge _ _ (v,x1) (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf])) hv (.refl _)
  | p13 => .step (edge _ _ (v,x1) (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf])) hv (.refl _)
  | p23 => .step (edge (v,p23) (v,p02) (v,x2) (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf]))
      (withPlane hv p02)
      (.step (edge _ _ (v,x0) (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf])) hv (.refl _))

/-- All four coordinate directions use actual shared-link plaquette steps. -/
def anchorStep {n : Nat} (v : Z4Vertex) (dir : Dir4)
    (hv : (v,p01) ∈ boxPlaquettes n) (hw : (addE v dir,p01) ∈ boxPlaquettes n) :
    ChainIn z4Lattice (boxPlaquettes n) (v,p01) (addE v dir,p01) := by
  cases dir with
  | x0 => exact .step (edge _ _ (addE v x0,x1) (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf])) hw (.refl _)
  | x1 => exact .step (edge _ _ (addE v x1,x0) (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf])) hw (.refl _)
  | x2 =>
      exact pathTrans (pathReverse (planeToAnchor v hv p02) (withPlane hv p02))
        (.step (edge (v,p02) (addE v x2,p02) (addE v x2,x0)
          (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf]))
          (withPlane hw p02) (planeToAnchor _ hw p02))
  | x3 =>
      exact pathTrans (pathReverse (planeToAnchor v hv p03) (withPlane hv p03))
        (.step (edge (v,p03) (addE v x3,p03) (addE v x3,x0)
          (by simp [edgesOf, dirsOf]) (by simp [edgesOf, dirsOf]))
          (withPlane hw p03) (planeToAnchor _ hw p03))

private theorem face_mem (n a b c d : Nat) (ha : a<n) (hb : b<n) (hc : c<n) (hd : d<n) :
    ((a,b,c,d),p01) ∈ boxPlaquettes n := (mem_boxPlaquettes _ _).mpr ⟨ha,hb,hc,hd⟩

def originToAnchor (n : Nat) : (a b c d : Nat) → a<n → b<n → c<n → d<n →
    ChainIn z4Lattice (boxPlaquettes n) originFace ((a,b,c,d),p01)
  | 0,0,0,0,_,_,_,_ => .refl _
  | a+1,b,c,d,ha,hb,hc,hd => pathTrans
      (originToAnchor n a b c d (by omega) hb hc hd)
      (anchorStep (a,b,c,d) x0 (face_mem n a b c d (by omega) hb hc hd) (face_mem n (a+1) b c d ha hb hc hd))
  | 0,b+1,c,d,ha,hb,hc,hd => pathTrans
      (originToAnchor n 0 b c d ha (by omega) hc hd)
      (anchorStep (0,b,c,d) x1 (face_mem n 0 b c d ha (by omega) hc hd) (face_mem n 0 (b+1) c d ha hb hc hd))
  | 0,0,c+1,d,ha,hb,hc,hd => pathTrans
      (originToAnchor n 0 0 c d ha hb (by omega) hd)
      (anchorStep (0,0,c,d) x2 (face_mem n 0 0 c d ha hb (by omega) hd) (face_mem n 0 0 (c+1) d ha hb hc hd))
  | 0,0,0,d+1,ha,hb,hc,hd => pathTrans
      (originToAnchor n 0 0 0 d ha hb hc (by omega))
      (anchorStep (0,0,0,d) x3 (face_mem n 0 0 0 d ha hb hc (by omega)) (face_mem n 0 0 0 (d+1) ha hb hc hd))
termination_by a b c d => a+b+c+d
decreasing_by all_goals omega

def originToFace {n : Nat} (p : Z4Plaq) (hp : p ∈ boxPlaquettes n) :
    ChainIn z4Lattice (boxPlaquettes n) originFace p := by
  obtain ⟨⟨a,b,c,d⟩, P⟩ := p
  have hb := (mem_boxPlaquettes _ _).mp hp
  change a<n ∧ b<n ∧ c<n ∧ d<n at hb
  exact pathTrans (originToAnchor n a b c d hb.1 hb.2.1 hb.2.2.1 hb.2.2.2)
    (pathReverse (planeToAnchor (a,b,c,d) (withPlane hp p01) P) hp)

theorem origin_mem {n : Nat} (hn : 0<n) : originFace ∈ boxPlaquettes n :=
  face_mem n 0 0 0 0 hn hn hn hn

def boxConnected {n : Nat} (hn : 0<n) : connectedIn (L := z4Lattice) (boxPlaquettes n) :=
  fun a b ha hb => pathTrans (pathReverse (originToFace a ha) (origin_mem hn)) (originToFace b hb)

def boxAnimal (n : Nat) (hn : 0<n) : RootedConnectedAnimal z4Chain where
  root := originFace
  support := boxPlaquettes n
  root_mem := origin_mem hn
  support_nodup := boxPlaquettes_nodup n
  connected := boxConnected hn

def boxProbe (n : Nat) (hn : 0<n) : ProbeCarrier (boxLinks n) where
  animal := boxAnimal n hn
  covers := fun _ h => h

theorem boxAnimal_size (n : Nat) (hn : 0<n) :
    (boxAnimal n hn).support.length = (n*n*n*n)*6 := boxPlaquettes_length n

end YMGap.Continuum.Z4FiniteBoxConnectedAnimal

#print axioms YMGap.Continuum.Z4FiniteBoxConnectedAnimal.originFace
#print axioms YMGap.Continuum.Z4FiniteBoxConnectedAnimal.pathTrans
#print axioms YMGap.Continuum.Z4FiniteBoxConnectedAnimal.pathReverse
#print axioms YMGap.Continuum.Z4FiniteBoxConnectedAnimal.withPlane
#print axioms YMGap.Continuum.Z4FiniteBoxConnectedAnimal.planeToAnchor
#print axioms YMGap.Continuum.Z4FiniteBoxConnectedAnimal.anchorStep
#print axioms YMGap.Continuum.Z4FiniteBoxConnectedAnimal.originToAnchor
#print axioms YMGap.Continuum.Z4FiniteBoxConnectedAnimal.originToFace
#print axioms YMGap.Continuum.Z4FiniteBoxConnectedAnimal.origin_mem
#print axioms YMGap.Continuum.Z4FiniteBoxConnectedAnimal.boxConnected
#print axioms YMGap.Continuum.Z4FiniteBoxConnectedAnimal.boxAnimal
#print axioms YMGap.Continuum.Z4FiniteBoxConnectedAnimal.boxProbe
#print axioms YMGap.Continuum.Z4FiniteBoxConnectedAnimal.boxAnimal_size
