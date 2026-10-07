/-
# Periodic Z4 torus plaquette lattice and the unconditional weighted KP on it

ADDITIVE.  **GROUP-BLIND PLUMBING** (U(1) rule: not gap evidence by itself).

* `torusBoundary N`: plaquette `p` carries link `ℓ` iff the base of `p` lies in the box
  `[0,N)⁴` and `ℓ ∈ torusEdgesOf N p` (four wrap-around links, `Z4TorusGeometry`).
  Off-box plaquettes carry no links, so they are isolated.
* `torusNbrs N p := (torusEdgesOf N p).flatMap (incidentPlaqs N)`: 4 links × 6 incident
  plaquettes.
* `torusNbrs_length`: the length is exactly 24 for every `N`.  For `N ≤ 2` the list has
  repetitions (wraparound collisions).  The count only needs the upper bound, so this is
  harmless.
* `torus_sound`: adjacency soundness, from `Z4TorusGeometry.filter_sub_incident`.
* `torusChain N : BddLattice` (D = 24), with count `(24+1)²` per step through the generic
  `AdjSpanningBuild.clusterCountBound_animal`.
* `torus_kp`: the unconditional weighted KP (`Z4PolymerKP.deg24_kp`) on the torus, with
  ε = 1/10000 and η = 1/2500.  Winding (non-contractible) polymers are included; there is
  no special treatment.
-/

import YMGap.Continuum.Z4PolymerKP
import YMGap.Continuum.Z4TorusGeometry

namespace YMGap.Continuum.Z4TorusPolymerKP

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.BddLatticeAnimal (BddLattice)
open YMGap.Continuum.PolymerModel (Lattice)
open YMGap.Continuum.SignedPolymerKP
open YMGap.Continuum.SizeWeightedPolymerKP
open YMGap.Continuum.Z4PolymerKP

def inBoxB (N : Nat) (v : Z4Vertex) : Bool :=
  decide (v.1 < N) && decide (v.2.1 < N) && decide (v.2.2.1 < N) && decide (v.2.2.2 < N)

theorem inBox_of (N : Nat) (v : Z4Vertex) (h : inBoxB N v = true) : InBox N v := by
  unfold inBoxB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1.1.1, of_decide_eq_true h.1.1.2, of_decide_eq_true h.1.2,
    of_decide_eq_true h.2⟩

def torusBoundary (N : Nat) (p : Z4Plaq) (ℓ : Z4Link) : Bool :=
  inBoxB N p.1 && decide (ℓ ∈ torusEdgesOf N p)

def torusLattice (N : Nat) : Lattice where
  Link := Z4Link
  Plaquette := Z4Plaq
  boundary := torusBoundary N

def torusNbrs (N : Nat) (p : Z4Plaq) : List Z4Plaq :=
  (torusEdgesOf N p).flatMap (incidentPlaqs N)

theorem torusNbrs_length (N : Nat) (p : Z4Plaq) : (torusNbrs N p).length = 24 := by
  unfold torusNbrs torusEdgesOf
  rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_cons,
    List.flatMap_nil, List.length_append, List.length_append, List.length_append,
    List.length_append, incidentPlaqs_length, incidentPlaqs_length, incidentPlaqs_length,
    incidentPlaqs_length]
  rfl

theorem torus_sound (N : Nat) (p q : Z4Plaq) (ℓ : Z4Link)
    (hp : torusBoundary N p ℓ = true) (hq : torusBoundary N q ℓ = true) :
    q ∈ torusNbrs N p := by
  unfold torusBoundary at hp hq
  rw [Bool.and_eq_true] at hp hq
  have hpℓ : ℓ ∈ torusEdgesOf N p := of_decide_eq_true hp.2
  obtain ⟨w, P⟩ := q
  have hw : InBox N w := inBox_of N w hq.1
  have hmem : (w, P) ∈ (torusPlaquettes N).filter
      (fun x => decide (ℓ ∈ torusEdgesOf N x)) :=
    List.mem_filter.mpr ⟨(mem_torusPlaquettes N w P).mpr hw, hq.2⟩
  obtain ⟨v, μ⟩ := ℓ
  exact List.mem_flatMap.mpr ⟨(v, μ), hpℓ, filter_sub_incident (w, P) hmem⟩

/-- **The periodic Z4 torus plaquette `BddLattice`** (degree bound 24, every `N`). -/
def torusChain (N : Nat) : BddLattice where
  toLattice := torusLattice N
  decEq := inferInstanceAs (DecidableEq Z4Plaq)
  nbrs := torusNbrs N
  D := 24
  deg_le := fun p => Nat.le_of_eq (torusNbrs_length N p)
  adjacent_mem_nbrs := fun p q adj => torus_sound N p q adj.link adj.on_p adj.on_q

/-- **Torus cluster-count bound with the over-count guarantee** (K = 625). -/
def torusClusterCountBound_animal (N : Nat) (p : (torusChain N).toLattice.Plaquette) :=
  YMGap.Continuum.AdjSpanningBuild.clusterCountBound_animal (torusChain N) p

/-- **Unconditional weighted KP on the periodic torus (PROVED).** Every torus polymer
system (connected, duplicate-free, support-distinct plaquette animals of size `1..N'`,
incompatibility = sharing a plaquette, winding polymers included) with activity
`|z X| ≤ (1/10000)^{|X|}`. -/
theorem torus_kp (N : Nat) (B : Z4BoxGas (torusChain N)) (z : Poly (torusChain N) → Q')
    (hz1 : ∀ X, (0 : Q') ≤ z X + epsZ ^ sz X) :
    ((0 : Q') ≤ Xi z shareB B.polys ∧
      ∀ p b r, B.polys = p ++ b :: r →
        Xi z shareB (p ++ r) ≤ (1 + etaZ ^ sz b) * Xi z shareB B.polys) ∧
    (1 : Q') ≤ prodm (fun x => 1 + etaZ ^ sz x) B.polys * Xi z shareB B.polys :=
  deg24_kp rfl ((0, 0, 0, 0), Z4Plane.p01) B z hz1

end YMGap.Continuum.Z4TorusPolymerKP

#print axioms YMGap.Continuum.Z4TorusPolymerKP.torusNbrs_length
#print axioms YMGap.Continuum.Z4TorusPolymerKP.torus_sound
#print axioms YMGap.Continuum.Z4TorusPolymerKP.torusClusterCountBound_animal
#print axioms YMGap.Continuum.Z4TorusPolymerKP.torus_kp
