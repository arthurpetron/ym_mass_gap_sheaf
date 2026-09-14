/-
# Finite weighted incidence: closed boundaries have even face counts

Two explicit coordinate weights on lattice links have boundary parity
one on every plaquette, or just on spatial plaquettes, respectively.
Finite double counting transfers even link incidence to even total face
count and even spatial face count. Face lists may contain repetitions;
there is no topological, gauge-group or analytic hypothesis.
-/

import YMGap.Continuum.Z4UnitCubeIncidenceParity
import YMGap.Continuum.Z4SpatialDefectTemporalDecoder

namespace YMGap.Continuum.Z4WeightedIncidenceParity

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4SpatialDefectTemporalDecoder

def nsum {A : Type} (f : A → Nat) : List A → Nat
  | [] => 0
  | x::xs => f x+nsum f xs

private theorem nsum_congr {A : Type} (f g : A → Nat) : ∀ xs : List A,
    (∀ x, x ∈ xs → f x=g x) → nsum f xs=nsum g xs
  | [], _ => rfl
  | x::xs, h => by
    change f x+nsum f xs=g x+nsum g xs
    rw [h x List.mem_cons_self, nsum_congr f g xs (fun y hy => h y (List.mem_cons_of_mem x hy))]

private theorem nsum_add {A : Type} (f g : A → Nat) : ∀ xs : List A,
    nsum (fun x => f x+g x) xs=nsum f xs+nsum g xs
  | [] => rfl
  | x::xs => by
    have ih := nsum_add f g xs
    simp only [nsum]
    omega

private theorem nsum_zero {A : Type} : ∀ xs : List A, nsum (fun _ => 0) xs=0
  | [] => rfl
  | _::xs => by simpa only [nsum, Nat.zero_add] using nsum_zero xs

private theorem nsum_point {A : Type} [BEq A] [LawfulBEq A] [DecidableEq A] (point : A) (value : Nat) :
    ∀ xs : List A, xs.Nodup →
      nsum (fun x => if x=point then value else 0) xs = if point ∈ xs then value else 0
  | [], _ => rfl
  | x::xs, hn => by
    have ih := nsum_point point value xs (List.nodup_cons.mp hn).2
    by_cases he : x=point
    · subst x
      have hf := (List.nodup_cons.mp hn).1
      simp only [nsum, ih, hf, ↓reduceIte, List.mem_cons_self, Nat.add_zero]
    · by_cases hm : point ∈ xs
      · have hc : point ∈ x::xs := List.mem_cons_of_mem x hm
        simp only [nsum, ih, he, hm, hc, ↓reduceIte, Nat.zero_add]
      · have hc : point ∉ x::xs := fun h => (List.mem_cons.mp h).elim (fun h => he h.symm) hm
        simp only [nsum, ih, he, hm, hc, ↓reduceIte, Nat.zero_add]

private theorem nsum_restrict {A : Type} [BEq A] [LawfulBEq A] [DecidableEq A] (w : A → Nat)
    (ambient : List A) (ha : ambient.Nodup) : ∀ selected : List A,
    selected.Nodup → (∀ x, x ∈ selected → x ∈ ambient) →
      nsum (fun x => if x ∈ selected then w x else 0) ambient = nsum w selected
  | [], _, _ => by simpa only [List.not_mem_nil, ↓reduceIte] using nsum_zero ambient
  | x::xs, hn, hs => by
    have hf := (List.nodup_cons.mp hn).1
    have he := nsum_congr (fun y => if y ∈ x::xs then w y else 0)
      (fun y => (if y=x then w x else 0)+(if y ∈ xs then w y else 0)) ambient (by
        intro y _
        by_cases hy : y=x
        · subst y
          simp only [List.mem_cons_self, hf, ↓reduceIte, Nat.add_zero]
        · by_cases hm : y ∈ xs
          · have hc : y ∈ x::xs := List.mem_cons_of_mem x hm
            simp only [hy, hm, hc, ↓reduceIte, Nat.zero_add]
          · have hc : y ∉ x::xs := fun h => (List.mem_cons.mp h).elim hy hm
            simp only [hy, hm, hc, ↓reduceIte, Nat.zero_add])
    rw [nsum_add, nsum_point x (w x) ambient ha, if_pos (hs x List.mem_cons_self),
      nsum_restrict w ambient ha xs (List.nodup_cons.mp hn).2
        (fun y hy => hs y (List.mem_cons_of_mem x hy))] at he
    exact he

theorem weighted_incidence (w : Z4Link → Nat) (links : List Z4Link) (hn : links.Nodup) :
    ∀ faces : List Z4Plaq, (∀ face, face ∈ faces → ∀ link, link ∈ edgesOf face → link ∈ links) →
      nsum (fun link => w link*faceIncidenceCount link faces) links =
        nsum (fun face => nsum w (edgesOf face)) faces
  | [], _ => by simpa only [faceIncidenceCount, Nat.mul_zero] using nsum_zero links
  | face::faces, hp => by
    have he := nsum_congr (fun link => w link*faceIncidenceCount link (face::faces))
      (fun link => (if link ∈ edgesOf face then w link else 0)+w link*faceIncidenceCount link faces)
      links (by
        intro link _
        by_cases h : link ∈ edgesOf face <;>
          simp only [faceIncidenceCount, h, ↓reduceIte, Nat.mul_add, Nat.mul_one, Nat.mul_zero])
    rw [nsum_add] at he
    have hh := nsum_restrict w links hn (edgesOf face) (edgesOf_nodup face) (hp face List.mem_cons_self)
    have ht := weighted_incidence w links hn faces (fun f hf => hp f (List.mem_cons_of_mem face hf))
    exact he.trans ((congrArg (fun n => n+nsum (fun link => w link*faceIncidenceCount link faces) links) hh).trans
      (congrArg (fun n => nsum w (edgesOf face)+n) ht))

private theorem nsum_even {A : Type} (f : A → Nat) : ∀ xs : List A,
    (∀ x, x ∈ xs → f x % 2=0) → nsum f xs % 2=0
  | [], _ => rfl
  | x::xs, h => by
    have hh := h x List.mem_cons_self
    have ht := nsum_even f xs (fun y hy => h y (List.mem_cons_of_mem x hy))
    change (f x+nsum f xs)%2=0
    omega

theorem closed_weighted_even (w : Z4Link → Nat) (links : List Z4Link) (hn : links.Nodup)
    (faces : List Z4Plaq)
    (hp : ∀ face, face ∈ faces → ∀ link, link ∈ edgesOf face → link ∈ links)
    (he : ∀ link, link ∈ links → faceIncidenceCount link faces % 2=0) :
    nsum (fun face => nsum w (edgesOf face)) faces % 2=0 := by
  rw [← weighted_incidence w links hn faces hp]
  exact nsum_even _ links (fun link hl => by rw [Nat.mul_mod, he link hl, Nat.mul_zero])

/-- A coordinate cochain with odd boundary sum on all six face orientations. -/
def allFaceWeight (link : Z4Link) : Nat :=
  match link.2 with
  | .x0 => 0
  | .x1 => link.1.1
  | .x2 => link.1.1+link.1.2.1
  | .x3 => link.1.1+link.1.2.1+link.1.2.2.1

/-- Remove the temporal-direction weight to detect just spatial faces. -/
def spatialFaceWeight (link : Z4Link) : Nat :=
  match link.2 with
  | .x0 => 0
  | .x1 => link.1.1
  | .x2 => link.1.1+link.1.2.1
  | .x3 => 0

theorem all_boundary_odd (face : Z4Plaq) : nsum allFaceWeight (edgesOf face)%2=1 := by
  rcases face with ⟨⟨a,b,c,t⟩,p⟩
  cases p <;> simp only [edgesOf, dirsOf, addE, nsum, allFaceWeight] <;> omega

theorem spatial_boundary_bit (face : Z4Plaq) :
    nsum spatialFaceWeight (edgesOf face)%2 = if (dirsOf face.2).2=Dir4.x3 then 0 else 1 := by
  rcases face with ⟨⟨a,b,c,t⟩,p⟩
  cases p <;> simp only [edgesOf, dirsOf, addE, nsum, spatialFaceWeight,
    reduceCtorEq, ↓reduceIte] <;> omega

private theorem nsum_all_parity : ∀ faces : List Z4Plaq,
    nsum (fun face => nsum allFaceWeight (edgesOf face)) faces % 2=faces.length%2
  | [] => rfl
  | face::faces => by
    have hh := all_boundary_odd face
    have ht := nsum_all_parity faces
    simp only [nsum, List.length_cons]
    omega

private theorem nsum_spatial_parity : ∀ faces : List Z4Plaq,
    nsum (fun face => nsum spatialFaceWeight (edgesOf face)) faces % 2=(spatialFaces faces).length%2
  | [] => rfl
  | face::faces => by
    have hh := spatial_boundary_bit face
    have ht := nsum_spatial_parity faces
    dsimp only [spatialFaces] at ht
    by_cases h : (dirsOf face.2).2=Dir4.x3
    · rw [if_pos h] at hh
      have hf : decide ((dirsOf face.2).2 ≠ Dir4.x3) = false := decide_eq_false (fun hn => hn h)
      simp only [nsum, spatialFaces, List.filter_cons, hf, Bool.false_eq_true, ↓reduceIte]
      omega
    · rw [if_neg h] at hh
      simp only [nsum, spatialFaces, List.filter_cons, decide_eq_true h, ↓reduceIte, List.length_cons]
      omega

theorem closed_face_counts_even (links : List Z4Link) (hn : links.Nodup) (faces : List Z4Plaq)
    (hp : ∀ face, face ∈ faces → ∀ link, link ∈ edgesOf face → link ∈ links)
    (he : ∀ link, link ∈ links → faceIncidenceCount link faces%2=0) :
    faces.length%2=0 ∧ (spatialFaces faces).length%2=0 := by
  constructor
  · rw [← nsum_all_parity]
    exact closed_weighted_even allFaceWeight links hn faces hp he
  · rw [← nsum_spatial_parity]
    exact closed_weighted_even spatialFaceWeight links hn faces hp he

end YMGap.Continuum.Z4WeightedIncidenceParity

#print axioms YMGap.Continuum.Z4WeightedIncidenceParity.nsum
#print axioms YMGap.Continuum.Z4WeightedIncidenceParity.weighted_incidence
#print axioms YMGap.Continuum.Z4WeightedIncidenceParity.closed_weighted_even
#print axioms YMGap.Continuum.Z4WeightedIncidenceParity.allFaceWeight
#print axioms YMGap.Continuum.Z4WeightedIncidenceParity.spatialFaceWeight
#print axioms YMGap.Continuum.Z4WeightedIncidenceParity.all_boundary_odd
#print axioms YMGap.Continuum.Z4WeightedIncidenceParity.spatial_boundary_bit
#print axioms YMGap.Continuum.Z4WeightedIncidenceParity.closed_face_counts_even
