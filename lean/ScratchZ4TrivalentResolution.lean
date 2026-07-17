import YMGap.Continuum.Z4FiniteBoxExhaustion
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath

namespace ScratchZ4TrivalentResolution

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

def enumerateFrom {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | i, x :: xs => (i, x) :: enumerateFrom (i + 1) xs

def enumerate {α : Type} (xs : List α) : List (Nat × α) :=
  enumerateFrom 0 xs

theorem enumerateFrom_length {α : Type} (i : Nat) : ∀ xs : List α,
    (enumerateFrom i xs).length = xs.length
  | [] => rfl
  | _ :: xs => by
      simp only [enumerateFrom, List.length_cons]
      rw [enumerateFrom_length (i + 1) xs]

theorem enumerate_length {α : Type} (xs : List α) :
    (enumerate xs).length = xs.length := enumerateFrom_length 0 xs

theorem exists_mem_enumerateFrom {α : Type} (start : Nat) :
    ∀ {xs : List α} {x : α}, x ∈ xs →
      ∃ i : Nat, (i, x) ∈ enumerateFrom start xs
  | [], _, h => by cases h
  | y :: ys, x, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | hy
      · exact ⟨start, List.mem_cons_self⟩
      · obtain ⟨i, hi⟩ := exists_mem_enumerateFrom (start + 1) hy
        exact ⟨i, List.mem_cons_of_mem _ hi⟩

theorem exists_mem_enumerate {α : Type} {xs : List α} {x : α}
    (h : x ∈ xs) : ∃ i : Nat, (i, x) ∈ enumerate xs :=
  exists_mem_enumerateFrom 0 h

def distinctBoxLinks (n : Nat) : List Z4Link :=
  (boxLinks n).eraseDups

def incidentPlaqIds (n : Nat) (ell : Z4Link) : List Nat :=
  ((enumerate (boxPlaquettes n)).filter fun ip => decide (ell ∈ edgesOf ip.2)).map
    Prod.fst

theorem mem_incidentPlaqIds {n : Nat} {ell : Z4Link} {i : Nat} :
    i ∈ incidentPlaqIds n ell ↔
      ∃ p : Z4Plaq, (i, p) ∈ enumerate (boxPlaquettes n) ∧
        ell ∈ edgesOf p := by
  simp [incidentPlaqIds]

def fuseChain (vacuum aux left right : Nat) : List Nat → List TrivalentVertex
  | [] => [(left, right, vacuum)]
  | [last] => [(left, right, last)]
  | next :: after :: rest =>
      (left, right, aux) :: fuseChain vacuum (aux + 1) aux next (after :: rest)

def fuseLabels (vacuum aux : Nat) : List Nat → List TrivalentVertex
  | [] => []
  | [edge] => [(edge, vacuum, vacuum)]
  | left :: right :: rest => fuseChain vacuum aux left right rest

def VertexContains (edge : Nat) (v : TrivalentVertex) : Prop :=
  edge = v.1 ∨ edge = v.2.1 ∨ edge = v.2.2

theorem fuseChain_contains_inputs (vacuum : Nat) :
    ∀ tail aux left right edge,
      edge ∈ left :: right :: tail →
        ∃ v, v ∈ fuseChain vacuum aux left right tail ∧
          VertexContains edge v
  | [], aux, left, right, edge, h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      refine ⟨(left, right, vacuum), by simp [fuseChain], ?_⟩
      rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  | [last], aux, left, right, edge, h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      refine ⟨(left, right, last), by simp [fuseChain], ?_⟩
      rcases h with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  | next :: after :: rest, aux, left, right, edge, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | rfl | htail
      · exact ⟨(edge, right, aux), by simp [fuseChain], Or.inl rfl⟩
      · exact ⟨(left, edge, aux), by simp [fuseChain],
          Or.inr (Or.inl rfl)⟩
      · have hrecursive : edge ∈ aux :: next :: after :: rest := by
          simp only [List.mem_cons]
          exact Or.inr htail
        obtain ⟨v, hv, hcontains⟩ :=
          fuseChain_contains_inputs vacuum (after :: rest) (aux + 1)
            aux next edge hrecursive
        exact ⟨v, by simp [fuseChain, hv], hcontains⟩

theorem fuseLabels_contains_inputs (vacuum aux edge : Nat) :
    ∀ {labels : List Nat}, edge ∈ labels →
      ∃ v, v ∈ fuseLabels vacuum aux labels ∧ VertexContains edge v
  | [], h => by cases h
  | [only], h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst only
      exact ⟨(edge, vacuum, vacuum), by simp [fuseLabels], Or.inl rfl⟩
  | left :: right :: rest, h => by
      exact fuseChain_contains_inputs vacuum rest aux left right edge h

def plaquetteEdgeCount (n : Nat) : Nat := (boxPlaquettes n).length

def linkBlockBase (n i : Nat) : Nat := plaquetteEdgeCount n + 8 * i

def linkBlockEdges (n i : Nat) : List Nat :=
  (List.range 8).map fun j => linkBlockBase n i + j

def resolutionEdges (n : Nat) : List Nat :=
  List.range (plaquetteEdgeCount n) ++
    (enumerate (distinctBoxLinks n)).flatMap fun indexed =>
      linkBlockEdges n indexed.1

def linkResolutionVertices (n i : Nat) (ell : Z4Link) :
    List TrivalentVertex :=
  fuseLabels (linkBlockBase n i) (linkBlockBase n i + 1)
    (incidentPlaqIds n ell)

def resolutionVertices (n : Nat) : List TrivalentVertex :=
  (enumerate (distinctBoxLinks n)).flatMap fun indexed =>
    linkResolutionVertices n indexed.1 indexed.2

theorem incidence_has_resolution_vertex {n : Nat} {p : Z4Plaq}
    (hp : p ∈ boxPlaquettes n) {ell : Z4Link} (hell : ell ∈ edgesOf p) :
    ∃ plaquetteId v,
      (plaquetteId, p) ∈ enumerate (boxPlaquettes n) ∧
      v ∈ resolutionVertices n ∧ VertexContains plaquetteId v := by
  obtain ⟨plaquetteId, hid⟩ := exists_mem_enumerate hp
  have hincident : plaquetteId ∈ incidentPlaqIds n ell :=
    mem_incidentPlaqIds.mpr ⟨p, hid, hell⟩
  have hellBox : ell ∈ boxLinks n := boundary_mem_boxLinks hp hell
  have hellDistinct : ell ∈ distinctBoxLinks n := by
    simpa [distinctBoxLinks] using hellBox
  obtain ⟨linkId, hlinkId⟩ := exists_mem_enumerate hellDistinct
  obtain ⟨v, hv, hcontains⟩ := fuseLabels_contains_inputs
    (linkBlockBase n linkId) (linkBlockBase n linkId + 1)
    plaquetteId hincident
  refine ⟨plaquetteId, v, hid, ?_, hcontains⟩
  unfold resolutionVertices
  exact List.mem_flatMap.mpr ⟨(linkId, ell), hlinkId, hv⟩

theorem length_flatMap_fixed {α β : Type} (xs : List α)
    (f : α → List β) (k : Nat) (h : ∀ x, (f x).length = k) :
    (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        h, ih, Nat.succ_mul]
      omega

theorem linkBlockEdges_length (n i : Nat) :
    (linkBlockEdges n i).length = 8 := by simp [linkBlockEdges]

theorem resolutionEdges_length (n : Nat) :
    (resolutionEdges n).length = plaquetteEdgeCount n +
      (distinctBoxLinks n).length * 8 := by
  unfold resolutionEdges
  rw [List.length_append, List.length_range]
  congr 1
  simpa only [enumerate_length] using
    (length_flatMap_fixed (enumerate (distinctBoxLinks n))
      (fun indexed => linkBlockEdges n indexed.1) 8
      (fun indexed => linkBlockEdges_length n indexed.1))

end ScratchZ4TrivalentResolution
