/-
# A constructive cofinal exhaustion of the closed four-dimensional lattice

The exact compensated graph tower has an unbounded number of finite graph
edges, but its repeated one-edge subdivision does not approximate four-
dimensional space.  This file supplies the missing geometric side of that
comparison: explicit finite lists of plaquettes and boundary links in the
already constructed `z4Chain` lattice, monotone in the box scale and cofinal
among all corner-anchored Z4 plaquettes and links.

At scale `n` the base vertices have all four coordinates below `n`, every one
of the six coordinate planes is included, and the link list is the complete
flattened boundary of those plaquettes.  Exact list lengths are derived in
the kernel:

* vertices: `n^4`;
* plaquettes: `6 n^4`;
* boundary-link occurrences: `24 n^4`.

The lists may repeat a link shared by several plaquettes; that multiplicity
is intentional and the final formula counts boundary occurrences.  This is
a genuine finite cofinal 4D geometry.  It does not yet identify a box with a
compensated trivalent packet graph or transport the graph gap to these boxes.
-/

import YMGap.Continuum.ClusterCount4DProgress

namespace YMGap.Continuum.Z4FiniteBoxExhaustion

open YMGap.Continuum.ClusterCount4DProgress

def z4Planes : List Z4Plane :=
  [.p01, .p02, .p03, .p12, .p13, .p23]

def boxVertices (n : Nat) : List Z4Vertex :=
  (List.range n).flatMap fun a =>
    (List.range n).flatMap fun b =>
      (List.range n).flatMap fun c =>
        (List.range n).map fun d => (a, b, c, d)

def boxPlaquettes (n : Nat) : List Z4Plaq :=
  (boxVertices n).flatMap fun v =>
    z4Planes.map fun P => (v, P)

/-- Boundary-link occurrences, with the multiplicity inherited from the
plaquette boundaries. -/
def boxLinks (n : Nat) : List Z4Link :=
  (boxPlaquettes n).flatMap edgesOf

theorem mem_boxVertices (a b c d n : Nat) :
    (a, b, c, d) ∈ boxVertices n ↔
      a < n ∧ b < n ∧ c < n ∧ d < n := by
  simp only [boxVertices, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a', ha', b', hb', c', hc', d', hd', heq⟩
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨ha', hb', hc', hd'⟩
  · rintro ⟨ha, hb, hc, hd⟩
    exact ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩

theorem mem_boxPlaquettes (p : Z4Plaq) (n : Nat) :
    p ∈ boxPlaquettes n ↔
      p.1.1 < n ∧ p.1.2.1 < n ∧ p.1.2.2.1 < n ∧
        p.1.2.2.2 < n := by
  obtain ⟨⟨a, b, c, d⟩, P⟩ := p
  cases P <;> simp [boxPlaquettes, z4Planes, mem_boxVertices]

theorem boxPlaquettes_mono {n m : Nat} (hnm : n ≤ m)
    {p : Z4Plaq} (hp : p ∈ boxPlaquettes n) :
    p ∈ boxPlaquettes m := by
  rw [mem_boxPlaquettes] at hp ⊢
  exact ⟨Nat.lt_of_lt_of_le hp.1 hnm,
    Nat.lt_of_lt_of_le hp.2.1 hnm,
    Nat.lt_of_lt_of_le hp.2.2.1 hnm,
    Nat.lt_of_lt_of_le hp.2.2.2 hnm⟩

/-- A closed stage at which the given plaquette has appeared. -/
def plaquetteStage (p : Z4Plaq) : Nat :=
  Nat.max p.1.1
    (Nat.max p.1.2.1 (Nat.max p.1.2.2.1 p.1.2.2.2)) + 1

theorem plaquette_mem_stage (p : Z4Plaq) :
    p ∈ boxPlaquettes (plaquetteStage p) := by
  obtain ⟨⟨a, b, c, d⟩, P⟩ := p
  rw [mem_boxPlaquettes]
  unfold plaquetteStage
  exact
    ⟨Nat.lt_succ_of_le (Nat.le_max_left _ _),
      Nat.lt_succ_of_le
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)),
      Nat.lt_succ_of_le
        (Nat.le_trans
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
          (Nat.le_max_right _ _)),
      Nat.lt_succ_of_le
        (Nat.le_trans
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
          (Nat.le_max_right _ _))⟩

theorem boundary_mem_boxLinks {n : Nat} {p : Z4Plaq}
    (hp : p ∈ boxPlaquettes n) {ell : Z4Link} (hell : ell ∈ edgesOf p) :
    ell ∈ boxLinks n := by
  unfold boxLinks
  exact List.mem_flatMap.mpr ⟨p, hp, hell⟩

theorem boxLinks_mono {n m : Nat} (hnm : n ≤ m)
    {ell : Z4Link} (hell : ell ∈ boxLinks n) :
    ell ∈ boxLinks m := by
  unfold boxLinks at hell ⊢
  rcases List.mem_flatMap.mp hell with ⟨p, hp, hboundary⟩
  exact List.mem_flatMap.mpr
    ⟨p, boxPlaquettes_mono hnm hp, hboundary⟩

/-- A canonical plaquette carrying any given positive-direction link. -/
def linkCarrierPlaquette : Z4Link → Z4Plaq
  | (u, .x0) => (u, .p01)
  | (u, .x1) => (u, .p01)
  | (u, .x2) => (u, .p02)
  | (u, .x3) => (u, .p03)

theorem link_mem_carrier_boundary (ell : Z4Link) :
    ell ∈ edgesOf (linkCarrierPlaquette ell) := by
  obtain ⟨u, d⟩ := ell
  cases d <;> simp [linkCarrierPlaquette, edgesOf, dirsOf]

theorem link_mem_some_box (ell : Z4Link) :
    ell ∈ boxLinks (plaquetteStage (linkCarrierPlaquette ell)) :=
  boundary_mem_boxLinks (plaquette_mem_stage (linkCarrierPlaquette ell))
    (link_mem_carrier_boundary ell)

private theorem length_flatMap_fixed {α β : Type} (xs : List α)
    (f : α → List β) (k : Nat) (h : ∀ x, (f x).length = k) :
    (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        h, ih, Nat.succ_mul]
      omega

theorem boxVertices_length (n : Nat) :
    (boxVertices n).length = n * n * n * n := by
  unfold boxVertices
  have h1 : ∀ (a b c : Nat),
      ((List.range n).map fun d => (a, b, c, d)).length = n := by
    intros
    simp
  have h2 : ∀ (a b : Nat),
      ((List.range n).flatMap fun c =>
        (List.range n).map fun d => (a, b, c, d)).length = n * n := by
    intro a b
    simpa only [List.length_range] using
      (length_flatMap_fixed (List.range n)
        (fun c => (List.range n).map fun d => (a, b, c, d)) n (h1 a b))
  have h3 : ∀ (a : Nat),
      ((List.range n).flatMap fun b =>
        (List.range n).flatMap fun c =>
          (List.range n).map fun d => (a, b, c, d)).length =
        n * (n * n) := by
    intro a
    simpa only [List.length_range] using
      (length_flatMap_fixed (List.range n)
        (fun b => (List.range n).flatMap fun c =>
          (List.range n).map fun d => (a, b, c, d)) (n * n) (h2 a))
  have h4 := length_flatMap_fixed (List.range n)
    (fun a => (List.range n).flatMap fun b =>
      (List.range n).flatMap fun c =>
        (List.range n).map fun d => (a, b, c, d)) (n * (n * n)) h3
  simpa only [List.length_range, Nat.mul_assoc] using h4

theorem boxPlaquettes_length (n : Nat) :
    (boxPlaquettes n).length = (n * n * n * n) * 6 := by
  unfold boxPlaquettes
  calc
    ((boxVertices n).flatMap fun v => z4Planes.map fun P => (v, P)).length =
        (boxVertices n).length * 6 := by
          apply length_flatMap_fixed
          intro v
          simp [z4Planes]
    _ = (n * n * n * n) * 6 := by rw [boxVertices_length]

theorem boxLinks_length (n : Nat) :
    (boxLinks n).length = ((n * n * n * n) * 6) * 4 := by
  unfold boxLinks
  calc
    ((boxPlaquettes n).flatMap edgesOf).length =
        (boxPlaquettes n).length * 4 := by
          apply length_flatMap_fixed
          intro p
          rfl
    _ = ((n * n * n * n) * 6) * 4 := by rw [boxPlaquettes_length]

theorem boxPlaquetteCount_unbounded (bound : Nat) :
    ∃ n : Nat, bound ≤ (boxPlaquettes n).length := by
  let n := bound + 1
  have hn : 0 < n := by unfold n; omega
  have h1 : n ≤ n * n := Nat.le_mul_of_pos_right n hn
  have h2 : n * n ≤ (n * n) * n :=
    Nat.le_mul_of_pos_right (n * n) hn
  have h3 : (n * n) * n ≤ ((n * n) * n) * n :=
    Nat.le_mul_of_pos_right ((n * n) * n) hn
  have h4 : ((n * n) * n) * n ≤ (((n * n) * n) * n) * 6 :=
    Nat.le_mul_of_pos_right (((n * n) * n) * n) (by decide)
  refine ⟨n, ?_⟩
  rw [boxPlaquettes_length]
  exact Nat.le_trans (by unfold n; omega)
    (Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4)))

/-- Abstract finite cofinal Z4 geometry, recording monotonicity and closure
under plaquette boundary links. -/
structure CofinalFiniteZ4Exhaustion where
  plaquettes : Nat → List Z4Plaq
  links : Nat → List Z4Link
  plaquette_mono : ∀ {n m}, n ≤ m → ∀ {p},
    p ∈ plaquettes n → p ∈ plaquettes m
  link_mono : ∀ {n m}, n ≤ m → ∀ {ell},
    ell ∈ links n → ell ∈ links m
  boundary_closed : ∀ {n p ell}, p ∈ plaquettes n →
    ell ∈ edgesOf p → ell ∈ links n
  plaquette_cofinal : ∀ p, ∃ n, p ∈ plaquettes n
  link_cofinal : ∀ ell, ∃ n, ell ∈ links n

/-- The closed, explicit, and non-vacuous box exhaustion. -/
def z4BoxExhaustion : CofinalFiniteZ4Exhaustion where
  plaquettes := boxPlaquettes
  links := boxLinks
  plaquette_mono := fun hnm _ hp => boxPlaquettes_mono hnm hp
  link_mono := fun hnm _ hell => boxLinks_mono hnm hell
  boundary_closed := fun hp hell => boundary_mem_boxLinks hp hell
  plaquette_cofinal := fun p => ⟨plaquetteStage p, plaquette_mem_stage p⟩
  link_cofinal := fun ell =>
    ⟨plaquetteStage (linkCarrierPlaquette ell), link_mem_some_box ell⟩

theorem firstBox_has_six_plaquettes :
    (z4BoxExhaustion.plaquettes 1).length = 6 := by decide

theorem firstBox_has_twentyFour_boundary_occurrences :
    (z4BoxExhaustion.links 1).length = 24 := by decide

end YMGap.Continuum.Z4FiniteBoxExhaustion

#print axioms YMGap.Continuum.Z4FiniteBoxExhaustion.mem_boxPlaquettes
#print axioms YMGap.Continuum.Z4FiniteBoxExhaustion.boxPlaquettes_mono
#print axioms YMGap.Continuum.Z4FiniteBoxExhaustion.plaquette_mem_stage
#print axioms YMGap.Continuum.Z4FiniteBoxExhaustion.boundary_mem_boxLinks
#print axioms YMGap.Continuum.Z4FiniteBoxExhaustion.boxLinks_mono
#print axioms YMGap.Continuum.Z4FiniteBoxExhaustion.link_mem_some_box
#print axioms YMGap.Continuum.Z4FiniteBoxExhaustion.boxVertices_length
#print axioms YMGap.Continuum.Z4FiniteBoxExhaustion.boxPlaquettes_length
#print axioms YMGap.Continuum.Z4FiniteBoxExhaustion.boxLinks_length
#print axioms YMGap.Continuum.Z4FiniteBoxExhaustion.boxPlaquetteCount_unbounded
#print axioms YMGap.Continuum.Z4FiniteBoxExhaustion.z4BoxExhaustion
#print axioms YMGap.Continuum.Z4FiniteBoxExhaustion.firstBox_has_six_plaquettes
