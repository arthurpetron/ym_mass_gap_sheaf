/-
# Time slabs partition the torus (C11 gap closure)

ADDITIVE; proved finite lemmas, general `N` (choice-free).  For `0 < N`,
`r ≤ N`:

* `slabTimes_nodup`, `crossSection_nodup`, `slabVertices_nodup`;
* `slab_disjoint`: a vertex is not in both the slab `[s, s+r)` and its
  complement slab `[s+r, s+N)` (times mod `N`);
* `slab_cover`: every torus vertex is in one of them;
* `slab_partition_perm`: `slabVertices N s r ++ slabVertices N (s+r) (N−r)`
  is a permutation of `boxVertices N`.
-/

import YMGap.Continuum.TorusSlabInsertion
import YMGap.Continuum.TorusWilsonAction

namespace YMGap.Continuum.TorusSlabCover

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.TorusSlabInsertion
open YMGap.Continuum.TorusWilsonAction (nodup_map_on perm_of_nodup_mem)

theorem shift_key {N : Nat} (hN : 0 < N) (s : Nat) :
    s + (N - s % N) = N * (s / N + 1) := by
  have h1 := Nat.mod_add_div s N
  have h2 := Nat.mod_lt s hN
  rw [Nat.mul_succ]
  generalize N * (s / N) = M at h1 ⊢
  generalize s % N = q at h1 h2 ⊢
  omega

/-- Undo a time offset: `((s+y) % N + (N − s % N)) % N = y % N`. -/
theorem unshift {N : Nat} (hN : 0 < N) (s y : Nat) :
    ((s + y) % N + (N - s % N)) % N = y % N := by
  rw [Nat.mod_add_mod, show s + y + (N - s % N) = y + (s + (N - s % N)) by omega,
    shift_key hN s, Nat.add_mul_mod_self_left]

theorem shift_back {N : Nat} (hN : 0 < N) (s x : Nat) :
    (s + (x + (N - s % N)) % N) % N = x % N := by
  rw [Nat.add_mod_mod, show s + (x + (N - s % N)) = x + (s + (N - s % N)) by omega,
    shift_key hN s, Nat.add_mul_mod_self_left]

theorem slabTimes_nodup {N : Nat} (hN : 0 < N) (s : Nat) {r : Nat} (hr : r ≤ N) :
    (slabTimes N s r).Nodup := by
  unfold slabTimes
  refine nodup_map_on _ ?_ (range_nodup' r)
  intro j hj j' hj' h
  have e := congrArg (fun x => (x + (N - s % N)) % N) h
  simp only [unshift hN] at e
  rwa [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (List.mem_range.mp hj) hr),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (List.mem_range.mp hj') hr)] at e

theorem crossSection_nodup (N : Nat) : (crossSection N).Nodup := by
  unfold crossSection
  refine nodup_flatMap_tagged (fun z : Nat × Nat × Nat => z.1) _ ?_ ?_ (range_nodup' N)
  · intro b
    refine nodup_flatMap_tagged (fun z : Nat × Nat × Nat => z.2.1) _ ?_ ?_ (range_nodup' N)
    · intro c
      exact nodup_map_inj _ (fun _ _ h => by injection h with _ h; injection h) (range_nodup' N)
    · intro c z hz
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp hz; rfl
  · intro b z hz
    obtain ⟨c, _, hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hz; rfl

theorem slabVertices_nodup {N : Nat} (hN : 0 < N) (s : Nat) {r : Nat} (hr : r ≤ N) :
    (slabVertices N s r).Nodup := by
  unfold slabVertices
  exact nodup_flatMap_tagged (fun v : Z4Vertex => v.1) _
    (fun a => nodup_map_inj _ (fun _ _ h => by injection h) (crossSection_nodup N))
    (fun a v hv => by obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv; rfl)
    (slabTimes_nodup hN s hr)

/-- The slab and its complement slab are disjoint. -/
theorem slab_disjoint {N : Nat} (hN : 0 < N) (s : Nat) {r : Nat} (hr : r ≤ N)
    {v : Z4Vertex} (h1 : v ∈ slabVertices N s r)
    (h2 : v ∈ slabVertices N (s + r) (N - r)) : False := by
  obtain ⟨⟨j, hj, e1⟩, _⟩ := (mem_slabVertices N s r v).mp h1
  obtain ⟨⟨j', hj', e2⟩, _⟩ := (mem_slabVertices N (s + r) (N - r) v).mp h2
  rw [e1, Nat.add_assoc] at e2
  have e := congrArg (fun x => (x + (N - s % N)) % N) e2
  simp only [unshift hN] at e
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hj hr),
    Nat.mod_eq_of_lt (show r + j' < N by omega)] at e
  omega

/-- Every torus vertex lies in the slab or its complement slab. -/
theorem slab_cover {N : Nat} (hN : 0 < N) (s : Nat) {r : Nat} (hr : r ≤ N)
    {v : Z4Vertex} (hv : InBox N v) :
    v ∈ slabVertices N s r ∨ v ∈ slabVertices N (s + r) (N - r) := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  have hjN : (v.1 + (N - s % N)) % N < N := Nat.mod_lt _ hN
  have hsj : (s + (v.1 + (N - s % N)) % N) % N = v.1 := by
    rw [shift_back hN, Nat.mod_eq_of_lt h1]
  generalize (v.1 + (N - s % N)) % N = j at hjN hsj
  rcases Nat.lt_or_ge j r with hjr | hjr
  · exact Or.inl ((mem_slabVertices N s r v).mpr ⟨⟨j, hjr, hsj.symm⟩, h2, h3, h4⟩)
  · refine Or.inr ((mem_slabVertices N (s + r) (N - r) v).mpr
      ⟨⟨j - r, by omega, ?_⟩, h2, h3, h4⟩)
    rw [show s + r + (j - r) = s + j by omega, hsj]

/-- **Partition.** Slab ++ complement slab is a permutation of the torus vertices. -/
theorem slab_partition_perm {N : Nat} (hN : 0 < N) (s : Nat) {r : Nat} (hr : r ≤ N) :
    (slabVertices N s r ++ slabVertices N (s + r) (N - r)).Perm (boxVertices N) := by
  refine perm_of_nodup_mem ?_ (boxVertices_nodup' N) ?_
  · exact List.nodup_append.mpr ⟨slabVertices_nodup hN s hr,
      slabVertices_nodup hN (s + r) (Nat.sub_le N r),
      fun x hx y hy hxy => slab_disjoint hN s hr hx (hxy ▸ hy)⟩
  · intro x
    constructor
    · intro hx
      rcases List.mem_append.mp hx with h | h
      · exact (mem_boxVertices_iff N x).mpr (slab_inBox hN h)
      · exact (mem_boxVertices_iff N x).mpr (slab_inBox hN h)
    · intro hx
      rcases slab_cover hN s hr ((mem_boxVertices_iff N x).mp hx) with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ h

end YMGap.Continuum.TorusSlabCover
