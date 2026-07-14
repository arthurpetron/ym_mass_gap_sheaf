/-
# Enumeration bridge for the elementary cube surface

The geometric cube boundary is expressed as plaquettes, whereas the finite
trivalent packet state selects numerical plaquette identifiers.  This file
proves constructively that these two descriptions have the same incidence
count in every box containing the cube.  In particular, the selected incident
identifier count is even at every scale `n >= 2`.
-/

import YMGap.Continuum.Z4UnitCubeIncidenceParity
import YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

namespace YMGap.Continuum.Z4UnitCubeEnumerationParity

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry
open YMGap.Continuum.Z4UnitCubeIncidenceParity

private theorem range_nodup (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ k ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyk : y = k := List.mem_singleton.mp hy
      rw [hxy, hyk] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl k)

private theorem nodup_map_of_injective {a b : Type} (f : a → b)
    (hf : ∀ {x y}, f x = f y → x = y) :
    ∀ {xs : List a}, xs.Nodup → (xs.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
      have hp := List.nodup_cons.mp h
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_map_of_injective f hf hp.2⟩
      intro hmem
      obtain ⟨y, hy, heq⟩ := List.mem_map.mp hmem
      exact hp.1 ((hf heq) ▸ hy)

private theorem nodup_cartesian {a b : Type} (xs : List a) (ys : List b)
    (hxs : xs.Nodup) (hys : ys.Nodup) :
    (xs.flatMap (fun x => ys.map (fun y => (x, y)))).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
      have hp := List.nodup_cons.mp hxs
      simp only [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨?_, ih hp.2, ?_⟩
      · exact nodup_map_of_injective (fun y => (x, y))
          (fun h => by injection h) hys
      · intro p hpMem q hqMem hpq
        obtain ⟨y, _, hyp⟩ := List.mem_map.mp hpMem
        obtain ⟨z, hz, hzq⟩ := List.mem_flatMap.mp hqMem
        obtain ⟨_, _, htq⟩ := List.mem_map.mp hzq
        rw [← hyp, ← htq] at hpq
        have hxz : x = z := by injection hpq
        exact hp.1 (hxz ▸ hz)

/-- The coordinate-product vertex enumeration contains no duplicates. -/
theorem boxVertices_nodup (n : Nat) : (boxVertices n).Nodup := by
  have hr := range_nodup n
  have hcd := nodup_cartesian (List.range n) (List.range n) hr hr
  have hbcd := nodup_cartesian (List.range n)
    ((List.range n).flatMap fun c =>
      (List.range n).map fun d => (c, d)) hr hcd
  have habcd := nodup_cartesian (List.range n)
    ((List.range n).flatMap fun b =>
      (List.range n).flatMap fun c =>
        (List.range n).map fun d => (b, c, d)) hr (by
          simpa only [List.map_flatMap, List.map_map,
            Function.comp_apply] using hbcd)
  unfold boxVertices
  simpa only [List.map_flatMap, List.map_map,
    Function.comp_apply] using habcd

theorem z4Planes_nodup : z4Planes.Nodup := by decide

/-- The finite-box plaquette enumeration contains no duplicates. -/
theorem boxPlaquettes_nodup (n : Nat) : (boxPlaquettes n).Nodup := by
  unfold boxPlaquettes
  exact nodup_cartesian (boxVertices n) z4Planes
    (boxVertices_nodup n) z4Planes_nodup

theorem enumerateFrom_index_ge {a : Type} {start i : Nat} {x : a} :
    ∀ {xs : List a}, (i, x) ∈ enumerateFrom start xs → start ≤ i
  | [], h => by cases h
  | _ :: _, h => by
      simp only [enumerateFrom, List.mem_cons] at h
      rcases h with h | h
      · injection h with hi
        omega
      · have ht := enumerateFrom_index_ge h
        omega

/-- A numerical position in `enumerateFrom` identifies at most one value. -/
theorem enumerateFrom_index_unique {a : Type} {start i : Nat} {x y : a} :
    ∀ {xs : List a},
      (i, x) ∈ enumerateFrom start xs →
      (i, y) ∈ enumerateFrom start xs → x = y
  | [], hx, _ => by cases hx
  | _ :: _, hx, hy => by
      simp only [enumerateFrom, List.mem_cons] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · have hzx : x = _ := congrArg Prod.snd hx
        have hzy : y = _ := congrArg Prod.snd hy
        exact hzx.trans hzy.symm
      · have hi : i = start := congrArg Prod.fst hx
        have hge := enumerateFrom_index_ge hy
        rw [hi] at hge
        exact (Nat.not_succ_le_self start hge).elim
      · have hi : i = start := congrArg Prod.fst hy
        have hge := enumerateFrom_index_ge hx
        rw [hi] at hge
        exact (Nat.not_succ_le_self start hge).elim
      · exact enumerateFrom_index_unique hx hy

theorem enumerate_index_unique {a : Type} {xs : List a}
    {i : Nat} {x y : a}
    (hx : (i, x) ∈ enumerate xs) (hy : (i, y) ∈ enumerate xs) : x = y :=
  enumerateFrom_index_unique hx hy

/-- For an enumerated plaquette, membership of its identifier in the cube-ID
list is equivalent to membership of the plaquette in the geometric cube. -/
theorem mem_unitCubeSurfaceIds_iff_of_enumerate {n i : Nat} {p : Z4Plaq}
    (hip : (i, p) ∈ enumerate (boxPlaquettes n)) :
    i ∈ unitCubeSurfaceIds n ↔ p ∈ unitCubeSurface := by
  constructor
  · intro hi
    unfold unitCubeSurfaceIds at hi
    obtain ⟨⟨j, q⟩, hindexed, heq⟩ := List.mem_map.mp hi
    have hpair := (List.mem_filter.mp hindexed).1
    have hsurface : q ∈ unitCubeSurface := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp hindexed).2
    have hid : j = i := heq
    have hpEq : q = p := by
      apply enumerate_index_unique (i := i)
      · rw [hid] at hpair
        exact hpair
      · exact hip
    simpa only [hpEq] using hsurface
  · intro hp
    unfold unitCubeSurfaceIds
    apply List.mem_map.mpr
    refine ⟨(i, p), List.mem_filter.mpr ⟨hip, ?_⟩, rfl⟩
    simpa only [decide_eq_true_eq] using hp

theorem enumerateFrom_map_snd {a : Type} (start : Nat) :
    ∀ xs : List a, (enumerateFrom start xs).map Prod.snd = xs
  | [] => rfl
  | _ :: _ => by
      simp only [enumerateFrom, List.map_cons, enumerateFrom_map_snd]

theorem enumerate_map_snd {a : Type} (xs : List a) :
    (enumerate xs).map Prod.snd = xs := enumerateFrom_map_snd 0 xs

private theorem filter_eq_of_mem {a : Type} (p q : a → Bool) :
    ∀ xs : List a, (∀ x, x ∈ xs → p x = q x) →
      xs.filter p = xs.filter q
  | [], _ => rfl
  | x :: xs, h => by
      have hx := h x List.mem_cons_self
      have htail : ∀ y, y ∈ xs → p y = q y := by
        intro y hy
        exact h y (List.mem_cons_of_mem x hy)
      simp only [List.filter_cons, hx]
      rw [filter_eq_of_mem p q xs htail]

/-- The enumerated selected-ID intersection counts exactly the corresponding
selected physical plaquettes in the finite box. -/
theorem selectedIncidentIds_length_eq_selectedBoxFaces
    (n : Nat) (ell : Z4Link) :
    (((incidentPlaqIds n ell).filter fun i =>
        decide (i ∈ unitCubeSurfaceIds n)).length) =
      ((boxPlaquettes n).filter fun p =>
        decide (p ∈ unitCubeSurface) && decide (ell ∈ edgesOf p)).length := by
  unfold incidentPlaqIds
  rw [List.filter_map, List.filter_filter, List.length_map]
  let entries := enumerate (boxPlaquettes n)
  let leftPred : Nat × Z4Plaq → Bool := fun ip =>
    decide (ip.1 ∈ unitCubeSurfaceIds n) && decide (ell ∈ edgesOf ip.2)
  let rightPred : Nat × Z4Plaq → Bool := fun ip =>
    decide (ip.2 ∈ unitCubeSurface) && decide (ell ∈ edgesOf ip.2)
  have hfilter : entries.filter leftPred = entries.filter rightPred := by
    apply filter_eq_of_mem
    intro ip hip
    obtain ⟨i, p⟩ := ip
    have hiff := mem_unitCubeSurfaceIds_iff_of_enumerate
      (n := n) (i := i) (p := p) (by exact hip)
    have hdecide : decide (i ∈ unitCubeSurfaceIds n) =
        decide (p ∈ unitCubeSurface) := by
      by_cases hi : i ∈ unitCubeSurfaceIds n
      · have hp := hiff.mp hi
        simp only [hi, hp]
      · have hp : p ∉ unitCubeSurface := by
          intro hp
          exact hi (hiff.mpr hp)
        simp only [hi, hp]
    simp only [leftPred, rightPred, hdecide]
  change (entries.filter leftPred).length = _
  rw [hfilter]
  have hsnd := enumerate_map_snd (boxPlaquettes n)
  have hmapped : (entries.filter rightPred).map Prod.snd =
      (boxPlaquettes n).filter (fun p =>
        decide (p ∈ unitCubeSurface) && decide (ell ∈ edgesOf p)) := by
    let pred : Z4Plaq → Bool := fun p =>
      decide (p ∈ unitCubeSurface) && decide (ell ∈ edgesOf p)
    calc
      (entries.filter rightPred).map Prod.snd =
          (entries.filter (pred ∘ Prod.snd)).map Prod.snd := by
            rfl
      _ = (entries.map Prod.snd).filter pred :=
        (List.filter_map).symm
      _ = (boxPlaquettes n).filter pred := by rw [hsnd]
  rw [← hmapped, List.length_map]

private def remOne {a : Type} [DecidableEq a] (x : a) : List a → List a
  | [] => []
  | y :: ys => if y = x then ys else y :: remOne x ys

private theorem remOne_length {a : Type} [DecidableEq a] (x : a) :
    ∀ xs : List a, x ∈ xs → (remOne x xs).length + 1 = xs.length
  | [], h => absurd h List.not_mem_nil
  | y :: ys, h => by
      show (if y = x then ys else y :: remOne x ys).length + 1 =
        (y :: ys).length
      by_cases hyx : y = x
      · rw [if_pos hyx, List.length_cons]
      · rw [if_neg hyx, List.length_cons, List.length_cons]
        have htail : x ∈ ys := by
          rcases List.mem_cons.mp h with h | h
          · exact absurd h.symm hyx
          · exact h
        have ih := remOne_length x ys htail
        omega

private theorem mem_remOne {a : Type} [DecidableEq a] (x : a) :
    ∀ xs : List a, ∀ y : a, y ∈ xs → y ≠ x → y ∈ remOne x xs
  | [], _, h, _ => absurd h List.not_mem_nil
  | z :: zs, y, h, hyx => by
      show y ∈ (if z = x then zs else z :: remOne x zs)
      by_cases hzx : z = x
      · rw [if_pos hzx]
        rcases List.mem_cons.mp h with h | h
        · exact absurd (h.trans hzx) hyx
        · exact h
      · rw [if_neg hzx]
        rcases List.mem_cons.mp h with h | h
        · rw [h]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem_remOne x zs y h hyx)

private theorem nodup_subset_length_le {a : Type} [DecidableEq a] :
    ∀ (xs ys : List a), xs.Nodup →
      (∀ x, x ∈ xs → x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hnd, hsub => by
      have hx : x ∈ ys := hsub x List.mem_cons_self
      have hp := List.nodup_cons.mp hnd
      have htail : ∀ y, y ∈ xs → y ∈ remOne x ys := by
        intro y hy
        have hyx : y ≠ x := by
          intro h
          subst y
          exact hp.1 hy
        exact mem_remOne x ys y
          (hsub y (List.mem_cons_of_mem x hy)) hyx
      have ih := nodup_subset_length_le xs (remOne x ys) hp.2 htail
      have hlength := remOne_length x ys hx
      show xs.length + 1 ≤ ys.length
      omega

private theorem nodup_mem_iff_length_eq {a : Type} [DecidableEq a]
    (xs ys : List a) (hxs : xs.Nodup) (hys : ys.Nodup)
    (hmem : ∀ x, x ∈ xs ↔ x ∈ ys) : xs.length = ys.length := by
  apply Nat.le_antisymm
  · exact nodup_subset_length_le xs ys hxs
      (fun x hx => (hmem x).mp hx)
  · exact nodup_subset_length_le ys xs hys
      (fun x hx => (hmem x).mpr hx)

private theorem filter_length_eq_faceIncidenceCount (ell : Z4Link) :
    ∀ faces : List Z4Plaq,
      (faces.filter fun p => decide (ell ∈ edgesOf p)).length =
        faceIncidenceCount ell faces
  | [] => rfl
  | p :: rest => by
      by_cases hp : ell ∈ edgesOf p
      · simp [faceIncidenceCount, hp,
          filter_length_eq_faceIncidenceCount, Nat.add_comm]
      · simp [faceIncidenceCount, hp,
          filter_length_eq_faceIncidenceCount]

/-- Once the six cube faces occur in the box, the selected box-face count is
the intrinsic incidence count on the cube surface. -/
theorem selectedBoxFaces_length_eq_faceIncidenceCount
    {n : Nat} (hn : 2 ≤ n) (ell : Z4Link) :
    ((boxPlaquettes n).filter fun p =>
        decide (p ∈ unitCubeSurface) && decide (ell ∈ edgesOf p)).length =
      faceIncidenceCount ell unitCubeSurface := by
  let boxSelected := (boxPlaquettes n).filter fun p =>
    decide (p ∈ unitCubeSurface) && decide (ell ∈ edgesOf p)
  let cubeSelected := unitCubeSurface.filter fun p =>
    decide (ell ∈ edgesOf p)
  have hboxNodup : boxSelected.Nodup :=
    List.filter_sublist.nodup (boxPlaquettes_nodup n)
  have hcubeNodup : cubeSelected.Nodup :=
    List.filter_sublist.nodup unitCubeSurface_nodup
  have hmem : ∀ p, p ∈ boxSelected ↔ p ∈ cubeSelected := by
    intro p
    simp only [boxSelected, cubeSelected, List.mem_filter,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨_, hsurface, hincident⟩
      exact ⟨hsurface, hincident⟩
    · rintro ⟨hsurface, hincident⟩
      exact ⟨unitCubeSurface_mem_box hn hsurface,
        hsurface, hincident⟩
  have hlength := nodup_mem_iff_length_eq boxSelected cubeSelected
    hboxNodup hcubeNodup hmem
  have hcubeLength : cubeSelected.length =
      faceIncidenceCount ell unitCubeSurface :=
    filter_length_eq_faceIncidenceCount ell unitCubeSurface
  exact hlength.trans hcubeLength

/-- The fully selected incident-ID count is even at every box scale that
contains the elementary cube. -/
theorem selectedIncidentIds_even {n : Nat} (hn : 2 ≤ n) (ell : Z4Link) :
    (((incidentPlaqIds n ell).filter fun i =>
        decide (i ∈ unitCubeSurfaceIds n)).length) % 2 = 0 := by
  rw [selectedIncidentIds_length_eq_selectedBoxFaces]
  rw [selectedBoxFaces_length_eq_faceIncidenceCount hn]
  exact unitCubeFaceIncidenceCount_even ell

#print axioms boxVertices_nodup
#print axioms boxPlaquettes_nodup
#print axioms enumerateFrom_index_ge
#print axioms enumerateFrom_index_unique
#print axioms enumerate_index_unique
#print axioms mem_unitCubeSurfaceIds_iff_of_enumerate
#print axioms selectedIncidentIds_length_eq_selectedBoxFaces
#print axioms selectedBoxFaces_length_eq_faceIncidenceCount
#print axioms selectedIncidentIds_even

end YMGap.Continuum.Z4UnitCubeEnumerationParity
