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
        obtain ⟨y, hy, hyp⟩ := List.mem_map.mp hpMem
        obtain ⟨z, hz, hzq⟩ := List.mem_flatMap.mp hqMem
        obtain ⟨t, ht, htq⟩ := List.mem_map.mp hzq
        rw [← hyp, ← htq] at hpq
        have hxz : x = z := by injection hpq
        exact hp.1 (hxz ▸ hz)

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

theorem boxPlaquettes_nodup (n : Nat) : (boxPlaquettes n).Nodup := by
  unfold boxPlaquettes
  exact nodup_cartesian (boxVertices n) z4Planes
    (boxVertices_nodup n) z4Planes_nodup

theorem enumerateFrom_index_ge {a : Type} {start i : Nat} {x : a} :
    ∀ {xs : List a}, (i, x) ∈ enumerateFrom start xs → start ≤ i
  | [], h => by cases h
  | y :: ys, h => by
      simp only [enumerateFrom, List.mem_cons] at h
      rcases h with h | h
      · injection h with hi
        omega
      · have ht := enumerateFrom_index_ge h
        omega

theorem enumerateFrom_index_unique {a : Type} {start i : Nat} {x y : a} :
    ∀ {xs : List a},
      (i, x) ∈ enumerateFrom start xs →
      (i, y) ∈ enumerateFrom start xs → x = y
  | [], hx, _ => by cases hx
  | z :: zs, hx, hy => by
      simp only [enumerateFrom, List.mem_cons] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · injection hx with _ hzx
        injection hy with _ hzy
        exact hzx.trans hzy.symm
      · injection hx with hi _
        have hge := enumerateFrom_index_ge hy
        omega
      · injection hy with hi _
        have hge := enumerateFrom_index_ge hx
        omega
      · exact enumerateFrom_index_unique hx hy

theorem enumerate_index_unique {a : Type} {xs : List a}
    {i : Nat} {x y : a}
    (hx : (i, x) ∈ enumerate xs) (hy : (i, y) ∈ enumerate xs) : x = y :=
  enumerateFrom_index_unique hx hy

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
  | x :: xs => by
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
        simp only [decide_eq_true_eq, hi, hp]
      · have hp : p ∉ unitCubeSurface := by
          intro hp
          exact hi (hiff.mpr hp)
        simp only [decide_eq_false_iff_not, hi, hp]
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

private def occurrences {a : Type} [DecidableEq a] (x : a) :
    List a → Nat
  | [] => 0
  | y :: ys => (if y = x then 1 else 0) + occurrences x ys

private theorem count_eq_occurrences {a : Type} [DecidableEq a]
    (x : a) : ∀ xs : List a, xs.count x = occurrences x xs
  | [] => rfl
  | y :: ys => by
      rw [List.count_cons, occurrences, count_eq_occurrences x ys]
      by_cases hxy : y = x
      · subst y
        simp [Nat.add_comm]
      · simp [hxy, Nat.add_comm]

private theorem occurrences_eq_zero_of_not_mem {a : Type}
    [DecidableEq a] (x : a) :
    ∀ xs : List a, x ∉ xs → occurrences x xs = 0
  | [], _ => rfl
  | y :: ys, hnot => by
      simp only [List.mem_cons, not_or] at hnot
      have hyx : y ≠ x := fun h => hnot.1 h.symm
      rw [occurrences, if_neg hyx,
        occurrences_eq_zero_of_not_mem x ys hnot.2]

private theorem occurrences_eq_one_of_mem_nodup {a : Type}
    [DecidableEq a] (x : a) :
    ∀ xs : List a, xs.Nodup → x ∈ xs → occurrences x xs = 1
  | [], _, h => by cases h
  | y :: ys, hnd, hmem => by
      have hfresh := (List.nodup_cons.mp hnd).1
      have hrestNodup := (List.nodup_cons.mp hnd).2
      simp only [List.mem_cons] at hmem
      rcases hmem with hxy | htail
      · subst y
        have hzero : occurrences x ys = 0 :=
          occurrences_eq_zero_of_not_mem x ys hfresh
        simp [occurrences, hzero]
      · have hne : y ≠ x := by
          intro h
          subst y
          exact hfresh htail
        rw [occurrences, if_neg hne]
        simp only [Nat.zero_add]
        exact occurrences_eq_one_of_mem_nodup x ys hrestNodup htail

private theorem count_eq_one_of_mem_nodup {a : Type} [DecidableEq a]
    (x : a) {xs : List a} (hnd : xs.Nodup) (hmem : x ∈ xs) :
    xs.count x = 1 := by
  rw [count_eq_occurrences]
  exact occurrences_eq_one_of_mem_nodup x xs hnd hmem

private theorem nodup_mem_iff_length_eq {a : Type} [DecidableEq a]
    (xs ys : List a) (hxs : xs.Nodup) (hys : ys.Nodup)
    (hmem : ∀ x, x ∈ xs ↔ x ∈ ys) : xs.length = ys.length := by
  apply List.Perm.length_eq
  apply List.perm_iff_count.mpr
  intro x
  by_cases hx : x ∈ xs
  · have hy := (hmem x).mp hx
    rw [count_eq_one_of_mem_nodup x hxs hx,
      count_eq_one_of_mem_nodup x hys hy]
  · have hy : x ∉ ys := by
      intro hy
      exact hx ((hmem x).mpr hy)
    rw [List.count_eq_zero.mpr hx, List.count_eq_zero.mpr hy]

private theorem filter_length_eq_faceIncidenceCount (ell : Z4Link) :
    ∀ faces : List Z4Plaq,
      (faces.filter fun p => decide (ell ∈ edgesOf p)).length =
        faceIncidenceCount ell faces
  | [] => rfl
  | p :: rest => by
      by_cases hp : ell ∈ edgesOf p
      · simp [List.filter_cons, faceIncidenceCount, hp,
          filter_length_eq_faceIncidenceCount, Nat.add_comm]
      · simp [List.filter_cons, faceIncidenceCount, hp,
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
      faceIncidenceCount ell unitCubeSurface := by
    exact filter_length_eq_faceIncidenceCount ell unitCubeSurface
  exact hlength.trans hcubeLength

/-- The fully selected incident-ID count is even at every box scale that
contains the elementary cube. -/
theorem selectedIncidentIds_even {n : Nat} (hn : 2 ≤ n) (ell : Z4Link) :
    (((incidentPlaqIds n ell).filter fun i =>
        decide (i ∈ unitCubeSurfaceIds n)).length) % 2 = 0 := by
  rw [selectedIncidentIds_length_eq_selectedBoxFaces]
  rw [selectedBoxFaces_length_eq_faceIncidenceCount hn]
  exact unitCubeFaceIncidenceCount_even ell

end YMGap.Continuum.Z4UnitCubeEnumerationParity
