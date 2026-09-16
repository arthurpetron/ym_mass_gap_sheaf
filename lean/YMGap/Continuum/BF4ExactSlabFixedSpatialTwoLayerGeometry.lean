/-
# Two temporal layers at a fixed spatial cutoff and on one original carrier

All five face families are filtered from the SAME physical face-ID list.
The independent width restricts the three spatial BASE coordinates, using
the existing slab convention. The time window has three spatial slices and
two temporal layers. Its exact permutation and duplicate-freeness count the
middle spatial action once, without identifying the two endpoint slices.

This supplies finite geometry for an original common temporal sweep followed
by middle-block Haar integration. No operator composition, decay estimate,
or continuum conclusion is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFaceLinkLocality

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private def widthIds (extent width : Nat) : List Nat :=
  (slabPhysicalFaceEdges extent).filter (fun id =>
    let p := slabPlaquetteAt extent id
    decide (p.1.1 < width ∧ p.1.2.1 < width ∧ p.1.2.2.1 < width))

def spatialIds (extent width time : Nat) : List Nat :=
  (widthIds extent width).filter (fun id =>
    let p := slabPlaquetteAt extent id
    decide (p.1.2.2.2 = time ∧ (dirsOf p.2).2 ≠ Dir4.x3))

def temporalIds (extent width time : Nat) : List Nat :=
  (widthIds extent width).filter (fun id =>
    let p := slabPlaquetteAt extent id
    decide (p.1.2.2.2 = time ∧ (dirsOf p.2).2 = Dir4.x3))

/-- Literal boundary-complete time window, on the unchanged ambient IDs. -/
def windowIds (extent width start : Nat) : List Nat :=
  (widthIds extent width).filter (fun id =>
    let p := slabPlaquetteAt extent id
    decide (start ≤ p.1.2.2.2 ∧ plaquetteTimeAdmissible (start+2) p))

/-- The middle spatial slice is one list, between the two temporal layers. -/
def twoLayerIds (extent width start : Nat) : List Nat :=
  spatialIds extent width start ++ temporalIds extent width start ++
  spatialIds extent width (start+1) ++ temporalIds extent width (start+1) ++
  spatialIds extent width (start+2)

theorem spatialIds_mem_iff (extent width time id : Nat) :
    id ∈ spatialIds extent width time ↔
      id ∈ slabPhysicalFaceEdges extent ∧
      (slabPlaquetteAt extent id).1.1 < width ∧
      (slabPlaquetteAt extent id).1.2.1 < width ∧
      (slabPlaquetteAt extent id).1.2.2.1 < width ∧
      (slabPlaquetteAt extent id).1.2.2.2 = time ∧
      (dirsOf (slabPlaquetteAt extent id).2).2 ≠ Dir4.x3 := by
  simp only [spatialIds, widthIds, List.mem_filter, decide_eq_true_eq, and_assoc]

theorem temporalIds_mem_iff (extent width time id : Nat) :
    id ∈ temporalIds extent width time ↔
      id ∈ slabPhysicalFaceEdges extent ∧
      (slabPlaquetteAt extent id).1.1 < width ∧
      (slabPlaquetteAt extent id).1.2.1 < width ∧
      (slabPlaquetteAt extent id).1.2.2.1 < width ∧
      (slabPlaquetteAt extent id).1.2.2.2 = time ∧
      (dirsOf (slabPlaquetteAt extent id).2).2 = Dir4.x3 := by
  simp only [temporalIds, widthIds, List.mem_filter, decide_eq_true_eq, and_assoc]

theorem windowIds_mem_iff (extent width start id : Nat) :
    id ∈ windowIds extent width start ↔
      id ∈ slabPhysicalFaceEdges extent ∧
      (slabPlaquetteAt extent id).1.1 < width ∧
      (slabPlaquetteAt extent id).1.2.1 < width ∧
      (slabPlaquetteAt extent id).1.2.2.1 < width ∧
      start ≤ (slabPlaquetteAt extent id).1.2.2.2 ∧
      plaquetteTimeAdmissible (start+2) (slabPlaquetteAt extent id) := by
  simp only [windowIds, widthIds, List.mem_filter, decide_eq_true_eq, and_assoc]

private def phase (start : Nat) (p : Z4Plaq) : Nat :=
  if p.1.2.2.2 = start then
    if (dirsOf p.2).2 = Dir4.x3 then 1 else 0
  else if p.1.2.2.2 = start+1 then
    if (dirsOf p.2).2 = Dir4.x3 then 3 else 2
  else if p.1.2.2.2 = start+2 ∧ (dirsOf p.2).2 ≠ Dir4.x3 then 4 else 5

private theorem phase_pins (start : Nat) (p : Z4Plaq) :
    (phase start p = 0 ↔ p.1.2.2.2 = start ∧ (dirsOf p.2).2 ≠ Dir4.x3) ∧
    (phase start p = 1 ↔ p.1.2.2.2 = start ∧ (dirsOf p.2).2 = Dir4.x3) ∧
    (phase start p = 2 ↔ p.1.2.2.2 = start+1 ∧ (dirsOf p.2).2 ≠ Dir4.x3) ∧
    (phase start p = 3 ↔ p.1.2.2.2 = start+1 ∧ (dirsOf p.2).2 = Dir4.x3) ∧
    (phase start p = 4 ↔ p.1.2.2.2 = start+2 ∧ (dirsOf p.2).2 ≠ Dir4.x3) ∧
    (phase start p < 5 ↔ start ≤ p.1.2.2.2 ∧ plaquetteTimeAdmissible (start+2) p) := by
  obtain ⟨⟨a,b,c,time⟩,plane⟩ := p
  cases plane <;> simp only [phase, dirsOf, plaquetteTimeAdmissible,
    ne_eq, reduceCtorEq, not_false_eq_true, not_true_eq_false, if_true, if_false, and_true, and_false]
  all_goals
    by_cases h0 : time = start
    · simp only [if_pos h0]
      repeat' first | apply And.intro | apply Iff.intro | intro h
      all_goals first | exact False.elim h | exact True.intro | omega
    · simp only [if_neg h0]
      by_cases h1 : time = start+1
      · simp only [if_pos h1]
        repeat' first | apply And.intro | apply Iff.intro | intro h
        all_goals first | exact False.elim h | exact True.intro | omega
      · simp only [if_neg h1]
        by_cases h2 : time = start+2
        · try simp only [if_pos h2]
          repeat' first | apply And.intro | apply Iff.intro | intro h
          all_goals first | exact False.elim h | exact True.intro | omega
        · try simp only [if_neg h2]
          repeat' first | apply And.intro | apply Iff.intro | intro h
          all_goals first | exact False.elim h | exact True.intro | omega

private theorem five_partition (key : Nat → Nat) : ∀ ids : List Nat,
    ((ids.filter (fun j => decide (key j = 0))) ++
      (ids.filter (fun j => decide (key j = 1))) ++
      (ids.filter (fun j => decide (key j = 2))) ++
      (ids.filter (fun j => decide (key j = 3))) ++
      (ids.filter (fun j => decide (key j = 4)))).Perm
      (ids.filter (fun j => decide (key j < 5)))
  | [] => List.Perm.nil
  | j::ids => by
    have ih := five_partition key ids
    by_cases h0 : key j = 0
    · simpa [h0] using List.Perm.cons j ih
    by_cases h1 : key j = 1
    · have move := List.perm_middle (a := j)
        (l₁ := ids.filter (fun k => decide (key k = 0)))
        (l₂ := (ids.filter (fun k => decide (key k = 1))) ++
          (ids.filter (fun k => decide (key k = 2))) ++
          (ids.filter (fun k => decide (key k = 3))) ++
          (ids.filter (fun k => decide (key k = 4))))
      have hm := move.trans (by simpa only [List.append_assoc] using List.Perm.cons j ih)
      simpa [h1, List.append_assoc] using hm
    by_cases h2 : key j = 2
    · have move := List.perm_middle (a := j)
        (l₁ := (ids.filter (fun k => decide (key k = 0))) ++
          (ids.filter (fun k => decide (key k = 1))))
        (l₂ := (ids.filter (fun k => decide (key k = 2))) ++
          (ids.filter (fun k => decide (key k = 3))) ++
          (ids.filter (fun k => decide (key k = 4))))
      have hm := move.trans (by simpa only [List.append_assoc] using List.Perm.cons j ih)
      simpa [h2, List.append_assoc] using hm
    by_cases h3 : key j = 3
    · have move := List.perm_middle (a := j)
        (l₁ := (ids.filter (fun k => decide (key k = 0))) ++
          (ids.filter (fun k => decide (key k = 1))) ++
          (ids.filter (fun k => decide (key k = 2))))
        (l₂ := (ids.filter (fun k => decide (key k = 3))) ++
          (ids.filter (fun k => decide (key k = 4))))
      have hm := move.trans (by simpa only [List.append_assoc] using List.Perm.cons j ih)
      simpa [h3, List.append_assoc] using hm
    by_cases h4 : key j = 4
    · have move := List.perm_middle (a := j)
        (l₁ := (ids.filter (fun k => decide (key k = 0))) ++
          (ids.filter (fun k => decide (key k = 1))) ++
          (ids.filter (fun k => decide (key k = 2))) ++
          (ids.filter (fun k => decide (key k = 3))))
        (l₂ := ids.filter (fun k => decide (key k = 4)))
      have hm := move.trans (by simpa only [List.append_assoc] using List.Perm.cons j ih)
      simpa [h4, List.append_assoc] using hm
    have hn : ¬ key j < 5 := by omega
    simpa [h0,h1,h2,h3,h4,hn] using ih

/-- Exact completeness of the five classes, with no replacement action. -/
theorem twoLayerIds_perm_window (extent width start : Nat) :
    (twoLayerIds extent width start).Perm (windowIds extent width start) := by
  have h := five_partition (fun id => phase start (slabPlaquetteAt extent id)) (widthIds extent width)
  have h0 := fun id => (phase_pins start (slabPlaquetteAt extent id)).1
  have h1 := fun id => (phase_pins start (slabPlaquetteAt extent id)).2.1
  have h2 := fun id => (phase_pins start (slabPlaquetteAt extent id)).2.2.1
  have h3 := fun id => (phase_pins start (slabPlaquetteAt extent id)).2.2.2.1
  have h4 := fun id => (phase_pins start (slabPlaquetteAt extent id)).2.2.2.2.1
  have h5 := fun id => (phase_pins start (slabPlaquetteAt extent id)).2.2.2.2.2
  simpa only [h0,h1,h2,h3,h4,h5] using h

theorem windowIds_physical {extent width start id : Nat}
    (hi : id ∈ windowIds extent width start) : id ∈ slabPhysicalFaceEdges extent :=
  ((windowIds_mem_iff extent width start id).mp hi).1

private theorem range_nodup (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro a ha b hb he
      have hb' := List.mem_singleton.mp hb
      subst b
      subst a
      exact Nat.lt_irrefl n (List.mem_range.mp ha)

theorem windowIds_nodup (extent width start : Nat) : (windowIds extent width start).Nodup :=
  List.filter_sublist.nodup (List.filter_sublist.nodup (range_nodup _))

theorem twoLayerIds_physical {extent width start id : Nat}
    (hi : id ∈ twoLayerIds extent width start) : id ∈ slabPhysicalFaceEdges extent :=
  windowIds_physical ((twoLayerIds_perm_window extent width start).mem_iff.mp hi)

theorem twoLayerIds_nodup (extent width start : Nat) : (twoLayerIds extent width start).Nodup :=
  (twoLayerIds_perm_window extent width start).nodup_iff.mpr (windowIds_nodup extent width start)

/-- Together with `twoLayerIds_nodup`, every middle spatial factor occurs once. -/
theorem middle_spatial_mem {extent width start id : Nat}
    (hi : id ∈ spatialIds extent width (start+1)) : id ∈ twoLayerIds extent width start := by
  simp only [twoLayerIds, List.mem_append, or_assoc]
  exact Or.inr (Or.inr (Or.inl hi))

/-- Containment guards give the intended complete spatial-base box and time
window, not merely a subset of whichever faces happened to be enumerated. -/
theorem windowFaces_mem_iff (extent width start : Nat)
    (hw : width ≤ extent+1) (ht : start+2 ≤ extent) (p : Z4Plaq) :
    p ∈ (windowIds extent width start).map (slabPlaquetteAt extent) ↔
      p.1.1 < width ∧ p.1.2.1 < width ∧ p.1.2.2.1 < width ∧
      start ≤ p.1.2.2.2 ∧ plaquetteTimeAdmissible (start+2) p := by
  constructor
  · intro hp
    obtain ⟨id,hi,rfl⟩ := List.mem_map.mp hp
    exact ((windowIds_mem_iff extent width start id).mp hi).2
  · intro hp
    have hm : p ∈ boundaryCompleteSlabPlaquettes extent := by
      apply (mem_boundaryCompleteSlabPlaquettes extent p).mpr
      constructor
      · rw [mem_boxPlaquettes]
        have hs : p.1.2.2.2 ≤ start+2 := by
          obtain ⟨v,plane⟩ := p
          cases plane <;> simp only [plaquetteTimeAdmissible] at hp <;> dsimp only at * <;> omega
        exact ⟨Nat.lt_of_lt_of_le hp.1 hw, Nat.lt_of_lt_of_le hp.2.1 hw,
          Nat.lt_of_lt_of_le hp.2.2.1 hw, by omega⟩
      · obtain ⟨v,plane⟩ := p
        cases plane <;> simp only [plaquetteTimeAdmissible] at hp ⊢ <;> omega
    let id := listIndexOf p (boundaryCompleteSlabPlaquettes extent)
    have hi : id ∈ slabPhysicalFaceEdges extent := List.mem_range.mpr (listIndexOf_lt_of_mem p _ hm)
    have he : slabPlaquetteAt extent id = p := getD_listIndexOf_of_mem _ _ _ hm
    refine List.mem_map.mpr ⟨id, (windowIds_mem_iff extent width start id).mpr ?_, he⟩
    exact ⟨hi, he.symm ▸ hp⟩

#print axioms phase_pins
#print axioms five_partition
#print axioms List.perm_middle

end YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry.spatialIds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry.temporalIds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry.windowIds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry.twoLayerIds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry.spatialIds_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry.temporalIds_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry.windowIds_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry.twoLayerIds_perm_window
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry.windowIds_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry.windowIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry.twoLayerIds_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry.twoLayerIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry.middle_spatial_mem
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry.windowFaces_mem_iff
