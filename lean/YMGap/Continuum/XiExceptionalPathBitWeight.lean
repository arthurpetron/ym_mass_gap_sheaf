/-
# Exact activity of a finite occurrence path mask

The target chain records path vertices in walk order, whereas a finite bit
mask selects them in ambient order.  This file proves that the two products
agree up to rational equivalence.  The proof keeps occurrence identities:
selected indices are permutation-equivalent to the `Nodup` path index list,
then commutativity transports the activity product.
-/

import YMGap.Continuum.XiExceptionalPathMaskAlgebra

namespace YMGap.Continuum.XiExceptionalPathBitWeight

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathMaskAlgebra

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Selected occurrence indices -/

def selectedIndices : {n : Nat} → OccBitVec n → List Nat
  | 0, .nil => []
  | _ + 1, .cons false tail => (selectedIndices tail).map Nat.succ
  | _ + 1, .cons true tail => 0 :: (selectedIndices tail).map Nat.succ

theorem selectedIndices_mem_iff : ∀ {n : Nat} (bits : OccBitVec n)
    (i : Nat), i ∈ selectedIndices bits ↔ i < n ∧ bits.at i = true
  | 0, .nil, i => by simp [selectedIndices]
  | n + 1, .cons false tail, 0 => by
      simp [selectedIndices, BitVec.at]
  | n + 1, .cons true tail, 0 => by
      simp [selectedIndices, BitVec.at]
  | n + 1, .cons false tail, i + 1 => by
      simp only [selectedIndices, List.mem_map]
      constructor
      · intro h
        obtain ⟨j, hj, hji⟩ := h
        have hij : j = i := Nat.succ.inj hji
        subst j
        have hp := (selectedIndices_mem_iff tail i).mp hj
        exact ⟨by omega, hp.2⟩
      · intro h
        have hp : i < n ∧ tail.at i = true := ⟨by omega, h.2⟩
        exact ⟨i, (selectedIndices_mem_iff tail i).mpr hp, rfl⟩
  | n + 1, .cons true tail, i + 1 => by
      simp only [selectedIndices, List.mem_cons, List.mem_map]
      constructor
      · intro h
        rcases h with hzero | htail
        · cases hzero
        · obtain ⟨j, hj, hji⟩ := htail
          have hij : j = i := Nat.succ.inj hji
          subst j
          have hp := (selectedIndices_mem_iff tail i).mp hj
          exact ⟨by omega, hp.2⟩
      · intro h
        exact Or.inr ⟨i,
          (selectedIndices_mem_iff tail i).mpr ⟨by omega, h.2⟩, rfl⟩

theorem selectedIndices_nodup : ∀ {n : Nat} (bits : OccBitVec n),
    (selectedIndices bits).Nodup
  | 0, .nil => List.nodup_nil
  | _ + 1, .cons false tail =>
      nodup_map_of_injOn Nat.succ (selectedIndices tail)
        (selectedIndices_nodup tail)
        (fun _ _ _ _ h => Nat.succ.inj h)
  | _ + 1, .cons true tail => by
      apply List.nodup_cons.mpr
      constructor
      · intro hzero
        obtain ⟨i, _, hi⟩ := List.mem_map.mp hzero
        cases hi
      · exact nodup_map_of_injOn Nat.succ (selectedIndices tail)
          (selectedIndices_nodup tail)
          (fun _ _ _ _ h => Nat.succ.inj h)

theorem selectedIndices_map_polyAt :
    ∀ (Gamma : List (Polymer L)) (bits : OccBitVec Gamma.length),
      (selectedIndices bits).map (polyAt Gamma) = selectByBits Gamma bits
  | [], .nil => rfl
  | X :: Gamma, .cons false tail => by
      change
        (((selectedIndices tail).map Nat.succ).map (polyAt (X :: Gamma))) =
          selectByBits Gamma tail
      have hpoint :
          (selectedIndices tail).map (polyAt (X :: Gamma) ∘ Nat.succ) =
            (selectedIndices tail).map (polyAt Gamma) := by
        apply List.map_congr_left
        intro i _
        exact polyAt_cons_succ X Gamma i
      rw [List.map_map, hpoint, selectedIndices_map_polyAt Gamma tail]
  | X :: Gamma, .cons true tail => by
      change
        X :: (((selectedIndices tail).map Nat.succ).map
          (polyAt (X :: Gamma))) = X :: selectByBits Gamma tail
      have hpoint :
          (selectedIndices tail).map (polyAt (X :: Gamma) ∘ Nat.succ) =
            (selectedIndices tail).map (polyAt Gamma) := by
        apply List.map_congr_left
        intro i _
        exact polyAt_cons_succ X Gamma i
      rw [List.map_map, hpoint, selectedIndices_map_polyAt Gamma tail]

/-! ## 2. A constructive permutation criterion for `Nodup` lists -/

private theorem nat_perm_of_nodup_mem_iff :
    ∀ (xs ys : List Nat), xs.Nodup → ys.Nodup →
      (∀ a, a ∈ xs ↔ a ∈ ys) → xs.Perm ys
  | [], [], _, _, _ => List.Perm.nil
  | [], y :: ys, _, _, hmem => by
      have hy : y ∈ ([] : List Nat) := (hmem y).mpr List.mem_cons_self
      cases hy
  | x :: xs, ys, hxs, hys, hmem => by
      have hparts := List.nodup_cons.mp hxs
      have hxys : x ∈ ys := (hmem x).mp List.mem_cons_self
      obtain ⟨as, bs, hsplit⟩ := List.append_of_mem hxys
      subst ys
      have hmiddle : (x :: (as ++ bs)).Perm (as ++ x :: bs) :=
        List.perm_middle.symm
      have hmiddleNodup : (x :: (as ++ bs)).Nodup :=
        hmiddle.symm.nodup hys
      have hrestParts := List.nodup_cons.mp hmiddleNodup
      have htailMem : ∀ a, a ∈ xs ↔ a ∈ as ++ bs := by
        intro a
        constructor
        · intro haxs
          have hax : a ≠ x := by
            intro hax
            subst a
            exact hparts.1 haxs
          have hay := (hmem a).mp (List.mem_cons_of_mem x haxs)
          rcases List.mem_append.mp hay with haas | htail
          · exact List.mem_append_left bs haas
          · have habs := (List.mem_cons.mp htail).resolve_left hax
            exact List.mem_append_right as habs
        · intro harest
          have hax : a ≠ x := by
            intro hax
            subst a
            exact hrestParts.1 harest
          have hay : a ∈ as ++ x :: bs := by
            rcases List.mem_append.mp harest with haas | habs
            · exact List.mem_append_left (x :: bs) haas
            · exact List.mem_append_right as (List.mem_cons_of_mem x habs)
          exact (List.mem_cons.mp ((hmem a).mpr hay)).resolve_left hax
      have htailPerm := nat_perm_of_nodup_mem_iff xs (as ++ bs)
        hparts.2 hrestParts.2 htailMem
      exact (List.Perm.cons x htailPerm).trans hmiddle

theorem selectedIndices_pathOccurrenceBits_perm
    (n : Nat) (vertices : List Nat)
    (hnodup : vertices.Nodup)
    (hbound : ∀ i, i ∈ vertices → i < n) :
    (selectedIndices (pathOccurrenceBits n vertices)).Perm vertices := by
  apply nat_perm_of_nodup_mem_iff _ _
    (selectedIndices_nodup _) hnodup
  intro i
  rw [selectedIndices_mem_iff]
  constructor
  · intro hp
    have hbit := hp.2
    rw [pathOccurrenceBits_at n vertices i hp.1] at hbit
    exact of_decide_eq_true hbit
  · intro hi
    have hib := hbound i hi
    exact ⟨hib, by
      rw [pathOccurrenceBits_at n vertices i hib]
      exact decide_eq_true hi⟩

/-! ## 3. Activity products respect the path permutation -/

private theorem familyActivity_swap (w : Q')
    (label : L.Plaquette → Rep) (A B : Polymer L)
    (S : List (Polymer L)) :
    familyActivity w (A :: B :: S) label ≈
      familyActivity w (B :: A :: S) label := by
  simp only [familyActivity_cons]
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
  exact Q'.mul_assoc_eqv _ _ _

theorem familyActivity_perm (w : Q') (label : L.Plaquette → Rep) :
    ∀ {S T : List (Polymer L)}, S.Perm T →
      familyActivity w S label ≈ familyActivity w T label
  | _, _, List.Perm.nil => Q'.eqv_refl 1
  | _, _, List.Perm.cons X h =>
      Q'.mul_eqv_congr_left (activity w X label) _ _
        (familyActivity_perm w label h)
  | _, _, List.Perm.swap A B S =>
      Q'.eqv_symm (familyActivity_swap w label A B S)
  | _, _, List.Perm.trans h1 h2 =>
      Q'.eqv_trans _ _ _ (familyActivity_perm w label h1)
        (familyActivity_perm w label h2)

theorem CWalk.activityWeight_eq_familyActivity_vertices
    (w : Q') (label : L.Plaquette → Rep) :
    ∀ {X Y : Polymer L}
      (walk : CWalk (fun A B : Polymer L => !(compatibleB A B)) X Y),
      walk.activityWeight w label ≈
        familyActivity w walk.vertices label
  | _, _, .single X => by
      simp only [CWalk.activityWeight, CWalk.vertices, familyActivity_cons,
        familyActivity_nil]
      exact Q'.eqv_symm (Q'.mul_one_eqv (activity w X label))
  | _, _, .cons _ rest => by
      simp only [CWalk.activityWeight, CWalk.vertices, familyActivity_cons]
      exact Q'.mul_eqv_congr_left _ _ _
        (CWalk.activityWeight_eq_familyActivity_vertices w label rest)

theorem pathOccurrenceFamilyActivity_eqv_walk
    (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep)
    (path : DistinctExceptionalPolymerPath Gamma qP b2 left right marked) :
    familyActivity w
        (selectByBits Gamma
          (pathOccurrenceBits Gamma.length path.indexWalk.vertices)) label ≈
      path.polymerWalk.activityWeight w label := by
  have hp := selectedIndices_pathOccurrenceBits_perm Gamma.length
    path.indexWalk.vertices path.index_nodup
    (fun i hi => by
      have hseedN := (forwardSeed_parts Gamma.length left right
        (predAt Gamma b2) path.seed_true).1
      exact walk_vertices_lt_of_seed Gamma.length (incAtDistinct Gamma)
        left right path.indexWalk hseedN i hi)
  have hmapPerm := hp.map (polyAt Gamma)
  rw [selectedIndices_map_polyAt Gamma
    (pathOccurrenceBits Gamma.length path.indexWalk.vertices)] at hmapPerm
  rw [← path.polymer_vertices] at hmapPerm
  exact Q'.eqv_trans _ _ _ (familyActivity_perm w label hmapPerm)
    (Q'.eqv_symm
      (CWalk.activityWeight_eq_familyActivity_vertices w label
        path.polymerWalk))

theorem pathOccurrenceMaskWeight_eqv_walk
    (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep)
    (path : DistinctExceptionalPolymerPath Gamma qP b2 left right marked) :
    maskWeight w Gamma label
        (bitMask (pathOccurrenceBits Gamma.length path.indexWalk.vertices)) ≈
      path.polymerWalk.activityWeight w label := by
  refine Q'.eqv_trans _ _ _
    (maskWeight_eqv_familyActivity w Gamma label
      (bitMask
        (pathOccurrenceBits Gamma.length path.indexWalk.vertices))) ?_
  rw [maskFamily_toMask_eq_selectByBits]
  exact pathOccurrenceFamilyActivity_eqv_walk w Gamma label path

#print axioms selectedIndices_pathOccurrenceBits_perm
#print axioms familyActivity_perm
#print axioms CWalk.activityWeight_eq_familyActivity_vertices
#print axioms pathOccurrenceFamilyActivity_eqv_walk
#print axioms pathOccurrenceMaskWeight_eqv_walk

end YMGap.Continuum.XiExceptionalPathBitWeight
