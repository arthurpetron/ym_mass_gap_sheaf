/-
# Computed two-replica labels covering each selected face

Each face chooses a positive label on the left, right, or both. Both
replicas vanish outside the selected list, and every listed face is
occupied in at least one replica. This is the finite carrier needed for
the representation expansion of a two-slot Mobius coefficient.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

namespace YMGap.Continuum.PairedPositiveFaceLabellings

set_option autoImplicit false

open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

def positivePairs (K : Nat) : List (Nat × Nat) :=
  (List.range K).map (fun n => (n+1,0)) ++
    (List.range K).map (fun n => (0,n+1)) ++
    (List.range K).flatMap (fun n => (List.range K).map (fun m => (n+1,m+1)))

theorem positivePairs_sound {K : Nat} {spins : Nat × Nat} (h : spins ∈ positivePairs K) :
    spins.1 ≤ K ∧ spins.2 ≤ K ∧ (0 < spins.1 ∨ 0 < spins.2) := by
  simp only [positivePairs, List.mem_append, List.mem_map, List.mem_flatMap] at h
  rcases h with (⟨n,hn,he⟩ | ⟨n,hn,he⟩) | ⟨n,hn,m,hm,he⟩
  all_goals subst spins
  all_goals simp only [List.mem_range] at *
  · exact ⟨by omega,by omega,Or.inl (by omega)⟩
  · exact ⟨by omega,by omega,Or.inr (by omega)⟩
  · exact ⟨by omega,by omega,Or.inl (by omega)⟩

def setPair (pair : EdgeLabelling × EdgeLabelling) (id : Nat) (spins : Nat × Nat) : EdgeLabelling × EdgeLabelling :=
  (setEdgeLabel pair.1 id spins.1, setEdgeLabel pair.2 id spins.2)

def labels (K : Nat) : List Nat → List (EdgeLabelling × EdgeLabelling)
  | [] => [(zeroEdgeLabelling,zeroEdgeLabelling)]
  | id::ids => (positivePairs K).flatMap (fun spins => (labels K ids).map (fun pair => setPair pair id spins))

theorem outside (K : Nat) : ∀ ids : List Nat, ∀ pair, pair ∈ labels K ids →
    ∀ id, id ∉ ids → pair.1 id = 0 ∧ pair.2 id = 0
  | [], pair, h, _, _ => by
    simp only [labels, List.mem_singleton] at h
    subst pair
    exact ⟨rfl,rfl⟩
  | head::ids, pair, h, id, hn => by
    obtain ⟨spins,_,hmap⟩ := List.mem_flatMap.mp h
    obtain ⟨tail,ht,he⟩ := List.mem_map.mp hmap
    subst pair
    have hne : id ≠ head := fun he => hn (List.mem_cons.mpr (Or.inl he))
    have hi := outside K ids tail ht id (fun h => hn (List.mem_cons_of_mem head h))
    simpa only [setPair, setEdgeLabel, if_neg hne] using hi

theorem covers (K : Nat) : ∀ ids : List Nat, ∀ pair, pair ∈ labels K ids →
    ∀ id, id ∈ ids → 0 < pair.1 id ∨ 0 < pair.2 id
  | [], _, _, _, hi => by cases hi
  | head::ids, pair, h, id, hi => by
    obtain ⟨spins,hs,hmap⟩ := List.mem_flatMap.mp h
    obtain ⟨tail,ht,he⟩ := List.mem_map.mp hmap
    subst pair
    by_cases he : id = head
    · subst id
      simpa only [setPair, setEdgeLabel, ↓reduceIte] using (positivePairs_sound hs).2.2
    · have hm : id ∈ ids := (List.mem_cons.mp hi).resolve_left he
      simpa only [setPair, setEdgeLabel, if_neg he] using covers K ids tail ht id hm

theorem bounded (K : Nat) : ∀ ids : List Nat, ∀ pair, pair ∈ labels K ids →
    ∀ id, pair.1 id ≤ K ∧ pair.2 id ≤ K
  | [], pair, h, _ => by
    simp only [labels, List.mem_singleton] at h
    subst pair
    exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  | head::ids, pair, h, id => by
    obtain ⟨spins,hs,hmap⟩ := List.mem_flatMap.mp h
    obtain ⟨tail,ht,he⟩ := List.mem_map.mp hmap
    subst pair
    by_cases he : id = head
    · subst id
      have hp := positivePairs_sound hs
      simpa only [setPair, setEdgeLabel, ↓reduceIte] using And.intro hp.1 hp.2.1
    · simpa only [setPair, setEdgeLabel, if_neg he] using bounded K ids tail ht id

end YMGap.Continuum.PairedPositiveFaceLabellings

#print axioms YMGap.Continuum.PairedPositiveFaceLabellings.positivePairs
#print axioms YMGap.Continuum.PairedPositiveFaceLabellings.positivePairs_sound
#print axioms YMGap.Continuum.PairedPositiveFaceLabellings.labels
#print axioms YMGap.Continuum.PairedPositiveFaceLabellings.outside
#print axioms YMGap.Continuum.PairedPositiveFaceLabellings.covers
#print axioms YMGap.Continuum.PairedPositiveFaceLabellings.bounded
