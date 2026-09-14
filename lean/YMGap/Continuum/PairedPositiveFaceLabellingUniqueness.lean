/-
# The original two-replica enumeration has no repeated entries

For a duplicate-free selected support, the head spins recover the branch
and resetting that head to zero recovers the tail. No equality decision on
functions and no deduplication of the original enumeration is used.
-/

import YMGap.Continuum.PairedPositiveFaceLabellings
import YMGap.Continuum.CayleyPruferInjection
import YMGap.Continuum.CayleyParentInj

namespace YMGap.Continuum.PairedPositiveFaceLabellingUniqueness

set_option autoImplicit false

open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.CayleyPruferInjection

theorem flatMap_nodup {A B : Type} (block : A → List B) (source : List A)
    (hs : source.Nodup) (hb : ∀ a, a ∈ source → (block a).Nodup)
    (hd : ∀ a, a ∈ source → ∀ b, b ∈ source → a ≠ b →
      ∀ x, x ∈ block a → x ∉ block b) : (source.flatMap block).Nodup := by
  apply List.pairwise_flatMap.mpr
  refine ⟨hb, hs.imp_of_mem ?_⟩
  intro a b ha hb hab x hx y hy he
  exact hd a ha b hb hab x hx (he ▸ hy)

theorem positivePairs_nodup (K : Nat) : (positivePairs K).Nodup := by
  have hr := CayleyParentInj.range_nodup K
  have hm (n : Nat) : ((List.range K).map (fun m => (n+1,m+1))).Nodup :=
    nodup_map_of_injOn _ _ hr (fun a _ b _ he => by
      have h := congrArg Prod.snd he
      exact Nat.add_right_cancel h)
  unfold positivePairs
  apply List.nodup_append.mpr
  refine ⟨List.nodup_append.mpr ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact nodup_map_of_injOn _ _ hr (fun a _ b _ he =>
      Nat.add_right_cancel (congrArg Prod.fst he))
  · exact nodup_map_of_injOn _ _ hr (fun a _ b _ he =>
      Nat.add_right_cancel (congrArg Prod.snd he))
  · intro x hx y hy he
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hy
    have h := congrArg Prod.fst he
    omega
  · apply flatMap_nodup _ _ hr (fun n _ => hm n)
    intro a _ b _ hab x hx hy
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨d,_,he⟩ := List.mem_map.mp hy
    exact hab (Nat.add_right_cancel (congrArg Prod.fst he)).symm
  · intro x hx y hy he
    obtain ⟨a,_,hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hy
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨c,_,rfl⟩ := List.mem_map.mp hx
      have h := congrArg Prod.snd he
      omega
    · obtain ⟨c,_,rfl⟩ := List.mem_map.mp hx
      have h := congrArg Prod.fst he
      omega

theorem setPair_head (pair : EdgeLabelling × EdgeLabelling) (id : Nat) (spins : Nat × Nat) :
    ((setPair pair id spins).1 id, (setPair pair id spins).2 id) = spins := by
  simp only [setPair,setEdgeLabel,↓reduceIte]

theorem setPair_erase (pair : EdgeLabelling × EdgeLabelling) (id : Nat) (spins : Nat × Nat)
    (hz : pair.1 id = 0 ∧ pair.2 id = 0) :
    setPair (setPair pair id spins) id (0,0) = pair := by
  apply Prod.ext
  · funext i
    by_cases hi : i = id
    · subst i
      simpa only [setPair,setEdgeLabel,↓reduceIte] using hz.1.symm
    · simp only [setPair,setEdgeLabel,if_neg hi]
  · funext i
    by_cases hi : i = id
    · subst i
      simpa only [setPair,setEdgeLabel,↓reduceIte] using hz.2.symm
    · simp only [setPair,setEdgeLabel,if_neg hi]

theorem labels_nodup (K : Nat) : ∀ ids : List Nat, ids.Nodup → (labels K ids).Nodup
  | [], _ => List.nodup_cons.mpr ⟨List.not_mem_nil,List.nodup_nil⟩
  | id::ids, hn => by
      have ht := List.nodup_cons.mp hn
      have hz (pair : EdgeLabelling × EdgeLabelling) (hp : pair ∈ labels K ids) :=
        outside K ids pair hp id ht.1
      apply flatMap_nodup _ _ (positivePairs_nodup K)
      · intro spins _
        apply nodup_map_of_injOn _ _ (labels_nodup K ids ht.2)
        intro a ha b hb he
        have h := congrArg (fun pair => setPair pair id (0,0)) he
        dsimp only at h
        rw [setPair_erase a id spins (hz a ha),setPair_erase b id spins (hz b hb)] at h
        exact h
      · intro a _ b _ hab pair hp hq
        obtain ⟨left,_,hl⟩ := List.mem_map.mp hp
        obtain ⟨right,_,hr⟩ := List.mem_map.mp hq
        have h := congrArg (fun p : EdgeLabelling × EdgeLabelling => (p.1 id,p.2 id))
          (hl.trans hr.symm)
        dsimp only at h
        rw [setPair_head,setPair_head] at h
        exact hab h

end YMGap.Continuum.PairedPositiveFaceLabellingUniqueness

#print axioms YMGap.Continuum.PairedPositiveFaceLabellingUniqueness.flatMap_nodup
#print axioms YMGap.Continuum.PairedPositiveFaceLabellingUniqueness.positivePairs_nodup
#print axioms YMGap.Continuum.PairedPositiveFaceLabellingUniqueness.setPair_head
#print axioms YMGap.Continuum.PairedPositiveFaceLabellingUniqueness.setPair_erase
#print axioms YMGap.Continuum.PairedPositiveFaceLabellingUniqueness.labels_nodup
