/-
# A finite carrier bound for the reversible whole-forest code

For mass S, c<=S/2 roots, root alphabet size M and neighbor alphabet size D,
the code has at most 4^S*M^c*D^(S-c) possibilities in its c stratum. If
D<=L and M*D<=L^2, this is at most (4L)^S. Summing the actual finite code
strata gives (8L)^S. The carrier is constructed, not an arbitrary number.

This bounds codes of supplied forests. Applying it to original spatial pairs
requires their faithful forest construction and full-pair recovery.
-/

import YMGap.Continuum.FiniteRootedForestCode

namespace YMGap.Continuum.FiniteRootedForestCount

set_option autoImplicit false

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.BF4ExactSlabTwoCapLocalCode
open YMGap.Continuum.FiniteRootedForestCode

def rootWords {A : Type} (pool : List A) : Nat → List (List A)
  | 0 => [[]]
  | n+1 => (cartesian pool (rootWords pool n)).map (fun rw => rw.1::rw.2)

theorem rootWords_length {A : Type} (pool : List A) : ∀ n,
    (rootWords pool n).length=pool.length^n
  | 0 => rfl
  | n+1 => by
    rw [rootWords,List.length_map,cartesian_length,rootWords_length pool n,Nat.pow_succ,Nat.mul_comm]

theorem rootWords_mem {A : Type} (pool : List A) : ∀ word : List A,
    (∀ x, x ∈ word → x ∈ pool) → word ∈ rootWords pool word.length
  | [], _ => List.mem_cons_self
  | x::xs, hp => by
    apply List.mem_map.mpr
    exact ⟨(x,xs),(mem_cartesian_iff _ _ _).mpr ⟨hp x List.mem_cons_self,
      rootWords_mem pool xs (fun y hy => hp y (List.mem_cons_of_mem x hy))⟩,rfl⟩

def stratum {A : Type} (pool : List A) (D S c : Nat) : List (Code A D) :=
  cartesian (choiceSeqs 2 (2*S)) (cartesian (rootWords pool c) (choiceSeqs D (S-c)))

theorem stratum_length {A : Type} (pool : List A) (D S c : Nat) :
    (stratum pool D S c).length=2^(2*S)*(pool.length^c*D^(S-c)) := by
  rw [stratum,cartesian_length,cartesian_length,choiceSeqs_length,choiceSeqs_length,rootWords_length]

theorem root_descent_cost (M D L S c : Nat) (hD : D ≤ L) (hMD : M*D ≤ L^2)
    (hc : 2*c ≤ S) : M^c*D^(S-c) ≤ L^S := by
  have he : S-c=c+(S-2*c) := by omega
  calc
    M^c*D^(S-c) = (M*D)^c*D^(S-2*c) := by rw [he,Nat.pow_add,Nat.mul_pow,Nat.mul_assoc]
    _ ≤ (L^2)^c*L^(S-2*c) := Nat.mul_le_mul (Nat.pow_le_pow_left hMD c)
      (Nat.pow_le_pow_left hD (S-2*c))
    _ = L^S := by
      rw [← Nat.pow_mul,← Nat.pow_add]
      congr 1
      omega

theorem stratum_length_le {A : Type} (pool : List A) (D L S c : Nat)
    (hD : D ≤ L) (hMD : pool.length*D ≤ L^2) (hc : 2*c ≤ S) :
    (stratum pool D S c).length ≤ (4*L)^S := by
  rw [stratum_length]
  have h := Nat.mul_le_mul_left (2^(2*S)) (root_descent_cost pool.length D L S c hD hMD hc)
  simpa only [Nat.pow_mul,← Nat.mul_pow] using h

def carrier {A : Type} (pool : List A) (D S : Nat) : List (Code A D) :=
  (List.range (S+1)).flatMap (fun c => if 2*c ≤ S then stratum pool D S c else [])

theorem encode_mem {BL : BddLattice} (forest : List (RTree BL))
    (pool : List BL.toLattice.Plaquette)
    (hp : ∀ r, r ∈ roots forest → r ∈ pool) (hc : 2*forest.length ≤ mass forest) :
    encode forest ∈ carrier pool BL.D (mass forest) := by
  apply List.mem_flatMap.mpr
  refine ⟨forest.length,List.mem_range.mpr (by omega),?_⟩
  rw [if_pos hc]
  apply (mem_cartesian_iff _ _ _).mpr
  refine ⟨mem_choiceSeqs_of_length _ _ _ (bits_length forest),?_⟩
  apply (mem_cartesian_iff _ _ _).mpr
  constructor
  · have h := rootWords_mem pool (roots forest) hp
    simpa only [roots,List.length_map] using h
  · apply mem_choiceSeqs_of_length
    have h := choices_length forest
    change (choices forest).length=mass forest-forest.length
    omega

theorem flatMap_length_le {A B : Type} (f : A → List B) (C : Nat) : ∀ xs : List A,
    (∀ x, x ∈ xs → (f x).length ≤ C) → (xs.flatMap f).length ≤ xs.length*C
  | [], _ => by simp only [List.flatMap_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | x::xs, h => by
    have hx := h x List.mem_cons_self
    have ht := flatMap_length_le f C xs (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem succ_le_two_pow : ∀ S : Nat, S+1 ≤ 2^S
  | 0 => by decide
  | S+1 => by
    have h := succ_le_two_pow S
    rw [Nat.pow_succ]
    omega

theorem carrier_length_le {A : Type} (pool : List A) (D L S : Nat)
    (hD : D ≤ L) (hMD : pool.length*D ≤ L^2) : (carrier pool D S).length ≤ (8*L)^S := by
  have h := flatMap_length_le (fun c => if 2*c ≤ S then stratum pool D S c else [])
    ((4*L)^S) (List.range (S+1)) (fun c _ => by
      dsimp only
      by_cases hc : 2*c ≤ S
      · rw [if_pos hc]; exact stratum_length_le pool D L S c hD hMD hc
      · rw [if_neg hc]; exact Nat.zero_le _)
  rw [List.length_range] at h
  apply Nat.le_trans h
  have hs := Nat.mul_le_mul_right ((4*L)^S) (succ_le_two_pow S)
  simpa only [← Nat.mul_pow,← Nat.mul_assoc] using hs

end YMGap.Continuum.FiniteRootedForestCount

#print axioms YMGap.Continuum.FiniteRootedForestCount.rootWords
#print axioms YMGap.Continuum.FiniteRootedForestCount.rootWords_length
#print axioms YMGap.Continuum.FiniteRootedForestCount.rootWords_mem
#print axioms YMGap.Continuum.FiniteRootedForestCount.stratum
#print axioms YMGap.Continuum.FiniteRootedForestCount.stratum_length
#print axioms YMGap.Continuum.FiniteRootedForestCount.root_descent_cost
#print axioms YMGap.Continuum.FiniteRootedForestCount.stratum_length_le
#print axioms YMGap.Continuum.FiniteRootedForestCount.carrier
#print axioms YMGap.Continuum.FiniteRootedForestCount.encode_mem
#print axioms YMGap.Continuum.FiniteRootedForestCount.flatMap_length_le
#print axioms YMGap.Continuum.FiniteRootedForestCount.succ_le_two_pow
#print axioms YMGap.Continuum.FiniteRootedForestCount.carrier_length_le
