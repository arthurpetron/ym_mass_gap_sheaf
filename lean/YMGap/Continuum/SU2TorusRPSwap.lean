/-
# Torus RP (d9v): link-list permutations leave `∫ Π T_K` invariant

An adjacent transposition of the link list is a block involution (`swapInv`) that relabels the plaquette indices
(`swap_idx`). Chaining these along `List.Perm` gives `perm_haar`: for nodup link lists `L₁ ~ L₂` containing every
plaquette link, `∫_{|L₁|} Π T_K[L₁] = ∫_{|L₁|} Π T_K[L₂]`. Observables and Θ are not transported yet.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPRelabel
import YMGap.Continuum.SU2TorusRPSupTK

namespace YMGap.Continuum.SU2TorusRPSwap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection (QuaternionBlockInvolution)
open YMGap.Continuum.SU2TorusRPSplitTK (plaqIdx)
def swapK (k b : Nat) : Nat := if b = k then k + 1 else if b = k + 1 then k else b
theorem idx_pre {α} [BEq α] [LawfulBEq α] (ℓ : α) (B : List α) : ∀ pre : List α, ℓ ∉ pre →
    (pre ++ B).idxOf ℓ = pre.length + B.idxOf ℓ
  | [], _ => by rw [List.nil_append, List.length_nil, Nat.zero_add]
  | a :: pre, h => by
    have ha : a ≠ ℓ := fun e => h (e ▸ List.mem_cons_self ..)
    have hb : (a == ℓ) = false := beq_false_of_ne ha
    rw [List.cons_append, List.idxOf_cons, hb, cond_false,
      idx_pre ℓ B pre fun hm => h (List.mem_cons_of_mem _ hm)]
    simp only [List.length_cons]; omega
theorem idx_mem {α} [BEq α] [LawfulBEq α] (ℓ : α) (B B' : List α) : ∀ pre : List α, ℓ ∈ pre →
    (pre ++ B).idxOf ℓ = (pre ++ B').idxOf ℓ ∧ (pre ++ B).idxOf ℓ < pre.length
  | [], h => nomatch h
  | a :: pre, h => by
    rw [List.cons_append, List.cons_append, List.idxOf_cons, List.idxOf_cons]
    cases hb : (a == ℓ) with
    | true => rw [cond_true, cond_true]; exact ⟨rfl, Nat.succ_pos _⟩
    | false =>
      have ha : a ≠ ℓ := fun e => by rw [e, beq_self_eq_true] at hb; exact Bool.noConfusion hb
      rw [cond_false, cond_false]
      have hm : ℓ ∈ pre := by
        cases h with
        | head => exact absurd rfl ha
        | tail _ hm => exact hm
      obtain ⟨e, lt⟩ := idx_mem ℓ B B' pre hm
      refine ⟨by rw [e], ?_⟩
      rw [List.length_cons]; exact Nat.succ_lt_succ lt
theorem swap_idx (pre A : List Z4Link) (x y : Z4Link) (hxy : x ≠ y)
    (ℓ : Z4Link) : swapK pre.length ((pre ++ x :: y :: A).idxOf ℓ) = (pre ++ y :: x :: A).idxOf ℓ := by
  by_cases hm : ℓ ∈ pre
  · obtain ⟨e, lt⟩ := idx_mem ℓ (x :: y :: A) (y :: x :: A) pre hm
    rw [← e]; unfold swapK; rw [if_neg (by omega), if_neg (by omega)]
  · rw [idx_pre ℓ _ pre hm, idx_pre ℓ _ pre hm]
    rw [List.idxOf_cons, List.idxOf_cons, List.idxOf_cons, List.idxOf_cons]
    cases h1 : (x == ℓ) with
    | true =>
      have e : x = ℓ := eq_of_beq h1
      have h2 : (y == ℓ) = false := beq_false_of_ne (fun e' => hxy (e.trans e'.symm))
      rw [h2]; simp only [cond_true, cond_false, swapK]; (repeat' split) <;> omega
    | false =>
      cases h2 : (y == ℓ) with
      | true => simp only [cond_true, cond_false, swapK]; rw [if_neg (by omega), if_pos trivial, Nat.add_zero]
      | false => simp only [cond_false, swapK]; (repeat' split) <;> omega
def swapInv (n k : Nat) (hk : k + 1 < n) : QuaternionBlockInvolution n where
  map := swapK k
  map_lt b hb := by unfold swapK; (repeat' split) <;> omega
  involutive b hb := by unfold swapK; (repeat' split) <;> omega

/-- The four links of a plaquette (in `plaqIdx` order). -/
def plaqL (N : Nat) (p : Z4Plaq) : List Z4Link :=
  [(p.1, (dirsOf p.2).1), (tAdd N p.1 (dirsOf p.2).1, (dirsOf p.2).2),
   (tAdd N p.1 (dirsOf p.2).2, (dirsOf p.2).1), (p.1, (dirsOf p.2).2)]

theorem idx_lt {α} [BEq α] [LawfulBEq α] (ℓ : α) : ∀ L : List α, ℓ ∈ L → L.idxOf ℓ < L.length
  | [], h => nomatch h
  | a :: L, h => by
    rw [List.idxOf_cons, List.length_cons]
    cases hb : (a == ℓ) with
    | true => exact Nat.succ_pos _
    | false =>
      have hm : ℓ ∈ L := by
        rcases List.mem_cons.1 h with e | hm
        · rw [e, beq_self_eq_true] at hb; exact Bool.noConfusion hb
        · exact hm
      exact Nat.succ_lt_succ (idx_lt ℓ L hm)

theorem plaqIdx_lt (L : List Z4Link) (N : Nat) (p : Z4Plaq) (h : ∀ ℓ ∈ plaqL N p, ℓ ∈ L) :
    ∀ b ∈ plaqIdx L N p, b < L.length := by
  intro b hb
  unfold plaqIdx at hb
  unfold plaqL at h
  rcases List.mem_cons.1 hb with e | hb
  · rw [e]; exact idx_lt _ L (h _ (List.mem_cons_self ..))
  rcases List.mem_cons.1 hb with e | hb
  · rw [e]; exact idx_lt _ L (h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  rcases List.mem_cons.1 hb with e | hb
  · rw [e]; exact idx_lt _ L (h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  rcases List.mem_cons.1 hb with e | hb
  · rw [e]; exact idx_lt _ L (h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  exact absurd hb (List.not_mem_nil)

theorem swap_plaqIdx (pre A : List Z4Link) (x y : Z4Link) (hxy : x ≠ y) (N : Nat) (p : Z4Plaq) :
    (plaqIdx (pre ++ x :: y :: A) N p).map (swapK pre.length) = plaqIdx (pre ++ y :: x :: A) N p := by
  unfold plaqIdx
  simp only [List.map_cons, List.map_nil]
  rw [swap_idx pre A x y hxy, swap_idx pre A x y hxy, swap_idx pre A x y hxy, swap_idx pre A x y hxy]

variable (N : Nat) (β : Q') (K : Nat) (ps : List Z4Plaq)

theorem swap_haar (pre A : List Z4Link) (x y : Z4Link) (hxy : x ≠ y)
    (hmem : ∀ p ∈ ps, ∀ ℓ ∈ plaqL N p, ℓ ∈ pre ++ x :: y :: A) :
    (quaternionHaar (pre ++ x :: y :: A).length
        (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (pre ++ x :: y :: A) N β K) ps)).eqv
      (quaternionHaar (pre ++ x :: y :: A).length
        (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (pre ++ y :: x :: A) N β K) ps)) := by
  have hk : pre.length + 1 < (pre ++ x :: y :: A).length := by
    rw [List.length_append, List.length_cons, List.length_cons]; omega
  have hlt := fun p hp => plaqIdx_lt _ N p (hmem p hp)
  exact YMGap.Continuum.SU2TorusRPRelabel.relabel_haar _ _ N β K (swapInv _ _ hk) ps hlt
    (fun p _ => swap_plaqIdx pre A x y hxy N p)
    (YMGap.Continuum.SU2TorusRPSupTK.sup_prodTK _ N β K ps hlt)

theorem perm_haar_pre {A B : List Z4Link} (hAB : A.Perm B) : ∀ pre : List Z4Link, (pre ++ A).Nodup →
    (∀ p ∈ ps, ∀ ℓ ∈ plaqL N p, ℓ ∈ pre ++ A) →
    (quaternionHaar (pre ++ A).length
        (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (pre ++ A) N β K) ps)).eqv
      (quaternionHaar (pre ++ A).length
        (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (pre ++ B) N β K) ps)) := by
  induction hAB with
  | nil => intro pre _ _; exact Q'.eqv_refl _
  | cons x _ ih =>
    rename_i l₁ l₂ _
    intro pre hnd hmem
    rw [List.append_cons pre x l₁, List.append_cons pre x l₂]
    rw [List.append_cons pre x l₁] at hnd hmem
    exact ih _ hnd hmem
  | swap x y l =>
    intro pre hnd hmem
    have hp := (List.pairwise_append.1 hnd).2.1
    have hyx : y ≠ x := (List.pairwise_cons.1 hp).1 x (List.mem_cons_self ..)
    exact swap_haar N β K ps pre l y x hyx hmem
  | trans h12 _ ih1 ih2 =>
    intro pre hnd hmem
    have hP := List.Perm.append_left pre h12
    have e := hP.length_eq
    have h2 := ih2 pre (hP.nodup_iff.1 hnd) fun p hp ℓ hℓ => hP.mem_iff.1 (hmem p hp ℓ hℓ)
    rw [← e] at h2
    exact Q'.eqv_trans _ _ _ (ih1 pre hnd hmem) h2

theorem perm_haar {L₁ L₂ : List Z4Link} (h : L₁.Perm L₂) (hnd : L₁.Nodup)
    (hmem : ∀ p ∈ ps, ∀ ℓ ∈ plaqL N p, ℓ ∈ L₁) :
    (quaternionHaar L₁.length (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK L₁ N β K) ps)).eqv
      (quaternionHaar L₁.length (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK L₂ N β K) ps)) :=
  perm_haar_pre N β K ps h [] hnd hmem

end YMGap.Continuum.SU2TorusRPSwap

#print axioms YMGap.Continuum.SU2TorusRPSwap.swap_haar
#print axioms YMGap.Continuum.SU2TorusRPSwap.idx_lt
#print axioms YMGap.Continuum.SU2TorusRPSwap.plaqIdx_lt
#print axioms YMGap.Continuum.SU2TorusRPSwap.swap_plaqIdx
#print axioms YMGap.Continuum.SU2TorusRPSwap.perm_haar
