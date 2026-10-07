/-
# R1 commit 8: the link-connected gas is a `Z4BoxGas` on the torus box; link grouping bound

ADDITIVE.  **GROUP-BLIND PLUMBING.**  Assume `P` is duplicate-free and lies in `torusPlaquettes N`.
* `leaf_inv`: every explored cluster is grown, duplicate-free, and inside `A ∪ Q`, and it
  contains `A`.
* `tree_distinct`, `gas_distinct`: no two polymers of `gas N P` have the same support.
* `linkBox`: `gas N P` as a `Z4BoxGas (torusChain N)`.
* `hgroupL`: `Π_{x ∈ gas, x ≁_link a} (1 + η^{|x|}) ≤ (5/3)^{24·|a|}`, through the
  24-neighbour cover `nbA a` and `z4_hgroup` (the 625ⁿ animal count).
-/

import YMGap.Continuum.SU2LinkGasGeometry

namespace YMGap.Continuum.SU2LinkGasBox

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.Z4TorusPolymerKP
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BddLatticeAnimal (sameSupport)
open YMGap.Continuum.SizeWeightedPolymerKP (prodm etaZ)
open YMGap.Continuum.Z4PolymerKP
open YMGap.Continuum.PolymerDecayZ4 (prodm_sub_le)
open YMGap.Continuum.SU2ClusterExplore (adj touch pick explore pick_some pick_none)
open YMGap.Continuum.SU2PolymerIdentity (incL gas)
open YMGap.Continuum.SU2LinkGasGeometry

variable (N : Nat)

def rm (x : Z4Plaq) : List Z4Plaq → List Z4Plaq
  | [] => []
  | y :: l => if y = x then l else y :: rm x l

theorem rm_len (x : Z4Plaq) : ∀ l : List Z4Plaq, x ∈ l → (rm x l).length + 1 = l.length
  | [], h => absurd h List.not_mem_nil
  | y :: l, h => by
    unfold rm
    split
    · rfl
    · rename_i hne
      have hx : x ∈ l := (List.mem_cons.mp h).resolve_left (fun e => hne e.symm)
      show (rm x l).length + 1 + 1 = l.length + 1
      rw [rm_len x l hx]

theorem mem_rm {x y : Z4Plaq} (hne : y ≠ x) : ∀ l : List Z4Plaq, y ∈ l → y ∈ rm x l
  | [], h => absurd h List.not_mem_nil
  | z :: l, h => by
    unfold rm
    split
    · rename_i e
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd e hne
      · exact h
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_rm hne l h)

theorem len_le_of_sub : ∀ (l₁ l₂ : List Z4Plaq), l₁.Nodup → (∀ x, x ∈ l₁ → x ∈ l₂) →
    l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | x :: l₁, l₂, hn, hs => by
    have hx := hs x List.mem_cons_self
    have hn' := List.nodup_cons.mp hn
    have ih := len_le_of_sub l₁ (rm x l₂) hn'.2 fun y hy =>
      mem_rm (fun e => hn'.1 (by rw [← e]; exact hy)) l₂ (hs y (List.mem_cons_of_mem _ hy))
    have := rm_len x l₂ hx
    show l₁.length + 1 ≤ _; omega

theorem nodup_excl {A Q₁ Q₂ : List Z4Plaq} {q : Z4Plaq} (h : (A ++ (Q₁ ++ q :: Q₂)).Nodup) :
    (A ++ (Q₁ ++ Q₂)).Nodup ∧ ((q :: A) ++ (Q₁ ++ Q₂)).Nodup := by
  have hp : (A ++ (Q₁ ++ q :: Q₂)).Perm (q :: (A ++ (Q₁ ++ Q₂))) := by
    rw [← List.append_assoc, ← List.append_assoc]; exact List.perm_middle
  have h2 := hp.nodup_iff.mp h
  exact ⟨(List.nodup_cons.mp h2).2, h2⟩

theorem q_notin {A Q₁ Q₂ : List Z4Plaq} {q : Z4Plaq} (h : (A ++ (Q₁ ++ q :: Q₂)).Nodup) :
    q ∉ A ∧ q ∉ Q₁ ++ Q₂ := by
  have h3 := (List.nodup_cons.mp (nodup_excl h).2).1
  exact ⟨fun hq => h3 (List.mem_append_left _ hq), fun hq => h3 (List.mem_append_right _ hq)⟩

theorem mem_split {Q₁ Q₂ : List Z4Plaq} {q x : Z4Plaq} (h : x ∈ Q₁ ++ Q₂) : x ∈ Q₁ ++ q :: Q₂ :=
  List.mem_append.mpr ((List.mem_append.mp h).imp id (List.mem_cons_of_mem _))

theorem leaf_inv : ∀ (f : Nat) (A Q : List Z4Plaq), Q.length ≤ f → (A ++ Q).Nodup → Grow N A →
    ∀ L ∈ explore N f A Q, Grow N L.1 ∧ L.1.Nodup ∧ (∀ x, x ∈ L.1 → x ∈ A ∨ x ∈ Q) ∧
      (∀ x, x ∈ A → x ∈ L.1) := by
  intro f
  induction f with
  | zero =>
    intro A Q _ hn hg L hL
    rw [show explore N 0 A Q = [(A, Q)] from rfl, List.mem_singleton] at hL
    subst hL
    exact ⟨hg, (List.nodup_append.mp hn).1, fun x hx => Or.inl hx, fun _ h => h⟩
  | succ f ih =>
    intro A Q hl hn hg L hL
    cases hp : pick N A Q with
    | none =>
      simp only [explore, hp, List.mem_singleton] at hL
      subst hL
      exact ⟨hg, (List.nodup_append.mp hn).1, fun x hx => Or.inl hx, fun _ h => h⟩
    | some r =>
      obtain ⟨Q₁, q, Q₂⟩ := r
      obtain ⟨hQe, hq, _⟩ := pick_some N A Q Q₁ q Q₂ hp
      simp only [explore, hp, List.mem_append] at hL
      subst hQe
      have hl' : (Q₁ ++ Q₂).length ≤ f := by
        simp only [List.length_append, List.length_cons] at hl ⊢; omega
      obtain ⟨n1, n2⟩ := nodup_excl hn
      rcases hL with hL | hL
      · obtain ⟨a, b, c, d⟩ := ih A _ hl' n1 hg L hL
        exact ⟨a, b, fun x hx => (c x hx).imp id mem_split, d⟩
      · obtain ⟨a, b, c, d⟩ := ih (q :: A) _ hl' n2 (.add q A hg hq) L hL
        refine ⟨a, b, fun x hx => ?_, fun x hx => d x (List.mem_cons_of_mem _ hx)⟩
        rcases c x hx with h | h
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inr (List.mem_append_right _ List.mem_cons_self)
          · exact Or.inl h
        · exact Or.inr (mem_split h)

abbrev NS (X Y : List Z4Plaq) : Prop := ¬ sameSupport (L := TL N) X Y

theorem tree_distinct : ∀ (f : Nat) (A Q : List Z4Plaq), Q.length ≤ f → (A ++ Q).Nodup →
    Grow N A → ((explore N f A Q).map Prod.fst).Pairwise (NS N) := by
  intro f
  induction f with
  | zero => intro A Q _ _ _; exact List.pairwise_singleton _ _
  | succ f ih =>
    intro A Q hl hn hg
    cases hp : pick N A Q with
    | none => simp only [explore, hp]; exact List.pairwise_singleton _ _
    | some r =>
      obtain ⟨Q₁, q, Q₂⟩ := r
      obtain ⟨hQe, hq, _⟩ := pick_some N A Q Q₁ q Q₂ hp
      simp only [explore, hp, List.map_append]
      subst hQe
      have hl' : (Q₁ ++ Q₂).length ≤ f := by
        simp only [List.length_append, List.length_cons] at hl ⊢; omega
      obtain ⟨n1, n2⟩ := nodup_excl hn
      obtain ⟨qa, qq⟩ := q_notin hn
      refine List.pairwise_append.mpr ⟨ih A _ hl' n1 hg, ih (q :: A) _ hl' n2 (.add q A hg hq),
        fun X hX Y hY hs => ?_⟩
      obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hX
      obtain ⟨L', hL', rfl⟩ := List.mem_map.mp hY
      have hqY := (leaf_inv N f _ _ hl' n2 (.add q A hg hq) L' hL').2.2.2 q List.mem_cons_self
      rcases (leaf_inv N f _ _ hl' n1 hg L hL).2.2.1 q (hs.2 q hqY) with h | h
      · exact qa h
      · exact qq h

theorem gas_inv : ∀ P : List Z4Plaq, P.Nodup →
    ∀ x, x ∈ gas N P → Grow N x ∧ x.Nodup ∧ ∀ p, p ∈ x → p ∈ P
  | [], _, _, hx => absurd hx List.not_mem_nil
  | r :: P, hP, x, hx => by
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hx
      obtain ⟨a, b, c, _⟩ := leaf_inv N _ [r] P (Nat.le_refl _) hP (.one r) L hL
      refine ⟨a, b, fun p hp => ?_⟩
      rcases c p hp with h | h
      · rw [List.mem_singleton.mp h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ h
    · obtain ⟨a, b, c⟩ := gas_inv P (List.nodup_cons.mp hP).2 x hx
      exact ⟨a, b, fun p hp => List.mem_cons_of_mem _ (c p hp)⟩

theorem gas_distinct : ∀ P : List Z4Plaq, P.Nodup → (gas N P).Pairwise (NS N)
  | [], _ => List.Pairwise.nil
  | r :: P, hP => by
    refine List.pairwise_append.mpr ⟨tree_distinct N _ [r] P (Nat.le_refl _) hP (.one r),
      gas_distinct P (List.nodup_cons.mp hP).2, fun X hX Y hY hs => ?_⟩
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hX
    have hr := (leaf_inv N _ [r] P (Nat.le_refl _) hP (.one r) L hL).2.2.2 r List.mem_cons_self
    exact (List.nodup_cons.mp hP).1
      ((gas_inv N P (List.nodup_cons.mp hP).2 Y hY).2.2 r (hs.1 r hr))

theorem grow_len : ∀ x : List Z4Plaq, Grow N x → 1 ≤ x.length
  | _, .one _ => Nat.le_refl 1
  | _, .add _ _ _ _ => Nat.succ_le_succ (Nat.zero_le _)

variable (P : List Z4Plaq) (hP : P.Nodup) (hbox : ∀ p, p ∈ P → p ∈ torusPlaquettes N)

/-- The link-connected gas as a torus box gas. -/
def linkBox : Z4BoxGas (torusChain N) where
  polys := gas N P
  N := P.length
  size_ok := fun X hX => ⟨grow_len N X (gas_inv N P hP X hX).1,
    len_le_of_sub X P (gas_inv N P hP X hX).2.1 (gas_inv N P hP X hX).2.2⟩
  nodup := fun X hX => (gas_inv N P hP X hX).2.1
  conn := fun X hX => grow_conn N X (gas_inv N P hP X hX).1
    (fun p hp => hbox p ((gas_inv N P hP X hX).2.2 p hp))
  distinct := gas_distinct N P hP

include hP in
theorem gas_nodup : (gas N P).Nodup :=
  (gas_distinct N P hP).imp fun {X Y} h e => by subst e; exact h ⟨fun _ h => h, fun _ h => h⟩

/-- The 24-neighbour cover of a cluster. -/
def nbA (a : List Z4Plaq) : List Z4Plaq := a.flatMap (nb N)

theorem nbA_len : ∀ a : List Z4Plaq, (nbA N a).length = 24 * a.length
  | [] => rfl
  | p :: a => by
    show (nb N p ++ nbA N a).length = _
    rw [List.length_append, nb_length, nbA_len a, List.length_cons]; omega

theorem sz_nbA (a : List Z4Plaq) :
    sz (BL := torusChain N) (nbA N a) ≤ 24 * sz (BL := torusChain N) a := by
  cases a with
  | nil => show 1 ≤ 24; decide
  | cons p a =>
    have hl := nbA_len N (p :: a)
    show sz (BL := torusChain N) (nbA N (p :: a)) ≤ 24 * (p :: a).length
    generalize nbA N (p :: a) = X at hl ⊢
    cases X with
    | nil => show 1 ≤ _; simp only [List.length_cons]; omega
    | cons y ys => show (y :: ys).length ≤ _; omega

theorem pow_mono_exp {c : Q'} (hc : (1 : Q') ≤ c) {a b : Nat} (h : a ≤ b) : c ^ a ≤ c ^ b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have h0 : (0 : Q') ≤ c := Q'.le_trans' _ _ _ (by decide) hc
  have hk : (1 : Q') ≤ c ^ k := by
    induction k with
    | zero => exact Q'.le_refl' 1
    | succ k ih =>
      show (1 : Q') ≤ c * c ^ k
      exact Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ 1 * 1) (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hc (by decide))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (ih (Nat.le_add_right _ _)) h0))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))) ?_
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hk (Q'.pow_nonneg _ h0 _)) ?_
  exact Q'.le_of_eqv (Q'.eqv_symm (YMGap.Continuum.HeatKernelPolymerActivityR1.pow_add' c a k))

include hP hbox in
/-- **Link grouping bound.** -/
theorem hgroupL (d0 : Z4Plaq) (a : List Z4Plaq) :
    prodm (fun x => 1 + etaZ ^ sz (BL := torusChain N) x) ((gas N P).filter (incL N a)) ≤
      five3 ^ (24 * sz (BL := torusChain N) a) := by
  have hf : ∀ x : List Z4Plaq, (1 : Q') ≤ 1 + etaZ ^ sz (BL := torusChain N) x :=
    fun x => Q'.add_le_self_of_nonneg _ _ (Q'.pow_nonneg _ (by decide) _)
  refine Q'.le_trans' _ _ _ (prodm_sub_le _ hf _ ((gas N P).filter (shareB (BL := torusChain N) (nbA N a)))
    ((gas_nodup N P hP).sublist List.filter_sublist) fun x hx => ?_) ?_
  · obtain ⟨hxg, hxi⟩ := List.mem_filter.mp hx
    obtain ⟨p, hp, q, hq, e⟩ := (incL_iff N a x).mp hxi
    have hqb := hbox q ((gas_inv N P hP x hxg).2.2 q hq)
    refine List.mem_filter.mpr ⟨hxg, (shareB_iff _ _).mpr ⟨q, ?_, hq⟩⟩
    exact List.mem_flatMap.mpr ⟨p, hp, mem_nb N hqb e⟩
  · exact Q'.le_trans' _ _ _ (z4_hgroup rfl d0 (linkBox N P hP hbox) (nbA N a))
      (pow_mono_exp (by decide) (sz_nbA N a))

end YMGap.Continuum.SU2LinkGasBox
