/-
# R1 commit 6: the Haar polymer identity on a finite box

ADDITIVE.  This is the combinatorial half.  With `root_step` (commit 5) it gives

  `polymer_identity`:  `∫ Π_{p∈P} W_p  ≈  Ξ(gas P)`, using link-incompatibility `incL`
  and the true activity `z(γ) = ∫ Π_{p∈γ} f_p`.

Here `W_p = c + f_p` with `c ≈ 1`.  The normalization is `∫ Π W` itself.  `P` is any finite
plaquette list whose links are coordinates of the box.  A Dirichlet box is the special case
where `P` is the set of interior plaquettes.

* `gas (p :: P') = (clusters explored from p in P') ++ gas P'`.  A polymer is a link-connected
  cluster, and it is computable.
* `leaf_spec`: every leaf `(A', R)` has `A' = new ++ A` with `new ⊆ Q`, and
  `R = Q.filter (¬ touch A')`.
* `explore_filter`: exploration commutes with deleting the plaquettes that touch a fixed
  cluster.
* `gas_filter`: `(gas Q).filter (cpt incL A') = gas (Q.filter (¬touch A'))`.
* `Xi_block`: the clusters rooted at the same `p` are pairwise incompatible.
-/

import YMGap.Continuum.SU2ClusterExplore
import YMGap.Continuum.SignedPolymerKP

namespace YMGap.Continuum.SU2PolymerIdentity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HaarDisjointSupport
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.SU2PlaqSupport
open YMGap.Continuum.SU2HaarAlgebra
open YMGap.Continuum.SU2ClusterExplore
open YMGap.Continuum.SignedPolymerKP (Xi Xi_nil Xi_cons cpt)
open YMGap.Continuum.ClusterCount4DProgress

variable (N : Nat)

theorem adj_self (p : Z4Plaq) : adj N p p = true :=
  List.any_eq_true.mpr ⟨_, List.mem_cons_self .., List.any_eq_true.mpr
    ⟨_, List.mem_cons_self .., decide_eq_true rfl⟩⟩

theorem touch_of_mem {A : List Z4Plaq} {q : Z4Plaq} (h : q ∈ A) : touch N A q = true :=
  List.any_eq_true.mpr ⟨q, h, adj_self N q⟩

theorem touch_append (B A : List Z4Plaq) (x : Z4Plaq) :
    touch N (B ++ A) x = (touch N B x || touch N A x) := List.any_append

theorem touch_mono {B A : List Z4Plaq} {x : Z4Plaq} (h : touch N A x = true) :
    touch N (B ++ A) x = true := by rw [touch_append, h, Bool.or_true]

/-- Link-incompatibility of two clusters. -/
def incL (A B : List Z4Plaq) : Bool := B.any (touch N A)

/-- The polymer gas of a plaquette list: clusters rooted at the first plaquette, then the rest. -/
def gas : List Z4Plaq → List (List Z4Plaq)
  | [] => []
  | p :: P' => (explore N P'.length [p] P').map Prod.fst ++ gas P'

theorem filter_nil_of {β : Type} (g : β → Bool) : ∀ l : List β, (∀ a ∈ l, g a = false) →
    l.filter g = []
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filter_cons_of_neg (by rw [h a (List.mem_cons_self ..)]; decide)]
    exact filter_nil_of g l fun b hb => h b (List.mem_cons_of_mem _ hb)

theorem filter_skip {Q₁ Q₂ : List Z4Plaq} {q : Z4Plaq} (g : Z4Plaq → Bool) (h : g q = false) :
    (Q₁ ++ q :: Q₂).filter g = (Q₁ ++ Q₂).filter g := by
  rw [List.filter_append, List.filter_append, List.filter_cons_of_neg (by rw [h]; decide)]

theorem leaf_spec : ∀ (f : Nat) (A Q : List Z4Plaq), Q.length ≤ f →
    ∀ L ∈ explore N f A Q, ∃ new : List Z4Plaq, L.1 = new ++ A ∧
      L.2 = Q.filter (fun x => !touch N L.1 x) := by
  intro f
  induction f with
  | zero =>
    intro A Q hl L hL
    have : Q = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst this
    rw [List.mem_singleton.mp hL]; exact ⟨[], rfl, rfl⟩
  | succ f ih =>
    intro A Q hl L hL
    cases hp : pick N A Q with
    | none =>
      simp only [explore, hp, List.mem_singleton] at hL
      subst hL
      refine ⟨[], rfl, (List.filter_eq_self.mpr fun x hx => ?_).symm⟩
      rw [pick_none N A Q hp x hx]; rfl
    | some r =>
      obtain ⟨Q₁, q, Q₂⟩ := r
      obtain ⟨hQe, hq, _⟩ := pick_some N A Q Q₁ q Q₂ hp
      simp only [explore, hp, List.mem_append] at hL
      subst hQe
      have hl' : (Q₁ ++ Q₂).length ≤ f := by
        simp only [List.length_append, List.length_cons] at hl ⊢; omega
      rcases hL with hL | hL
      · obtain ⟨new, h1, h2⟩ := ih A _ hl' L hL
        refine ⟨new, h1, ?_⟩
        rw [h2, filter_skip]; rw [h1, touch_mono N hq]; rfl
      · obtain ⟨new, h1, h2⟩ := ih (q :: A) _ hl' L hL
        refine ⟨new ++ [q], by rw [h1, List.append_assoc]; rfl, ?_⟩
        rw [h2, filter_skip]
        rw [touch_of_mem N (by rw [h1]; exact List.mem_append_right _ (List.mem_cons_self ..))]; rfl

theorem pick_filter (A : List Z4Plaq) (g : Z4Plaq → Bool) :
    ∀ Q Q₁ q Q₂, pick N A Q = some (Q₁, q, Q₂) → g q = true →
      pick N A (Q.filter g) = some (Q₁.filter g, q, Q₂.filter g)
  | [], _, _, _, h, _ => absurd h (by simp [pick])
  | y :: Q, Q₁, q, Q₂, h, hg => by
    unfold pick at h
    cases ht : touch N A y with
    | true =>
      rw [ht] at h
      simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [List.filter_cons_of_pos hg]
      simp only [pick, ht, ↓reduceIte, List.filter_nil]
    | false =>
      rw [ht] at h
      simp only [Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨⟨R₁, r, R₂⟩, hr, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have ih := pick_filter A g Q R₁ r R₂ hr hg
      cases hy : g y with
      | true =>
        rw [List.filter_cons_of_pos hy, List.filter_cons_of_pos hy]
        simp only [pick, ht, Bool.false_eq_true, ↓reduceIte, ih, Option.map_some]
      | false =>
        rw [List.filter_cons_of_neg (by rw [hy]; decide),
          List.filter_cons_of_neg (by rw [hy]; decide)]
        exact ih

/-- The cluster predicate "no plaquette touches `B`". -/
def away (B : List Z4Plaq) (x : Z4Plaq) : Bool := !touch N B x

theorem cpt_eq (B γ : List Z4Plaq) : cpt (incL N) B γ = γ.all (away N B) := by
  show (!γ.any (touch N B)) = _
  rw [List.not_any_eq_all_not]; rfl

theorem explore_filter (B : List Z4Plaq) : ∀ (f : Nat) (A Q : List Z4Plaq), Q.length ≤ f →
    A.all (away N B) = true → ∀ f', (Q.filter (away N B)).length ≤ f' →
    ((explore N f A Q).map Prod.fst).filter (fun γ => γ.all (away N B)) =
      (explore N f' A (Q.filter (away N B))).map Prod.fst := by
  intro f
  induction f with
  | zero =>
    intro A Q hl hA f' _
    have : Q = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst this
    cases f' <;> simp [explore, hA, pick]
  | succ f ih =>
    intro A Q hl hA f' hl'
    have none_case : (∀ x ∈ Q.filter (away N B), touch N A x = false) →
        [A] = (explore N f' A (Q.filter (away N B))).map Prod.fst := fun h => by
      have hn : pick N A (Q.filter (away N B)) = none := by
        cases hp : pick N A (Q.filter (away N B)) with
        | none => rfl
        | some r =>
          obtain ⟨h1, h2, _⟩ := pick_some N A _ r.1 r.2.1 r.2.2 hp
          rw [h r.2.1 (by rw [h1]; exact List.mem_append_right _ (List.mem_cons_self ..))] at h2
          exact absurd h2 (by decide)
      cases f' <;> simp [explore, hn]
    cases hp : pick N A Q with
    | none =>
      simp only [explore, hp, List.map_cons, List.map_nil]
      simp only [List.filter, hA]
      exact none_case fun x hx => pick_none N A Q hp x (List.mem_filter.mp hx).1
    | some r =>
      obtain ⟨Q₁, q, Q₂⟩ := r
      obtain ⟨hQe, _, _⟩ := pick_some N A Q Q₁ q Q₂ hp
      simp only [explore, hp, List.map_append, List.filter_append]
      subst hQe
      have hl1 : (Q₁ ++ Q₂).length ≤ f := by
        simp only [List.length_append, List.length_cons] at hl ⊢; omega
      cases hg : away N B q with
      | false =>
        have hnil : ((explore N f (q :: A) (Q₁ ++ Q₂)).map Prod.fst).filter
            (fun γ => γ.all (away N B)) = [] := filter_nil_of _ _ fun γ hγ => by
          obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hγ
          obtain ⟨new, h1, _⟩ := leaf_spec N f _ _ hl1 L hL
          rw [h1, List.all_append, List.all_cons, hg]; simp
        rw [hnil, List.append_nil, ih A _ hl1 hA f' (by rw [← filter_skip _ hg]; exact hl'),
          filter_skip _ hg]
      | true =>
        have hpf := pick_filter N A (away N B) _ Q₁ q Q₂ hp hg
        have hlen : (Q₁ ++ q :: Q₂).filter (away N B) =
            Q₁.filter (away N B) ++ q :: Q₂.filter (away N B) := by
          rw [List.filter_append, List.filter_cons_of_pos hg]
        obtain ⟨f'', rfl⟩ : ∃ f'', f' = f'' + 1 := ⟨f' - 1, by
          rw [hlen] at hl'; simp only [List.length_append, List.length_cons] at hl'; omega⟩
        have hl2 : ((Q₁ ++ Q₂).filter (away N B)).length ≤ f'' := by
          rw [hlen] at hl'; rw [List.filter_append]
          simp only [List.length_append, List.length_cons] at hl' ⊢; omega
        have hA' : (q :: A).all (away N B) = true := by rw [List.all_cons, hg, hA]; rfl
        simp only [explore, hpf, List.map_append]
        rw [ih A _ hl1 hA f'' hl2, ih (q :: A) _ hl1 hA' f'' hl2, List.filter_append]

theorem gas_filter (B : List Z4Plaq) : ∀ Q : List Z4Plaq,
    (gas N Q).filter (cpt (incL N) B) = gas N (Q.filter (away N B))
  | [] => rfl
  | p :: Q => by
    have hc : cpt (incL N) B = fun γ => γ.all (away N B) := funext (cpt_eq N B)
    show ((explore N Q.length [p] Q).map Prod.fst ++ gas N Q).filter _ = _
    rw [List.filter_append, gas_filter B Q, hc]
    cases hg : away N B p with
    | false =>
      rw [List.filter_cons_of_neg (by rw [hg]; decide)]
      rw [filter_nil_of _ _ fun γ hγ => ?_, List.nil_append]
      obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hγ
      obtain ⟨new, h1, _⟩ := leaf_spec N _ _ _ (Nat.le_refl _) L hL
      rw [h1, List.all_append, List.all_cons, hg]; simp
    | true =>
      rw [List.filter_cons_of_pos hg]
      show _ = (explore N _ [p] _).map Prod.fst ++ gas N _
      rw [explore_filter N B Q.length [p] Q (Nat.le_refl _) (by simp [hg]) _ (Nat.le_refl _)]

/-- Clusters that share a member are incompatible, so `Ξ` splits off a block of them. -/
theorem Xi_block (z : List Z4Plaq → Q') (G : List (List Z4Plaq)) : ∀ Ls : List (List Z4Plaq),
    (∀ A ∈ Ls, ∀ B ∈ Ls, incL N A B = true) →
    (Xi z (incL N) (Ls ++ G)).eqv
      (Xi z (incL N) G + sm (fun A => z A * Xi z (incL N) (G.filter (cpt (incL N) A))) Ls)
  | [], _ => az _
  | A :: Ls, h => by
    rw [List.cons_append, Xi_cons, List.filter_append,
      filter_nil_of _ _ (fun B hB => by
        show (!incL N A B) = false
        rw [h A (List.mem_cons_self ..) B (List.mem_cons_of_mem _ hB)]; rfl), List.nil_append]
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Xi_block z G Ls fun a ha b hb =>
      h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) (Q'.eqv_refl _)) ?_
    let V := YMGap.Continuum.RingNormaliser.PolyExpr.var
    exact YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (V 0) (V 1)) (V 2)) (.add (V 0) (.add (V 2) (V 1))) (by decide)
      (fun | 0 => Xi z (incL N) G | 1 => sm (fun A => z A * Xi z (incL N) (G.filter (cpt (incL N) A))) Ls
           | _ => z A * Xi z (incL N) (G.filter (cpt (incL N) A)))

/-! ## The identity -/

variable (n : Nat) (links : List Z4Link) (F : Z4Plaq → RatPoly) (c : Q') (hc : c.eqv 1)
  (hF : ∀ p, FreeOff (idxB links N p) false (F p))

include hc hF in
/-- **Haar polymer identity.**  `∫ Π_{p∈P} (c + f_p) ≈ Ξ(gas P)`, with link-incompatibility
and true activities `z(γ) = ∫ Π_{p∈γ} f_p`. -/
theorem polymer_identity : ∀ (k : Nat) (P : List Z4Plaq), P.length ≤ k →
    (∀ p ∈ P, Lk links N p) →
    (quaternionHaar n (prodPoly (W F c) P)).eqv
      (Xi (fun γ => quaternionHaar n (prodPoly F γ)) (incL N) (gas N P)) := by
  intro k
  induction k with
  | zero =>
    intro P hl _
    have : P = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst this
    show (quaternionHaar n polyOne).eqv (Xi _ _ [])
    rw [Xi_nil]; exact YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.quaternionHaar_polyOne n
  | succ k ih =>
    intro P hl hP
    cases P with
    | nil => exact ih [] (Nat.zero_le _) hP
    | cons p₀ P' =>
      have hl' : P'.length ≤ k := by simp only [List.length_cons] at hl; omega
      have hP' : ∀ p ∈ P', Lk links N p := fun p hp => hP p (List.mem_cons_of_mem _ hp)
      refine Q'.eqv_trans _ _ _ (root_step n links N F c hc hF p₀ P' hP) ?_
      have spec := leaf_spec N P'.length [p₀] P' (Nat.le_refl _)
      have hmem : ∀ A ∈ (explore N P'.length [p₀] P').map Prod.fst, p₀ ∈ A := fun A hA => by
        obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hA
        obtain ⟨new, h1, _⟩ := spec L hL
        rw [h1]; exact List.mem_append_right _ (List.mem_singleton_self _)
      refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Xi_block N _ _ _ fun A hA B hB =>
        List.any_eq_true.mpr ⟨p₀, hmem B hB, touch_of_mem N (hmem A hA)⟩))
      rw [sm_map]
      refine Q'.add_eqv_congr' (ih P' hl' hP') (sm_congr _ fun L hL => ?_)
      obtain ⟨_, _, h2⟩ := spec L hL
      refine Q'.mul_eqv_congr_left _ _ _ ?_
      show (quaternionHaar n (prodPoly (W F c) L.2)).eqv _
      rw [gas_filter, h2]
      exact ih _ (Nat.le_trans (List.length_filter_le _ _) hl')
        (fun p hp => hP' p (List.mem_filter.mp hp).1)

open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (torusIntegrand plaqWeight polyPartition coeffW
  coeffW_zero_eqv)
open YMGap.Continuum.SU2HaarL1Activity (fPoly)

theorem integrand_eq (w : Q') (M : Nat) (links : List Z4Link) : ∀ P : List Z4Plaq,
    torusIntegrand w M links N P =
      prodPoly (W (fun p => fPoly w links N p M) (coeffW w 0 * 1)) P
  | [] => rfl
  | p :: P => by
    show polyMul _ _ = polyMul _ _
    rw [integrand_eq w M links P, plaqWeight_split]; rfl

/-- **R1 identity for the multi-link SU(2) Gibbs partition function** on any finite plaquette
list whose links are box coordinates.  The left side is the repo's `polyPartition`, the Haar
integral of `Π_p plaqWeight`.  The right side is `Ξ` of the link-connected polymer gas with
link-incompatibility and true activities `z(γ) = ∫ Π_{p∈γ} f_p`. -/
theorem polyPartition_eq_Xi (w : Q') (M : Nat) (links : List Z4Link) (P : List Z4Plaq)
    (hL : ∀ p ∈ P, Lk links N p) :
    (polyPartition w M links N P).eqv
      (Xi (fun γ => quaternionHaar links.length (prodPoly (fun p => fPoly w links N p M) γ))
        (incL N) (gas N P)) := by
  show (quaternionHaar links.length (torusIntegrand w M links N P)).eqv _
  rw [integrand_eq]
  exact polymer_identity N links.length links _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (coeffW_zero_eqv w))
    (fun p => fPoly_free w links N p M) P.length P (Nat.le_refl _) hL

end YMGap.Continuum.SU2PolymerIdentity
