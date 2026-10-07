/-
# Wilson action on the periodic Z⁴ torus, with translation invariance

ADDITIVE.  Group carrier: the repo's `RepTheory.ConstructiveGroup` (setoid
group, choice-free).  A gauge configuration is `U : Z4Link → G.Carrier`
(only values on `torusLinks N` enter).  The plaquette holonomy of `(w, P)`,
`P` spanning `(a, b)`, is the ordered product around the periodic boundary
`torusEdgesOf N (w,P)`:

  `U_p = U(w,a) · U(w+â, b) · U(w+b̂, a)⁻¹ · U(w, b)⁻¹`   (`+` = `tAdd`).

The action is `S_f(U) = Σ_{p ∈ torusPlaquettes N} f(U_p)` for a weight
`f : G.Carrier → Q'`.  Since `Q'` carries no `Re tr`, `f` is ABSTRACT: the
Wilson choice is `f(g) = 1 − Re tr(g)/n` (for SU(2) on rational quaternions,
`1 − x₀`), but the theorems hold for every `f`.  `S_f(U)` is a computable `Q'`
value, so `S_f(U) ≤ c` is decidable.

* `torusPlaquettes_shift_perm`: periodic translation permutes the torus
  plaquette list (general `N ≥ 1`), via an explicit inverse shift.
* `holonomy_shift`: the holonomy of the translated configuration at `p` is
  the holonomy of `U` at the translated plaquette (definitional after
  `tAdd_tShift`).
* `wilsonAction_shift_invariant`: `S_f(U ∘ shift_t) ≈ S_f(U)` for all `t`.

**U(1) test.** Group-blind: definitions and invariance hold for any group
(U(1) included).  This is PLUMBING (the configuration space and action), not
a gap statement.  Choice-free; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.Z4TorusGeometry
import YMGap.Continuum.RingNormaliser
import YMGap.RepTheory.ConstructiveGroup

namespace YMGap.Continuum.TorusWilsonAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4TorusGeometry
open YMGap.RepTheory

/-! ## 1. Inverse translation and the plaquette permutation -/

/-- Componentwise inverse shift `N − t_i % N`. -/
def invShift (N : Nat) (t : Z4Vertex) : Z4Vertex :=
  (N - t.1 % N, N - t.2.1 % N, N - t.2.2.1 % N, N - t.2.2.2 % N)

theorem cancel_mod {N : Nat} (hN : 0 < N) {x : Nat} (hx : x < N) (t : Nat) :
    (x + (t + (N - t % N))) % N = x ∧ (x + ((N - t % N) + t)) % N = x := by
  have h1 := Nat.mod_add_div t N
  have h2 := Nat.mod_lt t hN
  have key : t + (N - t % N) = N * (t / N + 1) := by
    rw [Nat.mul_succ]
    generalize N * (t / N) = M at h1 ⊢
    generalize t % N = q at h1 h2 ⊢
    omega
  have k1 : (x + (t + (N - t % N))) % N = x := by
    rw [key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  refine ⟨k1, ?_⟩
  rw [Nat.add_comm (N - t % N) t]; exact k1

theorem tShift_invShift_left {N : Nat} (hN : 0 < N) (t : Z4Vertex) {v : Z4Vertex}
    (hv : InBox N v) : tShift N (invShift N t) (tShift N t v) = v := by
  rw [tShift_comp]
  obtain ⟨a, b, c, d⟩ := v
  obtain ⟨h1, h2, h3, h4⟩ := hv
  show ((a + (t.1 + (N - t.1 % N))) % N, (b + (t.2.1 + (N - t.2.1 % N))) % N,
    (c + (t.2.2.1 + (N - t.2.2.1 % N))) % N, (d + (t.2.2.2 + (N - t.2.2.2 % N))) % N) = _
  rw [(cancel_mod hN h1 _).1, (cancel_mod hN h2 _).1, (cancel_mod hN h3 _).1,
    (cancel_mod hN h4 _).1]

theorem tShift_invShift_right {N : Nat} (hN : 0 < N) (t : Z4Vertex) {v : Z4Vertex}
    (hv : InBox N v) : tShift N t (tShift N (invShift N t) v) = v := by
  rw [tShift_comp]
  obtain ⟨a, b, c, d⟩ := v
  obtain ⟨h1, h2, h3, h4⟩ := hv
  show ((a + ((N - t.1 % N) + t.1)) % N, (b + ((N - t.2.1 % N) + t.2.1)) % N,
    (c + ((N - t.2.2.1 % N) + t.2.2.1)) % N, (d + ((N - t.2.2.2 % N) + t.2.2.2)) % N) = _
  rw [(cancel_mod hN h1 _).2, (cancel_mod hN h2 _).2, (cancel_mod hN h3 _).2,
    (cancel_mod hN h4 _).2]

/-- Translation of a plaquette. -/
def shiftPlaq (N : Nat) (t : Z4Vertex) (p : Z4Plaq) : Z4Plaq := (tShift N t p.1, p.2)

theorem nodup_map_on {α β : Type} (f : α → β) :
    ∀ {xs : List α}, (∀ x, x ∈ xs → ∀ y, y ∈ xs → f x = f y → x = y) →
      xs.Nodup → (xs.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hinj, h => by
      have hp := List.nodup_cons.mp h
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_map_on f (fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha)
        b (List.mem_cons_of_mem _ hb)) hp.2⟩
      intro hmem
      obtain ⟨y, hy, heq⟩ := List.mem_map.mp hmem
      have := hinj y (List.mem_cons_of_mem _ hy) x List.mem_cons_self heq
      exact hp.1 (this ▸ hy)

theorem mem_shifted_plaquettes {N : Nat} (hN : 0 < N) (t : Z4Vertex) (p : Z4Plaq) :
    p ∈ (torusPlaquettes N).map (shiftPlaq N t) ↔ p ∈ torusPlaquettes N := by
  obtain ⟨v, P⟩ := p
  constructor
  · intro h
    obtain ⟨⟨w, Q⟩, _, he⟩ := List.mem_map.mp h
    rw [← he]
    exact (mem_torusPlaquettes N _ Q).mpr (tShift_inBox hN t w)
  · intro h
    have hv := (mem_torusPlaquettes N v P).mp h
    refine List.mem_map.mpr ⟨(tShift N (invShift N t) v, P),
      (mem_torusPlaquettes N _ P).mpr (tShift_inBox hN _ v), ?_⟩
    show (tShift N t (tShift N (invShift N t) v), P) = (v, P)
    rw [tShift_invShift_right hN t hv]

/-- Remove the first occurrence (choice-free; core `erase`/`perm_iff_count`
lemmas pull in the choice axiom). -/
def rem {α : Type} [DecidableEq α] (a : α) : List α → List α
  | [] => []
  | b :: t => if a = b then t else b :: rem a t

theorem rem_sub {α : Type} [DecidableEq α] (a x : α) :
    ∀ {l : List α}, x ∈ rem a l → x ∈ l
  | [], h => h
  | b :: t, h => by
      rcases Decidable.em (a = b) with hab | hab
      · rw [rem, if_pos hab] at h; exact List.mem_cons_of_mem _ h
      · rw [rem, if_neg hab] at h
        rcases List.mem_cons.mp h with h | h
        · rw [h]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (rem_sub a x h)

theorem mem_rem_of_ne {α : Type} [DecidableEq α] (a x : α) (hxa : x ≠ a) :
    ∀ {l : List α}, x ∈ l → x ∈ rem a l
  | [], h => h
  | b :: t, h => by
      rcases Decidable.em (a = b) with hab | hab
      · rw [rem, if_pos hab]
        rcases List.mem_cons.mp h with h | h
        · exact absurd (h.trans hab.symm) hxa
        · exact h
      · rw [rem, if_neg hab]
        rcases List.mem_cons.mp h with h | h
        · rw [h]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem_rem_of_ne a x hxa h)

theorem not_mem_rem {α : Type} [DecidableEq α] (a : α) :
    ∀ {l : List α}, l.Nodup → a ∉ rem a l
  | [], _, h => by cases h
  | b :: t, hn, h => by
      have hp := List.nodup_cons.mp hn
      rcases Decidable.em (a = b) with hab | hab
      · rw [rem, if_pos hab] at h; exact hp.1 (hab ▸ h)
      · rw [rem, if_neg hab] at h
        rcases List.mem_cons.mp h with h | h
        · exact hab h
        · exact not_mem_rem a hp.2 h

theorem rem_nodup {α : Type} [DecidableEq α] (a : α) :
    ∀ {l : List α}, l.Nodup → (rem a l).Nodup
  | [], h => h
  | b :: t, hn => by
      have hp := List.nodup_cons.mp hn
      rcases Decidable.em (a = b) with hab | hab
      · rw [rem, if_pos hab]; exact hp.2
      · rw [rem, if_neg hab]
        exact List.nodup_cons.mpr ⟨fun h => hp.1 (rem_sub a b h), rem_nodup a hp.2⟩

theorem perm_cons_rem {α : Type} [DecidableEq α] (a : α) :
    ∀ {l : List α}, a ∈ l → l.Perm (a :: rem a l)
  | [], h => by cases h
  | b :: t, h => by
      rcases Decidable.em (a = b) with hab | hab
      · rw [rem, if_pos hab, hab]
      · rw [rem, if_neg hab]
        have ht : a ∈ t := by
          rcases List.mem_cons.mp h with h | h
          · exact absurd h hab
          · exact h
        exact ((perm_cons_rem a ht).cons b).trans (List.Perm.swap a b _)

/-- Two duplicate-free lists with the same members are permutations (choice-free). -/
theorem perm_of_nodup_mem {α : Type} [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, l₁.Nodup → l₂.Nodup → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁.Perm l₂
  | [], [], _, _, _ => List.Perm.nil
  | [], b :: _, _, _, h => by
      have := (h b).mpr List.mem_cons_self
      cases this
  | a :: t, l₂, h1, h2, h => by
      have hp := List.nodup_cons.mp h1
      have ha : a ∈ l₂ := (h a).mp List.mem_cons_self
      have ih : t.Perm (rem a l₂) := by
        refine perm_of_nodup_mem hp.2 (rem_nodup a h2) ?_
        intro x
        constructor
        · intro hx
          exact mem_rem_of_ne a x (fun e => hp.1 (e ▸ hx))
            ((h x).mp (List.mem_cons_of_mem _ hx))
        · intro hx
          have hx2 := (h x).mpr (rem_sub a x hx)
          rcases List.mem_cons.mp hx2 with e | e
          · exact absurd (e ▸ hx) (not_mem_rem a h2)
          · exact e
      exact (ih.cons a).trans (perm_cons_rem a ha).symm

/-- **Translation permutes the torus plaquettes** (`N ≥ 1`, any `t`). -/
theorem torusPlaquettes_shift_perm {N : Nat} (hN : 0 < N) (t : Z4Vertex) :
    ((torusPlaquettes N).map (shiftPlaq N t)).Perm (torusPlaquettes N) := by
  have hn2 := torusPlaquettes_nodup N
  have hn1 : ((torusPlaquettes N).map (shiftPlaq N t)).Nodup := by
    refine nodup_map_on _ ?_ hn2
    intro ⟨v, P⟩ hx ⟨w, Q⟩ hy he
    have hv := (mem_torusPlaquettes N v P).mp hx
    have hw := (mem_torusPlaquettes N w Q).mp hy
    have e1 : tShift N t v = tShift N t w := congrArg Prod.fst he
    have e2 : P = Q := congrArg Prod.snd he
    have e3 := congrArg (tShift N (invShift N t)) e1
    rw [tShift_invShift_left hN t hv, tShift_invShift_left hN t hw] at e3
    rw [e3, e2]
  exact perm_of_nodup_mem hn1 hn2 (mem_shifted_plaquettes hN t)

/-! ## 2. Sums over permuted lists -/

/-- Finite `Q'` sum of a list. -/
def qsum : List Q' → Q'
  | [] => 0
  | a :: l => a + qsum l

theorem qsum_perm {l₁ l₂ : List Q'} (h : l₁.Perm l₂) : (qsum l₁).eqv (qsum l₂) := by
  induction h with
  | nil => exact Q'.eqv_refl _
  | cons x _ ih => exact Q'.add_eqv_congr_left _ _ _ ih
  | swap x y l =>
      show (y + (x + qsum l)).eqv (x + (y + qsum l))
      exact poly_identity_of_normal_eq
        (.add (.var 0) (.add (.var 1) (.var 2))) (.add (.var 1) (.add (.var 0) (.var 2)))
        (by decide) (fun | 0 => y | 1 => x | _ => qsum l)
  | trans _ _ ih1 ih2 => exact Q'.eqv_trans _ _ _ ih1 ih2

/-! ## 3. Holonomy and the Wilson action -/

/-- A gauge configuration: one group element per link. -/
abbrev GaugeConfig (G : ConstructiveGroup.{0}) : Type := Z4Link → G.Carrier

/-- Plaquette holonomy around the periodic boundary `torusEdgesOf N p`. -/
def holonomy (G : ConstructiveGroup.{0}) (N : Nat) (U : GaugeConfig G) (p : Z4Plaq) :
    G.Carrier :=
  G.mul (G.mul (U (p.1, (dirsOf p.2).1)) (U (tAdd N p.1 (dirsOf p.2).1, (dirsOf p.2).2)))
    (G.mul (G.inv (U (tAdd N p.1 (dirsOf p.2).2, (dirsOf p.2).1)))
      (G.inv (U (p.1, (dirsOf p.2).2))))

/-- The holonomy reads exactly the four periodic boundary links. -/
theorem holonomy_links (N : Nat) (p : Z4Plaq) :
    torusEdgesOf N p = [(p.1, (dirsOf p.2).1), (p.1, (dirsOf p.2).2),
      (tAdd N p.1 (dirsOf p.2).2, (dirsOf p.2).1),
      (tAdd N p.1 (dirsOf p.2).1, (dirsOf p.2).2)] := rfl

/-- Wilson-type action `S_f(U) = Σ_p f(U_p)` over the torus plaquettes, for an
abstract weight `f` (Wilson: `f g = 1 − Re tr g / n`). -/
def wilsonAction (G : ConstructiveGroup.{0}) (N : Nat) (f : G.Carrier → Q')
    (U : GaugeConfig G) : Q' :=
  qsum ((torusPlaquettes N).map fun p => f (holonomy G N U p))

/-- Translated configuration `(t·U)(ℓ) = U(ℓ + t)`. -/
def shiftConfig (G : ConstructiveGroup.{0}) (N : Nat) (t : Z4Vertex) (U : GaugeConfig G) :
    GaugeConfig G := fun ℓ => U (shiftLink N t ℓ)

theorem holonomy_shift (G : ConstructiveGroup.{0}) (N : Nat) (t : Z4Vertex)
    (U : GaugeConfig G) (p : Z4Plaq) :
    holonomy G N (shiftConfig G N t U) p = holonomy G N U (shiftPlaq N t p) := by
  obtain ⟨w, P⟩ := p
  simp only [holonomy, shiftConfig, shiftLink, shiftPlaq, tAdd_tShift]

/-- **Translation invariance of the torus Wilson action** (`N ≥ 1`, every
translation `t`, every weight `f`, every group). -/
theorem wilsonAction_shift_invariant (G : ConstructiveGroup.{0}) {N : Nat} (hN : 0 < N)
    (f : G.Carrier → Q') (t : Z4Vertex) (U : GaugeConfig G) :
    (wilsonAction G N f (shiftConfig G N t U)).eqv (wilsonAction G N f U) := by
  unfold wilsonAction
  have hfun : (fun p => f (holonomy G N (shiftConfig G N t U) p)) =
      (fun p => f (holonomy G N U p)) ∘ shiftPlaq N t := by
    funext p; exact congrArg f (holonomy_shift G N t U p)
  rw [hfun, ← List.map_map]
  exact qsum_perm ((torusPlaquettes_shift_perm hN t).map _)

end YMGap.Continuum.TorusWilsonAction
