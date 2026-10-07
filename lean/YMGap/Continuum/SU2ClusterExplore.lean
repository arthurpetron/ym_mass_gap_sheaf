/-
# R1 commit 5: cluster exploration of the multi-link Haar integral

ADDITIVE.  `W_p = c + f_p` (`c ≈ 1`).  Expanding one frontier plaquette at a time gives the
analytic half of the polymer identity.

* `adj p q`: `p` and `q` share a link.  `touch A q`: `q` shares a link with some `a ∈ A`.
* `pick A Q`: the first `q ∈ Q` touching `A`, with `Q = Q₁ ++ q :: Q₂`.
* `explore f A Q` is a binary tree of leaves `(A', R)`.  At each pick it either excludes q
  or adds it to the cluster.  It stops when nothing in the frontier touches the cluster.
* `explore_haar`: `∫ (Π_A f)(Π_Q W) ≈ Σ_{(A',R)} ∫Π_{A'} f · ∫Π_R W`, for fuel `≥ |Q|`.
  The leaf factorization is `polymer_factor` (link-disjoint ⇒ block-disjoint).
* `root_step`: `Z(p₀ :: P') ≈ Z(P') + Σ_{(A',R) ∈ explore [p₀] P'} ∫Π_{A'} f · Z(R)`.
-/

import YMGap.Continuum.SU2HaarAlgebra

namespace YMGap.Continuum.SU2ClusterExplore

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (quaternionHaar_append)
open YMGap.Continuum.SU2HaarDisjointSupport
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.SU2PlaqSupport
open YMGap.Continuum.SU2HaarAlgebra
open YMGap.Continuum.ClusterCount4DProgress

/-! ## Adjacency and exploration -/

def adj (N : Nat) (p q : Z4Plaq) : Bool :=
  (plaqLinks N p).any fun ℓ => (plaqLinks N q).any fun ℓ' => decide (ℓ = ℓ')

def touch (N : Nat) (A : List Z4Plaq) (q : Z4Plaq) : Bool := A.any fun a => adj N a q

def pick (N : Nat) (A : List Z4Plaq) : List Z4Plaq → Option (List Z4Plaq × Z4Plaq × List Z4Plaq)
  | [] => none
  | x :: Q => if touch N A x then some ([], x, Q)
      else (pick N A Q).map fun r => (x :: r.1, r.2.1, r.2.2)

def explore (N : Nat) : Nat → List Z4Plaq → List Z4Plaq → List (List Z4Plaq × List Z4Plaq)
  | 0, A, Q => [(A, Q)]
  | f + 1, A, Q => match pick N A Q with
    | none => [(A, Q)]
    | some (Q₁, q, Q₂) => explore N f A (Q₁ ++ Q₂) ++ explore N f (q :: A) (Q₁ ++ Q₂)

theorem pick_none (N : Nat) (A : List Z4Plaq) : ∀ Q, pick N A Q = none → ∀ x ∈ Q, touch N A x = false
  | [], _, x, hx => absurd hx List.not_mem_nil
  | y :: Q, h, x, hx => by
    unfold pick at h
    cases ht : touch N A y with
    | true => rw [ht] at h; exact absurd h (by simp)
    | false =>
      rw [ht] at h
      simp only [Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ht
      · exact pick_none N A Q h x hx

theorem pick_some (N : Nat) (A : List Z4Plaq) : ∀ Q Q₁ q Q₂, pick N A Q = some (Q₁, q, Q₂) →
    Q = Q₁ ++ q :: Q₂ ∧ touch N A q = true ∧ ∀ x ∈ Q₁, touch N A x = false
  | [], _, _, _, h => absurd h (by simp [pick])
  | y :: Q, Q₁, q, Q₂, h => by
    unfold pick at h
    cases ht : touch N A y with
    | true =>
      rw [ht] at h
      simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, ht, fun _ hx => absurd hx List.not_mem_nil⟩
    | false =>
      rw [ht] at h
      simp only [Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨⟨R₁, r, R₂⟩, hr, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨h1, h2, h3⟩ := pick_some N A Q R₁ r R₂ hr
      refine ⟨by rw [h1]; rfl, h2, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ht
      · exact h3 x hx

/-! ## Leaf factorization -/

variable (n : Nat) (links : List Z4Link) (N : Nat)

/-- All four links of `p` are coordinates of the box. -/
def Lk (p : Z4Plaq) : Prop := ∀ ℓ, ℓ ∈ plaqLinks N p → ℓ ∈ links

theorem leaf_disj (A Q : List Z4Plaq) (hA : ∀ p ∈ A, Lk links N p) (hQ : ∀ p ∈ Q, Lk links N p)
    (ht : ∀ x ∈ Q, touch N A x = false) (k : Nat) (hk : setB links N A k = true) :
    setB links N Q k = false := by
  obtain ⟨a, ha, hak⟩ := List.any_eq_true.mp hk
  cases h : setB links N Q k with
  | false => rfl
  | true =>
    obtain ⟨x, hx, hxk⟩ := List.any_eq_true.mp h
    have hf : idxB links N x k = false := idx_disj links N a x (hA a ha) (hQ x hx) (fun ℓ hℓ hℓ' => by
      have : touch N A x = true :=
        List.any_eq_true.mpr ⟨a, ha, List.any_eq_true.mpr ⟨ℓ, hℓ,
          List.any_eq_true.mpr ⟨ℓ, hℓ', decide_eq_true rfl⟩⟩⟩
      rw [ht x hx] at this; exact absurd this (by decide)) k hak
    rw [hf] at hxk; exact absurd hxk (by decide)

variable (F : Z4Plaq → RatPoly) (c : Q') (hc : c.eqv 1)
  (hF : ∀ p, FreeOff (idxB links N p) false (F p))

/-- The plaquette weight `c + f_p`. -/
def W (p : Z4Plaq) : RatPoly := [([], c)] ++ F p

include hF in
theorem W_free (p : Z4Plaq) : FreeOff (idxB links N p) false (W F c p) :=
  free_add _ _ (fun s hs k _ c' _ => by rw [List.mem_singleton.mp hs]; rfl) (hF p)

/-- Value of a leaf `(A', R)`. -/
theorem az (x : Q') : x.eqv (x + 0) := by
  let V := YMGap.Continuum.RingNormaliser.PolyExpr.var
  exact YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq (V 0)
    (YMGap.Continuum.RingNormaliser.PolyExpr.add (V 0) (.const 0)) (by decide) (fun _ => x)

def leafVal (L : List Z4Plaq × List Z4Plaq) : Q' :=
  quaternionHaar n (prodPoly F L.1) * quaternionHaar n (prodPoly (W F c) L.2)

theorem haar_mul_append (C X Y : RatPoly) :
    (quaternionHaar n (polyMul C (X ++ Y))).eqv
      (quaternionHaar n (polyMul C X) + quaternionHaar n (polyMul C Y)) := by
  refine Q'.eqv_trans _ _ _ (pe_haar n (pe_comm n C _)) ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.add_eqv_congr' (pe_haar n (pe_comm n X C))
    (pe_haar n (pe_comm n Y C)))
  show (quaternionHaar n ((X ++ Y).flatMap _)).eqv _
  rw [List.flatMap_append]
  exact quaternionHaar_append n _ _

include hc in
theorem W_split (p : Z4Plaq) (R : RatPoly) :
    PE n (polyMul (W F c p) R) (R ++ polyMul (F p) R) := by
  show PE n (([([], c)] ++ F p).flatMap _) _
  rw [List.flatMap_append]
  exact pe_append n (pe_const n c hc R) (pe_refl n _)

include hc hF in
theorem explore_haar : ∀ (f : Nat) (A Q : List Z4Plaq), Q.length ≤ f →
    (∀ p ∈ A, Lk links N p) → (∀ p ∈ Q, Lk links N p) →
    (quaternionHaar n (polyMul (prodPoly F A) (prodPoly (W F c) Q))).eqv
      (sm (leafVal n F c) (explore N f A Q)) := by
  have leaf : ∀ A Q : List Z4Plaq, (∀ p ∈ A, Lk links N p) → (∀ p ∈ Q, Lk links N p) →
      (∀ x ∈ Q, touch N A x = false) →
      (quaternionHaar n (polyMul (prodPoly F A) (prodPoly (W F c) Q))).eqv
        (sm (leafVal n F c) [(A, Q)]) := fun A Q hA hQ ht =>
    Q'.eqv_trans _ _ _ (polymer_factor n links N F (W F c) hF (W_free links N F c hF) A Q
      (leaf_disj links N A Q hA hQ ht)) (az _)
  intro f
  induction f with
  | zero =>
    intro A Q hl hA hQ
    have : Q = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst this
    exact leaf A [] hA hQ (fun _ hx => absurd hx List.not_mem_nil)
  | succ f ih =>
    intro A Q hl hA hQ
    cases hp : pick N A Q with
    | none =>
      simp only [explore, hp]
      exact leaf A Q hA hQ (pick_none N A Q hp)
    | some r =>
      obtain ⟨Q₁, q, Q₂⟩ := r
      obtain ⟨hQe, _, _⟩ := pick_some N A Q Q₁ q Q₂ hp
      simp only [explore, hp]
      subst hQe
      have hl' : (Q₁ ++ Q₂).length ≤ f := by
        simp only [List.length_append, List.length_cons] at hl ⊢; omega
      have hQ' : ∀ p ∈ Q₁ ++ Q₂, Lk links N p := fun p hp =>
        hQ p (List.mem_append.mpr ((List.mem_append.mp hp).imp id (List.mem_cons_of_mem _)))
      have hq' : Lk links N q := hQ q (List.mem_append.mpr (Or.inr (List.mem_cons_self ..)))
      refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (sm_append _ _ _))
      have h1 : PE n (polyMul (prodPoly F A) (prodPoly (W F c) (Q₁ ++ q :: Q₂)))
          (polyMul (prodPoly F A) (prodPoly (W F c) (Q₁ ++ Q₂) ++
            polyMul (F q) (prodPoly (W F c) (Q₁ ++ Q₂)))) :=
        pe_mulL n _ (pe_trans n (pe_extract n (W F c) q Q₂ Q₁) (W_split n F c hc q _))
      refine Q'.eqv_trans _ _ _ (pe_haar n h1) ?_
      refine Q'.eqv_trans _ _ _ (haar_mul_append n _ _ _)
        (Q'.add_eqv_congr' (ih A _ hl' hA hQ') ?_)
      have h2 : PE n (polyMul (prodPoly F A) (polyMul (F q) (prodPoly (W F c) (Q₁ ++ Q₂))))
          (polyMul (prodPoly F (q :: A)) (prodPoly (W F c) (Q₁ ++ Q₂))) :=
        pe_trans n (pe_symm n (pe_assoc n _ _ _)) (pe_mulR n _ (pe_comm n _ _))
      refine Q'.eqv_trans _ _ _ (pe_haar n h2) (ih (q :: A) _ hl' (fun p hp => ?_) hQ')
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hq'
      · exact hA p hp

include hc hF in
/-- One root step of the polymer identity. -/
theorem root_step (p₀ : Z4Plaq) (P' : List Z4Plaq) (hP : ∀ p ∈ p₀ :: P', Lk links N p) :
    (quaternionHaar n (prodPoly (W F c) (p₀ :: P'))).eqv
      (quaternionHaar n (prodPoly (W F c) P') + sm (leafVal n F c) (explore N P'.length [p₀] P')) := by
  show (quaternionHaar n (polyMul (W F c p₀) (prodPoly (W F c) P'))).eqv _
  refine Q'.eqv_trans _ _ _ (pe_haar n (W_split n F c hc p₀ _)) ?_
  refine Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _) (Q'.add_eqv_congr' (Q'.eqv_refl _) ?_)
  refine Q'.eqv_trans _ _ _ (pe_haar n (pe_mulR n _ (pe_symm n (pe_one n (F p₀))))) ?_
  refine explore_haar n links N F c hc hF P'.length [p₀] P' (Nat.le_refl _) (fun p hp => ?_)
    (fun p hp => hP p (List.mem_cons_of_mem _ hp))
  rw [List.mem_singleton.mp hp]; exact hP p₀ (List.mem_cons_self ..)

end YMGap.Continuum.SU2ClusterExplore
