/-
# R1 commit 3: block support of plaquette polynomials, and polymer-product factorization

ADDITIVE.

* `FreeOff A b p` (from `SU2HaarDisjointSupport`): every monomial of p is free on the blocks
  where `A = b`.
* Closure lemmas: support is preserved by `polyOne`, `+`, `·`, `−`, scalars, the quaternion
  product and conjugate, and the Chebyshev characters.
* `plaq_free`: `χ_s(U_p)` and `f_p = Σ_{1≤s≤M} coeffW w s χ_s(U_p)` use only the blocks
  `idxs p` of p's four links.
* `prod_free`: `Π_{p∈γ} F_p` uses only `⋃_{p∈γ} idxs p`.
* `polymer_factor`: if no block index of γ is a block index of R, then
  `∫ (Π_γ F)(Π_R G) ≈ ∫ Π_γ F · ∫ Π_R G`.
* `idx_disj`: link-disjoint plaquettes with all links in `links` have disjoint block indices,
  since `idxOf` is injective on members.
* `plaqWeight_split`: `plaqWeight w M p = [([], coeffW w 0 · 1)] ++ fPoly w … p M`, as an exact
  list identity.
-/

import YMGap.Continuum.SU2HaarL1Activity
import YMGap.Continuum.SU2PlaqWordHolonomy

namespace YMGap.Continuum.SU2PlaqSupport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs
open YMGap.Continuum.SU2MultiLinkHaarFactorization
open YMGap.Continuum.SU2HaarDisjointSupport
open YMGap.Continuum.SU2HaarL1Activity
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry

variable (A : Nat → Bool) (b : Bool)

theorem free_one : FreeOff A b polyOne := fun s hs k _ c _ => by
  rw [List.mem_singleton.mp hs]; rfl

theorem free_add {p q : RatPoly} (hp : FreeOff A b p) (hq : FreeOff A b q) :
    FreeOff A b (polyAdd p q) := fun s hs =>
  (List.mem_append.mp hs).elim (hp s) (hq s)

theorem free_map {p : RatPoly} (f : Q' → Q') (hp : FreeOff A b p) :
    FreeOff A b (p.map fun t => (t.1, f t.2)) := fun s hs => by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact hp t ht

theorem free_mul {p q : RatPoly} (hp : FreeOff A b p) (hq : FreeOff A b q) :
    FreeOff A b (polyMul p q) := fun s hs k hk c hc => by
  obtain ⟨u, hu, hs'⟩ := List.mem_flatMap.mp hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs'
  show exponentAt (monoMul u.1 t.1) _ = 0
  rw [emul, hp u hu k hk c hc, hq t ht k hk c hc]

theorem free_var (i : Nat) (h : ∀ k, A k = b → ∀ c, c < 4 → 4 * k + c ≠ i) :
    FreeOff A b (polyVar i) := fun s hs k hk c hc => by
  rw [List.mem_singleton.mp hs]
  show exponentAt (List.replicate i 0 ++ [1]) (4 * k + c) = 0
  rw [exponentAt_replicate_append]
  have hne := h k hk c hc
  split
  · rfl
  · exact exponentAt_of_length_le _ _ (by show 1 ≤ _; omega)

/-- All four components free. -/
def QFree (q : PolyQuaternion) : Prop :=
  FreeOff A b q.scalar ∧ FreeOff A b q.iPart ∧ FreeOff A b q.jPart ∧ FreeOff A b q.kPart

theorem qfree_mul {q r : PolyQuaternion} (hq : QFree A b q) (hr : QFree A b r) :
    QFree A b (PolyQuaternion.mul q r) := by
  obtain ⟨q0, q1, q2, q3⟩ := hq
  obtain ⟨r0, r1, r2, r3⟩ := hr
  have m := fun {x y : RatPoly} (hx : FreeOff A b x) (hy : FreeOff A b y) => free_mul A b hx hy
  have n := fun {x : RatPoly} (hx : FreeOff A b x) => free_map A b (fun c => -c) hx
  have a := fun {x y : RatPoly} (hx : FreeOff A b x) (hy : FreeOff A b y) => free_add A b hx hy
  exact ⟨a (m q0 r0) (n (a (m q1 r1) (a (m q2 r2) (m q3 r3)))),
    a (m q0 r1) (a (m q1 r0) (a (m q2 r3) (n (m q3 r2)))),
    a (m q0 r2) (a (m q2 r0) (a (m q3 r1) (n (m q1 r3)))),
    a (m q0 r3) (a (m q3 r0) (a (m q1 r2) (n (m q2 r1))))⟩

theorem qfree_conj {q : PolyQuaternion} (hq : QFree A b q) : QFree A b (PolyQuaternion.conj q) :=
  ⟨hq.1, free_map A b (fun c => -c) hq.2.1, free_map A b (fun c => -c) hq.2.2.1,
    free_map A b (fun c => -c) hq.2.2.2⟩

theorem qfree_coord (i : Nat) (h : A i ≠ b) : QFree A b (PolyQuaternion.coordinateVariable i) := by
  have hv : ∀ c', c' < 4 → FreeOff A b (polyVar (4 * i + c')) := fun c' hc' =>
    free_var A b _ (fun k hk c hc e => by
      have hki : k = i := by omega
      exact h (hki ▸ hk))
  exact ⟨by have := hv 0 (by decide); rwa [Nat.add_zero] at this, hv 1 (by decide),
    hv 2 (by decide), hv 3 (by decide)⟩

theorem free_char {x : RatPoly} (hx : FreeOff A b x) :
    ∀ n, FreeOff A b (characterPolynomial x n) ∧ FreeOff A b (characterPolynomial x (n + 1))
  | 0 => ⟨free_one A b, free_map A b _ hx⟩
  | n + 1 => by
    have ih := free_char hx n
    exact ⟨ih.2, free_add A b (free_mul A b (free_map A b _ hx) ih.2) (free_map A b _ ih.1)⟩

theorem free_mono {A' : Nat → Bool} {b' : Bool} {p : RatPoly} (hp : FreeOff A b p)
    (h : ∀ k, A' k = b' → A k = b) : FreeOff A' b' p := fun s hs k hk => hp s hs k (h k hk)

/-! ## Plaquette block indices -/

/-- The four boundary links of `p`, in `plaqWord` order. -/
def plaqLinks (N : Nat) (p : Z4Plaq) : List Z4Link :=
  [(p.1, (dirsOf p.2).1), (tAdd N p.1 (dirsOf p.2).1, (dirsOf p.2).2),
    (tAdd N p.1 (dirsOf p.2).2, (dirsOf p.2).1), (p.1, (dirsOf p.2).2)]

/-- Block-index indicator of plaquette `p`. -/
def idxB (links : List Z4Link) (N : Nat) (p : Z4Plaq) (k : Nat) : Bool :=
  (plaqLinks N p).any fun ℓ => decide (links.idxOf ℓ = k)

theorem idxB_of_mem (links : List Z4Link) (N : Nat) (p : Z4Plaq) {ℓ : Z4Link} (h : ℓ ∈ plaqLinks N p) :
    idxB links N p (links.idxOf ℓ) = true :=
  List.any_eq_true.mpr ⟨ℓ, h, decide_eq_true rfl⟩

theorem qfree_link (links : List Z4Link) (N : Nat) (p : Z4Plaq) {ℓ : Z4Link}
    (h : ℓ ∈ plaqLinks N p) : QFree (idxB links N p) false (linkVar links ℓ) :=
  qfree_coord _ _ _ (by rw [idxB_of_mem links N p h]; decide)

theorem plaq_free (links : List Z4Link) (N : Nat) (p : Z4Plaq) (s : Nat) :
    FreeOff (idxB links N p) false (plaqCharacter links N p s) := by
  have m := fun {i : Nat} (h : i < 4) => qfree_link links N p (List.getElem_mem (l := plaqLinks N p) (n := i) h)
  have hw : QFree (idxB links N p) false (plaqWord links N p) :=
    qfree_mul _ _ (qfree_mul _ _ (m (by decide : 0 < 4)) (m (by decide : 1 < 4)))
      (qfree_mul _ _ (qfree_conj _ _ (m (by decide : 2 < 4))) (qfree_conj _ _ (m (by decide : 3 < 4))))
  exact (free_char _ _ hw.1 s).1

theorem fPoly_free (w : Q') (links : List Z4Link) (N : Nat) (p : Z4Plaq) :
    ∀ M, FreeOff (idxB links N p) false (fPoly w links N p M)
  | 0 => fun _ hs => absurd hs List.not_mem_nil
  | M + 1 => free_add _ _ (fPoly_free w links N p M) (free_map _ _ _ (plaq_free links N p (M + 1)))

/-! ## Polymer products -/

/-- Block indicator of a plaquette list. -/
def setB (links : List Z4Link) (N : Nat) (γ : List Z4Plaq) (k : Nat) : Bool :=
  γ.any fun p => idxB links N p k

theorem prod_free (links : List Z4Link) (N : Nat) (F : Z4Plaq → RatPoly)
    (hF : ∀ p, FreeOff (idxB links N p) false (F p)) :
    ∀ γ, FreeOff (setB links N γ) false (prodPoly F γ)
  | [] => free_one _ _
  | p :: γ => free_mul _ _
      (free_mono _ _ (hF p) (fun k hk => by
        have : (idxB links N p k || setB links N γ k) = false := hk
        cases h : idxB links N p k
        · rfl
        · rw [h, Bool.true_or] at this; exact absurd this (by decide)))
      (free_mono _ _ (prod_free links N F hF γ) (fun k hk => by
        have : (idxB links N p k || setB links N γ k) = false := hk
        cases h : setB links N γ k
        · rfl
        · rw [h, Bool.or_true] at this; exact absurd this (by decide)))

/-- **Polymer-product factorization (PROVED).** -/
theorem polymer_factor (n : Nat) (links : List Z4Link) (N : Nat) (F G : Z4Plaq → RatPoly)
    (hF : ∀ p, FreeOff (idxB links N p) false (F p)) (hG : ∀ p, FreeOff (idxB links N p) false (G p))
    (γ R : List Z4Plaq) (hd : ∀ k, setB links N γ k = true → setB links N R k = false) :
    (quaternionHaar n (polyMul (prodPoly F γ) (prodPoly G R))).eqv
      (quaternionHaar n (prodPoly F γ) * quaternionHaar n (prodPoly G R)) :=
  haar_disj n (setB links N γ) _ (prod_free links N F hF γ) _
    (free_mono _ _ (prod_free links N G hG R) (fun k hk => hd k hk))

/-! ## Link-disjoint ⇒ index-disjoint -/

theorem idxOf_inj {links : List Z4Link} {ℓ ℓ' : Z4Link} (h : ℓ ∈ links) (h' : ℓ' ∈ links)
    (e : links.idxOf ℓ = links.idxOf ℓ') : ℓ = ℓ' := by
  have a := YMGap.Continuum.SU2PlaqWordHolonomy.getElem?_idxOf h
  have a' := YMGap.Continuum.SU2PlaqWordHolonomy.getElem?_idxOf h'
  rw [e, a'] at a
  exact Option.some.inj a.symm

theorem idx_disj (links : List Z4Link) (N : Nat) (p q : Z4Plaq)
    (hp : ∀ ℓ, ℓ ∈ plaqLinks N p → ℓ ∈ links) (hq : ∀ ℓ, ℓ ∈ plaqLinks N q → ℓ ∈ links)
    (hd : ∀ ℓ, ℓ ∈ plaqLinks N p → ℓ ∉ plaqLinks N q) (k : Nat) (hk : idxB links N p k = true) :
    idxB links N q k = false := by
  obtain ⟨ℓ, hℓ, e⟩ := List.any_eq_true.mp hk
  cases h : idxB links N q k with
  | false => rfl
  | true =>
    obtain ⟨ℓ', hℓ', e'⟩ := List.any_eq_true.mp h
    have := idxOf_inj (hp ℓ hℓ) (hq ℓ' hℓ') ((of_decide_eq_true e).trans (of_decide_eq_true e').symm)
    exact absurd (this ▸ hℓ') (hd ℓ hℓ)

/-! ## plaqWeight = constant term ++ excited part -/

theorem plaqWeight_split (w : Q') (links : List Z4Link) (N : Nat) (p : Z4Plaq) :
    ∀ M, plaqWeight w links N p M = [([], coeffW w 0 * 1)] ++ fPoly w links N p M
  | 0 => rfl
  | M + 1 => by
    show polyAdd (plaqWeight w links N p M) _ = _
    rw [plaqWeight_split w links N p M]
    show ([([], coeffW w 0 * 1)] ++ fPoly w links N p M) ++ _ = _
    rw [List.append_assoc]; rfl

end YMGap.Continuum.SU2PlaqSupport
