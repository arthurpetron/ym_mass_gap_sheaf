/-
# Torus RP (f6): every supported polynomial is an observable (`obsOf`)

For a duplicate-free link list `L`, `obsOf L X : Obs` rebuilds `X` monomial by monomial from link-coordinate
variables. `obsOf_pe`: if every monomial of `X` has length `≤ 4|L|`, then `PE n (eval L (obsOf L X)) X`.
`obsOf_on`: if every variable that occurs in `X` lies in a block whose link satisfies `Q`, then `OnLinks Q (obsOf L X)`.

**RP FOR THE UNTRUNCATED WILSON MEASURE (K → ∞) IS OPEN; this file is a support lemma.**
-/

import YMGap.Continuum.SU2TorusRPCSObs
import YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal
import YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport

namespace YMGap.Continuum.SU2TorusRPObsOf

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul varMono)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_refl pe_append)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2TorusRPSubst (pe_mul2)
open YMGap.Continuum.SU2TorusRPObs (Obs evalI eval OnLinks comp)
open YMGap.Continuum.SU2TorusRPThetaPoly (d0)
open YMGap.Continuum.SU2TorusRPReindex (pe_mono)

variable (L : List Z4Link)

def vr (k : Nat) : Obs := .var (L.getD (k / 4) d0) (k % 4)

def pw (k : Nat) : Nat → Obs
  | 0 => .const 1
  | e + 1 => .mul (vr L k) (pw k e)

def mo : Nat → List Nat → Obs
  | _, [] => .const 1
  | k, e :: m => .mul (pw L k e) (mo (k + 1) m)

def obsOf : RatPoly → Obs
  | [] => .const 0
  | (m, c) :: X => .add (.mul (.const c) (mo L 0 m)) (obsOf X)

theorem pe_coef (n : Nat) (a : List Nat) {c d : Q'} (h : c.eqv d) : PE n [(a, c)] [(a, d)] := fun _ =>
  YMGap.Constructive.Q'.add_eqv_congr' (YMGap.Constructive.Q'.mul_eqv_congr_right _ _ _ h) (Q'.eqv_refl _)

theorem mul_single (a b : List Nat) (c d : Q') : polyMul [(a, c)] [(b, d)] = [(monoMul a b, c * d)] := by
  unfold polyMul; simp only [List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil]

open YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal (exponentAt_monoMul)

/-- A single monomial with coefficient eqv `1` and prescribed exponents. -/
def Mono (n : Nat) (P : RatPoly) (f : Nat → Nat) : Prop :=
  ∃ E : List Nat, PE n P [(E, 1)] ∧ ∀ i, exponentAt E i = f i

theorem mono_mul (n : Nat) {P R : RatPoly} {f g : Nat → Nat} (hP : Mono n P f) (hR : Mono n R g) :
    Mono n (polyMul P R) (fun i => f i + g i) := by
  obtain ⟨E, hE, hf⟩ := hP
  obtain ⟨E', hE', hg⟩ := hR
  refine ⟨monoMul E E', pe_trans n (pe_mul2 n hE hE') ?_, fun i => by rw [exponentAt_monoMul, hf, hg]⟩
  rw [mul_single]; exact pe_coef n _ (Q'.mul_one_eqv 1)

theorem mono_one (n : Nat) : Mono n (eval L (.const 1)) (fun _ => 0) :=
  ⟨[], pe_coef n [] (Q'.mul_one_eqv 1), fun i => by cases i <;> rfl⟩

variable (hnd : L.Nodup)

include hnd in
theorem mono_vr (n : Nat) (k : Nat) (hk : k < 4 * L.length) :
    Mono n (eval L (vr L k)) (fun i => if i = k then 1 else 0) := by
  refine ⟨varMono k, ?_, fun i => YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport.exponentAt_varMono k i⟩
  have hi := YMGap.Continuum.SU2TorusRPThetaPoly.idxOf_getD L hnd (k / 4) (by omega)
  show PE n (comp (YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.linkVar L (L.getD (k / 4) d0)) (k % 4)) _
  unfold YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.linkVar
  rw [hi]
  have e : 4 * (k / 4) + k % 4 = k := by omega
  obtain h | h | h | h : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  all_goals rw [h] at e ⊢
  · show PE n (polyVar (4 * (k / 4))) _; rw [show 4 * (k / 4) = k by omega]; exact pe_refl n _
  · show PE n (polyVar (4 * (k / 4) + 1)) _; rw [e]; exact pe_refl n _
  · show PE n (polyVar (4 * (k / 4) + 2)) _; rw [e]; exact pe_refl n _
  · show PE n (polyVar (4 * (k / 4) + 3)) _; rw [e]; exact pe_refl n _

theorem mono_ext (n : Nat) {P : RatPoly} {f g : Nat → Nat} (h : ∀ i, f i = g i) (hP : Mono n P f) : Mono n P g := by
  obtain ⟨E, hE, hf⟩ := hP; exact ⟨E, hE, fun i => (hf i).trans (h i)⟩

include hnd in
theorem mono_pw (n k : Nat) : ∀ e : Nat, (e ≠ 0 → k < 4 * L.length) →
    Mono n (eval L (pw L k e)) (fun i => if i = k then e else 0)
  | 0, _ => mono_ext n (fun i => by split <;> rfl) (mono_one L n)
  | e + 1, hk => mono_ext n (fun i => by split <;> omega)
      (mono_mul n (mono_vr L hnd n k (hk (Nat.succ_ne_zero _))) (mono_pw n k e fun _ => hk (Nat.succ_ne_zero _)))

include hnd in
theorem mono_mo (n : Nat) : ∀ (m : List Nat) (k : Nat), (∀ j, m.getD j 0 ≠ 0 → k + j < 4 * L.length) →
    Mono n (eval L (mo L k m)) (fun i => if k ≤ i then m.getD (i - k) 0 else 0)
  | [], k, _ => mono_ext n (fun i => by split <;> rfl) (mono_one L n)
  | e :: m, k, h => by
    have h1 := mono_pw L hnd n k e fun he => by have := h 0 he; omega
    have h2 := mono_mo n m (k + 1) fun j hj => by have := h (j + 1) hj; omega
    refine mono_ext n (fun i => ?_) (mono_mul n h1 h2)
    dsimp only
    rcases Nat.lt_trichotomy i k with hi | hi | hi
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · subst hi; rw [if_pos rfl, if_neg (by omega), if_pos (Nat.le_refl _), Nat.sub_self]; rfl
    · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
      have : i - k = (i - (k + 1)) + 1 := by omega
      rw [this, Nat.zero_add]; rfl

theorem getD_lt : ∀ (m : List Nat) (j : Nat), m.getD j 0 ≠ 0 → j < m.length
  | [], _, h => absurd rfl h
  | _ :: _, 0, _ => Nat.succ_pos _
  | _ :: m, j + 1, h => Nat.succ_lt_succ (getD_lt m j h)

theorem pe_zero (n : Nat) {c : Q'} (hc : c.eqv 0) : PE n [([], c)] [] := fun _ => by
  show (c * _ + 0).eqv 0
  rw [Q'.add_zero']
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hc) (YMGap.Constructive.Q'.zero_mul_eqv _)

include hnd in
theorem obsOf_pe (n : Nat) : ∀ X : RatPoly, (∀ t ∈ X, t.1.length ≤ 4 * L.length) →
    PE n (eval L (obsOf L X)) X
  | [], _ => pe_zero n (Q'.mul_one_eqv 0)
  | (m, c) :: X, h => by
    obtain ⟨E, hE, hf⟩ := mono_mo L hnd n m 0 fun j hj => by
      have := getD_lt m j hj; have := h _ (List.mem_cons_self ..); simp only [] at this; omega
    show PE n (polyAdd (polyMul [([], c * 1)] (eval L (mo L 0 m))) (eval L (obsOf L X))) ((m, c) :: X)
    refine (?_ : PE n (_ ++ _) ([(m, c)] ++ X)) |> fun h' => h'
    refine pe_append n ?_ (obsOf_pe n X fun t ht => h t (List.mem_cons_of_mem _ ht))
    refine pe_trans n (pe_mul2 n (pe_refl n _) hE) ?_
    rw [mul_single]
    refine pe_trans n (pe_mono n _ (e := monoMul [] E) (e' := m) fun i => ?_) (pe_coef n m ?_)
    · show exponentAt E i = _; rw [hf]; simp only [Nat.zero_le, if_true, Nat.sub_zero]; rfl
    · exact Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (Q'.mul_one_eqv _)

theorem pw_on (Q : Z4Link → Prop) (k : Nat) : ∀ e : Nat, (e ≠ 0 → Q (L.getD (k / 4) d0)) → OnLinks Q (pw L k e)
  | 0, _ => trivial
  | e + 1, h => ⟨h (Nat.succ_ne_zero _), pw_on Q k e fun _ => h (Nat.succ_ne_zero _)⟩

theorem mo_on (Q : Z4Link → Prop) : ∀ (m : List Nat) (k : Nat),
    (∀ j, m.getD j 0 ≠ 0 → Q (L.getD ((k + j) / 4) d0)) → OnLinks Q (mo L k m)
  | [], _, _ => trivial
  | e :: m, k, h => ⟨pw_on L Q k e fun he => h 0 he, mo_on Q m (k + 1) fun j hj => by
      have := h (j + 1) hj; rwa [show k + (j + 1) = k + 1 + j by omega] at this⟩

theorem obsOf_on (Q : Z4Link → Prop) : ∀ X : RatPoly,
    (∀ t ∈ X, ∀ i, exponentAt t.1 i ≠ 0 → Q (L.getD (i / 4) d0)) → OnLinks Q (obsOf L X)
  | [], _ => trivial
  | (m, c) :: X, h => ⟨⟨trivial, mo_on L Q m 0 fun j hj => by
      rw [Nat.zero_add]; exact h _ (List.mem_cons_self ..) j hj⟩,
    obsOf_on Q X fun t ht => h t (List.mem_cons_of_mem _ ht)⟩

end YMGap.Continuum.SU2TorusRPObsOf

#print axioms YMGap.Continuum.SU2TorusRPObsOf.obsOf_pe
#print axioms YMGap.Continuum.SU2TorusRPObsOf.obsOf_on
