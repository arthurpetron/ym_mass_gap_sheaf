/-
# Unconditional Z4 instance of the weighted signed-polymer KP bound

ADDITIVE.  **GROUP-BLIND PLUMBING** (U(1) rule: not gap evidence by itself).

"Polymer" here means a box polymer system `Z4BoxGas`: a finite list of plaquette sets
`X : List z4Chain.Plaquette` (corner-anchored Z≥0⁴ plaquettes of `ClusterCount4DProgress`) with
* each `X` duplicate-free and internally connected (`connectedIn`), i.e. a genuine lattice animal;
* `1 ≤ |X| ≤ N` (the finite box/size cutoff);
* pairwise distinct supports (`¬ sameSupport`).
Incompatibility is `shareB` ("share a plaquette").  Activities are signed, with
`|z X| ≤ ε^{|X|}` and `ε = 1/10000`.  The weights are `m X = 1 + η^{|X|}` with `η = 1/2500`.

PROVED here:
* `group_le`: the grouping lemma, via the computable choice `asg` (the first shared
  plaquette in list order);
* `pigeon`: the up-to-support pigeonhole into `enumPolys`;
* `class_sum`: the per-plaquette count `Σ_{X∋q} η^{|X|} ≤ geoS N ≤ 1/3`, from
  `z4ClusterCountBound_animal` (625^n);
* `z4_hgroup`, which closes `hgroup` of `SizeWeightedPolymerKP.z4_cond`;
* **`z4_kp`**: for every `Z4BoxGas` and every such `z`, `0 ≤ Ξ`, the removal ratio
  `Ξ(Λ∖b) ≤ (1+η^{|b|}) Ξ(Λ)`, and `1 ≤ Π(1+η^{|X|})·Ξ(Λ)`.  These hold with no further
  hypotheses.

Axioms: `propext`, `Quot.sound`.
-/

import YMGap.Continuum.SizeWeightedPolymerKP
import YMGap.Continuum.ClusterCount4DProgress

namespace YMGap.Continuum.Z4PolymerKP

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SignedPolymerKP
open YMGap.Continuum.SizeWeightedPolymerKP
open YMGap.Continuum.BddLatticeAnimal (IsClusterThrough enumPolys sameSupport animalCount
  animalK animalCount_le_pow)
open YMGap.Continuum.ClusterCount4DProgress (z4Chain z4ClusterCountBound_animal)

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩

abbrev PL := z4Chain.toLattice.Plaquette
abbrev Poly := List PL
instance : DecidableEq PL := z4Chain.decEq

/-! ## Sharing, first shared plaquette -/

def shareB (X Y : Poly) : Bool := X.any (fun p => decide (p ∈ Y))

theorem shareB_iff : ∀ X Y : Poly, shareB X Y = true ↔ ∃ p, p ∈ X ∧ p ∈ Y
  | [], _ => ⟨fun h => by simp [shareB] at h, fun ⟨_, hp, _⟩ => absurd hp List.not_mem_nil⟩
  | a :: X, Y => by
    have ih := shareB_iff X Y
    show (decide (a ∈ Y) || shareB X Y) = true ↔ _
    rw [Bool.or_eq_true, decide_eq_true_iff, ih]
    constructor
    · rintro (h | ⟨p, hp, hq⟩)
      · exact ⟨a, List.mem_cons_self, h⟩
      · exact ⟨p, List.mem_cons_of_mem _ hp, hq⟩
    · rintro ⟨p, hp, hq⟩
      cases hp with
      | head => exact Or.inl hq
      | tail _ h => exact Or.inr ⟨p, h, hq⟩

theorem shareB_symm (X Y : Poly) : shareB X Y = shareB Y X :=
  Bool.eq_iff_iff.mpr ((shareB_iff X Y).trans (Iff.trans
    ⟨fun ⟨p, h1, h2⟩ => ⟨p, h2, h1⟩, fun ⟨p, h1, h2⟩ => ⟨p, h2, h1⟩⟩ (shareB_iff Y X).symm))

def firstIn (a : Poly) : Poly → Option PL
  | [] => none
  | p :: x => if p ∈ a then some p else firstIn a x

theorem firstIn_spec (a : Poly) : ∀ (x : Poly) (q : PL), firstIn a x = some q → q ∈ x ∧ q ∈ a
  | [], _, h => by simp [firstIn] at h
  | p :: x, q, h => by
    by_cases hp : p ∈ a
    · rw [firstIn, if_pos hp] at h
      cases h; exact ⟨List.mem_cons_self, hp⟩
    · rw [firstIn, if_neg hp] at h
      have := firstIn_spec a x q h
      exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

theorem firstIn_some (a : Poly) : ∀ x : Poly, (∃ p, p ∈ x ∧ p ∈ a) → ∃ q, firstIn a x = some q
  | [], ⟨_, hp, _⟩ => absurd hp List.not_mem_nil
  | p :: x, ⟨r, hr, hra⟩ => by
    by_cases hp : p ∈ a
    · exact ⟨p, by rw [firstIn, if_pos hp]⟩
    · rw [firstIn, if_neg hp]
      cases hr with
      | head => exact absurd hra hp
      | tail _ h => exact firstIn_some a x ⟨r, h, hra⟩

def asg (a : Poly) (d : PL) (x : Poly) : PL := (firstIn a x).getD d

theorem asg_spec (a : Poly) (d : PL) (x : Poly) (h : shareB a x = true) :
    asg a d x ∈ x ∧ asg a d x ∈ a := by
  obtain ⟨p, hpa, hpx⟩ := (shareB_iff a x).mp h
  obtain ⟨q, hq⟩ := firstIn_some a x ⟨p, hpx, hpa⟩
  unfold asg; rw [hq]; exact firstIn_spec a x q hq

/-! ## Grouping lemma -/

theorem prodm_nonneg0 {β : Type} (g : β → Q') (h : ∀ q, (0 : Q') ≤ g q) :
    ∀ A : List β, (0 : Q') ≤ prodm g A
  | [] => (by decide : (0 : Q') ≤ 1)
  | q :: A => Q'.mul_nonneg _ _ (h q) (prodm_nonneg0 g h A)

theorem prodm_mono_pt {β : Type} (g g' : β → Q') (h0 : ∀ q, (0 : Q') ≤ g q)
    (h : ∀ q, g q ≤ g' q) : ∀ A : List β, prodm g A ≤ prodm g' A
  | [] => Q'.le_refl' 1
  | q :: A => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (h q) (prodm_nonneg0 g h0 A))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (prodm_mono_pt g g' h0 h A)
        (Q'.le_trans' _ _ _ (h0 q) (h q)))

theorem insert_le {β : Type} [DecidableEq β] (q0 : β) (c : Q') (hc : (1 : Q') ≤ c)
    (G : β → Q') (hG : ∀ q, (0 : Q') ≤ G q) : ∀ A : List β, q0 ∈ A →
      c * prodm G A ≤ prodm (fun q => if q0 = q then c * G q else G q) A
  | [], h => absurd h List.not_mem_nil
  | q :: A, h => by
    let V := PolyExpr.var
    have hc0 : (0 : Q') ≤ c := Q'.le_trans' _ _ _ (by decide) hc
    have hle : ∀ q', G q' ≤ (if q0 = q' then c * G q' else G q') := fun q' => by
      by_cases e : q0 = q'
      · rw [if_pos e]
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _)))
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hc (hG q'))
      · rw [if_neg e]; exact Q'.le_refl' _
    show c * (G q * prodm G A) ≤ (if q0 = q then c * G q else G q) * prodm _ A
    have assoc : (c * (G q * prodm G A)).eqv ((c * G q) * prodm G A) :=
      poly_identity_of_normal_eq (V 0 * (V 1 * V 2)) ((V 0 * V 1) * V 2) (by decide)
        (fun | 0 => c | 1 => G q | _ => prodm G A)
    by_cases hq : q0 = q
    · rw [if_pos hq]
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv assoc) (Q'.mul_le_mul_of_nonneg_left _ _ _
        (prodm_mono_pt _ _ hG hle A) (Q'.mul_nonneg _ _ hc0 (hG q)))
    · rw [if_neg hq]
      have hA : q0 ∈ A := by
        cases h with
        | head => exact absurd rfl hq
        | tail _ h' => exact h'
      have comm : (c * (G q * prodm G A)).eqv (G q * (c * prodm G A)) :=
        poly_identity_of_normal_eq (V 0 * (V 1 * V 2)) (V 1 * (V 0 * V 2)) (by decide)
          (fun | 0 => c | 1 => G q | _ => prodm G A)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv comm)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (insert_le q0 c hc G hG A hA) (hG q))

theorem group_le {β : Type} (f : β → Q') (hf : ∀ x, (1 : Q') ≤ f x) (asgf : β → PL)
    (A : List PL) : ∀ L : List β, (∀ x, x ∈ L → asgf x ∈ A) →
      prodm f L ≤ prodm (fun q => prodm f (L.filter (fun x => decide (asgf x = q)))) A
  | [], _ => prodm_ge_one (fun _ => (1 : Q')) (fun _ => Q'.le_refl' 1) A
  | x :: L, hL => by
    have ih := group_le f hf asgf A L (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    have hx := hL x List.mem_cons_self
    let G := fun q => prodm f (L.filter (fun y => decide (asgf y = q)))
    have hG : ∀ q, (0 : Q') ≤ G q := fun q => prodm_nonneg f hf _
    have hfun : (fun q => prodm f ((x :: L).filter (fun y => decide (asgf y = q)))) =
        (fun q => if asgf x = q then f x * G q else G q) := by
      funext q
      by_cases h : asgf x = q
      · rw [if_pos h]; simp [List.filter, h, prodm, G]
      · rw [if_neg h]; simp [List.filter, h, G]
    rw [hfun]
    exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ ih (m_nonneg f hf x))
      (insert_le (asgf x) (f x) (hf x) G hG A hx)

/-! ## List helpers and the up-to-support pigeonhole -/

theorem mem_filter' {β : Type} (p : β → Bool) {x : β} :
    ∀ {l : List β}, x ∈ l.filter p → x ∈ l ∧ p x = true
  | [], h => by simp [List.filter] at h
  | a :: l, h => by
    cases hp : p a
    · simp only [List.filter, hp] at h
      have := mem_filter' p h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
    · simp only [List.filter, hp] at h
      cases h with
      | head => exact ⟨List.mem_cons_self, hp⟩
      | tail _ h' =>
        have := mem_filter' p h'; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

theorem pairwise_filter {β : Type} (R : β → β → Prop) (p : β → Bool) :
    ∀ {l : List β}, l.Pairwise R → (l.filter p).Pairwise R
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
    cases h with
    | cons h1 h2 =>
      cases hp : p a
      · simp only [List.filter, hp]; exact pairwise_filter R p h2
      · simp only [List.filter, hp]
        exact List.Pairwise.cons (fun y hy => h1 y (mem_filter' p hy).1) (pairwise_filter R p h2)

theorem len_split {β : Type} (p : β → Bool) :
    ∀ l : List β, l.length = (l.filter p).length + (l.filter (fun x => !p x)).length
  | [] => rfl
  | a :: l => by
    have ih := len_split p l
    cases hp : p a <;> simp only [List.filter, hp, Bool.not_false, Bool.not_true,
      List.length_cons] <;> omega

def ssB (X Y : Poly) : Bool := X.all (fun a => decide (a ∈ Y)) && Y.all (fun a => decide (a ∈ X))

theorem ssB_iff (X Y : Poly) : ssB X Y = true ↔ sameSupport X Y := by
  simp only [ssB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_iff]
  rfl

theorem ss_trans {X Y W : Poly} (h1 : sameSupport X Y) (h2 : sameSupport Y W) :
    sameSupport X W := ⟨fun a h => h2.1 a (h1.1 a h), fun a h => h1.2 a (h2.2 a h)⟩

theorem ss_symm {X Y : Poly} (h : sameSupport X Y) : sameSupport Y X := ⟨h.2, h.1⟩

theorem pigeon : ∀ (L2 L1 : List Poly), L1.Pairwise (fun X Y => ¬ sameSupport X Y) →
    (∀ X, X ∈ L1 → ∃ Y, Y ∈ L2 ∧ sameSupport X Y) → L1.length ≤ L2.length
  | [], [], _, _ => Nat.le_refl 0
  | [], X :: _, _, h => by
    obtain ⟨_, hY, _⟩ := h X List.mem_cons_self; exact absurd hY List.not_mem_nil
  | y :: L2, L1, hpw, h => by
    have hs := len_split (fun X => ssB X y) L1
    have hin : (L1.filter (fun X => ssB X y)).length ≤ 1 := by
      have hp := pairwise_filter _ (fun X => ssB X y) hpw
      have hm : ∀ X, X ∈ L1.filter (fun X => ssB X y) → sameSupport X y :=
        fun X hX => (ssB_iff X y).mp (mem_filter' _ hX).2
      revert hp hm
      generalize L1.filter (fun X => ssB X y) = l
      intro hp hm
      match l, hp, hm with
      | [], _, _ => exact Nat.zero_le _
      | [_], _, _ => exact Nat.le_refl _
      | X1 :: X2 :: _, hp, hm =>
        cases hp with
        | cons h1 _ =>
          exact absurd (ss_trans (hm X1 List.mem_cons_self)
            (ss_symm (hm X2 (List.mem_cons_of_mem _ List.mem_cons_self))))
            (h1 X2 List.mem_cons_self)
    have hout := pigeon L2 (L1.filter (fun X => !ssB X y)) (pairwise_filter _ _ hpw)
      (fun X hX => by
        have hm := mem_filter' _ hX
        obtain ⟨Y, hY, hXY⟩ := h X hm.1
        cases hY with
        | head =>
          have : ssB X y = true := (ssB_iff X y).mpr hXY
          simp [this] at hm
        | tail _ h' => exact ⟨Y, h', hXY⟩)
    simp only [List.length_cons]
    omega

/-! ## Per-plaquette geometric count -/

def sz : Poly → Nat
  | [] => 1
  | X => X.length

theorem sz_of_ne (X : Poly) (h : 1 ≤ X.length) : sz X = X.length := by
  cases X with
  | nil => simp at h
  | cons _ _ => rfl

theorem sz_pos (X : Poly) : 1 ≤ sz X := by
  cases X with
  | nil => exact Nat.le_refl 1
  | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)

def δ (X : Poly) : Q' := etaZ ^ sz X

theorem δ_nonneg (X : Poly) : (0 : Q') ≤ δ X := Q'.pow_nonneg _ (by decide) _

theorem sumd_split (p : Poly → Bool) : ∀ L : List Poly,
    (sumd δ L).eqv (sumd δ (L.filter p) + sumd δ (L.filter (fun x => !p x)))
  | [] => (by decide : (0 : Q').eqv (0 + 0))
  | a :: L => by
    let V := PolyExpr.var
    have ih := sumd_split p L
    cases hp : p a
    · simp only [List.filter, hp, Bool.not_false]
      show (δ a + sumd δ L).eqv (sumd δ (L.filter p) + (δ a + sumd δ (L.filter (fun x => !p x))))
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) ih) ?_
      exact poly_identity_of_normal_eq (V 0 + (V 1 + V 2)) (V 1 + (V 0 + V 2)) (by decide)
        (fun | 0 => δ a | 1 => sumd δ (L.filter p) | _ => sumd δ (L.filter (fun x => !p x)))
    · simp only [List.filter, hp, Bool.not_true]
      show (δ a + sumd δ L).eqv ((δ a + sumd δ (L.filter p)) + sumd δ (L.filter (fun x => !p x)))
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) ih) ?_
      exact poly_identity_of_normal_eq (V 0 + (V 1 + V 2)) ((V 0 + V 1) + V 2) (by decide)
        (fun | 0 => δ a | 1 => sumd δ (L.filter p) | _ => sumd δ (L.filter (fun x => !p x)))

theorem sumd_const (v : Q') : ∀ L : List Poly, (∀ X, X ∈ L → δ X = v) →
    (sumd δ L).eqv (Q'.ofNat L.length * v)
  | [], _ => by
    let V := PolyExpr.var
    show (0 : Q').eqv (Q'.ofNat 0 * v)
    exact poly_identity_of_normal_eq (PolyExpr.const 0) (PolyExpr.const 0 * V 0) (by decide)
      (fun _ => v)
  | a :: L, h => by
    let V := PolyExpr.var
    have ih := sumd_const v L (fun X hX => h X (List.mem_cons_of_mem _ hX))
    show (δ a + sumd δ L).eqv (Q'.ofNat (L.length + 1) * v)
    rw [h a List.mem_cons_self]
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) ih) ?_
    have h1 : (Q'.ofNat (L.length + 1)).eqv (Q'.ofNat L.length + 1) :=
      Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv _ 1) (Q'.add_eqv_congr_left _ _ _ (by decide))
    refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.mul_eqv_congr_right _ _ _ h1))
    exact poly_identity_of_normal_eq (V 0 + V 1 * V 0) ((V 1 + PolyExpr.const 1) * V 0)
      (by decide) (fun | 0 => v | _ => Q'.ofNat L.length)

theorem ofNat_le' {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b := by
  show (Int.ofNat a) * ((Q'.ofNat b).den : Int) ≤ (Int.ofNat b) * ((Q'.ofNat a).den : Int)
  show (Int.ofNat a) * (1 : Int) ≤ (Int.ofNat b) * (1 : Int)
  rw [Int.mul_one, Int.mul_one]
  exact Int.ofNat_le.mpr h

theorem mul_pow' (a b : Q') : ∀ k : Nat, (a ^ k * b ^ k).eqv ((a * b) ^ k)
  | 0 => (by decide : ((1 : Q') * 1).eqv 1)
  | k + 1 => by
    let V := PolyExpr.var
    show (a * a ^ k * (b * b ^ k)).eqv (a * b * (a * b) ^ k)
    refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq (V 0 * V 1 * (V 2 * V 3))
      (V 0 * V 2 * (V 1 * V 3)) (by decide)
      (fun | 0 => a | 1 => a ^ k | 2 => b | _ => b ^ k)) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (mul_pow' a b k)

theorem pow_congr' {a b : Q'} (h : a.eqv b) : ∀ k : Nat, (a ^ k).eqv (b ^ k)
  | 0 => Q'.eqv_refl _
  | k + 1 => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
      (Q'.mul_eqv_congr_left _ _ _ (pow_congr' h k))

theorem K_eta : (animalK z4Chain * etaZ).eqv quarter := by decide

/-- **Per-plaquette count (PROVED).** -/
theorem class_sum (q : PL) : ∀ (N : Nat) (L : List Poly),
    L.Pairwise (fun X Y => ¬ sameSupport X Y) →
    (∀ X, X ∈ L → IsClusterThrough z4Chain q X.length X) →
    (∀ X, X ∈ L → 1 ≤ X.length ∧ X.length ≤ N) → sumd δ L ≤ geoS N
  | 0, [], _, _, _ => Q'.le_refl' _
  | 0, X :: _, _, _, hs =>
    absurd (Nat.le_trans (hs X List.mem_cons_self).1 (hs X List.mem_cons_self).2) (by decide)
  | N + 1, L, hpw, hcl, hs => by
    let p : Poly → Bool := fun X => decide (X.length = N + 1)
    have hsplit := sumd_split p L
    have hrest := class_sum q N (L.filter (fun x => !p x)) (pairwise_filter _ _ hpw)
      (fun X hX => hcl X (mem_filter' _ hX).1)
      (fun X hX => by
        have hm := mem_filter' _ hX
        have := hs X hm.1
        have hne : X.length ≠ N + 1 := fun h => by
          have hpX : p X = true := decide_eq_true h
          have h2 := hm.2
          rw [hpX] at h2
          exact absurd h2 (by decide)
        exact ⟨this.1, Nat.le_of_lt_succ (Nat.lt_of_le_of_ne this.2 hne)⟩)
    let Lc := L.filter p
    have hconst : ∀ X, X ∈ Lc → δ X = etaZ ^ (N + 1) := fun X hX => by
      have hm := mem_filter' _ hX
      have hl : X.length = N + 1 := of_decide_eq_true hm.2
      show etaZ ^ sz X = _
      rw [sz_of_ne X (hl ▸ Nat.succ_le_succ (Nat.zero_le N)), hl]
    have hcount : Lc.length ≤ (enumPolys z4Chain q (N + 1)).length :=
      pigeon _ Lc (pairwise_filter _ _ hpw) (fun X hX => by
        have hm := mem_filter' _ hX
        have hl : X.length = N + 1 := of_decide_eq_true hm.2
        have hc := hcl X hm.1
        rw [hl] at hc
        exact (z4ClusterCountBound_animal q).2 (N + 1) X hc)
    have hA : animalCount z4Chain q (N + 1) ≤ animalK z4Chain ^ (N + 1) :=
      animalCount_le_pow z4Chain q (N + 1)
    have hη0 : (0 : Q') ≤ etaZ ^ (N + 1) := Q'.pow_nonneg _ (by decide) _
    have hclass : sumd δ Lc ≤ quarter ^ (N + 1) := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (sumd_const _ Lc hconst)) ?_
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (ofNat_le' hcount) hη0) ?_
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hA hη0) ?_
      exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (mul_pow' _ _ _) (pow_congr' K_eta _))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add hclass hrest) (Q'.le_of_eqv ?_)
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 + V 1) (V 1 + V 0) (by decide)
      (fun | 0 => quarter ^ (N + 1) | _ => geoS N)

/-! ## The box gas and the unconditional Z4 KP -/

structure Z4BoxGas where
  polys : List Poly
  N : Nat
  size_ok : ∀ X, X ∈ polys → 1 ≤ X.length ∧ X.length ≤ N
  nodup : ∀ X, X ∈ polys → X.Nodup
  conn : ∀ X, X ∈ polys → Nonempty (YMGap.Continuum.PolymerModel.connectedIn X)
  distinct : polys.Pairwise (fun X Y => ¬ sameSupport X Y)

def five3 : Q' := Q'.mkPos 5 3 (by decide)

theorem pow_const_prodm (c : Q') : ∀ A : List PL, prodm (fun _ => c) A = c ^ A.length
  | [] => rfl
  | _ :: A => by
    show c * prodm (fun _ => c) A = c ^ (A.length + 1)
    rw [pow_const_prodm c A]; rfl

/-- **`hgroup` closed (PROVED).** -/
theorem z4_hgroup (B : Z4BoxGas) (a : Poly) :
    prodm (fun x => 1 + etaZ ^ sz x) (B.polys.filter (shareB a)) ≤ five3 ^ sz a := by
  let L := B.polys.filter (shareB a)
  let d : PL := ((0, 0, 0, 0), YMGap.Continuum.ClusterCount4DProgress.Z4Plane.p01)
  have hf : ∀ x, (1 : Q') ≤ 1 + etaZ ^ sz x :=
    fun x => Q'.add_le_self_of_nonneg _ _ (Q'.pow_nonneg _ (by decide) _)
  have hasg : ∀ x, x ∈ L → asg a d x ∈ a := fun x hx => (asg_spec a d x (mem_filter' _ hx).2).2
  refine Q'.le_trans' _ _ _ (group_le _ hf (asg a d) a L hasg) ?_
  have hpiece : ∀ q, prodm (fun x => 1 + etaZ ^ sz x)
      (L.filter (fun x => decide (asg a d x = q))) ≤ five3 := fun q => by
    let Lq := L.filter (fun x => decide (asg a d x = q))
    have hmemB : ∀ X, X ∈ Lq → X ∈ B.polys ∧ q ∈ X := fun X hX => by
      have h1 := mem_filter' _ hX
      have h2 := mem_filter' _ h1.1
      have hq : asg a d X = q := by simpa using h1.2
      exact ⟨h2.1, hq ▸ (asg_spec a d X h2.2).1⟩
    have hS : sumd δ Lq ≤ geoS B.N :=
      class_sum q B.N Lq (pairwise_filter _ _ (pairwise_filter _ _ B.distinct))
        (fun X hX => ⟨rfl, (hmemB X hX).2, B.nodup X (hmemB X hX).1, B.conn X (hmemB X hX).1⟩)
        (fun X hX => B.size_ok X (hmemB X hX).1)
    have hS3 : sumd δ Lq ≤ third := Q'.le_trans' _ _ _ hS (geom_quarter B.N)
    have h2 : sumd δ Lq + sumd δ Lq ≤ 1 :=
      Q'.le_trans' _ _ _ (Q'.add_le_add hS3 hS3) (by decide)
    refine Q'.le_trans' _ _ _ (prod_le_sum δ δ_nonneg Lq h2) ?_
    exact Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.le_refl' 1) (Q'.add_le_add hS3 hS3))
      (by decide)
  have hfive : (1 : Q') ≤ five3 := by decide
  refine Q'.le_trans' _ _ _ (prodm_mono_pt _ (fun _ => five3)
    (fun q => prodm_nonneg _ hf _) hpiece a) ?_
  rw [pow_const_prodm]
  have hlen : a.length ≤ sz a := by
    cases a with
    | nil => exact Nat.zero_le _
    | cons _ _ => exact Nat.le_refl _
  exact pow_mono_exp hfive hlen

/-- **Unconditional Z4 KP (PROVED).** For every box polymer system and every activity with
`|z X| ≤ (1/10000)^{|X|}`. -/
theorem z4_kp (B : Z4BoxGas) (z : Poly → Q')
    (hz1 : ∀ X, (0 : Q') ≤ z X + epsZ ^ sz X) :
    ((0 : Q') ≤ Xi z shareB B.polys ∧
      ∀ p b r, B.polys = p ++ b :: r →
        Xi z shareB (p ++ r) ≤ (1 + etaZ ^ sz b) * Xi z shareB B.polys) ∧
    (1 : Q') ≤ prodm (fun x => 1 + etaZ ^ sz x) B.polys * Xi z shareB B.polys := by
  have hc := z4_cond shareB sz sz_pos B.polys (fun a => z4_hgroup B a)
  have hm : ∀ x, (1 : Q') ≤ 1 + etaZ ^ sz x :=
    fun x => Q'.add_le_self_of_nonneg _ _ (Q'.pow_nonneg _ (by decide) _)
  have he : ∀ a, (0 : Q') ≤ epsZ ^ sz a := fun a => Q'.pow_nonneg _ (by decide) _
  exact ⟨kpw_main z shareB _ _ shareB_symm hm he hz1 B.polys hc.1 hc.2,
    kpw_lower z shareB _ _ shareB_symm hm he hz1 B.polys hc.1 hc.2⟩

end YMGap.Continuum.Z4PolymerKP

#print axioms YMGap.Continuum.ClusterCount4DProgress.z4ClusterCountBound_animal
#print axioms YMGap.Continuum.Z4PolymerKP.group_le
#print axioms YMGap.Continuum.Z4PolymerKP.pigeon
#print axioms YMGap.Continuum.Z4PolymerKP.class_sum
#print axioms YMGap.Continuum.Z4PolymerKP.z4_hgroup
#print axioms YMGap.Continuum.Z4PolymerKP.z4_kp
