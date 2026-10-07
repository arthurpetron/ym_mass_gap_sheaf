/-
# Torus RP assembly (b6): the conj flip respects Haar-context equivalence (`PECongr`)

Key fact (`haar_odd`): a monomial with an odd exponent at some coordinate has Haar moment `≈ 0`. So in every
context `m`, `phi n (signSel X) m ≈ sg(parity m) (phi n X m)` (`phi_sign`). Hence `PE n X Y → PE n (signSel X)
(signSel Y)` (`conj_peCongr`), with no support hypothesis. With `ringSub_comp`, the conj flip can now be composed
after any `RingSub`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (`PECongr` for reindex/head shear, geometry (c), assembly (d) remain).
-/

import YMGap.Continuum.SU2TorusRPConj

namespace YMGap.Continuum.SU2TorusRPConjCongr

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
  (selectedExponentParity signSelectedTerm signSelectedPolynomial)
open YMGap.Continuum.SU2HaarAlgebra (PE phi sm sm_congr sm_map)
open YMGap.Continuum.SU2MultiLinkHaarFactorization (exponentAt_drop allZero_iff)
open YMGap.Continuum.SU2TorusRPConj (step parity_eq parity_monoMul sg PECongr)

/-! ## Odd parity forces an odd selected coordinate -/

theorem foldl_false (S : Nat → Bool) (m : List Nat) : ∀ (l : List Nat) (p : Bool),
    (∀ i ∈ l, S i = true → exponentAt m i % 2 = 0) → l.foldl (step S m) p = p
  | [], _, _ => rfl
  | c :: l, p, h => by
    simp only [List.foldl_cons]
    have : step S m p c = p := by
      unfold step; split
      · have := h c (List.mem_cons_self ..) (by assumption); simp [this]
      · rfl
    rw [this]; exact foldl_false S m l p fun i hi => h i (List.mem_cons_of_mem _ hi)

theorem sm4_odd (e0 e1 e2 e3 : Nat) (h : e0 % 2 = 1 ∨ e1 % 2 = 1 ∨ e2 % 2 = 1 ∨ e3 % 2 = 1) :
    sphereMoment4 e0 e1 e2 e3 = 0 := by
  unfold sphereMoment4
  rw [dif_neg]; omega

theorem prefix_odd : ∀ (n : Nat) (mono : List Nat) (i : Nat), i < 4 * n → exponentAt mono i % 2 = 1 →
    (quaternionHaarPrefix n mono).eqv 0
  | 0, _, i, hi, _ => by omega
  | n + 1, mono, i, hi, ho => by
    show (sphereMoment4 _ _ _ _ * quaternionHaarPrefix n (mono.drop 4)).eqv 0
    by_cases h4 : i < 4
    · rw [sm4_odd _ _ _ _ (by
        have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases this with rfl | rfl | rfl | rfl <;> simp [ho])]
      exact Q'.zero_mul_eqv _
    · have := prefix_odd n (mono.drop 4) (i - 4) (by omega) (by rw [exponentAt_drop]; rw [show 4 + (i - 4) = i by omega]; exact ho)
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ this) (Q'.mul_zero_eqv _)

theorem haar_odd (n : Nat) (mono : List Nat) (i : Nat) (ho : exponentAt mono i % 2 = 1) :
    (quaternionHaarMono n mono).eqv 0 := by
  unfold quaternionHaarMono
  by_cases hi : i < 4 * n
  · split
    · exact prefix_odd n mono i hi ho
    · exact Q'.eqv_refl _
  · have hz : allZero (mono.drop (4 * n)) = false := by
      cases hc : allZero (mono.drop (4 * n))
      · rfl
      · have := (allZero_iff _).mp hc (i - 4 * n)
        rw [exponentAt_drop, show 4 * n + (i - 4 * n) = i by omega] at this
        omega
    rw [hz]; exact Q'.eqv_refl _

/-- Either the Haar moment vanishes or the selected parity is even. -/
theorem haar_or_even (n N : Nat) (S : Nat → Bool) (mono : List Nat) :
    (quaternionHaarMono n mono).eqv 0 ∨ selectedExponentParity N S mono = false := by
  cases hf : (List.range mono.length).find? (fun i => exponentAt mono i % 2 == 1) with
  | some i =>
    left
    have := List.find?_some hf
    exact haar_odd n mono i (by simpa using this)
  | none =>
    right
    rw [parity_eq]
    refine foldl_false S mono _ false fun i _ _ => ?_
    by_cases hl : i < mono.length
    · have := List.find?_eq_none.mp hf i (List.mem_range.mpr hl)
      simp at this; omega
    · rw [YMGap.Continuum.SU2MultiLinkHaarFactorization.exponentAt_of_length_le mono i (by omega)]

/-! ## The sign pulls out of every context -/

theorem sg_neg_true (x : Q') : sg true x = -x := rfl
theorem sg_false (x : Q') : sg false x = x := rfl

theorem term_sign (n N : Nat) (S : Nat → Bool) (m : List Nat) (x : List Nat × Q') :
    ((signSelectedTerm N S x).2 * quaternionHaarMono n (monoMul m (signSelectedTerm N S x).1)).eqv
      (sg (selectedExponentParity N S m) (x.2 * quaternionHaarMono n (monoMul m x.1))) := by
  show ((sg (selectedExponentParity N S x.1) x.2) * quaternionHaarMono n (monoMul m x.1)).eqv _
  have hp := parity_monoMul N S m x.1
  rcases haar_or_even n N S (monoMul m x.1) with h0 | he
  · have l : ((sg (selectedExponentParity N S x.1) x.2) * quaternionHaarMono n (monoMul m x.1)).eqv 0 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h0) (Q'.mul_zero_eqv _)
    have r : (x.2 * quaternionHaarMono n (monoMul m x.1)).eqv 0 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h0) (Q'.mul_zero_eqv _)
    refine Q'.eqv_trans _ _ _ l ?_
    cases selectedExponentParity N S m
    · exact Q'.eqv_symm r
    · exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ r) (by decide))
  · rw [he] at hp
    have e : selectedExponentParity N S x.1 = selectedExponentParity N S m := by
      cases h1 : selectedExponentParity N S x.1 <;> cases h2 : selectedExponentParity N S m <;>
        simp_all
    rw [e]
    cases selectedExponentParity N S m
    · exact Q'.eqv_refl _
    · exact Q'.neg_mul_eqv _ _

theorem sm_sg {β : Type} (b : Bool) (f : β → Q') : ∀ l : List β, (sm (fun x => sg b (f x)) l).eqv (sg b (sm f l))
  | [] => by
    cases b
    · exact Q'.eqv_refl _
    · show (0 : Q').eqv (-0); decide
  | x :: l => by
    cases b
    · exact Q'.add_eqv_congr' (Q'.eqv_refl _) (by simpa [sg] using sm_sg false f l)
    · exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (sm_sg true f l))
        (Q'.eqv_symm (Q'.neg_add_eqv _ _))

theorem phi_sign (n N : Nat) (S : Nat → Bool) (X : RatPoly) (m : List Nat) :
    (phi n (signSelectedPolynomial N S X) m).eqv (sg (selectedExponentParity N S m) (phi n X m)) := by
  unfold phi signSelectedPolynomial
  rw [sm_map]
  exact Q'.eqv_trans _ _ _ (sm_congr X fun x _ => term_sign n N S m x) (sm_sg _ _ X)

theorem sg_congr (b : Bool) {x y : Q'} (h : x.eqv y) : (sg b x).eqv (sg b y) := by
  cases b
  · exact h
  · exact Q'.neg_eqv_congr _ _ h

/-- **The conj flip respects `PE n`.** -/
theorem conj_peCongr (n N : Nat) (S : Nat → Bool) : PECongr n (signSelectedPolynomial N S) := fun h m =>
  Q'.eqv_trans _ _ _ (phi_sign n N S _ m)
    (Q'.eqv_trans _ _ _ (sg_congr _ (h m)) (Q'.eqv_symm (phi_sign n N S _ m)))

end YMGap.Continuum.SU2TorusRPConjCongr

#print axioms YMGap.Continuum.SU2TorusRPConjCongr.conj_peCongr
