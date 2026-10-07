/-
# Disjoint-block factorization of the multi-link polynomial Haar

Companion to `SU2TorusMultiLinkPolyGibbs` (YM Group Realizer).  Proves
`DisjointFactorizes a b (shiftPoly a)`: for `p` supported on the first `a`
quaternion blocks and `q` on `b` blocks (local coordinates), with
`shiftPoly a q` moving `q` to blocks `a, …, a+b−1`,

  `∫_{a+b} p · (shift q) ≈ (∫_a p) · (∫_b q)`.

Monomial core: `quaternionHaarPrefix` splits over the first `a` blocks
(`prefix_split`), depends only on exponents below `4·blocks` (`prefix_congr`),
and the zero-tail test commutes with the shift (`allZero_iff`).
-/

import YMGap.Continuum.SU2TorusMultiLinkPolyGibbs
import YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal

namespace YMGap.Continuum.SU2MultiLinkHaarFactorization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs

theorem exponentAt_drop : ∀ (k : Nat) (m : List Nat) (i : Nat),
    exponentAt (m.drop k) i = exponentAt m (k + i)
  | 0, m, i => by simp
  | k + 1, [], i => by simp [exponentAt]
  | k + 1, x :: xs, i => by
      rw [List.drop_succ_cons, exponentAt_drop k xs i,
        show k + 1 + i = (k + i) + 1 by omega]
      simp [exponentAt]

theorem exponentAt_cons_zero (x : Nat) (xs : List Nat) : exponentAt (x :: xs) 0 = x := rfl

theorem prefix_congr : ∀ (a : Nat) (m m' : List Nat),
    (∀ i, i < 4 * a → exponentAt m i = exponentAt m' i) →
    quaternionHaarPrefix a m = quaternionHaarPrefix a m'
  | 0, _, _, _ => rfl
  | a + 1, m, m', h => by
      unfold quaternionHaarPrefix
      rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
        prefix_congr a (m.drop 4) (m'.drop 4) (fun i hi => by
          rw [exponentAt_drop, exponentAt_drop]; exact h _ (by omega))]

theorem prefix_split : ∀ (a b : Nat) (M : List Nat),
    (quaternionHaarPrefix (a + b) M).eqv
      (quaternionHaarPrefix a M * quaternionHaarPrefix b (M.drop (4 * a)))
  | 0, b, M => by
      rw [Nat.zero_add]
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | a + 1, b, M => by
      rw [Nat.succ_add]
      show (_ * quaternionHaarPrefix (a + b) (M.drop 4)).eqv
        ((_ * quaternionHaarPrefix a (M.drop 4)) * _)
      have hd : M.drop (4 * (a + 1)) = (M.drop 4).drop (4 * a) := by
        rw [List.drop_drop]; congr 1; omega
      rw [hd]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (prefix_split a b (M.drop 4)))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

theorem allZero_iff : ∀ l : List Nat, allZero l = true ↔ ∀ i, exponentAt l i = 0
  | [] => by simp [allZero, exponentAt]
  | e :: es => by
      have ih := allZero_iff es
      simp only [allZero, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨h0, h1⟩ i
        cases i with
        | zero => exact h0
        | succ i => exact (ih.mp h1) i
      · intro h
        exact ⟨h 0, ih.mpr (fun i => h (i + 1))⟩

theorem exponentAt_replicate_append : ∀ (k : Nat) (m : List Nat) (i : Nat),
    exponentAt (List.replicate k 0 ++ m) i = if i < k then 0 else exponentAt m (i - k)
  | 0, m, i => by simp
  | k + 1, m, 0 => by rw [List.replicate_succ]; rfl
  | k + 1, m, i + 1 => by
      have := exponentAt_replicate_append k m i
      simp only [List.replicate_succ, List.cons_append]
      show exponentAt (List.replicate k 0 ++ m) i = _
      rw [this]
      by_cases h : i < k
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]; congr 1; omega

theorem exponentAt_of_length_le : ∀ (m : List Nat) (i : Nat), m.length ≤ i →
    exponentAt m i = 0
  | [], i, _ => by simp [exponentAt]
  | x :: xs, 0, h => by simp at h
  | x :: xs, i + 1, h => by
      show exponentAt xs i = 0
      exact exponentAt_of_length_le xs i (by simp at h; omega)

/-- Shift a polynomial in `b` local blocks to blocks `a, …`. -/
def shiftPoly (a : Nat) (q : RatPoly) : RatPoly :=
  q.map fun t => (List.replicate (4 * a) 0 ++ t.1, t.2)

/-- **Monomial factorization.** -/
theorem mono_factor (a b : Nat) (m1 m2 : List Nat) (h1 : m1.length ≤ 4 * a) :
    (quaternionHaarMono (a + b) (monoMul m1 (List.replicate (4 * a) 0 ++ m2))).eqv
      (quaternionHaarMono a m1 * quaternionHaarMono b m2) := by
  let M := monoMul m1 (List.replicate (4 * a) 0 ++ m2)
  have eM : ∀ i, exponentAt M i =
      exponentAt m1 i + (if i < 4 * a then 0 else exponentAt m2 (i - 4 * a)) := by
    intro i
    rw [YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.exponentAt_monoMul,
      exponentAt_replicate_append]
  have hpa : quaternionHaarPrefix a M = quaternionHaarPrefix a m1 :=
    prefix_congr a M m1 (fun i hi => by rw [eM, if_pos hi]; rfl)
  have hpb : quaternionHaarPrefix b (M.drop (4 * a)) = quaternionHaarPrefix b m2 :=
    prefix_congr b _ m2 (fun i _ => by
      rw [exponentAt_drop, eM, if_neg (by omega),
        exponentAt_of_length_le m1 _ (by omega)]
      simp)
  have hz : allZero (M.drop (4 * (a + b))) = allZero (m2.drop (4 * b)) := by
    apply Bool.eq_iff_iff.mpr
    rw [allZero_iff, allZero_iff]
    constructor
    · intro h i
      have := h i
      rw [exponentAt_drop, eM, if_neg (by omega),
        exponentAt_of_length_le m1 _ (by omega)] at this
      rw [exponentAt_drop]
      have e : 4 * (a + b) + i - 4 * a = 4 * b + i := by omega
      rw [e] at this; simpa using this
    · intro h i
      rw [exponentAt_drop, eM, if_neg (by omega),
        exponentAt_of_length_le m1 _ (by omega)]
      have e : 4 * (a + b) + i - 4 * a = 4 * b + i := by omega
      rw [e, ← exponentAt_drop]; simpa using h i
  show (quaternionHaarMono (a + b) M).eqv _
  unfold quaternionHaarMono
  rw [hz, List.drop_eq_nil_of_le h1]
  have h0 : allZero ([] : List Nat) = true := rfl
  rw [if_pos h0]
  cases hb : allZero (m2.drop (4 * b))
  · simp only [Bool.false_eq_true, if_false]
    exact Q'.eqv_symm (Q'.mul_zero_eqv _)
  · simp only [if_true]
    exact Q'.eqv_trans _ _ _ (prefix_split a b M) (by rw [hpa, hpb]; exact Q'.eqv_refl _)

private theorem haar_row (a b : Nat) (s : RatTerm) (hs : s.1.length ≤ 4 * a) :
    ∀ q : RatPoly,
      (quaternionHaar (a + b) ((shiftPoly a q).map fun t => (monoMul s.1 t.1, s.2 * t.2))).eqv
        ((s.2 * quaternionHaarMono a s.1) * quaternionHaar b q)
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv _)
  | t :: q => by
      have ih := haar_row a b s hs q
      show ((s.2 * t.2) * quaternionHaarMono (a + b)
              (monoMul s.1 (List.replicate (4 * a) 0 ++ t.1)) + _).eqv
        ((s.2 * quaternionHaarMono a s.1) * (t.2 * quaternionHaarMono b t.1 + quaternionHaar b q))
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ (mono_factor a b s.1 t.1 hs)) ih) ?_
      refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))
      exact Q'.add_eqv_congr'
        (YMGap.Continuum.RingNormaliser.q_mul4_swap _ _ _ _) (Q'.eqv_refl _)

/-- **Disjoint factorization (PROVED).** -/
theorem haar_factor (a b : Nat) :
    ∀ p : RatPoly, (∀ s, s ∈ p → s.1.length ≤ 4 * a) → ∀ q : RatPoly,
      (quaternionHaar (a + b) (polyMul p (shiftPoly a q))).eqv
        (quaternionHaar a p * quaternionHaar b q)
  | [], _, q => Q'.eqv_symm (Q'.zero_mul_eqv _)
  | s :: p, hp, q => by
      show (quaternionHaar (a + b) (((shiftPoly a q).map fun t => (monoMul s.1 t.1, s.2 * t.2)) ++
          polyMul p (shiftPoly a q))).eqv
        ((s.2 * quaternionHaarMono a s.1 + quaternionHaar a p) * quaternionHaar b q)
      refine Q'.eqv_trans _ _ _
        (YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_append _ _ _) ?_
      refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))
      exact Q'.add_eqv_congr' (haar_row a b s (hp s (List.mem_cons_self ..)) q)
        (haar_factor a b p (fun s' h => hp s' (List.mem_cons_of_mem _ h)) q)

/-- `DisjointFactorizes a b (shiftPoly a)` holds. -/
theorem disjointFactorizes (a b : Nat) : DisjointFactorizes a b (shiftPoly a) :=
  fun p q hp _ => haar_factor a b p hp q

end YMGap.Continuum.SU2MultiLinkHaarFactorization

#print axioms YMGap.Continuum.SU2MultiLinkHaarFactorization.mono_factor
#print axioms YMGap.Continuum.SU2MultiLinkHaarFactorization.disjointFactorizes
