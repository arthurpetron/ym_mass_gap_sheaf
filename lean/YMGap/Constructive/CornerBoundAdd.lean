/-
Addition law L3b — the corner vanishes: `cornerAdd a b m → 0` (Mertens' estimate).

`cornerAddₘ = Σ_{i<m} tᵢ(a)·(P⁻ₘ(b) − P⁻_{m−i}(b))` (L3a, addition-law version).
Bounding the signed weight `tᵢ(a)` by its magnitude `t⁺ᵢ(a)` and the signed
block `P⁻ₘ(b) − P⁻_{m−i}(b)` by the magnitude block (`block_upper`/`block_lower`)
gives `±cornerAddₘ ≤ cornerAbsAddₘ` with

    cornerAbsAddₘ := Σ_{i<m} t⁺ᵢ(a)·blockAbs b (m−i) i .

Every product `t⁺ᵢ(a)·blockAbs b (m−i) i` mixes the `a`-tail (weights) and the
`b`-block, both living at total degree `≥ m`, so for `m` large the whole sum is
small.  With global bounds `B_a`, `B_b` on `P⁺(a)`, `P⁺(b)` and `δ` chosen so
`(B_a+B_b)·δ ≤ ε`, splitting at `K = max(halfRatioCutoff a, termAbsModulus a (½δ))`
and `N = K + termAbsModulus b (½δ)`:

  * `i < K`: the `b`-block `blockAbs b (m−i) i` starts past the `b`-cutoff, so `≤ δ`
    (uniform `expNeg_tail_bound` on `b`); the part is `≤ (Σ_{i<K} t⁺ᵢ(a))·δ ≤ B_a·δ`.
  * `K ≤ i`: the `a`-weights sum to `blockAbs a K (m−K) ≤ δ` (a-tail from `K`), the
    `b`-blocks are `≤ B_b`; the part is `≤ δ·B_b`.

So `cornerAbsAddₘ ≤ (B_a+B_b)·δ ≤ ε` for `m ≥ K + termAbsModulus b (½δ)`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` only, plus `Quot.sound` where `omega`/`Nat` enter.  No `Classical.*`,
no `sorryAx`.
-/

import YMGap.Constructive.ProductDecompAdd
import YMGap.Constructive.CornerBound

namespace YMGap.Constructive

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.HalfPow
open YMGap.Constructive.RatNat

/-! ## `cornerAbsAdd` and the `±cornerAdd ≤ cornerAbsAdd` reduction -/

/-- `cornerAbsTermAdd a b m i = t⁺ᵢ(a)·blockAbs b (m−i) i`. -/
def cornerAbsTermAdd (a b : Q') (m : Nat) : Nat → Q' :=
  fun i => ExpNeg.termAbs a i * ExpNeg.blockAbs b (m - i) i

/-- `cornerAbsAddₘ = Σ_{i<m} t⁺ᵢ(a)·blockAbs b (m−i) i`. -/
def cornerAbsAdd (a b : Q') (m : Nat) : Q' := finSum (cornerAbsTermAdd a b m) m

/-- Termwise: `±cornerTermAdd ≤ cornerAbsTermAdd`, for `i < m`. -/
theorem cornerTermAdd_abs_le (a b : Q') (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b)
    (m i : Nat) (hi : i < m) :
    cornerTermAdd a b m i ≤ cornerAbsTermAdd a b m i
      ∧ -(cornerTermAdd a b m i) ≤ cornerAbsTermAdd a b m i := by
  have hmi : (m - i) + i = m := by omega
  have hBnn : (0 : Q') ≤ ExpNeg.termAbs a i := termAbs_nonneg a ha i
  have hdnn : (0 : Q') ≤ ExpNeg.blockAbs b (m - i) i := by
    -- blockAbs b (m-i) i = finSum (fun j => termAbs b ((m-i)+j)) i, a sum of nonneg terms.
    rw [blockAbs_eq_finSum]
    have h := finSum_monotone_of_nonneg (fun j => ExpNeg.termAbs b ((m - i) + j))
      (fun j => termAbs_nonneg b hb ((m - i) + j)) 0 i (Nat.zero_le i)
    -- finSum _ 0 = 0
    exact h
  -- bounds on the weight u = term a i: -B ≤ u ≤ B
  obtain ⟨hu2, hnu⟩ := term_two_sided a ha i
  -- bounds on the diff v = P⁻ₘ(b) + -(P⁻_{m-i}(b)): -d ≤ v ≤ d
  have hv2 : ExpNeg.partialSum b m + -(ExpNeg.partialSum b (m - i))
      ≤ ExpNeg.blockAbs b (m - i) i := by
    have h := block_upper b hb (m - i) i
    rw [hmi] at h
    exact Q'.sub_le_of_le_add h
  -- first the `-(v) ≤ d` form, then convert to `-d ≤ v`
  have hnv : -(ExpNeg.partialSum b m + -(ExpNeg.partialSum b (m - i)))
      ≤ ExpNeg.blockAbs b (m - i) i := by
    have hbl := block_lower b hb (m - i) i
    rw [hmi] at hbl
    have h2 : ExpNeg.partialSum b (m - i) + -(ExpNeg.partialSum b m)
        ≤ ExpNeg.blockAbs b (m - i) i := Q'.sub_le_of_le_add hbl
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) h2
    exact Q'.eqv_trans _ _ _
      (Q'.neg_add_eqv (ExpNeg.partialSum b m) (-(ExpNeg.partialSum b (m - i))))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (-(ExpNeg.partialSum b m)) (-(-(ExpNeg.partialSum b (m - i))))
          (ExpNeg.partialSum b (m - i)) (Q'.neg_neg_eqv (ExpNeg.partialSum b (m - i))))
        (Q'.add_comm_eqv (-(ExpNeg.partialSum b m)) (ExpNeg.partialSum b (m - i))))
  -- -d ≤ v  from  -v ≤ d  (negate both sides, cancel double negation)
  have hv1 : -(ExpNeg.blockAbs b (m - i) i)
      ≤ ExpNeg.partialSum b m + -(ExpNeg.partialSum b (m - i)) := by
    refine Q'.le_trans' _ _ _ (Q'.neg_le_neg hnv) (Q'.le_of_eqv ?_)
    exact Q'.neg_neg_eqv (ExpNeg.partialSum b m + -(ExpNeg.partialSum b (m - i)))
  -- -B ≤ u from hnu : -(term a i) ≤ termAbs a i
  have hu1 : -(ExpNeg.termAbs a i) ≤ ExpNeg.term a i := by
    refine Q'.le_trans' _ _ _ (Q'.neg_le_neg hnu) (Q'.le_of_eqv ?_)
    exact Q'.neg_neg_eqv (ExpNeg.term a i)
  refine ⟨?_, ?_⟩
  · -- cornerTermAdd = u·v ≤ B·d = cornerAbsTermAdd
    exact Q'.mul_le_of_bounds hBnn hdnn hu1 hu2 hv1 hv2
  · -- -(u·v) = (-u)·v ≤ B·d
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.neg_mul_eqv _ _))) ?_
    -- bounds for -u : -B ≤ -u ≤ B
    have hnu1 : -(ExpNeg.termAbs a i) ≤ -(ExpNeg.term a i) := by
      refine Q'.le_trans' _ _ _ ?_ (Q'.neg_le_neg hu2)
      exact Q'.le_refl' _
    have hnu2 : -(ExpNeg.term a i) ≤ ExpNeg.termAbs a i := hnu
    exact Q'.mul_le_of_bounds hBnn hdnn hnu1 hnu2 hv1 hv2

theorem cornerAdd_le_cornerAbs (a b : Q') (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b)
    (m : Nat) : cornerAdd a b m ≤ cornerAbsAdd a b m :=
  finSum_le_lt (cornerTermAdd a b m) (cornerAbsTermAdd a b m) m
    (fun i hi => (cornerTermAdd_abs_le a b ha hb m i hi).1)

theorem neg_cornerAdd_le_cornerAbs (a b : Q') (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b)
    (m : Nat) : -(cornerAdd a b m) ≤ cornerAbsAdd a b m := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (neg_finSum (cornerTermAdd a b m) m)) ?_
  exact finSum_le_lt (fun i => -(cornerTermAdd a b m i)) (cornerAbsTermAdd a b m) m
    (fun i hi => (cornerTermAdd_abs_le a b ha hb m i hi).2)

/-! ## The Mertens bound -/

/-- **`cornerAbsAddₘ → 0`.**  For `a, b ≥ 0` and `ε > 0`, every `m` past an
explicit modulus has `cornerAbsAdd a b m ≤ ε`. -/
theorem cornerAbsAdd_le (a b : Q') (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b)
    (ε : Q') (hε : (0 : Q') < ε) :
    ∃ N : Nat, ∀ m : Nat, N ≤ m → cornerAbsAdd a b m ≤ ε := by
  obtain ⟨Ba, hBa0, hBa⟩ := exists_psAbs_bound a ha
  obtain ⟨Bb, hBb0, hBb⟩ := exists_psAbs_bound b hb
  obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le (Q'.zero_le_add _ _ hBa0 hBb0) hε
  have hδnn : (0 : Q') ≤ δ := Q'.le_of_lt hδpos
  have hhδ : (0 : Q') < half * δ := ExpNeg.half_mul_pos δ hδpos
  have hhδnn : (0 : Q') ≤ half * δ := Q'.le_of_lt hhδ
  -- cutoffs for the `a`-tail (weights)
  have hMcutA : halfRatioCutoff a ≤ termAbsModulus a (half * δ) := by
    unfold ExpNeg.termAbsModulus; exact Nat.le_add_right _ _
  obtain ⟨K, hKdef⟩ :
      ∃ K, K = max (halfRatioCutoff a) (termAbsModulus a (half * δ)) := ⟨_, rfl⟩
  have hKcut : halfRatioCutoff a ≤ K := by rw [hKdef]; exact Nat.le_max_left _ _
  have hKM : termAbsModulus a (half * δ) ≤ K := by rw [hKdef]; exact Nat.le_max_right _ _
  -- cutoff for the `b`-block start
  have hMcutB : halfRatioCutoff b ≤ termAbsModulus b (half * δ) := by
    unfold ExpNeg.termAbsModulus; exact Nat.le_add_right _ _
  refine ⟨K + termAbsModulus b (half * δ), fun m hm => ?_⟩
  have hKm : K ≤ m := Nat.le_trans (Nat.le_add_right _ _) hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hKm  -- m = K + d
  -- split cornerAbsAdd at K
  have hsplit : (cornerAbsAdd a b (K + d)).eqv
      (finSum (cornerAbsTermAdd a b (K + d)) K
        + finSum (fun j => cornerAbsTermAdd a b (K + d) (K + j)) d) :=
    finSum_split (cornerAbsTermAdd a b (K + d)) K d
  -- Part 1 ≤ Ba·δ : for i < K the `b`-block starts past the b-cutoff so ≤ δ
  have hpart1 : finSum (cornerAbsTermAdd a b (K + d)) K ≤ Ba * δ := by
    have hterm1 : ∀ i, i < K → cornerAbsTermAdd a b (K + d) i ≤ ExpNeg.termAbs a i * δ := by
      intro i hiK
      have hblock : ExpNeg.blockAbs b ((K + d) - i) i ≤ δ := by
        have hmodi : termAbsModulus b (half * δ) ≤ (K + d) - i := by omega
        exact expNeg_tail_bound b hb δ hδnn ((K + d) - i)
          (Nat.le_trans hMcutB hmodi)
          (termAbs_le_of_modulus_le b (half * δ) hb hhδ ((K + d) - i) hmodi) i
      exact Q'.mul_le_mul_of_nonneg_left _ _ (ExpNeg.termAbs a i) hblock
        (termAbs_nonneg a ha i)
    refine Q'.le_trans' _ _ _
      (finSum_le_lt (cornerAbsTermAdd a b (K + d)) (fun i => ExpNeg.termAbs a i * δ) K hterm1) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (finSum_mul_const (ExpNeg.termAbs a) δ K))) ?_
    rw [← partialSumAbs_eq_finSum]
    exact Q'.mul_le_mul_of_nonneg_right (partialSumAbs a K) Ba δ (hBa K) hδnn
  -- Part 2 ≤ δ·Bb : for K ≤ i the `a`-weights sum to a-tail ≤ δ, blocks ≤ Bb
  have hpart2 : finSum (fun j => cornerAbsTermAdd a b (K + d) (K + j)) d ≤ δ * Bb := by
    have hterm2 : ∀ j, (fun j => cornerAbsTermAdd a b (K + d) (K + j)) j
        ≤ ExpNeg.termAbs a (K + j) * Bb := by
      intro j
      show ExpNeg.termAbs a (K + j) * ExpNeg.blockAbs b ((K + d) - (K + j)) (K + j)
          ≤ ExpNeg.termAbs a (K + j) * Bb
      exact Q'.mul_le_mul_of_nonneg_left _ _ (ExpNeg.termAbs a (K + j))
        (blockAbs_le_bound b hb hBb _ _) (termAbs_nonneg a ha (K + j))
    refine Q'.le_trans' _ _ _
      (finSum_le_finSum_of_termwise (fun j => cornerAbsTermAdd a b (K + d) (K + j))
        (fun j => ExpNeg.termAbs a (K + j) * Bb) hterm2 d) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (finSum_mul_const (fun j => ExpNeg.termAbs a (K + j)) Bb d))) ?_
    rw [← blockAbs_eq_finSum]
    have hblockK : ExpNeg.blockAbs a K d ≤ δ :=
      expNeg_tail_bound a ha δ hδnn K hKcut
        (termAbs_le_of_modulus_le a (half * δ) ha hhδ K hKM) d
    exact Q'.mul_le_mul_of_nonneg_right (ExpNeg.blockAbs a K d) δ Bb hblockK hBb0
  -- combine: Ba·δ + δ·Bb ≃ (Ba+Bb)·δ ≤ ε
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add hpart1 hpart2) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hδ
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (Ba * δ) (δ * Bb) (Bb * δ) (Q'.mul_comm_eqv δ Bb)) ?_
  exact Q'.eqv_symm (Q'.add_mul_eqv Ba Bb δ)

end YMGap.Constructive

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.cornerAdd_le_cornerAbs
#print axioms YMGap.Constructive.neg_cornerAdd_le_cornerAbs
#print axioms YMGap.Constructive.cornerAbsAdd_le
