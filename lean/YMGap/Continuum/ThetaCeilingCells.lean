/-
# Interval certificate engine for the actual signed radial cost (theta ceiling)

For the SAME constructed limit `productRadialCostCReal` (JacobiProductRadialLimit), this file reduces a
whole-interval ceiling `D_∞(x) ≤ C` on `x ∈ [-1,1]` to a finite rational check:

* `sTerm_anti`: each actual factor ratio `r_i(x) = 2c_i/(1+2c_i x+c_i²)` is antitone on `[-1,∞)`.
* `summand_le_upPos` / `summand_le_upNeg`: cell enclosures.  On a cell `[a,b] ⊆ [0,1]`,
  `d_i(x) ≤ (1-a²)·r_i(a)² + b·r_i(a)`; on a cell `[a,b] ⊆ [-1,0]`, `d_i(x) ≤ (1-b²)·r_i(a)² + b·r_i(b)`.
  Each is an explicit cleared sum of nonnegative products, so no derivative or Lipschitz constant is needed:
  monotone interval enclosure replaces the Lipschitz step.
* `cost_le_head_add_pay`: `D_{N+L}(x) ≤ D_N(x) + 4c_N/(1-w²)` once `c_N ≤ 1/8`.  This reuses
  `radialSummand_bounds` and `sTerm_finite_tail_le`; the starting `N` is explicit data.
* `chain_bound`, `ceiling_of_chain`: a decidable chain of cells covering `[-1,1]` with
  `Σ_{i<N} up_i(cell) ≤ C - 4c_N/(1-w²)` gives `CReal.leRat D_∞(x) C` for every rational `x ∈ [-1,1]`.

The "addition + tail gives D_N ≤ 3/[2(1-w)]" shortcut is NOT used.  This is not an addition identity, a
Poisson identity, an angular or Haar certificate, or a physical statement.
-/

import YMGap.Continuum.JacobiProductRadialLimit

namespace YMGap.Continuum.ThetaCeilingCells

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.JacobiHeatRadialMixtureCancellation
open YMGap.Continuum.JacobiProductRadialSignedTail
open YMGap.Continuum.JacobiProductRadialLimit

local infix:50 " ≈ " => Q'.eqv

theorem nonneg_of_eqv {a b : Q'} (h : a ≈ b) (hb : (0 : Q') ≤ b) : (0 : Q') ≤ a :=
  Q'.le_trans' _ _ _ hb (Q'.ge_of_eqv h)

theorem one_add_nonneg {x : Q'} (hx : (-1 : Q') ≤ x) : (0 : Q') ≤ 1 + x :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv 1)) (Q'.add_le_add_left 1 (-1) x hx)

/-- The actual factor ratio is antitone in `x` on `[-1,∞)`. -/
theorem sTerm_anti {w a x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (ha : (-1 : Q') ≤ a) (hax : a ≤ x) (i : Nat) :
    HKConv.sTerm w x i ≤ HKConv.sTerm w a i := by
  have hc : (0 : Q') ≤ HKPos.geoAmp w i := Q'.le_of_lt (HKPos.pow_succ_pos_lt_one hw0 hw1 (2*i)).1
  have hr := HKConv.sTerm_nonneg hw0 hw1 ha i
  have hx : (-1 : Q') ≤ x := Q'.le_trans' _ _ _ ha hax
  apply HKConv.divPos_le_of_le (HKConv.factor_num_pos hw0 hw1 hx i)
  have hpin : HKConv.sTerm w a i * HKPos.factor (HKPos.geoAmp w i) a ≈ HKPos.two (HKPos.geoAmp w i) :=
    HKConv.divPos_mul_eqv (HKConv.factor_num_pos hw0 hw1 ha i)
  have hf : HKPos.factor (HKPos.geoAmp w i) a ≤ HKPos.factor (HKPos.geoAmp w i) x :=
    Q'.add_le_add_left 1 _ _ (Q'.add_le_add_right _ _ _
      (Q'.mul_le_mul_of_nonneg_left a x _ hax (HKPos.two_nonneg hc)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpin) (Q'.mul_le_mul_of_nonneg_left _ _ _ hf hr)

/-- Upper enclosure of `d_i` on a cell `[a,b] ⊆ [0,1]`. -/
def upPos (w a b : Q') (i : Nat) : Q' :=
  radialA a * (HKConv.sTerm w a i * HKConv.sTerm w a i) + b * HKConv.sTerm w a i

/-- Upper enclosure of `d_i` on a cell `[a,b] ⊆ [-1,0]`. -/
def upNeg (w a b : Q') (i : Nat) : Q' :=
  radialA b * (HKConv.sTerm w a i * HKConv.sTerm w a i) + b * HKConv.sTerm w b i

theorem summand_le_upPos {w a b x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (ha0 : (0 : Q') ≤ a) (hax : a ≤ x) (hxb : x ≤ b) (hx1 : x ≤ (1 : Q')) (i : Nat) :
    radialSummand w x i ≤ upPos w a b i := by
  have ha : (-1 : Q') ≤ a := Q'.le_trans' _ _ _ (by decide) ha0
  have hx : (-1 : Q') ≤ x := Q'.le_trans' _ _ _ ha hax
  have hx0 : (0 : Q') ≤ x := Q'.le_trans' _ _ _ ha0 hax
  have hr := HKConv.sTerm_nonneg hw0 hw1 hx i
  have hrh := HKConv.sTerm_nonneg hw0 hw1 ha i
  have hd := Q'.sub_nonneg_of_le (sTerm_anti hw0 hw1 ha hax i)
  apply Q'.le_of_sub_nonneg
  refine nonneg_of_eqv (poly_identity_of_normal_eq
    (.add (.add (.mul (.add (.const 1) (.neg (.mul (.var 1) (.var 1)))) (.mul (.var 3) (.var 3)))
        (.mul (.var 2) (.var 3)))
      (.neg (.add (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 0)))) (.mul (.var 4) (.var 4)))
        (.mul (.var 0) (.var 4)))))
    (.add (.add (.add
      (.mul (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.var 0)))
        (.mul (.add (.var 3) (.neg (.var 4))) (.add (.var 3) (.var 4))))
      (.mul (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.var 1))) (.mul (.var 3) (.var 3))))
      (.mul (.add (.var 2) (.neg (.var 0))) (.var 3)))
      (.mul (.var 0) (.add (.var 3) (.neg (.var 4)))))
    (by decide) (fun | 0 => x | 1 => a | 2 => b | 3 => HKConv.sTerm w a i | _ => HKConv.sTerm w x i)) ?_
  exact Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hx1) (one_add_nonneg hx))
      (Q'.mul_nonneg _ _ hd (Q'.zero_le_add _ _ hrh hr)))
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hax) (Q'.zero_le_add _ _ hx0 ha0))
      (Q'.mul_nonneg _ _ hrh hrh)))
    (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hxb) hrh))
    (Q'.mul_nonneg _ _ hx0 hd)

theorem summand_le_upNeg {w a b x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (ha : (-1 : Q') ≤ a) (hax : a ≤ x) (hxb : x ≤ b) (hb0 : b ≤ (0 : Q')) (i : Nat) :
    radialSummand w x i ≤ upNeg w a b i := by
  have hx : (-1 : Q') ≤ x := Q'.le_trans' _ _ _ ha hax
  have hx1 : x ≤ (1 : Q') := Q'.le_trans' _ _ _ hxb (Q'.le_trans' _ _ _ hb0 (by decide))
  have hr := HKConv.sTerm_nonneg hw0 hw1 hx i
  have hrh := HKConv.sTerm_nonneg hw0 hw1 ha i
  have hd := Q'.sub_nonneg_of_le (sTerm_anti hw0 hw1 ha hax i)
  have hl := Q'.sub_nonneg_of_le (sTerm_anti hw0 hw1 hx hxb i)
  have hnb := Q'.sub_nonneg_of_le hb0
  have hbx := Q'.sub_nonneg_of_le hxb
  apply Q'.le_of_sub_nonneg
  refine nonneg_of_eqv (poly_identity_of_normal_eq
    (.add (.add (.mul (.add (.const 1) (.neg (.mul (.var 2) (.var 2)))) (.mul (.var 3) (.var 3)))
        (.mul (.var 2) (.var 5)))
      (.neg (.add (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 0)))) (.mul (.var 4) (.var 4)))
        (.mul (.var 0) (.var 4)))))
    (.add (.add (.add
      (.mul (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.var 0)))
        (.mul (.add (.var 3) (.neg (.var 4))) (.add (.var 3) (.var 4))))
      (.mul (.mul (.add (.var 2) (.neg (.var 0)))
          (.add (.add (.var 2) (.neg (.var 0))) (.add (.add (.const 0) (.neg (.var 2)))
            (.add (.const 0) (.neg (.var 2))))))
        (.mul (.var 3) (.var 3))))
      (.mul (.add (.var 2) (.neg (.var 0))) (.var 4)))
      (.mul (.add (.const 0) (.neg (.var 2))) (.add (.var 4) (.neg (.var 5)))))
    (by decide) (fun | 0 => x | 1 => a | 2 => b | 3 => HKConv.sTerm w a i | 4 => HKConv.sTerm w x i
                     | _ => HKConv.sTerm w b i)) ?_
  exact Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hx1) (one_add_nonneg hx))
      (Q'.mul_nonneg _ _ hd (Q'.zero_le_add _ _ hrh hr)))
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hbx (Q'.zero_le_add _ _ hbx (Q'.zero_le_add _ _ hnb hnb)))
      (Q'.mul_nonneg _ _ hrh hrh)))
    (Q'.mul_nonneg _ _ hbx hr))
    (Q'.mul_nonneg _ _ hnb hl)

/-- A certified cell: `[a,b]` inside `[0,1]` or `[-1,0]` with summed enclosure at most `B`. -/
def cellOK (w B : Q') (N : Nat) (a b : Q') : Prop :=
  a ≤ b ∧ (((0 : Q') ≤ a ∧ finSum (upPos w a b) N ≤ B) ∨ (b ≤ (0 : Q') ∧ finSum (upNeg w a b) N ≤ B))

instance (w B : Q') (N : Nat) (a b : Q') : Decidable (cellOK w B N a b) := by
  unfold cellOK; exact inferInstance

theorem cell_bound {w B a b x : Q'} {N : Nat} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (ha : (-1 : Q') ≤ a) (hc : cellOK w B N a b) (hax : a ≤ x) (hxb : x ≤ b) (hx1 : x ≤ (1 : Q')) :
    productRadialCost (HKConv.sTerm w x) N x ≤ B := by
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (radialSummand_sum_pin w x N)) ?_
  rcases hc.2 with ⟨ha0, hs⟩ | ⟨hb0, hs⟩
  · exact Q'.le_trans' _ _ _ (finSum_le_lt _ _ N fun i _ => summand_le_upPos hw0 hw1 ha0 hax hxb hx1 i) hs
  · exact Q'.le_trans' _ _ _ (finSum_le_lt _ _ N fun i _ => summand_le_upNeg hw0 hw1 ha hax hxb hb0 i) hs

/-- Decidable chain of consecutive cells `a = p₀ ≤ p₁ ≤ …`. -/
def chainOK (w B : Q') (N : Nat) : Q' → List Q' → Bool
  | _, [] => true
  | a, b :: rest => decide (cellOK w B N a b) && chainOK w B N b rest

def lastQ : Q' → List Q' → Q'
  | a, [] => a
  | _, b :: rest => lastQ b rest

theorem le_of_not_le' {x y : Q'} (h : ¬ x ≤ y) : y ≤ x :=
  Int.le_of_lt (Int.lt_of_not_ge h)

theorem chain_bound {w B x : Q'} {N : Nat} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hx1 : x ≤ (1 : Q')) :
    ∀ (rest : List Q') (a b : Q'), chainOK w B N a (b :: rest) = true → (-1 : Q') ≤ a → a ≤ x →
      x ≤ lastQ b rest → productRadialCost (HKConv.sTerm w x) N x ≤ B
  | [], a, b, h, ha, hax, hxb => by
      simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
      exact cell_bound hw0 hw1 ha h.1 hax hxb hx1
  | b' :: r, a, b, h, ha, hax, hxl => by
      simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
      by_cases hxb : x ≤ b
      · exact cell_bound hw0 hw1 ha h.1 hax hxb hx1
      · exact chain_bound hw0 hw1 hx1 r b b' (by simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq]; exact h.2)
          (Q'.le_trans' _ _ _ ha h.1.1) (le_of_not_le' hxb) hxl

/-- Signed tail from an explicit onset `c_N ≤ 1/8`: `D_{N+L} ≤ D_N + 4c_N/(1-w²)`. -/
theorem cost_le_head_add_pay {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) (hN : HKPos.geoAmp w N ≤ eighth) (L : Nat) :
    productRadialCost (HKConv.sTerm w x) (N+L) x ≤
      productRadialCost (HKConv.sTerm w x) N x + radialTailPayment w N := by
  have hsplit := finSum_split (radialSummand w x) N L
  have hd : finSum (fun j => radialSummand w x (N+j)) L ≤ finSum (fun j => HKConv.sTerm w x (N+j)) L :=
    finSum_le_lt _ _ L fun j _ => (radialSummand_bounds hw0 hw1 hx0 hx1 (N+j)).2
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (radialSummand_sum_pin w x (N+L))) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _
    (Q'.le_trans' _ _ _ hd (sTerm_finite_tail_le hw0 hw1 hx0 N hN L))) ?_
  exact Q'.add_le_add_right _ _ _ (Q'.le_of_eqv (radialSummand_sum_pin w x N))

/-- **Whole-interval ceiling from a cell chain (PROVED).**  Every rational `x ∈ [-1,1]` gets
`D_∞(x) ≤ C` for the SAME constructed limit, from an explicit onset `N` with `c_N ≤ 1/8`
and a chain from `-1` to `1` certified against the budget `C - 4c_N/(1-w²)`. -/
theorem ceiling_of_chain {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (C : Q') (N : Nat)
    (hN : HKPos.geoAmp w N ≤ eighth) (b : Q') (pts : List Q')
    (hch : chainOK w (C + -(radialTailPayment w N)) N (-1) (b :: pts) = true)
    (hlast : (1 : Q') ≤ lastQ b pts) (x : Q') (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.leRat (productRadialCostCReal hw0 hw1 hx0 hx1) C := by
  have hhead := chain_bound hw0 hw1 hx1 pts (-1) b hch (Q'.le_refl' _) hx0 (Q'.le_trans' _ _ _ hx1 hlast)
  refine CReal.leRat_of_eventually ⟨N, fun n hn => ?_⟩
  rw [productRadialCostCReal_approx]
  have he : N + (n - N) = n := Nat.add_sub_of_le hn
  have h := cost_le_head_add_pay hw0 hw1 hx0 hx1 N hN (n - N)
  rw [he] at h
  refine Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hhead) ?_)
  exact Q'.le_of_eqv (poly_identity_of_normal_eq (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
    (by decide) (fun | 0 => C | _ => radialTailPayment w N))

end YMGap.Continuum.ThetaCeilingCells
