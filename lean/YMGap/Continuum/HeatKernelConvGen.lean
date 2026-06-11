/-
Heat-kernel pointwise positivity, Part 3-GEN (gap G1, the `S`-factor for ALL a) —
lifting the manifestly-nonnegative sum

    S(x) = Σ_{n≥1} 2·a^{2n-1} / (1 + 2·a^{2n-1}·x + a^{4n-2})

from the small-`a` regime `a·a ≤ 1/2` to ALL `a ∈ (0,1)`.

# What this module closes

`Continuum/HeatKernelConv.lean` (`HKConv.sConvCReal`) built `S(x)` as a genuine
convergent `CReal`, but only under the smallness hypothesis `a·a ≤ 1/2`.  The
restriction came from feeding the partial sums to `Continuum.crealOfGeoIncrement`,
whose decay base is hardcoded to `1/2`: the per-term bound
`sTerm a x l ≤ Cstar a · (a·a)^l` is EXACT (no smallness), but dominating
`(a·a)^l ≤ (1/2)^l` needs `a·a ≤ 1/2`.

This module removes that restriction by building a GENERAL-BASE geometric tail
engine `crealOfGeoIncrementBase`, parametrised by the decay base `r = a·a < 1`
itself (no domination by `1/2`).  The new ingredient is the explicit
`r^n → 0` modulus for a general rational base `r ∈ [0,1)` — exactly the missing
rational lemma named in the `KPLimit.lean` docstring — proved here via a
multiplicative Bernoulli bound `(1 + n·(1−r))·r^n ≤ 1` and the Archimedean
`RatNat.le_ofNat_toNat`.

# The deliverable

  * `sConvCReal_general a x (0<a) (a<1) (−1≤x)` — `S(x)` as a convergent `CReal`
    for ALL `a ∈ (0,1)`, `−1 ≤ x`, with `approx N = HKConv.Spart a x N` and the
    explicit base-`(a·a)` modulus.  No `a·a ≤ 1/2`.
  * `sConvCReal_general_approx_nonneg`, `sConvCReal_general_geRat_zero`.
  * `R_geRat_zero_of_theta_general` — `R = Θ·S ≥ 0` for all `a ∈ (0,1)`, GIVEN
    any nonneg-approx `CReal` `Θ` realizing `ϑ₃/2a`.

# The precise remaining gap (honest, per AGENTS.md Rule 6)

  (G1-ϑ₃, all a) The `ϑ₃` partial-PRODUCT factor is still built (in
       `ThetaConv.lean`) only under the smallness regime; the general-`a` `ϑ₃`
       lift (whose product-MAGNITUDE bound needs the smallness) is NOT done
       here.  The assembled `R = ϑ₃·S ≥ 0` is delivered here only in the
       `Θ`-hypothetical form `R_geRat_zero_of_theta_general`.

  (G2) The IDENTITY `K_t(x) = (ϑ₃/2a)·S(x)` remains the separate analytic gap.

Everything below is fully proved and axiom-gated.  No `Classical.*`, no
`native_decide`, no `sorry`.
-/

import YMGap.Continuum.HeatKernelConv
import YMGap.Continuum.HeatKernelPos
import YMGap.Continuum.HeatKernelPos2
import YMGap.Continuum.KPLimit
import YMGap.Constructive.Reals
import YMGap.Constructive.CRealMul
import YMGap.Constructive.ExpPos
import YMGap.Constructive.RationalTail
import YMGap.Constructive.HalfPow
import YMGap.Constructive.CharacterTail
import YMGap.Constructive.RatNat

namespace YMGap.Continuum.HKConvGen

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HKConv
open YMGap.Continuum.HKPos
open YMGap.Constructive.RationalTail
open YMGap.Constructive.HalfPow

/-! ## 0. `Q'` left-cancellation of a strictly-positive factor -/

/-- `Int` regrouping: `(p·x)·(q·y) = (q·p)·(x·y)`.  Proved from
`Int.mul_assoc`/`Int.mul_comm` only (no `ring`). -/
theorem int_regroup (p x q y : Int) : (p * x) * (q * y) = (q * p) * (x * y) := by
  rw [Int.mul_assoc, Int.mul_left_comm x q y, ← Int.mul_assoc, Int.mul_comm p q]

/-- **Left-cancellation:** `0 < c → c·a ≤ c·b → a ≤ b`.  Reduces to the `Int`
cross-product and `Int.le_of_mul_le_mul_right` after stripping the common
positive factor `c.num·c.den`. -/
theorem mul_le_mul_left_cancel {a b c : Q'} (hc : (0 : Q') < c)
    (h : c * a ≤ c * b) : a ≤ b := by
  have hcnum : (0 : Int) < c.num := CReal.num_pos_of_pos hc
  have hcden : (0 : Int) < (c.den : Int) := by exact_mod_cast Q'.den_pos c
  have hcprod : (0 : Int) < c.num * (c.den : Int) := Int.mul_pos hcnum hcden
  have h0 : (c * a).num * ((c * b).den : Int) ≤ (c * b).num * ((c * a).den : Int) := h
  have hca_num : (c * a).num = c.num * a.num := rfl
  have hcb_num : (c * b).num = c.num * b.num := rfl
  have hca_den : ((c * a).den : Int) = (c.den : Int) * (a.den : Int) := by
    show (((c.den * a.den - 1) + 1 : Nat) : Int) = (c.den : Int) * (a.den : Int)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Q'.den_pos c) (Q'.den_pos a))))]
    exact Int.natCast_mul c.den a.den
  have hcb_den : ((c * b).den : Int) = (c.den : Int) * (b.den : Int) := by
    show (((c.den * b.den - 1) + 1 : Nat) : Int) = (c.den : Int) * (b.den : Int)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Q'.den_pos c) (Q'.den_pos b))))]
    exact Int.natCast_mul c.den b.den
  rw [hca_num, hcb_num, hca_den, hcb_den] at h0
  -- h0 : (c.num*a.num)*(c.den*b.den) ≤ (c.num*b.num)*(c.den*a.den)
  -- Goal : a.num*b.den ≤ b.num*a.den
  show a.num * (b.den : Int) ≤ b.num * (a.den : Int)
  apply Int.le_of_mul_le_mul_right (a := c.num * (c.den : Int)) _ hcprod
  -- Goal: (a.num*b.den)*(c.num*c.den) ≤ (b.num*a.den)*(c.num*c.den)
  -- LHS = (c.num*c.num... ) regroup both sides to match h0.
  -- (a.num*b.den)*(c.num*c.den) = (c.num*a.num)*(b.den*c.den)
  have eL : (a.num * (b.den : Int)) * (c.num * (c.den : Int))
          = (c.num * a.num) * ((c.den : Int) * (b.den : Int)) := by
    rw [int_regroup a.num (b.den : Int) c.num (c.den : Int)]
    rw [Int.mul_comm (b.den : Int) (c.den : Int)]
  have eR : (b.num * (a.den : Int)) * (c.num * (c.den : Int))
          = (c.num * b.num) * ((c.den : Int) * (a.den : Int)) := by
    rw [int_regroup b.num (a.den : Int) c.num (c.den : Int)]
    rw [Int.mul_comm (a.den : Int) (c.den : Int)]
  rw [eL, eR]
  exact h0

/-! ## 1. Multiplicative Bernoulli bound `(bScale g n)·r^n ≤ 1`

For `r ∈ [0,1]`, set `g = 1 + (−r) = 1 − r ≥ 0`.  The accumulator
`bScale g n = 1 + (g + … + g)` (n copies) satisfies `bScale g n · r^n ≤ 1`.
This is the multiplicative form of Bernoulli's inequality, kept additively so no
`Q'.ofNat`-arithmetic is needed beyond the recursion `bScale g (n+1) = bScale g n + g`. -/

/-- The additive accumulator `bScale g n = 1 + n·g` (built additively). -/
def bScale (g : Q') : Nat → Q'
  | 0 => 1
  | n + 1 => bScale g n + g

@[simp] theorem bScale_succ (g : Q') (n : Nat) :
    bScale g (n + 1) = bScale g n + g := rfl

/-- `1 ≤ bScale g n` for `0 ≤ g` (each step adds a nonnegative `g`). -/
theorem bScale_one_le {g : Q'} (hg : (0 : Q') ≤ g) : ∀ n, (1 : Q') ≤ bScale g n
  | 0 => Q'.le_refl' 1
  | n + 1 => by
      rw [bScale_succ]
      exact Q'.le_trans' _ _ _ (bScale_one_le hg n)
        (Q'.add_le_self_of_nonneg (bScale g n) g hg)

theorem bScale_nonneg {g : Q'} (hg : (0 : Q') ≤ g) (n : Nat) : (0 : Q') ≤ bScale g n :=
  Q'.le_trans' _ _ _ (Q'.le_of_lt (CReal.pos_of_num_pos (by decide))) (bScale_one_le hg n)

/-- The Bernoulli step `bScale g (n+1) · r ≤ bScale g n`, where `g = 1 + (−r)`.
Proof: `bScale g n − bScale g (n+1)·r = bScale g n·(1−r) − g·r = g·(bScale g n − r) ≥ 0`
since `bScale g n ≥ 1 ≥ r`. -/
theorem bScale_step {r : Q'} (hr0 : (0 : Q') ≤ r) (hr1 : r ≤ (1 : Q')) (n : Nat) :
    bScale (1 + (-r)) (n + 1) * r ≤ bScale (1 + (-r)) n := by
  let g := (1 + (-r))
  show bScale g (n + 1) * r ≤ bScale g n
  have hg_nn : (0 : Q') ≤ g := Q'.sub_nonneg_of_le (c := r) (d := 1) hr1
  have hBn1 : (1 : Q') ≤ bScale g n := bScale_one_le hg_nn n
  -- bScale g (n+1)·r = (bScale g n + g)·r = bScale g n·r + g·r
  have he1 : (bScale g (n + 1) * r).eqv (bScale g n * r + g * r) := by
    rw [bScale_succ]
    exact Q'.add_mul_eqv (bScale g n) g r
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he1) ?_
  -- bScale g n·r + g·r ≤ bScale g n.  Show via: bScale g n·r + g·r ≤ bScale g n·r + g·(bScale g n)
  -- and bScale g n·r + g·bScale g n = bScale g n·(r + g) and r + g = 1.
  -- g·r ≤ g·bScale g n  (r ≤ 1 ≤ bScale g n, g ≥ 0)
  have hr_le_Bn : r ≤ bScale g n := Q'.le_trans' _ _ _ hr1 hBn1
  have hstep : bScale g n * r + g * r ≤ bScale g n * r + g * bScale g n :=
    Q'.add_le_add_left (bScale g n * r) (g * r) (g * bScale g n)
      (Q'.mul_le_mul_of_nonneg_left r (bScale g n) g hr_le_Bn hg_nn)
  refine Q'.le_trans' _ _ _ hstep ?_
  -- bScale g n·r + g·bScale g n = bScale g n·r + bScale g n·g = bScale g n·(r+g) = bScale g n·1 = bScale g n
  have heq : (bScale g n * r + g * bScale g n).eqv (bScale g n) := by
    -- g·bScale g n ≃ bScale g n·g
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (bScale g n * r) _ _ (Q'.mul_comm_eqv g (bScale g n))) ?_
    -- bScale g n·r + bScale g n·g ≃ bScale g n·(r + g)
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_add_eqv (bScale g n) r g)) ?_
    -- r + g = r + (1 + (-r)) ≃ 1
    have hrg : (r + g).eqv (1 : Q') := by
      show (r + (1 + (-r))).eqv (1 : Q')
      -- r + (1 + (-r)) ≃ (r + (-r)) + 1 ... use comm/assoc
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left r _ _ (Q'.add_comm_eqv 1 (-r))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv r (-r) 1)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (r + (-r)) 0 1 (Q'.add_neg_self_eqv r)) ?_
      show ((0 : Q') + 1).eqv (1 : Q')
      exact Q'.zero_add' 1 ▸ Q'.eqv_refl 1
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (bScale g n) _ _ hrg) ?_
    exact Q'.mul_one_eqv (bScale g n)
  exact Q'.le_of_eqv heq

/-- **Multiplicative Bernoulli:** `bScale (1 + (−r)) n · r^n ≤ 1` for `0 ≤ r ≤ 1`.
Induction on `n`, using `bScale_step` and `0 ≤ r^n`. -/
theorem bernoulli_pow {r : Q'} (hr0 : (0 : Q') ≤ r) (hr1 : r ≤ (1 : Q')) :
    ∀ n, bScale (1 + (-r)) n * r ^ n ≤ (1 : Q')
  | 0 => by
      show bScale (1 + (-r)) 0 * r ^ 0 ≤ (1 : Q')
      exact Q'.le_of_eqv (Q'.mul_one_eqv (bScale (1 + (-r)) 0))
  | n + 1 => by
      let g := (1 + (-r))
      show bScale g (n + 1) * r ^ (n + 1) ≤ (1 : Q')
      -- bScale g (n+1)·r^(n+1) = (bScale g (n+1)·r)·r^n ≤ bScale g n · r^n ≤ 1
      have hrn_nn : (0 : Q') ≤ r ^ n := Q'.pow_nonneg r hr0 n
      have he : (bScale g (n + 1) * r ^ (n + 1)).eqv
          ((bScale g (n + 1) * r) * r ^ n) := by
        show (bScale g (n + 1) * (r * r ^ n)).eqv ((bScale g (n + 1) * r) * r ^ n)
        exact Q'.eqv_symm (Q'.mul_assoc_eqv (bScale g (n + 1)) r (r ^ n))
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he) ?_
      -- (bScale g (n+1)·r)·r^n ≤ (bScale g n)·r^n
      have hstep : (bScale g (n + 1) * r) * r ^ n ≤ bScale g n * r ^ n :=
        Q'.mul_le_mul_of_nonneg_right _ _ (r ^ n) (bScale_step hr0 hr1 n) hrn_nn
      exact Q'.le_trans' _ _ _ hstep (bernoulli_pow hr0 hr1 n)

/-! ## 2. The explicit `r^n → 0` modulus (general base `r ∈ (0,1)`) -/

/-- `r^n` is antitone in `n` for `0 ≤ r ≤ 1`: `m ≤ n → r^n ≤ r^m`. -/
theorem pow_base_le_succ {r : Q'} (hr0 : (0 : Q') ≤ r) (hr1 : r ≤ (1 : Q')) (n : Nat) :
    r ^ (n + 1) ≤ r ^ n := by
  show r * r ^ n ≤ r ^ n
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right r 1 (r ^ n) hr1 (Q'.pow_nonneg r hr0 n)) ?_
  exact Q'.le_of_eqv (Q'.one_mul_eqv (r ^ n))

theorem pow_base_add_le {r : Q'} (hr0 : (0 : Q') ≤ r) (hr1 : r ≤ (1 : Q')) (m : Nat) :
    ∀ d, r ^ (m + d) ≤ r ^ m
  | 0 => Q'.le_refl' _
  | d + 1 => by
      have e : m + (d + 1) = (m + d) + 1 := by omega
      rw [e]
      exact Q'.le_trans' _ _ _ (pow_base_le_succ hr0 hr1 (m + d))
        (pow_base_add_le hr0 hr1 m d)

theorem pow_base_antitone {r : Q'} (hr0 : (0 : Q') ≤ r) (hr1 : r ≤ (1 : Q'))
    {m n : Nat} (h : m ≤ n) : r ^ n ≤ r ^ m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact pow_base_add_le hr0 hr1 m d

/-- `Q'.ofNat (n+1) ≃ Q'.ofNat n + 1`.  Both sides have denominator `1`; the
numerator identity is `Int.ofNat (n+1) = Int.ofNat n + 1`. -/
theorem ofNat_succ_eqv (n : Nat) : (Q'.ofNat (n + 1)).eqv (Q'.ofNat n + 1) := by
  show (Q'.ofNat (n + 1)).num * ((Q'.ofNat n + 1).den : Int)
     = (Q'.ofNat n + 1).num * ((Q'.ofNat (n + 1)).den : Int)
  show (Int.ofNat (n + 1)) * (1 : Int) = (Int.ofNat n * 1 + 1 * 1) * (1 : Int)
  rw [Int.mul_one, Int.mul_one, Int.mul_one, Int.one_mul]
  rfl

/-- `ofNat n · g ≤ bScale g n` for `0 ≤ g` (the additive accumulator dominates
`n` copies of `g`).  Induction on `n`. -/
theorem ofNat_mul_le_bScale {g : Q'} (hg : (0 : Q') ≤ g) :
    ∀ n, Q'.ofNat n * g ≤ bScale g n
  | 0 => by
      -- ofNat 0 · g ≃ 0 · g ≃ 0 ≤ 1 = bScale g 0
      have h00 : (Q'.ofNat 0).eqv (0 : Q') := rfl
      have hz : (Q'.ofNat 0 * g).eqv (0 : Q') :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (Q'.ofNat 0) 0 g h00)
          (Q'.zero_mul_eqv g)
      refine Q'.le_trans' (Q'.ofNat 0 * g) (0 : Q') (bScale g 0) (Q'.le_of_eqv hz) ?_
      exact bScale_nonneg hg 0
  | k + 1 => by
      rw [bScale_succ]
      have hsucc : (Q'.ofNat (k + 1) * g).eqv (Q'.ofNat k * g + g) := by
        refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ g (ofNat_succ_eqv k)) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (Q'.ofNat k) 1 g) ?_
        exact Q'.add_eqv_congr_left (Q'.ofNat k * g) _ _ (Q'.one_mul_eqv g)
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsucc) ?_
      exact Q'.add_le_add_right _ _ g (ofNat_mul_le_bScale hg k)

/-- The explicit modulus cutoff for `r^n ≤ δ`: `N = (1/((1−r)·δ)).num.toNat`,
where `1/((1−r)·δ)` is the genuine `Q'` quotient `divPos 1 ((1+(−r))·δ)`. -/
def powBaseCutoff (r δ : Q') : Nat :=
  (HKConv.divPos 1 ((1 + (-r)) * δ)).num.toNat

/-- **The general-base modulus (at the cutoff).**  For `0 < r < 1` and `0 < δ`,
`r^N ≤ δ` with `N = powBaseCutoff r δ`.

From `bScale g N · r^N ≤ 1` (Bernoulli) and `1 ≤ bScale g N · δ` (Archimedean
choice of `N`), `bScale g N · r^N ≤ bScale g N · δ`, then left-cancel the
strictly-positive `bScale g N`. -/
theorem pow_base_le_cutoff {r δ : Q'}
    (hr0 : (0 : Q') < r) (hr1 : r < (1 : Q')) (hδ : (0 : Q') < δ) :
    r ^ (powBaseCutoff r δ) ≤ δ := by
  let g := (1 + (-r))
  have hg_pos : (0 : Q') < g := HKPos.one_sub_pos hr1
  have hg_nn : (0 : Q') ≤ g := Q'.le_of_lt hg_pos
  have hgδ_pos : (0 : Q') < g * δ := HKPos.q_mul_pos hg_pos hδ
  have hgδnum : 0 < (g * δ).num := CReal.num_pos_of_pos hgδ_pos
  -- w = 1/(g·δ) = divPos 1 (g·δ) ;  N := powBaseCutoff r δ = w.num.toNat ;  w ≤ ofNat N.
  let w := HKConv.divPos 1 (g * δ)
  have hwnn : (0 : Q') ≤ w := HKConv.divPos_nonneg (Q'.le_of_lt (CReal.pos_of_num_pos (by decide)))
  -- N = powBaseCutoff r δ = w.num.toNat (definitionally).
  have hw_le : w ≤ Q'.ofNat (powBaseCutoff r δ) := RatNat.le_ofNat_toNat w hwnn
  show r ^ (powBaseCutoff r δ) ≤ δ
  -- 1 ≤ (ofNat N · g)·δ  via  ofNat N ≥ w and w·(g·δ) ≃ 1.
  have hone_le : (1 : Q') ≤ (Q'.ofNat (powBaseCutoff r δ) * g) * δ := by
    have hmul : w * (g * δ) ≤ Q'.ofNat (powBaseCutoff r δ) * (g * δ) :=
      Q'.mul_le_mul_of_nonneg_right w (Q'.ofNat (powBaseCutoff r δ)) (g * δ) hw_le
        (Q'.le_of_lt hgδ_pos)
    have hw1 : (w * (g * δ)).eqv 1 := HKConv.divPos_mul_eqv hgδnum
    have hle1 : (1 : Q') ≤ Q'.ofNat (powBaseCutoff r δ) * (g * δ) :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv hw1) hmul
    refine Q'.le_trans' _ _ _ hle1 ?_
    exact Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (powBaseCutoff r δ)) g δ))
  -- 1 ≤ bScale g N · δ  (ofNat N · g ≤ bScale g N)
  have hstepA : (1 : Q') ≤ bScale g (powBaseCutoff r δ) * δ := by
    refine Q'.le_trans' _ _ _ hone_le ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ δ (ofNat_mul_le_bScale hg_nn (powBaseCutoff r δ))
      (Q'.le_of_lt hδ)
  -- Bernoulli  bScale g N · r^N ≤ 1
  have hBern : bScale g (powBaseCutoff r δ) * r ^ (powBaseCutoff r δ) ≤ (1 : Q') :=
    bernoulli_pow (Q'.le_of_lt hr0) (Q'.le_of_lt hr1) (powBaseCutoff r δ)
  have hcomb : bScale g (powBaseCutoff r δ) * r ^ (powBaseCutoff r δ)
      ≤ bScale g (powBaseCutoff r δ) * δ := Q'.le_trans' _ _ _ hBern hstepA
  have hBpos : (0 : Q') < bScale g (powBaseCutoff r δ) :=
    Q'.pos_of_lt_of_le (CReal.pos_of_num_pos (by decide))
      (bScale_one_le hg_nn (powBaseCutoff r δ))
  exact mul_le_mul_left_cancel hBpos hcomb

/-- **The general-base modulus (eventual form).**  For `0 < r < 1` and `0 < δ`,
`r^n ≤ δ` for all `n ≥ powBaseCutoff r δ`. -/
theorem pow_base_le {r : Q'}
    (hr0 : (0 : Q') < r) (hr1 : r < (1 : Q')) (δ : Q') (hδ : (0 : Q') < δ) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → r ^ n ≤ δ := by
  refine ⟨powBaseCutoff r δ, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _
    (pow_base_antitone (Q'.le_of_lt hr0) (Q'.le_of_lt hr1) hn)
    (pow_base_le_cutoff hr0 hr1 hδ)

/-! ## 3. The general-base geometric tail engine (decay base `r`, not `1/2`) -/

/-- The single-step increment majorant `geoIncrBase C r l = C·r^l`. -/
def geoIncrBase (C r : Q') (l : Nat) : Q' := C * r ^ l

theorem geoIncrBase_nonneg {C r : Q'} (hC : (0 : Q') ≤ C) (hr : (0 : Q') ≤ r) (l : Nat) :
    (0 : Q') ≤ geoIncrBase C r l :=
  Q'.mul_nonneg _ _ hC (Q'.pow_nonneg r hr l)

/-- The telescoped tail-bound family `geoTailBase C r n = (C·r^n)·H`, where
`H = 1/(1−r) = divPos 1 (1+(−r))` bounds the geometric series `Σ_i r^i`. -/
def geoTailBase (C r : Q') (n : Nat) : Q' :=
  (C * r ^ n) * HKConv.divPos 1 (1 + (-r))

theorem geoTailBase_nonneg {C r : Q'} (hC : (0 : Q') ≤ C) (hr : (0 : Q') ≤ r) (n : Nat) :
    (0 : Q') ≤ geoTailBase C r n :=
  Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hC (Q'.pow_nonneg r hr n))
    (HKConv.divPos_nonneg (Q'.le_of_lt (CReal.pos_of_num_pos (by decide))))

/-- The geometric recurrence `1 + r·H ≤ H` with `H = divPos 1 (1+(−r))` (in fact
equality), for `0 < r < 1`.  Proved by multiplying through by `g = 1+(−r) > 0`
and left-cancelling: `(1 + r·H)·g ≃ g + r·(H·g) ≃ g + r ≃ 1 ≃ H·g`. -/
theorem geom_recurrence {r : Q'} (hr0 : (0 : Q') < r) (hr1 : r < (1 : Q')) :
    (1 : Q') + r * HKConv.divPos 1 (1 + (-r)) ≤ HKConv.divPos 1 (1 + (-r)) := by
  let g := (1 + (-r))
  have hg_pos : (0 : Q') < g := HKPos.one_sub_pos hr1
  have hgnum : 0 < g.num := CReal.num_pos_of_pos hg_pos
  let H := HKConv.divPos 1 g
  show (1 : Q') + r * H ≤ H
  -- It suffices to show g·(1 + r·H) ≤ g·H  (then left-cancel g > 0).
  apply mul_le_mul_left_cancel hg_pos
  -- g·(1 + r·H) ≃ g + r ≃ 1 ;  g·H ≃ H·g ≃ 1.  So both ≃ 1.
  have hHg : (H * g).eqv 1 := HKConv.divPos_mul_eqv hgnum
  have hgH : (g * H).eqv 1 := Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv g H) hHg
  -- LHS: g·(1 + r·H) ≃ g·1 + g·(r·H) ≃ g + r·(g·H) ≃ g + r·1 ≃ g + r ≃ 1
  have hLHS : (g * (1 + r * H)).eqv 1 := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv g 1 (r * H)) ?_
    -- g·1 + g·(r·H)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (g * 1) g (g * (r * H)) (Q'.mul_one_eqv g)) ?_
    -- g + g·(r·H) ≃ g + r·(g·H)   (reassociate g·(r·H) = r·(g·H))
    have hreassoc : (g * (r * H)).eqv (r * (g * H)) := by
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv g r H)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (g * r) (r * g) H
        (Q'.mul_comm_eqv g r)) ?_
      exact Q'.mul_assoc_eqv r g H
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left g _ _ hreassoc) ?_
    -- g + r·(g·H) ≃ g + r·1 ≃ g + r
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left g _ _ (Q'.mul_eqv_congr_left r _ _ hgH)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left g _ _ (Q'.mul_one_eqv r)) ?_
    -- g + r = (1 + (-r)) + r ≃ 1
    show ((1 + (-r)) + r).eqv (1 : Q')
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv 1 (-r) r) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 _ 0 (Q'.neg_add_self_eqv r)) ?_
    exact Q'.add_zero' 1 ▸ Q'.eqv_refl 1
  -- g·(1 + r·H) ≃ 1 ≃ g·H, so ≤.
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) (Q'.ge_of_eqv hgH)

/-- The geometric series `Σ_{i<d} r^i ≤ H = divPos 1 (1+(−r))` for `0 < r < 1`. -/
theorem geom_series_le_base {r : Q'} (hr0 : (0 : Q') < r) (hr1 : r < (1 : Q')) (d : Nat) :
    finSum (fun i => r ^ i) d ≤ HKConv.divPos 1 (1 + (-r)) := by
  refine CharacterTail.geom_series_le (fun i => r ^ i) 1 r
    (HKConv.divPos 1 (1 + (-r))) (Q'.le_of_lt hr0)
    (HKConv.divPos_nonneg (Q'.le_of_lt (CReal.pos_of_num_pos (by decide))))
    ?_ ?_ (geom_recurrence hr0 hr1) d
  · -- f 0 = r^0 = 1 ≤ 1
    show r ^ 0 ≤ (1 : Q')
    exact Q'.le_refl' 1
  · -- f (k+1) = r^(k+1) ≤ r·r^k = r·f k
    intro k
    show r ^ (k + 1) ≤ r * r ^ k
    exact Q'.le_refl' _

/-- **The telescoped tail bound.**  The base-`r` increments from index `n`
onward sum under `geoTailBase C r n`:
`finSum (fun i => geoIncrBase C r (n+i)) d ≤ geoTailBase C r n`. -/
theorem geoTailBase_series_le {C r : Q'} (hC : (0 : Q') ≤ C)
    (hr0 : (0 : Q') < r) (hr1 : r < (1 : Q')) (n d : Nat) :
    finSum (fun i => geoIncrBase C r (n + i)) d ≤ geoTailBase C r n := by
  -- termwise: geoIncrBase C r (n+i) ≃ (C·r^n)·r^i
  have hterm : (finSum (fun i => geoIncrBase C r (n + i)) d).eqv
      (finSum (fun i => (C * r ^ n) * r ^ i) d) :=
    RationalTail.finSum_eqv_congr _ _ (fun i => by
      show (C * r ^ (n + i)).eqv ((C * r ^ n) * r ^ i)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left C (r ^ (n + i)) (r ^ n * r ^ i)
          (Q'.pow_add_eqv r n i)) ?_
      exact Q'.eqv_symm (Q'.mul_assoc_eqv C (r ^ n) (r ^ i))) d
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hterm) ?_
  -- finSum (fun i => (C·r^n)·r^i) d = (C·r^n)·finSum (r^·) d  (pull constant out)
  -- bound finSum (r^·) d ≤ H, then (C·r^n)·(Σ r^i) ≤ (C·r^n)·H = geoTailBase.
  have hKnn : (0 : Q') ≤ C * r ^ n := Q'.mul_nonneg _ _ hC (Q'.pow_nonneg r (Q'.le_of_lt hr0) n)
  -- finSum (fun i => K·r^i) d ≃ K · finSum (r^·) d
  have hpull : (finSum (fun i => (C * r ^ n) * r ^ i) d).eqv
      ((C * r ^ n) * finSum (fun i => r ^ i) d) :=
    Q'.eqv_symm (RationalTail.const_mul_finSum (fun i => r ^ i) (C * r ^ n) d)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hpull) ?_
  -- (C·r^n)·(Σ r^i) ≤ (C·r^n)·H = geoTailBase C r n
  exact Q'.mul_le_mul_of_nonneg_left _ _ (C * r ^ n) (geom_series_le_base hr0 hr1 d) hKnn

/-- **The base-`r` modulus `geoTailBase C r n → 0`.**  Since
`geoTailBase C r n = (C·H)·r^n` (up to reassociation), choose `n` past the
`pow_base_le` cutoff for `δ' = δ/(C·H+1)`.  We package it directly through
`pow_base_le` at the rescaled tolerance supplied as a hypothesis. -/
theorem geoTailBase_modulus {C r : Q'} (hC : (0 : Q') ≤ C)
    (hr0 : (0 : Q') < r) (hr1 : r < (1 : Q'))
    (ε : Q') (hε : (0 : Q') < ε)
    (δ : Q') (hδ : (0 : Q') < δ)
    (hscale : (C * HKConv.divPos 1 (1 + (-r))) * δ ≤ ε) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → geoTailBase C r n ≤ ε := by
  obtain ⟨N, hN⟩ := pow_base_le hr0 hr1 δ hδ
  refine ⟨N, fun n hn => ?_⟩
  -- geoTailBase C r n = (C·r^n)·H ≃ (C·H)·r^n ≤ (C·H)·δ ≤ ε
  have hrn : r ^ n ≤ δ := hN n hn
  let K := C * HKConv.divPos 1 (1 + (-r))
  have hKnn : (0 : Q') ≤ K :=
    Q'.mul_nonneg _ _ hC (HKConv.divPos_nonneg (Q'.le_of_lt (CReal.pos_of_num_pos (by decide))))
  -- geoTailBase C r n ≃ K · r^n
  have he : (geoTailBase C r n).eqv (K * r ^ n) := by
    show ((C * r ^ n) * HKConv.divPos 1 (1 + (-r))).eqv
        ((C * HKConv.divPos 1 (1 + (-r))) * r ^ n)
    -- (C·r^n)·H ≃ C·(r^n·H) ≃ C·(H·r^n) ≃ (C·H)·r^n
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv C (r ^ n) (HKConv.divPos 1 (1 + (-r)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left C _ _ (Q'.mul_comm_eqv (r ^ n) (HKConv.divPos 1 (1 + (-r))))) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv C (HKConv.divPos 1 (1 + (-r))) (r ^ n))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he) ?_
  -- K·r^n ≤ K·δ ≤ ε
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left (r ^ n) δ K hrn hKnn) hscale

/-- **Infinite-volume limit from a base-`r` geometric increment.**  The base-`r`
analog of `Continuum.crealOfGeoIncrement`: a `Q'` partial-sum sequence `S` with a
two-sided SINGLE-STEP increment bound `|S(l+1)−S(l)| ≤ C·r^l` (`0 < r < 1`)
defines a `CReal` whose `approx` is `S`. -/
def crealOfGeoIncrementBase (S : Nat → Q') (C r : Q') (hC : (0 : Q') ≤ C)
    (hr0 : (0 : Q') < r) (hr1 : r < (1 : Q'))
    (hup : ∀ l, S (l + 1) ≤ S l + geoIncrBase C r l)
    (hlo : ∀ l, S l ≤ S (l + 1) + geoIncrBase C r l)
    (modulus : ∀ ε : Q', (0 : Q') < ε →
      ∃ δ : Q', (0 : Q') < δ ∧ (C * HKConv.divPos 1 (1 + (-r))) * δ ≤ ε) :
    CReal :=
  crealOfTail S (geoTailBase C r)
    (fun n d => Q'.le_trans' _ _ _
      (telescope_up S (geoIncrBase C r) hup n d)
      (Q'.add_le_add_left (S n) _ (geoTailBase C r n) (geoTailBase_series_le hC hr0 hr1 n d)))
    (fun n d => Q'.le_trans' _ _ _
      (telescope_lo S (geoIncrBase C r) hlo n d)
      (Q'.add_le_add_left (S (n + d)) _ (geoTailBase C r n) (geoTailBase_series_le hC hr0 hr1 n d)))
    (fun ε hε => by
      obtain ⟨δ, hδ, hscale⟩ := modulus ε hε
      exact geoTailBase_modulus hC hr0 hr1 ε hε δ hδ hscale)

@[simp] theorem crealOfGeoIncrementBase_approx (S : Nat → Q') (C r : Q') (hC : (0 : Q') ≤ C)
    (hr0 : (0 : Q') < r) (hr1 : r < (1 : Q'))
    (hup : ∀ l, S (l + 1) ≤ S l + geoIncrBase C r l)
    (hlo : ∀ l, S l ≤ S (l + 1) + geoIncrBase C r l)
    (modulus : ∀ ε : Q', (0 : Q') < ε →
      ∃ δ : Q', (0 : Q') < δ ∧ (C * HKConv.divPos 1 (1 + (-r))) * δ ≤ ε)
    (k : Nat) :
    (crealOfGeoIncrementBase S C r hC hr0 hr1 hup hlo modulus).approx k = S k := rfl

/-! ## 4. `S` as a convergent `CReal` for ALL `a ∈ (0,1)` (the deliverable)

The per-term bound `sTerm a x l ≤ Cstar a · (a·a)^l` is EXACT (the `(a·a)^l`
factor comes from `HKConv.two_geoAmp_eqv` with equality), so no `a·a ≤ 1/2` is
needed: the decay base is `r = a·a < 1` itself.  We feed it to the general-base
engine `crealOfGeoIncrementBase`. -/

/-- **The exact per-term bound at base `r = a·a` (no smallness).**  For
`0 < a < 1`, `−1 ≤ x`, the `l`-th `S`-summand satisfies
`sTerm a x l ≤ geoIncrBase (Cstar a) (a·a) l = Cstar a · (a·a)^l`. -/
theorem sTerm_le_geoIncrBase {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (l : Nat) :
    HKConv.sTerm a x l ≤ geoIncrBase (HKConv.Cstar a) (a * a) l := by
  have hc0 : (0 : Q') ≤ HKPos.geoAmp a l :=
    Q'.le_of_lt ((HKPos.pow_succ_pos_lt_one ha0 ha1 (2 * l)).1)
  have hca : HKPos.geoAmp a l ≤ a := by
    show a ^ (2 * l + 1) ≤ a
    exact HKPos.pow_succ_le_self (Q'.le_of_lt ha0) (Q'.le_of_lt ha1) (2 * l)
  have hC0 : (0 : Q') ≤ HKConv.Cstar a := Q'.le_of_lt (CReal.pos_of_num_pos (HKConv.Cstar_num_pos ha0))
  have hCb : HKPos.two a ≤ HKConv.Cstar a * HKPos.factorLB a := HKConv.Cstar_bound ha1
  -- reduce divPos ≤ geoIncrBase to: two (geoAmp) ≤ geoIncrBase ... * factor (geoAmp) x
  refine HKConv.divPos_le_of_le (HKConv.factor_num_pos ha0 ha1 hx l) ?_
  show HKPos.two (HKPos.geoAmp a l)
      ≤ geoIncrBase (HKConv.Cstar a) (a * a) l * HKPos.factor (HKPos.geoAmp a l) x
  let G := geoIncrBase (HKConv.Cstar a) (a * a) l
  show HKPos.two (HKPos.geoAmp a l) ≤ G * HKPos.factor (HKPos.geoAmp a l) x
  have hGnn : (0 : Q') ≤ G := geoIncrBase_nonneg hC0
    (Q'.mul_nonneg a a (Q'.le_of_lt ha0) (Q'.le_of_lt ha0)) l
  -- Step A: G * factor ≥ G * factorLB a
  have hfactorLB_le_factor : HKPos.factorLB (HKPos.geoAmp a l)
      ≤ HKPos.factor (HKPos.geoAmp a l) x :=
    HKPos.factorLB_le_factor hc0 hx
  have hfactorLB_a_le : HKPos.factorLB a ≤ HKPos.factorLB (HKPos.geoAmp a l) :=
    HKConv.factorLB_antitone hc0 hca (Q'.le_of_lt ha1)
  have hLB_chain : HKPos.factorLB a ≤ HKPos.factor (HKPos.geoAmp a l) x :=
    Q'.le_trans' _ _ _ hfactorLB_a_le hfactorLB_le_factor
  have stepA : G * HKPos.factorLB a ≤ G * HKPos.factor (HKPos.geoAmp a l) x :=
    Q'.mul_le_mul_of_nonneg_left _ _ G hLB_chain hGnn
  -- Step B: two a * (a*a)^l ≤ G * factorLB a   (via two a ≤ Cstar a · factorLB a)
  have haa_nn : (0 : Q') ≤ (a * a) ^ l :=
    Q'.pow_nonneg (a * a) (Q'.mul_nonneg a a (Q'.le_of_lt ha0) (Q'.le_of_lt ha0)) l
  have stepB : HKPos.two a * (a * a) ^ l ≤ G * HKPos.factorLB a := by
    have h1 : HKPos.two a * (a * a) ^ l
        ≤ (HKConv.Cstar a * HKPos.factorLB a) * (a * a) ^ l :=
      Q'.mul_le_mul_of_nonneg_right _ _ ((a * a) ^ l) hCb haa_nn
    have e : ((HKConv.Cstar a * HKPos.factorLB a) * (a * a) ^ l).eqv
        (G * HKPos.factorLB a) := by
      show ((HKConv.Cstar a * HKPos.factorLB a) * (a * a) ^ l).eqv
          ((HKConv.Cstar a * (a * a) ^ l) * HKPos.factorLB a)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv (HKConv.Cstar a) (HKPos.factorLB a) ((a * a) ^ l)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (HKConv.Cstar a) _ _
          (Q'.mul_comm_eqv (HKPos.factorLB a) ((a * a) ^ l))) ?_
      exact Q'.eqv_symm (Q'.mul_assoc_eqv (HKConv.Cstar a) ((a * a) ^ l) (HKPos.factorLB a))
    exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv e)
  -- Step C: two (geoAmp a l) ≃ two a * (a*a)^l  (EXACT, no smallness)
  have stepC : HKPos.two (HKPos.geoAmp a l) ≤ HKPos.two a * (a * a) ^ l :=
    Q'.le_of_eqv (HKConv.two_geoAmp_eqv a l)
  exact Q'.le_trans' _ _ _ stepC (Q'.le_trans' _ _ _ stepB stepA)

/-- **THE DELIVERABLE: `S(x)` as a convergent `CReal` for ALL `a ∈ (0,1)`,
`−1 ≤ x`** — no `a·a ≤ 1/2` hypothesis.  `approx N = HKConv.Spart a x N`
(the genuine finite-volume partial sum); the Cauchy modulus is the base-`(a·a)`
modulus inherited from `crealOfGeoIncrementBase` at the canonical constant
`Cstar a = 2a/(1−a)²`. -/
def sConvCReal_general {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) : CReal :=
  crealOfGeoIncrementBase (HKConv.Spart a x) (HKConv.Cstar a) (a * a)
    (Q'.le_of_lt (CReal.pos_of_num_pos (HKConv.Cstar_num_pos ha0)))
    (HKPos.q_mul_pos ha0 ha0)
    (by
      -- a*a < 1:  a*a ≤ 1*a = a < 1
      have haa_le_a : a * a ≤ a := by
        refine Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right a 1 a (Q'.le_of_lt ha1) (Q'.le_of_lt ha0)) ?_
        exact Q'.le_of_eqv (Q'.one_mul_eqv a)
      exact HKPos.q_lt_of_le_of_lt haa_le_a ha1)
    -- hup
    (fun l => by
      rw [HKConv.Spart_succ]
      exact Q'.add_le_add_left (HKConv.Spart a x l) (HKConv.sTerm a x l)
        (geoIncrBase (HKConv.Cstar a) (a * a) l)
        (sTerm_le_geoIncrBase ha0 ha1 hx l))
    -- hlo
    (fun l => by
      rw [HKConv.Spart_succ]
      refine Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg (HKConv.Spart a x l) (HKConv.sTerm a x l)
          (HKConv.sTerm_nonneg ha0 ha1 hx l)) ?_
      exact Q'.add_le_self_of_nonneg (HKConv.Spart a x l + HKConv.sTerm a x l)
        (geoIncrBase (HKConv.Cstar a) (a * a) l)
        (geoIncrBase_nonneg (Q'.le_of_lt (CReal.pos_of_num_pos (HKConv.Cstar_num_pos ha0)))
          (Q'.le_of_lt (HKPos.q_mul_pos ha0 ha0)) l))
    -- modulus
    (fun ε hε => by
      have hKpos : 0 < (HKConv.Cstar a * HKConv.divPos 1 (1 + (-(a * a)))).num := by
        have hCpos : (0 : Q') < HKConv.Cstar a :=
          CReal.pos_of_num_pos (HKConv.Cstar_num_pos ha0)
        have hDpos : (0 : Q') < HKConv.divPos 1 (1 + (-(a * a))) :=
          HKConv.divPos_pos (by decide : (0 : Int) < (1 : Q').num)
        exact CReal.num_pos_of_pos (HKPos.q_mul_pos hCpos hDpos)
      refine ⟨HKConv.divPos ε (HKConv.Cstar a * HKConv.divPos 1 (1 + (-(a * a)))),
        HKConv.divPos_pos (CReal.num_pos_of_pos hε), ?_⟩
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv _ _) ?_
      exact HKConv.divPos_mul_eqv hKpos)

/-- `S`'s `N`-th approximation is exactly the finite-volume partial sum
`HKConv.Spart a x N`. -/
@[simp] theorem sConvCReal_general_approx {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (N : Nat) :
    (sConvCReal_general ha0 ha1 hx).approx N = HKConv.Spart a x N := rfl

/-- Every approximation of the general-`a` `S` `CReal` is `≥ 0`. -/
theorem sConvCReal_general_approx_nonneg {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (N : Nat) :
    (0 : Q') ≤ (sConvCReal_general ha0 ha1 hx).approx N := by
  rw [sConvCReal_general_approx]
  exact HKConv.Spart_nonneg ha0 ha1 hx N

/-- **The general-`a` `S` `CReal`'s limit is `≥ 0`** (`ExpPos.geRat … 0`), for ALL
`a ∈ (0,1)`, `−1 ≤ x`. -/
theorem sConvCReal_general_geRat_zero {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) :
    ExpPos.geRat (sConvCReal_general ha0 ha1 hx) 0 := by
  apply ExpPos.geRat_of_eventually
  exact ⟨0, fun N _ => sConvCReal_general_approx_nonneg ha0 ha1 hx N⟩

/-! ## 5. The end-to-end consumer: `R = Θ·S ≥ 0` for ALL `a ∈ (0,1)`

`HeatKernelPos2.mul_geRat_zero` needs both factors as nonneg-approx `CReal`s.  The
`S`-factor is now supplied genuinely for ALL `a ∈ (0,1)` (no `a·a ≤ 1/2`); the
`ϑ₃/2a` factor `Θ` is consumed as a parameter with its nonneg-approx hypothesis. -/

/-- **`R = Θ·S ≥ 0` for ALL `a ∈ (0,1)`, with `S` genuinely built.**  GIVEN any
`CReal` `Θ` realizing `ϑ₃/2a` with nonnegative approximations, the product
`Θ · S` (with `S = sConvCReal_general`) has limit `≥ 0`.  This is
`HKPos2.mul_geRat_zero` with the `S`-factor's nonneg-approx hypothesis discharged
by `sConvCReal_general_approx_nonneg`, now valid for the full range of `a`. -/
theorem R_geRat_zero_of_theta_general {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x)
    (Θ : CReal) (hΘ : ∀ n, (0 : Q') ≤ Θ.approx n) :
    ExpPos.geRat (CReal.mul Θ (sConvCReal_general ha0 ha1 hx)) 0 :=
  HKPos2.mul_geRat_zero hΘ (sConvCReal_general_approx_nonneg ha0 ha1 hx)

end YMGap.Continuum.HKConvGen

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only through reused `Nat`/`Int`/`omega`/`finSum`/`decide`
helpers).  No `Classical.*`, no `native_decide`, no `sorry`. -/

#print axioms YMGap.Continuum.HKConvGen.int_regroup
#print axioms YMGap.Continuum.HKConvGen.mul_le_mul_left_cancel
#print axioms YMGap.Continuum.HKConvGen.bScale_one_le
#print axioms YMGap.Continuum.HKConvGen.bScale_step
#print axioms YMGap.Continuum.HKConvGen.bernoulli_pow
#print axioms YMGap.Continuum.HKConvGen.ofNat_succ_eqv
#print axioms YMGap.Continuum.HKConvGen.ofNat_mul_le_bScale
#print axioms YMGap.Continuum.HKConvGen.pow_base_antitone
#print axioms YMGap.Continuum.HKConvGen.pow_base_le_cutoff
#print axioms YMGap.Continuum.HKConvGen.pow_base_le
#print axioms YMGap.Continuum.HKConvGen.geom_recurrence
#print axioms YMGap.Continuum.HKConvGen.geom_series_le_base
#print axioms YMGap.Continuum.HKConvGen.geoTailBase_series_le
#print axioms YMGap.Continuum.HKConvGen.geoTailBase_modulus
#print axioms YMGap.Continuum.HKConvGen.crealOfGeoIncrementBase
#print axioms YMGap.Continuum.HKConvGen.sTerm_le_geoIncrBase
#print axioms YMGap.Continuum.HKConvGen.sConvCReal_general
#print axioms YMGap.Continuum.HKConvGen.sConvCReal_general_approx_nonneg
#print axioms YMGap.Continuum.HKConvGen.sConvCReal_general_geRat_zero
#print axioms YMGap.Continuum.HKConvGen.R_geRat_zero_of_theta_general
