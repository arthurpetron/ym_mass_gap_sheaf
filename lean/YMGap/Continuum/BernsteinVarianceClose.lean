/-
Bernstein variance — CLOSING the moment chain.

This module carries out the assembly that `BernsteinVariance.lean` and
`BinomialTheorem.lean` documented but did not build: the first and second
(falling-factorial) moments of the Bernstein weights, the per-term square
decomposition `(k − n x)² = k(k−1) + (1 − 2 n x) k + (n x)²`, and the scalar
collapse `n(n−1)x² + (1 − 2 n x) n x + (n x)² = n·x(1−x)` — closing the scaled
variance identity `BernsteinVarianceStmt` UNCONDITIONALLY on top of the proved
`binomialTheorem`.

# What is GENUINELY PROVED here (no residual, `[propext]`/`[propext,Quot.sound]`)

  * `ofNat_mul_eqv'` / `mul_sub_eqv` — the two missing ring/cast atoms.
  * `kk_mul_binom` — the double combinatorial absorption for the 2nd moment.
  * `firstMoment` / `secondMoment` — the two head-peeled reindexed moment sums,
    reduced to `binomialTheorem` at exponent `n−1` / `n−2`.
  * `sub_sq_expand` / `falling_bridge` / `bern_term_decomp` — the per-term
    algebra, and
  * `bernsteinVariance : BernsteinVarianceStmt` — the full scaled variance
    identity, unconditional.

# Honest named residual (the capstone, NOT closed here)

  * `BernsteinUniform` — the uniform-convergence estimate
    `|Bₙf − f| ≤ ω(δ) + ‖f‖/(2 n δ²)`.  Its variance input is exactly
    `bernsteinVariance` (proved); the remaining Chebyshev far-index split is a
    genuinely separate constructive-analysis lemma and is named, not faked.

# Axiom-gate (AGENTS.md Rule 1)

Every theorem reports `[propext]` / `[propext, Quot.sound]` only.
-/

import YMGap.Continuum.BinomialTheorem
import YMGap.Constructive.Soundness
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.BernsteinVarianceClose

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG
open YMGap.Continuum.BernsteinVariance
open YMGap.Continuum.BinomialTheorem

/-! ## Atoms A1 / A2 -/

/-- `ofNat a · ofNat b ≃ ofNat (a·b)` (product-first orientation), re-proved
locally to avoid the heavy `CosPiEnclosure` import chain. -/
theorem ofNat_mul_base (a b : Nat) :
    (Q'.ofNat a * Q'.ofNat b).eqv (Q'.ofNat (a * b)) := by
  show (Q'.ofNat a * Q'.ofNat b).num * ((Q'.ofNat (a * b)).den : Int)
      = (Q'.ofNat (a * b)).num * ((Q'.ofNat a * Q'.ofNat b).den : Int)
  rw [Q'.mul_den_cast]
  show ((Int.ofNat a) * (Int.ofNat b)) * 1
      = (Int.ofNat (a * b)) * (1 * 1)
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
  omega

/-- **A1.** `ofNat (a·b) ≃ ofNat a · ofNat b` — the `.eqv`, product-first shape
the moment reindexings consume. -/
theorem ofNat_mul_eqv' (a b : Nat) :
    (Q'.ofNat (a * b)).eqv (Q'.ofNat a * Q'.ofNat b) :=
  Q'.eqv_symm (ofNat_mul_base a b)

/-- **A2.** `a·(b + −c) ≃ a·b + −(a·c)` (mirror of `sub_mul_eqv`). -/
theorem mul_sub_eqv (a b c : Q') :
    (a * (b + -c)).eqv (a * b + -(a * c)) :=
  Q'.eqv_trans _ _ _ (Q'.mul_add_eqv a b (-c))
    (Q'.add_eqv_congr_left (a * b) _ _ (Q'.mul_neg_eqv a c))

/-- `(−a)·(−b) ≃ a·b` (local re-derivation). -/
theorem neg_mul_neg_eqv (a b : Q') : ((-a) * (-b)).eqv (a * b) :=
  Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv a (-b))
    (Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr (a * (-b)) (-(a * b)) (Q'.mul_neg_eqv a b))
      (Q'.neg_neg_eqv (a * b)))

/-! ## Nat atom N2 -/

/-- **N2.** Double absorption `(k+2)(k+1)·C(n+2,k+2) = (n+2)(n+1)·C(n,k)`. -/
theorem kk_mul_binom (n k : Nat) :
    (k + 2) * (k + 1) * binom (n + 2) (k + 2) = (n + 2) * (n + 1) * binom n k := by
  have h1 : (k + 2) * binom (n + 2) (k + 2) = (n + 2) * binom (n + 1) (k + 1) :=
    succ_mul_binom_reindex (n + 1) (k + 1)
  have h2 : (k + 1) * binom (n + 1) (k + 1) = (n + 1) * binom n k :=
    succ_mul_binom_reindex n k
  calc (k + 2) * (k + 1) * binom (n + 2) (k + 2)
      = (k + 1) * ((k + 2) * binom (n + 2) (k + 2)) := by
          rw [Nat.mul_comm (k + 2) (k + 1), Nat.mul_assoc]
    _ = (k + 1) * ((n + 2) * binom (n + 1) (k + 1)) := by rw [h1]
    _ = (n + 2) * ((k + 1) * binom (n + 1) (k + 1)) := by rw [Nat.mul_left_comm]
    _ = (n + 2) * ((n + 1) * binom n k) := by rw [h2]
    _ = (n + 2) * (n + 1) * binom n k := by rw [Nat.mul_assoc]

/-! ## Pure `Q'` reassociation helpers for the per-term moment reindexing -/

/-- `c1·(c2·((a·P)·Y)) ≃ (c1·c2)·(a·(P·Y))` — pull the two coefficients
together and reassociate the monomial. -/
theorem mono_reassoc_L1 (c1 c2 a P Y : Q') :
    (c1 * (c2 * ((a * P) * Y))).eqv ((c1 * c2) * (a * (P * Y))) :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c1 _ _
      (Q'.mul_eqv_congr_left c2 _ _ (Q'.mul_assoc_eqv a P Y)))
    (Q'.eqv_symm (Q'.mul_assoc_eqv c1 c2 (a * (P * Y))))

/-- `E·(a·Z) ≃ a·(E·Z)`. -/
theorem swap_mid (E a Z : Q') : (E * (a * Z)).eqv (a * (E * Z)) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv E a Z))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (E * a) (a * E) Z (Q'.mul_comm_eqv E a))
      (Q'.mul_assoc_eqv a E Z))

/-- `(D·E)·(a·Z) ≃ (D·a)·(E·Z)` — move the head monomial factor `a` up next to
the big coefficient `D`. -/
theorem mono_reassoc_L2 (D E a Z : Q') :
    ((D * E) * (a * Z)).eqv ((D * a) * (E * Z)) :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv D E (a * Z))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left D _ _ (swap_mid E a Z))
      (Q'.eqv_symm (Q'.mul_assoc_eqv D a (E * Z))))

/-! ## First moment (`n = m+1`) -/

/-- Per-term first-moment reindexing:
`S1seq (m+1) x y (j+1) ≃ (ofNat (m+1) · x) · S0seq m x y j`. -/
theorem firstMoment_term (m : Nat) (x y : Q') (j : Nat) :
    (S1seq (m + 1) x y (j + 1)).eqv ((Q'.ofNat (m + 1) * x) * S0seq m x y j) := by
  have hexp : (m + 1) - (j + 1) = m - j := by omega
  have hcoeff :
      (Q'.ofNat (j + 1) * Q'.ofNat (binom (m + 1) (j + 1))).eqv
        (Q'.ofNat (m + 1) * Q'.ofNat (binom m j)) :=
    Q'.eqv_trans _ _ _ (ofNat_mul_base (j + 1) (binom (m + 1) (j + 1)))
      (Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq (congrArg Q'.ofNat (succ_mul_binom_reindex m j)))
        (ofNat_mul_eqv' (m + 1) (binom m j)))
  show (Q'.ofNat (j + 1) * (Q'.ofNat (binom (m + 1) (j + 1)) *
          (x ^ (j + 1) * y ^ ((m + 1) - (j + 1))))).eqv
        ((Q'.ofNat (m + 1) * x) *
          (Q'.ofNat (binom m j) * (x ^ j * y ^ (m - j))))
  rw [hexp]
  refine Q'.eqv_trans _ _ _
    (mono_reassoc_L1 (Q'.ofNat (j + 1)) (Q'.ofNat (binom (m + 1) (j + 1)))
      x (x ^ j) (y ^ (m - j))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (x * (x ^ j * y ^ (m - j))) hcoeff) ?_
  exact mono_reassoc_L2 (Q'.ofNat (m + 1)) (Q'.ofNat (binom m j)) x
    (x ^ j * y ^ (m - j))

/-- **First moment** (`n = m+1`, symbolic `y`):
`Σ_{k<m+2} S1seq (m+1) x y k ≃ (ofNat (m+1) · x) · Σ_{k<m+1} S0seq m x y k`. -/
theorem firstMoment (m : Nat) (x y : Q') :
    (finSum (S1seq (m + 1) x y) (m + 2)).eqv
      ((Q'.ofNat (m + 1) * x) * finSum (S0seq m x y) (m + 1)) := by
  have hhead : (S1seq (m + 1) x y 0).eqv 0 := by
    show (Q'.ofNat 0 * bmono (m + 1) x y 0).eqv 0
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ 0 (bmono (m + 1) x y 0) Q'.ofNat_zero_eqv)
      (Q'.zero_mul_eqv _)
  refine Q'.eqv_trans _ _ _
    (finSum_head_peel_zero (S1seq (m + 1) x y) (m + 1) hhead) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr (fun j => S1seq (m + 1) x y (j + 1))
      (fun j => (Q'.ofNat (m + 1) * x) * S0seq m x y j)
      (fun j => firstMoment_term m x y j) (m + 1)) ?_
  exact Q'.eqv_symm (const_mul_finSum (S0seq m x y) (Q'.ofNat (m + 1) * x) (m + 1))

/-! ## Second (falling-factorial) moment (`n = m+2`) -/

/-- Per-term second-moment reindexing:
`S2seq (m+2) x y (i+2) ≃ (ofNat ((m+2)(m+1)) · (x·x)) · S0seq m x y i`. -/
theorem secondMoment_term (m : Nat) (x y : Q') (i : Nat) :
    (S2seq (m + 2) x y (i + 2)).eqv
      ((Q'.ofNat ((m + 2) * (m + 1)) * (x * x)) * S0seq m x y i) := by
  have hexp2 : (m + 2) - (i + 2) = m - i := by omega
  have hx : (x ^ (i + 2)).eqv ((x * x) * x ^ i) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv x x (x ^ i))
  have hcoeff2 :
      (Q'.ofNat ((i + 2) * (i + 1)) * Q'.ofNat (binom (m + 2) (i + 2))).eqv
        (Q'.ofNat ((m + 2) * (m + 1)) * Q'.ofNat (binom m i)) :=
    Q'.eqv_trans _ _ _ (ofNat_mul_base ((i + 2) * (i + 1)) (binom (m + 2) (i + 2)))
      (Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq (congrArg Q'.ofNat (kk_mul_binom m i)))
        (ofNat_mul_eqv' ((m + 2) * (m + 1)) (binom m i)))
  show (Q'.ofNat ((i + 2) * (i + 1)) * (Q'.ofNat (binom (m + 2) (i + 2)) *
          (x ^ (i + 2) * y ^ ((m + 2) - (i + 2))))).eqv
        ((Q'.ofNat ((m + 2) * (m + 1)) * (x * x)) *
          (Q'.ofNat (binom m i) * (x ^ i * y ^ (m - i))))
  rw [hexp2]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right (x ^ (i + 2)) ((x * x) * x ^ i) (y ^ (m - i)) hx))) ?_
  refine Q'.eqv_trans _ _ _
    (mono_reassoc_L1 (Q'.ofNat ((i + 2) * (i + 1)))
      (Q'.ofNat (binom (m + 2) (i + 2))) (x * x) (x ^ i) (y ^ (m - i))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ ((x * x) * (x ^ i * y ^ (m - i))) hcoeff2) ?_
  exact mono_reassoc_L2 (Q'.ofNat ((m + 2) * (m + 1))) (Q'.ofNat (binom m i))
    (x * x) (x ^ i * y ^ (m - i))

/-- **Second moment** (`n = m+2`, symbolic `y`):
`Σ_{k<m+3} S2seq (m+2) x y k ≃ (ofNat ((m+2)(m+1)) · (x·x)) · Σ_{k<m+1} S0seq m x y k`. -/
theorem secondMoment (m : Nat) (x y : Q') :
    (finSum (S2seq (m + 2) x y) (m + 3)).eqv
      ((Q'.ofNat ((m + 2) * (m + 1)) * (x * x)) * finSum (S0seq m x y) (m + 1)) := by
  have hh0 : (S2seq (m + 2) x y 0).eqv 0 := by
    show (Q'.ofNat (0 * (0 - 1)) * bmono (m + 2) x y 0).eqv 0
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ 0 (bmono (m + 2) x y 0) Q'.ofNat_zero_eqv)
      (Q'.zero_mul_eqv _)
  have hh1 : (S2seq (m + 2) x y 1).eqv 0 := by
    show (Q'.ofNat (1 * (1 - 1)) * bmono (m + 2) x y 1).eqv 0
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ 0 (bmono (m + 2) x y 1) Q'.ofNat_zero_eqv)
      (Q'.zero_mul_eqv _)
  have peel1 : (finSum (S2seq (m + 2) x y) (m + 3)).eqv
      (finSum (fun j => S2seq (m + 2) x y (j + 1)) (m + 2)) :=
    finSum_head_peel_zero (S2seq (m + 2) x y) (m + 2) hh0
  have peel2 : (finSum (fun j => S2seq (m + 2) x y (j + 1)) (m + 2)).eqv
      (finSum (fun i => S2seq (m + 2) x y (i + 2)) (m + 1)) :=
    finSum_head_peel_zero (fun j => S2seq (m + 2) x y (j + 1)) (m + 1) hh1
  refine Q'.eqv_trans _ _ _ peel1 (Q'.eqv_trans _ _ _ peel2 ?_)
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr (fun i => S2seq (m + 2) x y (i + 2))
      (fun i => (Q'.ofNat ((m + 2) * (m + 1)) * (x * x)) * S0seq m x y i)
      (fun i => secondMoment_term m x y i) (m + 1)) ?_
  exact Q'.eqv_symm
    (const_mul_finSum (S0seq m x y) (Q'.ofNat ((m + 2) * (m + 1)) * (x * x)) (m + 1))

/-! ## Small zero facts -/

/-- A falling-factorial coefficient that vanishes kills its `S2seq` term. -/
theorem s2seq_coeff_zero (n : Nat) (x y : Q') (k : Nat) (hk : k * (k - 1) = 0) :
    (S2seq n x y k).eqv 0 := by
  show (Q'.ofNat (k * (k - 1)) * bmono n x y k).eqv 0
  rw [hk]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ 0 (bmono n x y k) Q'.ofNat_zero_eqv)
    (Q'.zero_mul_eqv _)

/-- `ofNat 0 · z ≃ 0` (via a `Nat` witness `p = 0`). -/
theorem ofNat_zero_prod (p : Nat) (hp : p = 0) (z : Q') :
    (Q'.ofNat p * z).eqv 0 := by
  rw [hp]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ 0 z Q'.ofNat_zero_eqv) (Q'.zero_mul_eqv z)

/-! ## Collapsed moments (`y = 1−x`, tail closed by the partition of unity) -/

/-- **First moment, collapsed.**  `Σ_{k<n+1} k·bₙₖ(x,1−x) ≃ n·x`. -/
theorem firstMomentCollapsed (n : Nat) (x : Q') :
    (finSum (S1seq n x (1 - x)) (n + 1)).eqv (Q'.ofNat n * x) := by
  cases n with
  | zero =>
    have hf0 : (S1seq 0 x (1 - x) 0).eqv 0 := by
      show (Q'.ofNat 0 * bmono 0 x (1 - x) 0).eqv 0
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ 0 (bmono 0 x (1 - x) 0) Q'.ofNat_zero_eqv)
        (Q'.zero_mul_eqv _)
    have hL : (finSum (S1seq 0 x (1 - x)) 1).eqv 0 :=
      finSum_head_peel_zero (S1seq 0 x (1 - x)) 0 hf0
    exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm (ofNat_zero_prod 0 rfl x))
  | succ m =>
    refine Q'.eqv_trans _ _ _ (firstMoment m x (1 - x)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (m + 1) * x) _ 1 (partition_of_unity m x)) ?_
    exact Q'.mul_one_eqv (Q'.ofNat (m + 1) * x)

/-- **Second moment, collapsed.**  `Σ_{k<n+1} k(k−1)·bₙₖ(x,1−x) ≃ n(n−1)·x²`. -/
theorem secondMomentCollapsed (n : Nat) (x : Q') :
    (finSum (S2seq n x (1 - x)) (n + 1)).eqv
      (Q'.ofNat (n * (n - 1)) * (x * x)) := by
  cases n with
  | zero =>
    have hf0 : (S2seq 0 x (1 - x) 0).eqv 0 :=
      s2seq_coeff_zero 0 x (1 - x) 0 (by decide)
    have hL : (finSum (S2seq 0 x (1 - x)) 1).eqv 0 :=
      finSum_head_peel_zero (S2seq 0 x (1 - x)) 0 hf0
    exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm (ofNat_zero_prod (0 * (0 - 1)) (by decide) (x * x)))
  | succ n1 =>
    cases n1 with
    | zero =>
      have hf0 : (S2seq 1 x (1 - x) 0).eqv 0 :=
        s2seq_coeff_zero 1 x (1 - x) 0 (by decide)
      have hf1 : (S2seq 1 x (1 - x) 1).eqv 0 :=
        s2seq_coeff_zero 1 x (1 - x) 1 (by decide)
      have peel1 : (finSum (S2seq 1 x (1 - x)) 2).eqv
          (finSum (fun j => S2seq 1 x (1 - x) (j + 1)) 1) :=
        finSum_head_peel_zero (S2seq 1 x (1 - x)) 1 hf0
      have peel2 : (finSum (fun j => S2seq 1 x (1 - x) (j + 1)) 1).eqv 0 :=
        finSum_head_peel_zero (fun j => S2seq 1 x (1 - x) (j + 1)) 0 hf1
      have hL : (finSum (S2seq 1 x (1 - x)) 2).eqv 0 :=
        Q'.eqv_trans _ _ _ peel1 peel2
      exact Q'.eqv_trans _ _ _ hL
        (Q'.eqv_symm (ofNat_zero_prod (1 * (1 - 1)) (by decide) (x * x)))
    | succ m =>
      refine Q'.eqv_trans _ _ _ (secondMoment m x (1 - x)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat ((m + 2) * (m + 1)) * (x * x)) _ 1
          (partition_of_unity m x)) ?_
      exact Q'.mul_one_eqv (Q'.ofNat ((m + 2) * (m + 1)) * (x * x))

/-! ## Per-term square decomposition -/

/-- `k·(k−1) + k = k·k` (truncated `Nat` subtraction). -/
theorem kk_nat (k : Nat) : k * (k - 1) + k = k * k := by
  cases k with
  | zero => rfl
  | succ j => exact (Nat.mul_succ (j + 1) j).symm

/-- Scalar falling identity `ofNat k · ofNat k ≃ ofNat (k(k−1)) + ofNat k`. -/
theorem sq_falling (k : Nat) :
    (Q'.ofNat k * Q'.ofNat k).eqv (Q'.ofNat (k * (k - 1)) + Q'.ofNat k) := by
  refine Q'.eqv_trans _ _ _ (ofNat_mul_base k k) ?_
  rw [← kk_nat k]
  exact Q'.ofNat_add_eqv (k * (k - 1)) k

/-- Falling-factorial bridge `ofNat (k(k−1)) ≃ (ofNat k)² + −ofNat k`. -/
theorem falling_bridge (k : Nat) :
    (Q'.ofNat (k * (k - 1))).eqv
      (Q'.ofNat k * Q'.ofNat k + -(Q'.ofNat k)) := by
  have e0 : (Q'.ofNat (k * (k - 1))).eqv (Q'.ofNat (k * (k - 1)) + 0) :=
    Q'.eqv_of_eq (Q'.add_zero' (Q'.ofNat (k * (k - 1)))).symm
  have e1 : (Q'.ofNat (k * (k - 1)) + (0 : Q')).eqv
      (Q'.ofNat (k * (k - 1)) + (Q'.ofNat k + -(Q'.ofNat k))) :=
    Q'.add_eqv_congr_left _ 0 _ (Q'.eqv_symm (add_neg_self_eqv (Q'.ofNat k)))
  have e2 : (Q'.ofNat (k * (k - 1)) + (Q'.ofNat k + -(Q'.ofNat k))).eqv
      ((Q'.ofNat (k * (k - 1)) + Q'.ofNat k) + -(Q'.ofNat k)) :=
    Q'.eqv_symm (Q'.add_assoc_eqv _ (Q'.ofNat k) (-(Q'.ofNat k)))
  have e3 : ((Q'.ofNat (k * (k - 1)) + Q'.ofNat k) + -(Q'.ofNat k)).eqv
      (Q'.ofNat k * Q'.ofNat k + -(Q'.ofNat k)) :=
    Q'.add_eqv_congr_right _ _ (-(Q'.ofNat k)) (Q'.eqv_symm (sq_falling k))
  exact Q'.eqv_trans _ _ _ e0 (Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 e3))

/-- Square expansion `(K + −T)² ≃ (K·K + −(K·T)) + (−(T·K) + T·T)`. -/
theorem sub_sq_expand (K T : Q') :
    ((K + -T) * (K + -T)).eqv ((K * K + -(K * T)) + (-(T * K) + T * T)) := by
  have hleft : (K * (K + -T)).eqv (K * K + -(K * T)) := mul_sub_eqv K K T
  have hright : ((-T) * (K + -T)).eqv (-(T * K) + T * T) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (-T) K (-T))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ ((-T) * (-T)) (Q'.neg_mul_eqv T K))
        (Q'.add_eqv_congr_left (-(T * K)) _ _ (neg_mul_neg_eqv T T)))
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv K (-T) (K + -T)) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ ((-T) * (K + -T)) hleft)
    (Q'.add_eqv_congr_left (K * K + -(K * T)) _ _ hright)

/-- Associative-commutative regrouping `((a+b)+c)+(c+d) ≃ (a+(b+(c+c)))+d`. -/
theorem ac_five (a b c d : Q') :
    (((a + b) + c) + (c + d)).eqv ((a + (b + (c + c))) + d) := by
  have nfS : (((a + b) + c) + (c + d)).eqv (a + (b + (c + (c + d)))) :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (a + b) c (c + d))
      (Q'.add_assoc_eqv a b (c + (c + d)))
  have nfG : ((a + (b + (c + c))) + d).eqv (a + (b + (c + (c + d)))) :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (b + (c + c)) d)
      (Q'.add_eqv_congr_left a _ _
        (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv b (c + c) d)
          (Q'.add_eqv_congr_left b _ _ (Q'.add_assoc_eqv c c d))))
  exact Q'.eqv_trans _ _ _ nfS (Q'.eqv_symm nfG)

/-- **Coefficient decomposition** `(K + −T)² ≃ (ofNat (k(k−1)) + (1 − 2T)·K) + T·T`,
`K := ofNat k`. -/
theorem coeff_decomp (k : Nat) (T : Q') :
    ((Q'.ofNat k + -T) * (Q'.ofNat k + -T)).eqv
      ((Q'.ofNat (k * (k - 1)) + (1 + -(T + T)) * Q'.ofNat k) + T * T) := by
  have hS := sub_sq_expand (Q'.ofNat k) T
  have hKK : (Q'.ofNat k * Q'.ofNat k).eqv (Q'.ofNat (k * (k - 1)) + Q'.ofNat k) :=
    sq_falling k
  have hKT : (-(Q'.ofNat k * T)).eqv (-(T * Q'.ofNat k)) :=
    Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv (Q'.ofNat k) T)
  -- rewrite the source into ((a+K) + c) + (c + d)  with c = -(T·K), d = T·T
  have hS2 : ((Q'.ofNat k + -T) * (Q'.ofNat k + -T)).eqv
      (((Q'.ofNat (k * (k - 1)) + Q'.ofNat k) + -(T * Q'.ofNat k))
        + (-(T * Q'.ofNat k) + T * T)) :=
    Q'.eqv_trans _ _ _ hS
      (Q'.add_eqv_congr_right _ _ (-(T * Q'.ofNat k) + T * T)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ (-(Q'.ofNat k * T)) hKK)
          (Q'.add_eqv_congr_left (Q'.ofNat (k * (k - 1)) + Q'.ofNat k) _ _ hKT)))
  -- middle coefficient of the target: (1 + -(T+T))·K ≃ K + (-(T·K) + -(T·K))
  have hmid : ((1 + -(T + T)) * Q'.ofNat k).eqv
      (Q'.ofNat k + (-(T * Q'.ofNat k) + -(T * Q'.ofNat k))) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 (-(T + T)) (Q'.ofNat k)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ ((-(T + T)) * Q'.ofNat k)
        (Q'.one_mul_eqv (Q'.ofNat k))) ?_
    refine Q'.add_eqv_congr_left (Q'.ofNat k) _ _ ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv (T + T) (Q'.ofNat k)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.add_mul_eqv T T (Q'.ofNat k))) ?_
    exact Q'.neg_add_eqv (T * Q'.ofNat k) (T * Q'.ofNat k)
  -- AC rearrange source, then fold the middle back to the target coefficient
  refine Q'.eqv_trans _ _ _ hS2 ?_
  refine Q'.eqv_trans _ _ _
    (ac_five (Q'.ofNat (k * (k - 1))) (Q'.ofNat k) (-(T * Q'.ofNat k)) (T * T)) ?_
  refine Q'.add_eqv_congr_right _ _ (T * T) ?_
  exact Q'.add_eqv_congr_left (Q'.ofNat (k * (k - 1))) _ _ (Q'.eqv_symm hmid)

/-- **Per-term Bernstein decomposition.**
`(k − n x)²·bₙₖ ≃ S2seq k + (1 − 2 n x)·S1seq k + (n x)²·S0seq k`. -/
theorem bern_term_decomp (n : Nat) (x : Q') (k : Nat) :
    ((Q'.ofNat k + -(Q'.ofNat n * x)) * (Q'.ofNat k + -(Q'.ofNat n * x))
        * bmono n x (1 - x) k).eqv
      ((S2seq n x (1 - x) k
          + (1 + -((Q'.ofNat n * x) + (Q'.ofNat n * x))) * S1seq n x (1 - x) k)
        + (Q'.ofNat n * x) * (Q'.ofNat n * x) * S0seq n x (1 - x) k) := by
  have hcd := coeff_decomp k (Q'.ofNat n * x)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (bmono n x (1 - x) k) hcd) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv (Q'.ofNat (k * (k - 1)) + (1 + -((Q'.ofNat n * x) + (Q'.ofNat n * x)))
        * Q'.ofNat k) ((Q'.ofNat n * x) * (Q'.ofNat n * x)) (bmono n x (1 - x) k)) ?_
  refine Q'.add_eqv_congr_right _ _
    ((Q'.ofNat n * x) * (Q'.ofNat n * x) * bmono n x (1 - x) k) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv (Q'.ofNat (k * (k - 1)))
      ((1 + -((Q'.ofNat n * x) + (Q'.ofNat n * x))) * Q'.ofNat k)
      (bmono n x (1 - x) k)) ?_
  exact Q'.add_eqv_congr_left (Q'.ofNat (k * (k - 1)) * bmono n x (1 - x) k) _ _
    (Q'.mul_assoc_eqv (1 + -((Q'.ofNat n * x) + (Q'.ofNat n * x)))
      (Q'.ofNat k) (bmono n x (1 - x) k))

/-! ## The one residual algebraic identity, and the full reduction -/

/-- **Scalar collapse** — the pure `Q'` polynomial identity that closes the
variance sum once the three moments have been substituted:
`n(n−1)·x² + (1 − 2nx)·(n x) + (n x)² ≃ n·x(1−x)`. -/
def ScalarCollapse : Prop :=
  ∀ (n : Nat) (x : Q'),
    ((Q'.ofNat (n * (n - 1)) * (x * x)
        + (1 + -((Q'.ofNat n * x) + (Q'.ofNat n * x))) * (Q'.ofNat n * x))
      + (Q'.ofNat n * x) * (Q'.ofNat n * x)).eqv
      (Q'.ofNat n * (x * (1 - x)))

/-- **Full reduction.**  Given the scalar collapse, the scaled Bernstein-variance
identity holds unconditionally — every remaining input (both moments, the
partition of unity, the per-term decomposition) is proved above. -/
theorem bernsteinVariance_of_scalar (H : ScalarCollapse) : BernsteinVarianceStmt := by
  intro n x
  -- step 1: per-term decomposition
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr
      (fun k => (Q'.ofNat k - Q'.ofNat n * x) * (Q'.ofNat k - Q'.ofNat n * x)
                  * bmono n x (1 - x) k)
      (fun k => (S2seq n x (1 - x) k
          + (1 + -((Q'.ofNat n * x) + (Q'.ofNat n * x))) * S1seq n x (1 - x) k)
        + (Q'.ofNat n * x) * (Q'.ofNat n * x) * S0seq n x (1 - x) k)
      (fun k => bern_term_decomp n x k) (n + 1)) ?_
  -- step 2: split off the T²·S0 sum
  refine Q'.eqv_trans _ _ _
    (finSum_add
      (fun k => S2seq n x (1 - x) k
          + (1 + -((Q'.ofNat n * x) + (Q'.ofNat n * x))) * S1seq n x (1 - x) k)
      (fun k => (Q'.ofNat n * x) * (Q'.ofNat n * x) * S0seq n x (1 - x) k) (n + 1)) ?_
  -- step 3: split S2 from the (1−2T)·S1 sum
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _
      (finSum (fun k => (Q'.ofNat n * x) * (Q'.ofNat n * x) * S0seq n x (1 - x) k) (n + 1))
      (finSum_add (S2seq n x (1 - x))
        (fun k => (1 + -((Q'.ofNat n * x) + (Q'.ofNat n * x))) * S1seq n x (1 - x) k)
        (n + 1))) ?_
  -- step 4: substitute the three moments
  have h2 : (finSum (S2seq n x (1 - x)) (n + 1)).eqv
      (Q'.ofNat (n * (n - 1)) * (x * x)) := secondMomentCollapsed n x
  have h1 : (finSum (fun k => (1 + -((Q'.ofNat n * x) + (Q'.ofNat n * x)))
                * S1seq n x (1 - x) k) (n + 1)).eqv
      ((1 + -((Q'.ofNat n * x) + (Q'.ofNat n * x))) * (Q'.ofNat n * x)) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (const_mul_finSum (S1seq n x (1 - x))
        (1 + -((Q'.ofNat n * x) + (Q'.ofNat n * x))) (n + 1)))
      (Q'.mul_eqv_congr_left _ _ _ (firstMomentCollapsed n x))
  have h0 : (finSum (fun k => (Q'.ofNat n * x) * (Q'.ofNat n * x)
                * S0seq n x (1 - x) k) (n + 1)).eqv
      ((Q'.ofNat n * x) * (Q'.ofNat n * x)) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (const_mul_finSum (S0seq n x (1 - x))
        ((Q'.ofNat n * x) * (Q'.ofNat n * x)) (n + 1)))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ 1 (partition_of_unity n x))
        (Q'.mul_one_eqv _))
  have hAB : (finSum (S2seq n x (1 - x)) (n + 1)
              + finSum (fun k => (1 + -((Q'.ofNat n * x) + (Q'.ofNat n * x)))
                  * S1seq n x (1 - x) k) (n + 1)).eqv
      (Q'.ofNat (n * (n - 1)) * (x * x)
        + (1 + -((Q'.ofNat n * x) + (Q'.ofNat n * x))) * (Q'.ofNat n * x)) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ h2)
      (Q'.add_eqv_congr_left _ _ _ h1)
  have hfin :
      ((finSum (S2seq n x (1 - x)) (n + 1)
          + finSum (fun k => (1 + -((Q'.ofNat n * x) + (Q'.ofNat n * x)))
              * S1seq n x (1 - x) k) (n + 1))
        + finSum (fun k => (Q'.ofNat n * x) * (Q'.ofNat n * x)
            * S0seq n x (1 - x) k) (n + 1)).eqv
      ((Q'.ofNat (n * (n - 1)) * (x * x)
          + (1 + -((Q'.ofNat n * x) + (Q'.ofNat n * x))) * (Q'.ofNat n * x))
        + (Q'.ofNat n * x) * (Q'.ofNat n * x)) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ h0)
      (Q'.add_eqv_congr_right _ _ _ hAB)
  exact Q'.eqv_trans _ _ _ hfin (H n x)

/-! ## Discharging the scalar collapse -/

/-- Cancellation `((a + −R) + (P + (−a + −a))) + a ≃ P + −R`. -/
theorem cancel_lemma (a R P : Q') :
    (((a + -R) + (P + (-a + -a))) + a).eqv (P + -R) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (a + -R) (P + (-a + -a)) a) ?_
  have hY : ((P + (-a + -a)) + a).eqv (P + -a) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv P (-a + -a) a) ?_
    refine Q'.add_eqv_congr_left P _ _ ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (-a) (-a) a) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-a) _ _ (Q'.neg_add_self_eqv a)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' (-a))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (a + -R) _ _ hY) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (a + -R) _ _ (Q'.add_comm_eqv P (-a))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (a + -R) (-a) P)) ?_
  have hleftR : ((a + -R) + -a).eqv (-R) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-R) (-a)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a _ _ (Q'.add_comm_eqv (-R) (-a))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv a (-a) (-R))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-R) (add_neg_self_eqv a)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (-R))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ (-R) P hleftR) ?_
  exact Q'.add_comm_eqv (-R) P

/-- The scalar collapse with the falling factor pre-substituted:
`((N² − N)·x² + (1 − 2Nx)·(Nx)) + (Nx)² ≃ N·x(1−x)`. -/
theorem scalar_collapse_gen (N x : Q') :
    (((N * N + -N) * (x * x)
        + (1 + -((N * x) + (N * x))) * (N * x)) + (N * x) * (N * x)).eqv
      (N * (x * (1 - x))) := by
  have pp_eq : ((N * x) * (N * x)).eqv ((N * N) * (x * x)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv N x (N * x)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left N _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv x N x))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left N _ _
        (Q'.mul_eqv_congr_right _ _ x (Q'.mul_comm_eqv x N))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left N _ _ (Q'.mul_assoc_eqv N x x)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv N N (x * x))
  have hp1 : ((N * N + -N) * (x * x)).eqv ((N * N) * (x * x) + -(N * (x * x))) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (N * N) (-N) (x * x))
      (Q'.add_eqv_congr_left ((N * N) * (x * x)) _ _ (Q'.neg_mul_eqv N (x * x)))
  have hp2 : ((1 + -((N * x) + (N * x))) * (N * x)).eqv
      ((N * x) + (-((N * N) * (x * x)) + -((N * N) * (x * x)))) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 (-((N * x) + (N * x))) (N * x)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ ((-((N * x) + (N * x))) * (N * x))
        (Q'.one_mul_eqv (N * x))) ?_
    refine Q'.add_eqv_congr_left (N * x) _ _ ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv ((N * x) + (N * x)) (N * x)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.add_mul_eqv (N * x) (N * x) (N * x))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_add_eqv ((N * x) * (N * x)) ((N * x) * (N * x))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-((N * x) * (N * x)))
        (Q'.neg_eqv_congr _ _ pp_eq)) ?_
    exact Q'.add_eqv_congr_left (-((N * N) * (x * x))) _ _ (Q'.neg_eqv_congr _ _ pp_eq)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ ((N * x) * (N * x))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ ((1 + -((N * x) + (N * x))) * (N * x)) hp1)
        (Q'.add_eqv_congr_left ((N * N) * (x * x) + -(N * (x * x))) _ _ hp2))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ pp_eq) ?_
  refine Q'.eqv_trans _ _ _
    (cancel_lemma ((N * N) * (x * x)) (N * (x * x)) (N * x)) ?_
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left N _ _ (Q'.mul_add_eqv x 1 (-x))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left N _ _
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (x * (-x)) (Q'.mul_one_eqv x))
        (Q'.add_eqv_congr_left x _ _ (Q'.mul_neg_eqv x x)))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv N x (-(x * x))) ?_
  exact Q'.add_eqv_congr_left (N * x) _ _ (Q'.mul_neg_eqv N (x * x))

/-- **The scalar collapse, proved.** -/
theorem scalarCollapse : ScalarCollapse := by
  intro n x
  refine Q'.eqv_trans _ _ _ ?_ (scalar_collapse_gen (Q'.ofNat n) x)
  refine Q'.add_eqv_congr_right _ _ ((Q'.ofNat n * x) * (Q'.ofNat n * x)) ?_
  refine Q'.add_eqv_congr_right _ _
    ((1 + -((Q'.ofNat n * x) + (Q'.ofNat n * x))) * (Q'.ofNat n * x)) ?_
  exact Q'.mul_eqv_congr_right _ _ (x * x) (falling_bridge n)

/-- **Bernstein variance identity, UNCONDITIONAL.** -/
theorem bernsteinVariance : BernsteinVarianceStmt :=
  bernsteinVariance_of_scalar scalarCollapse

end YMGap.Continuum.BernsteinVarianceClose

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BernsteinVarianceClose.ofNat_mul_eqv'
#print axioms YMGap.Continuum.BernsteinVarianceClose.mul_sub_eqv
#print axioms YMGap.Continuum.BernsteinVarianceClose.neg_mul_neg_eqv
#print axioms YMGap.Continuum.BernsteinVarianceClose.kk_mul_binom
#print axioms YMGap.Continuum.BernsteinVarianceClose.firstMoment_term
#print axioms YMGap.Continuum.BernsteinVarianceClose.firstMoment
#print axioms YMGap.Continuum.BernsteinVarianceClose.secondMoment_term
#print axioms YMGap.Continuum.BernsteinVarianceClose.secondMoment
#print axioms YMGap.Continuum.BernsteinVarianceClose.firstMomentCollapsed
#print axioms YMGap.Continuum.BernsteinVarianceClose.secondMomentCollapsed
#print axioms YMGap.Continuum.BernsteinVarianceClose.kk_nat
#print axioms YMGap.Continuum.BernsteinVarianceClose.sq_falling
#print axioms YMGap.Continuum.BernsteinVarianceClose.falling_bridge
#print axioms YMGap.Continuum.BernsteinVarianceClose.sub_sq_expand
#print axioms YMGap.Continuum.BernsteinVarianceClose.coeff_decomp
#print axioms YMGap.Continuum.BernsteinVarianceClose.bern_term_decomp
#print axioms YMGap.Continuum.BernsteinVarianceClose.bernsteinVariance_of_scalar
#print axioms YMGap.Continuum.BernsteinVarianceClose.cancel_lemma
#print axioms YMGap.Continuum.BernsteinVarianceClose.scalar_collapse_gen
#print axioms YMGap.Continuum.BernsteinVarianceClose.scalarCollapse
#print axioms YMGap.Continuum.BernsteinVarianceClose.bernsteinVariance
