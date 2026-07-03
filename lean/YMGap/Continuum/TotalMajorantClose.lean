/-
# Inhabiting `TotalMajorant a` — the off-box Gaussian-beats-polynomial constant

`ThetaPtwiseTotalizerClose.TotalMajorant a` was left as the SOLE `Type`-level
obligation of Target A: a per-point positive rational `C y` with

    |chebTTerm a l y|  ≤  geoIncrBase (C y) a l  =  (C y)·aˡ    (∀ y : Q', ∀ l).

Feeding it to `thetaPtwiseData_of_totalMajorant` makes the two `F`-entangled
pointwise theta limits `ThetaPtwiseData a x (chebTConv …)` UNCONDITIONAL for every
`x`.  This module **inhabits it** (`totalMajorant`), off the box `[−1,1]` as well.

## The load-bearing correction

The parent module's comment cites the elementary bound `|T_m(y)| ≤ (2B_y)^m`.  That
is NOT recursion-clean: `T_{m+1} = 2y·T_m − T_{m−1}` gives
`|T_{m+1}| ≤ 2|y|·(2|y|)^m + (2|y|)^{m−1}`, which EXCEEDS `(2|y|)^{m+1}`.  The
all-`y`, recursion-clean bound is instead

    |T_m(y)|  ≤  (1 + 2·|y|)^m                                   (`abs_T_le_pow`),

which closes because `(1+2|y|)^{m−1} ≤ (1+2|y|)^m` (base `≥ 1`).  So the per-point
base is `B y := 1 + 2·|y|` (automatically `1 ≤ B y`, no `max(1,·)` guard).

## The chain

* `abs_T_le_pow`     — `|T_m(y)| ≤ (B y)^m`, two-step induction on `T_succ_succ`.
* `q_pow_mono`       — the missing `Q'` exponent-monotone `B^s ≤ B^t` for `1 ≤ B`.
* `mul_pow`/`pow_mul`— the two `Q'` power laws `(x·y)^n ≃ x^n·y^n`, `(x^m)^n ≃ x^{mn}`.
* `chebTTerm_abs_le` — `|chebTTerm a l y| ≤ a^{(l+1)²}·(B y)^{l+1}`.
* `core_bound`       — `(a^l·B y)^{l+1} ≤ (B y)^{N y}` (the per-point cutoff split:
                       the Gaussian `a^{(l+1)²}` crushing the exponential `(B y)^{l+1}`).
* `gaussBeatsExp`    — `a^{(l+1)²}·(B y)^{l+1} ≤ geoIncrBase (C y) a l`.
* `totalMajorant`    — inhabits `TotalMajorant a` with `C y = a·(B y)^{N y}`.
* `thetaPtwiseData`  — the assembled unconditional `ThetaPtwiseData`.

Here `N y := powBaseCutoff a (divPos 1 (B y))` is the crossover where `a^{t−1}·B y`
passes through `1`; the Gaussian exponent `(l+1)²` is used exactly once as
`a^{t²−t} = (a^{t−1})^t`.  No real analysis — `pow_base_le_cutoff` (Bernoulli +
Archimedean) supplies the crossover.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`.
-/

import YMGap.Continuum.ThetaPtwiseTotalizerClose
import YMGap.Continuum.ChebyshevBound
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.HeatKernelPos
import YMGap.Continuum.ThetaSeriesC1Close
import YMGap.Continuum.TsumDeriv

namespace YMGap.Continuum.TotalMajorantClose

open YMGap.Constructive
open YMGap.Continuum

local infix:50 " ≋ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

/-! ## 0. The per-point Chebyshev base `B y = 1 + 2·|y|` -/

/-- The per-point Chebyshev base `B y := 1 + 2·|y|` (automatically `1 ≤ B y`). -/
def Bpt (y : Q') : Q' := 1 + 2 * Q'.abs y

/-- `1 ≤ B y`. -/
theorem one_le_Bpt (y : Q') : (1 : Q') ≤ Bpt y :=
  Q'.add_le_self_of_nonneg 1 (2 * Q'.abs y)
    (Q'.mul_nonneg _ _ (Q'.le_of_lt (CReal.pos_of_num_pos (by decide))) (Q'.abs_nonneg y))

/-- `0 < B y`. -/
theorem Bpt_pos (y : Q') : (0 : Q') < Bpt y :=
  Q'.pos_of_lt_of_le (CReal.pos_of_num_pos (by decide)) (one_le_Bpt y)

/-- `0 ≤ B y`. -/
theorem Bpt_nonneg (y : Q') : (0 : Q') ≤ Bpt y :=
  Q'.le_trans' _ _ _ Q'.zero_le_one (one_le_Bpt y)

/-! ## 1. Elementary `Q'` power laws -/

/-- Exponent-monotone step `B^s ≤ B^{s+1}` for `1 ≤ B`. -/
theorem q_pow_le_succ {B : Q'} (hB : (1 : Q') ≤ B) (s : Nat) : B ^ s ≤ B ^ (s + 1) := by
  have hB0 : (0 : Q') ≤ B := Q'.le_trans' _ _ _ Q'.zero_le_one hB
  show B ^ s ≤ B * B ^ s
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv (B ^ s))) ?_
  exact Q'.mul_le_mul_of_nonneg_right 1 B (B ^ s) hB (Q'.pow_nonneg B hB0 s)

/-- `B^s ≤ B^{s+d}` for `1 ≤ B`. -/
theorem q_pow_add_le {B : Q'} (hB : (1 : Q') ≤ B) (s : Nat) : ∀ d, B ^ s ≤ B ^ (s + d)
  | 0 => Q'.le_refl' _
  | d + 1 => by
      have e : s + (d + 1) = (s + d) + 1 := by omega
      rw [e]
      exact Q'.le_trans' _ _ _ (q_pow_add_le hB s d) (q_pow_le_succ hB (s + d))

/-- **`Q'` exponent-monotonicity:** `1 ≤ B → s ≤ t → B^s ≤ B^t`.  (The dual of the
already-present exponent-antitone `HKConvGen.pow_base_antitone`.) -/
theorem q_pow_mono {B : Q'} (hB : (1 : Q') ≤ B) {s t : Nat} (h : s ≤ t) : B ^ s ≤ B ^ t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact q_pow_add_le hB s d

/-- `1 ≤ B^n` for `1 ≤ B`. -/
theorem one_le_qpow {B : Q'} (hB : (1 : Q') ≤ B) (n : Nat) : (1 : Q') ≤ B ^ n := by
  have h := q_pow_mono hB (Nat.zero_le n)
  rwa [Q'.pow_zero] at h

/-- Base-monotonicity of powers: `0 ≤ u → u ≤ v → u^n ≤ v^n`. -/
theorem pow_le_pow_base {u v : Q'} (hu : (0 : Q') ≤ u) (huv : u ≤ v) (n : Nat) :
    u ^ n ≤ v ^ n := by
  induction n with
  | zero => show (1 : Q') ≤ (1 : Q'); exact Q'.le_refl' 1
  | succ n ih =>
      show u * u ^ n ≤ v * v ^ n
      have hv : (0 : Q') ≤ v := Q'.le_trans' _ _ _ hu huv
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ huv (Q'.pow_nonneg _ hu n)) ?_
      exact Q'.mul_le_mul_of_nonneg_left _ _ _ ih hv

/-- Four-factor product swap `(x·y)·(u·v) ≃ (x·u)·(y·v)`. -/
theorem mul4_swap (x y u v : Q') : (x * y) * (u * v) ≋ (x * u) * (y * v) :=
  calc (x * y) * (u * v)
      ≋ x * (y * (u * v)) := Q'.mul_assoc_eqv x y (u * v)
    _ ≋ x * ((y * u) * v) := Q'.mul_eqv_congr_left x _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv y u v))
    _ ≋ x * ((u * y) * v) := Q'.mul_eqv_congr_left x _ _
                              (Q'.mul_eqv_congr_right _ _ v (Q'.mul_comm_eqv y u))
    _ ≋ x * (u * (y * v)) := Q'.mul_eqv_congr_left x _ _ (Q'.mul_assoc_eqv u y v)
    _ ≋ (x * u) * (y * v) := Q'.eqv_symm (Q'.mul_assoc_eqv x u (y * v))

/-- Power of a product `(x·y)^n ≃ x^n·y^n`. -/
theorem mul_pow (x y : Q') (n : Nat) : ((x * y) ^ n) ≋ (x ^ n * y ^ n) := by
  induction n with
  | zero =>
      show ((1 : Q')) ≋ ((1 : Q') * (1 : Q'))
      exact Q'.eqv_symm (Q'.mul_one_eqv 1)
  | succ n ih =>
      show ((x * y) * (x * y) ^ n) ≋ ((x * x ^ n) * (y * y ^ n))
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (x * y) _ _ ih) ?_
      exact mul4_swap x y (x ^ n) (y ^ n)

/-- Power of a power `(x^m)^n ≃ x^{m·n}`. -/
theorem pow_mul (x : Q') (m n : Nat) : ((x ^ m) ^ n) ≋ (x ^ (m * n)) := by
  induction n with
  | zero =>
      have e : m * 0 = 0 := Nat.mul_zero m
      rw [e]
      exact Q'.eqv_refl _
  | succ n ih =>
      have e : m * (n + 1) = m + m * n := by
        have e1 : m * (n + 1) = m * n + m := Nat.mul_succ m n
        omega
      rw [e]
      show ((x ^ m) * (x ^ m) ^ n) ≋ (x ^ (m + m * n))
      refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.pow_add_eqv x m (m * n)))
      exact Q'.mul_eqv_congr_left (x ^ m) _ _ ih

/-! ## 2. `abs_T_le_pow` — the recursion-clean Chebyshev-`T` bound `|T_m(y)| ≤ (B y)^m`

The parent module's `(2|y|)^m` is NOT inductively provable; `(1 + 2|y|)^m` is. -/

/-- The paired two-step invariant `|T_m| ≤ B^m ∧ |T_{m+1}| ≤ B^{m+1}`, proved by
induction on `m` via `Cheb.T_succ_succ`. -/
theorem abs_T_le_pow_pair (y : Q') :
    ∀ m, Q'.abs (Cheb.T m y) ≤ (Bpt y) ^ m
       ∧ Q'.abs (Cheb.T (m + 1) y) ≤ (Bpt y) ^ (m + 1) := by
  intro m
  induction m with
  | zero =>
      refine ⟨?_, ?_⟩
      · -- |T 0 y| = |1| ≤ 1 = B^0
        show Q'.abs (1 : Q') ≤ (1 : Q')
        exact Q'.le_of_eqv (TsumDeriv.Q'.abs_of_nonneg Q'.zero_le_one)
      · -- |T 1 y| = |y| ≤ B = B^1
        show Q'.abs y ≤ Bpt y * 1
        have hy_nn : (0 : Q') ≤ Q'.abs y := Q'.abs_nonneg y
        have h1y_nn : (0 : Q') ≤ 1 + Q'.abs y :=
          Q'.le_trans' _ _ _ Q'.zero_le_one (Q'.add_le_self_of_nonneg 1 (Q'.abs y) hy_nn)
        have goal1 : Q'.abs y ≤ 1 + (Q'.abs y + Q'.abs y) := by
          refine Q'.le_trans' _ _ _
            (Q'.add_le_self_of_nonneg (Q'.abs y) (1 + Q'.abs y) h1y_nn) ?_
          refine Q'.le_of_eqv ?_
          calc Q'.abs y + (1 + Q'.abs y)
              ≋ (Q'.abs y + 1) + Q'.abs y := Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
            _ ≋ (1 + Q'.abs y) + Q'.abs y := Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)
            _ ≋ 1 + (Q'.abs y + Q'.abs y) := Q'.add_assoc_eqv _ _ _
        refine Q'.le_trans' _ _ _ goal1 ?_
        refine Q'.le_of_eqv ?_
        calc (1 : Q') + (Q'.abs y + Q'.abs y)
            ≋ 1 + 2 * Q'.abs y :=
              Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Cheb.two_mul_eqv (Q'.abs y)))
          _ ≋ (1 + 2 * Q'.abs y) * 1 := Q'.eqv_symm (Q'.mul_one_eqv _)
          _ ≋ Bpt y * 1 := Q'.eqv_refl _
  | succ k ih =>
      refine ⟨ih.2, ?_⟩
      show Q'.abs (Cheb.T (k + 2) y) ≤ (Bpt y) ^ (k + 2)
      rw [Cheb.T_succ_succ]
      have hBnn : (0 : Q') ≤ Bpt y := Bpt_nonneg y
      -- step 1: triangle across the recurrence
      have hstep1 : Q'.abs (((2 : Q') * y) * Cheb.T (k + 1) y + (-(Cheb.T k y)))
          ≤ Q'.abs (((2 : Q') * y) * Cheb.T (k + 1) y) + Q'.abs (Cheb.T k y) := by
        refine Q'.le_trans' _ _ _ (TsumDeriv.abs_add_le _ _) ?_
        exact Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (Q'.abs_neg' (Cheb.T k y)))
      -- step 2: |2y·T_{k+1}| ≤ (2|y|)·B^{k+1}
      have hstep2 : Q'.abs (((2 : Q') * y) * Cheb.T (k + 1) y)
          ≤ (2 * Q'.abs y) * (Bpt y) ^ (k + 1) := by
        refine Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le _ _) ?_
        have habs2y : Q'.abs ((2 : Q') * y) ≤ 2 * Q'.abs y := by
          refine Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le (2 : Q') y) ?_
          exact Q'.mul_le_mul_of_nonneg_right _ _ _
            (Q'.le_of_eqv (TsumDeriv.Q'.abs_of_nonneg
              (Q'.le_of_lt (CReal.pos_of_num_pos (by decide)))))
            (Q'.abs_nonneg y)
        refine Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _ ih.2 (Q'.abs_nonneg _)) ?_
        exact Q'.mul_le_mul_of_nonneg_right _ _ _ habs2y (Q'.pow_nonneg _ hBnn (k + 1))
      -- combine: |T_{k+2}| ≤ (2|y|)·B^{k+1} + B^k
      have hstep3 : Q'.abs (((2 : Q') * y) * Cheb.T (k + 1) y + (-(Cheb.T k y)))
          ≤ (2 * Q'.abs y) * (Bpt y) ^ (k + 1) + (Bpt y) ^ k := by
        refine Q'.le_trans' _ _ _ hstep1 ?_
        refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hstep2) ?_
        exact Q'.add_le_add_left _ _ _ ih.1
      refine Q'.le_trans' _ _ _ hstep3 ?_
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add_left _ _ _ (q_pow_le_succ (one_le_Bpt y) k)) ?_
      refine Q'.le_of_eqv ?_
      -- (2|y|)·B^{k+1} + B^{k+1} ≋ (1+2|y|)·B^{k+1} = B^{k+2}
      calc (2 * Q'.abs y) * (Bpt y) ^ (k + 1) + (Bpt y) ^ (k + 1)
          ≋ (2 * Q'.abs y) * (Bpt y) ^ (k + 1) + 1 * (Bpt y) ^ (k + 1) :=
            Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _))
        _ ≋ (2 * Q'.abs y + 1) * (Bpt y) ^ (k + 1) := Q'.eqv_symm (Q'.add_mul_eqv _ _ _)
        _ ≋ (1 + 2 * Q'.abs y) * (Bpt y) ^ (k + 1) :=
            Q'.mul_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)
        _ ≋ (Bpt y) ^ (k + 2) := Q'.eqv_refl _

/-- **`abs_T_le_pow`** — the recursion-clean all-`y` Chebyshev-`T` bound
`|T_m(y)| ≤ (1 + 2·|y|)^m`. -/
theorem abs_T_le_pow (m : Nat) (y : Q') : Q'.abs (Cheb.T m y) ≤ (Bpt y) ^ m :=
  (abs_T_le_pow_pair y m).1

/-! ## 3. The termwise factor bound (`L2`) -/

/-- **`chebTTerm_abs_le`** — `|chebTTerm a l y| ≤ a^{(l+1)²}·(B y)^{l+1}`. -/
theorem chebTTerm_abs_le {a : Q'} (ha0 : (0 : Q') < a) (l : Nat) (y : Q') :
    Q'.abs (ThetaSeriesC1Close.chebTTerm a l y)
      ≤ a ^ ((l + 1) * (l + 1)) * (Bpt y) ^ (l + 1) := by
  show Q'.abs (a ^ ((l + 1) * (l + 1)) * Cheb.T (l + 1) y)
      ≤ a ^ ((l + 1) * (l + 1)) * (Bpt y) ^ (l + 1)
  have hpownn : (0 : Q') ≤ a ^ ((l + 1) * (l + 1)) := Q'.pow_nonneg a (Q'.le_of_lt ha0) _
  refine Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le _ _) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.le_of_eqv (TsumDeriv.Q'.abs_of_nonneg hpownn)) (Q'.abs_nonneg _)) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ (abs_T_le_pow (l + 1) y) hpownn

/-! ## 4. Per-point cutoff and constant -/

/-- The per-point cutoff `N y := powBaseCutoff a (1/(B y))` — the crossover of
`a^{t−1}·B y` through `1`. -/
def Ncut (a y : Q') : Nat := HKConvGen.powBaseCutoff a (HKConv.divPos 1 (Bpt y))

/-- The per-point geometric constant `C y := a·(B y)^{N y}`. -/
def Ccoef (a y : Q') : Q' := a * (Bpt y) ^ (Ncut a y)

/-- `0 < C y`. -/
theorem Ccoef_pos {a : Q'} (ha0 : (0 : Q') < a) (y : Q') : (0 : Q') < Ccoef a y :=
  HKPos.q_mul_pos ha0 (HKPos.pow_pos (Bpt_pos y) (Ncut a y))

/-! ## 5. `core_bound` — the per-point cutoff split (`gaussBeatsExp` heart) -/

/-- **`core_bound`** — `(a^l·B y)^{l+1} ≤ (B y)^{N y}`.  Case split on whether the
active window `l+1` sits below the crossover `N y` (`a^l ≤ 1` alone suffices) or
above it (each `a·B y` factor is `≤ 1` past the cutoff `pow_base_le_cutoff`). -/
theorem core_bound {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (l : Nat) (y : Q') :
    (a ^ l * Bpt y) ^ (l + 1) ≤ (Bpt y) ^ (Ncut a y) := by
  have hBnn : (0 : Q') ≤ Bpt y := Bpt_nonneg y
  have hab_nn : (0 : Q') ≤ a ^ l * Bpt y :=
    Q'.mul_nonneg _ _ (Q'.pow_nonneg a (Q'.le_of_lt ha0) l) hBnn
  rcases Nat.lt_or_ge (Ncut a y) (l + 1) with hlt | hge
  · -- above the crossover:  N y ≤ l
    have hNl : Ncut a y ≤ l := Nat.lt_succ_iff.mp hlt
    have hδ : (0 : Q') < HKConv.divPos 1 (Bpt y) :=
      HKConv.divPos_pos (by decide : (0 : Int) < (1 : Q').num)
    have hpow : a ^ l ≤ a ^ (Ncut a y) :=
      HKConvGen.pow_base_antitone (Q'.le_of_lt ha0) (Q'.le_of_lt ha1) hNl
    have hcut : a ^ (Ncut a y) ≤ HKConv.divPos 1 (Bpt y) :=
      HKConvGen.pow_base_le_cutoff ha0 ha1 hδ
    have hbase : a ^ l * Bpt y ≤ (1 : Q') :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right (a ^ l) (a ^ (Ncut a y)) (Bpt y) hpow hBnn)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right (a ^ (Ncut a y)) (HKConv.divPos 1 (Bpt y)) (Bpt y)
            hcut hBnn)
          (Q'.le_of_eqv (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (Bpt_pos y)))))
    have h1 : (a ^ l * Bpt y) ^ (l + 1) ≤ (1 : Q') :=
      HKPos.pow_le_one hab_nn hbase (l + 1)
    exact Q'.le_trans' _ _ _ h1 (one_le_qpow (one_le_Bpt y) (Ncut a y))
  · -- below the crossover:  l+1 ≤ N y
    have hal1 : a ^ l ≤ (1 : Q') := HKPos.pow_le_one (Q'.le_of_lt ha0) (Q'.le_of_lt ha1) l
    have hbase : a ^ l * Bpt y ≤ Bpt y :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right (a ^ l) (1 : Q') (Bpt y) hal1 hBnn)
        (Q'.le_of_eqv (Q'.one_mul_eqv (Bpt y)))
    have h1 : (a ^ l * Bpt y) ^ (l + 1) ≤ (Bpt y) ^ (l + 1) :=
      pow_le_pow_base hab_nn hbase (l + 1)
    exact Q'.le_trans' _ _ _ h1 (q_pow_mono (one_le_Bpt y) hge)

/-! ## 6. `gaussBeatsExp` — the per-point majorant bound -/

/-- **`gaussBeatsExp`** — `a^{(l+1)²}·(B y)^{l+1} ≤ geoIncrBase (C y) a l`.  The
Gaussian exponent `(l+1)²` splits (via `pow_add`) as `a^{(l+1)}·(a^l)^{l+1}`; the
`(a^l)^{l+1}·B^{l+1}` block is `(a^l·B)^{l+1}`, bounded by `core_bound`. -/
theorem gaussBeatsExp {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (l : Nat) (y : Q') :
    a ^ ((l + 1) * (l + 1)) * (Bpt y) ^ (l + 1)
      ≤ HKConvGen.geoIncrBase (Ccoef a y) a l := by
  have hexp : (l + 1) * (l + 1) = (l + 1) + l * (l + 1) := by
    have e1 : (l + 1) * (l + 1) = (l + 1) * l + (l + 1) := Nat.mul_succ (l + 1) l
    have e2 : (l + 1) * l = l * (l + 1) := Nat.mul_comm (l + 1) l
    omega
  rw [hexp]
  have hcore := core_bound ha0 ha1 l y
  have hLHS : (a ^ ((l + 1) + l * (l + 1)) * (Bpt y) ^ (l + 1))
      ≋ (a ^ (l + 1) * (a ^ l * Bpt y) ^ (l + 1)) := by
    calc a ^ ((l + 1) + l * (l + 1)) * (Bpt y) ^ (l + 1)
        ≋ (a ^ (l + 1) * a ^ (l * (l + 1))) * (Bpt y) ^ (l + 1) :=
          Q'.mul_eqv_congr_right _ _ _ (Q'.pow_add_eqv a (l + 1) (l * (l + 1)))
      _ ≋ a ^ (l + 1) * (a ^ (l * (l + 1)) * (Bpt y) ^ (l + 1)) :=
          Q'.mul_assoc_eqv _ _ _
      _ ≋ a ^ (l + 1) * ((a ^ l) ^ (l + 1) * (Bpt y) ^ (l + 1)) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (pow_mul a l (l + 1))))
      _ ≋ a ^ (l + 1) * (a ^ l * Bpt y) ^ (l + 1) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (mul_pow (a ^ l) (Bpt y) (l + 1)))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) ?_
  have ha1nn : (0 : Q') ≤ a ^ (l + 1) := Q'.pow_nonneg a (Q'.le_of_lt ha0) (l + 1)
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hcore ha1nn) ?_
  refine Q'.le_of_eqv ?_
  -- a^{l+1}·B^{N} ≋ (a·B^{N})·a^l = geoIncrBase (C y) a l
  calc a ^ (l + 1) * (Bpt y) ^ (Ncut a y)
      ≋ (a * a ^ l) * (Bpt y) ^ (Ncut a y) := Q'.eqv_refl _
    _ ≋ a * (a ^ l * (Bpt y) ^ (Ncut a y)) := Q'.mul_assoc_eqv a (a ^ l) _
    _ ≋ a * ((Bpt y) ^ (Ncut a y) * a ^ l) :=
        Q'.mul_eqv_congr_left a _ _ (Q'.mul_comm_eqv _ _)
    _ ≋ (a * (Bpt y) ^ (Ncut a y)) * a ^ l :=
        Q'.eqv_symm (Q'.mul_assoc_eqv a _ (a ^ l))
    _ ≋ HKConvGen.geoIncrBase (Ccoef a y) a l := Q'.eqv_refl _

/-! ## 7. Inhabiting `TotalMajorant a` and the assembled `ThetaPtwiseData` -/

/-- **`totalMajorant`** — the total per-point geometric majorant, valid for EVERY
`y : Q'` (off the box `[−1,1]` as well), with `C y = a·(B y)^{N y}`. -/
def totalMajorant {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) :
    ThetaPtwiseTotalizerClose.TotalMajorant a where
  C := fun y => Ccoef a y
  Cpos := fun y => Ccoef_pos ha0 y
  bound := fun y l =>
    Q'.le_trans' _ _ _ (chebTTerm_abs_le ha0 l y) (gaussBeatsExp ha0 ha1 l y)

/-- **THE ASSEMBLED UNCONDITIONAL `ThetaPtwiseData`.**  Feeding `totalMajorant`
into `thetaPtwiseData_of_totalMajorant` discharges both `F`-entangled pointwise
theta limits for every `x`, with the common limit `F := chebTConv …`. -/
def thetaPtwiseData {a x : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) :
    ThetaSeriesC1Close.ThetaPtwiseData a x
      (ThetaPtwiseTotalizerClose.chebTConv ha0 ha1 (totalMajorant ha0 ha1)) :=
  ThetaPtwiseTotalizerClose.thetaPtwiseData_of_totalMajorant ha0 ha1 (totalMajorant ha0 ha1)

end YMGap.Continuum.TotalMajorantClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TotalMajorantClose.q_pow_mono
#print axioms YMGap.Continuum.TotalMajorantClose.mul_pow
#print axioms YMGap.Continuum.TotalMajorantClose.pow_mul
#print axioms YMGap.Continuum.TotalMajorantClose.abs_T_le_pow
#print axioms YMGap.Continuum.TotalMajorantClose.chebTTerm_abs_le
#print axioms YMGap.Continuum.TotalMajorantClose.core_bound
#print axioms YMGap.Continuum.TotalMajorantClose.gaussBeatsExp
#print axioms YMGap.Continuum.TotalMajorantClose.totalMajorant
#print axioms YMGap.Continuum.TotalMajorantClose.thetaPtwiseData
