/-
# W = 1 model with the vacuum coupling and the full spin tail: an infinite
# tridiagonal row-sum (Schur) test on finitely supported sequences, plus the dense
# n×n row-sum test

ADDITIVE.  **MODEL, not the true slab.**  It completes `W1StrongCouplingPerturbation`.

Type used for the infinite-dimensional part: sequences `x : Nat → Q'`, summed over
`i < n` for an ARBITRARY cutoff `n`.  Every finitely supported vector is covered, and these
are dense in ℓ²; no completion is formalized.

Model (spin index `s = 2j`, all `s ≥ 0` including the vacuum `s = 0`):
* `e s = w^{4 c4(s)}`, so `e 0 = 1`;
* coupling `c s = κ w^{2c4(s) + 2c4(s+1)}` between `s` and `s+1`, so the vacuum coupling is
  `c 0 = κ w⁶`;
* `T` is the infinite symmetric tridiagonal matrix `(e, c)`.

* `triForm e c x n = Σ_{i<n} e_i x_i² + 2 Σ_{i+1<n} c_i x_i x_{i+1}` (quadratic form of `T`).
* `triForm_le` (PROVED, plumbing): if `c ≥ 0` and every row sum
  `e_i + c_{i-1} + c_i ≤ ρ`, then `triForm ≤ ρ Σ x_i²` for every `n` and `x`.
* `excitedForm_bound` (PROVED): on `χ₀⊥` (the excited sequence `y_i = x_{i+1}`, which is
  exactly where `x₀ = 0`, so `c 0` drops out of the form),
  `⟨x,Tx⟩ ≤ ρ‖x‖²` with `ρ = w^{12} + κ w^{22}`, for ALL spins (tail included), given
  `w^{32} + κ w^{22} ≤ w^{12}` and `κ w^{22} ≥ 0`.
* `vacuum_rayleigh`: `⟨χ₀,Tχ₀⟩ = 1`.
* Certified (κ = 1/4): `excited_bound_1024`, `excited_bound_half`.
* Consequence (cited, NOT formalized: Courant–Fischer min-max for each finite section
  `T_N`): `λ₁(T_N) ≥ 1` and `λ₂(T_N) ≤ ρ`.  Hence the TRUE excited eigenvalue of the
  vacuum-included operator is at most `w^{12} + κ w^{22}`, uniformly in the truncation,
  even though the top eigenvector is not exactly `χ₀` (`c 0 ≠ 0`).
* `schurN` (PROVED, plumbing): the dense `n×n` symmetric nonnegative row-sum form test
  `Σ_{i,j<n} a_ij x_i x_j ≤ ρ Σ x_i²`.

U(1)-blind: all theorems except the `c4` exponents.  Axioms: `propext`, `Quot.sound`.
-/

import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.Geometric
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.ExpNeg

namespace YMGap.Continuum.W1VacuumTailRowSum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Constructive.SumOfSquares (q_mul_self_nonneg)

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

/-- lower coupling `c_{i-1}` (zero at `i = 0`). -/
def cl (c : Nat → Q') : Nat → Q'
  | 0 => 0
  | k + 1 => c k

/-- previous coordinate `x_{i-1}` (zero at `i = 0`). -/
def xm (x : Nat → Q') : Nat → Q'
  | 0 => 0
  | k + 1 => x k

def triForm (e c x : Nat → Q') : Nat → Q'
  | 0 => 0
  | n + 1 => triForm e c x n + e n * (x n * x n) +
      (cl c n * (xm x n * x n) + cl c n * (xm x n * x n))

def triRow (e c x : Nat → Q') : Nat → Q'
  | 0 => 0
  | n + 1 => triRow e c x n + (e n + cl c n + c n) * (x n * x n)

/-- `2 c a b ≤ c a² + c b²` for `c ≥ 0`. -/
theorem amgm (c a b : Q') (hc : (0 : Q') ≤ c) :
    c * (a * b) + c * (a * b) ≤ c * (a * a) + c * (b * b) := by
  let V := PolyExpr.var
  have hid : (c * (a * a) + c * (b * b)).eqv
      ((c * (a * b) + c * (a * b)) + c * ((a + -b) * (a + -b))) :=
    poly_identity_of_normal_eq
      (V 0 * (V 1 * V 1) + V 0 * (V 2 * V 2))
      ((V 0 * (V 1 * V 2) + V 0 * (V 1 * V 2)) + V 0 * ((V 1 + -V 2) * (V 1 + -V 2)))
      (by decide) (fun | 0 => c | 1 => a | _ => b)
  have h := Q'.add_le_add (Q'.le_refl' (c * (a * b) + c * (a * b)))
    (Q'.mul_nonneg _ _ hc (q_mul_self_nonneg (a + -b)))
  rw [Q'.add_zero'] at h
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_symm hid))

theorem triForm_key (e c x : Nat → Q') (hc : ∀ i, (0 : Q') ≤ c i) :
    ∀ n, triForm e c x (n + 1) + c n * (x n * x n) ≤ triRow e c x (n + 1)
  | 0 => by
      show (0 : Q') + e 0 * (x 0 * x 0) + ((0 : Q') * ((0 : Q') * x 0) + (0 : Q') * ((0 : Q') * x 0))
          + c 0 * (x 0 * x 0) ≤ (0 : Q') + (e 0 + 0 + c 0) * (x 0 * x 0)
      let V := PolyExpr.var
      let Z := PolyExpr.const 0
      exact Q'.le_of_eqv (poly_identity_of_normal_eq
        (Z + V 0 * (V 2 * V 2) + (Z * (Z * V 2) + Z * (Z * V 2)) + V 1 * (V 2 * V 2))
        (Z + (V 0 + Z + V 1) * (V 2 * V 2))
        (by decide) (fun | 0 => e 0 | 1 => c 0 | 2 => x 0 | _ => 0))
  | n + 1 => by
      have ih := triForm_key e c x hc n
      show triForm e c x (n + 1) + e (n + 1) * (x (n + 1) * x (n + 1)) +
          (c n * (x n * x (n + 1)) + c n * (x n * x (n + 1))) +
          c (n + 1) * (x (n + 1) * x (n + 1)) ≤
        triRow e c x (n + 1) + (e (n + 1) + c n + c (n + 1)) * (x (n + 1) * x (n + 1))
      have hm := amgm (c n) (x n) (x (n + 1)) (hc n)
      have step1 := Q'.add_le_add (Q'.add_le_add (Q'.le_refl' (triForm e c x (n + 1) +
          e (n + 1) * (x (n + 1) * x (n + 1)))) hm)
        (Q'.le_refl' (c (n + 1) * (x (n + 1) * x (n + 1))))
      refine Q'.le_trans' _ _ _ step1 ?_
      let V := PolyExpr.var
      have hid : (triForm e c x (n + 1) + e (n + 1) * (x (n + 1) * x (n + 1)) +
          (c n * (x n * x n) + c n * (x (n + 1) * x (n + 1))) +
          c (n + 1) * (x (n + 1) * x (n + 1))).eqv
          ((triForm e c x (n + 1) + c n * (x n * x n)) +
            (e (n + 1) + c n + c (n + 1)) * (x (n + 1) * x (n + 1))) :=
        poly_identity_of_normal_eq
          (V 0 + V 1 * (V 5 * V 5) + (V 2 * (V 4 * V 4) + V 2 * (V 5 * V 5)) + V 3 * (V 5 * V 5))
          ((V 0 + V 2 * (V 4 * V 4)) + (V 1 + V 2 + V 3) * (V 5 * V 5))
          (by decide)
          (fun | 0 => triForm e c x (n + 1) | 1 => e (n + 1) | 2 => c n | 3 => c (n + 1)
               | 4 => x n | _ => x (n + 1))
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hid) ?_
      exact Q'.add_le_add ih (Q'.le_refl' _)

theorem triForm_le_triRow (e c x : Nat → Q') (hc : ∀ i, (0 : Q') ≤ c i) :
    ∀ n, triForm e c x n ≤ triRow e c x n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
      have h := Q'.add_le_add (Q'.le_refl' (triForm e c x (n + 1)))
        (Q'.mul_nonneg _ _ (hc n) (q_mul_self_nonneg (x n)))
      rw [Q'.add_zero'] at h
      exact Q'.le_trans' _ _ _ h (triForm_key e c x hc n)

theorem triRow_le (e c x : Nat → Q') (ρ : Q') (hrow : ∀ i, e i + cl c i + c i ≤ ρ) :
    ∀ n, triRow e c x n ≤ ρ * finSum (fun i => x i * x i) n
  | 0 => by
      show (0 : Q') ≤ ρ * 0
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_zero_eqv ρ))
  | n + 1 => by
      show triRow e c x n + (e n + cl c n + c n) * (x n * x n) ≤
        ρ * (finSum (fun i => x i * x i) n + x n * x n)
      have h := Q'.add_le_add (triRow_le e c x ρ hrow n)
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (hrow n) (q_mul_self_nonneg (x n)))
      refine Q'.le_trans' _ _ _ h (Q'.le_of_eqv ?_)
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 * V 1 + V 0 * V 2) (V 0 * (V 1 + V 2)) (by decide)
        (fun | 0 => ρ | 1 => finSum (fun i => x i * x i) n | _ => x n * x n)

/-- **Infinite tridiagonal row-sum test** (finitely supported sequences, any cutoff). -/
theorem triForm_le (e c x : Nat → Q') (ρ : Q') (hc : ∀ i, (0 : Q') ≤ c i)
    (hrow : ∀ i, e i + cl c i + c i ≤ ρ) (n : Nat) :
    triForm e c x n ≤ ρ * finSum (fun i => x i * x i) n :=
  Q'.le_trans' _ _ _ (triForm_le_triRow e c x hc n) (triRow_le e c x ρ hrow n)


/-! ## The W = 1 model with the vacuum, all spins -/

def c4' (s : Nat) : Nat := s * (s + 2)
def eS (w : Q') (s : Nat) : Q' := w ^ (4 * c4' s)
def cS (κ w : Q') (s : Nat) : Q' := κ * w ^ (2 * c4' s + 2 * c4' (s + 1))

/-- The vacuum diagonal entry is `1`, so `⟨χ₀,Tχ₀⟩ = 1`. -/
theorem vacuum_rayleigh (w : Q') : eS w 0 = 1 := rfl

/-- Vacuum coupling `c 0 = κ w⁶ ≠ 0` (kept in the operator). -/
theorem vacuum_coupling (κ w : Q') : cS κ w 0 = κ * w ^ 6 := rfl

theorem pow_antitone (w : Q') (h0 : (0 : Q') ≤ w) (h1 : w ≤ 1) (m : Nat) :
    ∀ d, w ^ (m + d) ≤ w ^ m
  | 0 => Q'.le_refl' _
  | d + 1 => by
      show w * w ^ (m + d) ≤ w ^ m
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ h1 (Q'.pow_nonneg w h0 (m + d)))
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) (pow_antitone w h0 h1 m d))

theorem pow_le_of_le (w : Q') (h0 : (0 : Q') ≤ w) (h1 : w ≤ 1) {m k : Nat} (h : m ≤ k) :
    w ^ k ≤ w ^ m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact pow_antitone w h0 h1 m d

/-- **Excited (χ₀⊥) form bound, all spins.** With `y_i = x_{i+1}` (i.e. `x₀ = 0`):
`⟨x,Tx⟩ ≤ (w^{12} + κ w^{22}) ‖x‖²` for every finitely supported `x ⊥ χ₀`. -/
theorem excitedForm_bound (w κ : Q') (h0 : (0 : Q') ≤ w) (h1 : w ≤ 1) (hκ : (0 : Q') ≤ κ)
    (hsmall : w ^ 32 + κ * w ^ 22 ≤ w ^ 12) (y : Nat → Q') (n : Nat) :
    triForm (fun i => eS w (i + 1)) (fun i => cS κ w (i + 1)) y n ≤
      (w ^ 12 + κ * w ^ 22) * finSum (fun i => y i * y i) n := by
  refine triForm_le _ _ y _ (fun i => Q'.mul_nonneg _ _ hκ (Q'.pow_nonneg w h0 _)) ?_ n
  intro i
  cases i with
  | zero =>
      show w ^ 12 + 0 + κ * w ^ 22 ≤ w ^ 12 + κ * w ^ 22
      rw [Q'.add_zero']; exact Q'.le_refl' _
  | succ k =>
      show eS w (k + 2) + cS κ w (k + 1) + cS κ w (k + 2) ≤ w ^ 12 + κ * w ^ 22
      have hk2 : 32 ≤ 4 * c4' (k + 2) := by
        show 32 ≤ 4 * ((k + 2) * (k + 2 + 2))
        have : 2 * 4 ≤ (k + 2) * (k + 2 + 2) := Nat.mul_le_mul (by omega) (by omega)
        omega
      have hc1 : 22 ≤ 2 * c4' (k + 1) + 2 * c4' (k + 1 + 1) := by
        show 22 ≤ 2 * ((k + 1) * (k + 1 + 2)) + 2 * ((k + 1 + 1) * (k + 1 + 1 + 2))
        have a : 1 * 3 ≤ (k + 1) * (k + 1 + 2) := Nat.mul_le_mul (by omega) (by omega)
        have b : 2 * 4 ≤ (k + 1 + 1) * (k + 1 + 1 + 2) := Nat.mul_le_mul (by omega) (by omega)
        omega
      have hc2 : 22 ≤ 2 * c4' (k + 2) + 2 * c4' (k + 2 + 1) := by
        show 22 ≤ 2 * ((k + 2) * (k + 2 + 2)) + 2 * ((k + 2 + 1) * (k + 2 + 1 + 2))
        have a : 2 * 4 ≤ (k + 2) * (k + 2 + 2) := Nat.mul_le_mul (by omega) (by omega)
        have b : 3 * 5 ≤ (k + 2 + 1) * (k + 2 + 1 + 2) := Nat.mul_le_mul (by omega) (by omega)
        omega
      have e1 : eS w (k + 2) ≤ w ^ 32 := pow_le_of_le w h0 h1 hk2
      have e2 : cS κ w (k + 1) ≤ κ * w ^ 22 :=
        Q'.mul_le_mul_of_nonneg_left _ _ κ (pow_le_of_le w h0 h1 hc1) hκ
      have e3 : cS κ w (k + 2) ≤ κ * w ^ 22 :=
        Q'.mul_le_mul_of_nonneg_left _ _ κ (pow_le_of_le w h0 h1 hc2) hκ
      have hs := Q'.add_le_add (Q'.add_le_add e1 e2) e3
      refine Q'.le_trans' _ _ _ hs ?_
      have h2 := Q'.add_le_add hsmall (Q'.le_refl' (κ * w ^ 22))
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) h2
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (V 0 + V 1 + V 1) ((V 0 + V 1) + V 1) (by decide)
        (fun | 0 => w ^ 32 | _ => κ * w ^ 22)

def w1024 : Q' := Q'.mkPos 1 1024 (by decide)
def wHalf : Q' := Q'.mkPos 1 2 (by decide)
def kappa : Q' := Q'.mkPos 1 4 (by decide)

set_option maxRecDepth 100000 in
/-- **Certified, w = 1/1024, κ = 1/4, all spins.** -/
theorem excited_bound_1024 (y : Nat → Q') (n : Nat) :
    triForm (fun i => eS w1024 (i + 1)) (fun i => cS kappa w1024 (i + 1)) y n ≤
      (w1024 ^ 12 + kappa * w1024 ^ 22) * finSum (fun i => y i * y i) n :=
  excitedForm_bound w1024 kappa (by decide) (by decide) (by decide) (by decide) y n

set_option maxRecDepth 100000 in
/-- **Certified, w = 1/2, κ = 1/4, all spins.** -/
theorem excited_bound_half (y : Nat → Q') (n : Nat) :
    triForm (fun i => eS wHalf (i + 1)) (fun i => cS kappa wHalf (i + 1)) y n ≤
      (wHalf ^ 12 + kappa * wHalf ^ 22) * finSum (fun i => y i * y i) n :=
  excitedForm_bound wHalf kappa (by decide) (by decide) (by decide) (by decide) y n

/-! ## Dense n×n row-sum (Schur) form test -/

theorem finSumCongr {f g : Nat → Q'} (h : ∀ i, (f i).eqv (g i)) :
    ∀ n, (finSum f n).eqv (finSum g n)
  | 0 => Q'.eqv_refl _
  | n + 1 => Q'.add_eqv_congr' (finSumCongr h n) (h n)

def hlf : Q' := Q'.mkPos 1 2 (by decide)

theorem hlf_two (t : Q') : (hlf * (t + t)).eqv t := by
  let V := PolyExpr.var
  have h1 : (hlf * (t + t)).eqv ((hlf + hlf) * t) :=
    poly_identity_of_normal_eq (V 0 * (V 1 + V 1)) ((V 0 + V 0) * V 1) (by decide)
      (fun | 0 => hlf | _ => t)
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (by decide : (hlf + hlf).eqv 1)) (Q'.one_mul_eqv t))

theorem term_le (a xi xj : Q') (ha : (0 : Q') ≤ a) :
    a * (xi * xj) ≤ (hlf * xi * xi) * a + (hlf * xj * xj) * a := by
  have hm := amgm a xi xj ha
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _ hlf hm (by decide)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (hlf_two _))) ?_
  refine Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv ?_)
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq
    (V 0 * (V 1 * (V 2 * V 2) + V 1 * (V 3 * V 3)))
    (V 0 * V 2 * V 2 * V 1 + V 0 * V 3 * V 3 * V 1) (by decide)
    (fun | 0 => hlf | 1 => a | 2 => xi | _ => xj)

/-- **Dense row-sum test**: symmetric nonnegative `a`, every truncated row sum `≤ ρ`
⇒ `Σ_{i,j<n} a_ij x_i x_j ≤ ρ Σ_{i<n} x_i²`. -/
theorem schurN (a : Nat → Nat → Q') (x : Nat → Q') (ρ : Q') (n : Nat)
    (hnn : ∀ i j, (0 : Q') ≤ a i j) (hsym : ∀ i j, a i j = a j i)
    (hrow : ∀ i, finSum (fun j => a i j) n ≤ ρ) :
    finSum (fun i => finSum (fun j => a i j * (x i * x j)) n) n ≤
      ρ * finSum (fun i => x i * x i) n := by
  have hX : ∀ i, (0 : Q') ≤ hlf * x i * x i := fun i => by
    have := Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ hlf) (q_mul_self_nonneg (x i))
    refine Q'.le_trans' _ _ _ this (Q'.le_of_eqv ?_)
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (V 0 * (V 1 * V 1)) (V 0 * V 1 * V 1) (by decide)
      (fun | 0 => hlf | _ => x i)
  -- termwise
  have s1 := YMGap.Constructive.ExpNeg.finSum_le_finSum_of_termwise _ _
    (fun i => YMGap.Constructive.ExpNeg.finSum_le_finSum_of_termwise _ _
      (fun j => term_le (a i j) (x i) (x j) (hnn i j)) n) n
  refine Q'.le_trans' _ _ _ s1 ?_
  -- split the double sum
  have split : (finSum (fun i => finSum (fun j =>
      (hlf * x i * x i) * a i j + (hlf * x j * x j) * a i j) n) n).eqv
      (finSum (fun i => (hlf * x i * x i) * finSum (fun j => a i j) n) n +
        finSum (fun j => (hlf * x j * x j) * finSum (fun i => a j i) n) n) := by
    refine Q'.eqv_trans _ _ _ (finSumCongr (fun i => RationalTail.finSum_add _ _ n) n) ?_
    refine Q'.eqv_trans _ _ _ (RationalTail.finSum_add _ _ n) ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · exact finSumCongr (fun i => Q'.eqv_symm (RationalTail.const_mul_finSum _ _ n)) n
    · refine Q'.eqv_trans _ _ _ (RationalTail.finSum_swap (fun i j => (hlf * x j * x j) * a i j) n n) ?_
      refine finSumCongr (fun j => ?_) n
      refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (RationalTail.const_mul_finSum _ _ n))
      exact finSumCongr (fun i => by rw [hsym i j]; exact Q'.eqv_refl _) n
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv split) ?_
  have b1 := YMGap.Constructive.ExpNeg.finSum_le_finSum_of_termwise
    (fun i => (hlf * x i * x i) * finSum (fun j => a i j) n) (fun i => (hlf * x i * x i) * ρ)
    (fun i => Q'.mul_le_mul_of_nonneg_left _ _ _ (hrow i) (hX i)) n
  have b2 := YMGap.Constructive.ExpNeg.finSum_le_finSum_of_termwise
    (fun j => (hlf * x j * x j) * finSum (fun i => a j i) n) (fun j => (hlf * x j * x j) * ρ)
    (fun j => Q'.mul_le_mul_of_nonneg_left _ _ _ (hrow j) (hX j)) n
  refine Q'.le_trans' _ _ _ (Q'.add_le_add b1 b2) (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (RationalTail.finSum_add _ _ n)) ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (RationalTail.const_mul_finSum _ _ n))
  refine finSumCongr (fun i => ?_) n
  let V := PolyExpr.var
  have h1 : ((hlf * x i * x i) * ρ + (hlf * x i * x i) * ρ).eqv (hlf * ((ρ * (x i * x i)) + (ρ * (x i * x i)))) :=
    poly_identity_of_normal_eq (V 0 * V 1 * V 1 * V 2 + V 0 * V 1 * V 1 * V 2)
      (V 0 * ((V 2 * (V 1 * V 1)) + (V 2 * (V 1 * V 1)))) (by decide)
      (fun | 0 => hlf | 1 => x i | _ => ρ)
  exact Q'.eqv_trans _ _ _ h1 (hlf_two _)

end YMGap.Continuum.W1VacuumTailRowSum

#print axioms YMGap.Continuum.W1VacuumTailRowSum.triForm_le
#print axioms YMGap.Continuum.W1VacuumTailRowSum.excitedForm_bound
#print axioms YMGap.Continuum.W1VacuumTailRowSum.excited_bound_1024
#print axioms YMGap.Continuum.W1VacuumTailRowSum.excited_bound_half
#print axioms YMGap.Continuum.W1VacuumTailRowSum.schurN

