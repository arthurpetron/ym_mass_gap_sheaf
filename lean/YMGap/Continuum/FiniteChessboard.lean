/-
# P3: the abstract chessboard estimate in power form (Cauchy–Schwarz doubling induction)

**Label: abstract RP scaffolding; also true for U(1); not gap evidence. No chart-closure claim.**
Additive. Constructive: no maximiser, no contradiction, no roots, no `Classical`. Every estimate is a rational
inequality, and the replication seminorm stays in power form `ω(conf F)^(2^k)`.

## Setting (`RPFunctional`)
An observable setoid `Obs` carries a commutative associative product and a family of reflections `θ d`, one per axis.
Each `θ d` is a multiplicative congruence, and the reflections commute pairwise. A rational functional `ω` respects `≈`.
For every axis `d` it satisfies:
* **RP** `0 ≤ ω(A · θ_d A)`;
* **polarisation** `ω((sA+tB) · θ_d(sA+tB)) = s²ω(Aθ_dA) + 2st·ω(Aθ_dB) + t²ω(Bθ_dB)` for integers `s, t`
  (bilinearity and symmetry of `(A,B) ↦ ω(A θ_d B)`, stated as one rational identity).

`θ` need not be involutive, and `ω` need not be θ-invariant.

## Chessboard configurations
`conf k F`, for `F : List Bool → Obs` (block labels `x ∈ {0,1}^k`, head = outermost axis), is
`conf (k+1) F = conf k (F ∘ cons false) · θ_k (conf k (F ∘ cons true))`. This is the product over the `2^k` blocks
of the reflected copies `θ^x (F x)`.

## Main theorem (`chessboard_pow`)
`ω(conf k F)^(2^k) ≤ ∏_{c ∈ {0,1}^k} ω(conf k (fun _ => F c))`. Here `pow2 k x = x^(2^k)` by iterated squaring
(`pow2_eq_pow` bridges it to `Q'` powers).
The proof is induction on `k` by Cauchy–Schwarz along the outermost axis. The doubled configuration
`conf k G · θ_k conf k G` is identified with `conf k (G · θ_k G)` (`conf_mul`, `conf_theta`), so the induction
hypothesis applies to the same functional on `k` axes.
-/

import YMGap.Continuum.SU2TorusRPCSRat
import YMGap.Constructive.Sqrt
import YMGap.Constructive.Geometric
import YMGap.Constructive.SumOfSquares
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.FiniteChessboard

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2TorusRPCSRat (quad cs_q)

/-- An RP functional with a family of commuting reflections (see the header). -/
structure RPFunctional where
  Obs : Type
  E : Obs → Obs → Prop
  E_refl : ∀ a, E a a
  E_symm : ∀ {a b}, E a b → E b a
  E_trans : ∀ {a b c}, E a b → E b c → E a c
  mul : Obs → Obs → Obs
  mul_congr : ∀ {a a' b b'}, E a a' → E b b' → E (mul a b) (mul a' b')
  mul_comm : ∀ a b, E (mul a b) (mul b a)
  mul_assoc : ∀ a b c, E (mul (mul a b) c) (mul a (mul b c))
  θ : Nat → Obs → Obs
  θ_congr : ∀ d {a b}, E a b → E (θ d a) (θ d b)
  θ_mul : ∀ d a b, E (θ d (mul a b)) (mul (θ d a) (θ d b))
  θ_comm : ∀ d e a, E (θ d (θ e a)) (θ e (θ d a))
  lin : Int → Obs → Int → Obs → Obs
  ω : Obs → Q'
  ω_congr : ∀ {a b}, E a b → (ω a).eqv (ω b)
  rp : ∀ d A, (0 : Q') ≤ ω (mul A (θ d A))
  polar : ∀ d A B s t, (ω (mul (lin s A t B) (θ d (lin s A t B)))).eqv
    (quad (ω (mul A (θ d A))) (ω (mul A (θ d B))) (ω (mul B (θ d B))) s t)

variable (R : RPFunctional)

/-- **Reflection Cauchy–Schwarz (power form):** `ω(Aθ_dB)² ≤ ω(Aθ_dA)·ω(Bθ_dB)`. -/
theorem rp_cs (d : Nat) (A B : R.Obs) :
    R.ω (R.mul A (R.θ d B)) * R.ω (R.mul A (R.θ d B)) ≤
      R.ω (R.mul A (R.θ d A)) * R.ω (R.mul B (R.θ d B)) :=
  cs_q _ _ _ fun s t =>
    Q'.le_trans' _ _ _ (R.rp d (R.lin s A t B)) (Q'.le_of_eqv (R.polar d A B s t))

/-- Chessboard configuration over `{0,1}^k` (head of the label = outermost axis `k-1`). -/
def conf : (k : Nat) → (List Bool → R.Obs) → R.Obs
  | 0, F => F []
  | k + 1, F => R.mul (conf k fun x => F (false :: x)) (R.θ k (conf k fun x => F (true :: x)))

theorem conf_congr : ∀ (k : Nat) {F G : List Bool → R.Obs}, (∀ x, R.E (F x) (G x)) →
    R.E (conf R k F) (conf R k G)
  | 0, _, _, h => h []
  | k + 1, _, _, h => R.mul_congr (conf_congr k fun _ => h _) (R.θ_congr k (conf_congr k fun _ => h _))

/-- `(ab)(cd) ≈ (ac)(bd)` in the commutative setoid monoid. -/
theorem mul_swap4 (a b c d : R.Obs) :
    R.E (R.mul (R.mul a b) (R.mul c d)) (R.mul (R.mul a c) (R.mul b d)) := by
  refine R.E_trans (R.mul_assoc a b (R.mul c d)) ?_
  refine R.E_trans (R.mul_congr (R.E_refl a) (R.E_symm (R.mul_assoc b c d))) ?_
  refine R.E_trans (R.mul_congr (R.E_refl a) (R.mul_congr (R.mul_comm b c) (R.E_refl d))) ?_
  refine R.E_trans (R.mul_congr (R.E_refl a) (R.mul_assoc c b d)) ?_
  exact R.E_symm (R.mul_assoc a c (R.mul b d))

/-- `conf` is multiplicative blockwise. -/
theorem conf_mul : ∀ (k : Nat) (F G : List Bool → R.Obs),
    R.E (conf R k fun x => R.mul (F x) (G x)) (R.mul (conf R k F) (conf R k G))
  | 0, _, _ => R.E_refl _
  | k + 1, F, G => by
      show R.E (R.mul (conf R k fun x => R.mul (F (false :: x)) (G (false :: x)))
        (R.θ k (conf R k fun x => R.mul (F (true :: x)) (G (true :: x)))))
        (R.mul (R.mul (conf R k fun x => F (false :: x)) (R.θ k (conf R k fun x => F (true :: x))))
          (R.mul (conf R k fun x => G (false :: x)) (R.θ k (conf R k fun x => G (true :: x)))))
      refine R.E_trans (R.mul_congr (conf_mul k _ _)
        (R.E_trans (R.θ_congr k (conf_mul k _ _)) (R.θ_mul k _ _))) ?_
      exact mul_swap4 R _ _ _ _

/-- A reflection of an axis `j ≥ k` passes blockwise into a `k`-axis configuration. -/
theorem conf_theta : ∀ (k j : Nat), k ≤ j → ∀ (F : List Bool → R.Obs),
    R.E (R.θ j (conf R k F)) (conf R k fun x => R.θ j (F x))
  | 0, _, _, _ => R.E_refl _
  | k + 1, j, hj, F => by
      have hk : k ≤ j := Nat.le_of_succ_le hj
      refine R.E_trans (R.θ_mul j _ _) (R.mul_congr (conf_theta k j hk _) ?_)
      exact R.E_trans (R.θ_comm j k _) (R.θ_congr k (conf_theta k j hk _))

/-- The doubled half-configuration is again a `k`-axis configuration. -/
theorem conf_double (k : Nat) (G : List Bool → R.Obs) :
    R.E (R.mul (conf R k G) (R.θ k (conf R k G))) (conf R k fun x => R.mul (G x) (R.θ k (G x))) :=
  R.E_symm (R.E_trans (conf_mul R k _ _)
    (R.mul_congr (R.E_refl _) (R.E_symm (conf_theta R k k (Nat.le_refl k) G))))

/-! ## Power form and the cube product -/

/-- `pow2 k x = x^(2^k)` by iterated squaring. -/
def pow2 : Nat → Q' → Q'
  | 0, x => x
  | k + 1, x => pow2 k (x * x)

/-- Product over `{0,1}^k` (same label convention as `conf`). -/
def cubeProd : (k : Nat) → (List Bool → Q') → Q'
  | 0, h => h []
  | k + 1, h => cubeProd k (fun x => h (false :: x)) * cubeProd k (fun x => h (true :: x))

theorem sq_nonneg' (x : Q') : (0 : Q') ≤ x * x :=
  YMGap.Constructive.SumOfSquares.q_mul_self_nonneg x

theorem pow2_congr : ∀ (k : Nat) {x y : Q'}, x.eqv y → (pow2 k x).eqv (pow2 k y)
  | 0, _, _, h => h
  | k + 1, _, _, h => pow2_congr k (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
      (Q'.mul_eqv_congr_left _ _ _ h))

theorem pow2_nonneg : ∀ (k : Nat) {x : Q'}, (0 : Q') ≤ x → (0 : Q') ≤ pow2 k x
  | 0, _, h => h
  | k + 1, x, _ => pow2_nonneg k (sq_nonneg' x)

theorem pow2_mono : ∀ (k : Nat) {x y : Q'}, (0 : Q') ≤ x → x ≤ y → pow2 k x ≤ pow2 k y
  | 0, _, _, _, h => h
  | k + 1, x, _, hx, h => pow2_mono k (sq_nonneg' x)
      (Q'.mul_le_mul_of_nonneg h h (Q'.le_trans' _ _ _ hx h) hx)

theorem pow2_mul : ∀ (k : Nat) (x y : Q'), (pow2 k (x * y)).eqv (pow2 k x * pow2 k y)
  | 0, _, _ => Q'.eqv_refl _
  | k + 1, x, y => by
      show (pow2 k ((x * y) * (x * y))).eqv (pow2 k (x * x) * pow2 k (y * y))
      refine Q'.eqv_trans _ _ _ (pow2_congr k ?_) (pow2_mul k _ _)
      exact YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide)
        (fun i => if i = 0 then x else y)

theorem cubeProd_congr : ∀ (k : Nat) {g h : List Bool → Q'}, (∀ x, (g x).eqv (h x)) →
    (cubeProd k g).eqv (cubeProd k h)
  | 0, _, _, e => e []
  | k + 1, _, _, e => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (cubeProd_congr k fun _ => e _))
      (Q'.mul_eqv_congr_left _ _ _ (cubeProd_congr k fun _ => e _))

/-- `ω(conf)` of a doubled configuration is nonnegative (RP). -/
theorem conf_double_nonneg (k : Nat) (G : List Bool → R.Obs) :
    (0 : Q') ≤ R.ω (conf R k fun x => R.mul (G x) (R.θ k (G x))) :=
  Q'.le_trans' _ _ _ (R.rp k (conf R k G)) (Q'.le_of_eqv (R.ω_congr (conf_double R k G)))

/-- `conf (k+1)` of a constant equals the doubled `conf k` of that constant (rewritten blockwise). -/
theorem conf_const_succ (k : Nat) (a : R.Obs) :
    (R.ω (conf R (k + 1) fun _ => a)).eqv (R.ω (conf R k fun _ => R.mul a (R.θ k a))) :=
  R.ω_congr (conf_double R k fun _ => a)

/-- Nonnegativity of every replicated (constant) configuration with at least one axis. -/
theorem conf_const_nonneg (k : Nat) (a : R.Obs) : (0 : Q') ≤ R.ω (conf R (k + 1) fun _ => a) :=
  R.rp k (conf R k fun _ => a)

/-- **Chessboard estimate, power form (`k ≥ 0` axes):**
`ω(conf k F)^(2^k) ≤ ∏_{c ∈ {0,1}^k} ω(conf k (fun _ => F c))`. -/
theorem chessboard_pow : ∀ (k : Nat) (F : List Bool → R.Obs),
    pow2 k (R.ω (conf R k F)) ≤ cubeProd k (fun c => R.ω (conf R k fun _ => F c))
  | 0, F => Q'.le_refl' _
  | k + 1, F => by
      let G0 : List Bool → R.Obs := fun x => F (false :: x)
      let G1 : List Bool → R.Obs := fun x => F (true :: x)
      let H0 : List Bool → R.Obs := fun x => R.mul (G0 x) (R.θ k (G0 x))
      let H1 : List Bool → R.Obs := fun x => R.mul (G1 x) (R.θ k (G1 x))
      let g := R.ω (conf R (k + 1) F)
      let a := R.ω (conf R k H0)
      let b := R.ω (conf R k H1)
      have ha : (0 : Q') ≤ a := conf_double_nonneg R k G0
      have hb : (0 : Q') ≤ b := conf_double_nonneg R k G1
      -- Cauchy–Schwarz along the outermost axis `k`.
      have hcs : g * g ≤ a * b := by
        have h := rp_cs R k (conf R k G0) (conf R k G1)
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_refl _)) (Q'.le_trans' _ _ _ h (Q'.le_of_eqv ?_))
        exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (R.ω_congr (conf_double R k G0)))
          (Q'.mul_eqv_congr_left _ _ _ (R.ω_congr (conf_double R k G1)))
      have step1 : pow2 (k + 1) g ≤ pow2 k a * pow2 k b :=
        Q'.le_trans' _ _ _ (pow2_mono k (sq_nonneg' g) hcs) (Q'.le_of_eqv (pow2_mul k a b))
      have ih0 := chessboard_pow k H0
      have ih1 := chessboard_pow k H1
      have step2 : pow2 k a * pow2 k b ≤
          cubeProd k (fun c => R.ω (conf R k fun _ => H0 c)) *
            cubeProd k (fun c => R.ω (conf R k fun _ => H1 c)) :=
        Q'.mul_le_mul_of_nonneg ih0 ih1 (Q'.le_trans' _ _ _ (pow2_nonneg k ha) ih0) (pow2_nonneg k hb)
      refine Q'.le_trans' _ _ _ step1 (Q'.le_trans' _ _ _ step2 (Q'.le_of_eqv ?_))
      show (cubeProd k (fun c => R.ω (conf R k fun _ => H0 c)) *
          cubeProd k (fun c => R.ω (conf R k fun _ => H1 c))).eqv
        (cubeProd k (fun c => R.ω (conf R (k + 1) fun _ => F (false :: c))) *
          cubeProd k (fun c => R.ω (conf R (k + 1) fun _ => F (true :: c))))
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (cubeProd_congr k fun c => Q'.eqv_symm (conf_const_succ R k (G0 c))))
        (Q'.mul_eqv_congr_left _ _ _ (cubeProd_congr k fun c => Q'.eqv_symm (conf_const_succ R k (G1 c))))

theorem pow_two_mul : ∀ (x : Q') (n : Nat), ((x * x) ^ n).eqv (x ^ (n * 2))
  | _, 0 => Q'.eqv_refl _
  | x, n + 1 => by
      rw [Nat.succ_mul]
      show ((x * x) * (x * x) ^ n).eqv (x * (x * x ^ (n * 2)))
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (pow_two_mul x n)) ?_
      exact Q'.mul_assoc_eqv x x _

/-- Bridge: `pow2 k x = x^(2^k)` for the `Q'` power of `Geometric`. -/
theorem pow2_eq_pow : ∀ (k : Nat) (x : Q'), (pow2 k x).eqv (x ^ (2 ^ k))
  | 0, x => Q'.eqv_symm (Q'.mul_one_eqv x)
  | k + 1, x => by
      refine Q'.eqv_trans _ _ _ (pow2_eq_pow k (x * x)) ?_
      rw [Nat.pow_succ]
      exact pow_two_mul x (2 ^ k)

end YMGap.Continuum.FiniteChessboard
#print axioms YMGap.Continuum.FiniteChessboard.RPFunctional
#print axioms YMGap.Continuum.FiniteChessboard.rp_cs
#print axioms YMGap.Continuum.FiniteChessboard.conf
#print axioms YMGap.Continuum.FiniteChessboard.conf_congr
#print axioms YMGap.Continuum.FiniteChessboard.mul_swap4
#print axioms YMGap.Continuum.FiniteChessboard.conf_mul
#print axioms YMGap.Continuum.FiniteChessboard.conf_theta
#print axioms YMGap.Continuum.FiniteChessboard.conf_double
#print axioms YMGap.Continuum.FiniteChessboard.pow2
#print axioms YMGap.Continuum.FiniteChessboard.cubeProd
#print axioms YMGap.Continuum.FiniteChessboard.sq_nonneg'
#print axioms YMGap.Continuum.FiniteChessboard.pow2_congr
#print axioms YMGap.Continuum.FiniteChessboard.pow2_nonneg
#print axioms YMGap.Continuum.FiniteChessboard.pow2_mono
#print axioms YMGap.Continuum.FiniteChessboard.pow2_mul
#print axioms YMGap.Continuum.FiniteChessboard.cubeProd_congr
#print axioms YMGap.Continuum.FiniteChessboard.conf_double_nonneg
#print axioms YMGap.Continuum.FiniteChessboard.conf_const_succ
#print axioms YMGap.Continuum.FiniteChessboard.conf_const_nonneg
#print axioms YMGap.Continuum.FiniteChessboard.chessboard_pow
#print axioms YMGap.Continuum.FiniteChessboard.pow_two_mul
#print axioms YMGap.Continuum.FiniteChessboard.pow2_eq_pow
