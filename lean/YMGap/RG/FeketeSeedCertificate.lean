/-
# Fekete-style seed certificate for submultiplicative transfer-norm sequences

**Label: finite-certificate FORMAT. NOT gap evidence. NOT a proof of the Yang–Mills mass gap.**

If `Λ : Nat → Q'` is nonnegative and submultiplicative, `Λ (n+m) ≤ Λ n · Λ m` (automatic for
operator norms of powers of one transfer operator), then a single finite-`N` bound
`Λ N ≤ ρ^N` propagates to every multiple: `Λ (k·N) ≤ ρ^(k·N)` for `k ≥ 1`, and to every length
`Λ (q·N + r) ≤ ρ^(q·N) · Λ r`. This turns the `hseed` input (seed contraction at the
crossover nome `w_{j0}`) into one finite, checkable inequality.

Method: Okuyama–Ohzeki 2610.32291 (Fekete sandwich on hierarchical lattices). It holds for
abelian models too; a strong-coupling seed is U(1)-valid. This is a crossover certificate
format, not gap evidence.

PROVED: `qpow_nonneg`, `qpow_add`, `qpow_le_one`, `qpow_le_self`, `fekete_multiple`,
`fekete_general`, `fekete_seed_lt_one`.

OPEN (hypothesis `hcert_OPEN`): the actual certified value `Λ_N ≤ ρ^N` at the crossover nome
(a numerical/interval computation not done here), and the identification of `Λ` with the
transfer-operator norms of the repo carrier.
-/

import YMGap.Constructive.Rationals
import YMGap.Constructive.RationalsMul
import YMGap.Constructive.RegularCRealArith
import YMGap.Constructive.Sqrt
import YMGap.Continuum.RingNormaliser

namespace YMGap.RG.FeketeSeedCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Rational power `ρ^n` by recursion. -/
def qpow (ρ : Q') : Nat → Q'
  | 0 => 1
  | n + 1 => qpow ρ n * ρ

theorem qpow_nonneg (ρ : Q') (hρ : (0 : Q') ≤ ρ) : ∀ n, (0 : Q') ≤ qpow ρ n
  | 0 => (by decide : (0 : Q') ≤ 1)
  | n + 1 => Q'.mul_nonneg _ _ (qpow_nonneg ρ hρ n) hρ

/-- `ρ^(a+b) ≈ ρ^a · ρ^b` (PROVED). -/
theorem qpow_add (ρ : Q') (a : Nat) : ∀ b, qpow ρ (a + b) ≈ qpow ρ a * qpow ρ b
  | 0 => poly_identity_of_normal_eq (.var 0) (.mul (.var 0) (.const 1)) (by decide)
      (fun _ => qpow ρ a)
  | b + 1 =>
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ ρ (qpow_add ρ a b))
        (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.var 0) (.mul (.var 1) (.var 2))) (by decide)
          (fun | 0 => qpow ρ a | 1 => qpow ρ b | _ => ρ))

/-- `0 ≤ ρ ≤ 1 ⟹ ρ^n ≤ 1` (PROVED). -/
theorem qpow_le_one (ρ : Q') (hρ0 : (0 : Q') ≤ ρ) (hρ1 : ρ ≤ (1 : Q')) :
    ∀ n, qpow ρ n ≤ (1 : Q')
  | 0 => (by decide : (1 : Q') ≤ 1)
  | n + 1 =>
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ ρ (qpow_le_one ρ hρ0 hρ1 n) hρ0)
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (poly_identity_of_normal_eq (.mul (.const 1) (.var 0)) (.var 0)
            (by decide) (fun _ => ρ))) hρ1)

/-- `0 ≤ ρ ≤ 1 ⟹ ρ^(n+1) ≤ ρ` (PROVED). -/
theorem qpow_le_self (ρ : Q') (hρ0 : (0 : Q') ≤ ρ) (hρ1 : ρ ≤ (1 : Q')) (n : Nat) :
    qpow ρ (n + 1) ≤ ρ :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ ρ (qpow_le_one ρ hρ0 hρ1 n) hρ0)
    (Q'.le_of_eqv (poly_identity_of_normal_eq (.mul (.const 1) (.var 0)) (.var 0)
      (by decide) (fun _ => ρ)))


/-- **Multiples (PROVED from `hsub` and OPEN `hcert_OPEN`).**
`Λ N ≤ ρ^N` ⟹ `Λ ((k+1)·N) ≤ ρ^((k+1)·N)` for every `k`. -/
theorem fekete_multiple (Λ : Nat → Q') (hΛ0 : ∀ n, (0 : Q') ≤ Λ n)
    (hsub : ∀ n m, Λ (n + m) ≤ Λ n * Λ m) (ρ : Q') (hρ : (0 : Q') ≤ ρ) (N : Nat)
    (hcert_OPEN : Λ N ≤ qpow ρ N) : ∀ k, Λ ((k + 1) * N) ≤ qpow ρ ((k + 1) * N)
  | 0 => by rw [Nat.one_mul]; exact hcert_OPEN
  | k + 1 => by
      have ih := fekete_multiple Λ hΛ0 hsub ρ hρ N hcert_OPEN k
      rw [Nat.succ_mul]
      exact Q'.le_trans' _ _ _ (hsub _ _)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg ih hcert_OPEN (qpow_nonneg ρ hρ _) (hΛ0 N))
          (Q'.ge_of_eqv (qpow_add ρ _ _)))

/-- **Every length (PROVED):** `Λ ((q+1)·N + r) ≤ ρ^((q+1)·N) · Λ r`. -/
theorem fekete_general (Λ : Nat → Q') (hΛ0 : ∀ n, (0 : Q') ≤ Λ n)
    (hsub : ∀ n m, Λ (n + m) ≤ Λ n * Λ m) (ρ : Q') (hρ : (0 : Q') ≤ ρ) (N : Nat)
    (hcert_OPEN : Λ N ≤ qpow ρ N) (q r : Nat) :
    Λ ((q + 1) * N + r) ≤ qpow ρ ((q + 1) * N) * Λ r :=
  Q'.le_trans' _ _ _ (hsub _ _)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (fekete_multiple Λ hΛ0 hsub ρ hρ N hcert_OPEN q) (hΛ0 r))

/-- **Seed below one (PROVED):** with `0 ≤ ρ < 1`, `N ≥ 1`, every multiple satisfies
`Λ ((k+1)·N) ≤ ρ < 1`, i.e. a strict seed contraction. -/
theorem fekete_seed_lt_one (Λ : Nat → Q') (hΛ0 : ∀ n, (0 : Q') ≤ Λ n)
    (hsub : ∀ n m, Λ (n + m) ≤ Λ n * Λ m) (ρ : Q') (hρ0 : (0 : Q') ≤ ρ) (hρ1 : ρ < (1 : Q')) (N : Nat)
    (hcert_OPEN : Λ (N + 1) ≤ qpow ρ (N + 1)) (k : Nat) :
    Λ ((k + 1) * (N + 1)) ≤ ρ ∧ ρ < (1 : Q') := by
  refine ⟨Q'.le_trans' _ _ _ (fekete_multiple Λ hΛ0 hsub ρ hρ0 (N + 1) hcert_OPEN k) ?_, hρ1⟩
  have h : (k + 1) * (N + 1) = ((k + 1) * (N + 1) - 1) + 1 := by
    rw [Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos k) (Nat.succ_pos N))]
  rw [h]
  exact qpow_le_self ρ hρ0 (Q'.le_of_lt hρ1) _

/-- Sanity check: `(1/2)^3 ≈ 1/8` (decide). -/
example : qpow (Q'.mkPos 1 2 (by decide)) 3 ≈ Q'.mkPos 1 8 (by decide) := by decide

end YMGap.RG.FeketeSeedCertificate
