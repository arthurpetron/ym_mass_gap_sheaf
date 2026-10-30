/-
# Backward-arc power monotonicity for the two-arc torus covariance

**Label: elementary monotonicity lemma. NOT gap evidence. Does NOT discharge `hcov`.**

For a positive self-adjoint contraction `T` and a vector `y`, the sequence
`c k := ⟨y, T^k y⟩` is nonincreasing in `k`. Abstracted here as the hypothesis
`hstep : ∀ k, c (k+1) ≤ c k`. Consequences:
* `c_antitone` : `k ≤ l → c l ≤ c k`;
* `backward_arc_le_forward` : `2m+1 ≤ M → c (2M - 2m) ≤ c (2m)`;
* `twoArc_le_twice_forward` and `twoArc_cov_of_forward` : a two-arc covariance bound
  `c(2m) + c(2M-2m) ≤ 2C·X` follows from the single-arc bound `c(2m) ≤ C·X`.

This is the honest content of the HP notes' "two-cut reflection discharges `hcov`" claim
(misattributed to Hsu 2610.29019 App. F.5; F.5 is a site-reflection factorization). It is
plain power monotonicity of a positive contraction, which **U(1) also satisfies**. Only the
backward arc is handled.

OPEN (not formalized here): `hstep` for the repo transfer carrier (`completedTime`) and,
separately, the identification of `EhatHK` with the transfer correlator `c` (the remaining
content of `hcov`).
-/

import YMGap.Constructive.Rationals
import YMGap.Constructive.RationalsMul
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.TorusBackwardArcMonotone

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

/-- **Antitone from one-step monotonicity (PROVED).** -/
theorem c_antitone (c : Nat → Q') (hstep : ∀ k, c (k + 1) ≤ c k) (k : Nat) :
    ∀ d, c (k + d) ≤ c k
  | 0 => Q'.le_refl' _
  | d + 1 => Q'.le_trans' _ _ _ (hstep (k + d)) (c_antitone c hstep k d)

theorem c_antitone' (c : Nat → Q') (hstep : ∀ k, c (k + 1) ≤ c k) {k l : Nat} (hkl : k ≤ l) :
    c l ≤ c k := by
  have h := c_antitone c hstep k (l - k)
  rwa [Nat.add_sub_cancel' hkl] at h

/-- **Backward arc ≤ forward arc (PROVED):** `2m+1 ≤ M → c (2M-2m) ≤ c (2m)`. -/
theorem backward_arc_le_forward (c : Nat → Q') (hstep : ∀ k, c (k + 1) ≤ c k) (m M : Nat)
    (hmM : 2 * m + 1 ≤ M) : c (2 * M - 2 * m) ≤ c (2 * m) := by
  apply c_antitone' c hstep
  have h0 : 2 * m ≤ M := Nat.le_trans (Nat.le_succ _) hmM
  have h1 : 2 * m + 2 * m ≤ 2 * M := by
    rw [← Nat.two_mul (2 * m)]; exact Nat.mul_le_mul_left 2 h0
  exact Nat.le_sub_of_add_le h1

/-- **Two arcs ≤ twice the forward arc (PROVED).** -/
theorem twoArc_le_twice_forward (c : Nat → Q') (hstep : ∀ k, c (k + 1) ≤ c k) (m M : Nat)
    (hmM : 2 * m + 1 ≤ M) : c (2 * m) + c (2 * M - 2 * m) ≤ (2 : Q') * c (2 * m) :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ (backward_arc_le_forward c hstep m M hmM))
    (Q'.le_of_eqv (poly_identity_of_normal_eq (.add (.var 0) (.var 0))
      (.mul (.const 2) (.var 0)) (by decide) (fun _ => c (2 * m))))

/-- **Two-arc `hcov` with constant `2C` from the single-arc bound (PROVED from `hforward_OPEN`).** -/
theorem twoArc_cov_of_forward (c : Nat → Q') (hstep : ∀ k, c (k + 1) ≤ c k) (m M : Nat)
    (hmM : 2 * m + 1 ≤ M) (C X : Q') (hforward_OPEN : c (2 * m) ≤ C * X) :
    c (2 * m) + c (2 * M - 2 * m) ≤ ((2 : Q') * C) * X :=
  Q'.le_trans' _ _ _ (twoArc_le_twice_forward c hstep m M hmM)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hforward_OPEN (by decide))
      (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _)))

end YMGap.Continuum.TorusBackwardArcMonotone
