/-
Track B / R2 — **the AF trajectory-certificate bridge for O(4) restoration**:
discharging the bare per-step sign residual `CouplingRunning.betaDrop_nonneg`
from the PROVED two-loop trajectory certificate.

# Where this sits in the chain

`O4RestorationProgress.CouplingRunning` isolates the O(4)-restoration residual
to a single per-step SIGN condition `betaDrop_nonneg : ∀ k, 0 ≤ betaDrop k` — the
asymptotic-freedom statement that the dimensionless rotation-breaking coupling
runs downhill under blocking (`β ≤ 0`).  Downstream, `rubricO4Restoration_of_coupling`
turns any `CouplingRunning` into the weak legacy slot `RubricO4Restoration`.

Separately, `AFTrajectoryCertificate` packages the NAMED two-loop physics — the
recurrence WITH an explicit cubic remainder `E`
(`|τ_{k+1} − (τ_k − β·τ_k²)| ≤ E·τ_k³`) — and PROVES from it the contracting drop

      drop :  τ_{k+1} ≤ τ_k·(1 − (β/2)·τ_k)                (AFTrajectoryCertificate.drop)

# What this module delivers

The bare sign `betaDrop_nonneg` is exactly downhill monotonicity `g_{k+1} ≤ g_k`.
The certificate's contracting `drop` gives `τ_{k+1} ≤ τ_k·(1 − c·τ_k)`; the only
missing glue is the trivial order fact `τ·(1 − c·τ) ≤ τ` (for `τ ≥ 0`, `c·τ ≥ 0`).
This module supplies that glue (`mul_one_sub_le_self`) and BUILDS the bridge

      couplingRunning_of_AFCertificate : AFTrajectoryCertificate → CouplingRunning

whose `betaDrop_nonneg` field is the DERIVED `g_{k+1} ≤ g_k` — no longer a bare
assumption.  Composing with `rubricO4Restoration_of_coupling` yields

      rubricO4Restoration_of_AFCertificate :
        AFTrajectoryCertificate → RubricO4Restoration.

# Honest scope / what stays open

This does NOT discharge O(4) restoration.  It derives a physically motivated
scalar-decay witness from the certificate field
`recurrence` — the NAMED two-loop lattice-perturbation input (Lüscher–Weisz
shape) with its explicit cubic remainder constant `E`.  Inhabiting the certificate
with the true 4D interacting rotation-breaking coupling's remainder constant
remains a physics obligation for the scalar model.  Since the destination
predicate is independently trivially inhabitable, this is not a sharpening of
the Clay statement itself and supplies no observable covariance.

# Axiom-gate (AGENTS.md Rules 1, 8)

Pure `Q'` order/`eqv` arithmetic plus reuse of the proved `drop` lemma; every
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
All witnesses are `Type`-level data.
-/

import YMGap.Continuum.AFTrajectoryCertificate
import YMGap.Continuum.O4RestorationProgress
import YMGap.Continuum.O4RestorationH4

namespace YMGap.Continuum.O4H4Homomorphism

open YMGap.Constructive
open YMGap.Continuum

/-! ## 0. Small `Q'` order glue

Two elementary order facts and the trivial contraction bound `τ·(1 − c·τ) ≤ τ`. -/

/-- `-x ≤ 0` for `0 ≤ x` (cross-product form). -/
theorem neg_nonpos_of_nonneg {x : Q'} (h : (0 : Q') ≤ x) : -x ≤ (0 : Q') := by
  show (-x).num * ((0 : Q').den : Int) ≤ (0 : Q').num * ((-x).den : Int)
  have hh : (0 : Q').num * (x.den : Int) ≤ x.num * ((0 : Q').den : Int) := h
  have h0n : (0 : Q').num = 0 := rfl
  have h0d : ((0 : Q').den : Int) = 1 := rfl
  have hxn : (-x).num = -x.num := rfl
  have hxd : ((-x).den : Int) = (x.den : Int) := rfl
  rw [h0n, h0d] at hh
  rw [h0n, h0d, hxn, hxd]
  omega

/-- `1 − x ≤ 1` for `0 ≤ x`.  (`1 − x = 1 + −x ≤ 1 + 0 ≈ 1`.) -/
theorem one_sub_le_one {x : Q'} (h : (0 : Q') ≤ x) : (1 : Q') - x ≤ 1 := by
  have hneg : -x ≤ (0 : Q') := neg_nonpos_of_nonneg h
  have hstep : (1 : Q') + -x ≤ 1 + 0 := Q'.add_le_add_left 1 (-x) 0 hneg
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1)))

/-- **The trivial contraction bound.**  `a·(1 − c·a) ≤ a` for `a ≥ 0` and
`c·a ≥ 0`.  (`1 − c·a ≤ 1`, then multiply by `a ≥ 0`, then `a·1 ≈ a`.)  This is
the only glue between the certificate's contracting `drop` and downhill
monotonicity. -/
theorem mul_one_sub_le_self (a c : Q') (ha : (0 : Q') ≤ a) (hca : (0 : Q') ≤ c * a) :
    a * (1 - c * a) ≤ a := by
  have hle1 : (1 : Q') - c * a ≤ 1 := one_sub_le_one hca
  have hmul : a * (1 - c * a) ≤ a * 1 :=
    Q'.mul_le_mul_of_nonneg_left (1 - c * a) 1 a hle1 ha
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.mul_one_eqv a))

/-- The subtraction-free reconstruction tautology `a ≈ b + (a − b)`.
`b + (a + −b) ≈ b + (−b + a) ≈ (b + −b) + a ≈ 0 + a ≈ a`. -/
theorem reconstruct_eqv (a b : Q') : a.eqv (b + (a + -b)) := by
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left b (a + -b) (-b + a) (Q'.add_comm_eqv a (-b))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv b (-b) a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (b + -b) 0 a (Q'.add_neg_self_eqv b)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' a)

/-! ## 1. The bridge constructor — certificate ⇒ running coupling

The AF segment `g k := τ (k0 + k)` is a `CouplingRunning`: its per-step decrease
`δ_k := g k − g (k+1)` is nonnegative BECAUSE the certificate's contracting `drop`
gives `g (k+1) = τ (k0+k+1) ≤ τ (k0+k)·(1 − (β/2)·τ (k0+k)) ≤ τ (k0+k) = g k`
(the last step via `mul_one_sub_le_self`).  So `betaDrop_nonneg` — the bare AF
sign — is DERIVED from the named two-loop recurrence-with-remainder. -/

/-- **The bridge constructor.**  An `AFTrajectoryCertificate` yields a
`CouplingRunning` on its AF segment `g k := τ (k0 + k)`.  The residual sign
`betaDrop_nonneg` is the DERIVED downhill monotonicity `g (k+1) ≤ g k`, obtained
from the proved contracting `drop` chained through the trivial contraction bound
`mul_one_sub_le_self`. -/
def couplingRunning_of_AFCertificate
    (C : AFTrajectoryCertificate.AFTrajectoryCertificate) :
    O4RestorationProgress.CouplingRunning where
  g := fun k => C.τ (C.k0 + k)
  g_nonneg := fun k => Q'.le_of_lt (C.τ_pos (C.k0 + k))
  betaDrop := fun k => C.τ (C.k0 + k) - C.τ (C.k0 + k + 1)
  betaDrop_nonneg := fun k => by
    -- 0 ≤ g k − g (k+1)  ⟺  g (k+1) = τ (k0+k+1) ≤ τ (k0+k) = g k.
    have hτnn : (0 : Q') ≤ C.τ (C.k0 + k) := Q'.le_of_lt (C.τ_pos (C.k0 + k))
    have hca : (0 : Q') ≤ AFTrajectoryCertificate.halfBeta C.β * C.τ (C.k0 + k) :=
      Q'.mul_nonneg _ _ (AFTrajectoryCertificate.halfBeta_nonneg C.β_pos) hτnn
    have hdrop := AFTrajectoryCertificate.drop C (C.k0 + k) (Nat.le_add_right C.k0 k)
    have hself := mul_one_sub_le_self (C.τ (C.k0 + k))
      (AFTrajectoryCertificate.halfBeta C.β) hτnn hca
    have hle : C.τ (C.k0 + k + 1) ≤ C.τ (C.k0 + k) := Q'.le_trans' _ _ _ hdrop hself
    exact Q'.sub_nonneg_of_le hle
  run_step := fun k => reconstruct_eqv (C.τ (C.k0 + k)) (C.τ (C.k0 + k + 1))

/-! ## 2. The composition — certificate ⇒ the weak legacy slot

Composing the bridge with the downstream wiring
`rubricO4Restoration_of_coupling` fires the weak scalar slot from the two-loop
trajectory certificate.  This records provenance for one witness, but the slot
does not require that provenance and is not full O4 restoration. -/

/-- **The composition.**  The weak legacy slot fires from an
`AFTrajectoryCertificate`: the scalar content is the certificate's
`recurrence` (the named two-loop lattice-perturbation running with explicit cubic
remainder `E`), but no same-action observable covariance follows. -/
theorem rubricO4Restoration_of_AFCertificate
    (C : AFTrajectoryCertificate.AFTrajectoryCertificate) :
    YMGap.Rubric.ClayScorecard.RubricO4Restoration :=
  O4RestorationH4.rubricO4Restoration_of_coupling (couplingRunning_of_AFCertificate C)

end YMGap.Continuum.O4H4Homomorphism

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.O4H4Homomorphism.neg_nonpos_of_nonneg
#print axioms YMGap.Continuum.O4H4Homomorphism.one_sub_le_one
#print axioms YMGap.Continuum.O4H4Homomorphism.mul_one_sub_le_self
#print axioms YMGap.Continuum.O4H4Homomorphism.reconstruct_eqv
#print axioms YMGap.Continuum.O4H4Homomorphism.couplingRunning_of_AFCertificate
#print axioms YMGap.Continuum.O4H4Homomorphism.rubricO4Restoration_of_AFCertificate
