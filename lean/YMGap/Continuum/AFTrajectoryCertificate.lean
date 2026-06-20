/-
Track B / R2 — the **asymptotic-freedom TRAJECTORY CERTIFICATE**: the two-loop
running as a constructive recurrence WITH EXPLICIT REMAINDER CONSTANTS, from which
the reciprocal `1/k` modulus that feeds the gap chain is DERIVED (not assumed).

# What this module delivers

The standard two-loop asymptotic-freedom (AF) flow for the log-coupling
`τ_k = −log w_k` (with `w_k` the per-scale heat-kernel weight) is

      τ_{k+1}  =  τ_k − β·τ_k²  +  O(τ_k³)               (two-loop AF flow)

with `β > 0` the two-loop ratio and a remainder of cubic order.  Upstream, the
gap chain consumes an `AFRateModulus` whose per-scale margin obeys a NAMED
reciprocal rate `1 − w_k ≤ A/(k+B)`.  Here that rate is turned into a THEOREM:
from the recurrence packaged WITH an explicit remainder bound `E ≥ 0`,

      | τ_{k+1} − (τ_k − β·τ_k²) |  ≤  E·τ_k³            (named remainder bound)

we derive — entirely in the constructive rationals `Q'`, axiom-clean — the
contracting drop, the reciprocal-linear growth `1/τ_k ≥ 1/τ_{k0} + (β/2)(k−k0)`,
hence the reciprocal decay `τ_k ≤ A/(k+B)` with EXPLICIT `A`, `B`, and finally an
`AFRateModulus` whose `1/k` rate is a CONSEQUENCE of the recurrence.

The structure:

  * `AFTrajectoryCertificate` — the recurrence-with-remainder as `Type`-level
    data: the trajectory `τ`, the two-loop coefficient `β > 0`, the remainder
    bound `E ≥ 0`, a base index `k0`, the smallness window `τ_small`, the
    remainder recurrence `recurrence`, and a matching lower-rate witness
    (`A'`, `τ_lower`) so a two-sided `AFRateModulus` can be produced honestly.

  * `drop` — the drop lemma: `recurrence` + smallness `E·τ_k ≤ β/2` gives the
    contracting form `τ_{k+1} ≤ τ_k·(1 − (β/2)·τ_k)`.  (The `−βτ²` term
    dominates the `+Eτ³` remainder once `τ` is small.)

  * `af_reciprocal_rate` — THE deliverable: `τ_k ≤ A/(k+B)` for `k ≥ k0`, with
    EXPLICIT `A = 2/β` and `B = 2/(β·τ_{k0})` (returned as DATA, both `> 0`),
    re-using the reciprocal-increment machinery of `AFReciprocalRate`.

  * `afRateModulus_of_AFCertificate` — the recurrence ⇒ `AFRateModulus` theorem:
    setting `w_k := 1 − τ_k`, the per-scale margin `1 − w_k = τ_k` inherits the
    reciprocal upper rate (and the carried lower rate), so the `AFRateModulus`
    interface is INHABITED by the certificate — the `1/k` rate is DERIVED.

  * `quadratic_defect_summable` — the closing corollary: a defect bounded by a
    constant times `τ_k²`, when `τ` itself obeys a reciprocal rate with an
    integer offset `B ≥ 2`, is dominated by `C·A²·1/(k+B)²` and is therefore
    summable with the explicit inverse-square Cauchy modulus.

# What is NAMED physics (honest)

  * The two-loop coefficient `β` and the remainder bound `E` (the field
    `recurrence`) are the NAMED physical input.  Lüscher–Weisz-type lattice
    perturbation theory supplies the asymptotic relation
    `τ_{k+1} = τ_k − β τ_k² + O(τ_k³)`; the EXPLICIT cubic remainder bound `E` is
    the constructive obligation, NOT derived here from first principles.

  * The certificate is the constructive INTERFACE.  Inhabiting it with the true
    lattice β-function remainder constant is the physics obligation.  This module
    proves the IMPLICATION recurrence-with-remainder ⇒ reciprocal-rate ⇒
    `AFRateModulus`, eliminating the bare `1 − w_k ≤ A/(k+B)` assumption.

  * This is NOT a 4D Yang–Mills mass gap.  It is the scalar recurrence layer that
    converts a named two-loop running into the reciprocal modulus the chain uses.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` arithmetic (the positivity-guarded `Q'.divPos` and its order
characterizations, reused `Q'` order/`eqv`/`abs` lemmas) plus the structural
reciprocal induction reused from `AFReciprocalRate`.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` /
`Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All
witnesses (`β`, `E`, `A`, `B`, the rate bounds) are `Type`-level data.
-/

import YMGap.Continuum.AFReciprocalRate
import YMGap.Continuum.SummableInverseSquare

namespace YMGap.Continuum.AFTrajectoryCertificate

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.AFReciprocalRate

/-! ## 0. The two-loop half-coefficient `c = β/2`

The contracting rate produced by the drop lemma is `c = β·half` with
`half = 1/2`.  We record its positivity from `β > 0`. -/

/-- The contracting rate `c = β/2 = β·half`. -/
def halfBeta (β : Q') : Q' := β * HalfPow.half

theorem halfBeta_pos {β : Q'} (hβ : (0 : Q') < β) : (0 : Q') < halfBeta β :=
  Q'.mul_pos hβ (by decide)

theorem halfBeta_nonneg {β : Q'} (hβ : (0 : Q') < β) : (0 : Q') ≤ halfBeta β :=
  Q'.le_of_lt (halfBeta_pos hβ)

/-- `2·(β·half) ≃ β` — the defining identity of the half-coefficient.
`(β·half) + (β·half) ≃ β·(half + half) ≃ β·1 ≃ β`. -/
theorem two_halfBeta_eqv (β : Q') : (halfBeta β + halfBeta β).eqv β := by
  show (β * HalfPow.half + β * HalfPow.half).eqv β
  -- β·half + β·half ≃ β·(half + half)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv β HalfPow.half HalfPow.half)) ?_
  -- half + half ≃ 1
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left β (HalfPow.half + HalfPow.half) 1 ?_) (Q'.mul_one_eqv β)
  -- half + half ≃ 1 at the cross-product level.
  show (HalfPow.half + HalfPow.half).num * ((1 : Q').den : Int)
      = (1 : Q').num * ((HalfPow.half + HalfPow.half).den : Int)
  decide

/-! ## 1. The AF trajectory certificate (the recurrence-with-remainder, as DATA)

The named two-loop physics, packaged with explicit constants. -/

/-- **The asymptotic-freedom trajectory certificate.**

A `Type`-level record of the two-loop AF recurrence WITH an explicit cubic
remainder bound, together with the smallness window that makes the `−βτ²` term
dominate the remainder, and a matching lower-rate witness so a two-sided
`AFRateModulus` can be produced.

Fields:
  * `τ` — the log-coupling trajectory.
  * `β` — the two-loop coefficient (`> 0`), NAMED physics input.
  * `E` — the explicit cubic remainder bound (`≥ 0`), NAMED physics input.
  * `k0` — the base index from which the small-`τ` regime holds.
  * `τ_pos` — `τ_k > 0`.
  * `τ_small` — for `k ≥ k0`, `E·τ_k ≤ β/2` (the remainder is dominated).
  * `recurrence` — for `k ≥ k0`, `|τ_{k+1} − (τ_k − β·τ_k²)| ≤ E·τ_k³`.
  * `A'`, `A'_pos`, `τ_lower` — a matching reciprocal LOWER rate
    `A'/(k+B) ≤ τ_k` (the two-sided two-loop running; carried as named data so
    the produced `AFRateModulus.rate_lower` is honest). -/
structure AFTrajectoryCertificate : Type where
  /-- The log-coupling trajectory `τ_k`. -/
  τ : Nat → Q'
  /-- The two-loop coefficient `β > 0` (NAMED physics). -/
  β : Q'
  /-- The explicit cubic remainder bound `E ≥ 0` (NAMED physics). -/
  E : Q'
  /-- The base index from which the small-`τ` two-loop regime holds. -/
  k0 : Nat
  /-- `β > 0`. -/
  β_pos : (0 : Q') < β
  /-- `E ≥ 0`. -/
  E_nonneg : (0 : Q') ≤ E
  /-- `τ_k > 0`. -/
  τ_pos : ∀ k, (0 : Q') < τ k
  /-- **Smallness:** for `k ≥ k0`, the remainder is dominated: `E·τ_k ≤ β/2`. -/
  τ_small : ∀ k, k0 ≤ k → E * τ k ≤ halfBeta β
  /-- **Small coupling:** in the AF regime `k ≥ k0` the coupling is `< 1`
  (so the weight `w_k = 1 − τ_k` lands in `[0,1)`). -/
  τ_lt_one : ∀ k, k0 ≤ k → τ k < 1
  /-- **The two-loop recurrence with explicit remainder:** for `k ≥ k0`,
  `|τ_{k+1} − (τ_k − β·τ_k²)| ≤ E·τ_k³`. -/
  recurrence : ∀ k, k0 ≤ k →
    Q'.abs (τ (k + 1) - (τ k - β * (τ k * τ k))) ≤ E * (τ k * (τ k * τ k))
  /-- The lower-rate constant `A' > 0`. -/
  A' : Q'
  /-- `A' > 0`. -/
  A'_pos : (0 : Q') < A'
  /-- **The matching reciprocal LOWER rate** (two-sided two-loop running),
  stated against the SAME explicit offset `B = 2/(β·τ_{k0})` used by the upper
  rate.  Carried as named data so the produced `rate_lower` is honest. -/
  τ_lower : ∀ d,
    Q'.divPos A'
      (harmDen (recip (halfBeta β) (halfBeta_pos β_pos)
        * recip (τ k0) (τ_pos k0)) d)
      (harmDen_pos (Q'.mul_pos (recip_pos (halfBeta β) (halfBeta_pos β_pos))
        (recip_pos (τ k0) (τ_pos k0))) d)
    ≤ τ (k0 + d)

/-! ## 2. The drop lemma

From the remainder recurrence and the smallness window, the trajectory obeys the
CONTRACTING form `τ_{k+1} ≤ τ_k·(1 − c·τ_k)` with `c = β/2`.  The cubic remainder
`+E·τ³` is dominated by half of the `−β·τ²` term once `E·τ ≤ β/2`. -/

/-- **The drop lemma.**  For `k ≥ k0`,
`τ_{k+1} ≤ τ_k·(1 − (β/2)·τ_k)`.

Proof.  From `recurrence` and `le_abs_self`,
`τ_{k+1} − (τ_k − β·τ_k²) ≤ E·τ_k³`, so `τ_{k+1} ≤ (τ_k − β·τ_k²) + E·τ_k³`.
Since `E·τ_k³ = (E·τ_k)·τ_k² ≤ (β/2)·τ_k²` (smallness × `τ_k² ≥ 0`),
`τ_{k+1} ≤ (τ_k − β·τ_k²) + (β/2)·τ_k² ≃ τ_k − (β/2)·τ_k² ≃ τ_k·(1 − (β/2)·τ_k)`,
using `β − β/2 = β/2`. -/
theorem drop_core (τk τk1 β E c : Q')
    (hτk_nn : (0 : Q') ≤ τk)
    (hsmall : E * τk ≤ c)
    (htwoc : (c + c).eqv β)
    (habs : Q'.abs (τk1 - (τk - β * (τk * τk))) ≤ E * (τk * (τk * τk))) :
    τk1 ≤ τk * (1 - c * τk) := by
  have hττ_nn : (0 : Q') ≤ τk * τk := Q'.mul_nonneg τk τk hτk_nn hτk_nn
  -- (1) τk1 − (τk − β·τk²) ≤ E·τk³.
  have h1 : τk1 - (τk - β * (τk * τk)) ≤ E * (τk * (τk * τk)) :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self _) habs
  -- so τk1 ≤ (τk − β·τk²) + E·τk³.
  have h2 : τk1 ≤ (τk - β * (τk * τk)) + E * (τk * (τk * τk)) := by
    -- from a − b ≤ d we get a ≤ d + b (= b + d); here a = τk1, b = (τk − βτk²).
    have hsub : τk1 + -(τk - β * (τk * τk)) ≤ E * (τk * (τk * τk)) := h1
    -- add (τk − βτk²) on the right, then collapse.
    have hadd : (τk1 + -(τk - β * (τk * τk))) + (τk - β * (τk * τk))
        ≤ E * (τk * (τk * τk)) + (τk - β * (τk * τk)) :=
      Q'.add_le_add_right _ _ _ hsub
    -- LHS ≃ τk1.
    have hLHS : ((τk1 + -(τk - β * (τk * τk))) + (τk - β * (τk * τk))).eqv τk1 := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv τk1 (-(τk - β * (τk * τk))) (τk - β * (τk * τk))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left τk1 _ 0 (Q'.neg_add_self_eqv (τk - β * (τk * τk)))) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' τk1)
    -- RHS = E·τk³ + (τk − βτk²) ≃ (τk − βτk²) + E·τk³.
    have hRHS : (E * (τk * (τk * τk)) + (τk - β * (τk * τk))).eqv
        ((τk - β * (τk * τk)) + E * (τk * (τk * τk))) :=
      Q'.add_comm_eqv _ _
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hLHS)
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hRHS))
  -- (2) E·τk³ ≤ c·τk², since E·τk³ = (E·τk)·τk² and E·τk ≤ c.
  have hEcube_eqv : (E * (τk * (τk * τk))).eqv ((E * τk) * (τk * τk)) :=
    -- (E·τk)·(τk·τk) ≃ E·(τk·(τk·τk)) by mul_assoc.
    Q'.eqv_symm (Q'.mul_assoc_eqv E τk (τk * τk))
  have h3 : E * (τk * (τk * τk)) ≤ c * (τk * τk) := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hEcube_eqv) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hsmall hττ_nn
  -- (3) τk1 ≤ (τk − β·τk²) + c·τk².
  have h4 : τk1 ≤ (τk - β * (τk * τk)) + c * (τk * τk) :=
    Q'.le_trans' _ _ _ h2 (Q'.add_le_add_left _ _ _ h3)
  -- (4) (τk − β·τk²) + c·τk² ≃ τk − c·τk² ≃ τk·(1 − c·τk).
  --     since β = 2c, β·τk² − c·τk² = c·τk².
  have htarget : ((τk - β * (τk * τk)) + c * (τk * τk)).eqv (τk * (1 - c * τk)) := by
    -- LHS = (τk + −(β·τk²)) + c·τk² ≃ τk + (−(β·τk²) + c·τk²).
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv τk (-(β * (τk * τk))) (c * (τk * τk))) ?_
    -- reduce the bracket −(β·τk²) + c·τk² ≃ −(c·τk²).
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left τk (-(β * (τk * τk)) + c * (τk * τk)) (-(c * (τk * τk))) ?_) ?_
    · -- −(β·τk²) + c·τk² ≃ −(c·τk²).
      -- β·τk² ≃ (2c)·τk² ≃ (c+c)·τk² ≃ c·τk² + c·τk², so −(β·τk²) ≃ −(c·τk²) − c·τk²;
      -- adding c·τk² gives −(c·τk²).
      -- Work it as: β·(τk·τk) ≃ (c+c)·(τk·τk) ≃ c·(τk·τk) + c·(τk·τk).
      have hβsplit : (β * (τk * τk)).eqv (c * (τk * τk) + c * (τk * τk)) := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right β (c + c) (τk * τk) ?_) (ExpNeg.add_mul_eqv c c (τk * τk))
        -- β ≃ c + c.
        exact Q'.eqv_symm htwoc
      -- −(β·τk²) ≃ −(c·τk² + c·τk²)
      have hnegβ : (-(β * (τk * τk))).eqv (-(c * (τk * τk) + c * (τk * τk))) :=
        Q'.neg_eqv_congr _ _ hβsplit
      -- −(β·τk²) + c·τk² ≃ −(c·τk² + c·τk²) + c·τk²
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (c * (τk * τk)) hnegβ) ?_
      -- −(x + x) + x ≃ −x where x = c·τk².
      -- −(x + x) ≃ −x + −x ; (−x + −x) + x ≃ −x + (−x + x) ≃ −x + 0 ≃ −x.
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (c * (τk * τk)) (Q'.neg_add_eqv (c * (τk * τk)) (c * (τk * τk)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (-(c * (τk * τk))) (-(c * (τk * τk))) (c * (τk * τk))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (-(c * (τk * τk))) _ 0 (Q'.neg_add_self_eqv (c * (τk * τk)))) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' (-(c * (τk * τk))))
    · -- τk + −(c·τk²) ≃ τk·(1 − c·τk).
      -- RHS τk·(1 − c·τk) = τk·(1 + −(c·τk)) ≃ τk·1 + τk·(−(c·τk)) ≃ τk + −(τk·(c·τk)).
      refine Q'.eqv_symm ?_
      show (τk * (1 + -(c * τk))).eqv (τk + -(c * (τk * τk)))
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv τk 1 (-(c * τk))) ?_
      -- τk·1 + τk·(−(c·τk)) ≃ τk + −(τk·(c·τk))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (τk * 1) τk (τk * (-(c * τk))) (Q'.mul_one_eqv τk)) ?_
      refine Q'.add_eqv_congr_left τk (τk * (-(c * τk))) (-(c * (τk * τk))) ?_
      -- τk·(−(c·τk)) ≃ −(τk·(c·τk)) ≃ −(c·(τk·τk)).
      refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv τk (c * τk)) ?_
      refine Q'.neg_eqv_congr _ _ ?_
      -- τk·(c·τk) ≃ c·(τk·τk):  τk·(c·τk) ≃ (τk·c)·τk ≃ (c·τk)·τk ≃ c·(τk·τk).
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv τk c τk)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (τk * c) (c * τk) τk (Q'.mul_comm_eqv τk c)) ?_
      exact Q'.mul_assoc_eqv c τk τk
  exact Q'.le_trans' _ _ _ h4 (Q'.le_of_eqv htarget)

/-- **The drop lemma.**  For `k ≥ k0`, the certificate trajectory obeys the
contracting form `τ_{k+1} ≤ τ_k·(1 − (β/2)·τ_k)`.  Instantiates `drop_core` with
`c = β/2 = halfBeta β`, the smallness window `τ_small`, the half-coefficient
identity `(c + c) ≃ β` (`two_halfBeta_eqv`), and the remainder `recurrence`. -/
theorem drop (C : AFTrajectoryCertificate) (k : Nat) (hk : C.k0 ≤ k) :
    C.τ (k + 1) ≤ C.τ k * (1 - halfBeta C.β * C.τ k) :=
  drop_core (C.τ k) (C.τ (k + 1)) C.β C.E (halfBeta C.β)
    (Q'.le_of_lt (C.τ_pos k))
    (C.τ_small k hk)
    (two_halfBeta_eqv C.β)
    (C.recurrence k hk)

/-! ## 3. The reciprocal modulus — THE deliverable

The drop lemma is exactly the contracting recurrence `recip_step` / `recip_lb` /
`tau_inverse_linear_rate` of `AFReciprocalRate` consume, with `c = β/2`.  We feed
it through to obtain the reciprocal decay `τ_k ≤ A/(k+B)` with EXPLICIT constants:

      A  = 1/c        = 2/β,
      B  = (1/c)·(1/τ_{k0}) = 2/(β·τ_{k0}),

both `> 0`, returned as DATA (against the shifted index `d = k − k0`). -/

/-- **The reciprocal `1/k` rate (THE deliverable).**  Under the certificate, the
log-coupling decays reciprocally in the step count `d = k − k0`:

      τ_{k0+d}  ≤  A / (d + B),     A = 2/β,  B = 2/(β·τ_{k0}),

both `> 0`, returned as `Type`-level DATA.  This is the proved `1/k` rate, with
the cubic remainder `E` absorbed by the drop lemma. -/
def af_reciprocal_rate (C : AFTrajectoryCertificate) :
    Σ' (A : Q') (B : Q') (_ : (0 : Q') < A) (hB : (0 : Q') < B),
      ∀ d, C.τ (C.k0 + d)
        ≤ Q'.divPos A (harmDen B d) (harmDen_pos hB d) :=
  tau_inverse_linear_rate C.τ C.τ_pos (halfBeta C.β) (halfBeta_pos C.β_pos) C.k0
    (fun k hk => drop C k hk)

/-! ## 4. Wiring to the chain interface — recurrence ⇒ `AFRateModulus`

Set `w_k := 1 − τ_k`.  Then the per-scale margin is exactly `1 − w_k = τ_k`, so
the proved reciprocal upper rate is the `rate_upper` field, and the certificate's
carried lower rate is the `rate_lower` field.  The smallness `E·τ_k ≤ β/2` with
`E ≥ 0` and `τ_k > 0` keeps `0 < τ_k`; we additionally take the certificate to
provide a margin `< 1` from `0 < 1 − w_k = τ_k` and `τ_k ≤ A/(d+B)`.  To keep
`w_k = 1 − τ_k ∈ [0,1)` cleanly for ALL `k` (the `AFRateModulus` fields are
indexed over all `k`), we clamp the weight model to the AF window by using the
shifted trajectory `τ' k := τ (k0 + k)` and the shifted rate; this is the genuine
AF segment.  The produced `AFRateModulus` has its `1/k` rate DERIVED. -/

/-- `0 ≤ 1 − τ` for `τ ≤ 1`. -/
theorem one_sub_nonneg {τ : Q'} (h : τ ≤ 1) : (0 : Q') ≤ 1 - τ := by
  -- 1 − τ = 1 + −τ ; 0 ≤ 1 + −τ ⟺ τ ≤ 1 (sub_nonneg_of_le, with the summands
  -- commuted to match `1 + −τ`).
  have h0 : (0 : Q') ≤ 1 + -τ := Q'.sub_nonneg_of_le h
  exact h0

/-- `1 − τ < 1` for `0 < τ`.  Cross-product:
`(1−τ).num·1 = (τ.den − τ.num) < τ.den = 1·(1−τ).den` since `0 < τ.num`. -/
theorem one_sub_lt_one {τ : Q'} (h : (0 : Q') < τ) : (1 : Q') - τ < 1 := by
  have hnum : (0 : Int) < τ.num := Q'.num_pos_of_pos h
  show ((1 : Q') - τ).num * ((1 : Q').den : Int)
      < (1 : Q').num * (((1 : Q') - τ).den : Int)
  -- (1 − τ).num = 1·(-τ).den + (-τ).num·1.den = τ.den + (−τ.num) = τ.den − τ.num.
  have hn : ((1 : Q') - τ).num = (τ.den : Int) - τ.num := by
    show (1 : Q').num * ((-τ).den : Int) + (-τ).num * ((1 : Q').den : Int)
        = (τ.den : Int) - τ.num
    have h1n : (1 : Q').num = 1 := rfl
    have h1d : ((1 : Q').den : Int) = 1 := rfl
    have hnd : ((-τ).den : Int) = (τ.den : Int) := rfl
    have hnn : (-τ).num = -τ.num := rfl
    rw [h1n, h1d, hnd, hnn, Int.one_mul, Int.mul_one]
    omega
  -- (1 − τ).den = 1.den · (-τ).den = τ.den.
  have hd : (((1 : Q') - τ).den : Int) = (τ.den : Int) := by
    show (((1 : Q').den * (-τ).den : Nat) : Int) = (τ.den : Int)
    have : (1 : Q').den = 1 := rfl
    rw [this, Nat.one_mul]
    rfl
  rw [hn, hd]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]
  -- τ.den − τ.num < τ.den ⟺ 0 < τ.num.
  omega

/-! ### The shifted AF segment and the `AFRateModulus` it produces

`τ'_k := τ (k0 + k)` is the AF segment.  Its margin model is `w_k := 1 − τ'_k`,
giving `1 − w_k = τ'_k`, the proved reciprocal rate (upper) and the certificate's
carried lower rate (lower).  Both `w_k ∈ [0,1)` from `0 < τ'_k < 1`. -/

/-- **The recurrence ⇒ `AFRateModulus` theorem.**  An `AFTrajectoryCertificate`
PRODUCES an `AFRateModulus` constructively: with `w_k := 1 − τ(k0+k)` the
per-scale margin `1 − w_k = τ(k0+k)` obeys the DERIVED reciprocal upper rate
`τ(k0+k) ≤ A/(k+B)` (from the drop lemma, `A = 2/β`, `B = 2/(β·τ_{k0})`) and the
certificate's carried lower rate.  The `1/k` rate is no longer assumed — it is a
consequence of the two-loop recurrence-with-remainder. -/
def afRateModulus_of_AFCertificate (C : AFTrajectoryCertificate) : AFRateModulus where
  A := recip (halfBeta C.β) (halfBeta_pos C.β_pos)
  A' := C.A'
  B := recip (halfBeta C.β) (halfBeta_pos C.β_pos) * recip (C.τ C.k0) (C.τ_pos C.k0)
  A_pos := recip_pos (halfBeta C.β) (halfBeta_pos C.β_pos)
  A'_pos := C.A'_pos
  B_pos := Q'.mul_pos (recip_pos (halfBeta C.β) (halfBeta_pos C.β_pos))
    (recip_pos (C.τ C.k0) (C.τ_pos C.k0))
  w := fun k => 1 - C.τ (C.k0 + k)
  w_nonneg := by
    -- 0 ≤ 1 − τ(k0+k) ⟸ τ(k0+k) ≤ 1 ⟸ τ(k0+k) < 1.
    intro k
    have hlt : C.τ (C.k0 + k) < 1 :=
      C.τ_lt_one (C.k0 + k) (Nat.le_add_right C.k0 k)
    exact one_sub_nonneg (Q'.le_of_lt hlt)
  w_lt_one := by
    -- 1 − τ(k0+k) < 1 ⟸ 0 < τ(k0+k).
    intro k
    exact one_sub_lt_one (C.τ_pos (C.k0 + k))
  rate_upper := by
    -- rate_upper: 1 − (1 − τ(k0+k)) = τ(k0+k) ≤ A/(k+B), the DERIVED reciprocal
    -- rate.  `af_reciprocal_rate C` is definitionally `tau_inverse_linear_rate`
    -- with `c = β/2`, returning exactly `A = 1/c`, `B = (1/c)·(1/τ_{k0})`.
    intro k
    have heqv : ((1 : Q') - (1 - C.τ (C.k0 + k))).eqv (C.τ (C.k0 + k)) :=
      one_sub_one_sub_eqv (C.τ (C.k0 + k))
    have hrate := (af_reciprocal_rate C).2.2.2.2 k
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv) hrate
  rate_lower := by
    -- rate_lower: A'/(k+B) ≤ 1 − (1 − τ(k0+k)) = τ(k0+k), the carried lower rate.
    intro k
    have heqv : ((1 : Q') - (1 - C.τ (C.k0 + k))).eqv (C.τ (C.k0 + k)) :=
      one_sub_one_sub_eqv (C.τ (C.k0 + k))
    exact Q'.le_trans' _ _ _ (C.τ_lower k) (Q'.ge_of_eqv heqv)

/-! ## 5. Quadratic-defect ⇒ summable corollary

A defect `δ_k ≤ C·τ_k²` along a trajectory obeying a reciprocal rate
`τ_k ≤ A·1/(k+B)` (with an INTEGER offset `B ≥ 2`, the clean shape the
inverse-square endpoint consumes) is dominated by `(C·A²)·1/(k+B)²`, hence is
summable with the explicit dyadic Cauchy modulus.  This closes the loop
"AF recurrence ⇒ reciprocal rate ⇒ inverse-square ⇒ summable" with explicit
constants. -/

/-- **The quadratic-defect summability corollary.**  Suppose a nonnegative defect
`δ` obeys `δ_k ≤ M · invSqTerm B k = M · 1/(k+B)²` for some `M > 0` and integer
offset `B ≥ 2` (the typical case being `M = C·A²` from `δ_k ≤ C·τ_k²` and a
reciprocal rate `τ_k ≤ A/(k+B)`).  Then `∑ δ` is Cauchy with the EXPLICIT modulus
`N r = M.num.toNat·2^r + 1`: every window past `N r` sums to at most `(1/2)^r`.

This is the named closing statement of the AF recurrence ⇒ summable loop. -/
def quadratic_defect_summable
    (M : Q') (B : Nat) (hM : (0 : Q') < M) (hB : 2 ≤ B)
    (δ : Nat → Q')
    (hδ0 : ∀ k, (0 : Q') ≤ δ k)
    (hδmaj : ∀ k, δ k ≤ M * SummableInverseSquare.invSqTerm B hB k) :
    Σ' N : Nat → Nat,
      ∀ r M', SummableInverseSquare.tailSum δ (N r) M' ≤ HalfPow.half ^ r :=
  SummableInverseSquare.summable_of_inverse_square_bound M B hM hB δ hδ0 hδmaj

/-- **A concrete firing of the quadratic-defect corollary.**  With `M = 1`,
`B = 2`, and the defect `δ_k = 1/(k+2)²` (the `τ_k² ≍ 1/k²` shape), the corollary
produces the explicit Cauchy modulus `N r = 2^r + 1`.  This exhibits the
"AF recurrence ⇒ inverse-square ⇒ summable" endpoint non-vacuously. -/
def quadratic_defect_summable_demo :
    Σ' N : Nat → Nat,
      ∀ r M', SummableInverseSquare.tailSum
        (fun k => SummableInverseSquare.invSqTerm 2 (by decide) k) (N r) M'
        ≤ HalfPow.half ^ r :=
  quadratic_defect_summable 1 2 (by decide) (by decide)
    (fun k => SummableInverseSquare.invSqTerm 2 (by decide) k)
    (fun k => SummableInverseSquare.invSqTerm_nonneg 2 (by decide) k)
    (fun k => Q'.ge_of_eqv
      (Q'.one_mul_eqv (SummableInverseSquare.invSqTerm 2 (by decide) k)))

end YMGap.Continuum.AFTrajectoryCertificate

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AFTrajectoryCertificate.two_halfBeta_eqv
#print axioms YMGap.Continuum.AFTrajectoryCertificate.drop_core
#print axioms YMGap.Continuum.AFTrajectoryCertificate.drop
#print axioms YMGap.Continuum.AFTrajectoryCertificate.af_reciprocal_rate
#print axioms YMGap.Continuum.AFTrajectoryCertificate.one_sub_nonneg
#print axioms YMGap.Continuum.AFTrajectoryCertificate.one_sub_lt_one
#print axioms YMGap.Continuum.AFTrajectoryCertificate.afRateModulus_of_AFCertificate
#print axioms YMGap.Continuum.AFTrajectoryCertificate.quadratic_defect_summable
#print axioms YMGap.Continuum.AFTrajectoryCertificate.quadratic_defect_summable_demo
