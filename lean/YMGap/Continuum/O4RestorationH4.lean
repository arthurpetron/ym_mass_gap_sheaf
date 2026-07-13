/-
Track B+RepTheory / R2 — **strengthening the scalar anisotropy precursor from
Cauchy-convergence to genuine decay-to-zero, and wiring it to the weak legacy
scorecard slot.**

# The wiring hole this module closes

The asymptotic-freedom (AF) decay pipeline terminates in
`O4RestorationAF.RotationRestored`, a **Cauchy-convergence** statement: for every
`ε` there is `N` past which any two AF-step coefficients agree within `ε`.  But a
Cauchy sequence need not tend to `0`.  The historical
`RubricO4Restoration` slot asks for an existential scalar below every tolerance,
yet does not pin a schedule or action.  This module supplies the genuine
`breakCoeff` schedule to that weak slot while separately proving its strict
zero-decay content.

The stronger fact is ALREADY implicit in the pipeline: the geometric envelope
`breakCoeff_le_geo : breakCoeff k ≤ breakCoeff 0 · (1/2)^k` together with the
explicit Archimedean modulus `HalfPow.pow_half_le : (1/2)^δ.den ≤ δ` give decay to
`0` directly — the → 0 content was thrown away, used only for Cauchy-ness.

# What this module PROVES (all `[propext]` / `[propext, Quot.sound]` only)

  * `breakCoeff_le_offset` / `breakCoeff_le_of_le` — the AF coefficient is
    antitone across any number of blocking steps: `N ≤ k ⟹ breakCoeff k ≤
    breakCoeff N` (chained from the proved single-step `breakCoeff_antitone`).
  * `breakCoeff_vanishes` — **the strengthening**: from the geometric envelope plus
    the Archimedean half-power modulus, the AF coefficient decays BELOW every
    tolerance, `∀ ε>0, ∃ N, ∀ k≥N, breakCoeff k < ε` (a genuine limit `= 0`, with
    strict `<`, not mere Cauchy-ness).  The strictness comes from the `+1` rescaling
    `δ = ε/(breakCoeff 0 + 1)` (same pattern as `decay_modulus`).
  * `rubricO4Restoration_of_decay` — **legacy wiring**: instantiates the weak
    slot `RubricO4Restoration` with `defect := breakCoeff D` and `base :=
    breakCoeff D 0 + 1`.  This is the first term that connects the AF-decay pipeline
    to that legacy scorecard slot.
  * `rubricO4Restoration_of_flow` / `rubricO4Restoration_of_coupling` — the same
    wiring routed through a `DimensionlessFlow` / `CouplingRunning`, so the clause
    fires from the RG-flow data (the physical content being the AF monotonicity /
    beta-sign).
  * `rubricO4Restoration_geoFlow` — a non-vacuity capstone: the wired clause fires
    on the concrete STRICTLY-decreasing inhabitant `geoFlow`.

# Honest scope / what stays open (the frontier is UNCHANGED)

The geometric / `a²` decay is legitimate only under the Gaussian-UV /
asymptotic-freedom hypothesis: spin-4 anisotropy can be marginal/relevant at a
non-trivial IR fixed point (Hasenbusch–Vicari, arXiv 1108.0491).  The decay `shape`
`scale_step` / the beta-sign `betaDrop_nonneg` are justified by the dim-6,
`O(a²)`-coefficient, loop-stable leading rotation-breaking operator
(Davoudi–Savage, arXiv 1204.4146; the `d + 2 = 6` dimension-counting backbone), but
this is the JUSTIFICATION for the shape, NOT a proof.  Therefore the single
genuinely-open physical residual remains the asymptotic-freedom beta-function SIGN
`O4RestorationProgress.CouplingRunning.betaDrop_nonneg` (`β ≤ 0`) on the TRUE 4D
interacting rotation-breaking coupling; it is NOT discharged here.  Even after
that scalar sign is supplied, full O4 restoration still requires a physical
observable action and a uniform response bound on the same continuum functional.

Note also (honesty): the scorecard clause `RubricO4Restoration` is stated with an
EXISTENTIAL `∃ defect` inside `∀ k`, so it is weakly-constraining — the point of
this module is to supply the GENUINE AF coefficient `breakCoeff` as that defect (not
a vacuous placeholder), thereby making the connection to the real decay content
`breakCoeff_vanishes` explicit.  `geoFlow` is a MODEL inhabitant of the beta-sign
residual, not the physical interacting theory.

# The alternative (H4 *-homomorphism interface)

The genuinely-new open content of the discrete-carrier route is a non-trivial
`H₄` action on a genuine associative SU(2) observable algebra.  The legacy
`charAlg` only has a nonassociative lowest-channel operation;
`CarrierPrecursors` carries only the identity-rotation witness
`o4_restoration_on_charAlg` plus the
boundary `heatKernel_not_equivariant_under_collapse`.  Its ANALYTIC half —
"coefficients on the defect subspace vanish as `a → 0`" — is exactly
`breakCoeff_vanishes` here.  That route still needs the associative fusion-sum
carrier, its discrete non-trivial action, and the same `betaDrop_nonneg`.

# Axiom-gate (AGENTS.md Rules 1, 8)

Pure `Q'` arithmetic reusing the proved envelope / Archimedean modulus and two
small local order helpers (`q_lt_add_of_pos_right`, `lt_of_lt_of_le`, copied at the
`Int` cross-product level to avoid extra imports).  Every load-bearing declaration
is gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.
No `Classical.*`, no `native_decide`, no `sorry`, no `Prop := True` stub.  All
witnesses are `Type`-level data.
-/

import YMGap.Continuum.O4RestorationAF
import YMGap.Continuum.O4RestorationProgress
import YMGap.Rubric.ClayScorecard

namespace YMGap.Continuum.O4RestorationH4

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.O4RestorationAF

/-! ## 0. Two small `Q'` order helpers (local copies, `Int` cross-product level)

`q_lt_add_of_pos_right` (`a < a + b` for `0 < b`) supplies the strictness of the
decay-to-zero, and `lt_of_lt_of_le` chains a strict `<` through a following `≤`.
Both are proved at the `Int` cross-product representation, mirroring the existing
copies elsewhere in the development, to avoid pulling extra imports. -/

/-- `0 < b → a < a + b` on `Q'` (strict self-grows-under-positive-add). -/
theorem q_lt_add_of_pos_right (a b : Q') (hb : (0 : Q') < b) : a < a + b := by
  show a.num * ((a + b).den : Int) < (a + b).num * (a.den : Int)
  have hbnum : (0 : Int) < b.num := Q'.num_pos_of_pos hb
  show a.num * ((a.den * b.den : Nat) : Int)
      < (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.den : Int)
  have hcast : ((a.den * b.den : Nat) : Int) = (a.den : Int) * (b.den : Int) :=
    Int.natCast_mul a.den b.den
  rw [hcast]
  have hadenpos : (0 : Int) < (a.den : Int) := by exact_mod_cast a.den_pos
  have hexpand : (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.den : Int)
      = a.num * ((a.den : Int) * (b.den : Int))
        + b.num * (a.den : Int) * (a.den : Int) := by
    rw [Int.add_mul]
    have e1 : a.num * (b.den : Int) * (a.den : Int)
        = a.num * ((a.den : Int) * (b.den : Int)) := by
      rw [Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [e1]
  rw [hexpand]
  have key : (0 : Int) < b.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_pos (Int.mul_pos hbnum hadenpos) hadenpos
  omega

/-- `a < b → b ≤ c → a < c` on `Q'` (strict-then-nonstrict chaining). -/
theorem lt_of_lt_of_le {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hcd : (0 : Int) < (c.den : Int) := by exact_mod_cast c.den_pos
  have had : (0 : Int) ≤ (a.den : Int) := by exact_mod_cast Nat.zero_le _
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_lt_mul_of_pos_right e1 hcd
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_left e2 had
    have hl : (a.den : Int) * (b.num * (c.den : Int))
            = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_comm b.num (a.den : Int), Int.mul_assoc]
    have hrr : (a.den : Int) * (c.num * (b.den : Int))
             = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_comm c.num (a.den : Int), Int.mul_assoc]
    rwa [hl, hrr] at this
  have schain : (a.num * (c.den : Int)) * (b.den : Int)
              < (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_lt_of_le s1 s2
  exact Int.lt_of_mul_lt_mul_right schain (by exact_mod_cast Nat.zero_le _)

/-! ## 1. Multi-step antitonicity of the AF coefficient

The proved single-step `breakCoeff_antitone` chains into: the coefficient does not
increase across ANY number of blocking steps. -/

/-- `breakCoeff (N + j) ≤ breakCoeff N` — antitonicity across `j` blocking steps
(induction on the offset `j`, chaining the single-step decay). -/
theorem breakCoeff_le_offset (D : ScalingDimensionDecay) (N : Nat) :
    ∀ j : Nat, breakCoeff D (N + j) ≤ breakCoeff D N
  | 0 => Q'.le_refl' (breakCoeff D N)
  | j + 1 =>
      Q'.le_trans' _ _ _ (breakCoeff_antitone D (N + j)) (breakCoeff_le_offset D N j)

/-- `N ≤ k → breakCoeff k ≤ breakCoeff N` — the AF coefficient is antitone. -/
theorem breakCoeff_le_of_le (D : ScalingDimensionDecay) {N k : Nat} (h : N ≤ k) :
    breakCoeff D k ≤ breakCoeff D N := by
  obtain ⟨j, hj⟩ := Nat.le.dest h
  subst hj
  exact breakCoeff_le_offset D N j

/-! ## 2. A positive baseline for the coefficient -/

/-- `0 < breakCoeff D 0 + 1` — a strictly-positive baseline (the `+1` guarantees
positivity even at the Gaussian fixed point where `breakCoeff 0 = 0`). -/
theorem breakCoeff_zero_add_one_pos (D : ScalingDimensionDecay) :
    (0 : Q') < breakCoeff D 0 + 1 := by
  have hCnn : (0 : Q') ≤ breakCoeff D 0 := breakCoeff_nonneg D 0
  have h1le : (1 : Q') ≤ breakCoeff D 0 + 1 := by
    have h := Q'.add_le_add_right 0 (breakCoeff D 0) 1 hCnn
    rwa [Q'.zero_add'] at h
  exact Q'.pos_of_lt_of_le (by decide) h1le

/-! ## 3. THE STRENGTHENING — decay below every tolerance (limit = 0)

From the geometric envelope `breakCoeff k ≤ breakCoeff 0 · (1/2)^k` and the
explicit Archimedean modulus `(1/2)^δ.den ≤ δ`, the coefficient drops below every
positive `ε` (a genuine limit `= 0`, with a STRICT `<`), not merely Cauchy. -/

/-- **The strengthening (limit = 0).**  For every positive `ε` there is a step `N`
past which the AF rotation-breaking coefficient is strictly below `ε`:
`∀ ε>0, ∃ N, ∀ k≥N, breakCoeff k < ε`.  The modulus is `N := (ε/(breakCoeff 0 +
1)).den`; the `+1` rescaling supplies the strictness. -/
theorem breakCoeff_vanishes (D : ScalingDimensionDecay) :
    ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ k : Nat, N ≤ k →
      breakCoeff D k < ε := by
  intro ε hε
  have hCnn : (0 : Q') ≤ breakCoeff D 0 := breakCoeff_nonneg D 0
  have hC1pos : (0 : Q') < breakCoeff D 0 + 1 := breakCoeff_zero_add_one_pos D
  let δ : Q' := Q'.divPos ε (breakCoeff D 0 + 1) hC1pos
  have hδpos : (0 : Q') < δ := Q'.divPos_pos ε (breakCoeff D 0 + 1) hC1pos hε
  refine ⟨δ.den, fun k hk => ?_⟩
  -- ≤ chain: breakCoeff k ≤ breakCoeff δ.den ≤ breakCoeff 0 · (1/2)^δ.den
  --          ≤ breakCoeff 0 · δ
  have hkN : breakCoeff D k ≤ breakCoeff D δ.den := breakCoeff_le_of_le D hk
  have hgeo : breakCoeff D δ.den ≤ breakCoeff D 0 * half ^ δ.den :=
    breakCoeff_le_geo D δ.den
  have hpow : half ^ δ.den ≤ δ := HalfPow.pow_half_le δ hδpos
  have hCmul : breakCoeff D 0 * half ^ δ.den ≤ breakCoeff D 0 * δ :=
    Q'.mul_le_mul_of_nonneg_left (half ^ δ.den) δ (breakCoeff D 0) hpow hCnn
  have hchain : breakCoeff D k ≤ breakCoeff D 0 * δ :=
    Q'.le_trans' _ _ _ hkN (Q'.le_trans' _ _ _ hgeo hCmul)
  -- strict: breakCoeff 0 · δ < ε  (via (breakCoeff 0)·δ + δ ≈ (breakCoeff 0 + 1)·δ ≈ ε)
  have hstrict : breakCoeff D 0 * δ < ε := by
    have heqv1 : (δ * (breakCoeff D 0 + 1)).eqv ε :=
      Q'.divPos_mul_eqv ε (breakCoeff D 0 + 1) hC1pos
    have heqv2 : (δ * (breakCoeff D 0 + 1)).eqv (δ * breakCoeff D 0 + δ) :=
      Q'.eqv_trans _ _ _ (Q'.mul_add_eqv δ (breakCoeff D 0) 1)
        (Q'.add_eqv_congr_left (δ * breakCoeff D 0) (δ * 1) δ (Q'.mul_one_eqv δ))
    have heqv3 : (δ * breakCoeff D 0 + δ).eqv ε :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm heqv2) heqv1
    have hlt : δ * breakCoeff D 0 < δ * breakCoeff D 0 + δ :=
      q_lt_add_of_pos_right (δ * breakCoeff D 0) δ hδpos
    have hlt2 : δ * breakCoeff D 0 < ε := lt_of_lt_of_le hlt (Q'.le_of_eqv heqv3)
    exact Q'.lt_of_le_of_lt (Q'.le_of_eqv (Q'.mul_comm_eqv (breakCoeff D 0) δ)) hlt2
  exact Q'.lt_of_le_of_lt hchain hstrict

/-! ## 4. Legacy wiring — inhabiting the weak scorecard slot

Instantiate `RubricO4Restoration` with the GENUINE AF coefficient `breakCoeff D` as
the rotational-anisotropy defect, and `breakCoeff D 0 + 1` as the positive baseline.
The `defect k < ε` is the strengthening `breakCoeff_vanishes`; `0 ≤ defect k` is
`breakCoeff_nonneg`; the baseline is positive by `breakCoeff_zero_add_one_pos` and
bounds `defect k` via multi-step antitonicity down from step `0`. -/

/-- **Legacy wiring.**  The weak scorecard slot `RubricO4Restoration` is inhabited
using `defect := breakCoeff D` (the derived AF rotation-breaking coefficient).
The strictness `defect k < ε` is the decay-to-zero `breakCoeff_vanishes`, upgrading
the Cauchy-only `RotationRestored`. -/
theorem rubricO4Restoration_of_decay (D : ScalingDimensionDecay) :
    YMGap.Rubric.ClayScorecard.RubricO4Restoration := by
  intro ε hε
  obtain ⟨N, hN⟩ := breakCoeff_vanishes D ε hε
  refine ⟨N, fun k hk => ?_⟩
  refine ⟨breakCoeff D, hN k hk, breakCoeff_nonneg D k,
    breakCoeff D 0 + 1, breakCoeff_zero_add_one_pos D, ?_⟩
  -- defect k = breakCoeff k ≤ breakCoeff 0 ≤ breakCoeff 0 + 1
  exact Q'.le_trans' _ _ _ (breakCoeff_le_of_le D (Nat.zero_le k))
    (Q'.add_le_self_of_nonneg (breakCoeff D 0) 1 (by decide))

/-- **The wiring routed through a `DimensionlessFlow`.**  For any dimensionless RG
flow, the weak legacy slot fires with `defect` the flow's engineering-dimension
coefficient.  The physical content carried by the flow is the AF monotonicity
`dimless_antitone`. -/
theorem rubricO4Restoration_of_flow
    (F : O4RestorationProgress.DimensionlessFlow) :
    YMGap.Rubric.ClayScorecard.RubricO4Restoration :=
  rubricO4Restoration_of_decay (O4RestorationProgress.scalingDimensionDecay_of_flow F)

/-- **The wiring routed through a `CouplingRunning`.**  For any running coupling,
the weak legacy slot fires; the scalar content is the one-step asymptotic-freedom
beta-sign `betaDrop_nonneg` on the TRUE interacting coupling — the sole remaining
open residual, NOT discharged here. -/
theorem rubricO4Restoration_of_coupling
    (R : O4RestorationProgress.CouplingRunning) :
    YMGap.Rubric.ClayScorecard.RubricO4Restoration :=
  rubricO4Restoration_of_flow (O4RestorationProgress.flowOfCoupling R)

/-- **Non-vacuity capstone.**  The wired clause fires on the concrete
STRICTLY-decreasing model flow `geoFlow` (`g k = 1/2 + (1/2)^k`, `β < 0`),
demonstrating this provenance-bearing witness.  It is not the physical
interacting theory and does not establish observable O4 covariance. -/
theorem rubricO4Restoration_geoFlow :
    YMGap.Rubric.ClayScorecard.RubricO4Restoration :=
  rubricO4Restoration_of_flow O4RestorationProgress.geoFlow

end YMGap.Continuum.O4RestorationH4

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.O4RestorationH4.q_lt_add_of_pos_right
#print axioms YMGap.Continuum.O4RestorationH4.lt_of_lt_of_le
#print axioms YMGap.Continuum.O4RestorationH4.breakCoeff_le_offset
#print axioms YMGap.Continuum.O4RestorationH4.breakCoeff_le_of_le
#print axioms YMGap.Continuum.O4RestorationH4.breakCoeff_zero_add_one_pos
#print axioms YMGap.Continuum.O4RestorationH4.breakCoeff_vanishes
#print axioms YMGap.Continuum.O4RestorationH4.rubricO4Restoration_of_decay
#print axioms YMGap.Continuum.O4RestorationH4.rubricO4Restoration_of_flow
#print axioms YMGap.Continuum.O4RestorationH4.rubricO4Restoration_of_coupling
#print axioms YMGap.Continuum.O4RestorationH4.rubricO4Restoration_geoFlow
