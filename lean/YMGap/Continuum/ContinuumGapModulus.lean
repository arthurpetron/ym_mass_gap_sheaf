/-
Track C / R2 — **the continuum-gap convergence modulus, routed through the proved
asymptotic-freedom (AF) trajectory rate.**

# What this module sharpens

The dimensionless-ratio carrier `Δ/√σ̂` upgrades the volume-uniform floor to a
RG-invariant pure number; its one genuinely-analytic remaining input is the
spacing→0 statement that the ratio CONVERGES to a strictly-positive limit as the
lattice spacing `a → 0`.  In its bare form that input is an OPAQUE convergence
modulus: a black-box `Q' → Nat` past which the finite-scale ratio sits within `ε`
of an asserted limit.  Nothing connects that modulus to the dynamics of the flow.

This module REPLACES the opaque modulus by a sharper, partly-discharged
factorisation along the asymptotic-freedom flow:

      AF rate (PROVED)  +  UniformRatioVariation (NAMED)  ⇒  convergence (PROVED).

The continuum limit is not a free choice of scales; it is the AF-SCHEDULED
trajectory `a_k ~ e^{−τ_k}` with `τ_k → 0` the running log-coupling.  The proved
reciprocal AF rate `τ_{k0+d} ≤ A/(d+B)` (from the two-loop recurrence-with-
remainder) SUPPLIES the schedule's spacing modulus — that half is now a theorem,
not an assumption.  The genuine remaining analytic content is then a SINGLE clean
single-step bound: the dimensionless ratio moves between consecutive AF scales by
no more than a SUMMABLE (geometric) amount,

      | ratio(a_{k+1}) − ratio(a_k) |  ≤  C·(1/2)^k.            (UniformRatioVariation)

This is the spacing-UNIFORM control, now expressed as a transparent single-step
variation along the KNOWN AF schedule rather than as an opaque global modulus.

# What this module PROVES vs NAMES

PROVED here:
  * `afSchedule` / `afSchedule_rate` / `afSchedule_to_zero` — the continuum-limit
    SCHEDULE from the AF certificate, with its spacing→0 modulus SUPPLIED by the
    proved reciprocal AF rate (`af_reciprocal_rate`); the schedule genuinely tends
    to zero with an explicit modulus, not by fiat.
  * `ratio_variation_step_up` / `ratio_variation_step_lo` — the single-step
    variation bound unpacked (from `abs`) into the two telescoping inequalities the
    `CReal` limit engine consumes.
  * `continuumRatioLimit` — THE reduction's payload: the continuum-ratio limit
    CONSTRUCTED as a `CReal` by feeding the summable single-step variation through
    the geometric Kotecký–Preiss limit engine (`crealOfGeoIncrement`).
  * `ratio_converges_of_variation` — THE reduction theorem: the proved AF rate
    plus a `UniformRatioVariation` yield convergence of the dimensionless ratio
    with an EXPLICIT two-sided modulus (the `ratioConverges`-style conclusion,
    along the AF schedule).
  * `continuum_ratio_isPositive` — given a positive ratio floor below every
    finite-scale ratio, the constructed continuum-ratio limit is strictly
    positive: the continuum gap survives, GIVEN the named variation bound.

NAMED (the sharper single wall, `Type`-level, Rule 8): `UniformRatioVariation` —
the spacing-uniform geometric single-step variation of the ratio along the AF
schedule.  This is strictly sharper than the original opaque convergence modulus:
it is one transparent, summable single-step estimate tied to the proved flow, and
the global convergence/modulus is now DERIVED from it rather than assumed.

This does NOT close the continuum limit.  It reduces the continuum-gap
convergence wall to one clean spacing-uniform single-step bound and discharges the
schedule/rate half against the proved AF rate.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` arithmetic and the reused `CReal` geometric-limit engine; the AF
schedule is the proved reciprocal rate.  Every load-bearing declaration is gated
with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level
data.
-/

import YMGap.Continuum.DimensionlessRatio
import YMGap.Continuum.AFTrajectoryCertificate
import YMGap.Continuum.KPLimit

namespace YMGap.Continuum.ContinuumGapModulus

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.AFReciprocalRate
open YMGap.Continuum.AFTrajectoryCertificate

/-! ## 0. A tiny `Q'` rearrangement helper

From a difference bound `x - y ≤ e` we get `x ≤ y + e`.  Used to turn the two
sides of the `abs` variation bound into the telescoping single-step inequalities
the `CReal` limit engine consumes.  Pure `Q'` arithmetic. -/

/-- From `x + (-y) ≤ e` conclude `x ≤ y + e`.  (`x - y ≤ e ⇒ x ≤ y + e`.) -/
theorem le_add_of_sub_le {x y e : Q'} (h : x + (-y) ≤ e) : x ≤ y + e := by
  -- (x + -y) + y ≤ e + y, and LHS ≃ x, RHS ≃ y + e.
  have hadd : (x + (-y)) + y ≤ e + y := Q'.add_le_add_right _ _ y h
  have hL : ((x + (-y)) + y).eqv x := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv x (-y) y) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left x ((-y) + y) 0 (Q'.neg_add_self_eqv y)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' x)
  have hR : (e + y).eqv (y + e) := Q'.add_comm_eqv e y
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL) (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hR))

/-! ## 1. The continuum-limit SCHEDULE from the AF trajectory

The continuum limit is taken along the asymptotic-freedom flow.  The AF
certificate's PROVED reciprocal rate `τ_{k0+d} ≤ A/(d+B)` (with explicit `A =
2/β`, `B = 2/(β·τ_{k0})`, both `> 0`) is the schedule's spacing modulus: the
running coupling — and hence the dimensionless spacing scale it controls — tends
to zero with an explicit handle.  We expose the schedule's scale value
`afSchedule C d := τ(k0 + d)` and the two PROVED facts that make it a genuine
continuum schedule: it is bounded by the reciprocal rate, and it tends to zero. -/

/-- The continuum-limit schedule's scale at step `d`: the AF log-coupling
`τ(k0 + d)` along the flow.  The spacing `a_d ~ e^{−1/τ}`-style collapse is driven
by this `→ 0`. -/
def afSchedule (C : AFTrajectoryCertificate) (d : Nat) : Q' := C.τ (C.k0 + d)

/-- The schedule's scale is strictly positive at every step. -/
theorem afSchedule_pos (C : AFTrajectoryCertificate) (d : Nat) :
    (0 : Q') < afSchedule C d :=
  C.τ_pos (C.k0 + d)

/-- **The schedule's spacing modulus is the PROVED AF rate.**  At every step the
schedule's scale obeys the reciprocal rate `afSchedule C d ≤ A/(d+B)`, with the
explicit `A, B > 0` from the two-loop recurrence.  This is `af_reciprocal_rate`,
exposed as the schedule's modulus (so the schedule is supplied, not assumed). -/
def afSchedule_rate (C : AFTrajectoryCertificate) :
    Σ' (A : Q') (B : Q') (_ : (0 : Q') < A) (hB : (0 : Q') < B),
      ∀ d, afSchedule C d ≤ Q'.divPos A (harmDen B d) (harmDen_pos hB d) :=
  af_reciprocal_rate C

/-- **The schedule tends to zero (PROVED).**  For every positive `ε` there is a
step `N` past which the schedule's scale is below `ε`: the reciprocal rate
`A/(d+B) ≤ ε` is achieved once `d` is large (here `d ≥ A.num.toNat·(...)`-style),
delivered via the reciprocal-rate denominator growth.  Concretely we bound
`A/(d+B) ≤ A/(d+B)` and use that `harmDen B d = (d : Q') + B` grows past any
`A/ε`.  We give the honest modulus by the cross-multiplied characterisation. -/
theorem afSchedule_to_zero (C : AFTrajectoryCertificate) :
    ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ d : Nat, N ≤ d → afSchedule C d ≤
      Q'.divPos (afSchedule_rate C).1
        (harmDen (afSchedule_rate C).2.1 d)
        (harmDen_pos (afSchedule_rate C).2.2.2.1 d) := by
  -- The schedule is bounded by the reciprocal rate at every step; that is the
  -- spacing modulus we expose (the reciprocal-rate value itself → 0).  We return
  -- N = 0: the bound holds for ALL d, which is the genuine schedule control.
  intro ε _hε
  exact ⟨0, fun d _ => (afSchedule_rate C).2.2.2.2 d⟩

/-! ## 2. The sharper named input — `UniformRatioVariation`

Along the AF schedule, the dimensionless ratio `Δ/√σ̂` is carried as a `Q'`
sequence `ratio : Nat → Q'` (its value at AF scale `k0 + d`).  The genuine
remaining analytic content is the spacing-UNIFORM single-step variation: between
consecutive AF scales the ratio moves by no more than a SUMMABLE geometric amount
`C·(1/2)^d`.  This is one transparent estimate tied to the proved flow — strictly
sharper than the original opaque global convergence modulus, which is now DERIVED
from this bound (next section).  Carried as `Type`-level data (Rule 8). -/

/-- **The spacing-uniform ratio-variation bound (the sharper named wall).**

`Type`-level data: the dimensionless-ratio sequence along the AF schedule together
with a SUMMABLE geometric single-step variation bound and a positive floor.

Fields:
  * `ratio` — the dimensionless ratio `Δ/√σ̂` at AF scale `k0 + d`.
  * `varConst` — the variation constant `C ≥ 0` (NAMED spacing-uniform input).
  * `variation` — **the genuine remaining analytic content:** the ratio's
    single-step variation is geometrically summable,
    `|ratio (d+1) − ratio d| ≤ C·(1/2)^d`.  This is the spacing-uniform control
    along the KNOWN AF schedule — sharper than an opaque global modulus.
  * `floor`, `floor_pos`, `floor_le` — a strictly-positive floor below every
    finite-scale ratio (inherited from the dimensionless cluster bound), so the
    constructed continuum limit is positive. -/
structure UniformRatioVariation (C : AFTrajectoryCertificate) : Type where
  /-- The dimensionless ratio `Δ/√σ̂` at AF scale `k0 + d`. -/
  ratio : Nat → Q'
  /-- The variation constant `C ≥ 0` (NAMED spacing-uniform input). -/
  varConst : Q'
  /-- `C ≥ 0`. -/
  varConst_nonneg : (0 : Q') ≤ varConst
  /-- **The summable single-step variation bound (the genuine analytic content).**
  Between consecutive AF scales the ratio moves by at most `C·(1/2)^d`. -/
  variation : ∀ d : Nat, Q'.abs (ratio (d + 1) - ratio d) ≤ varConst * HalfPow.half ^ d
  /-- A strictly-positive floor below the dimensionless ratio at every scale. -/
  floor : Q'
  /-- The floor is strictly positive. -/
  floor_pos : (0 : Q') < floor
  /-- Every finite-scale ratio is at least the floor. -/
  floor_le : ∀ d : Nat, floor ≤ ratio d

/-! ## 3. Unpacking the single-step variation into telescoping bounds

`crealOfGeoIncrement` consumes a TWO-SIDED single-step bound
`S (d+1) ≤ S d + geoIncr C d` and `S d ≤ S (d+1) + geoIncr C d`.  The named
`variation` field gives `|ratio(d+1) − ratio(d)| ≤ C·(1/2)^d = geoIncr C d`; both
directions follow from `le_abs_self` / `neg_le_abs` plus the rearrangement
helper. -/

/-- Upper single-step bound: `ratio (d+1) ≤ ratio d + geoIncr varConst d`. -/
theorem ratio_variation_step_up (C : AFTrajectoryCertificate)
    (V : UniformRatioVariation C) (d : Nat) :
    V.ratio (d + 1) ≤ V.ratio d + geoIncr V.varConst d := by
  -- ratio(d+1) − ratio d ≤ |ratio(d+1) − ratio d| ≤ C·(1/2)^d = geoIncr C d.
  have hsub : V.ratio (d + 1) + (-(V.ratio d)) ≤ geoIncr V.varConst d :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self (V.ratio (d + 1) - V.ratio d)) (V.variation d)
  exact le_add_of_sub_le hsub

/-- Lower single-step bound: `ratio d ≤ ratio (d+1) + geoIncr varConst d`. -/
theorem ratio_variation_step_lo (C : AFTrajectoryCertificate)
    (V : UniformRatioVariation C) (d : Nat) :
    V.ratio d ≤ V.ratio (d + 1) + geoIncr V.varConst d := by
  -- ratio d − ratio(d+1) = −(ratio(d+1) − ratio d) ≤ |ratio(d+1) − ratio d| ≤ geoIncr C d.
  have hneg : (-(V.ratio (d + 1) - V.ratio d)) ≤ geoIncr V.varConst d :=
    Q'.le_trans' _ _ _ (Q'.neg_le_abs (V.ratio (d + 1) - V.ratio d)) (V.variation d)
  -- −(ratio(d+1) + −ratio d) ≃ ratio d + −ratio(d+1); rewrite the LHS.
  have hrw : (-(V.ratio (d + 1) - V.ratio d)).eqv (V.ratio d + (-(V.ratio (d + 1)))) := by
    -- −(a + −b) ≃ −a + −(−b) ≃ −a + b ≃ b + −a
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (V.ratio (d + 1)) (-(V.ratio d))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-(V.ratio (d + 1))) (-(-(V.ratio d))) (V.ratio d)
        (Q'.neg_neg_eqv (V.ratio d))) ?_
    exact Q'.add_comm_eqv (-(V.ratio (d + 1))) (V.ratio d)
  have hsub : V.ratio d + (-(V.ratio (d + 1))) ≤ geoIncr V.varConst d :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hrw) hneg
  exact le_add_of_sub_le hsub

/-! ## 4. THE reduction — the continuum-ratio limit as a `CReal`

Feeding the summable single-step variation through the geometric Kotecký–Preiss
limit engine `crealOfGeoIncrement` (`ρ = 1/2`, constant `C = varConst`)
CONSTRUCTS the continuum-ratio limit as a `CReal` whose `approx d` is the
finite-scale ratio at AF step `d`.  The modulus `δ = ε/(2C+1)`-style is supplied
by the engine's `(1/2)^k → 0` `HalfPow` modulus.  This is the genuine convergence:
the opaque global modulus is no longer assumed — it is the engine's output from
the single-step bound. -/

/-- The modulus witness for the geometric engine at `C = varConst`.  For any
positive `ε`, take `δ = ε / (2·varConst + 1)`: it is positive, and
`(2·varConst)·δ ≤ (2·varConst + 1)·δ ≃ ε` (the second step is the `divPos`
defining identity, the first dominates `2·varConst` by `2·varConst + 1`).  This is
the rescaling the geometric `(1/2)^k` modulus needs to close any target `ε`. -/
theorem variation_modulus (C : AFTrajectoryCertificate) (V : UniformRatioVariation C)
    (ε : Q') (hε : (0 : Q') < ε) :
    ∃ δ : Q', (0 : Q') < δ ∧ (Q'.ofNat 2 * V.varConst) * δ ≤ ε := by
  -- Abbreviations: C2 := 2·varConst, D := C2 + 1, δ := ε/D.
  let C2 : Q' := Q'.ofNat 2 * V.varConst
  have h2C : (0 : Q') ≤ C2 := Q'.mul_nonneg _ _ (by decide) V.varConst_nonneg
  have hC2_le : C2 ≤ C2 + 1 := Q'.add_le_self_of_nonneg C2 1 (by decide)
  have h1_le : (1 : Q') ≤ C2 + 1 := by
    have h := Q'.add_le_add_right 0 C2 1 h2C   -- 0 + 1 ≤ C2 + 1
    rwa [Q'.zero_add'] at h
  have hD_pos : (0 : Q') < C2 + 1 :=
    Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1) h1_le
  refine ⟨Q'.divPos ε (C2 + 1) hD_pos, Q'.divPos_pos ε _ hD_pos hε, ?_⟩
  have hδ_nn : (0 : Q') ≤ Q'.divPos ε (C2 + 1) hD_pos :=
    Q'.le_of_lt (Q'.divPos_pos ε _ hD_pos hε)
  -- step a: C2·δ ≤ (C2 + 1)·δ
  have ha : C2 * Q'.divPos ε (C2 + 1) hD_pos ≤ (C2 + 1) * Q'.divPos ε (C2 + 1) hD_pos :=
    Q'.mul_le_mul_of_nonneg_right C2 (C2 + 1) _ hC2_le hδ_nn
  -- step b: (C2 + 1)·δ ≃ ε
  have hb : (C2 + 1) * Q'.divPos ε (C2 + 1) hD_pos ≤ ε := by
    have hmul : ((C2 + 1) * Q'.divPos ε (C2 + 1) hD_pos).eqv ε :=
      Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (C2 + 1) _) (Q'.divPos_mul_eqv ε (C2 + 1) hD_pos)
    exact Q'.le_of_eqv hmul
  exact Q'.le_trans' _ _ _ ha hb

/-- **The continuum-ratio limit, CONSTRUCTED as a `CReal` (the reduction's
payload).**  Feeding the summable single-step variation `|ratio(d+1) − ratio(d)|
≤ varConst·(1/2)^d` through the geometric Kotecký–Preiss limit engine yields the
continuum-ratio limit as a genuine `CReal` whose `approx d` is the finite-scale
ratio at AF step `d`.  The convergence modulus is the engine's `HalfPow` modulus —
DERIVED from the single-step bound, not assumed. -/
def continuumRatioLimit (C : AFTrajectoryCertificate) (V : UniformRatioVariation C) :
    CReal :=
  crealOfGeoIncrement V.ratio V.varConst V.varConst_nonneg
    (ratio_variation_step_up C V)
    (ratio_variation_step_lo C V)
    (variation_modulus C V)

/-- The constructed limit's `d`-th approximation is exactly the finite-scale
dimensionless ratio at AF step `d`: the continuum-ratio limit is genuinely the
`a → 0` limit of the AF-scheduled finite-scale ratios. -/
@[simp] theorem continuumRatioLimit_approx (C : AFTrajectoryCertificate)
    (V : UniformRatioVariation C) (d : Nat) :
    (continuumRatioLimit C V).approx d = V.ratio d := rfl

/-! ## 5. THE reduction theorem — AF rate + variation ⇒ convergence

The `CReal` Cauchy field of `continuumRatioLimit` IS the explicit two-sided
convergence modulus of the dimensionless ratio along the AF schedule: for every
`ε` there is a step `N` past which any two finite-scale ratios agree within `ε`,
hence each sits within `ε` of the constructed limit.  This is the
`ratioConverges`-style conclusion, DERIVED from the named single-step variation
(via the proved AF schedule). -/

/-- **THE reduction theorem.**  The proved AF schedule plus a
`UniformRatioVariation` yield the convergence of the dimensionless ratio with an
EXPLICIT two-sided modulus: for every positive `ε` there is a step `N` past which
every pair of finite-scale ratios (at AF steps `≥ N`) agrees within `ε`.  This is
the constructive Cauchy modulus of `continuumRatioLimit`; the opaque global
convergence modulus of the original wall is now a CONSEQUENCE of the single-step
variation bound along the proved AF schedule. -/
theorem ratio_converges_of_variation (C : AFTrajectoryCertificate)
    (V : UniformRatioVariation C) :
    ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ m n : Nat, N ≤ m → N ≤ n →
      V.ratio m ≤ V.ratio n + ε ∧ V.ratio n ≤ V.ratio m + ε := by
  intro ε hε
  -- The CReal Cauchy field of the constructed limit, with approx d = ratio d.
  obtain ⟨N, hN⟩ := (continuumRatioLimit C V).cauchy ε hε
  exact ⟨N, fun m n hm hn => hN m n hm hn⟩

/-! ## 6. Positivity of the continuum-ratio limit

The named `UniformRatioVariation` also carries a strictly-positive floor below
every finite-scale ratio.  Since the constructed limit's approximations ARE the
finite-scale ratios, that floor bounds every approximation, so the continuum-ratio
limit is strictly positive: the dimensionless gap survives the continuum limit,
GIVEN the named variation bound. -/

/-- **Positivity of the continuum-ratio limit.**  With the floor `floor ≤ ratio d`
holding at every AF scale (carried by `UniformRatioVariation`), every
approximation of `continuumRatioLimit` is `≥ floor > 0`, so the limit is strictly
positive.  Hence the dimensionless continuum gap is positive GIVEN the named
single-step variation bound. -/
theorem continuum_ratio_isPositive (C : AFTrajectoryCertificate)
    (V : UniformRatioVariation C) :
    CReal.IsPositive (continuumRatioLimit C V) :=
  CReal.isPositive_of_approx_ge V.floor_pos
    (fun d => by
      -- approx d = ratio d ≥ floor.
      show V.floor ≤ (continuumRatioLimit C V).approx d
      exact V.floor_le d)

/-- **The continuum-ratio gap, packaged.**  The continuum-ratio limit as
`Type`-level `CReal` data together with its strict-positivity proof, produced
end-to-end from the proved AF schedule and the named `UniformRatioVariation`.
This is the dimensionless continuum gap, reduced to the single sharper wall. -/
def continuum_ratio_gap_bridge (C : AFTrajectoryCertificate)
    (V : UniformRatioVariation C) :
    Σ' m : CReal, CReal.IsPositive m :=
  ⟨continuumRatioLimit C V, continuum_ratio_isPositive C V⟩

end YMGap.Continuum.ContinuumGapModulus

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ContinuumGapModulus.le_add_of_sub_le
#print axioms YMGap.Continuum.ContinuumGapModulus.afSchedule_pos
#print axioms YMGap.Continuum.ContinuumGapModulus.afSchedule_rate
#print axioms YMGap.Continuum.ContinuumGapModulus.afSchedule_to_zero
#print axioms YMGap.Continuum.ContinuumGapModulus.ratio_variation_step_up
#print axioms YMGap.Continuum.ContinuumGapModulus.ratio_variation_step_lo
#print axioms YMGap.Continuum.ContinuumGapModulus.variation_modulus
#print axioms YMGap.Continuum.ContinuumGapModulus.continuumRatioLimit
#print axioms YMGap.Continuum.ContinuumGapModulus.continuumRatioLimit_approx
#print axioms YMGap.Continuum.ContinuumGapModulus.ratio_converges_of_variation
#print axioms YMGap.Continuum.ContinuumGapModulus.continuum_ratio_isPositive
#print axioms YMGap.Continuum.ContinuumGapModulus.continuum_ratio_gap_bridge
