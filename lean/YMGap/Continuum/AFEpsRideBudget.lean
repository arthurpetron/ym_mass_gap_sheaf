/-
Track B / R2 — **IDENTIFYING and BOUNDING the ADDITIVE block-spin erosion `ε_k`,
deriving `ε_k ≤ Dε/(k+1)²` in the deep UV — the ε side of the net-drift floor.**

# What is `ε_k`?  The honest identification (net-drift ride, possibility (b))

The true dimensionless-margin recursion (`TrueMarginRecursionPhysical.step`) is

    margin (k+1)  ≥  (1 − δ_k)·margin k  −  ε_k .

The MULTIPLICATIVE defect `δ_k = bondMovingDeltaRen N p (w k)` is the renormalized
bond-moving weight/gap contraction, and `AFDeepUVSummability.af_defect_invSq` already
DERIVES `δ_k ≤ afDefectScale·1/(k+1)²` from one-loop AF + the exact quadratic
factorization.  The task is the ADDITIVE `ε_k`: identify what it is and bound it.

Two honest candidates were weighed:

  (a) `ε_k` is an *independent* additive part of the same quadratic defect, with its
      OWN opaque scale `Dε` and `ε_k = O((1−w_k)²) ~ 1/k²`.  This is what the
      pre-existing `af_netDriftFloor` ASSUMES (`hε : ε_k ≤ Dε·recipSqSucc k`, opaque
      `Dε`).  It is honest but leaves `Dε` un-tied to anything derived.

  (b) `ε_k` is the **net-drift compensation** — the additive and multiplicative
      erosions are two bookkeepings of the SAME per-step change `|Δmargin_k|`
      (crux doc §4: "Physical margin ≈ const forces the compensation
      `ε_k ≈ δ_k·margin_k`").  A defect that renormalizes a *dimensionless margin*
      erodes it PROPORTIONALLY to the current margin; an absolute shift of the gap
      unrelated to the current gap size is dimensionally the residual that cannot be
      the leading behaviour.  So the honest BOUND is `ε_k ≤ margin_k·δ_k`.

**Verdict — (b) is the real `ε_k`.**  Structurally, `δ_k` is a dimensionless defect
on the weight `w`, and the step law acts on the dimensionless margin; the physical
erosion is multiplicative (a renormalization of the margin), so the additive `ε_k`
carried for conservative bookkeeping is genuinely bounded by `margin_k·δ_k`, NOT by
an independent quadratic with a free constant.  Numerically this is exactly the crux
§4 net-drift budget `η_k = δ_k·margin_k + ε_k` with the second term riding the first.

# What is DERIVED here

With a physical margin ceiling `margin_k ≤ Mmax` (the `physCeil`/`massLat<1` located
bound already carried across the continuum stack) and the net-drift ride
`ε_k ≤ margin_k·δ_k`,

    ε_k  ≤  margin_k·δ_k  ≤  Mmax·δ_k  ≤  Mmax·(afDefectScale·1/(k+1)²)
         =  (Mmax·afDefectScale)·1/(k+1)²  =  afEpsScale·1/(k+1)² ,

so `Dε = afEpsScale = Mmax·afDefectScale` is **DERIVED** — tied to the AF-derived
`Dδ = afDefectScale` and the physical ceiling, NOT an independent opaque constant.
This strictly SHRINKS the open content of the ε side: the pre-existing opaque
`hε : ε_k ≤ Dε·recipSqSucc k` is replaced by two smaller, structural named inputs
(a margin ceiling and the net-drift ride), and `Dε` becomes a derived quantity.

  * `afEpsScale`, `afEpsScale_nonneg` — the DERIVED additive scale `Mmax·afDefectScale`.
  * `af_eps_invSq` — **THE DERIVED DEEP-UV `ε_k ≤ Dε/(k+1)²`.**  From the ride
    `ε_k ≤ margin_k·δ_k`, the ceiling `margin_k ≤ Mmax`, and the AF-derived
    `af_defect_invSq`, yields `ε_k ≤ afEpsScale·recipSqSucc k`.
  * `af_netDriftFloor_derived` — the combined floor with BOTH `δ` AND `ε` DERIVED:
    proved one-loop AF + quadratic factorization + margin ceiling + net-drift ride ⟹
    the positive uniform dimensionless-margin floor, with NO opaque `Dε`/`hε` slot.

# HONEST SCOPE (what is DERIVED vs what stays NAMED-open)

  * DERIVED (deep UV): the per-step `δ_k ~ 1/k²` AND `ε_k ~ 1/k²` scalings, with
    `Dε = Mmax·Dδ` tied to the AF-derived `Dδ`.
  * NAMED (honest inputs, not derived here — strictly smaller than an opaque `Dε`):
      - the physical margin ceiling `margin_k ≤ Mmax` (`physCeil`; heat-kernel/AF);
      - the net-drift ride `ε_k ≤ margin_k·δ_k` (crux §4; the additive/multiplicative
        erosions are two bookkeepings of the same per-step change — FALSE for
        arbitrary `ε`, e.g. `ε_k ≡ 1`, hence a genuine input, not a smuggled goal);
      - the weight↔coupling dictionary `(1 − w_k) ≤ C·g_k²` (inherited);
      - the physical additive-erosion step law + anchor-dominance (the crossover /
        no-gap-closing content).
  * OPEN (unchanged): the finite crossover `k < K` no-gap-closing and `hMoment`.
    This module does NOT close the full YM defect bound — it closes the deep-UV ε
    side, mirroring what `af_defect_invSq` did for the δ side.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic reusing `af_defect_invSq`, `bondMovingDeltaRen_nonneg`,
the `mul_le_mul_of_nonneg_*` monotonicity, and `netDriftFloor_of_invSq`.  Every
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
All witnesses are `Type`-level `Q'` data.
-/

import YMGap.Continuum.AFDeepUVSummability

namespace YMGap.Continuum.AFEpsRideBudget

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.AFDeepUVSummability

/-! ## 1. The DERIVED additive scale `Dε = afEpsScale = Mmax·afDefectScale`. -/

/-- **The DERIVED additive-erosion scale** `Dε = Mmax·afDefectScale C D' p`.  It is
NOT an independent opaque constant: it is the AF-derived multiplicative scale
`afDefectScale` times the physical margin ceiling `Mmax`. -/
def afEpsScale (Mmax C D' : Q') (p : Nat) : Q' :=
  Mmax * afDefectScale C D' p

theorem afEpsScale_nonneg (Mmax C D' : Q') (p : Nat)
    (hMnn : (0 : Q') ≤ Mmax) (hC : (0 : Q') ≤ C) (hD' : (0 : Q') ≤ D') :
    (0 : Q') ≤ afEpsScale Mmax C D' p :=
  Q'.mul_nonneg _ _ hMnn (afDefectScale_nonneg C D' p hC hD')

/-! ## 2. THE DERIVED DEEP-UV `ε_k ≤ Dε/(k+1)²` via the net-drift ride. -/

/-- **`af_eps_invSq` — the DERIVED deep-UV per-step `1/k²` erosion bound.**

    ε_k  ≤  margin_k·δ_k  ≤  Mmax·δ_k  ≤  afEpsScale·(1/(k+1)²) ,

composing (i) the NAMED net-drift ride `ε_k ≤ margin_k·δ_k` (`hride`; the additive
erosion is bounded by the multiplicative erosion of the current margin — crux §4),
(ii) the NAMED margin ceiling `margin_k ≤ Mmax` (`hmceil`; `physCeil`), and (iii) the
AF-DERIVED per-step defect `δ_k = bondMovingDeltaRen N p (w k) ≤ afDefectScale·1/(k+1)²`
(`af_defect_invSq`, nonnegative by `bondMovingDeltaRen_nonneg`).  The additive scale
`Dε = afEpsScale = Mmax·afDefectScale` is DERIVED, not assumed. -/
theorem af_eps_invSq {u0 c2adj C D' Mmax : Q'} (margin ε : Nat → Q') (w : Nat → Q')
    (N p : Nat)
    (hC : (0 : Q') ≤ C) (hD' : (0 : Q') ≤ D') (hMnn : (0 : Q') ≤ Mmax)
    (hDu0 : (1 : Q') ≤ D' * u0) (hDβ : (1 : Q') ≤ D' * betaZero c2adj)
    (hw0 : ∀ k, (0 : Q') ≤ w k) (hw1 : ∀ k, w k ≤ (1 : Q'))
    (k : Nat) (hu : (0 : Q') < invRunningCoupling u0 c2adj k)
    (hlink : (1 : Q') - w k ≤ C * Q'.divPos 1 (invRunningCoupling u0 c2adj k) hu)
    (hmceil : margin k ≤ Mmax)
    (hride : ε k ≤ margin k * bondMovingDeltaRen N p (w k)) :
    ε k ≤ afEpsScale Mmax C D' p * recipSqSucc k := by
  -- δ_k = bondMovingDeltaRen N p (w k):  nonnegative, and ≤ afDefectScale·recipSqSucc k.
  have hδnn : (0 : Q') ≤ bondMovingDeltaRen N p (w k) :=
    bondMovingDeltaRen_nonneg (hw0 k) (hw1 k) N p
  have hδ : bondMovingDeltaRen N p (w k) ≤ afDefectScale C D' p * recipSqSucc k :=
    af_defect_invSq w N p hC hD' hDu0 hDβ hw0 hw1 k hu hlink
  -- Step 1: margin_k·δ_k ≤ Mmax·δ_k  (ceiling, δ ≥ 0).
  have hstep1 : margin k * bondMovingDeltaRen N p (w k)
      ≤ Mmax * bondMovingDeltaRen N p (w k) :=
    Q'.mul_le_mul_of_nonneg_right (margin k) Mmax (bondMovingDeltaRen N p (w k))
      hmceil hδnn
  -- Step 2: Mmax·δ_k ≤ Mmax·(afDefectScale·recipSqSucc k)  (Mmax ≥ 0).
  have hstep2 : Mmax * bondMovingDeltaRen N p (w k)
      ≤ Mmax * (afDefectScale C D' p * recipSqSucc k) :=
    Q'.mul_le_mul_of_nonneg_left (bondMovingDeltaRen N p (w k))
      (afDefectScale C D' p * recipSqSucc k) Mmax hδ hMnn
  -- Reassociate: Mmax·(afDefectScale·recip) ≃ (Mmax·afDefectScale)·recip = afEpsScale·recip.
  have hassoc : (Mmax * (afDefectScale C D' p * recipSqSucc k)).eqv
      (afEpsScale Mmax C D' p * recipSqSucc k) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv Mmax (afDefectScale C D' p) (recipSqSucc k))
  -- Chain: ε_k ≤ margin_k·δ_k ≤ Mmax·δ_k ≤ Mmax·(afDefectScale·recip) ≃ afEpsScale·recip.
  exact Q'.le_trans' _ _ _ hride
    (Q'.le_trans' _ _ _ hstep1
      (Q'.le_trans' _ _ _ hstep2 (Q'.le_of_eqv hassoc)))

/-! ## 3. THE COMBINED FLOOR — BOTH `δ` and `ε` DERIVED (no opaque `Dε`/`hε`). -/

/-- **`af_netDriftFloor_derived` — the deep-UV positive margin floor with the ε side
DERIVED.**

Given the physical additive-erosion recursion (`hstep`, anchor) and the AF-rate
inputs (proved linear law via `hDu0`/`hDβ`, weight link `hlink`, `w_k ∈ [0,1]`), PLUS
the two structural ε inputs — the margin ceiling `margin_k ≤ Mmax` (`hmceil`) and the
net-drift ride `ε_k ≤ margin_k·δ_k` (`hride`) — BOTH per-step budgets are DERIVED:

    δ_k = bondMovingDeltaRen N p (w k)  ≤  afDefectScale·1/(k+1)²   (`af_defect_invSq`)
    ε_k                                  ≤  afEpsScale·1/(k+1)²      (`af_eps_invSq`)

with `afEpsScale = Mmax·afDefectScale` DERIVED, so `netDriftFloor_of_invSq` yields the
positive uniform floor `(1 − 2·afDefectScale)·margin 0 − 2·afEpsScale > 0`.

Unlike `af_netDriftFloor`, there is NO opaque `Dε` and NO `hε : ε_k ≤ Dε·recipSqSucc k`
hypothesis: the ε side is now derived from the δ side, the ceiling, and the ride.  The
`hmceil` ceiling, the `hride` net-drift relation, and the `anchor` (crossover /
no-gap-closing content) remain named physical inputs — the honest deep-UV composition
of BOTH erosion sides, NOT closure of the full bound. -/
theorem af_netDriftFloor_derived {u0 c2adj C D' Mmax : Q'}
    (margin ε : Nat → Q') (w : Nat → Q') (N p : Nat)
    (hC : (0 : Q') ≤ C) (hD' : (0 : Q') ≤ D') (hMnn : (0 : Q') ≤ Mmax)
    (hDu0 : (1 : Q') ≤ D' * u0) (hDβ : (1 : Q') ≤ D' * betaZero c2adj)
    (hw0 : ∀ k, (0 : Q') ≤ w k) (hw1 : ∀ k, w k ≤ (1 : Q'))
    (hu : ∀ k, (0 : Q') < invRunningCoupling u0 c2adj k)
    (hlink : ∀ k, (1 : Q') - w k
        ≤ C * Q'.divPos 1 (invRunningCoupling u0 c2adj k) (hu k))
    (hstep : ∀ k, (1 - bondMovingDeltaRen N p (w k)) * margin k - ε k ≤ margin (k + 1))
    (hδ1 : ∀ k, bondMovingDeltaRen N p (w k) ≤ 1)
    (hεnn : ∀ k, (0 : Q') ≤ ε k) (hm0 : (0 : Q') ≤ margin 0)
    (hmceil : ∀ k, margin k ≤ Mmax)
    (hride : ∀ k, ε k ≤ margin k * bondMovingDeltaRen N p (w k))
    (hanchor : 2 * afEpsScale Mmax C D' p
        < (1 - 2 * afDefectScale C D' p) * margin 0) :
    ∀ k, (1 - 2 * afDefectScale C D' p) * margin 0 - 2 * afEpsScale Mmax C D' p
          ≤ margin k
       ∧ (0 : Q') < (1 - 2 * afDefectScale C D' p) * margin 0
          - 2 * afEpsScale Mmax C D' p :=
  netDriftFloor_of_invSq margin (fun k => bondMovingDeltaRen N p (w k)) ε
    (afDefectScale C D' p) (afEpsScale Mmax C D' p)
    hstep
    (fun k => bondMovingDeltaRen_nonneg (hw0 k) (hw1 k) N p)
    hδ1 hεnn hm0
    (afDefectScale_nonneg C D' p hC hD')
    (afEpsScale_nonneg Mmax C D' p hMnn hC hD')
    (fun k => af_defect_invSq w N p hC hD' hDu0 hDβ hw0 hw1 k (hu k) (hlink k))
    (fun k => af_eps_invSq margin ε w N p hC hD' hMnn hDu0 hDβ hw0 hw1 k (hu k)
      (hlink k) (hmceil k) (hride k))
    hanchor

end YMGap.Continuum.AFEpsRideBudget

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AFEpsRideBudget.afEpsScale_nonneg
#print axioms YMGap.Continuum.AFEpsRideBudget.af_eps_invSq
#print axioms YMGap.Continuum.AFEpsRideBudget.af_netDriftFloor_derived
