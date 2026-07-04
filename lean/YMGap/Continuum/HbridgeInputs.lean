/-
Track 11.6-hbridge / R2 — **The two feeding fields of the pinned
`SpectralMarginInput.hbridge`, split into a CLOSED schedule choice `(b) hLin` and a
genuinely-open named residual `(a) hId`.**

# What this module does (read first)

The pinned shift-control field of `AsymptoticSpectralLoc.SpectralMarginInput`,

    shift_k  ≤  δ_k · g_k,      g_k = divPos (floorRate_k) (a_k),

is produced verbatim by `PinnedBridgeProgress.EdgeShiftResidual.hbridge`, whose ONLY
non-theorem inputs are the two fields

  * `hLin` — the near-continuum LINEAR lower control `bmConst p·(1 − w_k) ≤ δ_k`
    (the graded defect does not vanish faster than linearly in the margin); and
  * `hId`  — the MODEL IDENTIFICATION `(L k).shift 1 ≤ bondMovingDeltaRen N p (w_k)`
    (the `weight defect ⟹ eigenvalue shift` bridge; node ①).

Everything else in the constructor chain (`edgeShift_le_gradedDefect`, the `1/a`
lift `hbridge_pinned_of_edge`, the `hFR` units rewrite) is already a THEOREM over the
PROVED `BondMovingQuadratic.bondMovingDeltaRen_quadratic`.

This module isolates the two:

  * **§1  (b) `hLin` CLOSES as a `SpacingSchedule` choice.**  Because the descent
    defect schedule `δ` is project-owned, PIN it to the quadratic modulus times the
    margin, `pinnedDelta p w k := bmConst p·(1 − w_k)`.  Then `hLin` is exactly
    reflexive (`Q'.le_refl'`).  `HbridgeScheduleInput.toEdgeShiftResidual` performs
    this pinning, discharging `hLin` by construction, so that the field-shaped pinned
    `hbridge` (`HbridgeScheduleInput.hbridge`) becomes a THEOREM whose SOLE remaining
    residual is `hId`.

  * **§2  the honest summability TENSION** (never hidden).  The pinned schedule is
    compatible with `AFDeltaDecay.SummableDescentTower.summable` ONLY when the margin
    `1 − w_k` is itself summable: `lossSum (pinnedDelta p w) n ≃ bmConst p ·
    lossSum (marginSeq w) n` (`lossSum_pinnedDelta_eqv`), so a uniform margin-sum
    bound `S` yields the tower loss bound `bmConst p·S`
    (`pinnedDelta_summable_of_marginSum`) — and ONLY then.  Along an AF-MARGINAL
    trajectory `1 − w_k ∼ A/(k+B)`, `∑ (1 − w_k)` is harmonic (divergent), so no such
    `S` exists and the schedule choice is INCOMPATIBLE with the summable tower: (b)
    closes as a schedule choice, but the honest closure requires a NON-AF
    (super-linearly / summably decaying) margin `1 − w_k`.

  * **§3  (a) `hId` stays the sole open residual.**  `HbridgeScheduleInput` carries
    `hId` and the per-scale `SpectralLocalization` (each with the OPEN `bulk_shift`).
    It is DELIBERATELY NOT inhabited on ℝ⁴.  `hId` is strictly sharper than the old
    constant `bulk_shift ≤ 1/12` (it is pinned to the OWNED, PROVED-quadratic
    `bondMovingDeltaRen`), but it remains genuinely open (node ①).

# Honest scope

Nothing here conjures the gap.  What is GENUINELY NEW and axiom-clean: (b) `hLin` is
discharged by an explicit owned schedule pinning, with the summability incompatibility
made a THEOREM (`lossSum_pinnedDelta_eqv`) rather than hidden; and the pinned field-
shaped `hbridge` is reduced to the single named residual `hId`.  The Clay YM mass gap
stays OPEN: `HbridgeScheduleInput` is uninhabited (its `L` carries the open
`bulk_shift`, and `hId` is not discharged).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and composition over `PinnedBridgeProgress` /
`BondMovingQuadratic` / `ProductFloor`; every carrier is `Type`-level data.  Each
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`,
no custom `axiom`.
-/

import YMGap.Continuum.PinnedBridgeProgress
import YMGap.Continuum.ProductFloor

namespace YMGap.Continuum.HbridgeInputs

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.RegularContinuumPipeline
open YMGap.Continuum.PinnedBridgeProgress
open YMGap.Continuum.ProductFloor

/-! ## 0. The pinned descent-defect schedule (the (b)-closing owned choice) -/

/-- The margin sequence `1 − w_k` (the located weak-coupling margin at scale `k`). -/
def marginSeq (w : Nat → Q') (k : Nat) : Q' := (1 : Q') - w k

/-- **THE PINNED SCHEDULE.**  The project-owned descent defect pinned to the
quadratic modulus times the margin,

    pinnedDelta p w k  :=  bmConst p · (1 − w_k)   ( = 18p·(1 − w_k) ).

This is the `SpacingSchedule`/tower-defect choice that makes the near-continuum
linear control `hLin` exactly reflexive. -/
def pinnedDelta (p : Nat) (w : Nat → Q') (k : Nat) : Q' :=
  bmConst p * ((1 : Q') - w k)

/-- `0 ≤ pinnedDelta p w k` on `0 ≤ w_k ≤ 1` (both factors nonnegative). -/
theorem pinnedDelta_nonneg {w : Nat → Q'} (hw1 : ∀ k, w k ≤ (1 : Q')) (p : Nat) (k : Nat) :
    (0 : Q') ≤ pinnedDelta p w k :=
  Q'.mul_nonneg _ _ (bmConst_nonneg p) (Q'.sub_nonneg_of_le (hw1 k))

/-! ## 1. (b) `hLin` CLOSES — the reduced input with the pinning that discharges it -/

/-- **THE REDUCED INPUT (with `hLin` discharged).**  The per-scale spectral-
localization certificates and the fixed-spacing schedule, together with the SOLE
remaining honest Type-level residual `hId`.  Relative to
`PinnedBridgeProgress.EdgeShiftResidual` this DROPS the `δ` schedule and the `hLin`
field: the schedule is PINNED to `pinnedDelta p w` and `hLin` becomes reflexive.

DELIBERATELY NOT inhabited on ℝ⁴: each `L k` still carries the OPEN `bulk_shift`
(node ①), and `hId` (the `weight defect ⟹ eigenvalue shift` identification) is the
named residual. -/
structure HbridgeScheduleInput (N p : Nat) : Type where
  /-- The RG weight trajectory. -/
  w : Nat → Q'
  /-- Each weight is nonnegative. -/
  hw0 : ∀ k, (0 : Q') ≤ w k
  /-- Each weight is `≤ 1`. -/
  hw1 : ∀ k, w k ≤ (1 : Q')
  /-- The per-scale spectral-localization certificate (open `bulk_shift`). -/
  L : ∀ k, SpectralLocalization (w k)
  /-- **`hId`** — the model identification (the SOLE named residual). -/
  hId : ∀ k, (L k).shift 1 ≤ bondMovingDeltaRen N p (w k)
  /-- The fixed-spacing infinite-volume cluster bounds. -/
  atSpacing : Nat → RegUniformClusterBound
  /-- The (fixed) lattice spacing. -/
  spacing : Q'
  /-- The spacing is strictly positive. -/
  spacing_pos : (0 : Q') < spacing
  /-- The floor-rate dictionary `floorRate_k = 1 − w_k³`. -/
  hFR : ∀ k, (atSpacing k).floorRate = heatKernelMargin (w k)

/-- **THE PINNING — `hLin` discharged reflexively.**  From an
`HbridgeScheduleInput`, build a `PinnedBridgeProgress.EdgeShiftResidual` whose defect
schedule is `δ := pinnedDelta p w` and whose `hLin` field
`bmConst p·(1 − w_k) ≤ δ_k` is EXACTLY reflexive (`Q'.le_refl'`).  Every other field
is supplied verbatim; only `hId` remains as an open residual. -/
def HbridgeScheduleInput.toEdgeShiftResidual {N p : Nat}
    (I : HbridgeScheduleInput N p) : EdgeShiftResidual N p where
  w := I.w
  hw0 := I.hw0
  hw1 := I.hw1
  L := I.L
  δ := pinnedDelta p I.w
  hId := I.hId
  -- (b) CLOSES: `bmConst p·(1 − w_k) ≤ pinnedDelta p w k` is reflexive by definition.
  hLin := fun k => Q'.le_refl' (pinnedDelta p I.w k)
  atSpacing := I.atSpacing
  spacing := I.spacing
  spacing_pos := I.spacing_pos
  hFR := I.hFR

/-- **THE EDGE FORM.**  Under an `HbridgeScheduleInput`, the located-edge relative
shift bound holds at every scale `k`, with the pinned schedule:

    (L k).shift 1  ≤  pinnedDelta p w k · heatKernelMargin (w_k)
                   ( = 18p·(1 − w_k)·(1 − w_k³) ). -/
theorem HbridgeScheduleInput.edgeForm {N p : Nat} (I : HbridgeScheduleInput N p) (k : Nat) :
    (I.L k).shift 1 ≤ pinnedDelta p I.w k * heatKernelMargin (I.w k) :=
  I.toEdgeShiftResidual.edgeForm k

/-- **THE FIELD-SHAPED PINNED `hbridge` (with `hLin` closed).**  Lifting the edge
form by `1/a` and rewriting `heatKernelMargin (w_k) = floorRate_k`, the pinned
`SpectralMarginInput.hbridge` field shape holds at every scale `k` with the pinned
schedule `δ := pinnedDelta p w` — the SOLE remaining open input is `hId`:

    divPos ((L k).shift 1) a  ≤  pinnedDelta p w k · divPos (floorRate_k) a. -/
theorem HbridgeScheduleInput.hbridge {N p : Nat} (I : HbridgeScheduleInput N p) (k : Nat) :
    Q'.divPos ((I.L k).shift 1) I.spacing I.spacing_pos
      ≤ pinnedDelta p I.w k *
          Q'.divPos ((I.atSpacing k).floorRate) I.spacing I.spacing_pos :=
  I.toEdgeShiftResidual.hbridge k

/-! ## 2. The honest summability TENSION — pinned `δ` is summable IFF the margin is -/

/-- **THE CONSTANT PULL-OUT.**  The partial loss-sum of the pinned schedule is the
quadratic modulus times the partial margin-sum:

    ∑_{k<n} pinnedDelta p w k  ≃  bmConst p · ∑_{k<n} (1 − w_k).

PROOF: induction; the empty sum is `bmConst p·0 ≃ 0`; the step distributes
`bmConst p·(A + (1−w_n)) ≃ bmConst p·A + bmConst p·(1−w_n)` (`Q'.mul_add_eqv`), with
`pinnedDelta p w n` definitionally `bmConst p·(1 − w_n)`. -/
theorem lossSum_pinnedDelta_eqv (p : Nat) (w : Nat → Q') :
    ∀ n, (lossSum (pinnedDelta p w) n).eqv (bmConst p * lossSum (marginSeq w) n)
  | 0 => Q'.eqv_symm (Q'.mul_zero_eqv (bmConst p))
  | n + 1 => by
      show (lossSum (pinnedDelta p w) n + pinnedDelta p w n).eqv
        (bmConst p * (lossSum (marginSeq w) n + marginSeq w n))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (pinnedDelta p w n) (lossSum_pinnedDelta_eqv p w n)) ?_
      -- LHS is now `bmConst p·(∑margin) + bmConst p·(1−w_n)`; RHS via `mul_add_eqv`.
      exact Q'.eqv_symm
        (Q'.mul_add_eqv (bmConst p) (lossSum (marginSeq w) n) (marginSeq w n))

/-- **THE SUMMABILITY COMPATIBILITY (positive direction).**  IF the margin has a
uniform partial-sum bound `S` (`∀ n, ∑_{k<n}(1 − w_k) ≤ S`) — i.e. `1 − w_k` decays
SUMMABLY (super-linearly, NOT the AF-marginal `∼ 1/k`) — then the pinned schedule
satisfies the `SummableDescentTower.summable` loss bound with `R := bmConst p · S`:

    ∀ n, ∑_{k<n} pinnedDelta p w k  ≤  bmConst p · S.

This is the ONLY regime in which the (b)-closing schedule pinning is compatible with
the summable descent tower.  Along an AF-MARGINAL margin `1 − w_k ∼ A/(k+B)` the
hypothesis has NO witness `S` (the harmonic sum diverges), so the pinning is then
incompatible with the tower — the documented tension. -/
theorem pinnedDelta_summable_of_marginSum (p : Nat) (w : Nat → Q') {S : Q'}
    (hS : ∀ n, lossSum (marginSeq w) n ≤ S) (n : Nat) :
    lossSum (pinnedDelta p w) n ≤ bmConst p * S := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (lossSum_pinnedDelta_eqv p w n)) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ (hS n) (bmConst_nonneg p)

/-! ## 3. Doc-section — what CLOSES vs. what REDUCES (CRITICAL honesty)

  * **(b) `hLin` CLOSES** (as an owned schedule choice).  Pinning
    `δ_k := pinnedDelta p w k = bmConst p·(1 − w_k)` makes the field
    `bmConst p·(1 − w_k) ≤ δ_k` reflexive (`Q'.le_refl'`); the pinned field-shaped
    `hbridge` (`HbridgeScheduleInput.hbridge`) is then a THEOREM.  The load-bearing
    caveat rides with it as a THEOREM, not a hope: `lossSum_pinnedDelta_eqv` +
    `pinnedDelta_summable_of_marginSum` show the tower `summable` field holds IFF the
    margin `1 − w_k` is summable — which the AF-marginal `∼ 1/k` does NOT supply.  So
    the honest closure requires a NON-AF (super-linearly decaying) margin.

  * **(a) `hId` REDUCES only** (stays the sole named residual, node ①).  The model
    identification `(L k).shift 1 ≤ bondMovingDeltaRen N p (w_k)` is pinned to the
    OWNED, PROVED-quadratic `bondMovingDeltaRen` (strictly sharper than the old
    opaque `bulk_shift ≤ 1/12`), but it is not pure arithmetic and is not discharged.
    `HbridgeScheduleInput` is DELIBERATELY NOT inhabited on ℝ⁴ (its `L` carries the
    open `bulk_shift`, and `hId` is open).  The Clay YM mass gap stays OPEN. -/

end YMGap.Continuum.HbridgeInputs

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HbridgeInputs.pinnedDelta_nonneg
#print axioms YMGap.Continuum.HbridgeInputs.HbridgeScheduleInput.toEdgeShiftResidual
#print axioms YMGap.Continuum.HbridgeInputs.HbridgeScheduleInput.edgeForm
#print axioms YMGap.Continuum.HbridgeInputs.HbridgeScheduleInput.hbridge
#print axioms YMGap.Continuum.HbridgeInputs.lossSum_pinnedDelta_eqv
#print axioms YMGap.Continuum.HbridgeInputs.pinnedDelta_summable_of_marginSum
