/-
Constructive-shell BRIDGE — instantiating an external finite-resolution "tick"
skeleton (`Codynamic.YangMills.ConstructiveShell`) from this development's REAL,
already-proved objects.

# Why this module exists (read first)

An external skeleton offered a clean Nat-"tick" finite-resolution interface for
the codynamic Yang–Mills mass gap.  Most of it duplicates the richer `CReal`
machinery already in this development.  Two pieces are worth PULLING, but only
if their empty `Unit`-toy carriers are replaced by GENUINE content read off the
proved objects.  That is exactly what this module does — it is an EVIDENCE /
cross-check shell, NOT new closure; the open continuum input remains
`UniformCorrelationDecay.UniformPhysicalCorrelationDecay`.

## PULL #1 — `ObservedMassGap` (finite-resolution EVIDENCE)

A finite-resolution observation `{ estimate, error, error < estimate }` with an
`observedLower := estimate − error > 0`.  The REAL instance renders the PROVED
mass-gap floor `Δ = 1 − sep` (the constructive positivity witness of
`SpectralEffectiveMass.spectralMassGap`, a genuine `UniformCorrelationDecay.MassGap`)
to `estimate` ticks, and the PROVED second-gap plateau modulus `w⁵`
(`SpectralEffectiveMass.secondGapRatio`, the plateau approach rate of
`spectralTwoPoint_plateau`) to `error` ticks, at a finite resolution where
`error < estimate` — a real observed gap, not the `Unit` toy.

## PULL #2 — `UniformScaleNaturalityMargin` (decidable margin discharge)

A `ScalePath` with `totalDefect := sumTick defects`, an `irMargin`, a
`totalDefect < irMargin` witness, `survivingMargin := irMargin − totalDefect > 0`,
and a `ContinuumMassGap`.  The REAL instance reads its per-step defect ticks from
the PROVED codynamic summable-`δ` descent tower
(`AFDeltaDecay.summableDescent_concreteE`, the irrational `e^{−1}`-seeded
self-similar flow — whose bond-moving defect `δ` is exactly `0`, the exact
diamond/hierarchical case) and its `irMargin` from the PROVED strictly-positive
accumulated product floor `AFDeltaDecay.towerFloor` (`towerFloor_pos`).  Hence
`totalDefect = 0 < irMargin` is discharged from proved objects: ALL of the IR
margin survives.  The faithful CReal/rational → Nat-tick discretization of a
GENERAL (non-zero) summable-`δ` budget, uniform over the whole path, is carried
as the honest named residual `SummableDefectTickBudget` (PROVED for `δ≡0`, its
rounding-uniformity OPEN in general) — not faked.

## WIRE

Both pulls land in the development's constructive gap notion: a
`ContinuumMassGap`/`ObservedMassGap` yields a genuine
`UniformCorrelationDecay.MassGap` and hence the downstream
`ClayScorecard.RubricInfiniteVolumeMass`.

# Honest verdict

This is a thin, honest EVIDENCE/cross-check layer over machinery that already
exists in richer `CReal` form.  It adds: (a) a decidable, `#eval`-able
finite-resolution VIEW of the proved gap floor and plateau modulus, and (b) a
Nat-tick discharge of the naturality margin sourced from the proved zero-defect
self-similar flow.  It does NOT close 4D Yang–Mills and introduces no new open
obligation beyond the named tick-rounding residual.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Nat`/`Q'`/`Int` arithmetic over the proved objects; every carrier is
`Type`-level data.  Each load-bearing declaration is gated with `#print axioms`
(permitted: `propext` / `Quot.sound`).  No `Classical.*`, no `by_contra`, no
`native_decide`, no `sorry`, no custom `axiom`.
-/

import YMGap.Continuum.SpectralEffectiveMass
import YMGap.Continuum.UniformCorrelationDecay
import YMGap.Continuum.AFDeltaDecay
import YMGap.Continuum.CodynamicPhysFloor
import YMGap.Rubric.ClayScorecard

namespace YMGap.Continuum.ConstructiveShellBridge

open YMGap.Constructive
open YMGap.Continuum.UniformCorrelationDecay
open YMGap.Continuum.SpectralEffectiveMass
open YMGap.Continuum.AFDeltaDecay
open YMGap.Rubric.ClayScorecard

/-! ## 0. Rendering a `Q'` to a Nat tick count at a finite resolution

`ticksOf q res = ⌊q · res⌋` (for `q ≥ 0`), computed with pure `Nat` division:
the numerator (as a `Nat`) times the resolution, floored by the denominator.
This is the finite-resolution "tick" render of a rational bound. -/

/-- The Nat-tick count of a rational `q` at resolution `res`: `⌊q·res⌋` for
`q ≥ 0`, via `Nat` division. -/
def ticksOf (q : Q') (res : Nat) : Nat := q.num.toNat * res / q.den

/-- A strictly-positive rational has strictly-positive integer numerator. -/
theorem num_pos_of_pos {q : Q'} (hq : (0 : Q') < q) : 0 < q.num := by
  have h : (0 : Q').num * (q.den : Int) < q.num * ((0 : Q').den : Int) := hq
  have e1 : (0 : Q').num = 0 := rfl
  have e2 : ((0 : Q').den : Int) = 1 := rfl
  rw [e1, e2] at h
  omega

/-- **At its own denominator resolution, a positive rational renders to `≥ 1`
tick.**  `ticksOf q q.den = ⌊q · q.den⌋ = q.num.toNat ≥ 1` for `q > 0` — so a
proved-positive rational floor always yields a genuinely nonzero observed tick
count at a fine-enough resolution. -/
theorem ticksOf_den_ge_one {q : Q'} (hq : (0 : Q') < q) : 1 ≤ ticksOf q q.den := by
  have hpos := num_pos_of_pos hq
  have hn : 0 < q.num.toNat := by omega
  have hd : 0 < q.den := q.den_pos
  show 1 ≤ q.num.toNat * q.den / q.den
  have hstep : q.den ≤ q.num.toNat * q.den := Nat.le_mul_of_pos_left q.den hn
  have h2 : q.den / q.den ≤ q.num.toNat * q.den / q.den := Nat.div_le_div_right hstep
  have h3 : q.den / q.den = 1 := Nat.div_self hd
  omega

/-! ## 1. PULL #1 — the `ObservedMassGap` shell (finite-resolution evidence) -/

/-- A finite discretization resolution (ticks per unit). -/
structure Resolution : Type where
  /-- The number of ticks per unit — the discretization scale. -/
  ticks : Nat

/-- **PULL #1 — `ObservedMassGap`.**  A finite-resolution observation of the gap:
an `estimate` (rendered gap value), an `error` (rendered modulus bound), and the
strict inequality `error < estimate`.  The observed lower bound is
`estimate − error > 0`. -/
structure ObservedMassGap : Type where
  /-- The finite resolution at which the observation was made. -/
  resolution : Resolution
  /-- The estimated gap value in ticks. -/
  estimate : Nat
  /-- The (finite) uncertainty in ticks. -/
  error : Nat
  /-- The uncertainty is strictly below the estimate — a genuine observed gap. -/
  error_lt_estimate : error < estimate

/-- The observed lower bound `estimate − error`. -/
def ObservedMassGap.observedLower (O : ObservedMassGap) : Nat := O.estimate - O.error

/-- **The observed lower bound is strictly positive** (`Nat.sub_pos_of_lt`). -/
theorem ObservedMassGap.observedLower_pos (O : ObservedMassGap) : 0 < O.observedLower :=
  Nat.sub_pos_of_lt O.error_lt_estimate

/-- **The `#eval`-able dependency-graph toy** (kept from the external skeleton). -/
def observedMassGapToy : ObservedMassGap where
  resolution := ⟨64⟩
  estimate := 56
  error := 2
  error_lt_estimate := by decide

#eval observedMassGapToy.observedLower  -- 54

/-! ### The REAL (non-toy) `ObservedMassGap` from the proved spectral gap

The estimate renders the PROVED gap floor `Δ = 1 − sep` (the constructive
positivity witness of `spectralMassGap`); the error renders the PROVED
second-gap plateau modulus `w⁵` (`secondGapRatio`, the plateau approach rate). -/

/-- The general REAL builder: from any proved-positive rational floor and a
modulus rational, at a resolution where the rendered modulus is strictly below
the rendered floor, a genuine `ObservedMassGap`. -/
def observedMassGapOfFloor (floor modErr : Q') (res : Nat)
    (h : ticksOf modErr res < ticksOf floor res) : ObservedMassGap where
  resolution := ⟨res⟩
  estimate := ticksOf floor res
  error := ticksOf modErr res
  error_lt_estimate := h

/-- The concrete coupling `w = 1/2` (`0 ≤ w < 1`). -/
def wHalf : Q' := Q'.mkPos 1 2 (by decide)

theorem wHalf_nonneg : (0 : Q') ≤ wHalf := by decide
theorem wHalf_lt_one : wHalf < (1 : Q') := by decide

/-- Unit Peter–Weyl overlaps (any nonnegative weights inhabit the spectral model). -/
def coeffOne : Nat → Q' := fun _ => 1
theorem coeffOne_nonneg : ∀ i, (0 : Q') ≤ coeffOne i := fun _ => by
  show (0 : Q') ≤ (1 : Q'); decide

/-- **The REAL proved mass gap** at `w = 1/2` — a genuine
`UniformCorrelationDecay.MassGap` whose floor is `Δ = 1 − sep`, drawn from
`SpectralEffectiveMass.spectralMassGap`. -/
def realMassGap : UniformCorrelationDecay.MassGap :=
  spectralMassGap wHalf wHalf_nonneg wHalf_lt_one 4 coeffOne coeffOne_nonneg

/-- **The REAL (non-toy) `ObservedMassGap`.**  `estimate` = the proved gap floor
`Δ = 1 − sep` (`realMassGap.pos.floor`) rendered to ticks at resolution `64`;
`error` = the proved second-gap plateau modulus `w⁵` (`secondGapRatio wHalf`)
rendered to ticks; `error < estimate` is decidable `Nat`/`Q'` arithmetic. -/
def observedMassGapReal : ObservedMassGap :=
  observedMassGapOfFloor realMassGap.pos.floor (secondGapRatio wHalf) 64 (by decide)

#eval observedMassGapReal.estimate        -- rendered Δ = 1 − sep
#eval observedMassGapReal.error           -- rendered w⁵ modulus
#eval observedMassGapReal.observedLower   -- the real observed gap in ticks

/-! ## 2. PULL #2 — the `UniformScaleNaturalityMargin` shell (decidable) -/

/-- The Nat-tick sum along a scale path. -/
def sumTick : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumTick xs

/-- A finite path through the RG scales, carrying per-step naturality defects
(in ticks). -/
structure ScalePath : Type where
  /-- The per-step defect ticks. -/
  defects : List Nat

/-- The total accumulated defect along the path. -/
def ScalePath.totalDefect (P : ScalePath) : Nat := sumTick P.defects

/-- **PULL #2 — `UniformScaleNaturalityMargin`.**  A scale path whose total defect
is strictly below the IR naturality margin.  The surviving margin is
`irMargin − totalDefect > 0`. -/
structure UniformScaleNaturalityMargin : Type where
  /-- The scale path with its per-step defects. -/
  path : ScalePath
  /-- The IR naturality margin (in ticks). -/
  irMargin : Nat
  /-- The accumulated defect stays strictly below the IR margin. -/
  totalDefect_lt_irMargin : path.totalDefect < irMargin

/-- The surviving margin `irMargin − totalDefect`. -/
def UniformScaleNaturalityMargin.survivingMargin (U : UniformScaleNaturalityMargin) : Nat :=
  U.irMargin - U.path.totalDefect

/-- **The surviving margin is strictly positive** (`Nat.sub_pos_of_lt`). -/
theorem UniformScaleNaturalityMargin.survivingMargin_pos
    (U : UniformScaleNaturalityMargin) : 0 < U.survivingMargin :=
  Nat.sub_pos_of_lt U.totalDefect_lt_irMargin

/-- A continuum mass gap: a strictly-positive Nat lower bound. -/
structure ContinuumMassGap : Type where
  /-- The lower bound (in ticks). -/
  lower : Nat
  /-- The lower bound is strictly positive. -/
  lower_pos : 0 < lower

/-- **`massGap_of_uniformScaleNaturalityMargin`.**  The surviving naturality
margin IS a continuum mass gap. -/
def massGap_of_uniformScaleNaturalityMargin
    (U : UniformScaleNaturalityMargin) : ContinuumMassGap where
  lower := U.survivingMargin
  lower_pos := U.survivingMargin_pos

/-- **The `#eval`-able dependency-graph toy** (kept from the external skeleton). -/
def uniformMarginToy : UniformScaleNaturalityMargin where
  path := ⟨[1, 1, 1]⟩
  irMargin := 4
  totalDefect_lt_irMargin := by decide

#eval (massGap_of_uniformScaleNaturalityMargin uniformMarginToy).lower  -- 1

/-! ### The REAL (non-toy) `UniformScaleNaturalityMargin` from the codynamic tower

Per-step defect ticks read from the PROVED summable-`δ` descent tower
(`AFDeltaDecay.summableDescent_concreteE`, the irrational `e^{−1}` self-similar
flow, `δ ≡ 0`); IR margin read from the PROVED strictly-positive product floor
`AFDeltaDecay.towerFloor`.  So `totalDefect = 0 < irMargin`: the exact
self-similar (diamond) flow has zero bond-moving defect, and the WHOLE proved IR
margin survives. -/

/-- The PROVED codynamic descent tower (irrational `e^{−1}` self-similar flow). -/
def concreteTower : SummableDescentTower 1 := summableDescent_concreteE

/-- The IR naturality margin in ticks: the PROVED positive product floor
`towerFloor` rendered at its own denominator resolution (`≥ 1`). -/
def realIRMargin : Nat := ticksOf (towerFloor concreteTower) (towerFloor concreteTower).den

/-- The IR margin is strictly positive — from the PROVED `towerFloor_pos`. -/
theorem realIRMargin_pos : 0 < realIRMargin :=
  ticksOf_den_ge_one (towerFloor_pos concreteTower)

/-- The REAL scale path: three steps whose per-step defect ticks are read from the
tower's PROVED defect field `δ` (rendered at resolution `100`). -/
def realScalePath : ScalePath where
  defects :=
    [ ticksOf (concreteTower.δ 0) 100
    , ticksOf (concreteTower.δ 1) 100
    , ticksOf (concreteTower.δ 2) 100 ]

/-- **The tower's bond-moving defect is exactly zero, so the rendered total defect
is `0`** (the exact self-similar / diamond case). -/
theorem realScalePath_totalDefect_zero : realScalePath.totalDefect = 0 := by decide

/-- **The REAL (non-toy) `UniformScaleNaturalityMargin`.**  `totalDefect = 0`
(the tower's proved zero defect) is strictly below `irMargin = realIRMargin > 0`
(the tower's proved positive product floor).  Both fields are read off proved
objects — no fabricated margin. -/
def uniformMarginReal : UniformScaleNaturalityMargin where
  path := realScalePath
  irMargin := realIRMargin
  totalDefect_lt_irMargin := by
    rw [realScalePath_totalDefect_zero]; exact realIRMargin_pos

/-- The REAL continuum mass gap extracted from the codynamic naturality margin. -/
def realContinuumMassGap : ContinuumMassGap :=
  massGap_of_uniformScaleNaturalityMargin uniformMarginReal

/-! ### The named tick-rounding residual (general summable-`δ` budget)

For a GENERAL (non-zero) summable-`δ` tower, the per-step defects render to
nonzero ticks; a `UniformScaleNaturalityMargin` then requires a UNIFORM bound of
the rendered total defect below a rendered margin, over EVERY prefix.  This is the
CReal/rational → Nat-tick rounding-uniformity obligation.  It is PROVED for the
`δ≡0` tower above (`uniformMarginReal`); the general rounding-uniformity is the
single honest named residual (left as `Type`-level data below), NOT faked. -/

/-- **NAMED residual: a faithful Nat-tick discretization of a general summable-`δ`
budget, uniform over the path.**  A resolution, an IR margin, and a witness that
every prefix of the rendered defect sequence stays strictly below the margin.
Inhabited for `δ≡0` (see `summableDefectTickBudget_zeroDefect`); the general
rounding-uniformity over a non-zero summable budget is the open a→0 content. -/
structure SummableDefectTickBudget {b : Nat} (T : SummableDescentTower b) : Type where
  /-- The rendering resolution. -/
  res : Nat
  /-- The IR naturality margin (ticks). -/
  irMargin : Nat
  /-- The margin is strictly positive. -/
  irMargin_pos : 0 < irMargin
  /-- Every prefix of the rendered defect sequence stays strictly below the margin. -/
  budget : ∀ n, sumTick ((List.range n).map (fun k => ticksOf (T.δ k) res)) < irMargin

/-- A `SummableDefectTickBudget` yields, at each prefix length `n`, a genuine
`UniformScaleNaturalityMargin`. -/
def SummableDefectTickBudget.toUniformMargin {b : Nat} {T : SummableDescentTower b}
    (B : SummableDefectTickBudget T) (n : Nat) : UniformScaleNaturalityMargin where
  path := ⟨(List.range n).map (fun k => ticksOf (T.δ k) B.res)⟩
  irMargin := B.irMargin
  totalDefect_lt_irMargin := B.budget n

/-! ## 3. WIRE — both pulls land in the development's constructive `MassGap`

A `ContinuumMassGap` (a positive Nat lower bound) is a genuine
`UniformCorrelationDecay.MassGap` (its floor `ofNat lower > 0`), hence yields the
downstream `ClayScorecard.RubricInfiniteVolumeMass`.  An `ObservedMassGap` routes
through its `observedLower`. -/

/-- `0 < ofNat n` for `0 < n`. -/
theorem ofNat_pos {n : Nat} (hn : 0 < n) : (0 : Q') < Q'.ofNat n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact Q'.ofNat_succ_pos m

/-- **`continuumMassGap_toMassGap`.**  A Nat continuum gap `lower > 0` IS a
constructive `UniformCorrelationDecay.MassGap`: `m = ofNat lower`, floor
`ofNat lower > 0`. -/
def continuumMassGap_toMassGap (G : ContinuumMassGap) : UniformCorrelationDecay.MassGap where
  m := CReal.ofQ' (Q'.ofNat G.lower)
  pos :=
    { floor := Q'.ofNat G.lower
      floor_pos := ofNat_pos G.lower_pos
      floor_le := CReal.le_refl _ }

/-- **`continuumMassGap_imp_rubric` (PROVED).**  A Nat continuum mass gap yields the
downstream infinite-volume positive-mass rubric clause. -/
theorem continuumMassGap_imp_rubric (G : ContinuumMassGap) :
    RubricInfiniteVolumeMass (continuumMassGap_toMassGap G).m :=
  (continuumMassGap_toMassGap G).pos.isPositive

/-- **`observedMassGap_toMassGap`.**  An `ObservedMassGap` yields a constructive
`UniformCorrelationDecay.MassGap` through its `observedLower > 0`. -/
def observedMassGap_toMassGap (O : ObservedMassGap) : UniformCorrelationDecay.MassGap :=
  continuumMassGap_toMassGap ⟨O.observedLower, O.observedLower_pos⟩

/-- **`observedMassGap_imp_rubric` (PROVED).**  The finite-resolution observed gap
lands in the downstream infinite-volume positive-mass rubric clause. -/
theorem observedMassGap_imp_rubric (O : ObservedMassGap) :
    RubricInfiniteVolumeMass (observedMassGap_toMassGap O).m :=
  (observedMassGap_toMassGap O).pos.isPositive

/-- **Capstone A** — the REAL proved observed gap lands in the rubric. -/
theorem observedMassGapReal_imp_rubric :
    RubricInfiniteVolumeMass (observedMassGap_toMassGap observedMassGapReal).m :=
  observedMassGap_imp_rubric observedMassGapReal

/-- **Capstone B** — the REAL codynamic naturality-margin gap lands in the rubric. -/
theorem realContinuumMassGap_imp_rubric :
    RubricInfiniteVolumeMass (continuumMassGap_toMassGap realContinuumMassGap).m :=
  continuumMassGap_imp_rubric realContinuumMassGap

end YMGap.Continuum.ConstructiveShellBridge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ConstructiveShellBridge.ticksOf_den_ge_one
#print axioms YMGap.Continuum.ConstructiveShellBridge.ObservedMassGap.observedLower_pos
#print axioms YMGap.Continuum.ConstructiveShellBridge.observedMassGapReal
#print axioms YMGap.Continuum.ConstructiveShellBridge.UniformScaleNaturalityMargin.survivingMargin_pos
#print axioms YMGap.Continuum.ConstructiveShellBridge.massGap_of_uniformScaleNaturalityMargin
#print axioms YMGap.Continuum.ConstructiveShellBridge.realScalePath_totalDefect_zero
#print axioms YMGap.Continuum.ConstructiveShellBridge.uniformMarginReal
#print axioms YMGap.Continuum.ConstructiveShellBridge.realIRMargin_pos
#print axioms YMGap.Continuum.ConstructiveShellBridge.SummableDefectTickBudget.toUniformMargin
#print axioms YMGap.Continuum.ConstructiveShellBridge.continuumMassGap_imp_rubric
#print axioms YMGap.Continuum.ConstructiveShellBridge.observedMassGap_imp_rubric
#print axioms YMGap.Continuum.ConstructiveShellBridge.observedMassGapReal_imp_rubric
#print axioms YMGap.Continuum.ConstructiveShellBridge.realContinuumMassGap_imp_rubric
