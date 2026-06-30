/-
Track B / R2 — THE `C₄`-GRADED (inverse-Casimir / Sobolev `H^{-2}`) bond-moving
budget, and the HONEST reduction of the bulk obstruction to a SPECTRAL (not a
summability) input.

# The obstruction this module dissolves — and the precise honesty of it

`BulkModeCrux` proved the SHARP negative result for the plain heat-kernel-scaled
norm: on the bulk window `s ∼ 1/√(1−w)` the per-mode renormalized defect
`deltaRen w s = C₄(s)·(1−w) − (1 − w^{C₄(s)})` has a `w`-independent FLOOR
`deltaRen ≥ 1/128` (`BulkModeCrux.deltaRen_floor`), so the `μ`-weighted bulk sum
does NOT vanish as `w → 1` (`BulkModeCrux.bulkObstruction_floor`).  Per-`s`
heat-kernel reweighting is insufficient because `μ` normalizes MASS but does not
down-weight the DEFECT where the mass concentrates.

The diagnosed cure (read off in `BulkModeCrux`) is a `C₄(s)`-GRADED norm that
DIVIDES the per-mode residual by `C₄(s)²` — a genuine inverse-Casimir / Sobolev
`H^{-2}` retuning, NOT a multiplicative test factor (`qfac` ALONE fails: at
`τ·C₄(s) ∼ 1` it is itself `Θ(1)`).  This module BUILDS that graded budget and
proves the UNIFORM quadratic bound the plain norm lacked, then isolates EXACTLY
what makes the weak (graded) norm legitimate for the gap.

# What is PROVED here (genuine `Q'`/`Nat`, axiom-clean)

  * `gradedDefect w s` — the graded per-mode defect on the EXCITED mode `s+1`
    (the vacuum `s = 0` carries no defect, `deltaRen w 0 = 0`):
        gradedDefect w s  =  deltaRen w (s+1) / C₄(s+1)²        (`divPos`, `C₄>0`).
  * **`gradedDefect_le`** (THE KEY UNIFORM BOUND).  `gradedDefect w s ≤ (1−w)²`,
    UNIFORMLY in `s` — directly from `BulkModeCrux.deltaRen_upper`
    (`deltaRen ≤ C₄(s)²·(1−w)²`).  This is the uniform-quadratic bound the plain
    `μ`-norm could not produce: the `Θ(1)` bulk floor is divided away by `C₄²`.
  * `gradedBudget w N` / `massNorm w N` and **`gradedBudget_le`** — the graded
    budget `∑_{s<N} μ(s+1)·gradedDefect w s ≤ (1−w)²·massNorm`, with `massNorm`
    the normalized EXCITED mass.  `O((1−w)²)` per step — SUMMABLE along the AF
    trajectory `1−w_k ∼ 1/k` (`∑ 1/k² < ∞`).
  * `GradedTrajectory` / `gradedBudget_quad` / **`GradedTowerSummable`** — packages
    the per-step quadratic-in-margin bound `gradedBudget(w_k) ≤ Cmass·(1−w_k)²`
    into a `FullModeDefect`, whose `fmDefect_summable` gives the bounded dyadic
    tail-sums (the trajectory-sum convergence).  THE GRADED TOWER IS SUMMABLE.
  * **`SpectralLocalization` + `spectralLocalization_gap`** — THE HONEST REDUCTION.
    A `Type`-level interface carrying the one remaining input — the SPECTRAL fact
    that the transfer-operator gap is controlled by the bond-moving defect ONLY
    through its `C₄`-graded (low-mode-weighted) norm (equivalently: the bulk modes
    `s ∼ 1/√(1−w)` lie ABOVE the gap, so their `Θ(1)` defect does not lower the
    first-excited `s = 1` level).  From it the chain delivers a STRICTLY POSITIVE
    product floor.  `SpectralLocalization` is NOT inhabited here: it is the sharper
    open input — but a SPECTRAL statement, not a divergent-sum statement.
  * `gradedDefect_anchor` / `bondMovingDeltaRen_eq_core` — the budget is anchored
    at the physical first-excited mode: `gradedDefect w 0 · C₄(1)² ≃ deltaRen w 1`,
    and `deltaRen w 1` is EXACTLY the `s = 1` core that
    `BondMovingQuadratic.bondMovingDeltaRen` wraps and proves QUADRATIC.  The
    gap-relevant mode IS quadratic; the budget is non-vacuous.

# The verdict — the obstruction is now SPECTRAL, not summability

The plain-norm bulk floor (`BulkModeCrux`) was a SUMMABILITY obstruction: the
`μ`-weighted defect did not tend to `0`.  The `C₄²`-grading REMOVES it: the graded
budget is uniformly `O((1−w)²)`, SUMMABLE, and assembles into a positive product
floor.  What remains — `SpectralLocalization` — is a SPECTRAL-LOCALIZATION
statement about the transfer operator (the low modes control the gap), NOT a
statement about a divergent sum.  This is a strictly sharper, lower-dimensional
open input than the failed plain-norm route.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and composition over already-proved engines; every
load-bearing declaration is gated with `#print axioms` (permitted: `propext` /
`Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses
(the graded defect, the budget, the trajectory and spectral interfaces) are
`Type`-level data.
-/

import YMGap.Continuum.BondMovingQuadratic
import YMGap.Continuum.BondMovingScaledNorm
import YMGap.Continuum.BulkModeCrux
import YMGap.Continuum.GenuineResidualDefect

namespace YMGap.Continuum.GradedBondMovingBudget

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.BulkModeCrux
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.SummableInverseSquare

/-! ## 0. Positivity of the Casimir-square grading denominator -/

/-- `C₄(s+1) > 0`: the excited-mode Casimir is strictly positive
(`C₄(s+1) = (s+1)·(s+3) ≥ 3`). -/
theorem c4_succ_pos (s : Nat) : 0 < c4 (s + 1) := by
  show 0 < (s + 1) * (s + 1 + 2)
  exact Nat.mul_pos (Nat.succ_pos s) (by omega)

/-- `0 < ofNat n` for `0 < n`. -/
theorem ofNat_pos_of_pos {n : Nat} (hn : 0 < n) : (0 : Q') < Q'.ofNat n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact Q'.ofNat_succ_pos m

/-- **The grading denominator `C₄(s+1)² > 0`** (guards the per-mode division). -/
theorem c4sq_succ_pos (s : Nat) :
    (0 : Q') < Q'.ofNat (c4 (s + 1)) * Q'.ofNat (c4 (s + 1)) :=
  Q'.mul_pos (ofNat_pos_of_pos (c4_succ_pos s)) (ofNat_pos_of_pos (c4_succ_pos s))

/-! ## 1. The `C₄`-graded per-mode defect and its UNIFORM quadratic bound -/

/-- **The `C₄(s)`-graded (inverse-Casimir / Sobolev `H^{-2}`) per-mode defect** on
the EXCITED mode `s+1` (the vacuum `s = 0` carries no defect, `deltaRen w 0 = 0`):

    gradedDefect w s  =  deltaRen w (s+1) / C₄(s+1)²,

the renormalized bond-moving residual DIVIDED by the full Casimir square — the
genuine mode-graded retuning that the plain heat-kernel weight `μ` lacked. -/
def gradedDefect (w : Q') (s : Nat) : Q' :=
  Q'.divPos (deltaRen w (s + 1))
    (Q'.ofNat (c4 (s + 1)) * Q'.ofNat (c4 (s + 1))) (c4sq_succ_pos s)

/-- **THE KEY UNIFORM-QUADRATIC BOUND.**  On `[0,1]`,

    gradedDefect w s  ≤  (1 − w)²,        UNIFORMLY in `s`.

This is the bound the plain `μ`-norm could NOT produce.  `BulkModeCrux` showed the
ungraded per-mode defect has a `w`-independent FLOOR `≥ 1/128` on the bulk window
`s ∼ 1/√(1−w)`; dividing by `C₄(s)²` (where `C₄(s) ∼ 1/(1−w)` on that window)
collapses the `Θ(1)` floor to the uniform quadratic `(1−w)²`.  PROOF: directly
from `BulkModeCrux.deltaRen_upper` (`deltaRen ≤ C₄(s)²·(1−w)²`) via the quotient
upper bound `divPos_le_of_le_mul`. -/
theorem gradedDefect_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (s : Nat) :
    gradedDefect w s ≤ ((1 : Q') - w) * ((1 : Q') - w) := by
  refine Q'.divPos_le_of_le_mul (deltaRen w (s + 1))
    (Q'.ofNat (c4 (s + 1)) * Q'.ofNat (c4 (s + 1))) (c4sq_succ_pos s) ?_
  -- deltaRen ≤ (C₄²)·(1−w)²  ≃  (1−w)²·(C₄²)
  have hup : deltaRen w (s + 1)
      ≤ (Q'.ofNat (c4 (s + 1)) * Q'.ofNat (c4 (s + 1)))
          * (((1 : Q') - w) * ((1 : Q') - w)) :=
    deltaRen_upper hw0 hw1 (s + 1)
  exact Q'.le_trans' _ _ _ hup
    (Q'.le_of_eqv (Q'.mul_comm_eqv (Q'.ofNat (c4 (s + 1)) * Q'.ofNat (c4 (s + 1)))
      (((1 : Q') - w) * ((1 : Q') - w))))

/-- The graded defect is nonnegative on `[0,1]` (the renormalized residual is
nonnegative — `BulkModeCrux.deltaRen_lower` bounds it below by a nonneg quantity —
and the grading divides by a positive). -/
theorem gradedDefect_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (s : Nat) : (0 : Q') ≤ gradedDefect w s := by
  have hdr : (0 : Q') ≤ deltaRen w (s + 1) := by
    have hlow : (((1 : Q') - w) * ((1 : Q') - w))
          * (qpow w (c4 (s + 1)) * triSum (c4 (s + 1)))
        ≤ deltaRen w (s + 1) := deltaRen_lower hw0 hw1 (s + 1)
    have hlhs : (0 : Q') ≤ (((1 : Q') - w) * ((1 : Q') - w))
          * (qpow w (c4 (s + 1)) * triSum (c4 (s + 1))) :=
      Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hw1) (Q'.sub_nonneg_of_le hw1))
        (Q'.mul_nonneg _ _ (qpow_nonneg w hw0 (c4 (s + 1))) (triSum_nonneg (c4 (s + 1))))
    exact Q'.le_trans' _ _ _ hlhs hlow
  show (0 : Q') ≤ Q'.divPos (deltaRen w (s + 1))
    (Q'.ofNat (c4 (s + 1)) * Q'.ofNat (c4 (s + 1))) (c4sq_succ_pos s)
  unfold Q'.divPos
  exact Q'.mul_nonneg _ _ hdr (Q'.le_of_lt (Q'.recipPos_pos _ _))

/-! ## 2. The graded budget and its `O((1−w)²)` bound -/

/-- The normalized EXCITED mass `∑_{s<N} μ(s+1)` (the bulk/excited normalized mass;
the vacuum `s = 0`, which carries no defect, is excluded). -/
def massNorm (w : Q') (N : Nat) (hZ : (0 : Q') < Zsum w N) : Q' :=
  RationalTail.finSum (fun s => μ w N hZ (s + 1)) N

theorem massNorm_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (N : Nat)
    (hZ : (0 : Q') < Zsum w N) : (0 : Q') ≤ massNorm w N hZ :=
  FullModeAssembly.finSum_nonneg (fun s => μ_nonneg hw0 N hZ (s + 1)) N

/-- **The `C₄`-graded bond-moving budget** `∑_{s<N} μ(s+1)·gradedDefect w s` — the
heat-kernel-weighted sum of the graded (inverse-Casimir) per-mode defect over the
excited tower. -/
def gradedBudget (w : Q') (N : Nat) (hZ : (0 : Q') < Zsum w N) : Q' :=
  RationalTail.finSum (fun s => μ w N hZ (s + 1) * gradedDefect w s) N

theorem gradedBudget_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) (hZ : (0 : Q') < Zsum w N) : (0 : Q') ≤ gradedBudget w N hZ :=
  FullModeAssembly.finSum_nonneg
    (fun s => Q'.mul_nonneg _ _ (μ_nonneg hw0 N hZ (s + 1))
      (gradedDefect_nonneg hw0 hw1 s)) N

/-- **THE GRADED BUDGET BOUND.**  On `[0,1]`,

    gradedBudget w N  ≤  (1 − w)²·massNorm w N        ( = `O((1−w)²)` ),

so along the asymptotic-freedom trajectory `1 − w_k ∼ 1/k` the graded budget is
`∼ 1/k²` — SUMMABLE (`∑ 1/k² < ∞`), in contrast to the plain-norm bulk floor that
did not even vanish.  PROOF: termwise `μ(s+1)·gradedDefect ≤ (1−w)²·μ(s+1)`
(`gradedDefect_le` × the nonneg weight), then pull the constant `(1−w)²` out of
the finite sum. -/
theorem gradedBudget_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) (hZ : (0 : Q') < Zsum w N) :
    gradedBudget w N hZ ≤ ((1 : Q') - w) * ((1 : Q') - w) * massNorm w N hZ := by
  have hterm : ∀ s,
      μ w N hZ (s + 1) * gradedDefect w s
        ≤ ((1 : Q') - w) * ((1 : Q') - w) * μ w N hZ (s + 1) := by
    intro s
    have hg : gradedDefect w s ≤ ((1 : Q') - w) * ((1 : Q') - w) :=
      gradedDefect_le hw0 hw1 s
    have hμnn : (0 : Q') ≤ μ w N hZ (s + 1) := μ_nonneg hw0 N hZ (s + 1)
    have h1 : μ w N hZ (s + 1) * gradedDefect w s
        ≤ μ w N hZ (s + 1) * (((1 : Q') - w) * ((1 : Q') - w)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hg hμnn
    exact Q'.le_trans' _ _ _ h1
      (Q'.le_of_eqv (Q'.mul_comm_eqv (μ w N hZ (s + 1)) (((1 : Q') - w) * ((1 : Q') - w))))
  have hle : RationalTail.finSum (fun s => μ w N hZ (s + 1) * gradedDefect w s) N
      ≤ RationalTail.finSum
          (fun s => ((1 : Q') - w) * ((1 : Q') - w) * μ w N hZ (s + 1)) N :=
    CharacterTail.finSum_le_termwise _ _ hterm N
  refine Q'.le_trans' _ _ _ hle ?_
  exact Q'.le_of_eqv (Q'.eqv_symm
    (RationalTail.const_mul_finSum (fun s => μ w N hZ (s + 1))
      (((1 : Q') - w) * ((1 : Q') - w)) N))

/-! ## 3. The AF trajectory: graded summability into a `FullModeDefect` -/

/-- **The graded-trajectory data.**  A `Type`-level package along an asymptotic-
freedom rate `afr` (the named two-loop trajectory `1 − w_k ∼ 1/k`): the partition
positivity guard at the fixed cutoff `N₀`, and the UNIFORM bound `Cmass` on the
normalized excited mass `massNorm(w_k)`.  (The excited mass is a normalized density
fraction; its uniform `O(1)` bound is the AF-side mass-comparison input, named here
as data — the GOOD-side analogue of `BulkModeCrux.BulkObstruction.cmass`.) -/
structure GradedTrajectory (afr : AFRateModulus) (N₀ : Nat) : Type where
  /-- Partition positivity at the fixed cutoff. -/
  hZ : ∀ k, (0 : Q') < Zsum (afr.w k) N₀
  /-- The uniform excited-mass bound. -/
  Cmass : Q'
  /-- Its nonnegativity. -/
  Cmass_nonneg : (0 : Q') ≤ Cmass
  /-- The uniform bound on the normalized excited mass at every step. -/
  hmass : ∀ k, massNorm (afr.w k) N₀ (hZ k) ≤ Cmass

/-- **The per-step quadratic-in-margin bound.**  Along a graded trajectory,

    gradedBudget(w_k)  ≤  Cmass·(1 − w_k)²,

the clean `FullModeDefect`-shaped bound: chain `gradedBudget_le`
(`≤ (1−w_k)²·massNorm`) with the uniform mass bound (`massNorm ≤ Cmass`). -/
theorem gradedBudget_quad (afr : AFRateModulus) (N₀ : Nat)
    (gt : GradedTrajectory afr N₀) (k : Nat) :
    gradedBudget (afr.w k) N₀ (gt.hZ k)
      ≤ gt.Cmass * (((1 : Q') - afr.w k) * ((1 : Q') - afr.w k)) := by
  have hw0 : (0 : Q') ≤ afr.w k := afr.w_nonneg k
  have hw1 : afr.w k ≤ (1 : Q') := Q'.le_of_lt (afr.w_lt_one k)
  have hmarnn : (0 : Q') ≤ ((1 : Q') - afr.w k) * ((1 : Q') - afr.w k) :=
    Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hw1) (Q'.sub_nonneg_of_le hw1)
  have h1 : gradedBudget (afr.w k) N₀ (gt.hZ k)
      ≤ ((1 : Q') - afr.w k) * ((1 : Q') - afr.w k) * massNorm (afr.w k) N₀ (gt.hZ k) :=
    gradedBudget_le hw0 hw1 N₀ (gt.hZ k)
  have h2 : ((1 : Q') - afr.w k) * ((1 : Q') - afr.w k) * massNorm (afr.w k) N₀ (gt.hZ k)
      ≤ ((1 : Q') - afr.w k) * ((1 : Q') - afr.w k) * gt.Cmass :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (gt.hmass k) hmarnn
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ h2
      (Q'.le_of_eqv (Q'.mul_comm_eqv (((1 : Q') - afr.w k) * ((1 : Q') - afr.w k)) gt.Cmass)))

/-- **The graded budget as a `FullModeDefect`.**  Package the per-step graded
budget `δ_k = gradedBudget(w_k)` with its clean quadratic bound
`δ_k ≤ Cmass·(1 − w_k)²` (and nonnegativity) — exactly the data the summability /
product-floor machinery consumes. -/
def gradedFullModeDefect (afr : AFRateModulus) (N₀ : Nat)
    (gt : GradedTrajectory afr N₀) : FullModeDefect afr where
  d := fun k => gradedBudget (afr.w k) N₀ (gt.hZ k)
  d_nonneg := fun k =>
    gradedBudget_nonneg (afr.w_nonneg k) (Q'.le_of_lt (afr.w_lt_one k)) N₀ (gt.hZ k)
  M := gt.Cmass
  M_nonneg := gt.Cmass_nonneg
  d_quad := gradedBudget_quad afr N₀ gt

/-- **GRADED TOWER SUMMABLE (the trajectory-sum convergence).**  Every tail window
of the graded budget along the AF trajectory is bounded by the dyadically decaying
`D·1/(N+1)`:

    tailSum (gradedBudget ∘ w) N M  ≤  fmAconst·pot 2 N        ( = D/(N+1) ),

so the partial sums are uniformly bounded and the graded tower is SUMMABLE.  THE
DECISIVE CONTRAST with the plain-norm bulk floor (`BulkObstruction`): there the
per-step defect did not even vanish; here the `C₄²`-grading makes it
`O((1−w_k)²) ∼ 1/k²`, with convergent partial sums.  PROOF: `fmDefect_summable`
on the `gradedFullModeDefect`. -/
theorem GradedTowerSummable (afr : AFRateModulus) (N₀ : Nat)
    (gt : GradedTrajectory afr N₀) (N M : Nat) :
    tailSum (gradedFullModeDefect afr N₀ gt).d N M
      ≤ fmAconst afr (gradedFullModeDefect afr N₀ gt) * pot 2 (by decide) N :=
  fmDefect_summable afr (gradedFullModeDefect afr N₀ gt) N M

/-! ## 4. THE HONEST REDUCTION — the SPECTRAL-LOCALIZATION input -/

/-- **The spectral-localization interface (the new, sharper open input).**

It carries a graded trajectory plus the ONE remaining genuinely-open fact, stated
as `Type`-level data — the SPECTRAL statement that the transfer-operator mass gap
is controlled by the bond-moving defect ONLY through its `C₄`-graded (low-mode-
weighted) norm:

  * `gapDefect k` — the per-block GAP-RELEVANT defect (the quantity that actually
    enters the gap-persistence product), with its nonnegativity.
  * **`hlocalize`** — the spectral input: `gapDefect k ≤ gradedBudget(w_k)`.
    Equivalently: the bulk modes `s ∼ 1/√(1−w)` lie ABOVE the gap, so their `Θ(1)`
    (ungraded) defect does NOT lower the first-excited `s = 1` level — only the
    `C₄`-graded (low-mode) budget feeds the gap.

This is NOT inhabited here: it is the SHARPER open input replacing the failed
plain-norm route.  Crucially it is a SPECTRAL-LOCALIZATION statement about the
operator, NOT a statement about a divergent sum — the summability obstruction of
`BulkModeCrux` has been dissolved by the grading. -/
structure SpectralLocalization (afr : AFRateModulus) (N₀ : Nat) : Type where
  /-- The underlying graded trajectory (uniform excited-mass bound included). -/
  traj : GradedTrajectory afr N₀
  /-- The per-block gap-relevant defect. -/
  gapDefect : Nat → Q'
  /-- Its nonnegativity. -/
  gapDefect_nonneg : ∀ k, (0 : Q') ≤ gapDefect k
  /-- **THE SPECTRAL INPUT** — the gap is controlled through the `C₄`-graded
  (low-mode) budget. -/
  hlocalize : ∀ k, gapDefect k ≤ gradedBudget (afr.w k) N₀ (traj.hZ k)

/-- The `FullModeDefect` whose per-step defect is the gap-relevant `gapDefect`,
quadratically bounded by `Cmass·(1 − w_k)²` through the spectral-localization
input (`gapDefect ≤ gradedBudget ≤ Cmass·(1−w_k)²`). -/
def spectralLocalization_defect (afr : AFRateModulus) (N₀ : Nat)
    (sl : SpectralLocalization afr N₀) : FullModeDefect afr where
  d := sl.gapDefect
  d_nonneg := sl.gapDefect_nonneg
  M := sl.traj.Cmass
  M_nonneg := sl.traj.Cmass_nonneg
  d_quad := fun k =>
    Q'.le_trans' _ _ _ (sl.hlocalize k) (gradedBudget_quad afr N₀ sl.traj k)

/-- **THE REDUCTION — a strictly positive product floor from spectral
localization.**  Given a `SpectralLocalization` (the graded summability `+` the
spectral fact that the gap is controlled by the low-mode graded norm), the running
product of the renormalized per-block rates `ρ_j = 1 − gapDefect(w_{k₀+j})` over
the tail `k ≥ k₀` has a STRICTLY POSITIVE floor: a constructive real `floor` with a
positive rational lower bound `ε > 0` and `floor ≤ ∏_{j<n} ρ_j` for every prefix.

This fires `fullMode_gap_of_AFRate` on the `gapDefect`, whose summability is now
supplied by the `C₄`-GRADED budget (`GradedTowerSummable`) — NOT the divergent
plain-norm bulk sum.  The SOLE remaining hypothesis is the SPECTRAL-LOCALIZATION
input `SpectralLocalization.hlocalize`; it is a spectral statement about the
transfer operator, not a summability statement. -/
def spectralLocalization_gap (afr : AFRateModulus) (N₀ : Nat)
    (sl : SpectralLocalization afr N₀) :
    Σ' (floor : CReal) (ε : Q'),
      (0 : Q') < ε ∧ ExpPos.geRat floor ε
      ∧ ∀ n, CReal.leRat floor
          (RGGapPersistence.prodPrefix
            (fmTailRate afr (spectralLocalization_defect afr N₀ sl)
              (fmCutoff afr (spectralLocalization_defect afr N₀ sl))) n) :=
  fullMode_gap_of_AFRate afr (spectralLocalization_defect afr N₀ sl)

/-! ## 5. The s=1 anchor — the budget is non-vacuous at the first-excited mode -/

/-- **The anchor identity.**  The graded defect at the first excited mode
(`s = 0 ↦` physical mode `s+1 = 1`), multiplied back by its grading `C₄(1)²`,
recovers exactly the `s = 1` renormalized core `deltaRen w 1`:

    gradedDefect w 0 · C₄(1)²  ≃  deltaRen w 1. -/
theorem gradedDefect_anchor (w : Q') :
    (gradedDefect w 0 * (Q'.ofNat (c4 1) * Q'.ofNat (c4 1))).eqv (deltaRen w 1) :=
  Q'.divPos_mul_eqv (deltaRen w (0 + 1))
    (Q'.ofNat (c4 (0 + 1)) * Q'.ofNat (c4 (0 + 1))) (c4sq_succ_pos 0)

/-- **The bond-moving defect is the `s = 1` core.**  `BondMovingQuadratic`'s
renormalized dominant-mode defect is exactly `p·dimQ 1·deltaRen w 1` — the same
`s = 1` core that the graded budget is anchored at (definitional). -/
theorem bondMovingDeltaRen_eq_core (N p : Nat) (w : Q') :
    bondMovingDeltaRen N p w = Q'.ofNat p * (dimQ 1 * deltaRen w 1) := rfl

/-- **The anchored mode IS quadratic.**  The `s = 1` core `deltaRen w 1` — to which
the graded budget is anchored — satisfies the QUADRATIC bound `≤ C₄(1)²·(1−w)²`
(`BulkModeCrux.deltaRen_upper`, the same content `bondMovingDeltaRen_quadratic`
wraps).  So the gap-relevant first-excited mode is genuinely quadratic and the
graded budget is non-vacuous. -/
theorem gradedDefect_anchor_quadratic {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    deltaRen w 1
      ≤ (Q'.ofNat (c4 1) * Q'.ofNat (c4 1)) * (((1 : Q') - w) * ((1 : Q') - w)) :=
  deltaRen_upper hw0 hw1 1

end YMGap.Continuum.GradedBondMovingBudget

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.GradedBondMovingBudget.c4_succ_pos
#print axioms YMGap.Continuum.GradedBondMovingBudget.c4sq_succ_pos
#print axioms YMGap.Continuum.GradedBondMovingBudget.gradedDefect_le
#print axioms YMGap.Continuum.GradedBondMovingBudget.gradedDefect_nonneg
#print axioms YMGap.Continuum.GradedBondMovingBudget.massNorm_nonneg
#print axioms YMGap.Continuum.GradedBondMovingBudget.gradedBudget_nonneg
#print axioms YMGap.Continuum.GradedBondMovingBudget.gradedBudget_le
#print axioms YMGap.Continuum.GradedBondMovingBudget.gradedBudget_quad
#print axioms YMGap.Continuum.GradedBondMovingBudget.gradedFullModeDefect
#print axioms YMGap.Continuum.GradedBondMovingBudget.GradedTowerSummable
#print axioms YMGap.Continuum.GradedBondMovingBudget.spectralLocalization_defect
#print axioms YMGap.Continuum.GradedBondMovingBudget.spectralLocalization_gap
#print axioms YMGap.Continuum.GradedBondMovingBudget.gradedDefect_anchor
#print axioms YMGap.Continuum.GradedBondMovingBudget.bondMovingDeltaRen_eq_core
#print axioms YMGap.Continuum.GradedBondMovingBudget.gradedDefect_anchor_quadratic
