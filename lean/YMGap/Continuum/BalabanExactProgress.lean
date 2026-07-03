/-
Track B1 (Balaban) — REBASING the codynamic exact identification off the fixed
`s = 1` majorant, and the resulting HONEST reduction of the FULL-model codynamic
gap to the SINGLE spectral-localization datum.

# The object under attack

`CodynamicGap.CodynamicExactIdentification.dominates` requires the EXACT physical
per-scale loss to be bounded by `renDefect afr pMult (k₀+k)` — the `s = 1`
(dominant-mode) pointwise defect ONLY.  The reduction `codynamic_gap_of_exact`
that consumes it is MAJORANT-AGNOSTIC: it uses `dominates` solely to bound partial
sums termwise by the proved budget `tailBudget = 72/145`, and `tailBudget < 3/4`.

# The refutation (honest, conditional)

Under the honest instantiation `exactLoss k = ∑_s μ(w_k,s)·modeDefect(w_k,s)` (the
plain μ-weighted ALL-mode per-scale loss), `dominates` is FALSE: `BulkModeCrux`
gives a `w`-independent bulk FLOOR `deltaRen ≥ 1/128` on the window
`s ∼ 1/√(1−w)` carrying `O(1)` normalized mass, so the honest all-mode loss is
`Θ(1)` per step while `renDefect` is `Θ((1−w)²)`.  The single in-tree inhabitant
(`CodynamicHierarchical`) sets `exactLoss = 0`, genuine only on the hierarchical
lattice.  This is the `FullModeTowerSummable`-FALSE result: the plain tower
`∑_s modeDefect ∼ ∑ s³` diverges under the `s = 1` scheme.

# The correct replacement — rebasing onto ANY summable majorant

The refutation kills only the plain-norm bookkeeping.  Since the reduction is
majorant-agnostic, we GENERALIZE `dominates` from the fixed `s = 1` majorant to
ANY majorant sequence `B` carrying a proved uniform partial-sum budget `β < 3/4`
(`MajorantIdentification`).  Then the Q'-level `BudgetObj`/`ClosureWitness` engine
fires UNCHANGED (`majorant_gap`).  Two instances are built:

  * `ofCodynamicExact` — the OLD `s = 1` route as a special case (majorant =
    `renDefect`-tail, budget = `tailBudget = 72/145`).  So the generalization
    strictly SUBSUMES `codynamic_gap_of_exact` (`ofCodynamicExact_gap_eq`).
  * `gradedMajorantIdentification` — the NEW route: majorant = the `C₄`-GRADED
    (inverse-Casimir / Sobolev `H^{-2}`) bond-moving budget along the AF
    trajectory (`GradedBondMovingBudget.gradedFullModeDefect`), which the grading
    makes UNIFORMLY `O((1−w)²)` and SUMMABLE (`GradedTowerSummable`).  Domination
    is exactly the spectral-localization datum
    `SpectralLocalization.hlocalize` — the bulk modes lie ABOVE the gap, so their
    `Θ(1)` defect does not feed the first-excited level.

# The two engine-bridge gaps CLOSED here (genuine numeric work, not wiring)

The honest verdict flagged that the graded route (a) lived only at the CReal
product-floor level, and (b) had NO `< 3/4` budget-fit and NO tail cutoff — the
graded constant `fmAconst = Cmass·rateScaled²` carries a FREE `Cmass`.  Both are
resolved here WITHIN the Q' engine:

  * `const_unit_le_half` / `fmAconst_pot_le_half` — for ANY `FullModeDefect` and
    the graded tail cutoff `K = 2·fmAconst.num.toNat`, the graded budget
    `fmAconst·pot 2 K = fmAconst/(K+1) ≤ 1/2 < 3/4`.  This is the missing
    Q'-level graded budget-fit — a `finSum`-from-0-with-tail-cutoff analogue of
    `tailBudget_lt_initial`, closing gap (b) uniformly in the free `Cmass`.
  * The graded route now feeds the SAME Q' `BudgetObj` engine as the `s = 1`
    route (via `MajorantIdentification`), so no CReal↔Q' adapter is needed —
    closing gap (a).

# The net reduction

`gradedCodynamicGap` : the FULL-model codynamic gap is a genuine `ClosureWitness`
whose ONLY open input is `SpectralLocalization` (carrying `hlocalize`).  The
obstruction is converted summability→spectral, and the summability side + the
`< 3/4` budget-fit are BOTH fully proved.  The load-bearing residual is exactly
`SpectralLocalization.hlocalize` (= `bulkCtrl`, the `p ≥ 2` vacuum-normalized bulk
eigenvalue-shift / discrete SU(2) fusion local-CLT), which remains OPEN and is NOT
inhabited here.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` composition over already-proved engines; `Type`-level witnesses
only.  Every load-bearing declaration is gated with `#print axioms` (permitted:
`propext` / `Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Categorical.CodynCat
import YMGap.Continuum.CodynamicGap
import YMGap.Continuum.GradedBondMovingBudget
import YMGap.Continuum.FullModeAssembly

namespace YMGap.Continuum.BalabanExactProgress

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Categorical
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.GradedBondMovingBudget

/-! ## 0. Small self-contained `Q'` / sum helpers -/

/-- `μ < λ → 0 < λ − μ` (positivity of the budget excess).  Inlined to avoid a
heavy cross-import; same proof as `ClusteringImpliesGap.sub_pos_of_lt`. -/
theorem sub_pos_of_lt {μ lam : Q'} (h : μ < lam) : (0 : Q') < lam - μ := by
  apply CReal.pos_of_num_pos
  have hμlt : μ.num * (lam.den : Int) < lam.num * (μ.den : Int) := h
  show (0 : Int) < lam.num * (μ.den : Int) + (-μ).num * (lam.den : Int)
  have hneg : (-μ).num * (lam.den : Int) = -(μ.num * (lam.den : Int)) := by
    show (-μ.num) * (lam.den : Int) = -(μ.num * (lam.den : Int))
    rw [Int.neg_mul]
  rw [hneg]
  omega

/-- `finSum (fun k => f (K+k)) N = tailSum f K N` — the shifted partial sum equals
the tail sum (identical recursion; same induction as
`CodynamicGap.finSum_tailDegradation_eq`). -/
theorem finSum_shift_eq (f : Nat → Q') (K : Nat) :
    ∀ N, finSum (fun k => f (K + k)) N = tailSum f K N
  | 0 => rfl
  | N + 1 => by
    show finSum (fun k => f (K + k)) N + f (K + N)
        = tailSum f K N + f (K + N)
    rw [finSum_shift_eq f K N]

/-! ## 1. `const · (1/m) ≤ 1/2` — the generic graded budget-fit numeric lemma -/

/-- **The generic head-cutoff bound.**  For any nonnegative `a` and any `m` with
`2·a.num.toNat ≤ m`, `a·(1/m) ≤ 1/2`.  (Cross product `a.num·2 ≤ a.den·m`, from
`a.num·2 = 2·a.num.toNat ≤ m ≤ a.den·m`.)  This is the reusable engine behind the
graded `< 3/4` budget-fit. -/
theorem const_unit_le_half {a : Q'} (hnn : (0 : Q') ≤ a) {m : Nat} (hm : 0 < m)
    (hbound : 2 * a.num.toNat ≤ m) : a * unit m hm ≤ HalfPow.half := by
  have hAnum : 0 ≤ a.num := (Q'.zero_le_iff_num_nonneg _).mp hnn
  show (a * unit m hm).num * (HalfPow.half.den : Int)
      ≤ HalfPow.half.num * ((a * unit m hm).den : Int)
  have hhn : HalfPow.half.num = 1 := rfl
  have hhd : (HalfPow.half.den : Int) = 2 := rfl
  rw [hhn, hhd, Int.one_mul]
  have hLn : (a * unit m hm).num = a.num := by
    show a.num * (unit m hm).num = a.num
    rw [unit_num, Int.mul_one]
  have hLd : ((a * unit m hm).den : Int) = (a.den : Int) * (m : Int) := by
    rw [Q'.mul_den_cast, unit_den]
  rw [hLn, hLd]
  have htoNat : ((a.num.toNat : Nat) : Int) = a.num := Int.toNat_of_nonneg hAnum
  have hden1 : (1 : Int) ≤ (a.den : Int) := by
    have := a.den_pos; exact_mod_cast this
  have hstepA : a.num * 2 ≤ (m : Int) := by
    have hc' : ((2 * a.num.toNat : Nat) : Int) ≤ (m : Int) := by exact_mod_cast hbound
    have heqI : ((2 * a.num.toNat : Nat) : Int) = a.num * 2 := by push_cast [htoNat]; omega
    rw [heqI] at hc'; exact hc'
  have hmpos : (0 : Int) ≤ (m : Int) := by exact_mod_cast Nat.zero_le _
  have hstepB : (m : Int) ≤ (a.den : Int) * (m : Int) := by
    have := Int.mul_le_mul_of_nonneg_right hden1 hmpos
    rwa [Int.one_mul] at this
  exact Int.le_trans hstepA hstepB

/-- The graded tail cutoff `K = 2·fmAconst.num.toNat` for a full-mode defect. -/
def gradedFitCutoff (afr : AFRateModulus) (fm : FullModeDefect afr) : Nat :=
  2 * (fmAconst afr fm).num.toNat

/-- **The graded `< 1/2` budget-fit.**  For any `FullModeDefect`, the graded tail
budget `fmAconst·pot 2 K = fmAconst/(K+1)` at the cutoff `K = gradedFitCutoff`
satisfies `≤ 1/2`.  Since `pot 2 K = 1/(K+1) = unit (K+1)` and `2·fmAconst.num.toNat
= K ≤ K+1`, this is `const_unit_le_half`.  Closes the missing graded budget-fit
UNIFORMLY in the free `Cmass` inside `fmAconst`. -/
theorem fmAconst_pot_le_half (afr : AFRateModulus) (fm : FullModeDefect afr) :
    fmAconst afr fm * pot 2 (by decide) (gradedFitCutoff afr fm) ≤ HalfPow.half := by
  -- `pot 2 K` is defeq `unit (K + 2 - 1) = unit (K+1)`; apply the generic lemma.
  have hbound : 2 * (fmAconst afr fm).num.toNat ≤ gradedFitCutoff afr fm + 1 := by
    show 2 * (fmAconst afr fm).num.toNat ≤ 2 * (fmAconst afr fm).num.toNat + 1
    omega
  exact const_unit_le_half (fmAconst_nonneg afr fm)
    (m := gradedFitCutoff afr fm + 1) (by omega) hbound

/-- `1/2 < 3/4` — the head-room for the graded budget-fit. -/
theorem half_lt_gap : HalfPow.half < su2CasimirGap := by decide

/-! ## 2. The generalized (majorant-agnostic) exact identification -/

/-- **The rebased exact identification.**  Generalizes
`CodynamicGap.CodynamicExactIdentification`: instead of the fixed `s = 1` majorant
`renDefect`, it carries an ARBITRARY majorant sequence `majorant` with a proved
uniform partial-sum budget `majorantBudget` and the budget-fit
`majorantBudget < 3/4`.  The `dominates` field bounds the exact per-scale loss by
this majorant.  The `s = 1` route and the `C₄`-graded route are both instances. -/
structure MajorantIdentification : Type where
  /-- The EXACT physical per-scale gap-loss sequence. -/
  exactLoss : Nat → Q'
  /-- Each exact loss is nonnegative (a genuine loss factor). -/
  exactLoss_nonneg : ∀ k, (0 : Q') ≤ exactLoss k
  /-- The chosen summable majorant. -/
  majorant : Nat → Q'
  /-- Its uniform partial-sum budget. -/
  majorantBudget : Q'
  /-- The majorant's partial sums are bounded by the budget. -/
  majorant_summable : ∀ N, finSum majorant N ≤ majorantBudget
  /-- **The budget-fit** (`< 3/4 = su2CasimirGap`): the analogue of
  `tailBudget_lt_initial`, generalized to the chosen majorant. -/
  budget_fit : majorantBudget < su2CasimirGap
  /-- **THE OPEN CONTENT.**  The chosen majorant dominates the exact per-scale
  loss at every scale. -/
  dominates : ∀ k, exactLoss k ≤ majorant k

/-- The flow budget object built from a `MajorantIdentification`: the exact loss
as degradation, the chosen budget, and the `3/4` room.  Its `budget_summable`
chains termwise domination (`dominates`) with the majorant's own summability. -/
def majorantFlowBudget (E : MajorantIdentification) : BudgetObj where
  degradation := E.exactLoss
  initial_bound := su2CasimirGap
  budget := E.majorantBudget
  budget_summable := fun N =>
    Q'.le_trans' _ _ _
      (CharacterTail.finSum_le_termwise E.exactLoss E.majorant E.dominates N)
      (E.majorant_summable N)

/-- The surviving gap `g = 3/4 − majorantBudget`. -/
def majorantSurvivingGap (E : MajorantIdentification) : Q' :=
  su2CasimirGap - E.majorantBudget

/-- `0 < majorantSurvivingGap` — from the budget-fit. -/
theorem majorantSurvivingGap_pos (E : MajorantIdentification) :
    (0 : Q') < majorantSurvivingGap E :=
  sub_pos_of_lt E.budget_fit

/-- **THE REDUCTION (PROVED, given the majorant identification).**  From ANY
`MajorantIdentification` `E`, the exact-flow codynamic gap survives: the surviving
gap `g = 3/4 − majorantBudget > 0` is a genuine `ClosureWitness`.  Fires the
Q'-level `BudgetObj` engine UNCHANGED — the exact generalization of
`codynamic_gap_of_exact`, now majorant-agnostic. -/
def majorant_gap (E : MajorantIdentification) :
    ClosureWitness (majorantFlowBudget E) :=
  ⟨majorantSurvivingGap E, majorantSurvivingGap_pos E, by
    show (majorantFlowBudget E).budget + majorantSurvivingGap E
        ≤ (majorantFlowBudget E).initial_bound
    show E.majorantBudget + (su2CasimirGap - E.majorantBudget) ≤ su2CasimirGap
    exact Q'.ge_of_eqv (Q'.add_sub_cancel_eqv su2CasimirGap E.majorantBudget)⟩

/-- The exact codynamic gap (given `E`) is strictly positive. -/
theorem majorant_gap_pos (E : MajorantIdentification) :
    (0 : Q') < (majorant_gap E).1 :=
  (majorant_gap E).2.1

/-- The exact codynamic gap survives EVERY flow truncation
(`ClosureWitness.terminal`): `∑_{k<N} exactLoss_k + g ≤ 3/4`. -/
theorem majorant_gap_terminal (E : MajorantIdentification) (N : Nat) :
    finSum (majorantFlowBudget E).degradation N + (majorant_gap E).1
      ≤ (majorantFlowBudget E).initial_bound :=
  (majorant_gap E).terminal N

/-! ## 3. The `s = 1` route as an instance (strict subsumption) -/

/-- **The old `s = 1` route as a `MajorantIdentification`.**  Majorant = the
`renDefect`-tail `tailDegradation`, budget = `tailBudget = 72/145`, budget-fit =
`tailBudget_lt_initial`.  Domination is exactly `CodynamicExactIdentification`'s
own `dominates`. -/
def ofCodynamicExact (E : CodynamicGap.CodynamicExactIdentification) :
    MajorantIdentification where
  exactLoss := E.exactLoss
  exactLoss_nonneg := E.exactLoss_nonneg
  majorant := CodynamicGap.tailDegradation
  majorantBudget := CodynamicGap.tailBudget
  majorant_summable := CodynamicGap.tailDegradation_summable
  budget_fit := CodynamicGap.tailBudget_lt_initial
  dominates := E.dominates

/-- **Strict subsumption.**  The gap produced by the generalized reduction on the
`s = 1` instance is IDENTICAL (same value `3/4 − 72/145`) to the original
`codynamic_gap_of_exact`.  So `MajorantIdentification` genuinely generalizes the
`CodynamicExactIdentification` route without loss. -/
theorem ofCodynamicExact_gap_eq (E : CodynamicGap.CodynamicExactIdentification) :
    (majorant_gap (ofCodynamicExact E)).1 = (CodynamicGap.codynamic_gap_of_exact E).1 :=
  rfl

/-! ## 4. The `C₄`-graded route — the FULL-model reduction to `hlocalize` -/

/-- The graded full-mode defect of a spectral-localization datum (the majorant). -/
def gradedFm (afr : AFRateModulus) (N₀ : Nat)
    (sl : SpectralLocalization afr N₀) : FullModeDefect afr :=
  gradedFullModeDefect afr N₀ sl.traj

/-- The graded tail cutoff for that datum. -/
def gradedCutoff (afr : AFRateModulus) (N₀ : Nat)
    (sl : SpectralLocalization afr N₀) : Nat :=
  gradedFitCutoff afr (gradedFm afr N₀ sl)

/-- **The graded `MajorantIdentification`.**  The rebasing target: majorant = the
`C₄`-GRADED bond-moving budget along the AF trajectory (tail-shifted past the
graded cutoff), which the grading makes summable (`fmDefect_summable` /
`GradedTowerSummable`); budget = `fmAconst·pot 2 K ≤ 1/2 < 3/4`
(`fmAconst_pot_le_half`); domination = the spectral-localization input
`SpectralLocalization.hlocalize`.  The FALSE `s = 1` summability obligation is
replaced by the (open but sharper) SPECTRAL datum — and NOTHING else remains. -/
def gradedMajorantIdentification (afr : AFRateModulus) (N₀ : Nat)
    (sl : SpectralLocalization afr N₀) : MajorantIdentification where
  exactLoss := fun k => sl.gapDefect (gradedCutoff afr N₀ sl + k)
  exactLoss_nonneg := fun k => sl.gapDefect_nonneg (gradedCutoff afr N₀ sl + k)
  majorant := fun k => (gradedFm afr N₀ sl).d (gradedCutoff afr N₀ sl + k)
  majorantBudget :=
    fmAconst afr (gradedFm afr N₀ sl) * pot 2 (by decide) (gradedCutoff afr N₀ sl)
  majorant_summable := fun N => by
    rw [finSum_shift_eq (gradedFm afr N₀ sl).d (gradedCutoff afr N₀ sl) N]
    exact fmDefect_summable afr (gradedFm afr N₀ sl) (gradedCutoff afr N₀ sl) N
  budget_fit :=
    Q'.lt_of_le_of_lt (fmAconst_pot_le_half afr (gradedFm afr N₀ sl)) half_lt_gap
  dominates := fun k => sl.hlocalize (gradedCutoff afr N₀ sl + k)

/-- **THE FULL-MODEL CODYNAMIC GAP (given `SpectralLocalization`).**  A genuine
`ClosureWitness`: the surviving gap `g = 3/4 − fmAconst·pot 2 K > 0` for the
graded-budget flow.  Its ONLY open input is the `SpectralLocalization` datum
`sl` (carrying `hlocalize`).  The summability side and the `< 3/4` budget-fit are
BOTH fully proved; the summability→spectral conversion is complete. -/
def gradedCodynamicGap (afr : AFRateModulus) (N₀ : Nat)
    (sl : SpectralLocalization afr N₀) :
    ClosureWitness (majorantFlowBudget (gradedMajorantIdentification afr N₀ sl)) :=
  majorant_gap (gradedMajorantIdentification afr N₀ sl)

/-- The full-model codynamic gap is strictly positive (given `sl`). -/
theorem gradedCodynamicGap_pos (afr : AFRateModulus) (N₀ : Nat)
    (sl : SpectralLocalization afr N₀) :
    (0 : Q') < (gradedCodynamicGap afr N₀ sl).1 :=
  majorant_gap_pos (gradedMajorantIdentification afr N₀ sl)

/-- The full-model codynamic gap survives EVERY flow truncation (given `sl`). -/
theorem gradedCodynamicGap_terminal (afr : AFRateModulus) (N₀ : Nat)
    (sl : SpectralLocalization afr N₀) (N : Nat) :
    finSum (majorantFlowBudget (gradedMajorantIdentification afr N₀ sl)).degradation N
        + (gradedCodynamicGap afr N₀ sl).1
      ≤ (majorantFlowBudget (gradedMajorantIdentification afr N₀ sl)).initial_bound :=
  majorant_gap_terminal (gradedMajorantIdentification afr N₀ sl) N

/-! ## 5. The honest ledger (English)

  1. The FIXED `s = 1` majorant `dominates` is FALSE for the honest all-mode loss
     (`BulkModeCrux` bulk floor `1/128`; `FullModeTowerSummable`-FALSE).  Only the
     `exactLoss = 0` hierarchical dodge inhabits it.

  2. The reduction is MAJORANT-AGNOSTIC, so we rebase: `MajorantIdentification`
     accepts ANY summable majorant with budget `< 3/4`.  `majorant_gap` fires the
     same Q' `BudgetObj`/`ClosureWitness` engine (`ofCodynamicExact_gap_eq`: the
     `s = 1` route is recovered exactly).

  3. The correct majorant is the `C₄`-GRADED (inverse-Casimir / `H^{-2}`)
     bond-moving budget: the grading divides the `Θ(1)` bulk floor by `C₄² ∼
     1/(1−w)²`, making it UNIFORMLY `O((1−w)²)` and summable.  Two engine-bridge
     gaps are CLOSED here in Q': (a) the graded route now feeds the same Q' engine
     (no CReal adapter); (b) `fmAconst_pot_le_half` supplies the missing `< 3/4`
     budget-fit with a genuine tail cutoff, UNIFORMLY in the free `Cmass`.

  4. NET: `gradedCodynamicGap` — the FULL-model codynamic gap is a genuine
     `ClosureWitness` whose SOLE open input is `SpectralLocalization` (carrying
     `hlocalize` = `bulkCtrl`, the `p ≥ 2` vacuum-normalized bulk eigenvalue-shift
     / discrete SU(2) fusion local-CLT).  That datum is OPEN and NOT inhabited
     here.  The obstruction is converted summability→spectral, correctly and
     sharper; nothing is faked. -/

end YMGap.Continuum.BalabanExactProgress

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BalabanExactProgress.sub_pos_of_lt
#print axioms YMGap.Continuum.BalabanExactProgress.finSum_shift_eq
#print axioms YMGap.Continuum.BalabanExactProgress.const_unit_le_half
#print axioms YMGap.Continuum.BalabanExactProgress.fmAconst_pot_le_half
#print axioms YMGap.Continuum.BalabanExactProgress.half_lt_gap
#print axioms YMGap.Continuum.BalabanExactProgress.majorantFlowBudget
#print axioms YMGap.Continuum.BalabanExactProgress.majorantSurvivingGap_pos
#print axioms YMGap.Continuum.BalabanExactProgress.majorant_gap
#print axioms YMGap.Continuum.BalabanExactProgress.majorant_gap_pos
#print axioms YMGap.Continuum.BalabanExactProgress.majorant_gap_terminal
#print axioms YMGap.Continuum.BalabanExactProgress.ofCodynamicExact
#print axioms YMGap.Continuum.BalabanExactProgress.ofCodynamicExact_gap_eq
#print axioms YMGap.Continuum.BalabanExactProgress.gradedMajorantIdentification
#print axioms YMGap.Continuum.BalabanExactProgress.gradedCodynamicGap
#print axioms YMGap.Continuum.BalabanExactProgress.gradedCodynamicGap_pos
#print axioms YMGap.Continuum.BalabanExactProgress.gradedCodynamicGap_terminal
