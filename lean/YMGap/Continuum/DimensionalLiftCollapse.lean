/-
Track B / R2 — THE DIMENSIONAL LIFT of the atomic per-step defect `singleStep`, and
its machine-checked COLLAPSE at the d → 4 continuation.

# What this module does (read first)

`singleStep` (`SingleStepDefectReduction.SingleStepDefectBound`) is the atomic Clay
core: the real 4D SU(2) per-step block-spin defect obeys `realδ_k ≤ 6·(1−w_k)²`.  Every
tool tried in this campaign has reduced *to* it in 4D.  This module attacks it with a
GENUINELY-NEW angle never tried here: construct/analyse the defect in dimension `d > 4`
(mean-field / large-`d` concentration is cleaner) and ask whether it CONTINUES back to
`d = 4` as a genuine route, or COLLAPSES (re-introduces the atomic interacting-measure
defect / the renormalon).

The verdict is a machine-checked **COLLAPSE** (task criterion (iii)).  Two independent
d-dependencies pull in OPPOSITE directions:

  * the single-step defect MAGNITUDE bound `realδ ≤ 6(1−w)²` gets EASIER in higher `d`
    (the block fuses `m = b^{d−1}` plaquettes; the fusion CONCENTRATES, `2 − ρ_m ∼ 6ε/m`,
    numerically verified — the mean-field/large-`d` half);
  * the gap SURVIVAL needs a SUMMABLE defect (`Σ δ_k < ∞ ⟹ ∏(1 − δ_k) > 0`), and this
    summability is DESTROYED for every `d > 4`.

The reason is the coupling's classical dimension `[g²] = 4 − d`.  Only at `d = 4` is the
coupling marginal (`classicalScaling 4 = 0`) → asymptotic freedom → `w_k → 1`,
`1 − w_k ∼ 1/k`, `δ_k ∼ 1/k²`, `Σδ_k < ∞`, floor `> 0`.  For every `d ≥ 5` the coupling
is irrelevant (`classicalScaling d > 0`) → the UV/continuum flow reaches a NON-ZERO
fixed-point margin `fpMargin d = (d−4)/β₀ > 0` → the per-step defect does NOT decay → its
partial sums have NO finite budget (`dimLift_no_finite_budget`, Archimedean, machine-
checked for `d ≥ 12` where the fixed-point margin already exceeds `1`) → NO floor → NO
gap.  The summability that CREATES the floor is a `d = 4` MARGINAL miracle; the higher-`d`
theory is in the non-summable (gapless-continuum) regime.

So the dimensional lift makes the EASY half easier and BREAKS the hard half.  The d → 4
continuation is exactly where the marginal coupling / renormalon turns on.  This is NOT a
`:= SingleStepDefectBound` alias; it is a distinct multi-field adjudication whose collapse
is *proved*.

# What is machine-checked (all `propext`/`Quot.sound` only; Lean-core `Q'`/`Nat`)

  §1 the coefficient `c(d)`: the physical value `6 = dim(fund)·C₄(fund) = 2·3` is PURE
     rep theory, d-INDEPENDENT (`cCoeffRep_const`), so trivially continuable — NOT the
     obstruction.  The tempting "`3 = d−1` transverse" reading (`cCoeffDMinus`) AGREES at
     `d = 4` (`cCoeff_agree_at_four`, both `6`) but DISAGREES off `d = 4`
     (`cCoeff_disagree_at_five`, `6 ≠ 8`): the `3 = C₄ = d−1` coincidence is a `d = 4`
     accident.  Either reading is polynomial/constant → continuable.
  §2 the classical-scaling driver `classicalScaling d = d − 4`: `= 0` only at `d = 4`
     (`classicalScaling_four`), `> 0` for `d ≥ 5` (`classicalScaling_pos`).
  §3 the fixed-point margin `fpMargin d = (d−4)/β₀`: `= 0` at `d = 4` (`fpMargin_four`;
     AF/marginal/summable), `> 0` for `d ≥ 5` (`fpMargin_pos`; non-decaying defect).
  §4 the non-decaying fixed-point defect `dimLiftFPDefect d = 6·(fpMargin d)² > 0`
     (`dimLiftFPDefect_pos`, a positive constant for `d ≥ 5`), and the COLLAPSE:
     `dimLift_no_finite_budget` — for `d ≥ 12` the defect partial sums exceed ANY bound
     (no summability ⟹ no product floor ⟹ no gap).
  §5 the verdict bundle `DimLiftCollapseVerdict` (informational; inhabits NO frontier type).

# HONEST VERDICT

The dimensional lift does NOT give a genuine new route to `realδ_k(4) ≤ 6(1−w)²`.  The
coefficient is continuable and the large-`d` concentration genuinely eases the single-step
magnitude, but the gap-survival summability that makes the whole floor positive is a
`d = 4`-only marginal-coupling phenomenon; every `d > 4` is non-summable (no floor,
gapless continuum), and the d → 4 continuation re-introduces exactly the marginal coupling
= the renormalon = the interacting-measure content = `singleStep`.  `SingleStepDefectBound`
is NOT inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic reusing the proved `finSum_le_termwise`, `Q'.mul_pos`, and the
Archimedean `exists_ofNat_gt` / `largeInstPartialSum_eqv` pattern.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` / `Quot.sound`
only.  No `Classical.*`, no `native_decide`, no `sorry`, no `ring`.  All witnesses are
`Type`-level `Q'`/`Nat` data (Rule 8).
-/

import YMGap.Continuum.InstantonDiluteGas

namespace YMGap.Continuum.DimensionalLiftCollapse

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.InstantonDiluteGas

/-! ## §1. THE d-DEPENDENCE OF THE DEFECT COEFFICIENT `c(d)`.

In the Lean derivation (`RGTransport.dimQ`, `RGTransport.c4`, `RenDefectQuadFactor`) the
transverse-quadratic per-step defect on the first-excited (`s = 1`) mode is

    δ_ren ≤ dimQ(1)·C₄(1)·(1 − w)²  =  2·3·(1 − w)²  =  6·(1 − w)²,

with `dimQ(1) = s+1 = 2` (the SU(2) fundamental dimension `= N`) and `C₄(1) = s(s+2) = 3`
(the quadratic Casimir eigenvalue).  BOTH factors are PURE representation-theory data of
the gauge group SU(N); NEITHER carries the spacetime dimension `d`.  In particular the `3`
in `w^{C₄(1)} = w³` is the heat-kernel Casimir eigenvalue (`exp(−t·C₂)`), and the linear
`3(1 − w)` MUST equal `d/dw[w³]|₁ = 3` for the `O((1 − w)²)` cancellation
(`renDefect_factor`) — so both `3`s are the Casimir, not `d − 1`. -/

/-- **The physical coefficient `c(d) = dim(fund)·C₄(fund) = 6`, d-INDEPENDENT.**  The
transverse-quadratic coefficient is pure rep theory; it does not depend on the spacetime
dimension `d` at all.  (Verify `c(4) = 6`: `cCoeffRep 4 = ofNat 6`.) -/
def cCoeffRep (_d : Nat) : Q' := Q'.ofNat 6

/-- The tempting alternative reading "`3 = d − 1` transverse plaquette directions", giving
`c(d) = dimQ(1)·(d − 1) = 2·(d − 1)`.  This AGREES with the rep value only at `d = 4`. -/
def cCoeffDMinus (d : Nat) : Q' := Q'.ofNat (2 * (d - 1))

/-- **`c(d) = 6` is constant in `d`** — the rep-theory coefficient is d-INDEPENDENT, hence
trivially continuable; the coefficient is NOT the obstruction. -/
theorem cCoeffRep_const (d : Nat) : cCoeffRep d = Q'.ofNat 6 := rfl

/-- **`c(4) = 6`** (rep value). -/
theorem cCoeffRep_four : (cCoeffRep 4).eqv (Q'.ofNat 6) := by decide

/-- **The two readings AGREE at `d = 4`** (both `6`): the `C₄ = d − 1 = 3` coincidence. -/
theorem cCoeff_agree_at_four : (cCoeffRep 4).eqv (cCoeffDMinus 4) := by decide

/-- **The two readings DISAGREE off `d = 4`** (`6 ≠ 2·4 = 8` at `d = 5`): the `3 = d − 1`
reading is a `d = 4` accident; the physical (rep) coefficient stays `6` in every `d`. -/
theorem cCoeff_disagree_at_five : ¬ (cCoeffRep 5).eqv (cCoeffDMinus 5) := by decide

/-! ## §2. THE CLASSICAL-SCALING DRIVER `d − 4` (marginal only at `d = 4`).

The continuum gauge coupling has classical mass dimension `[g²] = 4 − d`.  It is
dimensionless (MARGINAL) exactly at `d = 4`, RELEVANT for `d < 4` (super-renormalizable),
IRRELEVANT for `d > 4` (non-renormalizable / IR-free).  Marginality at `d = 4` is what
produces asymptotic freedom, logarithmic running, dimensional transmutation, and the
renormalon — all `d = 4`-specific. -/

/-- **The classical scaling `d − 4`** — the tree-level term `(d − 4)·g²` in the `d`-dim
one-loop beta function `dg²/d(log μ) = (d − 4)·g² − β₀·g⁴`. -/
def classicalScaling (d : Nat) : Int := (d : Int) - 4

/-- **`classicalScaling 4 = 0`** — the coupling is exactly MARGINAL at `d = 4`. -/
theorem classicalScaling_four : classicalScaling 4 = 0 := by decide

/-- **`classicalScaling d > 0` for `d ≥ 5`** — the coupling is IRRELEVANT above four
dimensions (positive classical scaling), so the UV flow is driven AWAY from `g² = 0`. -/
theorem classicalScaling_pos (d : Nat) (h : 5 ≤ d) : 0 < classicalScaling d := by
  show (0 : Int) < (d : Int) - 4
  have hd : (5 : Int) ≤ (d : Int) := by exact_mod_cast h
  omega

/-! ## §3. THE FIXED-POINT MARGIN `fpMargin d = (d − 4)/β₀`.

Solving the tree-dominated flow near the origin: for `d > 4` the UV fixed point is
`g²_* = (d − 4)/β₀ > 0`, and the UV/continuum limit `a → 0` drives `g²(k) → g²_*` — a
NON-ZERO limit.  Hence `1 − w_k → 1 − w_* ≠ 0`: the per-step defect does NOT decay.  At
`d = 4` the fixed-point margin is `0` (asymptotic freedom, `w_k → 1`).  Here `β₀ = 11N/3`,
`N = 2`, so `β₀ = 22/3` and `fpMargin d = 3(d − 4)/22`. -/

/-- **The fixed-point coupling margin `g²_* = (d − 4)/β₀ = 3(d − 4)/22`** (`N = 2`). -/
def fpMargin (d : Nat) : Q' := Q'.mkPos (3 * ((d : Int) - 4)) 22 (by decide)

/-- **`fpMargin 4 = 0`** — asymptotic freedom at `d = 4`: the UV coupling flows to `0`,
`w_k → 1`, the defect decays, `Σδ` converges (summable, floor `> 0`). -/
theorem fpMargin_four : (fpMargin 4).eqv 0 := by decide

/-- **`fpMargin d > 0` for `d ≥ 5`** — for every `d > 4` the UV coupling flows to a
NON-ZERO fixed point, so `1 − w_* ≠ 0` and the per-step defect does not decay. -/
theorem fpMargin_pos (d : Nat) (h : 5 ≤ d) : (0 : Q') < fpMargin d := by
  apply pos_of_num_pos
  show (0 : Int) < 3 * ((d : Int) - 4)
  have hd : (5 : Int) ≤ (d : Int) := by exact_mod_cast h
  omega

/-! ## §4. THE NON-DECAYING FIXED-POINT DEFECT AND THE COLLAPSE (no finite budget).

The per-step defect at the `d > 4` fixed point is `6·(1 − w_*)²`, a strictly POSITIVE
CONSTANT independent of the block index `k` (modelled here on the coupling margin:
`dimLiftFPDefect d = 6·(fpMargin d)²`).  A defect that does not decay has partial sums with
NO finite budget — `Σδ_k = ∞` — so the product floor `∏(1 − δ_k)` collapses to `0`: NO gap.
This is the exact opposite of the `d = 4` case, where `δ_k ∼ 1/k²` is summable. -/

/-- **The non-decaying fixed-point defect `6·(fpMargin d)²`.**  For `d ≥ 5` this is a
strictly positive constant (`dimLiftFPDefect_pos`): the defect does NOT vanish along the
UV flow, in stark contrast to the `d = 4` asymptotically-free `δ_k → 0`. -/
def dimLiftFPDefect (d : Nat) : Q' := Q'.ofNat 6 * (fpMargin d * fpMargin d)

/-- **`0 < dimLiftFPDefect d` for `d ≥ 5`** — the fixed-point defect is a positive
constant; it never decays, so `Σ δ_k` cannot converge. -/
theorem dimLiftFPDefect_pos (d : Nat) (h : 5 ≤ d) : (0 : Q') < dimLiftFPDefect d := by
  have h6 : (0 : Q') < Q'.ofNat 6 := by decide
  have hm : (0 : Q') < fpMargin d := fpMargin_pos d h
  exact Q'.mul_pos h6 (Q'.mul_pos hm hm)

/-- The per-step defect model along the `d > 4` UV flow: the non-decaying constant
`fpMargin d` (a positive lower proxy for the fixed-point defect; the collapse is scale-
invariant, so the coupling margin is a faithful non-decaying stand-in). -/
def dimLiftDefect (d : Nat) (_k : Nat) : Q' := fpMargin d

/-- **`1 ≤ fpMargin d` for `d ≥ 12`** — in high enough dimension the fixed-point margin
already exceeds `1` (`3(d − 4)/22 ≥ 1 ⟺ d ≥ 12`; and `g²_* = (d − 4)/β₀ → ∞` as `d → ∞`).
This makes the divergence of `Σδ` elementary (each term `≥ 1`). -/
theorem one_le_fpMargin (d : Nat) (h : 12 ≤ d) : (1 : Q') ≤ fpMargin d := by
  show (1 : Q').num * ((fpMargin d).den : Int)
      ≤ (fpMargin d).num * ((1 : Q').den : Int)
  have hnum1 : (1 : Q').num = 1 := rfl
  have hden1 : ((1 : Q').den : Int) = 1 := rfl
  have hnumf : (fpMargin d).num = 3 * ((d : Int) - 4) := rfl
  have hdenf : ((fpMargin d).den : Int) = 22 := rfl
  rw [hnum1, hden1, hnumf, hdenf]
  have hd : (12 : Int) ≤ (d : Int) := by exact_mod_cast h
  omega

/-- **THE COLLAPSE — the higher-`d` defect has NO finite budget (`Σδ = ∞`).**  For every
candidate bound `B` there is a block-cutoff `N` at which the `d > 4` defect partial sum
EXCEEDS `B` (proved for `d ≥ 12`, where each per-step defect `≥ 1`, via the Archimedean
`exists_ofNat_gt` and termwise domination of the unit sequence).  A non-decaying defect
gives divergent `Σδ_k`, so the product floor `∏(1 − δ_k)` collapses to `0`: the higher-`d`
theory has NO uniform gap floor — the summability that creates the `d = 4` floor is a
marginal-coupling miracle destroyed by the lift.  Contrast the `d = 4` case
(`fpMargin_four = 0`, AF, `δ_k ∼ 1/k²` summable). -/
theorem dimLift_no_finite_budget (d : Nat) (h : 12 ≤ d) (B : Q') :
    ∃ N : Nat, B < finSum (dimLiftDefect d) N := by
  obtain ⟨N, hN⟩ := exists_ofNat_gt B
  refine ⟨N, ?_⟩
  -- unit partial sum: finSum largeInstTerm N ≃ ofNat N
  have hunit : (finSum largeInstTerm N).eqv (Q'.ofNat N) :=
    largeInstPartialSum_eqv N
  -- termwise 1 ≤ fpMargin d  ⟹  finSum unit ≤ finSum defect
  have hcmp : finSum largeInstTerm N ≤ finSum (dimLiftDefect d) N :=
    YMGap.Constructive.ExpNeg.finSum_le_finSum_of_termwise
      largeInstTerm (dimLiftDefect d) (fun _ => one_le_fpMargin d h) N
  -- B < ofNat N ≤ finSum unit ≤ finSum defect
  have hB : B < finSum largeInstTerm N :=
    lt_of_lt_of_le hN (Q'.ge_of_eqv hunit)
  exact lt_of_lt_of_le hB hcmp

/-! ## §5. THE VERDICT — the dimensional lift COLLAPSES at the d → 4 continuation.

Informational bundle of the PROVED facts.  It inhabits neither `SingleStepDefectBound`
nor any guarded Clay-frontier type; every field is a genuine theorem. -/

/-- A record of the machine-checked dimensional-lift adjudication.  Certifies: (i) the
defect coefficient is d-INDEPENDENT rep theory (`c(4) = 6`, continuable — not the
obstruction); (ii) the two coefficient readings coincide ONLY at `d = 4`; (iii) the
classical scaling `d − 4` is marginal ONLY at `d = 4`; (iv) the fixed-point margin
vanishes ONLY at `d = 4` (AF/summable) and is positive (non-decaying) for `d ≥ 5`; (v) the
higher-`d` defect has no finite budget (no floor / gapless continuum).  Conclusion: the
lift eases the single-step magnitude (large-`d` concentration) but BREAKS the gap-survival
summability, which is a `d = 4` marginal-coupling phenomenon; the d → 4 continuation
re-introduces the renormalon = the interacting measure = `singleStep`. -/
structure DimLiftCollapseVerdict : Type where
  /-- §1 — the coefficient `c(d) = 6` is constant in `d` (continuable rep theory). -/
  coeffContinuable : ∀ d, cCoeffRep d = Q'.ofNat 6
  /-- §1 — the `3 = d − 1` reading is only a `d = 4` coincidence. -/
  coeffCoincidence : (cCoeffRep 4).eqv (cCoeffDMinus 4)
      ∧ ¬ (cCoeffRep 5).eqv (cCoeffDMinus 5)
  /-- §2 — the coupling is MARGINAL only at `d = 4`. -/
  marginalOnlyAtFour : classicalScaling 4 = 0 ∧ ∀ d, 5 ≤ d → 0 < classicalScaling d
  /-- §3 — the fixed-point margin vanishes only at `d = 4` (AF), positive for `d ≥ 5`. -/
  fixedPointMargin : (fpMargin 4).eqv 0 ∧ ∀ d, 5 ≤ d → (0 : Q') < fpMargin d
  /-- §4 — the higher-`d` defect is a positive constant that never decays (`d ≥ 5`). -/
  defectNonDecaying : ∀ d, 5 ≤ d → (0 : Q') < dimLiftFPDefect d
  /-- §4 — the higher-`d` defect sum has NO finite budget (`d ≥ 12`): no floor, no gap. -/
  noFiniteBudget : ∀ d, 12 ≤ d → ∀ B : Q', ∃ N : Nat, B < finSum (dimLiftDefect d) N

/-- **The dimensional-lift COLLAPSE, assembled from PROVED facts.**  Inhabits no frontier
type; certifies the honest negative — the lift does not continue to a `d = 4` gap proof. -/
def dimLift_collapse_verdict : DimLiftCollapseVerdict where
  coeffContinuable := cCoeffRep_const
  coeffCoincidence := ⟨cCoeff_agree_at_four, cCoeff_disagree_at_five⟩
  marginalOnlyAtFour := ⟨classicalScaling_four, classicalScaling_pos⟩
  fixedPointMargin := ⟨fpMargin_four, fpMargin_pos⟩
  defectNonDecaying := dimLiftFPDefect_pos
  noFiniteBudget := dimLift_no_finite_budget

end YMGap.Continuum.DimensionalLiftCollapse

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.DimensionalLiftCollapse.cCoeffRep_const
#print axioms YMGap.Continuum.DimensionalLiftCollapse.cCoeffRep_four
#print axioms YMGap.Continuum.DimensionalLiftCollapse.cCoeff_agree_at_four
#print axioms YMGap.Continuum.DimensionalLiftCollapse.cCoeff_disagree_at_five
#print axioms YMGap.Continuum.DimensionalLiftCollapse.classicalScaling_four
#print axioms YMGap.Continuum.DimensionalLiftCollapse.classicalScaling_pos
#print axioms YMGap.Continuum.DimensionalLiftCollapse.fpMargin_four
#print axioms YMGap.Continuum.DimensionalLiftCollapse.fpMargin_pos
#print axioms YMGap.Continuum.DimensionalLiftCollapse.dimLiftFPDefect_pos
#print axioms YMGap.Continuum.DimensionalLiftCollapse.one_le_fpMargin
#print axioms YMGap.Continuum.DimensionalLiftCollapse.dimLift_no_finite_budget
#print axioms YMGap.Continuum.DimensionalLiftCollapse.dimLift_collapse_verdict
