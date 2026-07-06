/-
Track B / R2 — UNIFYING the crossover middle-window obligation with the existing
named RG wall `DefectGapRecursion` / `DominantModeRecursion`, and PINNING the
truly-uncovered summed sub-window of the moderate flow.

# What this module does (read first)

`CrossoverAnchorFloor.fullFloor_reduced_to_crossover` reduces the WHOLE 4D SU(N)
continuum margin floor to the single named middle-window obligation
`CrossoverWindowDefect δ ε K` via the ADDITIVE budget `(1 − Σδ)·margin`.  This
module makes three honest points and states the exact single remaining obligation.

## TASK 1 — the whole floor rests on ONE existing named RG wall

`fullFloor_of_defectRecursion` gives the ENTIRE positive continuum floor
`∀k, prodFloor ≤ physGap k`, `0 < prodFloor` from a SINGLE `DefectGapRecursion`
object — its PRODUCT floor `∏(1 − δ_k) ≥ prodFloor > 0`.  Its sole open field is
`recursion` (the per-step true-margin gap-degradation law).  Everything else — the
anchor (107/108, `RealCorrMass`), the deep-UV AF tail, the adequacy split, the
summability (`renormalized_gap_of_AFRate`), and the per-step complementarity — is
already proved.  `DominantModeRecursion.dominantModeRecursion` is a GENUINE
(non-degenerate) inhabitant for the SURROGATE survival-product margin, so the floor
is UNCONDITIONAL there; the sole residual is `UniformCouplingFromAF.TrueMarginRecursion`
(physGap pinned to the true margin), left uninhabited upstream.

## The KEY structural insight — ADDITIVE budget vs PRODUCT floor

`CrossoverAnchorFloor`'s route needs the crossover SUM `Σ_{k<K} δ_k < 1` (so the
coefficient `1 − Σδ` stays positive).  But the honest RG defect over the moderate
middle VIOLATES `Σδ < 1`:

    `middle_additive_budget_exceeds_one` :  6·((1/2)² + (1/3)² + (1/4)²) > 1

(the block-spin defect `6(1−w)²` summed over the three canonical middle steps is
`≈ 2.54 > 1`).  So the additive middle budget CANNOT close.  The `DefectGapRecursion`
PRODUCT floor `∏(1 − δ_k) > 0` needs only `Σδ_k < ∞` (the product converges to a
positive value), NOT `Σδ < 1`.  Hence the product route SUCCEEDS exactly where the
additive middle budget fails — and that is why the whole floor should rest on the
`DefectGapRecursion` wall, not on the additive `CrossoverWindowDefect`.

## TASK 2 — the moderate middle is a FINITE window; the uncovered sub-window is EMPTY

On the canonical AF trajectory `w_k = 1 − 1/(k+1)` the middle window `(1/6, 7/9)`
consists of EXACTLY THREE steps `k ∈ {1,2,3}` (`w = 1/2, 2/3, 3/4`); `w_0 = 0` and
`w_4 = 4/5` fall outside (`middle_is_three_steps`).  So `K_mid = 3` — a FINITE,
decidable budget.  Every middle step is below the proved character ceiling `7/9`
(`w³ < 1/2`, `middle_char_valid`), so the CHARACTER mechanism (`ρ_char = 2w³ < 1`)
covers the ENTIRE middle per step; the first step above the ceiling, `w_4 = 4/5`, is
covered by the block-spin per-step defect `< 1/2` (`w4_blockspin_covers`).  Hence the
truly-uncovered SUMMED sub-window is EMPTY (`no_uncovered_middle_step`): character
below `7/9`, block-spin above `0.711`, with a non-empty overlap at `w_3 = 3/4`
(`w3_in_overlap`).

## For the AF regime, the crossover budget IS the summability content

`crossoverDefect_ofInvSqDefect` proves the K-UNIFORM crossover budget for a defect
with an inverse-square (AF) majorant `δ_k ≤ A·1/(k+1)²`: `tailSum δ 0 K ≤ 2A`,
K-independent.  This is exactly the `Σδ < ∞` content of the product floor turned into
a concrete finite bound — the deep-UV part of the `DefectGapRecursion` summability.

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9)

The whole continuum gap now rests on the ONE existing named wall `DefectGapRecursion`
(its `recursion` field for the true margin, = `TrueMarginRecursion`, uninhabited).
The moderate middle is FINITE (`K_mid = 3` on the canonical trajectory) and per-step
FULLY COVERED (character below `7/9`, block-spin above `0.711`, overlap at `3/4`), so
the truly-uncovered summed sub-window is EMPTY.  What genuinely resists is not an
uncovered window but the SUMMED middle CONTRACTION: the harmonic AF flow has
`Σδ ≈ 2.54 > 1` over the middle, so the additive route is dead and the closure must
go through the product floor — i.e. the finite `K_mid`-step per-step contractions
must compose to keep `∏(1 − δ_k) > 0`, which is the `DefectGapRecursion.recursion`
field on the finite middle (the genuine Bałaban residual, now finite/decidable given
the trajectory).  NO 4D Yang–Mills mass gap is claimed; nothing is faked.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` core reusing the proved `continuum_floor_of_defectRecursion`,
`uv_tail_bound`, the `CrossoverWindowDefect` obligation, and decidable rational
comparisons.  Every load-bearing declaration is gated with `#print axioms`; permitted
output is `propext` / `Quot.sound` only (the pure-numeric lemmas are axiom-free).
No `sorry`, no `Classical.*`, no `native_decide`.  Nothing on the open frontier is
inhabited unconditionally.
-/

import YMGap.Continuum.CrossoverFlowContraction
import YMGap.Continuum.DominantModeRecursion
import YMGap.Continuum.UniformCouplingFromAF

namespace YMGap.Continuum.CrossoverDefectUnification

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.CrossoverAnchorFloor
open YMGap.Continuum.ContinuumClosureProgram

/-! ## 1. TASK 1 — the whole continuum floor on ONE `DefectGapRecursion` object -/

/-- **`fullFloor_of_defectRecursion` — the entire continuum floor on ONE named RG
wall.**  A single `DefectGapRecursion` `D` gives the positive uniform continuum
floor `∀k, prodFloor ≤ physGap k`, `0 < prodFloor` — via the PRODUCT floor
`∏(1 − δ_k) ≥ prodFloor > 0`.  Its ONLY open field is `recursion`; the anchor,
deep-UV AF tail, and summability are proved.  This is the headline unification: the
whole floor rests on `DefectGapRecursion`, exactly the existing named wall. -/
theorem fullFloor_of_defectRecursion (D : DefectGapRecursion) :
    (0 : Q') < D.prodFloor ∧ ∀ k : Nat, D.prodFloor ≤ D.physGap k :=
  continuum_floor_of_defectRecursion D

/-- **The floor is UNCONDITIONAL for the dominant-mode surrogate margin.**  The
proved `DominantModeRecursion.dominantModeRecursion` (genuine, non-degenerate:
`defect = δ_ren` not identically `0`, `physGap` the `Q'`-varying survival product,
`prodFloor = floorEps > 0` the proved summability output) inhabits the wall, so the
continuum floor holds unconditionally for that surrogate margin. -/
theorem fullFloor_of_dominantMode :
    (0 : Q') < DominantModeRecursion.dominantModeRecursion.prodFloor
      ∧ ∀ k : Nat,
        DominantModeRecursion.dominantModeRecursion.prodFloor
          ≤ DominantModeRecursion.dominantModeRecursion.physGap k :=
  fullFloor_of_defectRecursion DominantModeRecursion.dominantModeRecursion

/-! ## 2. The finite crossover window of ANY `DefectGapRecursion` inhabits the
     additive obligation — the literal identification `CrossoverWindowDefect`
     ⇐ `DefectGapRecursion` (the middle-window defect sum IS the wall's defect) -/

/-- **`crossoverDefect_ofDefectRecursion` — `CrossoverWindowDefect` is the finite
middle-window shadow of a `DefectGapRecursion`'s defect.**  For any
`DefectGapRecursion` `D`, the finite crossover window `k < K` inhabits the named
obligation `CrossoverWindowDefect D.defect ε K`, with `Bδ = K·1` (from
`defect_le_one`) and `Bε = K·εmax`.  So the middle-window obligation's δ-sequence
is LITERALLY the wall's defect sequence.  (The `Bδ = K` budget is NOT small — the
additive route does not close on it; §3 shows why the product route is needed.) -/
def crossoverDefect_ofDefectRecursion (D : DefectGapRecursion) (ε : Nat → Q')
    (K : Nat) (εmax : Q') (hεmax : (0 : Q') ≤ εmax)
    (hstepε : ∀ j, j < K → ε j ≤ εmax) :
    CrossoverWindowDefect D.defect ε K :=
  crossoverDefect_ofPerStep D.defect ε K 1 εmax (by decide) hεmax
    (fun j _ => D.defect_le_one j) hstepε

/-! ## 3. WHY the additive middle budget fails and the product floor is needed

The canonical AF trajectory `w_k = 1 − 1/(k+1)` has margins `1 − w_k = 1/(k+1)`.
Over the three middle steps `k = 1,2,3` the block-spin defect `6(1 − w)²` sums to
`6·((1/2)² + (1/3)² + (1/4)²) ≈ 2.54 > 1`, so the additive coefficient `1 − Σδ`
goes NEGATIVE.  The product `∏(1 − δ_k)` needs only `Σδ < ∞`, not `Σδ < 1`. -/

/-- **`middle_additive_budget_exceeds_one` — the additive middle budget breaks `1`.**
The block-spin defect `6(1 − w)²` summed over the canonical middle margins
`1 − w = 1/2, 1/3, 1/4` is `6·(1/4 + 1/9 + 1/16) > 1`.  So the ADDITIVE middle
budget cannot keep `1 − Σδ` positive — the additive `CrossoverWindowDefect` route is
dead on the honest RG defect, and the closure must go through the product floor. -/
theorem middle_additive_budget_exceeds_one :
    (1 : Q') <
      Q'.ofNat 6 *
        ( (Q'.mkPos 1 2 (by decide)) * (Q'.mkPos 1 2 (by decide))
        + ((Q'.mkPos 1 3 (by decide)) * (Q'.mkPos 1 3 (by decide))
        +  (Q'.mkPos 1 4 (by decide)) * (Q'.mkPos 1 4 (by decide))) ) := by
  decide

/-! ## 4. The K-UNIFORM crossover budget for an inverse-square (AF) defect

For a defect with an AF inverse-square majorant `δ_k ≤ A·1/(k+1)²`, the crossover
sum is bounded K-uniformly by `2A` (the deep-UV summability), inhabiting the
obligation with a K-INDEPENDENT budget.  This is the `Σδ < ∞` content of the product
floor made into a concrete finite bound. -/

/-- **`crossoverDefect_ofInvSqDefect` — the K-uniform AF crossover budget.**  If
`δ_k ≤ A·recipSqSucc k` for all `k` (`A ≥ 0`, the AF inverse-square majorant) and a
per-step additive cap `ε_j ≤ εmax` on `j < K`, the middle obligation is inhabited
with the K-INDEPENDENT `Bδ = 2A`, `Bε = K·εmax` — via `uv_tail_bound` at base `0`.
This is the deep-UV summability side; the moderate head is what breaks it (§3). -/
def crossoverDefect_ofInvSqDefect (δ ε : Nat → Q') (K : Nat) (A εmax : Q')
    (hA : (0 : Q') ≤ A) (hεmax : (0 : Q') ≤ εmax)
    (hUV : ∀ k, δ k ≤ A * recipSqSucc k)
    (hstepε : ∀ j, j < K → ε j ≤ εmax) :
    CrossoverWindowDefect δ ε K where
  Bδ := 2 * A
  Bε := Q'.ofNat K * εmax
  crossδ := uv_tail_bound δ 0 A hA (fun k _ => hUV k) K
  crossε := tailSum_le_ofNat_mul ε εmax hεmax K hstepε

/-! ## 5. TASK 2 — the moderate middle is a FINITE window; coverage is complete

Canonical AF trajectory `w_k = 1 − 1/(k+1)`: `w_0 = 0`, `w_1 = 1/2`, `w_2 = 2/3`,
`w_3 = 3/4`, `w_4 = 4/5`.  Middle `(1/6, 7/9)`. -/

/-- The canonical middle weights (three of them) and the two flanking weights. -/
def w0 : Q' := 0
def w1 : Q' := Q'.mkPos 1 2 (by decide)
def w2 : Q' := Q'.mkPos 2 3 (by decide)
def w3 : Q' := Q'.mkPos 3 4 (by decide)
def w4 : Q' := Q'.mkPos 4 5 (by decide)

/-- The strong-coupling floor `1/6` and the character ceiling `7/9`. -/
def midLo : Q' := Q'.mkPos 1 6 (by decide)
def midHi : Q' := Q'.mkPos 7 9 (by decide)

/-- **`middle_is_three_steps` — the middle window is EXACTLY `{1,2,3}`.**  On the
canonical trajectory the middle `(1/6, 7/9)` contains `w_1, w_2, w_3` and excludes
`w_0 = 0` (below) and `w_4 = 4/5` (above).  So `K_mid = 3` — a finite, decidable
crossover budget. -/
theorem middle_is_three_steps :
    (w1 < midHi ∧ midLo < w1)
      ∧ (w2 < midHi ∧ midLo < w2)
      ∧ (w3 < midHi ∧ midLo < w3)
      ∧ (w0 < midLo)
      ∧ (midHi < w4) := by decide

/-- **`middle_char_valid` — the character mechanism covers the WHOLE middle.**  Each
middle weight is below the character ceiling `2^{−1/3}` (`w³ < 1/2`), so the
character rate `ρ_char = 2w³ < 1` on all three middle steps. -/
theorem middle_char_valid :
    (w1 ^ 3 < Q'.mkPos 1 2 (by decide))
      ∧ (w2 ^ 3 < Q'.mkPos 1 2 (by decide))
      ∧ (w3 ^ 3 < Q'.mkPos 1 2 (by decide)) := by decide

/-- **`w4_blockspin_covers` — the first step above the ceiling is covered by
block-spin.**  `w_4 = 4/5` exceeds the character ceiling (`w_4³ > 1/2`), but the
block-spin per-step defect `6·(1 − w_4)² = 6/25 < 1/2`.  So the character-fail step
is covered by block-spin — no coverage gap at the handoff. -/
theorem w4_blockspin_covers :
    (Q'.mkPos 1 2 (by decide) < w4 ^ 3)
      ∧ (Q'.ofNat 6 * (((1 : Q') - w4) * ((1 : Q') - w4)) < Q'.mkPos 1 2 (by decide)) := by
  decide

/-- **`w3_in_overlap` — the two mechanisms genuinely overlap at `w_3 = 3/4`.**  At
`w_3` BOTH hold: character `w_3³ < 1/2` AND block-spin per-step `6(1 − w_3)² < 1/2`.
So the coverage handoff has a non-empty overlap, not a razor edge. -/
theorem w3_in_overlap :
    (w3 ^ 3 < Q'.mkPos 1 2 (by decide))
      ∧ (Q'.ofNat 6 * (((1 : Q') - w3) * ((1 : Q') - w3)) < Q'.mkPos 1 2 (by decide)) := by
  decide

/-- **`no_uncovered_middle_step` — the truly-uncovered summed sub-window is EMPTY.**
Every middle step (`w_1, w_2, w_3`) is character-covered (`w³ < 1/2`), and the first
step past the ceiling (`w_4`) is block-spin-covered (`6(1 − w)² < 1/2`).  So on the
canonical trajectory there is NO step where BOTH mechanisms fail: the uncovered
summed sub-window is empty. -/
theorem no_uncovered_middle_step :
    (w1 ^ 3 < Q'.mkPos 1 2 (by decide))
      ∧ (w2 ^ 3 < Q'.mkPos 1 2 (by decide))
      ∧ (w3 ^ 3 < Q'.mkPos 1 2 (by decide))
      ∧ (Q'.ofNat 6 * (((1 : Q') - w4) * ((1 : Q') - w4)) < Q'.mkPos 1 2 (by decide)) :=
  ⟨middle_char_valid.1, middle_char_valid.2.1, middle_char_valid.2.2,
   w4_blockspin_covers.2⟩

/-! ## 6. The single remaining obligation (statement)

Assembling §1–§5: the WHOLE continuum floor holds once a `DefectGapRecursion` is
supplied (`fullFloor_of_defectRecursion`), with the anchor, deep-UV AF tail,
adequacy, summability, and per-step middle complementarity ALL proved.  Its ONLY
open field is `recursion` for the TRUE margin — the honest named residual
`UniformCouplingFromAF.TrueMarginRecursion`.  `single_remaining_obligation` records
that IF that residual is inhabited THEN the whole floor holds for the genuine
dimensionless margin. -/

/-- **`single_remaining_obligation` — the whole floor on the ONE true-margin wall.**
IF the honest named residual `UniformCouplingFromAF.TrueMarginRecursion` `T` is
inhabited (its `recursion` field is the per-step non-abelian multi-link 4D
gap-degradation law for the TRUE margin `m_lat(a_k)/a_k`), THEN the positive
continuum floor holds for that true margin.  This is the exact single obligation on
which the entire Clay continuum gap rests; it is NOT inhabited here. -/
theorem single_remaining_obligation
    (T : UniformCouplingFromAF.TrueMarginRecursion) :
    (0 : Q') < T.D.prodFloor
      ∧ ∀ k : Nat, T.D.prodFloor ≤ T.trueMargin k := by
  refine ⟨T.D.prodFloor_pos, fun k => ?_⟩
  have h := (fullFloor_of_defectRecursion T.D).2 k
  rwa [T.physGap_is_trueMargin k] at h

end YMGap.Continuum.CrossoverDefectUnification

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CrossoverDefectUnification.fullFloor_of_defectRecursion
#print axioms YMGap.Continuum.CrossoverDefectUnification.fullFloor_of_dominantMode
#print axioms YMGap.Continuum.CrossoverDefectUnification.crossoverDefect_ofDefectRecursion
#print axioms YMGap.Continuum.CrossoverDefectUnification.middle_additive_budget_exceeds_one
#print axioms YMGap.Continuum.CrossoverDefectUnification.crossoverDefect_ofInvSqDefect
#print axioms YMGap.Continuum.CrossoverDefectUnification.middle_is_three_steps
#print axioms YMGap.Continuum.CrossoverDefectUnification.middle_char_valid
#print axioms YMGap.Continuum.CrossoverDefectUnification.w4_blockspin_covers
#print axioms YMGap.Continuum.CrossoverDefectUnification.w3_in_overlap
#print axioms YMGap.Continuum.CrossoverDefectUnification.no_uncovered_middle_step
#print axioms YMGap.Continuum.CrossoverDefectUnification.single_remaining_obligation
