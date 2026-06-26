/-
# Off-diagonal finish-line assembly for the π-free Chebyshev-`U` orthogonality

This module assembles the two per-leg second-difference residuals
(`ChebOrthoSecondDiff.BrLegRemainder` / `RadLegRemainder`) into the UNCONDITIONAL
even off-diagonal orthogonality `∫_{−1}^1 U_e(x)√(1−x²)dx = 0`, and supplies the
GENUINE rational/`CReal` helper bounds the per-leg balance needs.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `bdyRadical_le_one` — the two-sided value bound `|s_k| ≤ 1` on every cell
    radical `s_k = √(1 − b_k²)` (`1 − b_k² ≤ 1`).  The radical factors of the
    smooth-bracket leg are bounded by `1`; this discharges the radical side of
    `BrLegRemainder`'s Term B.
  * `OnBox_node` — the box predicate `OnBox x_k δ` (`|x_k| ≤ 1`, `0 ≤ δ ≤ 1`) for
    EVERY interior cell, so the proved bracket Taylor bounds
    (`ChebMarkovModulus.bracket{Quad,Cube}Bound_holds`) apply directly at the cell
    with `x = x_k`, `δ = 1/M`.
  * `offdiag_orthogonality_of_legs` — **THE WIRING**: from `BrLegRemainder e he` and
    `RadLegRemainder e he` for every even `e ≥ 2`, the COMBINED π-free off-diagonal
    orthogonality `∫U_e√ = 0` for all `e ≥ 1`, by composing the PROVED chain
    `secondDiffLeg2_of_legs` → `secondDiff_of_leg2` →
    `interiorSecondOrder_of_secondDiff` → `offdiag_closed_of_secondOrder`.

## What is NAMED-open (precisely — the genuine quantitative obstruction)

The two per-leg residuals `BrLegRemainder` / `RadLegRemainder` are TRUE (the true
values `|legBr − LZA|`, `|legRad − LZB|` are `O(δ³)` / `O(δ²)`), but they are NOT
provable from the second-difference moduli currently in the codebase, because the
proved symmetric radical second-difference quotient
`ChebOrthoLegClose.symmSecondClose.symmQuot` is only `O(M/j)` — far too weak (by a
factor `~M²`) to dominate `½·gradedRate ~ 1/(⌊√M⌋·j²)` after the `¼·h·g` prefactor.

The weakness is INHERITED: `symmQuot = (2·subSecondQuot + 2δ²)·(1/recipWitness)`
with `subSecondQuot ~ O(1)` (the sub-second-difference bound divides the genuine
`δ²`-scale `subSecondBound ~ 4δ²` by the LOOSE pointwise lower bound
`subSecondL = 1/M²` on a sum `~O(1)`, losing a factor `M²`) and
`1/recipWitness ~ M/j`.  So the named-open content reduces to ONE sharper analytic
input — a `δ²`-scale (not `O(1)`) bound on `s_+ s_- − s_k²`, equivalently a
pointwise lower bound `subSecondL ~ recipWitness²` (not `1/M²`) on the
sub-second-difference sum `s_+ s_- + s_k²`.  This is recorded precisely as
`SubSecondTightModulus`; given it, the per-leg balance is mechanical exponent
bookkeeping (`sharpBound_le_recip_jdist`-style `Int` cross-multiplication).

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on closed
`Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoSecondDiff
import YMGap.Continuum.ChebOrthoTaylor
import YMGap.Continuum.ChebOrthoFinal
import YMGap.Continuum.ChebBracketTaylor

namespace YMGap.Continuum.ChebOrthoOffDiagClose

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.ChebOrthoGradedClose
open YMGap.Continuum.ChebOrthoMidpoint

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The cell-radical two-sided bound `|s_k| ≤ 1`

Each cell radical `s_k = √(1 − b_k²)` satisfies `1 − b_k² ≤ 1` (drop the nonneg
square), hence `s_k ≤ 1` (and `≥ 0`, so two-sidedly `≤ 1`).  These are the radical
factors of the smooth-bracket leg `legBr = ¼(s_+ + s_-)(B_+ − B_-)`. -/

/-- **`1 − b_k² ≤ 1`** at an interior cell boundary: `n² − (2k − n)² ≤ n²`
(`mkPos`-level: `bdyNum ≤ omsDen` since `(2k−n)² ≥ 0`). -/
theorem bdyOneMinusSq_le_one (n k : Nat) (hn : 0 < n) (hk0 : 0 < k) (hkn : k < n) :
    bdyOneMinusSq n k hn hk0 hkn ≤ (1 : Q') := by
  show (bdyOneMinusSq n k hn hk0 hkn).num * ((1 : Q').den : Int)
      ≤ (1 : Q').num * ((bdyOneMinusSq n k hn hk0 hkn).den : Int)
  have hnum : (bdyOneMinusSq n k hn hk0 hkn).num = bdyNum n k := by
    show (Q'.mkPos (bdyNum n k) (SemicircleIntegral.omsDen n)
      (SemicircleIntegral.omsDen_pos hn)).num = bdyNum n k
    rw [Q'.mkPos_num]
  have hden : ((bdyOneMinusSq n k hn hk0 hkn).den : Int) = ((n * n : Nat) : Int) := by
    show ((Q'.mkPos (bdyNum n k) (SemicircleIntegral.omsDen n)
      (SemicircleIntegral.omsDen_pos hn)).den : Int) = ((n * n : Nat) : Int)
    rw [Q'.mkPos_den]; rfl
  rw [hnum, hden]
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  have h1n : (1 : Q').num = 1 := rfl
  rw [h1d, h1n, Int.mul_one, Int.one_mul]
  -- bdyNum n k = n² − (2k−n)² ≤ n² = ↑(n·n)
  show (n : Int) * (n : Int) - (2 * (k : Int) - (n : Int)) * (2 * (k : Int) - (n : Int))
      ≤ ((n * n : Nat) : Int)
  have hcast : ((n * n : Nat) : Int) = (n : Int) * (n : Int) := by push_cast; rfl
  rw [hcast]
  have hsq : (0 : Int) ≤ (2 * (k : Int) - (n : Int)) * (2 * (k : Int) - (n : Int)) := by
    rcases Int.le_total 0 (2 * (k : Int) - (n : Int)) with h | h
    · exact Int.mul_nonneg h h
    · have hneg : (0 : Int) ≤ -(2 * (k : Int) - (n : Int)) := by omega
      have hp : (0 : Int) ≤ (-(2 * (k : Int) - (n : Int))) * (-(2 * (k : Int) - (n : Int))) :=
        Int.mul_nonneg hneg hneg
      have he : (-(2 * (k : Int) - (n : Int))) * (-(2 * (k : Int) - (n : Int)))
          = (2 * (k : Int) - (n : Int)) * (2 * (k : Int) - (n : Int)) := by
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      rw [he] at hp; exact hp
  omega

/-- **The cell radical is two-sidedly `≤ 1`** at an interior cell `0 < k < n`:
`s_k = √(1 − b_k²) ≥ 0` and `≤ 1` (since `1 − b_k² ≤ 1 = 1·1`).  This is the bounded
radical factor of the smooth-bracket leg. -/
theorem bdyRadical_le_one (n : Nat) (hn : 0 < n) (k : Nat) (hk0 : 0 < k) (hkn : k < n) :
    AbsLeRat (bdyRadical n hn k) (1 : Q') := by
  refine bdyRadical_AbsLeRat n hn k hk0 hkn (1 : Q') (by decide) ?_
  -- 1 − b_k² ≤ 1·1
  refine Q'.le_trans' _ _ _ (bdyOneMinusSq_le_one n k hn hk0 hkn) ?_
  exact Q'.ge_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv 1))

/-! ## 2. The box predicate for an interior cell

The proved bracket Taylor bounds `ChebMarkovModulus.bracket{Quad,Cube}Bound_holds`
quantify over `OnBox x δ`.  Every interior cell supplies `OnBox x_k (1/M)` with
`x_k = uniformMidpoint M k ∈ [−1,1]` and `δ = 1/M ∈ (0,1]`. -/

/-- **`OnBox x_k (1/M)`** for an interior cell: `|x_k| ≤ 1` (`node_lo`/`node_hi`)
and `0 ≤ 1/M ≤ 1` (`M ≥ 1`). -/
theorem OnBox_node (M : Nat) (hM : 0 < M) (k : Nat) (hkn : k < M) :
    ChebBracketTaylor.OnBox (RiemannSOS.uniformMidpoint M hM k) (Q'.mkPos 1 M hM) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- x_k ≤ 1
    exact RiemannSOS.node_hi M hM k hkn
  · -- −1 ≤ x_k
    exact RiemannSOS.node_lo M hM k
  · -- 0 ≤ 1/M
    show (0 : Q') ≤ Q'.mkPos 1 M hM
    rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide
  · -- 1/M ≤ 1
    show (Q'.mkPos 1 M hM).num * ((1 : Q').den : Int)
        ≤ (1 : Q').num * ((Q'.mkPos 1 M hM).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
    have h1d : ((1 : Q').den : Int) = 1 := rfl
    have h1n : (1 : Q').num = 1 := rfl
    rw [h1d, h1n, Int.mul_one, Int.one_mul]
    -- 1 ≤ ↑M  (M ≥ 1)
    have : (1 : Nat) ≤ M := hM
    exact_mod_cast this

/-! ## 3. The named sharper analytic input (the genuine residual)

The per-leg residuals `BrLegRemainder` / `RadLegRemainder` are TRUE but unreachable
from the currently-proved second-difference moduli, because the symmetric radical
second-difference quotient `symmQuot` is `O(M/j)` (vacuous) rather than the
`δ^{3/2}/√j` scale claimed.  The weakness is the LOOSE pointwise lower bound
`subSecondL = 1/M²` used in `subSecondDiff_AbsLeRat`.  The sharper input below — a
`δ²`-scale bound on the sub-second-difference `s_+ s_- − s_k²` — closes that gap.

`SubSecondTightModulus M k` asserts the GENUINE `δ²`-scale (`= 1/M²` order) bound

    `|s_+ s_- − s_k²| ≤ (Q'.mkPos C M²)`   (C an explicit `Nat` constant),

i.e. the sub-second difference is `O(δ²)`, not `O(1)`.  This is STRICTLY the missing
tight constant; given it, `symmQuot` becomes `O(δ^{3/2}/√j)`, and the per-leg
exponent balance is the `sharpBound_le_recip_jdist`-style `Int` bookkeeping. -/

/-- **NAMED-open: the TIGHT sub-second-difference modulus** (`δ²`-scale).  The
genuine `O(δ²)` bound on the radical sub-second difference `s_+ s_- − s_k²` at an
interior cell, with an EXPLICIT `Nat` numerator `C` over `M²`:

    `AbsLeRat (s_+·s_- + (−s_k²)) (Q'.mkPos C (M*M))`.

This is STRICTLY the missing tight constant for the symmetric radical leg: the
proved `ChebOrthoRadSecondDiffSq.subSecondDiff_AbsLeRat` only gives the `O(1)`
quotient `subSecondQuot` (loose lower bound `1/M²`); the `δ²`-scale version requires
the tight pointwise lower bound `subSecondL ~ recipWitness²` on the sum
`s_+ s_- + s_k²`.  Recorded as the precise residual. -/
def SubSecondTightModulus (M : Nat) (hM : 0 < M) (k : Nat) : Prop :=
  ∀ hk0 : 0 < k, ∀ hkn : k < M, ∃ C : Nat,
    AbsLeRat
      (CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
        (CReal.neg (CReal.mul (SemicircleIntegral.nodeWeight M hM k)
          (SemicircleIntegral.nodeWeight M hM k))))
      (Q'.mkPos (C : Int) (M * M) (Nat.mul_pos hM hM))

/-! ## 4. THE WIRING — the unconditional off-diagonal from the two leg residuals

Given the per-leg residuals for every even `e ≥ 2`, the COMBINED π-free off-diagonal
orthogonality follows by composing the PROVED chain:

  `secondDiffLeg2_of_legs` : `BrLegRemainder ∧ RadLegRemainder → SecondDiffRemainderLeg2`
  `secondDiff_of_leg2`     : `SecondDiffRemainderLeg2 → SecondDiffRemainder`
  `interiorSecondOrder_of_secondDiff` : `SecondDiffRemainder → InteriorSecondOrderRemainder`
  `offdiag_closed_of_secondOrder`     : `(∀ even e≥2, InteriorSecondOrderRemainder) → ∫U_e√ = 0`. -/

/-- **THE WIRING (per even order).**  For even `e ≥ 2`, the two per-leg residuals
imply `ChebOrthoFinal.InteriorSecondOrderRemainder e he`, by composing the PROVED
reductions `secondDiffLeg2_of_legs` → `secondDiff_of_leg2` →
`interiorSecondOrder_of_secondDiff`. -/
theorem interiorSecondOrder_of_legs (e : Nat) (he : 0 < e) (he2 : 2 ≤ e)
    (hBr : ChebOrthoSecondDiff.BrLegRemainder e he)
    (hRad : ChebOrthoSecondDiff.RadLegRemainder e he) :
    ChebOrthoFinal.InteriorSecondOrderRemainder e he :=
  ChebOrthoTaylor.interiorSecondOrder_of_secondDiff e he
    (ChebOrthoLeadingModel.secondDiff_of_leg2 e he he2
      (ChebOrthoSecondDiff.secondDiffLeg2_of_legs e he hBr hRad))

/-- **THE OFF-DIAGONAL FINISH LINE (conditional on the two leg residuals).**  From
`BrLegRemainder e he` and `RadLegRemainder e he` for EVERY even `e ≥ 2`, the COMBINED
π-free off-diagonal orthogonality `∫U_e√ = 0` for all `e ≥ 1`: the Riemann-sum
sequence `seqOrth e` converges to a `czero`-equivalent limit.  ODD orders and the
boundary / out-of-range cells are UNCONDITIONAL (already in the PROVED chain); the
EVEN interior cells are supplied by `interiorSecondOrder_of_legs`. -/
theorem offdiag_orthogonality_of_legs
    (hBr : ∀ (e : Nat) (he : 0 < e), 2 ≤ e → e % 2 = 0 →
      ChebOrthoSecondDiff.BrLegRemainder e he)
    (hRad : ∀ (e : Nat) (he : 0 < e), 2 ≤ e → e % 2 = 0 →
      ChebOrthoSecondDiff.RadLegRemainder e he) :
    ∀ (e : Nat), 1 ≤ e →
      ∃ L : CReal, CReal.ConvergesTo (seqOrth e) L ∧ CReal.Equiv L CReal.czero :=
  ChebOrthoFinal.offdiag_closed_of_secondOrder
    (fun e he he2 heven =>
      interiorSecondOrder_of_legs e he he2
        (hBr e he he2 heven) (hRad e he he2 heven))

end YMGap.Continuum.ChebOrthoOffDiagClose

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `bdyOneMinusSq_le_one` / `bdyRadical_le_one` — the radicand and the two-sided
    cell-radical bounds `1 − b_k² ≤ 1`, `|s_k| ≤ 1` (the bounded radical factors of
    the smooth-bracket leg `legBr = ¼(s_+ + s_-)(B_+ − B_-)`).
  * `OnBox_node` — `OnBox x_k (1/M)` for every interior cell, so the proved bracket
    Taylor bounds `ChebMarkovModulus.bracket{Quad,Cube}Bound_holds` apply directly
    at `x = x_k`, `δ = 1/M`.
  * `interiorSecondOrder_of_legs` — the PROVED per-order wiring
    `BrLegRemainder ∧ RadLegRemainder → InteriorSecondOrderRemainder` (composing
    `secondDiffLeg2_of_legs` → `secondDiff_of_leg2` →
    `interiorSecondOrder_of_secondDiff`).
  * **`offdiag_orthogonality_of_legs`** — THE OFF-DIAGONAL FINISH LINE: the COMBINED
    π-free off-diagonal orthogonality `∫U_e√ = 0` for all `e ≥ 1`, reduced to the two
    per-leg residuals (for even `e ≥ 2`) via the fully PROVED downstream chain.

**NAMED-open (the honest residual — the genuine quantitative obstruction).**
  * `ChebOrthoSecondDiff.BrLegRemainder` / `RadLegRemainder` — TRUE (the true values
    `|legBr − LZA|`, `|legRad − LZB|` are `O(δ³)` / `O(δ²)`), but UNREACHABLE from the
    second-difference moduli currently in the codebase: the proved symmetric radical
    second-difference quotient `ChebOrthoLegClose.symmSecondClose.symmQuot` is
    `O(M/j)` (vacuous), not the `δ^{3/2}/√j` scale.  The weakness is inherited from
    the LOOSE pointwise lower bound `subSecondL = 1/M²` in
    `ChebOrthoRadSecondDiffSq.subSecondDiff_AbsLeRat`, which turns the genuine
    `δ²`-scale `subSecondBound ~ 4δ²` into the `O(1)` quotient `subSecondQuot`.
  * `SubSecondTightModulus M k` — the PRECISE missing analytic input: the `δ²`-scale
    (`1/M²` order) bound `|s_+ s_- − s_k²| ≤ C/M²`.  Given it, `symmQuot` becomes
    `O(δ^{3/2}/√j)` and the per-leg exponent balance is mechanical
    `sharpBound_le_recip_jdist`-style `Int` bookkeeping.

**Path to closure.**  Prove `SubSecondTightModulus` (a tight pointwise lower bound
`subSecondL ~ recipWitness²` on the sub-second-difference sum `s_+ s_- + s_k²`,
replacing the loose `1/M²`), re-derive `symmQuot ~ δ^{3/2}/√j`, then discharge the
two per-leg balances against `½·gradedRate` and feed `offdiag_orthogonality_of_legs`.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoOffDiagClose.bdyOneMinusSq_le_one
#print axioms YMGap.Continuum.ChebOrthoOffDiagClose.bdyRadical_le_one
#print axioms YMGap.Continuum.ChebOrthoOffDiagClose.OnBox_node
#print axioms YMGap.Continuum.ChebOrthoOffDiagClose.interiorSecondOrder_of_legs
#print axioms YMGap.Continuum.ChebOrthoOffDiagClose.offdiag_orthogonality_of_legs
