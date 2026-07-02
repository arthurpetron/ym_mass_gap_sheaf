/-
Track A / R2 (track: 1-monotone) — the HONEST VERDICT on the scout's proposed factoring of
`FiniteSMarginWorstcase.CrossRatioMonotone` through two same-direction ratio-monotonicities, and the
correctly-located residual that survives it.

# The proposal under audit

The scout proposed to discharge, per mode `s`, the cross-ratio target

    (★)  cross s :  (S_s·S_{s+2})·(Sh_{s+1}·Sh_{s+1}) ≤ (Sh_s·Sh_{s+2})·(S_{s+1}·S_{s+1})

(where `S_N := acN w (s+1) N`, `Sh_N := acN wH (s+1) N`, i.e. the `w²`-monotonicity of the
log-concavity-defect ratio `R(w) := S_s·S_{s+2}/S_{s+1}²` on `[0, wH]`) via the two SAME-DIRECTION
sub-monotonicities

    (I)   S_s(w)·Sh_{s+1}   ≤ Sh_s·S_{s+1}(w)          ("S_s/S_{s+1} increasing in w")
    (II)  S_{s+2}(w)·Sh_{s+1} ≤ Sh_{s+2}·S_{s+1}(w)    ("S_{s+2}/S_{s+1} increasing in w").

# The verdict this module PROVES (all axiom-clean, `[propext]` / `[propext, Quot.sound]`)

1. **The factoring is VALID pure algebra** — `crossFromFactors` / `crossFromFactorsAcN` /
   `scoutFactoringToCrossRatio`.  A witness of both `(I)` and `(II)` (packaged as `ScoutFactoring w`)
   DOES inhabit `CrossRatioMonotone w`: multiply the two nonnegative inequalities and reassociate the
   four factors (`mul_swap4`).  So `(I)∧(II)` is a genuine *sufficient* condition — the algebra is
   not the problem.

2. **…but factor `(I)` is FALSE, so the factoring is a STRICT REGRESSION** — `factorI_false_s1`,
   `scoutFactoring_uninhabited`.  At the worst mode `s = 1`, evaluated at `w = 1/4` (`wLo`) vs.
   `wH = 1/2`, factor `(I)` reads `acN(2,1;¼)·acN(2,2;½) ≤ acN(2,1;½)·acN(2,2;¼)` and is FALSE by
   exact rational `decide`.  Hence `ScoutFactoring wLo → False`: the scout's sufficient condition is
   itself uninhabitable, so it inhabits nothing — it replaces a TRUE goal by a FALSE subgoal.

3. **The target it replaces is TRUE and factor `(II)` holds** — `crossTarget_true_s1`,
   `factorII_true_s1`, `factoring_is_strict_regression`.  At the same `(s=1, w=¼)` the cross-ratio
   target `cross 1` holds and `(II)` holds; only `(I)` fails.  So the split reduces a satisfiable goal
   to an unsatisfiable one: a regression, not a relocation.  Reason: `S_s/S_{s+1}` sits at a *lower*
   total θ-exponent and is DECREASING in `w`; the two ratios genuinely oppose, and `R` increases only
   because the `(II)`-factor wins by an exponent margin — no same-direction split exists.

4. **The `216 ≤ 0` lacunary collision is NOT dissolved by factoring — it reappears as `16 ≤ 0`** —
   `facI_mlr_false`, `facI_arrayMLR_uninhabited`.  Any TP₂/`ArrayMLR` certificate for `(I)` (arrays
   `a = S_1 = (exp3:4)`, `m = S_2 = (exp6:4, exp8:3)`) forces at `e_k = 3 < e_j = 6` the inequality
   `a_k·m_j ≤ a_j·m_k`, i.e. `4·4 ≤ 0·0`, i.e. `16 ≤ 0` — the SAME lacunary obstruction as the
   `216 ≤ 0` of `AdjacentMLR.cross_false`, merely relocated.  The numerator array sits *below* the
   denominator, so disjoint support makes the MLR FALSE (not vacuous) — the scout inverted the
   support asymmetry that makes `(II)` (numerator *above*) genuinely close.

# The correctly-located residual (unchanged)

`FiniteSMarginWorstcase.CrossRatioMonotone w` (general `w`) remains the correct open node — it must
NOT be replaced by `ScoutFactoring`.  Its honest, non-pairwise content is the convexity-in-`N` of the
mean θ-exponent of the autoconvolution weight `S_N` (a variance / local-CLT inequality), for which no
TP₂/MLR certificate exists on any two-array split.  This module does NOT inhabit it; it only proves
that the proposed factoring is unsound and refutes it precisely.  NAMED-OPEN (never `sorry`).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `acN`/`coeffW`/`qpow` finite-sum algebra, `mul_swap4`
reassociation, and `decide` on closed concrete-rational / integer facts.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` / `propext, Quot.sound` only.
No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.CrossRatioMonotone
import YMGap.Continuum.AcNReserveAnalytic

namespace YMGap.Continuum.FiniteSMarginWorstcaseProof

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionGenFunction

/-! ## 0. Small helper: product of two nonnegative inequalities. -/

/-- **`mulLeMulBoth`** — two-sided product monotonicity `x ≤ X`, `y ≤ Y`, `0 ≤ y`, `0 ≤ X` ⟹
`x·y ≤ X·Y` (Mathlib-free; chains the two one-sided `Q'` lemmas). -/
private theorem mulLeMulBoth {x y X Y : Q'} (hx : x ≤ X) (hy : y ≤ Y)
    (h0y : (0 : Q') ≤ y) (h0X : (0 : Q') ≤ X) : x * y ≤ X * Y :=
  Q'.le_trans' (x * y) (X * y) (X * Y)
    (Q'.mul_le_mul_of_nonneg_right x X y hx h0y)
    (Q'.mul_le_mul_of_nonneg_left y Y X hy h0X)

/-! ## 1. The scout's proposed sufficient condition, packaged. -/

/-- **`ScoutFactoring w`** — the scout's two same-direction ratio-monotonicities, per mode.  Field
`facI` is `(I)` (`S_s/S_{s+1}` increasing) and `facII` is `(II)` (`S_{s+2}/S_{s+1}` increasing).
This module proves `ScoutFactoring w → CrossRatioMonotone w` (valid algebra) AND that `ScoutFactoring`
is uninhabitable at `w = 1/4` (`facI` is FALSE) — so it is a strict regression, never to be adopted.
-/
structure ScoutFactoring (w : Q') : Type where
  /-- `(I)`: `S_s(w)·Sh_{s+1} ≤ Sh_s·S_{s+1}(w)`. -/
  facI : ∀ s,
    acN w (s + 1) s * acN wH (s + 1) (s + 1)
      ≤ acN wH (s + 1) s * acN w (s + 1) (s + 1)
  /-- `(II)`: `S_{s+2}(w)·Sh_{s+1} ≤ Sh_{s+2}·S_{s+1}(w)`. -/
  facII : ∀ s,
    acN w (s + 1) (s + 2) * acN wH (s + 1) (s + 1)
      ≤ acN wH (s + 1) (s + 2) * acN w (s + 1) (s + 1)

/-! ## 2. The factoring is VALID pure algebra. -/

/-- **`crossFromFactors`** — the abstract four-factor multiply.  From `(I)` `Ss·Ts1 ≤ Ts·Ss1`,
`(II)` `Ss2·Ts1 ≤ Ts2·Ss1` and nonnegativity of the right-hand factors, conclude the cross-ratio
inequality `(Ss·Ss2)·(Ts1·Ts1) ≤ (Ts·Ts2)·(Ss1·Ss1)` — multiply the two nonnegative inequalities
(`mulLeMulBoth`) and reassociate both sides (`mul_swap4`).  This is the genuine content of the
scout's claim: the factoring IS algebraically sound. -/
theorem crossFromFactors {Ss Ss1 Ss2 Ts Ts1 Ts2 : Q'}
    (hSs2 : (0 : Q') ≤ Ss2) (hTs1 : (0 : Q') ≤ Ts1)
    (hTs : (0 : Q') ≤ Ts) (hSs1 : (0 : Q') ≤ Ss1)
    (hI : Ss * Ts1 ≤ Ts * Ss1) (hII : Ss2 * Ts1 ≤ Ts2 * Ss1) :
    (Ss * Ss2) * (Ts1 * Ts1) ≤ (Ts * Ts2) * (Ss1 * Ss1) := by
  have hprod : (Ss * Ts1) * (Ss2 * Ts1) ≤ (Ts * Ss1) * (Ts2 * Ss1) :=
    mulLeMulBoth hI hII (Q'.mul_nonneg _ _ hSs2 hTs1) (Q'.mul_nonneg _ _ hTs hSs1)
  have eL : ((Ss * Ts1) * (Ss2 * Ts1)).eqv ((Ss * Ss2) * (Ts1 * Ts1)) :=
    mul_swap4 Ss Ts1 Ss2 Ts1
  have eR : ((Ts * Ss1) * (Ts2 * Ss1)).eqv ((Ts * Ts2) * (Ss1 * Ss1)) :=
    mul_swap4 Ts Ss1 Ts2 Ss1
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv eL) (Q'.le_trans' _ _ _ hprod (Q'.le_of_eqv eR))

/-- **`crossFromFactorsAcN`** — `crossFromFactors` specialized to the actual `acN` weights at mode
`s`: `(I)` and `(II)` imply the `cross s` field of `CrossRatioMonotone`, using `acN_nonneg` for the
four nonnegativity side-conditions. -/
theorem crossFromFactorsAcN {w : Q'} (hw0 : (0 : Q') ≤ w) (s : Nat)
    (hI : acN w (s + 1) s * acN wH (s + 1) (s + 1)
            ≤ acN wH (s + 1) s * acN w (s + 1) (s + 1))
    (hII : acN w (s + 1) (s + 2) * acN wH (s + 1) (s + 1)
            ≤ acN wH (s + 1) (s + 2) * acN w (s + 1) (s + 1)) :
    (acN w (s + 1) s * acN w (s + 1) (s + 2)) * (acN wH (s + 1) (s + 1) * acN wH (s + 1) (s + 1))
      ≤ (acN wH (s + 1) s * acN wH (s + 1) (s + 2))
        * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1)) :=
  crossFromFactors (acN_nonneg hw0 _ _) (acN_nonneg (by decide) _ _)
    (acN_nonneg (by decide) _ _) (acN_nonneg hw0 _ _) hI hII

/-- **`scoutFactoringToCrossRatio` — the valid reduction.**  A `ScoutFactoring w` witness (with
`0 ≤ w`) inhabits `FiniteSMarginWorstcase.CrossRatioMonotone w`: the scout's factoring IS a genuine
sufficient condition.  (It is nonetheless useless — see §3: no such witness exists.) -/
def scoutFactoringToCrossRatio {w : Q'} (hw0 : (0 : Q') ≤ w) (H : ScoutFactoring w) :
    FiniteSMarginWorstcase.CrossRatioMonotone w where
  cross := fun s => crossFromFactorsAcN hw0 s (H.facI s) (H.facII s)

/-! ## 3. …but factor `(I)` is FALSE — the factoring is a STRICT REGRESSION. -/

/-- The falsifying interior point `w = 1/4` (`wH = 1/2` is the worst case). -/
def wLo : Q' := Q'.mkPos 1 4 (by decide)

/-- **`factorI_false_s1`** — factor `(I)` at mode `s = 1` is FALSE at `w = 1/4`.  It reads
`acN(2,1;¼)·acN(2,2;½) ≤ acN(2,1;½)·acN(2,2;¼)`, i.e. (with `S_1 = 4w³`, `S_2 = 4w⁶+3w⁸`)
`(4·¼³)·(4·½⁶+3·½⁸) ≤ (4·½³)·(4·¼⁶+3·¼⁸)`, false by exact rational `decide` (LHS ≈ 9× RHS). -/
theorem factorI_false_s1 :
    ¬ (acN wLo 2 1 * acN wH 2 2 ≤ acN wH 2 1 * acN wLo 2 2) := by decide

/-- **`factorII_true_s1`** — factor `(II)` at `s = 1`, `w = 1/4`, DOES hold (`decide`).  Its
numerator `S_{s+2}` sits at a *higher* total θ-exponent, so `S_{s+2}/S_{s+1}` is genuinely
increasing in `w`. -/
theorem factorII_true_s1 :
    acN wLo 2 3 * acN wH 2 2 ≤ acN wH 2 3 * acN wLo 2 2 := by decide

/-- **`crossTarget_true_s1`** — the cross-ratio TARGET `cross 1` DOES hold at `w = 1/4` (`decide`).
So the goal the scout replaces is satisfiable. -/
theorem crossTarget_true_s1 :
    (acN wLo 2 1 * acN wLo 2 3) * (acN wH 2 2 * acN wH 2 2)
      ≤ (acN wH 2 1 * acN wH 2 3) * (acN wLo 2 2 * acN wLo 2 2) := by decide

/-- **`factoring_is_strict_regression`** — the packaged verdict at `(s = 1, w = ¼)`: the TARGET
holds, factor `(II)` holds, but factor `(I)` FAILS.  So `(I)∧(II) → cross` reduces a TRUE goal to a
FALSE subgoal plus a true one — a strict regression, not a relocation. -/
theorem factoring_is_strict_regression :
    ((acN wLo 2 1 * acN wLo 2 3) * (acN wH 2 2 * acN wH 2 2)
        ≤ (acN wH 2 1 * acN wH 2 3) * (acN wLo 2 2 * acN wLo 2 2))
      ∧ (acN wLo 2 3 * acN wH 2 2 ≤ acN wH 2 3 * acN wLo 2 2)
      ∧ ¬ (acN wLo 2 1 * acN wH 2 2 ≤ acN wH 2 1 * acN wLo 2 2) :=
  ⟨crossTarget_true_s1, factorII_true_s1, factorI_false_s1⟩

/-- **`scoutFactoring_uninhabited` — THE VERDICT.**  `ScoutFactoring wLo` is uninhabitable: its
`facI 1` field is exactly the false inequality `factorI_false_s1`.  So the scout's sufficient
condition inhabits nothing — adding it is a strict regression, never a step toward closing
`CrossRatioMonotone`. -/
theorem scoutFactoring_uninhabited : ScoutFactoring wLo → False :=
  fun H => factorI_false_s1 (H.facI 1)

/-! ## 4. The `216 ≤ 0` lacunary collision reappears as `16 ≤ 0` in `(I)`. -/

/-- **`aFacI`** — the numerator array of the `(I)`-ratio `S_1/S_2` on the shared exponent grid
`{3,6,8}` (indices `0,1,2`): `S_1 = 4w³` gives `a = (4, 0, 0)`.  Support `{3}` — it lives *below* the
denominator. -/
def aFacI : Nat → Q'
  | 0 => Q'.ofNat 4
  | _ => 0

/-- **`mFacI`** — the denominator array of the `(I)`-ratio on `{3,6,8}`: `S_2 = 4w⁶+3w⁸` gives
`m = (0, 4, 3)`.  Support `{6,8}`.  Its structural zero at index `0` (exp `3`) is what makes the MLR
FALSE (not vacuous): the numerator sits below it. -/
def mFacI : Nat → Q'
  | 1 => Q'.ofNat 4
  | 2 => Q'.ofNat 3
  | _ => 0

/-- **`eFacI`** — the shared exponent grid `{3,6,8}` at indices `0,1,2`. -/
def eFacI : Nat → Nat
  | 0 => 3
  | 1 => 6
  | 2 => 8
  | _ => 0

/-- **`facI_mlr_false`** — the exact integer collision.  Any MLR/TP₂ certificate for `(I)` forces at
`e_k = 3 < e_j = 6` (indices `k=0`, `j=1`) the inequality `a_k·m_j ≤ a_j·m_k`, i.e. `4·4 ≤ 0·0`,
i.e. `16 ≤ 0` — FALSE.  This is the `216 ≤ 0` of `AdjacentMLR.cross_false` merely relocated by the
factoring, NOT dissolved. -/
theorem facI_mlr_false : ¬ (aFacI 0 * mFacI 1 ≤ aFacI 1 * mFacI 0) := by decide

/-- **`facI_arrayMLR_uninhabited`** — packaged: no `ArrayMLR` (pointwise TP₂) certificate exists for
factor `(I)`'s arrays.  Feeding any witness at `(j,k) = (1,0)` (with `e 0 = 3 < e 1 = 6`) yields the
false `16 ≤ 0`.  So `crossTP2`/`ArrayMLR` cannot discharge `(I)` any more than it discharges the
product arrays — the lacunary obstruction is intrinsic, not an artifact of the squaring. -/
theorem facI_arrayMLR_uninhabited :
    CrossRatioMonotone.ArrayMLR aFacI mFacI eFacI → False :=
  fun H => facI_mlr_false (H.mlr 1 0 (by decide))

/-! ## 5. PROVED vs. NAMED-open (honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `crossFromFactors` / `crossFromFactorsAcN` / `scoutFactoringToCrossRatio` — the factoring is
    VALID pure algebra: `ScoutFactoring w → CrossRatioMonotone w`.
  * `factorI_false_s1` — factor `(I)` at `(s=1, w=¼)` is FALSE (exact rational `decide`).
  * `factorII_true_s1` / `crossTarget_true_s1` — `(II)` and the TARGET both hold at the same point.
  * `factoring_is_strict_regression` — packaged: TRUE target + TRUE `(II)` + FALSE `(I)`.
  * `scoutFactoring_uninhabited` — `ScoutFactoring wLo → False`: the sufficient condition inhabits
    nothing (strict regression).
  * `facI_mlr_false` / `facI_arrayMLR_uninhabited` — the `216 ≤ 0` collision reappears as `16 ≤ 0`
    in `(I)`; no TP₂/`ArrayMLR` certificate exists for `(I)` either.

NAMED OPEN (Type-level structure, unchanged, never `sorry`):
  * `FiniteSMarginWorstcase.CrossRatioMonotone w` — the correctly-located residual.  Its honest
    non-pairwise content is the convexity-in-`N` of the mean θ-exponent of `S_N`; no two-array
    TP₂/MLR split captures it.  This module does NOT inhabit it and does NOT replace it.

HONEST VERDICT.  The scout's `(I)∧(II) → CrossRatioMonotone` factoring is algebraically valid but
UNSOUND to adopt: factor `(I)` is false, so `ScoutFactoring` is uninhabitable — a strict regression
that turns a true, satisfiable goal into a false one.  The `216 ≤ 0` lacunary collision is not
dissolved; it reappears as `16 ≤ 0`.  `CrossRatioMonotone` remains the correct open node.  This is a
sharp precise refutation of a proposed sub-step; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FiniteSMarginWorstcaseProof

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FiniteSMarginWorstcaseProof.crossFromFactors
#print axioms YMGap.Continuum.FiniteSMarginWorstcaseProof.crossFromFactorsAcN
#print axioms YMGap.Continuum.FiniteSMarginWorstcaseProof.scoutFactoringToCrossRatio
#print axioms YMGap.Continuum.FiniteSMarginWorstcaseProof.factorI_false_s1
#print axioms YMGap.Continuum.FiniteSMarginWorstcaseProof.factorII_true_s1
#print axioms YMGap.Continuum.FiniteSMarginWorstcaseProof.crossTarget_true_s1
#print axioms YMGap.Continuum.FiniteSMarginWorstcaseProof.factoring_is_strict_regression
#print axioms YMGap.Continuum.FiniteSMarginWorstcaseProof.scoutFactoring_uninhabited
#print axioms YMGap.Continuum.FiniteSMarginWorstcaseProof.facI_mlr_false
#print axioms YMGap.Continuum.FiniteSMarginWorstcaseProof.facI_arrayMLR_uninhabited
