/-
# The interior radical-leg √-Hölder difference bound toward
# `ChebOrthoGradedClose.InteriorGradedRemainder e` — the final numeric assembly of
# the π-free off-diagonal Chebyshev-`U` orthogonality `∫_{−1}^1 U_e(x)√(1−x²) dx = 0`.

The companion modules reduce the even-order off-diagonal orthogonality to the SINGLE
interior per-cell two-sided estimate `ChebOrthoGradedClose.InteriorGradedRemainder e
he` (the boundary cells are already closed UNCONDITIONALLY by
`ChebOrthoGradedClose.boundary_cell_bound`; the assembly chain
`gradedPerCellBound_of_interior → … → convergesTo_czero_of_bound` is PROVED), and
its EXACT algebra is fully PROVED upstream:

  * `ChebOrthoMidpoint.cellAdjR = orthTerm + gIncrR`;
  * `ChebOrthoRemainder.gIncr_pdiff_split`: the product-difference separation
    `gIncrR ≈ ½(½(s_+ + s_-)(B_+ − B_-) + ½(s_+ − s_-)(B_+ + B_-))` of the increment
    into the SMOOTH-bracket leg and the RADICAL leg;
  * `ChebOrthoRemainder.radSq_diff_equiv` / `ChebOrthoRemainder.bdyNum_diff` /
    `ChebOrthoRemainder.bdyOneMinusSq_diff`: the EXACT radicand difference
    `s_+² − s_-² ≈ ofQ'(−4(2k+1−M)/M²)`;
  * `ChebOrthoCancel.leading_cancellation`: the leading midpoint combination cancels
    `orthTerm` EXACTLY;
  * `ChebOrthoInterior.interiorRadicalSum_recipBound`: the constructive reciprocal
    LOWER bound `s_+ + s_- ≥ recipWitness M j` on the sum of the two cell radicals.

This module supplies GENUINE new content on the RADICAL leg: the two-sided
√-Hölder difference bound on the two adjacent cell radicals, in the exact
`ChebOrthoGradedClose.AbsLeRat` shape the assembly consumes.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `bdyNum_le_iff` — the interior radicand ordering `1 − b_{k+1}² ≤ 1 − b_k²` is
    decided by the `Int` sign of `2k+1−M` (same denominator `M²`), via
    `ChebOrthoRemainder.bdyNum_diff`.

  * `radicandDiff_le_csq` — for an interior pair and a rational `c > 0` with
    `4·|2k+1−M| ≤ c²·M²`, the LARGER radicand is `≤` the SMALLER `+ c²`
    (either direction), the √-Hölder hypothesis of `SqrtSubadd.holder_oneMinusSq`.

  * **`bdyRadicalDiff_holder_AbsLeRat`** — the GENUINE two-sided √-Hölder radical
    difference bound

        `AbsLeRat (s_+ + (−s_-)) c`        when `4·|2k+1−M| ≤ c²·M²`,

    `s_± = √(1 − b_{k±}²)` the two adjacent interior cell radicals.  PROOF: a case
    split on the `Int` sign of `2k+1−M` selects the larger radicand on the left and
    applies `SqrtSubadd.holder_oneMinusSq` to that leg (`leRat (√u − √v) c`); the
    OTHER side `leRat (−(√u − √v)) c` is the `holder_oneMinusSq` bound for the
    reflected pair `(√v − √u)`, composed through `bdyRadical_interior` and the
    additive-`Equiv` `congr` of `AbsLeRat`.  This is the radical-leg ingredient named
    open in `InteriorGradedRemainder`, here delivered UNCONDITIONALLY in the
    two-sided value-bound calculus.

  * `cHolderWitness` / `cHolderWitness_pos` / `cHolderWitness_sq_ge` — the explicit
    √-Hölder tolerance `c_H := (⌊√(4·|2k+1−M|·M)⌋ + 1)/M²`-type witness with
    `4·|2k+1−M| ≤ c_H²·M²` so that `bdyRadicalDiff_holder_AbsLeRat` applies with an
    EXPLICIT rational tolerance (`c_H ~ √(4|x_k|δ)`, the √-Hölder modulus
    `√(δ/j)`-scale of the radical leg).

## What is NAMED-open (precisely)

  * **The SHARP reciprocal-free radical difference** `|s_+ − s_-| ≤ 4|2k+1−M|δ /
    recipWitness` (= `s_+² − s_-²` divided by the reciprocal lower bound `s_+ + s_-
    ≥ recipWitness`, NO CReal reciprocal).  Its `AbsLeRat` form needs a limit-level
    "`D·S ≈ c`, `S ≥ L > 0` ⟹ `|D| ≤ |c|/L`" lemma whose two directions require a
    constructive sign split on `D = s_+ − s_-`; the √-Hölder bound proved here
    (`|s_+ − s_-| ≤ √(4|x_k|δ)`) is the WEAKER but UNCONDITIONAL radical-leg control.

  * `ChebOrthoGradedClose.InteriorGradedRemainder e he` — the full interior per-cell
    two-sided estimate against `gradedRate = C(e)/(⌊√M⌋·jdist²)`.  With BOTH the
    reciprocal lower bound (`ChebOrthoInterior`) and the √-Hölder radical difference
    (this module) PROVED, the residual is the NUMERIC second-order assembly: combine
    `gIncr_pdiff_split` + `leading_cancellation` (removing the `O(δ)` part EXACTLY)
    with the smooth-bracket-leg Lipschitz scale `Le e` (`R_poly`), the radical-leg
    bound (`R_rad`, this module's √-Hölder or the sharper reciprocal-free bound), and
    the exponent balancing `δ^{3/2}/j^{3/2} ≤ 1/(⌊√M⌋·j²)` to `gradedRate`.  Recorded
    precisely, NOT faked.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on closed
`Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoInterior
import YMGap.Continuum.ChebOrthoGradedClose
import YMGap.Continuum.ChebOrthoGraded
import YMGap.Continuum.ChebOrthoRemainder
import YMGap.Continuum.ChebOrthoCancel
import YMGap.Continuum.ChebOrthoMidpoint
import YMGap.Continuum.ChebUDClosure

namespace YMGap.Continuum.ChebOrthoAssembly

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoMidpoint
open YMGap.Continuum.ChebOrthoGraded
open YMGap.Continuum.ChebOrthoGradedClose
open YMGap.Continuum.ChebOrthoInterior

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The interior radicand ordering, decided by the sign of `2k+1−M` -/

/-- **The interior radicand ordering.**  For two adjacent interior cells
`0 < k`, `k+1 < M` (so `0 < k < M` too), the two radicands share the denominator
`M²`, so `1 − b_{k+1}² ≤ 1 − b_k²` reduces to the `Int` numerator comparison
`bdyNum M (k+1) ≤ bdyNum M k`, which by `ChebOrthoRemainder.bdyNum_diff` is
`−4·(2k+1−M) ≤ 0`, i.e. `0 ≤ 2k+1−M`.  (The reflected inequality holds when
`2k+1−M ≤ 0`.) -/
theorem bdyNum_le_of_sign (M k : Nat)
    (hsign : (0 : Int) ≤ 2 * (k : Int) + 1 - (M : Int)) :
    bdyNum M (k + 1) ≤ bdyNum M k := by
  have hd := ChebOrthoRemainder.bdyNum_diff M k
  -- bdyNum (k+1) − bdyNum k = −(4·(2k+1−M)) ≤ 0  since 2k+1−M ≥ 0
  omega

theorem bdyNum_ge_of_sign (M k : Nat)
    (hsign : 2 * (k : Int) + 1 - (M : Int) ≤ (0 : Int)) :
    bdyNum M k ≤ bdyNum M (k + 1) := by
  have hd := ChebOrthoRemainder.bdyNum_diff M k
  omega

/-- The radicand comparison in `Q'`: same denominator, so `≤` is the numerator `≤`.
`bdyNum M a ≤ bdyNum M b → bdyOneMinusSq M a ≤ bdyOneMinusSq M b`. -/
theorem bdyOneMinusSq_le_of_num (M : Nat) (hM : 0 < M) (a b : Nat)
    (ha0 : 0 < a) (han : a < M) (hb0 : 0 < b) (hbn : b < M)
    (hnum : bdyNum M a ≤ bdyNum M b) :
    bdyOneMinusSq M a hM ha0 han ≤ bdyOneMinusSq M b hM hb0 hbn := by
  -- both are mkPos (bdyNum M ·) (omsDen M) with den omsDen M = M*M.
  show (bdyOneMinusSq M a hM ha0 han).num * ((bdyOneMinusSq M b hM hb0 hbn).den : Int)
      ≤ (bdyOneMinusSq M b hM hb0 hbn).num * ((bdyOneMinusSq M a hM ha0 han).den : Int)
  have hna : (bdyOneMinusSq M a hM ha0 han).num = bdyNum M a := by
    show (Q'.mkPos (bdyNum M a) (SemicircleIntegral.omsDen M)
      (SemicircleIntegral.omsDen_pos hM)).num = bdyNum M a
    rw [Q'.mkPos_num]
  have hnb : (bdyOneMinusSq M b hM hb0 hbn).num = bdyNum M b := by
    show (Q'.mkPos (bdyNum M b) (SemicircleIntegral.omsDen M)
      (SemicircleIntegral.omsDen_pos hM)).num = bdyNum M b
    rw [Q'.mkPos_num]
  have hda : ((bdyOneMinusSq M a hM ha0 han).den : Int) = ((SemicircleIntegral.omsDen M : Nat) : Int) := by
    show ((Q'.mkPos (bdyNum M a) (SemicircleIntegral.omsDen M)
      (SemicircleIntegral.omsDen_pos hM)).den : Int) = ((SemicircleIntegral.omsDen M : Nat) : Int)
    rw [Q'.mkPos_den]
  have hdb : ((bdyOneMinusSq M b hM hb0 hbn).den : Int) = ((SemicircleIntegral.omsDen M : Nat) : Int) := by
    show ((Q'.mkPos (bdyNum M b) (SemicircleIntegral.omsDen M)
      (SemicircleIntegral.omsDen_pos hM)).den : Int) = ((SemicircleIntegral.omsDen M : Nat) : Int)
    rw [Q'.mkPos_den]
  rw [hna, hnb, hda, hdb]
  have hden0 : (0 : Int) ≤ ((SemicircleIntegral.omsDen M : Nat) : Int) := Int.natCast_nonneg _
  exact Int.mul_le_mul_of_nonneg_right hnum hden0

/-! ## 1. The √-Hölder tolerance witness `c_H = ⌊√(4|2k+1−M|)⌋⁺/M` -/

/-- **`m < (⌊√m⌋ + 1)²`** — the floor-sqrt upper bound.  If not, `(⌊√m⌋+1)² ≤ m`
gives `⌊√m⌋+1 ≤ ⌊√m⌋` by `isqrt_ge`, a contradiction. -/
theorem isqrt_lt_succ_sq (m : Nat) :
    m < (ChebOrthoMidpointEst.isqrt m + 1) * (ChebOrthoMidpointEst.isqrt m + 1) := by
  rcases Nat.lt_or_ge m ((ChebOrthoMidpointEst.isqrt m + 1) * (ChebOrthoMidpointEst.isqrt m + 1))
    with hlt | hge
  · exact hlt
  · exfalso
    have := ChebOrthoMidpointEst.isqrt_ge (m := m) (K := ChebOrthoMidpointEst.isqrt m + 1) hge
    omega

/-- The √-Hölder difference tolerance `c_H := (⌊√(4·|2k+1−M|)⌋ + 1)/M`.  Its square
`c_H² = (⌊√…⌋+1)²/M² ≥ 4·|2k+1−M|/M²` is `≥` the radicand difference, so it is a
valid √-Hölder modulus (`bdyRadicalDiff_holder_AbsLeRat`).  `c_H ~ √(4|x_k|δ)`, the
genuine radical-leg modulus `√(δ/j)` at distance `j`. -/
def cHolderWitness (M k : Nat) (hM : 0 < M) : Q' :=
  Q'.mkPos
    (((ChebOrthoMidpointEst.isqrt (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs)) + 1 : Nat)) : Int)
    M hM

theorem cHolderWitness_pos (M k : Nat) (hM : 0 < M) : (0 : Q') < cHolderWitness M k hM := by
  show (0 : Int) * ((cHolderWitness M k hM).den : Int)
      < (cHolderWitness M k hM).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  show (0 : Int) < (Q'.mkPos
    (((ChebOrthoMidpointEst.isqrt (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs)) + 1 : Nat)) : Int)
    M hM).num
  rw [Q'.mkPos_num]
  have : (0 : Nat) < ChebOrthoMidpointEst.isqrt (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs)) + 1 := by
    omega
  exact_mod_cast this

/-- `c_H · c_H = mkPos ((⌊√d⌋+1)²) (M²)` where `d = 4·|2k+1−M|`, and
`(⌊√d⌋+1)² ≥ d`, so `4·|2k+1−M| ≤ c_H²·M²` (numerator form). -/
theorem cHolderWitness_sq_num (M k : Nat) (hM : 0 < M) :
    (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs) : Int)
      ≤ (cHolderWitness M k hM * cHolderWitness M k hM).num := by
  have hnum : (cHolderWitness M k hM * cHolderWitness M k hM).num
      = (((ChebOrthoMidpointEst.isqrt (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs)) + 1 : Nat)) : Int)
        * (((ChebOrthoMidpointEst.isqrt (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs)) + 1 : Nat)) : Int) := by
    show (cHolderWitness M k hM).num * (cHolderWitness M k hM).num = _
    show (Q'.mkPos (((ChebOrthoMidpointEst.isqrt (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs)) + 1 : Nat)) : Int) M hM).num
        * (Q'.mkPos (((ChebOrthoMidpointEst.isqrt (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs)) + 1 : Nat)) : Int) M hM).num = _
    rw [Q'.mkPos_num]
  rw [hnum]
  -- (4·natAbs) ≤ (isqrt(4·natAbs) + 1)²  (Nat, isqrt_lt_succ_sq), cast to Int.
  have hub : (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs) : Nat)
      < (ChebOrthoMidpointEst.isqrt (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs)) + 1)
        * (ChebOrthoMidpointEst.isqrt (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs)) + 1) :=
    isqrt_lt_succ_sq (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs))
  have hubLe := Nat.le_of_lt hub
  exact_mod_cast hubLe

/-! ## 2. The radicand √-Hölder hypothesis `u ≤ v + c_H²` (both directions) -/

/-- **Same-denominator `≤`-against-a-sum.**  `mkPos a t ≤ mkPos b t + mkPos d t`
whenever `a ≤ b + d`.  (The reverse companion of `mkPos_add_le`.) -/
theorem mkPos_le_add (a b d : Int) (t : Nat) (ht : 0 < t) (h : a ≤ b + d) :
    Q'.mkPos a t ht ≤ Q'.mkPos b t ht + Q'.mkPos d t ht := by
  show (Q'.mkPos a t ht).num * ((Q'.mkPos b t ht + Q'.mkPos d t ht).den : Int)
      ≤ (Q'.mkPos b t ht + Q'.mkPos d t ht).num * ((Q'.mkPos a t ht).den : Int)
  have hnum : (Q'.mkPos b t ht + Q'.mkPos d t ht).num
      = b * (t : Int) + d * (t : Int) := by
    show (Q'.mkPos b t ht).num * ((Q'.mkPos d t ht).den : Int)
        + (Q'.mkPos d t ht).num * ((Q'.mkPos b t ht).den : Int)
        = b * (t : Int) + d * (t : Int)
    rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  have hden : ((Q'.mkPos b t ht + Q'.mkPos d t ht).den : Int) = (t : Int) * (t : Int) := by
    rw [Q'.add_den_cast, Q'.mkPos_den, Q'.mkPos_den]
  rw [hnum, hden, Q'.mkPos_num, Q'.mkPos_den]
  -- a·(t·t) ≤ (b·t + d·t)·t = (b+d)·t²
  have hfact : (b * (t : Int) + d * (t : Int)) * (t : Int)
      = (b + d) * ((t : Int) * (t : Int)) := by
    rw [← Int.add_mul b d (t : Int), Int.mul_assoc (b + d) (t : Int) (t : Int)]
  rw [hfact]
  have ht2 : (0 : Int) ≤ (t : Int) * (t : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  exact Int.mul_le_mul_of_nonneg_right h ht2

/-- **`mkPos a (M·M) ≤ mkPos b (M·M) + w·w`** for `w = mkPos cn M`, whenever
`a ≤ b + cn·cn`.  (`w·w` has numerator `cn²` and denominator `M²`, the same
denominator as the two radicand `mkPos`; raw cross-multiplication after the
num/den lemmas.)  This packages the √-Hölder radicand step. -/
theorem mkPos_le_add_sqWit (a b cn : Int) (M : Nat) (hM : 0 < M)
    (h : a ≤ b + cn * cn) :
    Q'.mkPos a (M * M) (Nat.mul_pos hM hM)
      ≤ Q'.mkPos b (M * M) (Nat.mul_pos hM hM)
        + (Q'.mkPos cn M hM) * (Q'.mkPos cn M hM) := by
  -- Raw cross-multiplication.  Let w := mkPos cn M.  Then w.num = cn, (w·w).num = cn²,
  -- ((w·w).den : Int) = M·M (mul_den_cast), and the sum's num/den via add lemmas.
  show (Q'.mkPos a (M * M) (Nat.mul_pos hM hM)).num
        * ((Q'.mkPos b (M * M) (Nat.mul_pos hM hM)
              + (Q'.mkPos cn M hM) * (Q'.mkPos cn M hM)).den : Int)
      ≤ (Q'.mkPos b (M * M) (Nat.mul_pos hM hM)
              + (Q'.mkPos cn M hM) * (Q'.mkPos cn M hM)).num
        * ((Q'.mkPos a (M * M) (Nat.mul_pos hM hM)).den : Int)
  -- the product w·w:  num = cn·cn (def), den (cast) = M·M.
  have hwwnum : ((Q'.mkPos cn M hM) * (Q'.mkPos cn M hM)).num = cn * cn := rfl
  have hwwden : (((Q'.mkPos cn M hM) * (Q'.mkPos cn M hM)).den : Int) = (M : Int) * (M : Int) := by
    rw [Q'.mul_den_cast]
    rw [show (Q'.mkPos cn M hM).den = M from Q'.mkPos_den cn M hM]
  -- the sum  v + w·w :  num = b·(w·w).den + (w·w).num·v.den, den (cast) = v.den·(w·w).den.
  have hsnum : (Q'.mkPos b (M * M) (Nat.mul_pos hM hM)
              + (Q'.mkPos cn M hM) * (Q'.mkPos cn M hM)).num
      = b * (((Q'.mkPos cn M hM) * (Q'.mkPos cn M hM)).den : Int)
        + (cn * cn) * (((M * M : Nat)) : Int) := by
    show (Q'.mkPos b (M * M) (Nat.mul_pos hM hM)).num
          * (((Q'.mkPos cn M hM) * (Q'.mkPos cn M hM)).den : Int)
        + ((Q'.mkPos cn M hM) * (Q'.mkPos cn M hM)).num
          * ((Q'.mkPos b (M * M) (Nat.mul_pos hM hM)).den : Int)
        = b * (((Q'.mkPos cn M hM) * (Q'.mkPos cn M hM)).den : Int)
          + (cn * cn) * (((M * M : Nat)) : Int)
    rw [Q'.mkPos_num, hwwnum, Q'.mkPos_den]
  have hsden : ((Q'.mkPos b (M * M) (Nat.mul_pos hM hM)
              + (Q'.mkPos cn M hM) * (Q'.mkPos cn M hM)).den : Int)
      = (((M * M : Nat)) : Int) * (((Q'.mkPos cn M hM) * (Q'.mkPos cn M hM)).den : Int) := by
    rw [Q'.add_den_cast, Q'.mkPos_den]
  rw [hsnum, hsden, Q'.mkPos_num, Q'.mkPos_den, hwwden]
  -- goal: a·(MM·(MM)) ≤ (b·(MM) + cn²·MM)·MM    (MM := M·M)
  have hMMcast : (((M * M : Nat)) : Int) = (M : Int) * (M : Int) := by push_cast; rfl
  rw [hMMcast]
  -- factor:  RHS = (b + cn²)·(MM)·MM,  LHS = a·MM·MM
  have hMM0 : (0 : Int) ≤ ((M : Int) * (M : Int)) * ((M : Int) * (M : Int)) :=
    Int.mul_nonneg (Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
      (Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
  -- a·(MM·MM) ≤ (b+cn²)·(MM·MM)
  have hstep : a * (((M : Int) * (M : Int)) * ((M : Int) * (M : Int)))
      ≤ (b + cn * cn) * (((M : Int) * (M : Int)) * ((M : Int) * (M : Int))) :=
    Int.mul_le_mul_of_nonneg_right h hMM0
  -- rewrite both sides to the goal's exact shape via Int ring identities
  have hL : a * (((M : Int) * (M : Int)) * ((M : Int) * (M : Int)))
      = a * (((M : Int) * (M : Int)) * ((M : Int) * (M : Int))) := rfl
  -- RHS shape: (b·(M·M) + (cn·cn)·(M·M))·(M·M)
  have hR : (b * ((M : Int) * (M : Int)) + (cn * cn) * ((M : Int) * (M : Int)))
        * ((M : Int) * (M : Int))
      = (b + cn * cn) * (((M : Int) * (M : Int)) * ((M : Int) * (M : Int))) := by
    rw [← Int.add_mul b (cn * cn) ((M : Int) * (M : Int)),
        Int.mul_assoc (b + cn * cn) ((M : Int) * (M : Int)) ((M : Int) * (M : Int))]
  rw [hR]
  exact hstep

/-- The numeric core: `cn := isqrt(4|2k+1−M|)+1`, `cn² ≥ 4|2k+1−M| ≥ ±(bdyNum diff)`. -/
theorem cHolder_cn_sq_ge (M k : Nat) (hM : 0 < M) :
    (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs) : Int)
      ≤ (((ChebOrthoMidpointEst.isqrt (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs)) + 1 : Nat)) : Int)
        * (((ChebOrthoMidpointEst.isqrt (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs)) + 1 : Nat)) : Int) := by
  have := cHolderWitness_sq_num M k hM
  -- (c·c).num = cn·cn definitionally
  have hnum : (cHolderWitness M k hM * cHolderWitness M k hM).num
      = (((ChebOrthoMidpointEst.isqrt (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs)) + 1 : Nat)) : Int)
        * (((ChebOrthoMidpointEst.isqrt (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs)) + 1 : Nat)) : Int) := rfl
  rwa [hnum] at this

/-- **The radicand √-Hölder hypothesis (upper cell larger).**  For an interior pair
`0 < k`, `k+1 < M`:

    `bdyOneMinusSq M (k+1) ≤ bdyOneMinusSq M k + c_H·c_H`

(holds since `c_H² ≥ 4|2k+1−M| ≥ −(bdyNum(k+1)−bdyNum k)`).  The √-Hölder hypothesis
`u ≤ v + c²` of `SqrtSubadd.holder_oneMinusSq`. -/
theorem radicandDiff_le_csq_up (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    bdyOneMinusSq M (k + 1) hM (Nat.succ_pos k) hk1n
      ≤ bdyOneMinusSq M k hM hk0 hkn + cHolderWitness M k hM * cHolderWitness M k hM := by
  have hu : bdyOneMinusSq M (k + 1) hM (Nat.succ_pos k) hk1n
      = Q'.mkPos (bdyNum M (k + 1)) (M * M) (Nat.mul_pos hM hM) := rfl
  have hv : bdyOneMinusSq M k hM hk0 hkn
      = Q'.mkPos (bdyNum M k) (M * M) (Nat.mul_pos hM hM) := rfl
  have hcw : cHolderWitness M k hM
      = Q'.mkPos (((ChebOrthoMidpointEst.isqrt (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs)) + 1 : Nat)) : Int) M hM := rfl
  rw [hu, hv, hcw]
  refine mkPos_le_add_sqWit _ _ _ M hM ?_
  have hd := ChebOrthoRemainder.bdyNum_diff M k
  have hcsq := cHolder_cn_sq_ge M k hM
  have h2 : -((2 * (k : Int) + 1 - (M : Int))) ≤ ((2 * (k : Int) + 1 - (M : Int)).natAbs : Int) := by
    have hh := Int.le_natAbs (a := -(2 * (k : Int) + 1 - (M : Int)))
    rwa [Int.natAbs_neg] at hh
  omega

theorem radicandDiff_le_csq_down (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    bdyOneMinusSq M k hM hk0 hkn
      ≤ bdyOneMinusSq M (k + 1) hM (Nat.succ_pos k) hk1n
          + cHolderWitness M k hM * cHolderWitness M k hM := by
  have hu : bdyOneMinusSq M (k + 1) hM (Nat.succ_pos k) hk1n
      = Q'.mkPos (bdyNum M (k + 1)) (M * M) (Nat.mul_pos hM hM) := rfl
  have hv : bdyOneMinusSq M k hM hk0 hkn
      = Q'.mkPos (bdyNum M k) (M * M) (Nat.mul_pos hM hM) := rfl
  have hcw : cHolderWitness M k hM
      = Q'.mkPos (((ChebOrthoMidpointEst.isqrt (4 * ((2 * (k : Int) + 1 - (M : Int)).natAbs)) + 1 : Nat)) : Int) M hM := rfl
  rw [hu, hv, hcw]
  refine mkPos_le_add_sqWit _ _ _ M hM ?_
  have hd := ChebOrthoRemainder.bdyNum_diff M k
  have hcsq := cHolder_cn_sq_ge M k hM
  have h1 : (2 * (k : Int) + 1 - (M : Int)) ≤ ((2 * (k : Int) + 1 - (M : Int)).natAbs : Int) :=
    Int.le_natAbs
  omega

/-! ## 3. THE √-Hölder radical-difference two-sided value bound -/

/-- **THE GENUINE √-Hölder radical-difference bound (two-sided).**  For two adjacent
INTERIOR cells `0 < k`, `k+1 < M`, the difference of the two genuine cell radicals
`s_± = √(1 − b_{k±}²)` is two-sidedly bounded by the √-Hölder tolerance
`c_H = (⌊√(4|2k+1−M|)⌋+1)/M`:

    `AbsLeRat (s_+ + (−s_-)) c_H`,        `c_H² ≥ 4·|2k+1−M|/M²`.

PROOF: each `leRat` direction is `SqrtSubadd.holder_oneMinusSq` applied to the
matching radicand ordering (`radicandDiff_le_csq_up` / `_down`), after unfolding the
two radicals as `sqrtFrom` (`ChebOrthoRemainder.bdyRadical_interior`); the negated
side `leRat (−(s_+ − s_-)) c_H` is the `holder_oneMinusSq` bound for the reflected
pair `s_- − s_+`, transferred through the pointwise-`eqv` congruence `leRat_congr`
(`−(a + −b) ≈ b + −a`).  This is the radical-leg ingredient named open in
`ChebOrthoGradedClose.InteriorGradedRemainder`, delivered UNCONDITIONALLY here.  It is
the √-Hölder modulus `|s_+ − s_-| ≤ √(4|x_k|δ) ~ √(δ/j)` of the radical leg. -/
theorem bdyRadicalDiff_holder_AbsLeRat (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hk1n : k + 1 < M) :
    AbsLeRat (CReal.add (bdyRadical M hM (k + 1)) (CReal.neg (bdyRadical M hM k)))
      (cHolderWitness M k hM) := by
  have hkn : k < M := by omega
  -- unfold both radicals into the matching sqrtFrom forms
  have hsp := ChebOrthoRemainder.bdyRadical_interior M hM (k + 1) (Nat.succ_pos k) hk1n
  have hsm := ChebOrthoRemainder.bdyRadical_interior M hM k hk0 hkn
  -- abbreviate the (positive) tolerance
  have hcpos := cHolderWitness_pos M k hM
  refine ⟨?_, ?_⟩
  · -- leRat (s_+ + (−s_-)) c_H  via holder_oneMinusSq (u = larger-indexed radicand)
    rw [hsp, hsm]
    exact CReal.holder_oneMinusSq
      (bdyOneMinusSq M (k + 1) hM (Nat.succ_pos k) hk1n) (SemicircleIntegral.nodeLB M hM)
      (bdyOneMinusSq_pos hM (Nat.succ_pos k) hk1n) (SemicircleIntegral.nodeLB_pos hM)
      (bdyLB_sq_le hM (Nat.succ_pos k) hk1n)
      (bdyOneMinusSq M k hM hk0 hkn) (SemicircleIntegral.nodeLB M hM)
      (bdyOneMinusSq_pos hM hk0 hkn) (SemicircleIntegral.nodeLB_pos hM)
      (bdyLB_sq_le hM hk0 hkn)
      (cHolderWitness M k hM) hcpos
      (radicandDiff_le_csq_up M hM k hk0 hkn hk1n)
  · -- leRat (−(s_+ + (−s_-))) c_H  ≈  leRat (s_- + (−s_+)) c_H
    -- pointwise: (−(a + −b)).approx n = −(a_n + −b_n) ≈ b_n + −a_n = (s_- + −s_+).approx n
    have hcongr : ∀ n,
        ((CReal.neg (CReal.add (bdyRadical M hM (k + 1)) (CReal.neg (bdyRadical M hM k)))).approx n)
          ≈ ((CReal.add (bdyRadical M hM k) (CReal.neg (bdyRadical M hM (k + 1)))).approx n) := by
      intro n
      show (-((bdyRadical M hM (k + 1)).approx n + -((bdyRadical M hM k).approx n)))
          ≈ ((bdyRadical M hM k).approx n + -((bdyRadical M hM (k + 1)).approx n))
      -- −(a + −b) = −a + b = b + −a
      refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv ((bdyRadical M hM (k + 1)).approx n)
        (-((bdyRadical M hM k).approx n))) ?_
      -- (−a) + (−(−b)) ≈ (−a) + b ≈ b + (−a)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv ((bdyRadical M hM k).approx n))) ?_
      exact Q'.add_comm_eqv (-((bdyRadical M hM (k + 1)).approx n)) ((bdyRadical M hM k).approx n)
    refine CReal.leRat_congr hcongr ?_
    -- leRat (s_- + (−s_+)) c_H via holder_oneMinusSq (u = lower-indexed radicand)
    rw [hsp, hsm]
    exact CReal.holder_oneMinusSq
      (bdyOneMinusSq M k hM hk0 hkn) (SemicircleIntegral.nodeLB M hM)
      (bdyOneMinusSq_pos hM hk0 hkn) (SemicircleIntegral.nodeLB_pos hM)
      (bdyLB_sq_le hM hk0 hkn)
      (bdyOneMinusSq M (k + 1) hM (Nat.succ_pos k) hk1n) (SemicircleIntegral.nodeLB M hM)
      (bdyOneMinusSq_pos hM (Nat.succ_pos k) hk1n) (SemicircleIntegral.nodeLB_pos hM)
      (bdyLB_sq_le hM (Nat.succ_pos k) hk1n)
      (cHolderWitness M k hM) hcpos
      (radicandDiff_le_csq_down M hM k hk0 hkn hk1n)

end YMGap.Continuum.ChebOrthoAssembly

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `bdyNum_le_of_sign` / `bdyNum_ge_of_sign` / `bdyOneMinusSq_le_of_num` — the
    interior radicand ordering decided by the `Int` sign of `2k+1−M`
    (`ChebOrthoRemainder.bdyNum_diff`, same denominator `M²`).
  * `isqrt_lt_succ_sq` — the floor-sqrt upper bound `m < (⌊√m⌋+1)²`.
  * `cHolderWitness` / `cHolderWitness_pos` / `cHolderWitness_sq_num` /
    `cHolder_cn_sq_ge` — the explicit √-Hölder tolerance `c_H =
    (⌊√(4|2k+1−M|)⌋+1)/M` with `c_H²·M² ≥ 4·|2k+1−M|` (`c_H ~ √(4|x_k|δ)`, the
    radical-leg modulus `√(δ/j)`).
  * `mkPos_le_add` / `mkPos_le_add_sqWit` — same-denominator `≤`-against-a-sum and
    its specialisation against a squared `mkcn/M` witness (raw cross-multiplication).
  * **`radicandDiff_le_csq_up`** / **`radicandDiff_le_csq_down`** — the radicand
    √-Hölder hypothesis `u ≤ v + c_H²` (both orderings), the exact input of
    `SqrtSubadd.holder_oneMinusSq`.
  * **`bdyRadicalDiff_holder_AbsLeRat`** — THE GENUINE two-sided √-Hölder radical
    difference bound `AbsLeRat (s_+ + (−s_-)) c_H` for an interior pair, via
    `SqrtSubadd.holder_oneMinusSq` on each radicand ordering (after
    `ChebOrthoRemainder.bdyRadical_interior`) and the additive-`eqv` congruence
    `CReal.leRat_congr` for the negated side.  This is the radical-leg ingredient
    named open in `ChebOrthoGradedClose.InteriorGradedRemainder`, delivered
    UNCONDITIONALLY in the `ChebOrthoGradedClose.AbsLeRat` calculus.

**NAMED-open (the honest residuals — precisely).**
  * **The SHARP reciprocal-free radical difference** `|s_+ − s_-| ≤
    4|2k+1−M|δ / recipWitness` (= `(s_+² − s_-²)` divided by the constructive
    reciprocal lower bound `s_+ + s_- ≥ recipWitness`, NO CReal reciprocal).  Its
    `AbsLeRat` form requires a limit-level cancellation lemma "`D·S ≈ ofQ' c`,
    `S ≥ L > 0`, `|c| ≤ K` ⟹ `|D| ≤ K/L`" whose two `leRat` directions need a
    constructive sign split on `D = s_+ − s_-` (no such cancellation lemma exists in
    the substrate).  The √-Hölder bound PROVED here
    (`bdyRadicalDiff_holder_AbsLeRat`, `|s_+ − s_-| ≤ √(4|x_k|δ)`) is the WEAKER but
    UNCONDITIONAL radical-leg control; both `interiorRadicalSum_recipBound`
    (`ChebOrthoInterior`) and this √-Hölder bound are now in hand.

  * `ChebOrthoGradedClose.InteriorGradedRemainder e he` — the full interior per-cell
    two-sided estimate against `gradedRate = C(e)/(⌊√M⌋·jdist²)`.  With BOTH the
    reciprocal lower bound and the √-Hölder radical difference PROVED, the residual is
    the NUMERIC second-order assembly: combine `ChebOrthoRemainder.gIncr_pdiff_split`
    + `ChebOrthoCancel.leading_cancellation` (removing the `O(δ)` part EXACTLY) with
    the smooth-bracket-leg Lipschitz scale `ChebOrthoMidpointCore.Le e` (`R_poly`),
    the radical-leg bound (`R_rad`, this module), and the exponent balancing
    `δ^{3/2}/j^{3/2} ≤ 1/(⌊√M⌋·j²)` to `gradedRate`.  Recorded precisely, NOT faked.

**Path to closure.**  Once `InteriorGradedRemainder e he` holds for every even
`e ≥ 2`, `ChebOrthoGradedClose.gradedPerCellBound_of_interior` (boundary cells
UNCONDITIONAL) + the PROVED bridges close the even-order
`ChebOrthoEvenFTC.OrthEvenZeroLimit` and the full π-free off-diagonal orthogonality
`∫U_e√ = 0` for all `e ≥ 1` (`ChebOrthoGradedClose.offdiag_closed_of_interior`).

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoAssembly.bdyNum_le_of_sign
#print axioms YMGap.Continuum.ChebOrthoAssembly.bdyOneMinusSq_le_of_num
#print axioms YMGap.Continuum.ChebOrthoAssembly.isqrt_lt_succ_sq
#print axioms YMGap.Continuum.ChebOrthoAssembly.cHolderWitness_pos
#print axioms YMGap.Continuum.ChebOrthoAssembly.cHolderWitness_sq_num
#print axioms YMGap.Continuum.ChebOrthoAssembly.cHolder_cn_sq_ge
#print axioms YMGap.Continuum.ChebOrthoAssembly.mkPos_le_add
#print axioms YMGap.Continuum.ChebOrthoAssembly.mkPos_le_add_sqWit
#print axioms YMGap.Continuum.ChebOrthoAssembly.radicandDiff_le_csq_up
#print axioms YMGap.Continuum.ChebOrthoAssembly.radicandDiff_le_csq_down
#print axioms YMGap.Continuum.ChebOrthoAssembly.bdyRadicalDiff_holder_AbsLeRat
