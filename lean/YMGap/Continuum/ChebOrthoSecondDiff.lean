/-
# The LEG SPLIT of the centered midpoint-difference remainder
# `SecondDiffRemainderLeg2`, separating the SMOOTH-BRACKET leg from the RADICAL leg
# of the π-free off-diagonal Chebyshev-`U` orthogonality `∫_{−1}^1 U_e(x)√(1−x²)dx = 0`.

The companion module `ChebOrthoLeadingModel` reduces the interior second-order
remainder to the strictly-smaller residual `SecondDiffRemainderLeg2 e he` — the
CENTERED midpoint-difference remainder

    `splitCReal e he (N+1) k − LZ e he (N+1) k`

against the graded rate `gradedRate e (N+1) k`, where (writing `G(x) = ½·s(x)·B_e(x)`)
`splitCReal` is the boundary increment `G(b_+) − G(b_-)` separated into legs
(`b_± = x_k ± δ`, `δ = 1/(N+1)`) and `LZ ≈ 2δ·G'(x_k)` is the concrete midpoint model.

## What this module supplies (axiom-clean, GENUINE new content)

The product-difference structure of `splitCReal` (`ChebOrthoRemainder.splitCReal`)
exposes the increment as the sum of TWO legs:

  * the SMOOTH-BRACKET leg `½·(s_+ + s_-)·(B_+ − B_-)`   (`legBr`), and
  * the RADICAL leg        `½·(s_+ − s_-)·(B_+ + B_-)`   (`legRad`),

both at the overall `½` of the increment.  And the concrete leading model
`LZ = s_k · MID`, `MID = (1/oms)·½h·(oms·B_e′(x_k) + (−(x_k·B_e(x_k))))`, splits
EXACTLY (a pure rational `(1/oms)·oms ≈ 1` distribution) into

  * the bracket-leg model `LZ_A = s_k · ofQ'(½h·B_e′(x_k))`            (`LZA`), and
  * the radical-leg model `LZ_B = s_k · ofQ'((1/oms)·½h·(−(x_k·B_e(x_k))))` (`LZB`).

This module proves, axiom-clean:

  * **`LZ_split`** — `LZ ≈ LZ_A + LZ_B` (the exact rational reciprocal split of the
    midpoint model, lifted to a `CReal` `Equiv` via `Equiv_of_approx_eqv`).

  * **`split_leg_decomp`** — the EXACT centered-difference LEG DECOMPOSITION

        `splitCReal + (−LZ) ≈ (legBr + (−LZ_A)) + (legRad + (−LZ_B))`,

    a pure per-approximation `Q'`-ring rearrangement (`Equiv_of_approx_eqv`):  the
    overall `½` is distributed over the two split legs, and the model `LZ` is split
    against them leg-by-leg.  This is the genuine SEPARATION of the smooth-bracket
    second-difference from the radical second-difference.

  * **`BrLegRemainder` / `RadLegRemainder`** — the two PRECISE strictly-smaller named
    residuals: the per-leg centered-difference remainder bounds, EACH against HALF the
    graded rate:
      - `AbsLeRat (legBr + (−LZ_A)) (½·gradedRate)`   (smooth-bracket leg), and
      - `AbsLeRat (legRad + (−LZ_B)) (½·gradedRate)`  (radical leg).

  * **`secondDiffLeg2_of_legs`** — THE REDUCTION
    `BrLegRemainder e he ∧ RadLegRemainder e he → SecondDiffRemainderLeg2 e he`,
    pairing the two leg bounds through `AbsLeRat.add` (`½g + ½g = g`),
    `AbsLeRat.of_equiv` along `split_leg_decomp`, and `AbsLeRat.mono`.

This is STRICTLY SMALLER than `SecondDiffRemainderLeg2`: each residual isolates a
SINGLE leg (the smooth-bracket finite difference, OR the radical finite difference),
against HALF the rate, with the algebra linking the two legs to the whole increment
and to the concrete model PROVED.  The smooth-bracket leg carries no radical
singularity (it multiplies the EXACT rational bracket second-difference
`B_+ − B_- − 2δ·B_e′(x_k)`); the radical leg carries the genuine √-Hölder content
(`s_+ + s_- − 2s_k`, `s_+ − s_-`), controlled by `ChebOrthoTaylor.radicalLeg_AbsLeRat`
+ the bracket Lipschitz scale `Le e`.

## What is NAMED-open (precisely — STRICTLY SMALLER than the input)

  * `BrLegRemainder e he` — the SMOOTH-BRACKET leg remainder
    `|½·(s_++s_-)·(B_+−B_-) − s_k·½h·B_e′(x_k)| ≤ ½·gradedRate`.  The radical factors
    are bounded `|s_±| ≤ 1`; the genuine content is the EXACT rational bracket
    second-difference `B_+ − B_- − 2δ·B_e′(x_k)` (scale `Le e·δ²`), no radical
    singularity.
  * `RadLegRemainder e he` — the RADICAL leg remainder
    `|½·(s_+−s_-)·(B_++B_-) − s_k·(1/oms)·½h·(−(x_k·B_e(x_k)))| ≤ ½·gradedRate`.  The
    bracket factors are bounded `|B_±| ≤ 2`; the genuine content is the √-Hölder
    radical second-difference (`s_+ + s_- − 2s_k`, `s_+ − s_-`), controlled by
    `ChebOrthoTaylor.radicalLeg_AbsLeRat` (`|s_+ − s_-| ≤ 4/jdist`) +
    `ChebOrthoInterior.interiorRadicalSum_recipBound`.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on closed
`Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoLeadingModel
import YMGap.Continuum.ChebOrthoRemainder
import YMGap.Continuum.ChebOrthoGraded
import YMGap.Continuum.ChebOrthoGradedClose
import YMGap.Continuum.ChebOrthoCancelDiv

namespace YMGap.Continuum.ChebOrthoSecondDiff

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.ChebOrthoGradedClose
open YMGap.Continuum.ChebOrthoLeadingModel

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≋ " => CReal.Equiv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

instance : Trans (CReal.Equiv) (CReal.Equiv) (CReal.Equiv) where
  trans h1 h2 := CReal.Equiv.trans h1 h2

/-- The half-weight rational `½` (matching `splitCReal`/`leadBlock`). -/
private def half : Q' := Q'.mkPos 1 2 (by decide)

/-! ## 0. The four split data (the two real radicals, the two rational brackets) -/

private def sP (n : Nat) (hn : 0 < n) (k : Nat) : CReal := ChebOrthoMidpoint.bdyRadical n hn (k + 1)
private def sM (n : Nat) (hn : 0 < n) (k : Nat) : CReal := ChebOrthoMidpoint.bdyRadical n hn k
private def bP (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) : Q' :=
  Gbracket e he (ChebOrthoMidpoint.bdyPoint n hn (k + 1))
private def bM (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) : Q' :=
  Gbracket e he (ChebOrthoMidpoint.bdyPoint n hn k)

/-! ## 1. The two legs of `splitCReal` (each carrying the overall `½`) -/

/-- The SMOOTH-BRACKET leg `legBr = ½·(½·(s_+ + s_-)·(B_+ − B_-))` (the overall `½`
of the increment carried outside, the leg's own `½` inside).  No radical singularity:
it multiplies the EXACT rational bracket finite difference `B_+ − B_-`. -/
def legBr (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) : CReal :=
  CReal.mul (CReal.ofQ' half)
    (CReal.mul (CReal.ofQ' half)
      (CReal.mul (CReal.add (sP n hn k) (sM n hn k))
        (CReal.add (CReal.ofQ' (bP e he n hn k)) (CReal.neg (CReal.ofQ' (bM e he n hn k))))))

/-- The RADICAL leg `legRad = ½·(½·(s_+ − s_-)·(B_+ + B_-))` (the √-Hölder leg). -/
def legRad (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) : CReal :=
  CReal.mul (CReal.ofQ' half)
    (CReal.mul (CReal.ofQ' half)
      (CReal.mul (CReal.add (sP n hn k) (CReal.neg (sM n hn k)))
        (CReal.add (CReal.ofQ' (bP e he n hn k)) (CReal.ofQ' (bM e he n hn k)))))

/-- **`splitCReal ≈ legBr + legRad`.**  The overall `½` distributes over the two
sum·difference legs (`mul_add` at each approximation index). -/
theorem split_eq_legs (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) :
    CReal.Equiv (ChebOrthoRemainder.splitCReal e he n hn k)
      (CReal.add (legBr e he n hn k) (legRad e he n hn k)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun p => by
    -- splitCReal.approx p = ½·(LA + LB);  (legBr+legRad).approx p = ½·LA + ½·LB.
    show (half * (half * (((sP n hn k).approx p + (sM n hn k).approx p)
              * (bP e he n hn k + (-(bM e he n hn k))))
          + half * (((sP n hn k).approx p + (-((sM n hn k).approx p)))
              * (bP e he n hn k + bM e he n hn k))))
        ≈ (half * (half * (((sP n hn k).approx p + (sM n hn k).approx p)
                  * (bP e he n hn k + (-(bM e he n hn k)))))
            + half * (half * (((sP n hn k).approx p + (-((sM n hn k).approx p)))
                  * (bP e he n hn k + bM e he n hn k))))
    exact Q'.mul_add_eqv half
      (half * (((sP n hn k).approx p + (sM n hn k).approx p)
        * (bP e he n hn k + (-(bM e he n hn k)))))
      (half * (((sP n hn k).approx p + (-((sM n hn k).approx p)))
        * (bP e he n hn k + bM e he n hn k))))

/-! ## 2. The two leg models splitting the concrete midpoint model `LZ` -/

/-- The bracket-leg model rational coefficient `MIDa = ½h·B_e′(x_k)`. -/
def MIDa (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) : Q' :=
  half * (lebW n hn * ChebOrthoWeightedFTC.Bderiv e he (RiemannSOS.uniformMidpoint n hn k))

/-- The radical-leg model rational coefficient
`MIDb = (1/oms)·½h·(−(x_k·B_e(x_k)))`. -/
def MIDb (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n) : Q' :=
  Q'.recipPos (oneMinusSqNode n k hn hk) (oneMinusSqNode_pos hn hk)
    * (half * (lebW n hn
        * (-(RiemannSOS.uniformMidpoint n hn k * Gbracket e he (RiemannSOS.uniformMidpoint n hn k)))))

/-- The bracket-leg model `LZ_A = s_k · ofQ'(MIDa)`. -/
def LZA (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) : CReal :=
  CReal.mul (nodeWeight n hn k) (CReal.ofQ' (MIDa e he n hn k))

/-- The radical-leg model `LZ_B = s_k · ofQ'(MIDb)`. -/
def LZB (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n) : CReal :=
  CReal.mul (nodeWeight n hn k) (CReal.ofQ' (MIDb e he n hn k hk))

/-- **Abstract reciprocal split.**  For rationals `r, oms, h, Bp, xB` with the
reciprocal identity `oms·r ≈ 1`,

    `r·(½·(h·(oms·Bp + xB))) ≈ ½·(h·Bp) + r·(½·(h·xB))`.

Distribute `(oms·Bp + xB)`, split the product over the `r`-factor; the first summand
`r·(½·(h·(oms·Bp)))` rearranges to `oms·(½·(h·Bp))` and `oms·r ≈ 1` collapses the
reciprocal; the second IS `r·(½·(h·xB))`.  Pure `Q'`-ring `calc`, division-free. -/
theorem reciprocal_split_abstract (r oms h Bp xB : Q') (hr : (oms * r) ≈ (1 : Q')) :
    (r * (half * (h * (oms * Bp + xB))))
      ≈ ((half * (h * Bp)) + r * (half * (h * xB))) := by
  -- distribute (oms·Bp + xB)
  have e1 : (half * (h * (oms * Bp + xB)))
      ≈ (half * (h * (oms * Bp)) + half * (h * xB)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_add_eqv h (oms * Bp) xB)) ?_
    exact Q'.mul_add_eqv half (h * (oms * Bp)) (h * xB)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ e1) ?_
  -- r·(A + B') ≈ r·A + r·B'
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv r (half * (h * (oms * Bp))) (half * (h * xB))) ?_
  refine Q'.add_eqv_congr' ?_ (Q'.eqv_refl _)
  -- r·(half·(h·(oms·Bp))) ≈ half·(h·Bp)
  have e2 : (half * (h * (oms * Bp))) ≈ (oms * (half * (h * Bp))) := by
    calc half * (h * (oms * Bp))
        ≈ half * ((h * oms) * Bp) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv h oms Bp))
      _ ≈ half * ((oms * h) * Bp) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv h oms))
      _ ≈ half * (oms * (h * Bp)) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.mul_assoc_eqv oms h Bp)
      _ ≈ (half * oms) * (h * Bp) := Q'.eqv_symm (Q'.mul_assoc_eqv half oms (h * Bp))
      _ ≈ (oms * half) * (h * Bp) := Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv half oms)
      _ ≈ oms * (half * (h * Bp)) := Q'.mul_assoc_eqv oms half (h * Bp)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ e2) ?_
  calc r * (oms * (half * (h * Bp)))
      ≈ (r * oms) * (half * (h * Bp)) := Q'.eqv_symm (Q'.mul_assoc_eqv r oms (half * (h * Bp)))
    _ ≈ (1 : Q') * (half * (h * Bp)) := by
        refine Q'.mul_eqv_congr_right _ _ _ ?_
        exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv r oms) hr
    _ ≈ (half * (h * Bp)) := Q'.one_mul_eqv _

/-- **`MIDcoeff ≈ MIDa + MIDb`.**  The EXACT rational reciprocal split of the midpoint
leading coefficient, instantiating `reciprocal_split_abstract` at the node data
(`r = 1/oms`, `oms = oneMinusSqNode`, `h = lebW`, `Bp = Bderiv`,
`xB = −(x_k·B_e(x_k))`), with `oms·r ≈ 1` from `mul_recipPos_eqv`. -/
theorem MIDcoeff_split (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n) :
    MIDcoeff e he n hn k hk ≈ (MIDa e he n hn k + MIDb e he n hn k hk) :=
  reciprocal_split_abstract
    (Q'.recipPos (oneMinusSqNode n k hn hk) (oneMinusSqNode_pos hn hk))
    (oneMinusSqNode n k hn hk) (lebW n hn)
    (ChebOrthoWeightedFTC.Bderiv e he (RiemannSOS.uniformMidpoint n hn k))
    (-(RiemannSOS.uniformMidpoint n hn k * Gbracket e he (RiemannSOS.uniformMidpoint n hn k)))
    (Q'.mul_recipPos_eqv (oneMinusSqNode n k hn hk) (oneMinusSqNode_pos hn hk))

/-- **`LZ ≈ LZ_A + LZ_B`.**  Lift `MIDcoeff_split` through `LZ = s_k · ofQ'(MIDcoeff)`:
`s_k·MIDcoeff ≈ s_k·(MIDa + MIDb) = s_k·MIDa + s_k·MIDb`, per approximation index. -/
theorem LZ_split (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n) :
    CReal.Equiv (LZ e he n hn k hk)
      (CReal.add (LZA e he n hn k) (LZB e he n hn k hk)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun p => by
    -- LZ.approx p = s_k_p · MIDcoeff ;  (LZA+LZB).approx p = s_k_p·MIDa + s_k_p·MIDb
    show ((nodeWeight n hn k).approx p * MIDcoeff e he n hn k hk)
        ≈ ((nodeWeight n hn k).approx p * MIDa e he n hn k
            + (nodeWeight n hn k).approx p * MIDb e he n hn k hk)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (MIDcoeff_split e he n hn k hk)) ?_
    exact Q'.mul_add_eqv ((nodeWeight n hn k).approx p)
      (MIDa e he n hn k) (MIDb e he n hn k hk))

/-! ## 3. The EXACT centered-difference LEG DECOMPOSITION -/

/-- A pure-`Q'` regrouping `(P + Q') + ((−A) + (−B')) ≈ (P + (−A)) + (Q' + (−B'))`
(the four-term shuffle pairing each leg with its model). -/
private theorem four_shuffle (P Q A B : Q') :
    ((P + Q) + ((-A) + (-B))) ≈ ((P + (-A)) + (Q + (-B))) := by
  calc (P + Q) + ((-A) + (-B))
      ≈ P + (Q + ((-A) + (-B))) := Q'.add_assoc_eqv P Q ((-A) + (-B))
    _ ≈ P + ((Q + (-A)) + (-B)) :=
        Q'.add_eqv_congr_left P _ _ (Q'.eqv_symm (Q'.add_assoc_eqv Q (-A) (-B)))
    _ ≈ P + (((-A) + Q) + (-B)) :=
        Q'.add_eqv_congr_left P _ _ (Q'.add_eqv_congr_right _ _ (-B) (Q'.add_comm_eqv Q (-A)))
    _ ≈ P + ((-A) + (Q + (-B))) :=
        Q'.add_eqv_congr_left P _ _ (Q'.add_assoc_eqv (-A) Q (-B))
    _ ≈ (P + (-A)) + (Q + (-B)) := Q'.eqv_symm (Q'.add_assoc_eqv P (-A) (Q + (-B)))

/-- **THE LEG DECOMPOSITION.**  The centered midpoint-difference remainder separates
EXACTLY into its smooth-bracket and radical leg remainders:

    `splitCReal + (−LZ) ≈ (legBr + (−LZ_A)) + (legRad + (−LZ_B))`.

PROOF: `splitCReal ≈ legBr + legRad` (`split_eq_legs`), `LZ ≈ LZ_A + LZ_B`
(`LZ_split`), so `splitCReal + (−LZ) ≈ (legBr + legRad) + (−(LZ_A + LZ_B)) ≈
(legBr + legRad) + ((−LZ_A) + (−LZ_B))`, then the four-term shuffle `four_shuffle`
pairs each leg with its model.  All steps via `Equiv_of_approx_eqv` and the
additive `Q'`-eqv calculus. -/
theorem split_leg_decomp (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n) :
    CReal.Equiv
      (CReal.add (ChebOrthoRemainder.splitCReal e he n hn k)
        (CReal.neg (LZ e he n hn k hk)))
      (CReal.add (CReal.add (legBr e he n hn k) (CReal.neg (LZA e he n hn k)))
        (CReal.add (legRad e he n hn k) (CReal.neg (LZB e he n hn k hk)))) := by
  -- step 1: splitCReal + (−LZ) ≈ (legBr + legRad) + (−(LZA + LZB))  via the two Equivs
  have hsplit := split_eq_legs e he n hn k
  have hLZ := LZ_split e he n hn k hk
  -- lift through add (· ) (neg · ) congruence:
  have hstep1 : CReal.Equiv
      (CReal.add (ChebOrthoRemainder.splitCReal e he n hn k) (CReal.neg (LZ e he n hn k hk)))
      (CReal.add (CReal.add (legBr e he n hn k) (legRad e he n hn k))
        (CReal.neg (CReal.add (LZA e he n hn k) (LZB e he n hn k hk)))) :=
    ChebOrthoRemainder.addNeg_Equiv_congr hsplit hLZ
  refine CReal.Equiv.trans hstep1 ?_
  -- step 2: per-approximation four-term shuffle.
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  -- LHS.approx p = (legBr_p + legRad_p) + (−(LZA_p + LZB_p))
  -- RHS.approx p = (legBr_p + (−LZA_p)) + (legRad_p + (−LZB_p))
  show (((legBr e he n hn k).approx p + (legRad e he n hn k).approx p)
        + (-((LZA e he n hn k).approx p + (LZB e he n hn k hk).approx p)))
      ≈ (((legBr e he n hn k).approx p + (-((LZA e he n hn k).approx p)))
          + ((legRad e he n hn k).approx p + (-((LZB e he n hn k hk).approx p))))
  -- −(A + B) ≈ (−A) + (−B), then four_shuffle.
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.neg_add_eqv ((LZA e he n hn k).approx p) ((LZB e he n hn k hk).approx p))) ?_
  exact four_shuffle ((legBr e he n hn k).approx p) ((legRad e he n hn k).approx p)
    ((LZA e he n hn k).approx p) ((LZB e he n hn k hk).approx p)

/-! ## 4. The two PRECISE strictly-smaller named residuals (per leg, HALF rate) -/

/-- **NAMED-open: the SMOOTH-BRACKET leg remainder.**  For even `e ≥ 2`, at every
interior cell, the smooth-bracket leg of the centered midpoint difference minus its
model is bounded by HALF the graded rate:

    `AbsLeRat (legBr + (−LZ_A)) (½·gradedRate)`.

Strictly smaller than `SecondDiffRemainderLeg2`: it isolates the SMOOTH-BRACKET leg
ALONE (no radical singularity — the radical factors `s_±` are bounded `≤ 1`; the
genuine content is the EXACT rational bracket second-difference
`B_+ − B_- − 2δ·B_e′(x_k)`, scale `Le e·δ²`), against HALF the rate. -/
def BrLegRemainder (e : Nat) (he : 0 < e) : Prop :=
  ∀ N k : Nat, 1 ≤ k → k ≤ N - 1 → ∀ hk : k < N + 1,
    AbsLeRat
      (CReal.add (legBr e he (N + 1) (Nat.succ_pos N) k)
        (CReal.neg (LZA e he (N + 1) (Nat.succ_pos N) k)))
      (half * ChebOrthoGraded.gradedRate e (N + 1) (Nat.succ_pos N) k)

/-- **NAMED-open: the RADICAL leg remainder.**  For even `e ≥ 2`, at every interior
cell, the radical leg of the centered midpoint difference minus its model is bounded
by HALF the graded rate:

    `AbsLeRat (legRad + (−LZ_B)) (½·gradedRate)`.

Strictly smaller than `SecondDiffRemainderLeg2`: it isolates the RADICAL leg ALONE
(the bracket factors `B_±` are bounded `≤ 2`; the genuine content is the √-Hölder
radical second-difference `s_+ + s_- − 2s_k` / `s_+ − s_-`, controlled by
`ChebOrthoTaylor.radicalLeg_AbsLeRat` + `ChebOrthoInterior.interiorRadicalSum_recipBound`),
against HALF the rate. -/
def RadLegRemainder (e : Nat) (he : 0 < e) : Prop :=
  ∀ N k : Nat, 1 ≤ k → k ≤ N - 1 → ∀ hk : k < N + 1,
    AbsLeRat
      (CReal.add (legRad e he (N + 1) (Nat.succ_pos N) k)
        (CReal.neg (LZB e he (N + 1) (Nat.succ_pos N) k hk)))
      (half * ChebOrthoGraded.gradedRate e (N + 1) (Nat.succ_pos N) k)

/-! ## 5. THE REDUCTION -/

/-- `½·g + ½·g ≈ g` for any rational `g`. -/
private theorem half_add_half (g : Q') : (half * g + half * g) ≈ g := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv half half g)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (by decide : (half + half) ≈ (1 : Q'))) ?_
  exact Q'.one_mul_eqv g

/-- **THE REDUCTION.**  `BrLegRemainder e he ∧ RadLegRemainder e he →
SecondDiffRemainderLeg2 e he`.  For each interior cell, add the two per-leg bounds
(`AbsLeRat.add`, getting `½g + ½g`), collapse to `g` (`half_add_half`,
`AbsLeRat.mono`), and transfer back to `splitCReal + (−LZ)` along the PROVED EXACT
leg decomposition `split_leg_decomp` (`AbsLeRat.of_equiv`). -/
theorem secondDiffLeg2_of_legs (e : Nat) (he : 0 < e)
    (hBr : BrLegRemainder e he) (hRad : RadLegRemainder e he) :
    ChebOrthoLeadingModel.SecondDiffRemainderLeg2 e he := by
  intro N k hk1 hkN hk
  -- per-leg bounds
  have hB := hBr N k hk1 hkN hk
  have hR := hRad N k hk1 hkN hk
  -- add them: AbsLeRat ((legBr + (−LZA)) + (legRad + (−LZB))) (½g + ½g)
  have hadd := AbsLeRat.add hB hR
  -- collapse ½g + ½g ≤ g  (mono via half_add_half)
  have hg := half_add_half (ChebOrthoGraded.gradedRate e (N + 1) (Nat.succ_pos N) k)
  have hadd' : AbsLeRat
      (CReal.add (CReal.add (legBr e he (N + 1) (Nat.succ_pos N) k)
          (CReal.neg (LZA e he (N + 1) (Nat.succ_pos N) k)))
        (CReal.add (legRad e he (N + 1) (Nat.succ_pos N) k)
          (CReal.neg (LZB e he (N + 1) (Nat.succ_pos N) k hk))))
      (ChebOrthoGraded.gradedRate e (N + 1) (Nat.succ_pos N) k) :=
    AbsLeRat.mono hadd (Q'.le_of_eqv hg)
  -- transfer back along the EXACT leg decomposition
  exact ChebOrthoCancelDiv.AbsLeRat.of_equiv
    (split_leg_decomp e he (N + 1) (Nat.succ_pos N) k hk) hadd'

end YMGap.Continuum.ChebOrthoSecondDiff

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `legBr` / `legRad` — the two legs of `splitCReal` (smooth-bracket / radical).
  * **`split_eq_legs`** — `splitCReal ≈ legBr + legRad` (the overall `½` distributes).
  * `MIDa` / `MIDb` / `LZA` / `LZB` — the bracket-leg and radical-leg models splitting
    the concrete midpoint model `LZ`.
  * **`MIDcoeff_split`** — `MIDcoeff ≈ MIDa + MIDb`, the EXACT rational reciprocal
    split (`(1/oms)·oms ≈ 1`) of the midpoint leading coefficient.
  * **`LZ_split`** — `LZ ≈ LZ_A + LZ_B` (lifting `MIDcoeff_split` through
    `LZ = s_k·ofQ'(MIDcoeff)`).
  * **`split_leg_decomp`** — THE EXACT centered-difference LEG DECOMPOSITION
    `splitCReal + (−LZ) ≈ (legBr + (−LZ_A)) + (legRad + (−LZ_B))`, separating the
    smooth-bracket second-difference from the radical second-difference.
  * `BrLegRemainder` / `RadLegRemainder` — the two PRECISE strictly-smaller named
    residuals: the per-leg centered-difference remainder bounds, EACH against HALF the
    graded rate.
  * **`secondDiffLeg2_of_legs`** — THE REDUCTION
    `BrLegRemainder e he ∧ RadLegRemainder e he → SecondDiffRemainderLeg2 e he`.

**NAMED-open (the honest residual — STRICTLY SMALLER than the input).**
  * `BrLegRemainder e he` — the SMOOTH-BRACKET leg remainder
    `|legBr − LZ_A| ≤ ½·gradedRate`.  No radical singularity (`|s_±| ≤ 1`); the
    genuine content is the EXACT rational bracket second-difference
    `B_+ − B_- − 2δ·B_e′(x_k)` (scale `Le e·δ²`).
  * `RadLegRemainder e he` — the RADICAL leg remainder
    `|legRad − LZ_B| ≤ ½·gradedRate`.  The bracket factors are bounded (`|B_±| ≤ 2`);
    the genuine content is the √-Hölder radical second-difference
    (`s_+ + s_- − 2s_k`, `s_+ − s_-`), controlled by
    `ChebOrthoTaylor.radicalLeg_AbsLeRat` (`|s_+ − s_-| ≤ 4/jdist`) +
    `ChebOrthoInterior.interiorRadicalSum_recipBound`.

  Both are STRICTLY SMALLER than `SecondDiffRemainderLeg2`: each isolates a SINGLE leg
  (smooth-bracket OR radical) against HALF the rate, with the algebra linking the two
  legs to the whole increment (`split_eq_legs`) and to the concrete model
  (`LZ_split`, `split_leg_decomp`) PROVED.

**Path to closure.**  Once `BrLegRemainder e he` and `RadLegRemainder e he` hold for
every even `e ≥ 2`, `secondDiffLeg2_of_legs` → (PROVED)
`ChebOrthoLeadingModel.secondDiff_of_leg2` →
`ChebOrthoTaylor.interiorSecondOrder_of_secondDiff` →
`ChebOrthoFinal.offdiag_closed_of_secondOrder` closes the full π-free off-diagonal
orthogonality `∫U_e√ = 0` for all `e ≥ 1`.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoSecondDiff.split_eq_legs
#print axioms YMGap.Continuum.ChebOrthoSecondDiff.reciprocal_split_abstract
#print axioms YMGap.Continuum.ChebOrthoSecondDiff.MIDcoeff_split
#print axioms YMGap.Continuum.ChebOrthoSecondDiff.LZ_split
#print axioms YMGap.Continuum.ChebOrthoSecondDiff.split_leg_decomp
#print axioms YMGap.Continuum.ChebOrthoSecondDiff.secondDiffLeg2_of_legs
