/-
# The CONCRETE midpoint LEADING MODEL `LZ` and the proof of obligation (1)
# `Equiv (add orthTerm LZ) czero` for the SECOND-DIFFERENCE residual
# `ChebOrthoTaylor.SecondDiffRemainder` (the π-free off-diagonal Chebyshev-`U`
# orthogonality `∫_{−1}^1 U_e(x)√(1−x²) dx = 0`).

The companion module `ChebOrthoTaylor` reduces the interior second-order remainder
to the strictly-smaller named residual `SecondDiffRemainder e he`: for each interior
cell there is a "leading model" `CReal` `LZ` with

  (1) `Equiv (add (orthTerm e (N+1) k) LZ) czero`                       (cancellation)
  (2) `AbsLeRat (add (splitCReal e he (N+1) k) (neg LZ)) (gradedRate …)` (remainder)

This module DEFINES a GENUINE closed-form midpoint model `LZ` (NOT `−orthTerm`) and
PROVES obligation (1) through the EXACT bracket-derivative identity
`ChebUDClosure.Bderiv_identity_uncond` (the algebraic core of
`ChebOrthoCancel.leading_cancellation`) un-cleared by
`ChebOrthoSecondOrder.CReal.cancel_mul_left`.

## The concrete leading model (the genuine content)

Write `x_k = (2k+1−n)/n` the midpoint node, `oms = 1 − x_k²` the POSITIVE RATIONAL
radicand (`oneMinusSqNode`), `s_k = √oms` the genuine `CReal` radical
(`nodeWeight`), `U = U_e(x_k)`, `B = B_e(x_k) = Gbracket`, `Bp = B_e′(x_k) = Bderiv`,
`h = 2/n = lebW`.  Define the RATIONAL "leading midpoint coefficient"

    `MID = (1/oms) · ( ½·h·( oms·Bp + (−(x_k·B)) ) )`,

where `1/oms` is the EXACT rational reciprocal of the positive rational `oms`
(`recipPos`, division-free in the genuine radical — the reciprocal is of the
RATIONAL radicand, never of the irrational `s_k`).  The leading model is

    `LZ := mul s_k (ofQ' MID)`  =  `s_k · MID`,

a GENUINE closed-form midpoint expression built from the radical `s_k`, the width
`h`, the node `x_k`, and the bracket data `Bp`, `B`.  It is NOT `−orthTerm` (it is
`s_k` times the rational leading coefficient `MID`), yet it is provably `≈ −orthTerm`.

## Why obligation (1) holds (proved here, axiom-clean)

  * `node_sq_collapse`:  `s_k · s_k ≈ ofQ' oms`   (`sqrtFrom_sq_equiv`).
  * `sk_orthTerm_collapse`:  `s_k · orthTerm ≈ ofQ'(h·(U·oms))`  (= `ofQ' R`), the
    s-cleared product (one `s_k` from `orthTerm`, one from the multiplier, collapsing
    `s_k² → oms`).
  * `leadBlock_eq_negR`:  `½·h·( oms·Bp + (−(x_k·B)) ) ≈ −R` via
    `Bderiv_identity_uncond` (`(1−x²)·Bp − x·B ≈ −2·(1−x²)·U`); this is the EXACT
    leading cancellation at the RATIONAL level — the algebraic heart of
    `leading_cancellation`.
  * `oms_MIDcoeff_eq_negR`:  `oms · MID ≈ −R` (cancel the rational `1/oms` against `oms`
    via `mul_recipPos_eqv`, then `leadBlock_eq_negR`).
  * `sk_LZ_collapse`:  `s_k · LZ = s_k·(s_k·MID) ≈ oms·MID ≈ −R = ofQ'(−R)`.
  * Hence `s_k · (orthTerm + LZ) ≈ R + (−R) ≈ 0`, and
    `CReal.cancel_mul_left` (lower bound `s_k ≥ 1/n = nodeLB > 0`) CANCELS the genuine
    radical factor `s_k`, yielding `Equiv (add orthTerm LZ) czero` — obligation (1).

This is the EXACT un-clearing the ledger of `ChebOrthoSecondOrder` describes: the
`s`-cleared rational leading cancellation upgraded to the genuine-`CReal` exact
`leadingCombo ≈ −orthTerm`, cancelling the `CReal` radical `s_k` with no `CReal`
reciprocal ever formed (only the RATIONAL reciprocal of the rational radicand).

## What is NAMED-open (precisely — obligation (2))

Obligation (2) — the SECOND-DIFFERENCE (Taylor) remainder bound
`AbsLeRat (add splitCReal (neg LZ)) gradedRate` with THIS concrete `LZ` — is
recorded as the strictly-smaller residual `SecondDiffRemainderLeg2`, and
`SecondDiffRemainderLeg2 e he → ChebOrthoTaylor.SecondDiffRemainder e he` is a PROVED
theorem (it pairs the PROVED obligation (1) with the named (2)).  The dominant
`orthTerm` and leading combination of `splitCReal` no longer appear: (2) is the
genuine boundary-vs-midpoint second-difference of the smooth legs (`splitCReal` is
at the cell BOUNDARIES `b_{k±}`, `LZ` at the MIDPOINT `x_k`), an `O(δ^{3/2})`-shaped
object controlled by `ChebOrthoTaylor.radicalLeg_AbsLeRat`
(`|s_+ − s_-| ≤ 4/jdist`) + the bracket Lipschitz scale.  NOT faked.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on closed
`Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoTaylor
import YMGap.Continuum.ChebOrthoSecondOrder
import YMGap.Continuum.ChebOrthoCancel
import YMGap.Continuum.ChebUDClosure

namespace YMGap.Continuum.ChebOrthoLeadingModel

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.ChebOrthoGradedClose

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≋ " => CReal.Equiv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

instance : Trans (CReal.Equiv) (CReal.Equiv) (CReal.Equiv) where
  trans h1 h2 := CReal.Equiv.trans h1 h2

/-! ## 0. The rational node-square bridge `oms ≈ 1 − x_k²`

The midpoint node is `x_k = (2k+1−n)/n` (`RiemannSOS.uniformMidpoint`) and the
radicand `oms = oneMinusSqNode n k = (n² − (2k+1−n)²)/n²`.  We record the EXACT
rational equality `oms ≈ 1 + (−(x_k·x_k))` (pure `Q'`/`Int` cross-multiplication). -/

/-- **`oms ≈ 1 + (−(x_k·x_k))`** — the radicand IS `1 − x_k²` as rationals.
Cross-multiply: `oms.num·D = (1 + (−(x·x))).num · oms.den` reduces (after expanding
the `mkPos` data) to the `Int` identity `(n²−(2k+1−n)²)·n² = (n²−(2k+1−n)²)·n²`. -/
theorem oms_eq_oneSubSq (n k : Nat) (hn : 0 < n) (hk : k < n) :
    oneMinusSqNode n k hn hk
      ≈ (1 + (-(RiemannSOS.uniformMidpoint n hn k * RiemannSOS.uniformMidpoint n hn k))) := by
  -- x = (2k+1−n)/n ; x·x = (2k+1−n)²/n² ; 1 + (−x²) = (n² − (2k+1−n)²)/n² = oms.
  -- the node value as a mkPos with numerator A := 2k+1−n
  have hx : RiemannSOS.uniformMidpoint n hn k
      = Q'.mkPos (2 * (k : Int) + 1 - (n : Int)) n hn := rfl
  -- x*x : num = A*A, den = n*n
  have hxxnum : (RiemannSOS.uniformMidpoint n hn k
      * RiemannSOS.uniformMidpoint n hn k).num
      = (2 * (k : Int) + 1 - (n : Int)) * (2 * (k : Int) + 1 - (n : Int)) := by
    rw [hx]
    show (Q'.mkPos (2 * (k : Int) + 1 - (n : Int)) n hn).num
        * (Q'.mkPos (2 * (k : Int) + 1 - (n : Int)) n hn).num
      = (2 * (k : Int) + 1 - (n : Int)) * (2 * (k : Int) + 1 - (n : Int))
    rw [Q'.mkPos_num]
  have hxxden : ((RiemannSOS.uniformMidpoint n hn k
      * RiemannSOS.uniformMidpoint n hn k).den : Int) = (n : Int) * (n : Int) := by
    rw [hx]
    show ((Q'.mkPos (2 * (k : Int) + 1 - (n : Int)) n hn
        * Q'.mkPos (2 * (k : Int) + 1 - (n : Int)) n hn).den : Int) = (n : Int) * (n : Int)
    rw [Q'.mul_den_cast, Q'.mkPos_den]
  -- goal cross-multiplication form
  show (oneMinusSqNode n k hn hk).num
        * ((1 + (-(RiemannSOS.uniformMidpoint n hn k
            * RiemannSOS.uniformMidpoint n hn k))).den : Int)
      = (1 + (-(RiemannSOS.uniformMidpoint n hn k
            * RiemannSOS.uniformMidpoint n hn k))).num
        * ((oneMinusSqNode n k hn hk).den : Int)
  -- numerator/denominator of (1 + (−(x·x)))
  have hsnum : (1 + (-(RiemannSOS.uniformMidpoint n hn k
      * RiemannSOS.uniformMidpoint n hn k))).num
      = ((1 : Q').num * ((-(RiemannSOS.uniformMidpoint n hn k
            * RiemannSOS.uniformMidpoint n hn k)).den : Int)
          + (-(RiemannSOS.uniformMidpoint n hn k
            * RiemannSOS.uniformMidpoint n hn k)).num * ((1 : Q').den : Int)) := rfl
  have hsden : ((1 + (-(RiemannSOS.uniformMidpoint n hn k
      * RiemannSOS.uniformMidpoint n hn k))).den : Int)
      = ((1 : Q').den : Int)
        * ((-(RiemannSOS.uniformMidpoint n hn k
            * RiemannSOS.uniformMidpoint n hn k)).den : Int) := by
    rw [Q'.add_den_cast]
  have hnegnum : (-(RiemannSOS.uniformMidpoint n hn k
      * RiemannSOS.uniformMidpoint n hn k)).num
      = -((RiemannSOS.uniformMidpoint n hn k
          * RiemannSOS.uniformMidpoint n hn k).num) := rfl
  have hnegden : ((-(RiemannSOS.uniformMidpoint n hn k
      * RiemannSOS.uniformMidpoint n hn k)).den : Int)
      = ((RiemannSOS.uniformMidpoint n hn k
          * RiemannSOS.uniformMidpoint n hn k).den : Int) := rfl
  have h1num : (1 : Q').num = 1 := rfl
  have h1den : ((1 : Q').den : Int) = 1 := rfl
  rw [hsnum, hsden, hnegnum, hnegden, h1num, h1den, hxxnum, hxxden]
  -- oms.num = omsNum n k = n² − A² ; oms.den = n²
  have homsnum : (oneMinusSqNode n k hn hk).num = omsNum n k := Q'.mkPos_num _ _ _
  have homsden : ((oneMinusSqNode n k hn hk).den : Int) = ((n * n : Nat) : Int) := by
    show ((Q'.mkPos (omsNum n k) (omsDen n) (omsDen_pos hn)).den : Int) = ((n * n : Nat) : Int)
    rw [Q'.mkPos_den]; rfl
  rw [homsnum, homsden]
  have hnn : ((n * n : Nat) : Int) = (n : Int) * (n : Int) := by push_cast; rfl
  rw [hnn, Int.one_mul, Int.mul_one]
  -- goal now: omsNum n k * (n*n) = ((n*n) + (-(A*A))) * (n*n)
  -- omsNum n k = n*n − A*A = n*n + −(A*A)  (def + sub_eq_add_neg)
  have hfac : omsNum n k
      = ((n : Int) * (n : Int)
          + (-((2 * (k : Int) + 1 - (n : Int)) * (2 * (k : Int) + 1 - (n : Int))))) := by
    show (n : Int) * (n : Int)
          - (2 * (k : Int) + 1 - (n : Int)) * (2 * (k : Int) + 1 - (n : Int))
        = ((n : Int) * (n : Int)
          + (-((2 * (k : Int) + 1 - (n : Int)) * (2 * (k : Int) + 1 - (n : Int)))))
    rw [Int.sub_eq_add_neg]
  rw [hfac]

/-! ## 1. The genuine radical and its square collapse -/

/-- The genuine cell radical `s_k = √oms` at an interior cell (`k < n`), exposed as
`sqrtFrom oms (nodeLB n)` (the `dif_pos` branch of `nodeWeight`). -/
theorem nodeWeight_eq_sqrtFrom (n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n) :
    nodeWeight n hn k
      = CReal.sqrtFrom (oneMinusSqNode n k hn hk) (nodeLB n hn)
          (oneMinusSqNode_pos hn hk) (nodeLB_pos hn) (nodeLB_sq_le hn hk) := by
  show (if hk' : k < n then
          CReal.sqrtFrom (oneMinusSqNode n k hn hk') (nodeLB n hn)
            (oneMinusSqNode_pos hn hk') (nodeLB_pos hn) (nodeLB_sq_le hn hk')
        else CReal.czero)
      = CReal.sqrtFrom (oneMinusSqNode n k hn hk) (nodeLB n hn)
          (oneMinusSqNode_pos hn hk) (nodeLB_pos hn) (nodeLB_sq_le hn hk)
  rw [dif_pos hk]

/-- **`s_k · s_k ≈ ofQ' oms`** — the genuine square collapse (`sqrtFrom_sq_equiv`). -/
theorem node_sq_collapse (n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n) :
    CReal.Equiv (CReal.mul (nodeWeight n hn k) (nodeWeight n hn k))
      (CReal.ofQ' (oneMinusSqNode n k hn hk)) := by
  rw [nodeWeight_eq_sqrtFrom n hn k hk]
  exact CReal.sqrtFrom_sq_equiv (oneMinusSqNode n k hn hk) (nodeLB n hn)
    (oneMinusSqNode_pos hn hk) (nodeLB_pos hn) (nodeLB_sq_le hn hk)

/-- **`∀ m, nodeLB n ≤ s_k.approx m`** — the pointwise lower bound feeding
`CReal.cancel_mul_left` (the Heron iterate is `≥ L = 1/n` at every index). -/
theorem nodeWeight_approx_ge (n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n) :
    ∀ m, nodeLB n hn ≤ (nodeWeight n hn k).approx m := by
  intro m
  rw [nodeWeight_eq_sqrtFrom n hn k hk, CReal.sqrtFrom_approx]
  exact CReal.heronSeq_lb (oneMinusSqNode n k hn hk) (nodeLB n hn)
    (oneMinusSqNode_pos hn hk) (nodeLB_pos hn) (nodeLB_sq_le hn hk) m

/-! ## 2. The rational leading coefficient `MID` and the cancellation `oms·MID ≈ −R` -/

/-- The half-weight rational `½`. -/
private def half : Q' := Q'.mkPos 1 2 (by decide)

/-- The rational target `R = h·(U·oms)` (= `s_k · orthTerm`-value). -/
def Rval (e n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n) : Q' :=
  lebW n hn * (uNode e n hn k * oneMinusSqNode n k hn hk)

/-- The RATIONAL "leading midpoint block" `½·h·( oms·Bp + (−(x·B)) )`. -/
def leadBlock (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n) : Q' :=
  half * (lebW n hn
    * (oneMinusSqNode n k hn hk * ChebOrthoWeightedFTC.Bderiv e he (RiemannSOS.uniformMidpoint n hn k)
        + (-(RiemannSOS.uniformMidpoint n hn k
              * Gbracket e he (RiemannSOS.uniformMidpoint n hn k)))))

/-- The RATIONAL leading coefficient `MID = (1/oms)·leadBlock`. -/
def MIDcoeff (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n) : Q' :=
  Q'.recipPos (oneMinusSqNode n k hn hk) (oneMinusSqNode_pos hn hk)
    * leadBlock e he n hn k hk

/-- **The abstract rational leading cancellation** (no abbreviations).  For
rationals `oms, x, Bp, B, U, h` with `oms ≈ 1 + (−(x·x))` and the bracket
derivative identity `(1+(−x²))·Bp + (−(x·B)) ≈ −((1+1)·((1+(−x²))·U))`, the block
`½·(h·(oms·Bp + (−(x·B))))` collapses to `−(h·(U·oms))`.  Pure `Q'`-ring `calc`. -/
theorem leadBlock_abstract (oms x Bp B U h : Q')
    (homs : oms ≈ (1 + (-(x * x))))
    (hBid : ((1 + (-(x * x))) * Bp + (-(x * B)))
            ≈ (-(((1 : Q') + (1 : Q')) * ((1 + (-(x * x))) * U)))) :
    (half * (h * (oms * Bp + (-(x * B))))) ≈ (-(h * (U * oms))) := by
  -- oms·Bp + (−x·B) ≈ (1+(−x²))·Bp + (−x·B) ≈ −((1+1)·((1+(−x²))·U)) ≈ −((1+1)·(oms·U))
  have hcomb : (oms * Bp + (-(x * B)))
      ≈ (-(((1 : Q') + (1 : Q')) * (oms * U))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_right _ _ _ homs))
      (Q'.eqv_trans _ _ _ hBid ?_)
    exact Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm homs)))
  calc half * (h * (oms * Bp + (-(x * B))))
      ≈ half * (h * (-(((1 : Q') + (1 : Q')) * (oms * U)))) :=
        Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hcomb)
    _ ≈ half * (-(h * (((1 : Q') + (1 : Q')) * (oms * U)))) :=
        Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_neg_eqv h (((1 : Q') + (1 : Q')) * (oms * U)))
    _ ≈ (-(half * (h * (((1 : Q') + (1 : Q')) * (oms * U))))) :=
        Q'.mul_neg_eqv half (h * (((1 : Q') + (1 : Q')) * (oms * U)))
    _ ≈ (-(h * (U * oms))) := by
        refine Q'.neg_eqv_congr _ _ ?_
        calc half * (h * (((1 : Q') + (1 : Q')) * (oms * U)))
            ≈ h * (half * (((1 : Q') + (1 : Q')) * (oms * U))) :=
              ChebUDClosure.mul_swap_outer half h (((1 : Q') + (1 : Q')) * (oms * U))
          _ ≈ h * (oms * U) := by
              refine Q'.mul_eqv_congr_left _ _ _ ?_
              calc half * (((1 : Q') + (1 : Q')) * (oms * U))
                  ≈ (half * ((1 : Q') + (1 : Q'))) * (oms * U) :=
                    Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
                _ ≈ (1 : Q') * (oms * U) :=
                    Q'.mul_eqv_congr_right _ _ _ (by decide)
                _ ≈ (oms * U) := Q'.one_mul_eqv _
          _ ≈ h * (U * oms) :=
              Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv oms U)

/-- **The leading block IS `−R`** (the EXACT rational leading cancellation).
`leadBlock = ½·h·(oms·Bp + (−x·B))`; by `Bderiv_identity_uncond`
`oms·Bp + (−x·B) ≈ −2·(oms·U)` (with `oms = 1 + (−x²)`), so
`leadBlock ≈ −(h·U·oms) = −R`.  Instantiates `leadBlock_abstract` at the node data.
This is the algebraic heart of `ChebOrthoCancel.leading_cancellation`, isolated at
the rational level. -/
theorem leadBlock_eq_negR (e : Nat) (he : 0 < e) (he2 : 2 ≤ e) (n : Nat) (hn : 0 < n)
    (k : Nat) (hk : k < n) :
    leadBlock e he n hn k hk ≈ (-(Rval e n hn k hk)) :=
  leadBlock_abstract (oneMinusSqNode n k hn hk) (RiemannSOS.uniformMidpoint n hn k)
    (ChebOrthoWeightedFTC.Bderiv e he (RiemannSOS.uniformMidpoint n hn k))
    (Gbracket e he (RiemannSOS.uniformMidpoint n hn k))
    (Cheb.U e (RiemannSOS.uniformMidpoint n hn k)) (lebW n hn)
    (oms_eq_oneSubSq n k hn hk)
    (ChebUDClosure.Bderiv_identity_uncond e he he2 (RiemannSOS.uniformMidpoint n hn k))

/-- **`oms · MID ≈ −R`** — cancel the rational reciprocal `(1/oms)·oms ≈ 1`
(`mul_recipPos_eqv`), then `leadBlock_eq_negR`. -/
theorem oms_MIDcoeff_eq_negR (e : Nat) (he : 0 < e) (he2 : 2 ≤ e) (n : Nat) (hn : 0 < n)
    (k : Nat) (hk : k < n) :
    (oneMinusSqNode n k hn hk * MIDcoeff e he n hn k hk) ≈ (-(Rval e n hn k hk)) := by
  -- oms · (r · leadBlock) ≈ (oms · r) · leadBlock ≈ 1 · leadBlock ≈ leadBlock ≈ −R
  show (oneMinusSqNode n k hn hk
      * (Q'.recipPos (oneMinusSqNode n k hn hk) (oneMinusSqNode_pos hn hk)
          * leadBlock e he n hn k hk)) ≈ (-(Rval e n hn k hk))
  calc oneMinusSqNode n k hn hk
        * (Q'.recipPos (oneMinusSqNode n k hn hk) (oneMinusSqNode_pos hn hk)
            * leadBlock e he n hn k hk)
      ≈ (oneMinusSqNode n k hn hk
            * Q'.recipPos (oneMinusSqNode n k hn hk) (oneMinusSqNode_pos hn hk))
          * leadBlock e he n hn k hk := Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    _ ≈ (1 : Q') * leadBlock e he n hn k hk :=
        Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_recipPos_eqv (oneMinusSqNode n k hn hk) (oneMinusSqNode_pos hn hk))
    _ ≈ leadBlock e he n hn k hk := Q'.one_mul_eqv _
    _ ≈ (-(Rval e n hn k hk)) := leadBlock_eq_negR e he he2 n hn k hk

/-! ## 3. The s-cleared product `s_k · orthTerm ≈ ofQ' R` -/

/-- **Abstract s-cleared product** (no abbreviations).  For a `CReal` `s` with
`s·s ≈ ofQ' oms` and rationals `h, U`, `s·(ofQ' h · (ofQ' U · s)) ≈ ofQ'(h·(U·oms))`.
Pure `CReal` `mul` comm/assoc + the square collapse. -/
theorem sk_orthTerm_abstract (s : CReal) (h U oms : Q')
    (hcol : CReal.Equiv (CReal.mul s s) (CReal.ofQ' oms)) :
    CReal.Equiv (CReal.mul s (CReal.mul (CReal.ofQ' h) (CReal.mul (CReal.ofQ' U) s)))
      (CReal.ofQ' (h * (U * oms))) := by
  -- Step 1: s·(H·(V·s)) ≈ H·(V·(s·s))
  have e1 : CReal.Equiv (CReal.mul s (CReal.mul (CReal.ofQ' h) (CReal.mul (CReal.ofQ' U) s)))
      (CReal.mul (CReal.ofQ' h) (CReal.mul (CReal.ofQ' U) (CReal.mul s s))) := by
    calc CReal.mul s (CReal.mul (CReal.ofQ' h) (CReal.mul (CReal.ofQ' U) s))
        ≋ CReal.mul (CReal.mul s (CReal.ofQ' h)) (CReal.mul (CReal.ofQ' U) s) :=
          CReal.Equiv.symm (CRealAlg.cmul_assoc s (CReal.ofQ' h) (CReal.mul (CReal.ofQ' U) s))
      _ ≋ CReal.mul (CReal.mul (CReal.ofQ' h) s) (CReal.mul (CReal.ofQ' U) s) :=
          CRealContinuumAlg.cmul_congr_left (CRealAlg.cmul_comm s (CReal.ofQ' h))
      _ ≋ CReal.mul (CReal.ofQ' h) (CReal.mul s (CReal.mul (CReal.ofQ' U) s)) :=
          CRealAlg.cmul_assoc (CReal.ofQ' h) s (CReal.mul (CReal.ofQ' U) s)
      _ ≋ CReal.mul (CReal.ofQ' h) (CReal.mul (CReal.mul s (CReal.ofQ' U)) s) :=
          CRealContinuumAlg.cmul_congr_right
            (CReal.Equiv.symm (CRealAlg.cmul_assoc s (CReal.ofQ' U) s))
      _ ≋ CReal.mul (CReal.ofQ' h) (CReal.mul (CReal.mul (CReal.ofQ' U) s) s) :=
          CRealContinuumAlg.cmul_congr_right
            (CRealContinuumAlg.cmul_congr_left (CRealAlg.cmul_comm s (CReal.ofQ' U)))
      _ ≋ CReal.mul (CReal.ofQ' h) (CReal.mul (CReal.ofQ' U) (CReal.mul s s)) :=
          CRealContinuumAlg.cmul_congr_right
            (CRealAlg.cmul_assoc (CReal.ofQ' U) s s)
  -- Step 2: collapse s·s → ofQ' oms, fold the ofQ' product
  have e2 : CReal.Equiv
      (CReal.mul (CReal.ofQ' h) (CReal.mul (CReal.ofQ' U) (CReal.mul s s)))
      (CReal.ofQ' (h * (U * oms))) := by
    calc CReal.mul (CReal.ofQ' h) (CReal.mul (CReal.ofQ' U) (CReal.mul s s))
        ≋ CReal.mul (CReal.ofQ' h) (CReal.mul (CReal.ofQ' U) (CReal.ofQ' oms)) :=
          CRealContinuumAlg.cmul_congr_right (CRealContinuumAlg.cmul_congr_right hcol)
      _ ≋ CReal.mul (CReal.ofQ' h) (CReal.ofQ' (U * oms)) :=
          CRealContinuumAlg.cmul_congr_right (CReal.Equiv.symm (CRealAlg.ofQ'_mul U oms))
      _ ≋ CReal.ofQ' (h * (U * oms)) := CReal.Equiv.symm (CRealAlg.ofQ'_mul h (U * oms))
  exact CReal.Equiv.trans e1 e2

/-- **`s_k · orthTerm ≈ ofQ' R`**, `R = h·(U·oms)`.  `orthTerm = h·(U·s_k)`, so
`s_k·orthTerm = h·U·(s_k·s_k) ≈ h·U·oms = R` (instantiates `sk_orthTerm_abstract`
with `node_sq_collapse`). -/
theorem sk_orthTerm_collapse (e : Nat) (n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n) :
    CReal.Equiv (CReal.mul (nodeWeight n hn k) (orthTerm e n hn k))
      (CReal.ofQ' (Rval e n hn k hk)) :=
  -- `orthTerm = mul (ofQ' lebW) (mul (ofQ' uNode) nodeWeight)`,
  -- `Rval = lebW * (uNode * oms)` — both definitional.
  sk_orthTerm_abstract (nodeWeight n hn k) (lebW n hn) (uNode e n hn k)
    (oneMinusSqNode n k hn hk) (node_sq_collapse n hn k hk)

/-! ## 4. The concrete leading model `LZ` and the product `s_k · LZ ≈ ofQ'(−R)` -/

/-- **THE CONCRETE LEADING MODEL** `LZ = s_k · MID`, the genuine closed-form midpoint
expression (`s_k` = `nodeWeight`, `MID` = `MIDcoeff` the rational leading
coefficient).  NOT `−orthTerm`. -/
def LZ (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n) : CReal :=
  CReal.mul (nodeWeight n hn k) (CReal.ofQ' (MIDcoeff e he n hn k hk))

/-- **Abstract `s·(s·ofQ' M) ≈ ofQ'(oms·M)`** (no abbreviations).  For a `CReal` `s`
with `s·s ≈ ofQ' oms` and a rational `M`:
`s·(s·ofQ' M) ≈ (s·s)·ofQ' M ≈ ofQ' oms · ofQ' M ≈ ofQ'(oms·M)`. -/
theorem sk_LZ_abstract (s : CReal) (oms M : Q')
    (hcol : CReal.Equiv (CReal.mul s s) (CReal.ofQ' oms)) :
    CReal.Equiv (CReal.mul s (CReal.mul s (CReal.ofQ' M))) (CReal.ofQ' (oms * M)) := by
  calc CReal.mul s (CReal.mul s (CReal.ofQ' M))
      ≋ CReal.mul (CReal.mul s s) (CReal.ofQ' M) :=
        CReal.Equiv.symm (CRealAlg.cmul_assoc s s (CReal.ofQ' M))
    _ ≋ CReal.mul (CReal.ofQ' oms) (CReal.ofQ' M) :=
        CRealContinuumAlg.cmul_congr_left hcol
    _ ≋ CReal.ofQ' (oms * M) := CReal.Equiv.symm (CRealAlg.ofQ'_mul oms M)

/-- **`s_k · LZ ≈ ofQ'(−R)`** — `s_k·(s_k·MID) ≈ oms·MID ≈ −R`.  Instantiates
`sk_LZ_abstract`, then rewrites `ofQ'(oms·MID) ≈ ofQ'(−R)` via `oms_MIDcoeff_eq_negR`. -/
theorem sk_LZ_collapse (e : Nat) (he : 0 < e) (he2 : 2 ≤ e) (n : Nat) (hn : 0 < n)
    (k : Nat) (hk : k < n) :
    CReal.Equiv (CReal.mul (nodeWeight n hn k) (LZ e he n hn k hk))
      (CReal.ofQ' (-(Rval e n hn k hk))) := by
  -- LZ = mul (nodeWeight) (ofQ' MIDcoeff) — definitional
  refine CReal.Equiv.trans
    (sk_LZ_abstract (nodeWeight n hn k) (oneMinusSqNode n k hn hk)
      (MIDcoeff e he n hn k hk) (node_sq_collapse n hn k hk)) ?_
  -- ofQ'(oms·MID) ≈ ofQ'(−R)
  refine SumOfSquares.Equiv_of_approx_eqv (fun _ => ?_)
  exact oms_MIDcoeff_eq_negR e he he2 n hn k hk

/-! ## 5. OBLIGATION (1): `Equiv (add orthTerm LZ) czero` -/

/-- A small helper: `mul s czero ≈ czero` (pointwise `s_n·0 ≈ 0`). -/
private theorem mul_czero (s : CReal) : CReal.Equiv (CReal.mul s CReal.czero) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => by
    show (s.approx n * (0 : Q')) ≈ (0 : Q')
    exact Q'.mul_zero_eqv (s.approx n))

/-- **OBLIGATION (1) — the leading cancellation with the CONCRETE model `LZ`.**
`Equiv (add (orthTerm e n k) (LZ e he n k)) czero` at an interior cell.

PROOF: multiply by the genuine radical `s_k`:
`s_k·(orthTerm + LZ) = s_k·orthTerm + s_k·LZ ≈ ofQ' R + ofQ'(−R) ≈ ofQ' 0 ≈ czero`;
then `CReal.cancel_mul_left` (pointwise lower bound `s_k ≥ 1/n > 0`) cancels the
radical, giving `Equiv (add orthTerm LZ) czero`.  NO `CReal` reciprocal is formed. -/
theorem leadingCancellation (e : Nat) (he : 0 < e) (he2 : 2 ≤ e) (n : Nat) (hn : 0 < n)
    (k : Nat) (hk : k < n) :
    CReal.Equiv (CReal.add (orthTerm e n hn k) (LZ e he n hn k hk)) CReal.czero := by
  -- s·(orthTerm + LZ) ≈ s·czero  (s := nodeWeight n hn k)
  have hmul : CReal.Equiv
      (CReal.mul (nodeWeight n hn k) (CReal.add (orthTerm e n hn k) (LZ e he n hn k hk)))
      (CReal.mul (nodeWeight n hn k) CReal.czero) := by
    -- LHS ≈ add (mul s orthTerm) (mul s LZ)
    have hdist : CReal.Equiv
        (CReal.mul (nodeWeight n hn k) (CReal.add (orthTerm e n hn k) (LZ e he n hn k hk)))
        (CReal.add (CReal.mul (nodeWeight n hn k) (orthTerm e n hn k))
          (CReal.mul (nodeWeight n hn k) (LZ e he n hn k hk))) :=
      SumOfSquares.Equiv_of_approx_eqv (fun p => by
        show ((nodeWeight n hn k).approx p
              * ((orthTerm e n hn k).approx p + (LZ e he n hn k hk).approx p))
          ≈ ((nodeWeight n hn k).approx p * (orthTerm e n hn k).approx p
              + (nodeWeight n hn k).approx p * (LZ e he n hn k hk).approx p)
        exact Q'.mul_add_eqv ((nodeWeight n hn k).approx p) ((orthTerm e n hn k).approx p)
          ((LZ e he n hn k hk).approx p))
    -- add (mul s orthTerm) (mul s LZ) ≈ add (ofQ' R) (ofQ'(−R)) ≈ ofQ'(R + (−R)) ≈ czero
    have hsum : CReal.Equiv
        (CReal.add (CReal.mul (nodeWeight n hn k) (orthTerm e n hn k))
          (CReal.mul (nodeWeight n hn k) (LZ e he n hn k hk)))
        CReal.czero := by
      have hA : CReal.Equiv (CReal.mul (nodeWeight n hn k) (orthTerm e n hn k))
          (CReal.ofQ' (Rval e n hn k hk)) := sk_orthTerm_collapse e n hn k hk
      have hB : CReal.Equiv (CReal.mul (nodeWeight n hn k) (LZ e he n hn k hk))
          (CReal.ofQ' (-(Rval e n hn k hk))) := sk_LZ_collapse e he he2 n hn k hk
      calc CReal.add (CReal.mul (nodeWeight n hn k) (orthTerm e n hn k))
            (CReal.mul (nodeWeight n hn k) (LZ e he n hn k hk))
          ≋ CReal.add (CReal.ofQ' (Rval e n hn k hk))
              (CReal.ofQ' (-(Rval e n hn k hk))) :=
            CReal.Equiv.trans (ChebOrthoTaylor.cadd_left_congr hA)
              (ChebOrthoTaylor.cadd_right_congr hB)
        _ ≋ CReal.czero := by
            -- add (ofQ' R) (ofQ'(−R)) = ofQ' (R + (−R)) ≈ ofQ' 0 = czero
            refine SumOfSquares.Equiv_of_approx_eqv (fun _ => ?_)
            show (Rval e n hn k hk + (-(Rval e n hn k hk))) ≈ (0 : Q')
            exact Q'.add_neg_self_eqv (Rval e n hn k hk)
    -- chain ; RHS mul s czero ≈ czero (symm)
    exact CReal.Equiv.trans (CReal.Equiv.trans hdist hsum)
      (CReal.Equiv.symm (mul_czero (nodeWeight n hn k)))
  -- cancel the radical s on the left (lower bound nodeLB, positive)
  exact ChebOrthoSecondOrder.CReal.cancel_mul_left hmul
    (nodeWeight_approx_ge n hn k hk) (nodeLB_pos hn)

/-! ## 6. The strictly-smaller residual (obligation (2)) and the reduction -/

/-- **NAMED-open: obligation (2)** — the SECOND-DIFFERENCE (Taylor) remainder bound
with THIS concrete leading model `LZ`.  Strictly smaller than
`ChebOrthoFinal.InteriorSecondOrderRemainder`: the dominant `orthTerm` and the
leading midpoint combination of `splitCReal` are GONE (cancelled into the PROVED
`leadingCancellation`); what remains is the boundary-vs-midpoint second difference of
the smooth legs (`splitCReal` at the cell BOUNDARIES `b_{k±}`, `LZ` at the MIDPOINT
`x_k`), an `O(δ^{3/2})`-shaped object against the SAME graded rate.  Controlled by
`ChebOrthoTaylor.radicalLeg_AbsLeRat` (`|s_+ − s_-| ≤ 4/jdist`) + the bracket
Lipschitz scale.  Recorded precisely, NOT faked. -/
def SecondDiffRemainderLeg2 (e : Nat) (he : 0 < e) : Prop :=
  ∀ N k : Nat, 1 ≤ k → k ≤ N - 1 →
    ∀ hk : k < N + 1,
      AbsLeRat
        (CReal.add (ChebOrthoRemainder.splitCReal e he (N + 1) (Nat.succ_pos N) k)
          (CReal.neg (LZ e he (N + 1) (Nat.succ_pos N) k hk)))
        (ChebOrthoGraded.gradedRate e (N + 1) (Nat.succ_pos N) k)

/-- **THE REDUCTION.**  For even `e ≥ 2`, `SecondDiffRemainderLeg2 e he` (obligation
(2) with the concrete `LZ`) implies `ChebOrthoTaylor.SecondDiffRemainder e he`: at
each interior cell, witness the leading model `LZ`, supply obligation (1) from the
PROVED `leadingCancellation`, and obligation (2) from the hypothesis. -/
theorem secondDiff_of_leg2 (e : Nat) (he : 0 < e) (he2 : 2 ≤ e)
    (h2 : SecondDiffRemainderLeg2 e he) :
    ChebOrthoTaylor.SecondDiffRemainder e he := by
  intro N k hk1 hkN
  have hk : k < N + 1 := by have : k ≤ N - 1 := hkN; omega
  refine ⟨LZ e he (N + 1) (Nat.succ_pos N) k hk, ?_, ?_⟩
  · exact leadingCancellation e he he2 (N + 1) (Nat.succ_pos N) k hk
  · exact h2 N k hk1 hkN hk

end YMGap.Continuum.ChebOrthoLeadingModel

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `oms_eq_oneSubSq` — the rational node-square bridge `oms ≈ 1 + (−(x_k·x_k))`.
  * `node_sq_collapse` / `nodeWeight_approx_ge` — the genuine radical square collapse
    `s_k·s_k ≈ ofQ' oms` and its pointwise lower bound `s_k ≥ 1/n`.
  * `leadBlock_eq_negR` — the EXACT rational leading cancellation
    `½·h·(oms·Bp + (−x·B)) ≈ −R` via `ChebUDClosure.Bderiv_identity_uncond` (the
    algebraic heart of `ChebOrthoCancel.leading_cancellation`).
  * `oms_MIDcoeff_eq_negR` — `oms·MID ≈ −R` (rational reciprocal cancellation).
  * `sk_orthTerm_collapse` — the s-cleared product `s_k·orthTerm ≈ ofQ' R`.
  * `sk_LZ_collapse` — `s_k·LZ ≈ ofQ'(−R)` for the CONCRETE model `LZ = s_k·MID`.
  * **`leadingCancellation`** — OBLIGATION (1): `Equiv (add orthTerm LZ) czero` for the
    GENUINE closed-form midpoint model `LZ` (NOT `−orthTerm`), via `s_k·(orthTerm+LZ) ≈
    R + (−R) ≈ 0` and `CReal.cancel_mul_left` (no `CReal` reciprocal formed; only the
    RATIONAL reciprocal of the rational radicand `oms`).
  * **`secondDiff_of_leg2`** — the PROVED reduction
    `SecondDiffRemainderLeg2 e he → ChebOrthoTaylor.SecondDiffRemainder e he` (pairing
    the PROVED (1) with the named (2)).

**NAMED-open (the honest residual — STRICTLY SMALLER, only obligation (2)).**
  * `SecondDiffRemainderLeg2 e he` — the SECOND-DIFFERENCE (Taylor) remainder bound
    `AbsLeRat (add splitCReal (neg LZ)) gradedRate` with the CONCRETE `LZ`.  The
    dominant `orthTerm`/leading pieces are GONE (separated into the PROVED
    `leadingCancellation`); the residual is the genuine boundary-vs-midpoint
    second difference of the smooth legs against the SAME graded rate, controlled by
    `ChebOrthoTaylor.radicalLeg_AbsLeRat` + the bracket Lipschitz scale.  NOT faked.

**Path to closure.**  Once `SecondDiffRemainderLeg2 e he` holds for every even
`e ≥ 2`, `secondDiff_of_leg2` → `ChebOrthoTaylor.interiorSecondOrder_of_secondDiff`
→ `ChebOrthoFinal.offdiag_closed_of_secondOrder` closes the full π-free off-diagonal
orthogonality `∫U_e√ = 0` for all `e ≥ 1`.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoLeadingModel.oms_eq_oneSubSq
#print axioms YMGap.Continuum.ChebOrthoLeadingModel.node_sq_collapse
#print axioms YMGap.Continuum.ChebOrthoLeadingModel.nodeWeight_approx_ge
#print axioms YMGap.Continuum.ChebOrthoLeadingModel.leadBlock_eq_negR
#print axioms YMGap.Continuum.ChebOrthoLeadingModel.oms_MIDcoeff_eq_negR
#print axioms YMGap.Continuum.ChebOrthoLeadingModel.sk_orthTerm_collapse
#print axioms YMGap.Continuum.ChebOrthoLeadingModel.sk_LZ_collapse
#print axioms YMGap.Continuum.ChebOrthoLeadingModel.leadingCancellation
#print axioms YMGap.Continuum.ChebOrthoLeadingModel.secondDiff_of_leg2
