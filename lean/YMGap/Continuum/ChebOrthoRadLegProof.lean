/-
# The EVENTUAL radical-leg bound `EventualRadLegRemainder`.

This module discharges the eventual per-cell RADICAL leg residual named in
`ChebOrthoLegAssembly` (the radical leg of the centered midpoint-difference remainder),
against HALF the graded rate, for `M = N+1` beyond an explicit per-order threshold.
It mirrors the SMOOTH-BRACKET leg blueprint (`ChebOrthoLegProof.eventualBrLegRemainder`)
but supplies the genuine √-Hölder content of the radical second differences.

## What is PROVED here (axiom-clean, GENUINE new content)

  * **`symmSecondDiff_sqrt_AbsLeRat`** — the TIGHT √-scale symmetric second-difference
    bound `|s_+ + s_- − 2 s_k| ≤ symmQuot_sqrt`, dividing the numerator
    `K = 2·subSecondQuot_tight + 2δ²` by the genuine √-scale sum lower bound
    `L = 2·omsSqrtLb` (`omsSqrtLb ~ √(jδ)`), giving the `~δ^{1/2}/j^{3/2}` scale.
  * **`antisymmSecondDiff_AbsLeRat`** — the antisymmetric second-difference reduction
    `|Δ₁''| ≤ antisymmQuot` (`Δ₁'' = (s_+ − s_-) − s_k'·h`, `s_k' = −x_k/s_k`,
    `h = lebW = 2δ`), via the exact `CReal.Equiv` clearing `s_k·(s_++s_-)`.
  * **`EventualRadLegRemainder`** — `ChebOrthoLegAssembly.EventualRadLegRemainder e he`.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide`/`ac_rfl` only on
closed/`Nat`-AC goals.  Axiom-gate at the foot.
-/

import YMGap.Continuum.ChebOrthoLegProof
import YMGap.Continuum.ChebOrthoTightModulus

set_option maxHeartbeats 1000000

namespace YMGap.Continuum.ChebOrthoRadLegProof

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoMidpoint
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.ChebOrthoGraded (jdist jdist_pos)
open YMGap.Continuum.ChebOrthoGradedClose (AbsLeRat)
open YMGap.Continuum.ChebOrthoCancelDiv
open YMGap.Continuum.ChebOrthoTightModulus
  (oms_lb oms_lb_pos oms_ge subSecondQuot_tight subSecondQuot_tight_nonneg
   subSecondQuot_tight_le_recip twoDeltaSq twoDeltaSq_nonneg twoDeltaSq_le
   symmD symmS radSum twoNode DS_AbsLeRat_tight jdist_le_M mkPos_add)
open YMGap.Continuum.ChebOrthoMidpointEst (isqrt isqrt_ge isqrt_sq_le isqrt_pos)

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≋ " => CReal.Equiv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

instance : Trans (CReal.Equiv) (CReal.Equiv) (CReal.Equiv) where
  trans h1 h2 := CReal.Equiv.trans h1 h2

/-! ## 0. The genuine √-scale node floor `omsSqrtLb ~ √(jδ)` -/

/-- The genuine √-scale node-radical floor `omsSqrtLb := ⌊√(jdist·M)⌋/(2M) ~ √(jδ)/2`.
Chosen so that `omsSqrtLb² ≤ oms_lb = jdist/(2M) ≤ oms`. -/
def omsSqrtLb (M k : Nat) (hM : 0 < M) : Q' :=
  Q'.mkPos (isqrt (jdist M k * M) : Int) (2 * M) (by omega)

theorem omsSqrtLb_pos (M k : Nat) (hM : 0 < M) (hk : k < M) : (0 : Q') < omsSqrtLb M k hM := by
  show (0 : Int) * ((omsSqrtLb M k hM).den : Int) < (omsSqrtLb M k hM).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  show (0 : Int) < (Q'.mkPos (isqrt (jdist M k * M) : Int) (2 * M) (by omega)).num
  rw [Q'.mkPos_num]
  have hjM : 0 < jdist M k * M := Nat.mul_pos (jdist_pos hk) hM
  have : 0 < isqrt (jdist M k * M) := by
    refine isqrt_ge (m := jdist M k * M) (K := 1) ?_
    have : 1 * 1 = 1 := by decide
    omega
  exact_mod_cast this

theorem omsSqrtLb_nonneg (M k : Nat) (hM : 0 < M) (hk : k < M) :
    (0 : Q') ≤ omsSqrtLb M k hM := Q'.le_of_lt (omsSqrtLb_pos M k hM hk)

/-- **`omsSqrtLb² ≤ oms_lb`.**  `(⌊√(jM)⌋/(2M))² = ⌊√(jM)⌋²/(4M²) ≤ (jM)/(4M²)
= j/(4M) ≤ j/(2M) = oms_lb`.  Pure `Int` cross-multiplication using `isqrt_sq_le`. -/
theorem omsSqrtLb_sq_le_oms_lb (M k : Nat) (hM : 0 < M) (hk : k < M) :
    omsSqrtLb M k hM * omsSqrtLb M k hM ≤ oms_lb M k hM := by
  show (omsSqrtLb M k hM * omsSqrtLb M k hM).num * ((oms_lb M k hM).den : Int)
      ≤ (oms_lb M k hM).num * ((omsSqrtLb M k hM * omsSqrtLb M k hM).den : Int)
  have hSn : (omsSqrtLb M k hM).num = (isqrt (jdist M k * M) : Int) := by
    show (Q'.mkPos (isqrt (jdist M k * M) : Int) (2 * M) (by omega)).num = _; rw [Q'.mkPos_num]
  have hSd : (omsSqrtLb M k hM).den = 2 * M := by
    show (Q'.mkPos (isqrt (jdist M k * M) : Int) (2 * M) (by omega)).den = _; rw [Q'.mkPos_den]
  have hLn : (oms_lb M k hM).num = (jdist M k : Int) := by
    show (Q'.mkPos (jdist M k : Int) (2 * M) (by omega)).num = _; rw [Q'.mkPos_num]
  have hLd : ((oms_lb M k hM).den : Int) = ((2 * M : Nat) : Int) := by
    show ((Q'.mkPos (jdist M k : Int) (2 * M) (by omega)).den : Int) = _; rw [Q'.mkPos_den]
  -- product num/den
  have hPn : (omsSqrtLb M k hM * omsSqrtLb M k hM).num
      = (isqrt (jdist M k * M) : Int) * (isqrt (jdist M k * M) : Int) := by
    show (omsSqrtLb M k hM).num * (omsSqrtLb M k hM).num = _; rw [hSn]
  have hPd : ((omsSqrtLb M k hM * omsSqrtLb M k hM).den : Int)
      = ((2 * M : Nat) : Int) * ((2 * M : Nat) : Int) := by
    rw [Q'.mul_den_cast, hSd]
  rw [hPn, hPd, hLn, hLd]
  -- isqrt(jM)²·(2M) ≤ jdist·((2M)·(2M))
  have h2M : ((2 * M : Nat) : Int) = 2 * (M : Int) := by push_cast; rfl
  rw [h2M]
  -- let s = isqrt(jM), s² ≤ jM
  have hsle : isqrt (jdist M k * M) * isqrt (jdist M k * M) ≤ jdist M k * M :=
    isqrt_sq_le (jdist M k * M)
  have hsleI : (isqrt (jdist M k * M) : Int) * (isqrt (jdist M k * M) : Int)
      ≤ (jdist M k : Int) * (M : Int) := by
    have : ((isqrt (jdist M k * M) * isqrt (jdist M k * M) : Nat) : Int)
        ≤ ((jdist M k * M : Nat) : Int) := by exact_mod_cast hsle
    push_cast at this; exact this
  -- s²·(2M) ≤ (jM)·(2M) ≤ jdist·(2M·2M) = jdist·4M² ; need s²·2M ≤ jdist·(2M·2M)
  have hM0 : (0 : Int) ≤ 2 * (M : Int) := by
    have : (0 : Int) ≤ (M : Int) := Int.natCast_nonneg _; omega
  have hstep : ((isqrt (jdist M k * M) : Int) * (isqrt (jdist M k * M) : Int)) * (2 * (M : Int))
      ≤ ((jdist M k : Int) * (M : Int)) * (2 * (M : Int)) :=
    Int.mul_le_mul_of_nonneg_right hsleI hM0
  refine Int.le_trans hstep ?_
  -- (jM)·(2M) ≤ jdist·(2M·2M)  ⟺  (jM)·(2M) ≤ jdist·4M² ⟺ 2jM² ≤ 4jM²  (true)
  have hge : ((jdist M k : Int) * (M : Int)) * (2 * (M : Int))
      ≤ (jdist M k : Int) * (2 * (M : Int) * (2 * (M : Int))) := by
    -- LHS = jdist·(M·2M) = jdist·2M² ; RHS = jdist·4M²
    have hjnn : (0 : Int) ≤ (jdist M k : Int) := Int.natCast_nonneg _
    have hMnn : (0 : Int) ≤ (M : Int) := Int.natCast_nonneg _
    -- M·2M ≤ 2M·2M
    have hinner : (M : Int) * (2 * (M : Int)) ≤ (2 * (M : Int)) * (2 * (M : Int)) := by
      have : (M : Int) ≤ 2 * (M : Int) := by omega
      exact Int.mul_le_mul_of_nonneg_right this hM0
    -- rearrange LHS to jdist·(M·2M)
    have hL : ((jdist M k : Int) * (M : Int)) * (2 * (M : Int))
        = (jdist M k : Int) * ((M : Int) * (2 * (M : Int))) := by rw [Int.mul_assoc]
    rw [hL]
    exact Int.mul_le_mul_of_nonneg_left hinner hjnn
  exact hge

/-- **`omsSqrtLb² ≤ oneMinusSqNode`** (so `heronSeq_lb` lifts `omsSqrtLb ≤ s_k.approx`). -/
theorem omsSqrtLb_sq_le_oms (M : Nat) (hM : 0 < M) (k : Nat) (hk0 : 0 < k) (hkn : k < M) :
    omsSqrtLb M k hM * omsSqrtLb M k hM ≤ oneMinusSqNode M k hM hkn :=
  Q'.le_trans' _ _ _ (omsSqrtLb_sq_le_oms_lb M k hM hkn) (oms_ge M hM k hk0 hkn)

/-- **`omsSqrtLb ≤ s_k.approx n`** at every Heron index (the genuine node-radical
floor), via `heronSeq_lb` with `omsSqrtLb² ≤ oms`. -/
theorem node_approx_ge_omsSqrtLb (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (n : Nat) :
    omsSqrtLb M k hM ≤ (nodeWeight M hM k).approx n := by
  rw [ChebOrthoLeadingModel.nodeWeight_eq_sqrtFrom M hM k hkn, CReal.sqrtFrom_approx]
  exact CReal.heronSeq_lb (oneMinusSqNode M k hM hkn) (omsSqrtLb M k hM)
    (oneMinusSqNode_pos hM hkn) (omsSqrtLb_pos M k hM hkn)
    (omsSqrtLb_sq_le_oms M hM k hk0 hkn) n

/-! ## 1. The TIGHT √-scale symmetric second-difference bound -/

/-- `2·omsSqrtLb` (the √-scale lower bound on `S = s_+ + s_- + 2 s_k`). -/
def twoOmsSqrtLb (M k : Nat) (hM : 0 < M) : Q' := omsSqrtLb M k hM + omsSqrtLb M k hM

theorem twoOmsSqrtLb_pos (M k : Nat) (hM : 0 < M) (hk : k < M) :
    (0 : Q') < twoOmsSqrtLb M k hM :=
  Q'.add_pos (omsSqrtLb_pos M k hM hk) (omsSqrtLb_pos M k hM hk)

/-- **√-scale pointwise lower bound on `S = s_+ + s_- + 2 s_k`.**  At every Heron index,
`2·omsSqrtLb ≤ S.approx n`, from `s_k ≥ omsSqrtLb` (`node_approx_ge_omsSqrtLb`) twice and
`s_+ + s_- ≥ 0`. -/
theorem symmS_lower_sqrt (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) :
    ∀ n, twoOmsSqrtLb M k hM ≤ (symmS M hM k).approx n := by
  intro n
  show twoOmsSqrtLb M k hM
      ≤ (((bdyRadical M hM (k + 1)).approx n + (bdyRadical M hM k).approx n)
          + ((nodeWeight M hM k).approx n + (nodeWeight M hM k).approx n))
  -- 2 s_k ≥ 2 omsSqrtLb
  have hsk := node_approx_ge_omsSqrtLb M hM k hk0 hkn n
  have h2sk : twoOmsSqrtLb M k hM
      ≤ ((nodeWeight M hM k).approx n + (nodeWeight M hM k).approx n) := by
    show (omsSqrtLb M k hM + omsSqrtLb M k hM) ≤ _
    exact Q'.add_le_add hsk hsk
  -- s_+ + s_- ≥ 0
  have hsp : (0 : Q') ≤ (bdyRadical M hM (k + 1)).approx n :=
    ChebOrthoInterior.bdyRadical_approx_nonneg M hM (k + 1) n
  have hsm : (0 : Q') ≤ (bdyRadical M hM k).approx n :=
    ChebOrthoInterior.bdyRadical_approx_nonneg M hM k n
  have hsum0 : (0 : Q')
      ≤ ((bdyRadical M hM (k + 1)).approx n + (bdyRadical M hM k).approx n) :=
    Q'.zero_le_add _ _ hsp hsm
  -- S = (s_+ + s_-) + 2 s_k ≥ 0 + 2 omsSqrtLb
  refine Q'.le_trans' _ _ _ h2sk ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_zero_add_eqv _))) ?_
  exact Q'.add_le_add hsum0 (Q'.le_refl' _)

/-- The TIGHT √-scale symmetric quotient `symmQuot_sqrt = K·(1/L)`,
`K = 2·subSecondQuot_tight + 2δ²`, `L = 2·omsSqrtLb`. -/
def symmQuot_sqrt (M k : Nat) (hM : 0 < M) (hkn : k < M) : Q' :=
  ((subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn) + twoDeltaSq M hM)
    * Q'.recipPos (twoOmsSqrtLb M k hM) (twoOmsSqrtLb_pos M k hM hkn)

theorem symmQuot_sqrt_nonneg (M k : Nat) (hM : 0 < M) (hkn : k < M) :
    (0 : Q') ≤ symmQuot_sqrt M k hM hkn := by
  refine Q'.mul_nonneg _ _ ?_ (Q'.le_of_lt (Q'.recipPos_pos _ _))
  exact Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (subSecondQuot_tight_nonneg M k hM hkn)
    (subSecondQuot_tight_nonneg M k hM hkn)) (twoDeltaSq_nonneg M hM)

/-- **THE TIGHT √-SCALE SYMMETRIC SECOND-DIFFERENCE BOUND.**  For an interior cell,
`|s_+ + s_- − 2 s_k| ≤ symmQuot_sqrt`, with the genuine `~δ^{1/2}/j^{3/2}` scale
(numerator `~1/(M·jdist)`, outer reciprocal `1/(2·omsSqrtLb) ~ 1/(2√(jδ)) ~ √M/(2√j)`).
Reciprocal-free, via `AbsLeRat.div_of_mul_ge` with the TIGHT numerator bound
`DS_AbsLeRat_tight` and the √-scale sum lower bound `symmS_lower_sqrt`. -/
theorem symmSecondDiff_sqrt_AbsLeRat (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    AbsLeRat (symmD M hM k) (symmQuot_sqrt M k hM hkn) := by
  refine ChebOrthoCancelDiv.AbsLeRat.div_of_mul_ge
    (D := symmD M hM k) (S := symmS M hM k)
    (K := (subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn) + twoDeltaSq M hM)
    (L := twoOmsSqrtLb M k hM)
    (KL := symmQuot_sqrt M k hM hkn)
    (DS_AbsLeRat_tight M hM k hk0 hkn hk1n)
    (symmS_lower_sqrt M hM k hk0 hkn)
    (twoOmsSqrtLb_pos M k hM hkn)
    (symmQuot_sqrt_nonneg M k hM hkn)
    ?_
  -- KL·L ≈ K
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv
      ((subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn) + twoDeltaSq M hM)
      (Q'.recipPos (twoOmsSqrtLb M k hM) (twoOmsSqrtLb_pos M k hM hkn))
      (twoOmsSqrtLb M k hM)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
        (Q'.mul_recipPos_eqv (twoOmsSqrtLb M k hM) (twoOmsSqrtLb_pos M k hM hkn)))) ?_
  exact Q'.mul_one_eqv _

/-! ## 2. The antisymmetric second-difference reduction

We bound the genuine √-Hölder antisymmetric content
`T1 := ½·B0·(s_+ − s_-) − LZB`  (this is `½·B0·Δ₁''`, `Δ₁'' = (s_+ − s_-) − s_k'·h`,
`s_k' = −x_k/s_k`), WITHOUT ever forming `1/s_k`.  The reduction is the EXACT `CReal`
identity `(s_k·(s_+ + s_-))·T1 ≋ ofQ'(δ·x_k·B0)·Δ₂`, which we then divide by the genuine
lower bound `s_k·(s_+ + s_-) ≥ 2·omsSqrtLb²` (`div_of_mul_ge`). -/

/-- The midpoint `x_k`. -/
def xk (M : Nat) (hM : 0 < M) (k : Nat) : Q' := RiemannSOS.uniformMidpoint M hM k

/-- `B0 = B_e(x_k)`. -/
def B0 (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) : Q' :=
  ChebOrthoOffDiag.Gbracket e he (xk M hM k)

/-- `s_+`. -/
def sP (M : Nat) (hM : 0 < M) (k : Nat) : CReal := bdyRadical M hM (k + 1)
/-- `s_-`. -/
def sM (M : Nat) (hM : 0 < M) (k : Nat) : CReal := bdyRadical M hM k
/-- `s_k`. -/
def sK (M : Nat) (hM : 0 < M) (k : Nat) : CReal := nodeWeight M hM k

/-- `s_+ − s_-`. -/
def radDiff (M : Nat) (hM : 0 < M) (k : Nat) : CReal := CReal.add (sP M hM k) (CReal.neg (sM M hM k))

/-- The antisymmetric target `T1 = ½·B0·(s_+ − s_-) − LZB`. -/
def antisymmTarget (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) (hk : k < M) : CReal :=
  CReal.add
    (CReal.mul (CReal.ofQ' (ChebOrthoLegProof.half * B0 e he M hM k)) (radDiff M hM k))
    (CReal.neg (ChebOrthoSecondDiff.LZB e he M hM k hk))

/-- The divisor `S = s_k·(s_+ + s_-)`. -/
def antisymmS (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.mul (sK M hM k) (radSum M hM k)

/-- **`oms · MIDb ≈ ½·h·(−(x_k·B0))`.**  `MIDb = (1/oms)·(½h(−x_kB0))`, so the
reciprocal collapses (`oms·(1/oms) ≈ 1`).  Pure `Q'`-ring. -/
theorem oms_mul_MIDb (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) (hk : k < M) :
    (oneMinusSqNode M k hM hk * ChebOrthoSecondDiff.MIDb e he M hM k hk)
      ≈ (ChebOrthoLegProof.half
          * (lebW M hM * (-(xk M hM k * B0 e he M hM k)))) := by
  -- MIDb = recipPos(oms) · W,  W = ½·(h·(−(x_k·B0)))
  show (oneMinusSqNode M k hM hk
        * (Q'.recipPos (oneMinusSqNode M k hM hk) (oneMinusSqNode_pos hM hk)
            * (ChebOrthoLegProof.half * (lebW M hM
                * (-(RiemannSOS.uniformMidpoint M hM k
                    * ChebOrthoOffDiag.Gbracket e he (RiemannSOS.uniformMidpoint M hM k)))))))
      ≈ (ChebOrthoLegProof.half * (lebW M hM
          * (-(xk M hM k * B0 e he M hM k))))
  -- oms·(recip · W) ≈ (oms·recip)·W ≈ 1·W ≈ W
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (oneMinusSqNode M k hM hk)
      (Q'.recipPos (oneMinusSqNode M k hM hk) (oneMinusSqNode_pos hM hk)) _)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_recipPos_eqv (oneMinusSqNode M k hM hk) (oneMinusSqNode_pos hM hk))) ?_
  exact Q'.one_mul_eqv _

/-- **Step B.**  `mul LZB (s_k·(s_+ + s_-)) ≋ ofQ'(½h·(−x_kB0)) · (s_+ + s_-)`.
`LZB = s_k·MIDb`; regroup to `(s_k·s_k)·(MIDb·(s_++s_-))`, collapse `s_k² ≋ oms`
(`node_sq_collapse`), then `oms·MIDb ≈ ½h(−x_kB0)` (`oms_mul_MIDb`). -/
theorem stepB (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) (hk : k < M) :
    CReal.Equiv
      (CReal.mul (ChebOrthoSecondDiff.LZB e he M hM k hk) (antisymmS M hM k))
      (CReal.mul (CReal.ofQ' (ChebOrthoLegProof.half
          * (lebW M hM * (-(xk M hM k * B0 e he M hM k))))) (radSum M hM k)) := by
  -- (1) regroup the four factors:  (s_k·MIDb)·(s_k·(s_++s_-)) ≋ (s_k·s_k)·(MIDb·(s_++s_-))
  have hregroup : CReal.Equiv
      (CReal.mul (ChebOrthoSecondDiff.LZB e he M hM k hk) (antisymmS M hM k))
      (CReal.mul (CReal.mul (sK M hM k) (sK M hM k))
        (CReal.mul (CReal.ofQ' (ChebOrthoSecondDiff.MIDb e he M hM k hk)) (radSum M hM k))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun p => by
      show ((sK M hM k).approx p * ChebOrthoSecondDiff.MIDb e he M hM k hk)
            * ((sK M hM k).approx p * (radSum M hM k).approx p)
          ≈ ((sK M hM k).approx p * (sK M hM k).approx p)
            * (ChebOrthoSecondDiff.MIDb e he M hM k hk * (radSum M hM k).approx p)
      generalize (sK M hM k).approx p = s
      generalize ChebOrthoSecondDiff.MIDb e he M hM k hk = m
      generalize (radSum M hM k).approx p = r
      -- (s·m)·(s·r) ≈ (s·s)·(m·r)
      exact Pivot2.swap_mul4 s m s r)
  refine CReal.Equiv.trans hregroup ?_
  -- (2) s_k·s_k ≋ ofQ' oms
  have hnodeSq := ChebOrthoLeadingModel.node_sq_collapse M hM k hk
  refine CReal.Equiv.trans (Pivot2.mul_congr_left (B :=
      CReal.mul (CReal.ofQ' (ChebOrthoSecondDiff.MIDb e he M hM k hk)) (radSum M hM k)) hnodeSq) ?_
  -- (3) ofQ' oms · (ofQ' MIDb · (s_++s_-)) ≋ (ofQ' oms · ofQ' MIDb) · (s_++s_-)
  refine CReal.Equiv.trans
    (CReal.Equiv.symm (CRealAlg.cmul_assoc (CReal.ofQ' (oneMinusSqNode M k hM hk))
      (CReal.ofQ' (ChebOrthoSecondDiff.MIDb e he M hM k hk)) (radSum M hM k))) ?_
  -- (4) ofQ' oms · ofQ' MIDb ≋ ofQ'(oms·MIDb) ≋ ofQ'(½h(−x_kB0))
  refine Pivot2.mul_congr_left (B := radSum M hM k) ?_
  refine CReal.Equiv.trans
    (CReal.Equiv.symm (CRealAlg.ofQ'_mul (oneMinusSqNode M k hM hk)
      (ChebOrthoSecondDiff.MIDb e he M hM k hk))) ?_
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => oms_mul_MIDb e he M hM k hk)

/-- The constant `q1 = (1−b_{k+1}²) − (1−b_k²) = bdyOneMinusSq(k+1) − bdyOneMinusSq(k)`. -/
def q1 (M : Nat) (hM : 0 < M) (k : Nat) (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) : Q' :=
  bdyOneMinusSq M (k + 1) hM (Nat.succ_pos k) hk1n + (-(bdyOneMinusSq M k hM hk0 hkn))

/-- **`(s_+ − s_-)·(s_+ + s_-) ≋ ofQ' q1`.**  Difference of squares (`diffOfSquares_eqv`,
per-approx) then the radicands collapse (`radSq_diff_equiv`). -/
theorem radDiff_mul_radSum (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    CReal.Equiv (CReal.mul (radDiff M hM k) (radSum M hM k))
      (CReal.ofQ' (q1 M hM k hk0 hkn hk1n)) := by
  -- (s_+−s_-)(s_++s_-) ≋ s_+² + (−s_-²)
  have hdsq : CReal.Equiv (CReal.mul (radDiff M hM k) (radSum M hM k))
      (CReal.add (CReal.mul (sP M hM k) (sP M hM k))
        (CReal.neg (CReal.mul (sM M hM k) (sM M hM k)))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun p => by
      show ((sP M hM k).approx p + (-((sM M hM k).approx p)))
            * ((sP M hM k).approx p + (sM M hM k).approx p)
          ≈ ((sP M hM k).approx p * (sP M hM k).approx p
              + (-((sM M hM k).approx p * (sM M hM k).approx p)))
      exact ChebOrthoCancelDiv.diffOfSquares_eqv ((sP M hM k).approx p) ((sM M hM k).approx p))
  refine CReal.Equiv.trans hdsq ?_
  -- s_+² + (−s_-²) ≋ ofQ'(bdy(k+1)) + (−ofQ'(bdy(k)))
  have hrad := ChebOrthoRemainder.radSq_diff_equiv M hM k hk0 hkn hk1n
  refine CReal.Equiv.trans hrad ?_
  -- ofQ' bdy(k+1) + (−ofQ' bdy(k)) ≋ ofQ'(bdy(k+1) + (−bdy(k))) = ofQ' q1
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-- **Step A.**  `mul (ofQ'(½B0)·(s_+ − s_-)) (s_k·(s_+ + s_-)) ≋ ofQ'(½B0·q1) · s_k`. -/
theorem stepA (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    CReal.Equiv
      (CReal.mul (CReal.mul (CReal.ofQ' (ChebOrthoLegProof.half * B0 e he M hM k)) (radDiff M hM k))
        (antisymmS M hM k))
      (CReal.mul (CReal.ofQ' (ChebOrthoLegProof.half * B0 e he M hM k * q1 M hM k hk0 hkn hk1n))
        (sK M hM k)) := by
  -- (1) regroup:  ((c·d)·(s·r)) ≋ c·(s·(d·r))
  have hregroup : CReal.Equiv
      (CReal.mul (CReal.mul (CReal.ofQ' (ChebOrthoLegProof.half * B0 e he M hM k)) (radDiff M hM k))
        (antisymmS M hM k))
      (CReal.mul (CReal.ofQ' (ChebOrthoLegProof.half * B0 e he M hM k))
        (CReal.mul (sK M hM k) (CReal.mul (radDiff M hM k) (radSum M hM k)))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun p => by
      show ((ChebOrthoLegProof.half * B0 e he M hM k) * (radDiff M hM k).approx p)
            * ((sK M hM k).approx p * (radSum M hM k).approx p)
          ≈ (ChebOrthoLegProof.half * B0 e he M hM k)
            * ((sK M hM k).approx p
                * ((radDiff M hM k).approx p * (radSum M hM k).approx p))
      generalize ChebOrthoLegProof.half * B0 e he M hM k = c
      generalize (radDiff M hM k).approx p = d
      generalize (sK M hM k).approx p = s
      generalize (radSum M hM k).approx p = r
      -- (c·d)·(s·r) ≈ c·(s·(d·r))
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c d (s * r)) ?_
      refine Q'.mul_eqv_congr_left _ _ _ ?_
      -- d·(s·r) ≈ s·(d·r)
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv d s r)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv d s)) ?_
      exact Q'.mul_assoc_eqv s d r)
  refine CReal.Equiv.trans hregroup ?_
  -- (2) (s_+−s_-)(s_++s_-) ≋ ofQ' q1
  refine CReal.Equiv.trans
    (Pivot2.mul_congr_right (A := CReal.ofQ' (ChebOrthoLegProof.half * B0 e he M hM k))
      (Pivot2.mul_congr_right (A := sK M hM k) (radDiff_mul_radSum M hM k hk0 hkn hk1n))) ?_
  -- (3) c·(s_k·ofQ' q1) ≋ ofQ'(c·q1)·s_k
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  show (ChebOrthoLegProof.half * B0 e he M hM k)
        * ((sK M hM k).approx p * q1 M hM k hk0 hkn hk1n)
      ≈ ((ChebOrthoLegProof.half * B0 e he M hM k) * q1 M hM k hk0 hkn hk1n)
        * (sK M hM k).approx p
  generalize ChebOrthoLegProof.half * B0 e he M hM k = c
  generalize (sK M hM k).approx p = s
  generalize q1 M hM k hk0 hkn hk1n = qq
  -- c·(s·qq) ≈ (c·qq)·s
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv c s qq)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv c s)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv s c qq) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv s (c * qq)) (Q'.eqv_refl _)

/-- Distribute `mul (A + (−B)) S ≋ mul A S + (−(mul B S))` (per-approx). -/
theorem mul_addNeg_distrib (A B S : CReal) :
    CReal.Equiv (CReal.mul (CReal.add A (CReal.neg B)) S)
      (CReal.add (CReal.mul A S) (CReal.neg (CReal.mul B S))) :=
  SumOfSquares.Equiv_of_approx_eqv (fun p => by
    show (A.approx p + (-(B.approx p))) * S.approx p
        ≈ (A.approx p * S.approx p + (-(B.approx p * S.approx p)))
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (A.approx p) (-(B.approx p)) (S.approx p)) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_mul_eqv (B.approx p) (S.approx p)))

/-- **`mul antisymmTarget antisymmS ≋ ofQ'(½B0·q1)·s_k + (−(ofQ'(½h(−x_kB0))·(s_++s_-)))`.** -/
theorem antisymm_numer_split (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    CReal.Equiv
      (CReal.mul (antisymmTarget e he M hM k hkn) (antisymmS M hM k))
      (CReal.add
        (CReal.mul (CReal.ofQ' (ChebOrthoLegProof.half * B0 e he M hM k * q1 M hM k hk0 hkn hk1n))
          (sK M hM k))
        (CReal.neg
          (CReal.mul (CReal.ofQ' (ChebOrthoLegProof.half
              * (lebW M hM * (-(xk M hM k * B0 e he M hM k))))) (radSum M hM k)))) := by
  -- distribute
  refine CReal.Equiv.trans
    (mul_addNeg_distrib
      (CReal.mul (CReal.ofQ' (ChebOrthoLegProof.half * B0 e he M hM k)) (radDiff M hM k))
      (ChebOrthoSecondDiff.LZB e he M hM k hkn) (antisymmS M hM k)) ?_
  -- congr: stepA on the first, stepB on the second (under neg)
  refine Pivot2.add_congr (stepA e he M hM k hk0 hkn hk1n)
    (Pivot2.neg_congr (stepB e he M hM k hkn))

/-- The scalar coefficient `c2 = δ·x_k·B0 = (1/M)·x_k·B0`. -/
def c2 (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) : Q' :=
  ChebOrthoLegProof.delta M hM * (xk M hM k * B0 e he M hM k)

/-- **`½·h·(−(x_k·B0)) ≈ −c2`.**  `½·(2/M)·(−x_kB0) = −(1/M)·(x_kB0) = −δ·x_kB0`. -/
theorem halfH_negxB_eq_negc2 (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) :
    (ChebOrthoLegProof.half * (lebW M hM * (-(xk M hM k * B0 e he M hM k))))
      ≈ (-(c2 e he M hM k)) := by
  -- ½·(h·(−p)) where p = x_k·B0 ; ½·h = δ ; result = −(δ·p)
  generalize hp : (xk M hM k * B0 e he M hM k) = p
  -- ½·(h·(−p)) ≈ ½·(−(h·p)) ≈ −(½·(h·p)) ≈ −((½·h)·p) ; ½·h ≈ δ
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_neg_eqv (lebW M hM) p)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv ChebOrthoLegProof.half (lebW M hM * p)) ?_
  refine Q'.neg_eqv_congr _ _ ?_
  -- ½·(h·p) ≈ (½·h)·p ≈ δ·p = c2 (after p = x_k·B0)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv ChebOrthoLegProof.half (lebW M hM) p)) ?_
  show ((ChebOrthoLegProof.half * lebW M hM) * p) ≈ c2 e he M hM k
  -- ½·h ≈ δ
  have hhalfH : (ChebOrthoLegProof.half * lebW M hM) ≈ ChebOrthoLegProof.delta M hM := by
    show (ChebOrthoLegProof.half * lebW M hM).num
          * ((ChebOrthoLegProof.delta M hM).den : Int)
        = (ChebOrthoLegProof.delta M hM).num
          * ((ChebOrthoLegProof.half * lebW M hM).den : Int)
    rw [Q'.mul_den_cast,
      show (ChebOrthoLegProof.half * lebW M hM).num
          = (ChebOrthoLegProof.half).num * (lebW M hM).num from rfl]
    show ((ChebOrthoLegProof.half).num * (Q'.mkPos 2 M hM).num)
          * ((Q'.mkPos 1 M hM).den : Int)
        = (Q'.mkPos 1 M hM).num
          * (((ChebOrthoLegProof.half).den : Int) * ((Q'.mkPos 2 M hM).den : Int))
    rw [Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_num, Q'.mkPos_den]
    have hhn : (ChebOrthoLegProof.half).num = 1 := by decide
    have hhd : ((ChebOrthoLegProof.half).den : Int) = 2 := by decide
    rw [hhn, hhd]; push_cast; omega
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hhalfH) ?_
  show (ChebOrthoLegProof.delta M hM * p) ≈ c2 e he M hM k
  rw [← hp]; exact Q'.eqv_refl _

/-- The pure-rational scalar identity `½·q1 ≈ −2·(δ·x_k)` (no `B0`).  `q1 ≈ −4A/M²`
(`bdyOneMinusSq_diff`, `A = 2k+1−M`), `½·q1 ≈ −2A/M² = −2·(1/M)·(A/M) = −2δx_k`. -/
theorem half_q1_eq (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    (ChebOrthoLegProof.half * q1 M hM k hk0 hkn hk1n)
      ≈ ((-(((1:Q')+1)))
          * (ChebOrthoLegProof.delta M hM * xk M hM k)) := by
  -- q1 ≈ mkPos (−4A) (M²)
  have hq1 := ChebOrthoRemainder.bdyOneMinusSq_diff M k hM hk0 hkn hk1n
  -- ½·q1 ≈ ½·mkPos(−4A)(M²)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hq1) ?_
  -- both sides are mkPos with den M² ; cross-mult check
  -- LHS = ½ · mkPos(−4A)(omsDen M),  RHS = (−2)·(δ·x_k)
  -- δ·x_k = mkPos 1 M · mkPos A M = mkPos A (M·M)
  show (ChebOrthoLegProof.half
        * Q'.mkPos (-(4 * (2 * (k : Int) + 1 - (M : Int))))
            (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM)).num
        * (((-(((1:Q')+1))) * (ChebOrthoLegProof.delta M hM * xk M hM k)).den : Int)
      = ((-(((1:Q')+1))) * (ChebOrthoLegProof.delta M hM * xk M hM k)).num
        * ((ChebOrthoLegProof.half
            * Q'.mkPos (-(4 * (2 * (k : Int) + 1 - (M : Int))))
                (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM)).den : Int)
  -- expand numerators/dens
  have hLn : (ChebOrthoLegProof.half
        * Q'.mkPos (-(4 * (2 * (k : Int) + 1 - (M : Int))))
            (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM)).num
      = (ChebOrthoLegProof.half).num * (-(4 * (2 * (k : Int) + 1 - (M : Int)))) := by
    show (ChebOrthoLegProof.half).num
        * (Q'.mkPos (-(4 * (2 * (k : Int) + 1 - (M : Int)))) _ _).num = _
    rw [Q'.mkPos_num]
  have hLd : ((ChebOrthoLegProof.half
        * Q'.mkPos (-(4 * (2 * (k : Int) + 1 - (M : Int))))
            (SemicircleIntegral.omsDen M) (SemicircleIntegral.omsDen_pos hM)).den : Int)
      = ((ChebOrthoLegProof.half).den : Int) * ((SemicircleIntegral.omsDen M : Nat) : Int) := by
    rw [Q'.mul_den_cast]
    show (((ChebOrthoLegProof.half).den : Int))
        * ((Q'.mkPos (-(4 * (2 * (k : Int) + 1 - (M : Int)))) (SemicircleIntegral.omsDen M) _).den : Int) = _
    rw [Q'.mkPos_den]
  have hRn : ((-(((1:Q')+1))) * (ChebOrthoLegProof.delta M hM * xk M hM k)).num
      = (-(((1:Q')+1))).num * ((ChebOrthoLegProof.delta M hM).num * (xk M hM k).num) := by
    show (-(((1:Q')+1))).num * (ChebOrthoLegProof.delta M hM * xk M hM k).num = _
    show (-(((1:Q')+1))).num * ((ChebOrthoLegProof.delta M hM).num * (xk M hM k).num) = _
    rfl
  have hRd : (((-(((1:Q')+1))) * (ChebOrthoLegProof.delta M hM * xk M hM k)).den : Int)
      = ((-(((1:Q')+1))).den : Int)
        * (((ChebOrthoLegProof.delta M hM).den : Int) * ((xk M hM k).den : Int)) := by
    rw [Q'.mul_den_cast, Q'.mul_den_cast]
  rw [hLn, hLd, hRn, hRd]
  -- delta = mkPos 1 M, xk = mkPos A M, half = mkPos 1 2, omsDen M = M*M
  have hdn : (ChebOrthoLegProof.delta M hM).num = 1 := by
    show (Q'.mkPos 1 M hM).num = 1; rw [Q'.mkPos_num]
  have hdd : ((ChebOrthoLegProof.delta M hM).den : Int) = (M : Int) := by
    show ((Q'.mkPos 1 M hM).den : Int) = (M : Int); rw [Q'.mkPos_den]
  have hxn : (xk M hM k).num = (2 * (k : Int) + 1 - (M : Int)) := by
    show (Q'.mkPos ((2 * (k : Int) + 1) - (M : Int)) M hM).num = _; rw [Q'.mkPos_num]
  have hxd : ((xk M hM k).den : Int) = (M : Int) := by
    show ((Q'.mkPos ((2 * (k : Int) + 1) - (M : Int)) M hM).den : Int) = _; rw [Q'.mkPos_den]
  have hhn : (ChebOrthoLegProof.half).num = 1 := by decide
  have hhd : ((ChebOrthoLegProof.half).den : Int) = 2 := by decide
  have hn11 : (-(((1:Q')+1))).num = -2 := by decide
  have hd11 : ((-(((1:Q')+1))).den : Int) = 1 := by decide
  have homs : ((SemicircleIntegral.omsDen M : Nat) : Int) = (M : Int) * (M : Int) := by
    show (((M * M : Nat)) : Int) = _; push_cast; rfl
  rw [hdn, hdd, hxn, hxd, hhn, hhd, hn11, hd11, homs]
  generalize (2 * (k : Int) + 1 - (M : Int)) = A
  generalize (M : Int) * (M : Int) = mm
  -- goal: 1 * (−(4·A)) * (1·mm) = (−2) * (1·A) * (2·mm) ; both = −4·(A·mm)
  simp only [Int.one_mul, Int.neg_mul]
  -- now:  −(4 * A * mm) = −(2 * A * (2 * mm))
  refine congrArg (fun z => -z) ?_
  -- 4 * A * mm = 2 * A * (2 * mm) ; rewrite RHS as (2*2)*(A*mm) = 4*(A*mm), LHS as 4*(A*mm)
  have hRgoal : (2 : Int) * A * (2 * mm) = 4 * (A * mm) := by
    have : (2 : Int) * A * (2 * mm) = (2 * 2) * (A * mm) := by
      simp only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]
    rw [this]; rfl
  have hLgoal : (4 : Int) * A * mm = 4 * (A * mm) := by rw [Int.mul_assoc]
  rw [hLgoal, hRgoal]

/-- **`½·B0·q1 ≈ −(c2 + c2)`.**  `½·B0·q1 ≈ B0·(½·q1) ≈ B0·(−2·δx_k) ≈ −2·c2`. -/
theorem half_B0_q1_eq (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    (ChebOrthoLegProof.half * B0 e he M hM k * q1 M hM k hk0 hkn hk1n)
      ≈ (-(c2 e he M hM k + c2 e he M hM k)) := by
  -- ½·B0·q1 ≈ B0·(½·q1)
  have hreassoc : (ChebOrthoLegProof.half * B0 e he M hM k * q1 M hM k hk0 hkn hk1n)
      ≈ (B0 e he M hM k * (ChebOrthoLegProof.half * q1 M hM k hk0 hkn hk1n)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv ChebOrthoLegProof.half (B0 e he M hM k))) ?_
    exact Q'.mul_assoc_eqv (B0 e he M hM k) ChebOrthoLegProof.half (q1 M hM k hk0 hkn hk1n)
  refine Q'.eqv_trans _ _ _ hreassoc ?_
  -- B0·(½q1) ≈ B0·(−2δx_k)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (half_q1_eq M hM k hk0 hkn hk1n)) ?_
  -- B0·((−2)·(δ·x_k)) ≈ −(c2 + c2)  ;  c2 = δ·(x_k·B0)
  -- B0·((−(1+1))·(δ·x_k)) ≈ (−(1+1))·(B0·(δ·x_k)) ≈ (−(1+1))·(δ·(x_k·B0)) = (−(1+1))·c2
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (B0 e he M hM k) (-(((1:Q')+1)))
      (ChebOrthoLegProof.delta M hM * xk M hM k))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv (B0 e he M hM k) (-(((1:Q')+1))))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (-(((1:Q')+1))) (B0 e he M hM k)
      (ChebOrthoLegProof.delta M hM * xk M hM k)) ?_
  -- (−(1+1))·(B0·(δx_k)) ; collapse B0·(δx_k) ≈ δ·(x_k·B0) = c2
  have hc2 : (B0 e he M hM k * (ChebOrthoLegProof.delta M hM * xk M hM k))
      ≈ c2 e he M hM k := by
    -- B0·(δ·x_k) ≈ δ·(x_k·B0)
    show (B0 e he M hM k * (ChebOrthoLegProof.delta M hM * xk M hM k))
        ≈ (ChebOrthoLegProof.delta M hM * (xk M hM k * B0 e he M hM k))
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (B0 e he M hM k) _) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (ChebOrthoLegProof.delta M hM) (xk M hM k) (B0 e he M hM k)) ?_
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hc2) ?_
  -- (−(1+1))·c2 ≈ −((1+1)·c2) ≈ −(c2 + c2)
  refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv ((1:Q')+1) (c2 e he M hM k)) ?_
  refine Q'.neg_eqv_congr _ _ ?_
  -- (1+1)·c2 ≈ c2 + c2
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (1:Q') 1 (c2 e he M hM k)) ?_
  exact Cheb.add_eqv_congr _ _ _ _ (Q'.one_mul_eqv (c2 e he M hM k)) (Q'.one_mul_eqv (c2 e he M hM k))

/-- **THE ANTISYMMETRIC NUMERATOR REDUCTION.**
`mul antisymmTarget (s_k·(s_+ + s_-)) ≋ ofQ'(c2)·symmD`, `c2 = δ·x_k·B0`.  Combines
`antisymm_numer_split` with the coefficient identities `half_B0_q1_eq`
(`½B0·q1 ≈ −(c2+c2)`) and `halfH_negxB_eq_negc2` (`½h(−x_kB0) ≈ −c2`), then the exact
per-approx factoring `ofQ'(−(c2+c2))·s_k + (−(ofQ'(−c2)·(s_++s_-))) ≈ c2·((s_++s_-)−2s_k)`. -/
theorem antisymm_numer (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    CReal.Equiv
      (CReal.mul (antisymmTarget e he M hM k hkn) (antisymmS M hM k))
      (CReal.mul (CReal.ofQ' (c2 e he M hM k)) (symmD M hM k)) := by
  refine CReal.Equiv.trans (antisymm_numer_split e he M hM k hk0 hkn hk1n) ?_
  -- substitute the two coefficient identities (lift ≈ to ofQ' Equiv)
  have hc1 : CReal.Equiv
      (CReal.ofQ' (ChebOrthoLegProof.half * B0 e he M hM k * q1 M hM k hk0 hkn hk1n))
      (CReal.ofQ' (-(c2 e he M hM k + c2 e he M hM k))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => half_B0_q1_eq e he M hM k hk0 hkn hk1n)
  have hc2 : CReal.Equiv
      (CReal.ofQ' (ChebOrthoLegProof.half * (lebW M hM * (-(xk M hM k * B0 e he M hM k)))))
      (CReal.ofQ' (-(c2 e he M hM k))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => halfH_negxB_eq_negc2 e he M hM k)
  refine CReal.Equiv.trans
    (Pivot2.add_congr
      (Pivot2.mul_congr_left (B := sK M hM k) hc1)
      (Pivot2.neg_congr (Pivot2.mul_congr_left (B := radSum M hM k) hc2))) ?_
  -- final per-approx factoring
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  show ((-(c2 e he M hM k + c2 e he M hM k)) * (sK M hM k).approx p
        + (-((-(c2 e he M hM k)) * (radSum M hM k).approx p)))
      ≈ (c2 e he M hM k
          * ((radSum M hM k).approx p + (-((nodeWeight M hM k).approx p + (nodeWeight M hM k).approx p))))
  generalize hcc : c2 e he M hM k = c
  generalize hr : (radSum M hM k).approx p = r
  -- sK = nodeWeight, so (sK).approx p = (nodeWeight).approx p
  show ((-(c + c)) * (sK M hM k).approx p + (-((-c) * r)))
      ≈ (c * (r + (-((nodeWeight M hM k).approx p + (nodeWeight M hM k).approx p))))
  have hsk : (sK M hM k).approx p = (nodeWeight M hM k).approx p := rfl
  rw [hsk]
  generalize hs : (nodeWeight M hM k).approx p = s
  -- (−(c+c))·s + (−((−c)·r)) ≈ c·(r + (−(s+s)))
  -- LHS: −((c+c)·s) + c·r  ;  RHS: c·r + c·(−(s+s)) = c·r − c·(s+s) = c·r − (c+c)·s ... check
  -- RHS = c·r + (−(c·(s+s))) = c·r + (−((c·s)+(c·s)))
  -- LHS = (−((c+c)·s)) + (c·r) = (−((c·s)+(c·s))) + c·r
  -- both equal c·r + (−((c·s)+(c·s))) by add_comm.
  -- LHS rewrite:
  refine Q'.eqv_trans _ (c * r + (-((c * s) + (c * s)))) _ ?_ (Q'.eqv_symm ?_)
  · -- LHS ≈ c·r + (−((c·s)+(c·s)))
    refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · -- −((−c)·r) ≈ c·r
      refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.neg_mul_eqv c r)) ?_
      exact Q'.neg_neg_eqv (c * r)
    · -- (−(c+c))·s ≈ −((c·s)+(c·s))
      refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv (c + c) s) ?_
      refine Q'.neg_eqv_congr _ _ ?_
      exact Q'.add_mul_eqv c c s
  · -- RHS ≈ c·r + (−((c·s)+(c·s)))
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c r (-(s + s))) ?_
    refine Q'.add_eqv_congr_left _ _ _ ?_
    -- c·(−(s+s)) ≈ −((c·s)+(c·s))
    refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv c (s + s)) ?_
    refine Q'.neg_eqv_congr _ _ ?_
    exact Q'.mul_add_eqv c s s

/-- The √-scale lower bound `L = omsSqrtLb · recipWitness` on `S = s_k·(s_+ + s_-)`. -/
def antisymmL (M k : Nat) (hM : 0 < M) : Q' :=
  omsSqrtLb M k hM * ChebOrthoInterior.recipWitness M (jdist M k) hM

theorem antisymmL_pos (M k : Nat) (hM : 0 < M) (hkn : k < M) (hj : 2 ≤ jdist M k) :
    (0 : Q') < antisymmL M k hM :=
  Q'.mul_pos (omsSqrtLb_pos M k hM hkn) (ChebOrthoInterior.recipWitness_pos M (jdist M k) hM hj)

/-- **Pointwise lower bound on `antisymmS = s_k·(s_+ + s_-)`.**  `s_k ≥ omsSqrtLb`
(`node_approx_ge_omsSqrtLb`), `s_+ + s_- ≥ recipWitness` (`interiorRadicalSum_ptwise`),
both nonneg, so the product `≥ omsSqrtLb·recipWitness`. -/
theorem antisymmS_lower (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hj : 2 ≤ jdist M k) :
    ∀ n, antisymmL M k hM ≤ (antisymmS M hM k).approx n := by
  intro n
  show antisymmL M k hM
      ≤ (sK M hM k).approx n * (radSum M hM k).approx n
  -- s_k.approx ≥ omsSqrtLb ≥ 0 ; (s_++s_-).approx ≥ recipWitness ≥ 0
  have hsk : omsSqrtLb M k hM ≤ (nodeWeight M hM k).approx n :=
    node_approx_ge_omsSqrtLb M hM k hk0 hkn n
  have hrs : ChebOrthoInterior.recipWitness M (jdist M k) hM
      ≤ (CReal.add (bdyRadical M hM (k + 1)) (bdyRadical M hM k)).approx n :=
    ChebOrthoCancelDiv.interiorRadicalSum_ptwise M hM k hk0 hkn hj n
  have hskn : (0 : Q') ≤ (nodeWeight M hM k).approx n :=
    Q'.le_trans' _ _ _ (omsSqrtLb_nonneg M k hM hkn) hsk
  have hrwn : (0 : Q') ≤ ChebOrthoInterior.recipWitness M (jdist M k) hM :=
    Q'.le_of_lt (ChebOrthoInterior.recipWitness_pos M (jdist M k) hM hj)
  -- product
  show omsSqrtLb M k hM * ChebOrthoInterior.recipWitness M (jdist M k) hM
      ≤ (nodeWeight M hM k).approx n * (radSum M hM k).approx n
  show omsSqrtLb M k hM * ChebOrthoInterior.recipWitness M (jdist M k) hM
      ≤ (nodeWeight M hM k).approx n
        * (CReal.add (bdyRadical M hM (k + 1)) (bdyRadical M hM k)).approx n
  exact Q'.mul_le_mul_of_nonneg hsk hrs hskn hrwn

/-- The two-sided value bound `|c2|`-rational `c2Abs = δ·|x_k|·2` (`|x_k|≤1·... `; we use
`|c2| ≤ c2Abs` with `c2Abs := mkPos (2·|2k+1−M|) (M·M)` since `|x_k·B0| ≤ |x_k|·2`,
`δ = 1/M`, `x_k = (2k+1−M)/M`). -/
def c2Abs (M k : Nat) (hM : 0 < M) : Q' :=
  Q'.mkPos (2 * (ChebOrthoCancelDiv.xkAbs M k : Int)) (M * M) (Nat.mul_pos hM hM)

theorem c2Abs_nonneg (M k : Nat) (hM : 0 < M) : (0 : Q') ≤ c2Abs M k hM := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (Q'.mkPos (2 * (ChebOrthoCancelDiv.xkAbs M k : Int)) (M * M) (Nat.mul_pos hM hM)).num
  rw [Q'.mkPos_num]
  exact Int.mul_nonneg (by decide) (Int.natCast_nonneg _)

/-- `|x_k| ≤ mkPos |2k+1−M| M`. -/
theorem xk_abs_le (M : Nat) (hM : 0 < M) (k : Nat) :
    xk M hM k ≤ Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM
      ∧ (-(xk M hM k)) ≤ Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM := by
  have hxn : (xk M hM k).num = (2 * (k : Int) + 1 - (M : Int)) := by
    show (Q'.mkPos ((2 * (k : Int) + 1) - (M : Int)) M hM).num = _; rw [Q'.mkPos_num]
  have hxd : ((xk M hM k).den : Int) = (M : Int) := by
    show ((Q'.mkPos ((2 * (k : Int) + 1) - (M : Int)) M hM).den : Int) = _; rw [Q'.mkPos_den]
  have hAn : (Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM).num
      = (ChebOrthoCancelDiv.xkAbs M k : Int) := by rw [Q'.mkPos_num]
  have hAd : ((Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM).den : Int) = (M : Int) := by
    rw [Q'.mkPos_den]
  have hM0 : (0 : Int) ≤ (M : Int) := Int.natCast_nonneg _
  -- |A| := natAbs(2k+1−M)
  have hxa1 : (2 * (k : Int) + 1 - (M : Int)) ≤ (ChebOrthoCancelDiv.xkAbs M k : Int) := by
    show (2 * (k : Int) + 1 - (M : Int)) ≤ ((2 * (k : Int) + 1 - (M : Int)).natAbs : Int)
    exact Int.le_natAbs
  have hxa2 : (-(2 * (k : Int) + 1 - (M : Int))) ≤ (ChebOrthoCancelDiv.xkAbs M k : Int) := by
    show (-(2 * (k : Int) + 1 - (M : Int))) ≤ ((2 * (k : Int) + 1 - (M : Int)).natAbs : Int)
    have := Int.le_natAbs (a := -(2 * (k : Int) + 1 - (M : Int)))
    rw [Int.natAbs_neg] at this; exact this
  refine ⟨?_, ?_⟩
  · show (xk M hM k).num * ((Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM).den : Int)
        ≤ (Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM).num * ((xk M hM k).den : Int)
    rw [hxn, hxd, hAn, hAd]
    exact Int.mul_le_mul_of_nonneg_right hxa1 hM0
  · show (-(xk M hM k)).num * ((Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM).den : Int)
        ≤ (Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM).num * ((-(xk M hM k)).den : Int)
    have hnn : (-(xk M hM k)).num = -(xk M hM k).num := rfl
    have hnd : ((-(xk M hM k)).den : Int) = ((xk M hM k).den : Int) := rfl
    rw [hnn, hnd, hxn, hxd, hAn, hAd]
    exact Int.mul_le_mul_of_nonneg_right hxa2 hM0

/-- **`|c2| ≤ c2Abs`.**  `c2 = δ·(x_k·B0)`, `|x_k|≤|A|/M`, `|B0|≤2`, `δ=1/M`, so
`|c2| ≤ (1/M)·(|A|/M·2) = 2|A|/M²`. -/
theorem c2_abs_le (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) (hkn : k < M) :
    c2 e he M hM k ≤ c2Abs M k hM ∧ (-(c2 e he M hM k)) ≤ c2Abs M k hM := by
  -- box bounds for x_k and B0
  have hx1 : RiemannSOS.uniformMidpoint M hM k ≤ (1 : Q') := RiemannSOS.node_hi M hM k hkn
  have hxm1 : (-(1 : Q')) ≤ RiemannSOS.uniformMidpoint M hM k := RiemannSOS.node_lo M hM k
  obtain ⟨hB0hi, hB0lo⟩ := ChebOrthoGradedClose.gbracket_abs_le e he (xk M hM k) hx1 hxm1
  obtain ⟨hxhi, hxlo⟩ := xk_abs_le M hM k
  -- |x_k·B0| ≤ (mkPos|A|M)·2
  have hxAge : (0 : Q') ≤ Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM := by
    rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; exact Int.natCast_nonneg _
  -- −A ≤ x_k  from  −x_k ≤ A
  have hxlo' : (-(Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM)) ≤ xk M hM k := by
    have h1 := Q'.neg_le_neg hxlo
    exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.neg_neg_eqv _))
  -- −2 ≤ B0  from  −B0 ≤ 2
  have hB0lo' : (-(2 : Q')) ≤ B0 e he M hM k := by
    have h1 := Q'.neg_le_neg hB0lo
    exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.neg_neg_eqv _))
  obtain ⟨hpvlo, hpvhi⟩ := ChebOrthoLegAssembly.mul_abs_le
    (u := xk M hM k) (v := B0 e he M hM k)
    (B := Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM) (d := (2 : Q'))
    hxAge (by decide) hxlo' hxhi hB0lo' hB0hi
  -- c2 = δ·(x_k·B0) ; δ ≥ 0
  have hd0 : (0 : Q') ≤ ChebOrthoLegProof.delta M hM := by
    show (0 : Q') ≤ Q'.mkPos 1 M hM; rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide
  -- −(δ·(B·d)) ≤ δ·(x_k·B0) ≤ δ·(B·d)
  obtain ⟨hclo, hchi⟩ := ChebOrthoLegAssembly.mul_abs_le
    (u := ChebOrthoLegProof.delta M hM) (v := xk M hM k * B0 e he M hM k)
    (B := ChebOrthoLegProof.delta M hM)
    (d := Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM * (2 : Q'))
    hd0 (Q'.mul_nonneg _ _ hxAge (by decide))
    (by
      refine Q'.le_trans' _ (0 : Q') _ ?_ hd0
      refine Q'.le_trans' _ (-(0:Q')) _ (Q'.neg_le_neg hd0) (Q'.le_of_eqv (by decide)))
    (Q'.le_refl' _) hpvlo hpvhi
  -- δ·(mkPos|A|M·2) ≈ c2Abs
  have hprodeqv : (ChebOrthoLegProof.delta M hM
        * (Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM * (2 : Q')))
      ≈ c2Abs M k hM := by
    -- δ·(mkPos|A|M·2) = mkPos 1 M·(mkPos|A|M·2) ; cross-mult to mkPos(2|A|)(M·M)
    show (ChebOrthoLegProof.delta M hM
          * (Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM * (2 : Q'))).num
          * ((c2Abs M k hM).den : Int)
        = (c2Abs M k hM).num
          * ((ChebOrthoLegProof.delta M hM
              * (Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM * (2 : Q'))).den : Int)
    have hcAn : (c2Abs M k hM).num = 2 * (ChebOrthoCancelDiv.xkAbs M k : Int) := by
      show (Q'.mkPos (2 * (ChebOrthoCancelDiv.xkAbs M k : Int)) (M * M) (Nat.mul_pos hM hM)).num = _
      rw [Q'.mkPos_num]
    have hcAd : ((c2Abs M k hM).den : Int) = ((M * M : Nat) : Int) := by
      show ((Q'.mkPos (2 * (ChebOrthoCancelDiv.xkAbs M k : Int)) (M * M) (Nat.mul_pos hM hM)).den : Int) = _
      rw [Q'.mkPos_den]
    -- LHS num = 1·(|A|·2) ; LHS den = M·(M·1)
    have hLn : (ChebOrthoLegProof.delta M hM
          * (Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM * (2 : Q'))).num
        = 1 * ((ChebOrthoCancelDiv.xkAbs M k : Int) * (2 : Q').num) := by
      show (ChebOrthoLegProof.delta M hM).num
          * (Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM * (2 : Q')).num = _
      show (Q'.mkPos 1 M hM).num
          * ((Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM).num * (2 : Q').num) = _
      rw [Q'.mkPos_num, Q'.mkPos_num]
    have hLd : ((ChebOrthoLegProof.delta M hM
          * (Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM * (2 : Q'))).den : Int)
        = (M : Int) * ((M : Int) * ((2 : Q').den : Int)) := by
      rw [Q'.mul_den_cast, Q'.mul_den_cast]
      show ((Q'.mkPos 1 M hM).den : Int)
          * (((Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM).den : Int) * ((2 : Q').den : Int)) = _
      rw [Q'.mkPos_den, Q'.mkPos_den]
    rw [hLn, hLd, hcAn, hcAd]
    have h2n : (2 : Q').num = 2 := by decide
    have h2d : ((2 : Q').den : Int) = 1 := by decide
    have hMM : ((M * M : Nat) : Int) = (M : Int) * (M : Int) := by push_cast; rfl
    rw [h2n, h2d, hMM]
    -- (1·(|A|·2))·(M·M) = (2·|A|)·(M·(M·1))
    generalize (ChebOrthoCancelDiv.xkAbs M k : Int) = a
    generalize (M : Int) = m
    simp only [Int.one_mul, Int.mul_one, Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _ hchi (Q'.le_of_eqv hprodeqv)
  · refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv hprodeqv)
    refine Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.le_refl' (c2 e he M hM k))) ?_
    -- −c2 ≤ δ·(B·d) from −(δ·(B·d)) ≤ c2  (hclo)
    have h1 : (-(c2 e he M hM k))
        ≤ (-(-(ChebOrthoLegProof.delta M hM
            * (Q'.mkPos (ChebOrthoCancelDiv.xkAbs M k : Int) M hM * (2 : Q'))))) :=
      Q'.neg_le_neg hclo
    exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.neg_neg_eqv _))

/-- The antisymmetric quotient `antisymmQuot = (c2Abs · symmQuot_sqrt) · (1/antisymmL)`. -/
def antisymmQuot (M k : Nat) (hM : 0 < M) (hkn : k < M) (hj : 2 ≤ jdist M k) : Q' :=
  (c2Abs M k hM * symmQuot_sqrt M k hM hkn)
    * Q'.recipPos (antisymmL M k hM) (antisymmL_pos M k hM hkn hj)

theorem antisymmQuot_nonneg (M k : Nat) (hM : 0 < M) (hkn : k < M) (hj : 2 ≤ jdist M k) :
    (0 : Q') ≤ antisymmQuot M k hM hkn hj := by
  refine Q'.mul_nonneg _ _ ?_ (Q'.le_of_lt (Q'.recipPos_pos _ _))
  exact Q'.mul_nonneg _ _ (c2Abs_nonneg M k hM) (symmQuot_sqrt_nonneg M k hM hkn)

/-- **THE ANTISYMMETRIC SECOND-DIFFERENCE BOUND.**  For an interior cell, the genuine
√-Hölder antisymmetric content `T1 = ½·B0·(s_+ − s_-) − LZB`  (= `½·B0·Δ₁''`) is
two-sidedly bounded by `antisymmQuot`.  Via `div_of_mul_ge` with `D = T1`,
`S = s_k·(s_+ + s_-)`, the EXACT numerator reduction `antisymm_numer`
(`D·S ≋ ofQ'(c2)·Δ₂`, `|c2|≤c2Abs`, `|Δ₂|≤symmQuot_sqrt`), and the √-scale lower bound
`antisymmS_lower`. -/
theorem antisymmSecondDiff_AbsLeRat (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) (hj : 2 ≤ jdist M k) :
    AbsLeRat (antisymmTarget e he M hM k hkn) (antisymmQuot M k hM hkn hj) := by
  -- numerator bound:  |D·S| ≤ c2Abs · symmQuot_sqrt
  obtain ⟨hc2hi, hc2lo⟩ := c2_abs_le e he M hM k hkn
  have hsymm : AbsLeRat (symmD M hM k) (symmQuot_sqrt M k hM hkn) :=
    symmSecondDiff_sqrt_AbsLeRat M hM k hk0 hkn hk1n
  have hnumK : AbsLeRat (CReal.mul (CReal.ofQ' (c2 e he M hM k)) (symmD M hM k))
      (c2Abs M k hM * symmQuot_sqrt M k hM hkn) :=
    ChebOrthoLegProof.AbsLeRat.ofQ'_smul hsymm hc2hi hc2lo (c2Abs_nonneg M k hM)
      (symmQuot_sqrt_nonneg M k hM hkn)
  have hDSK : AbsLeRat (CReal.mul (antisymmTarget e he M hM k hkn) (antisymmS M hM k))
      (c2Abs M k hM * symmQuot_sqrt M k hM hkn) :=
    ChebOrthoCancelDiv.AbsLeRat.of_equiv (antisymm_numer e he M hM k hk0 hkn hk1n) hnumK
  -- divide
  refine ChebOrthoCancelDiv.AbsLeRat.div_of_mul_ge
    (D := antisymmTarget e he M hM k hkn) (S := antisymmS M hM k)
    (K := c2Abs M k hM * symmQuot_sqrt M k hM hkn)
    (L := antisymmL M k hM)
    (KL := antisymmQuot M k hM hkn hj)
    hDSK
    (antisymmS_lower M hM k hk0 hkn hj)
    (antisymmL_pos M k hM hkn hj)
    (antisymmQuot_nonneg M k hM hkn hj)
    ?_
  -- KL·L ≈ K
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (c2Abs M k hM * symmQuot_sqrt M k hM hkn)
      (Q'.recipPos (antisymmL M k hM) (antisymmL_pos M k hM hkn hj))
      (antisymmL M k hM)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
        (Q'.mul_recipPos_eqv (antisymmL M k hM) (antisymmL_pos M k hM hkn hj)))) ?_
  exact Q'.mul_one_eqv _

/-! ## 3. The radical-leg decomposition `legRad − LZB ≈ T1 + T2` -/

/-- `T2 = ¼·(s_+ − s_-)·R_B2`, the bracket-quadratic-remainder radical term. -/
def T2 (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.mul (CReal.ofQ' ChebOrthoLegProof.quarter)
    (CReal.mul (radDiff M hM k)
      (CReal.ofQ' (ChebBracketTaylor.R_B2 e he (xk M hM k) (ChebOrthoLegProof.delta M hM))))

/-- **`bP + bM ≈ R_B2 + 2·B0`.**  `bP = G(bdyPoint(k+1)) ≈ G(x_k+δ)`,
`bM = G(bdyPoint(k)) ≈ G(x_k−δ)` (`Gbracket_arg_eqv` + `bdyPoint_eqv`); their sum is
`R_B2 + 2B0` by the definition of `R_B2`. -/
theorem bSum_eqv (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) :
    (ChebOrthoOffDiag.Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM (k + 1))
        + ChebOrthoOffDiag.Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM k))
      ≈ (ChebBracketTaylor.R_B2 e he (xk M hM k) (ChebOrthoLegProof.delta M hM)
          + (((1:Q')+1) * B0 e he M hM k)) := by
  -- bP ≈ G(x+δ), bM ≈ G(x−δ)
  have hbP : ChebOrthoOffDiag.Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM (k + 1))
      ≈ ChebOrthoOffDiag.Gbracket e he (xk M hM k + ChebOrthoLegProof.delta M hM) :=
    ChebOrthoLegProof.Gbracket_arg_eqv e he (ChebOrthoLegProof.bdyPoint_succ_eqv M hM k)
  have hbM : ChebOrthoOffDiag.Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM k)
      ≈ ChebOrthoOffDiag.Gbracket e he (xk M hM k + (-(ChebOrthoLegProof.delta M hM))) :=
    ChebOrthoLegProof.Gbracket_arg_eqv e he (ChebOrthoLegProof.bdyPoint_eqv M hM k)
  refine Q'.eqv_trans _ _ _ (Cheb.add_eqv_congr _ _ _ _ hbP hbM) ?_
  -- G(x+δ) + G(x−δ) ≈ R_B2 + 2·B0,  R_B2 = (G(x+δ)+G(x−δ)) − 2·B0
  -- so R_B2 + 2B0 = ((G(x+δ)+G(x−δ)) − 2B0) + 2B0 ≈ G(x+δ)+G(x−δ)
  refine Q'.eqv_symm ?_
  show ((ChebOrthoOffDiag.Gbracket e he (xk M hM k + ChebOrthoLegProof.delta M hM)
          + ChebOrthoOffDiag.Gbracket e he (xk M hM k + (-(ChebOrthoLegProof.delta M hM))))
        + (-(((1:Q')+(1:Q')) * ChebOrthoOffDiag.Gbracket e he (xk M hM k))))
        + (((1:Q')+1) * B0 e he M hM k)
      ≈ (ChebOrthoOffDiag.Gbracket e he (xk M hM k + ChebOrthoLegProof.delta M hM)
          + ChebOrthoOffDiag.Gbracket e he (xk M hM k + (-(ChebOrthoLegProof.delta M hM))))
  -- (S − 2B0) + 2B0 ≈ S  (B0 = Gbracket x_k by def)
  generalize hS : (ChebOrthoOffDiag.Gbracket e he (xk M hM k + ChebOrthoLegProof.delta M hM)
          + ChebOrthoOffDiag.Gbracket e he (xk M hM k + (-(ChebOrthoLegProof.delta M hM)))) = S
  show (S + (-(((1:Q')+(1:Q')) * ChebOrthoOffDiag.Gbracket e he (xk M hM k))))
        + (((1:Q')+1) * B0 e he M hM k) ≈ S
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv S (-(((1:Q')+(1:Q')) * ChebOrthoOffDiag.Gbracket e he (xk M hM k)))
      (((1:Q')+1) * B0 e he M hM k)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ ?_) (QPoly.q_add_zero_eqv S)
  -- −(2·B0) + 2·B0 ≈ 0  (note B0 = Gbracket x_k)
  show (-(((1:Q')+(1:Q')) * ChebOrthoOffDiag.Gbracket e he (xk M hM k)))
      + (((1:Q')+1) * ChebOrthoOffDiag.Gbracket e he (xk M hM k)) ≈ (0 : Q')
  exact Q'.neg_add_self_eqv _

/-- **`legRad ≈ ofQ'(½B0)·(s_+ − s_-) + T2`.**  `legRad = ¼·(s_+−s_-)·(B_++B_-)`,
`B_++B_- ≈ R_B2 + 2B0` (`bSum_eqv`), and `¼·(s_+−s_-)·(R_B2 + 2B0) = T2 + ½B0·(s_+−s_-)`. -/
theorem legRad_decomp (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) :
    CReal.Equiv (ChebOrthoSecondDiff.legRad e he M hM k)
      (CReal.add
        (CReal.mul (CReal.ofQ' (ChebOrthoLegProof.half * B0 e he M hM k)) (radDiff M hM k))
        (T2 e he M hM k)) := by
  -- collapse (ofQ' bP + ofQ' bM) ≋ ofQ'(R_B2 + 2B0)
  have hbsum : CReal.Equiv
      (CReal.add (CReal.ofQ' (ChebOrthoOffDiag.Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM (k + 1))))
        (CReal.ofQ' (ChebOrthoOffDiag.Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM k))))
      (CReal.ofQ' (ChebBracketTaylor.R_B2 e he (xk M hM k) (ChebOrthoLegProof.delta M hM)
          + (((1:Q')+1) * B0 e he M hM k))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => bSum_eqv e he M hM k)
  -- legRad ≋ ¼·(radDiff · (ofQ' bP + ofQ' bM)) ≋ ¼·(radDiff · ofQ'(R_B2+2B0))
  have hquart : CReal.Equiv (ChebOrthoSecondDiff.legRad e he M hM k)
      (CReal.mul (CReal.ofQ' ChebOrthoLegProof.quarter)
        (CReal.mul (radDiff M hM k)
          (CReal.add (CReal.ofQ' (ChebOrthoOffDiag.Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM (k + 1))))
            (CReal.ofQ' (ChebOrthoOffDiag.Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM k)))))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun p => by
      show (ChebOrthoLegProof.half * (ChebOrthoLegProof.half
              * (((bdyRadical M hM (k + 1)).approx p + (-((bdyRadical M hM k).approx p)))
                * (ChebOrthoOffDiag.Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM (k + 1))
                    + ChebOrthoOffDiag.Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM k)))))
          ≈ (ChebOrthoLegProof.quarter
              * (((bdyRadical M hM (k + 1)).approx p + (-((bdyRadical M hM k).approx p)))
                * (ChebOrthoOffDiag.Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM (k + 1))
                    + ChebOrthoOffDiag.Gbracket e he (ChebOrthoMidpoint.bdyPoint M hM k))))
      exact Q'.eqv_symm (Q'.mul_assoc_eqv ChebOrthoLegProof.half ChebOrthoLegProof.half _))
  refine CReal.Equiv.trans hquart ?_
  -- now ¼·(radDiff · (...)) ≋ ¼·(radDiff · ofQ'(R_B2+2B0))
  refine CReal.Equiv.trans
    (Pivot2.mul_congr_right (A := CReal.ofQ' ChebOrthoLegProof.quarter)
      (Pivot2.mul_congr_right (A := radDiff M hM k) hbsum)) ?_
  -- ¼·(radDiff · ofQ'(R_B2 + 2B0)) ≋ ofQ'(½B0)·radDiff + T2
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  show ChebOrthoLegProof.quarter
        * ((radDiff M hM k).approx p
          * (ChebBracketTaylor.R_B2 e he (xk M hM k) (ChebOrthoLegProof.delta M hM)
              + (((1:Q')+1) * B0 e he M hM k)))
      ≈ ((ChebOrthoLegProof.half * B0 e he M hM k) * (radDiff M hM k).approx p
          + ChebOrthoLegProof.quarter
            * ((radDiff M hM k).approx p
              * ChebBracketTaylor.R_B2 e he (xk M hM k) (ChebOrthoLegProof.delta M hM)))
  generalize hd : (radDiff M hM k).approx p = d
  generalize hR : ChebBracketTaylor.R_B2 e he (xk M hM k) (ChebOrthoLegProof.delta M hM) = R
  generalize hb : B0 e he M hM k = b
  -- ¼·(d·(R + 2b)) ≈ (½b)·d + ¼·(d·R)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_add_eqv d R (((1:Q')+1) * b))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv ChebOrthoLegProof.quarter (d * R) (d * (((1:Q')+1) * b))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) ?_
  refine Q'.add_eqv_congr' ?_ (Q'.eqv_refl _)
  -- ¼·(d·((1+1)·b)) ≈ (½·b)·d
  -- step: d·((1+1)·b) ≈ ((1+1)·b)·d
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv d (((1:Q')+1) * b))) ?_
  -- ¼·(((1+1)·b)·d) ≈ (¼·((1+1)·b))·d
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv ChebOrthoLegProof.quarter (((1:Q')+1) * b) d)) ?_
  refine Q'.mul_eqv_congr_right _ _ _ ?_
  -- ¼·((1+1)·b) ≈ ½·b :  ¼·((1+1)·b) ≈ (¼·(1+1))·b ≈ ½·b
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv ChebOrthoLegProof.quarter ((1:Q')+1) b)) ?_
  refine Q'.mul_eqv_congr_right _ _ _ ?_
  decide

/-- **THE RADICAL-LEG DECOMPOSITION.**  `legRad + (−LZB) ≈ antisymmTarget + T2`. -/
theorem rad_decomp (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) (hk : k < M) :
    CReal.Equiv
      (CReal.add (ChebOrthoSecondDiff.legRad e he M hM k)
        (CReal.neg (ChebOrthoSecondDiff.LZB e he M hM k hk)))
      (CReal.add (antisymmTarget e he M hM k hk) (T2 e he M hM k)) := by
  -- legRad + (−LZB) ≋ (ofQ'(½B0)·radDiff + T2) + (−LZB)
  refine CReal.Equiv.trans
    (Pivot2.add_congr (legRad_decomp e he M hM k) (Pivot2.equiv_refl _)) ?_
  -- ((A + T2) + (−L)) ≋ (A + (−L)) + T2   where A = ofQ'(½B0)·radDiff
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  show (((CReal.ofQ' (ChebOrthoLegProof.half * B0 e he M hM k)).approx p * (radDiff M hM k).approx p
          + (T2 e he M hM k).approx p)
        + (-((ChebOrthoSecondDiff.LZB e he M hM k hk).approx p)))
      ≈ (((CReal.ofQ' (ChebOrthoLegProof.half * B0 e he M hM k)).approx p * (radDiff M hM k).approx p
            + (-((ChebOrthoSecondDiff.LZB e he M hM k hk).approx p)))
          + (T2 e he M hM k).approx p)
  generalize (CReal.ofQ' (ChebOrthoLegProof.half * B0 e he M hM k)).approx p * (radDiff M hM k).approx p = A
  generalize (T2 e he M hM k).approx p = t
  generalize (ChebOrthoSecondDiff.LZB e he M hM k hk).approx p = L
  -- (A + t) + (−L) ≈ (A + (−L)) + t
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv A t (-L)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv t (-L))) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv A (-L) t)

/-! ## 4. The T2 (bracket-quadratic-remainder) term bound -/

/-- The quadratic bracket constant `C₂(e) = KS(e−1) + KS(e+1)`. -/
def C2num (e : Nat) : Nat := ChebMarkovModulus.KS (e - 1) + ChebMarkovModulus.KS (e + 1)

/-- **`|R_B2| ≤ C₂(e)·δ²`** at the interior cell. -/
theorem RB2_abs_le (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) (hkn : k < M) :
    ChebBracketTaylor.R_B2 e he (xk M hM k) (ChebOrthoLegProof.delta M hM)
        ≤ Q'.ofNat (C2num e) * (ChebOrthoLegProof.delta M hM * ChebOrthoLegProof.delta M hM)
      ∧ (-(ChebBracketTaylor.R_B2 e he (xk M hM k) (ChebOrthoLegProof.delta M hM)))
        ≤ Q'.ofNat (C2num e) * (ChebOrthoLegProof.delta M hM * ChebOrthoLegProof.delta M hM) := by
  have hbox := ChebOrthoOffDiagClose.OnBox_node M hM k hkn
  exact ChebMarkovModulus.bracketQuadBound_holds e he (xk M hM k) (ChebOrthoLegProof.delta M hM) hbox

/-- **T2 term bound (symbolic).**  `AbsLeRat T2 (¼·(sharpBound·(C₂·δ²)))`. -/
theorem T2_AbsLeRat (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) (hj : 2 ≤ jdist M k) :
    AbsLeRat (T2 e he M hM k)
      (ChebOrthoLegProof.quarter
        * (ChebOrthoCancelDiv.sharpBound M k hM hj
          * (Q'.ofNat (C2num e) * (ChebOrthoLegProof.delta M hM * ChebOrthoLegProof.delta M hM)))) := by
  obtain ⟨hrb1, hrb2⟩ := RB2_abs_le e he M hM k hkn
  have hRB0 : (0 : Q')
      ≤ Q'.ofNat (C2num e) * (ChebOrthoLegProof.delta M hM * ChebOrthoLegProof.delta M hM) := by
    refine Q'.mul_nonneg _ _ (ChebOrthoLegAssembly.ofNat_nonneg _) ?_
    have hd0 : (0 : Q') ≤ ChebOrthoLegProof.delta M hM := by
      show (0 : Q') ≤ Q'.mkPos 1 M hM; rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide
    exact Q'.mul_nonneg _ _ hd0 hd0
  -- |radDiff| ≤ sharpBound
  obtain ⟨hsd1, hsd2⟩ := ChebOrthoCancelDiv.bdyRadicalDiff_sharp M hM k hk0 hk1n hj
  -- inner: mul radDiff (ofQ' R_B2) ; use ofQ'_smul on (ofQ' R_B2)·radDiff then comm
  -- AbsLeRat (mul (ofQ' R_B2) radDiff) (C₂δ²·sharpBound)
  have hsharp0 : (0 : Q') ≤ ChebOrthoCancelDiv.sharpBound M k hM hj :=
    ChebOrthoCancelDiv.sharpBound_nonneg M k hM hj
  have hinner' : AbsLeRat
      (CReal.mul (CReal.ofQ' (ChebBracketTaylor.R_B2 e he (xk M hM k) (ChebOrthoLegProof.delta M hM)))
        (radDiff M hM k))
      ((Q'.ofNat (C2num e) * (ChebOrthoLegProof.delta M hM * ChebOrthoLegProof.delta M hM))
        * ChebOrthoCancelDiv.sharpBound M k hM hj) :=
    ChebOrthoLegProof.AbsLeRat.ofQ'_smul ⟨hsd1, hsd2⟩ hrb1 hrb2 hRB0 hsharp0
  -- reorder to mul radDiff (ofQ' R_B2) and bound C₂δ²·sharpBound → sharpBound·C₂δ²
  have hcomm : CReal.Equiv
      (CReal.mul (radDiff M hM k)
        (CReal.ofQ' (ChebBracketTaylor.R_B2 e he (xk M hM k) (ChebOrthoLegProof.delta M hM))))
      (CReal.mul (CReal.ofQ' (ChebBracketTaylor.R_B2 e he (xk M hM k) (ChebOrthoLegProof.delta M hM)))
        (radDiff M hM k)) :=
    CRealAlg.cmul_comm (radDiff M hM k) _
  have hinner : AbsLeRat
      (CReal.mul (radDiff M hM k)
        (CReal.ofQ' (ChebBracketTaylor.R_B2 e he (xk M hM k) (ChebOrthoLegProof.delta M hM))))
      (ChebOrthoCancelDiv.sharpBound M k hM hj
        * (Q'.ofNat (C2num e) * (ChebOrthoLegProof.delta M hM * ChebOrthoLegProof.delta M hM))) := by
    refine ChebOrthoCancelDiv.AbsLeRat.of_equiv hcomm ?_
    refine ChebOrthoGradedClose.AbsLeRat.mono hinner' ?_
    exact Q'.le_of_eqv (Q'.mul_comm_eqv _ _)
  -- outer: smul by quarter ≥ 0
  have hq0 : (0 : Q') ≤ ChebOrthoLegProof.quarter := by
    show (0 : Q') ≤ ChebOrthoLegProof.half * ChebOrthoLegProof.half
    exact Q'.mul_nonneg _ _ (by decide) (by decide)
  exact ChebOrthoGradedClose.AbsLeRat.smul_nonneg hq0 hinner

/-- The T2 threshold `M₀T = (4·C₂ e)²`. -/
def M0T (e : Nat) : Nat := (4 * C2num e) * (4 * C2num e)

/-- `¼·(sharpBound · (C₂·δ²)) ≈ mkPos (C₂·|A|) (M³·a)`,  `a = isqrt(4(j−1)j)`,
`A = xkAbs`.  We instead bound it via `sharpBound ≤ 4/jdist`. -/
theorem T2bound_le (e M k : Nat) (hM : 0 < M) (hk0 : 0 < k) (hkn : k < M)
    (hk1n : k + 1 < M) (hj : 2 ≤ jdist M k) (hthr : M0T e ≤ M) :
    (ChebOrthoLegProof.quarter
        * (ChebOrthoCancelDiv.sharpBound M k hM hj
          * (Q'.ofNat (C2num e) * (ChebOrthoLegProof.delta M hM * ChebOrthoLegProof.delta M hM))))
      ≤ ChebOrthoLegProof.quarter * ChebOrthoGraded.gradedRate e M hM k := by
  have hjpos : 0 < jdist M k := jdist_pos hkn
  have hq : 0 < isqrt M := isqrt_pos hM
  -- (1) sharpBound ≤ mkPos 4 jdist
  have hsharp : ChebOrthoCancelDiv.sharpBound M k hM hj
      ≤ Q'.mkPos 4 (jdist M k) (jdist_pos hkn) :=
    ChebOrthoFinal.sharpBound_le_recip_jdist M hM k hk1n hj
  -- C₂δ² ≥ 0
  have hC2d0 : (0 : Q')
      ≤ Q'.ofNat (C2num e) * (ChebOrthoLegProof.delta M hM * ChebOrthoLegProof.delta M hM) := by
    refine Q'.mul_nonneg _ _ (ChebOrthoLegAssembly.ofNat_nonneg _) ?_
    have hd0 : (0 : Q') ≤ ChebOrthoLegProof.delta M hM := by
      show (0 : Q') ≤ Q'.mkPos 1 M hM; rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide
    exact Q'.mul_nonneg _ _ hd0 hd0
  have hquarter0 : (0 : Q') ≤ ChebOrthoLegProof.quarter := by
    show (0 : Q') ≤ ChebOrthoLegProof.half * ChebOrthoLegProof.half
    exact Q'.mul_nonneg _ _ (by decide) (by decide)
  -- (2) sharpBound·C₂δ² ≤ (mkPos 4 j)·C₂δ²
  have hstep1 : (ChebOrthoCancelDiv.sharpBound M k hM hj
        * (Q'.ofNat (C2num e) * (ChebOrthoLegProof.delta M hM * ChebOrthoLegProof.delta M hM)))
      ≤ (Q'.mkPos 4 (jdist M k) (jdist_pos hkn)
        * (Q'.ofNat (C2num e) * (ChebOrthoLegProof.delta M hM * ChebOrthoLegProof.delta M hM))) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hsharp hC2d0
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hstep1 hquarter0) ?_
  -- (3) ¼·((mkPos 4 j)·(C₂·δ²)) ≈ mkPos C₂ (M²·j)  [¼·4 = 1 ; δ² = 1/M²]
  have hMMpos : 0 < M * M := Nat.mul_pos hM hM
  have hMMjpos : 0 < M * M * jdist M k := Nat.mul_pos hMMpos hjpos
  have hLHSeqv : (ChebOrthoLegProof.quarter
        * (Q'.mkPos 4 (jdist M k) (jdist_pos hkn)
          * (Q'.ofNat (C2num e) * (ChebOrthoLegProof.delta M hM * ChebOrthoLegProof.delta M hM))))
      ≈ Q'.mkPos (C2num e : Int) (M * M * jdist M k) hMMjpos := by
    -- compute via cross-mult ; quarter = mkPos 1 4, δ² = mkPos 1 (M·M)
    show (ChebOrthoLegProof.quarter
          * (Q'.mkPos 4 (jdist M k) (jdist_pos hkn)
            * (Q'.ofNat (C2num e) * (ChebOrthoLegProof.delta M hM * ChebOrthoLegProof.delta M hM)))).num
          * ((Q'.mkPos (C2num e : Int) (M * M * jdist M k) hMMjpos).den : Int)
        = (Q'.mkPos (C2num e : Int) (M * M * jdist M k) hMMjpos).num
          * ((ChebOrthoLegProof.quarter
            * (Q'.mkPos 4 (jdist M k) (jdist_pos hkn)
              * (Q'.ofNat (C2num e) * (ChebOrthoLegProof.delta M hM * ChebOrthoLegProof.delta M hM)))).den : Int)
    -- numerators: quarter.num·(4·(C₂·(1·1))) ; deltas num 1
    have hqn : (ChebOrthoLegProof.quarter).num = 1 := by decide
    have hqd : ((ChebOrthoLegProof.quarter).den : Int) = 4 := by decide
    have hdn : (ChebOrthoLegProof.delta M hM).num = 1 := by
      show (Q'.mkPos 1 M hM).num = 1; rw [Q'.mkPos_num]
    have hdd : ((ChebOrthoLegProof.delta M hM).den : Int) = (M : Int) := by
      show ((Q'.mkPos 1 M hM).den : Int) = _; rw [Q'.mkPos_den]
    have hcn : (Q'.ofNat (C2num e)).num = (C2num e : Int) := rfl
    have hcd : ((Q'.ofNat (C2num e)).den : Int) = 1 := rfl
    -- expand all .num/.den
    rw [show (ChebOrthoLegProof.quarter
          * (Q'.mkPos 4 (jdist M k) (jdist_pos hkn)
            * (Q'.ofNat (C2num e) * (ChebOrthoLegProof.delta M hM * ChebOrthoLegProof.delta M hM)))).num
        = (ChebOrthoLegProof.quarter).num * ((Q'.mkPos 4 (jdist M k) (jdist_pos hkn)).num
            * ((Q'.ofNat (C2num e)).num
              * ((ChebOrthoLegProof.delta M hM).num * (ChebOrthoLegProof.delta M hM).num))) from rfl]
    rw [Q'.mul_den_cast, Q'.mul_den_cast, Q'.mul_den_cast, Q'.mul_den_cast,
      Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_num, Q'.mkPos_den,
      hqn, hqd, hdn, hdd, hcn, hcd]
    have hMMj : ((M * M * jdist M k : Nat) : Int)
        = (M : Int) * (M : Int) * (jdist M k : Int) := by push_cast; rfl
    have hjc : ((jdist M k : Nat) : Int) = (jdist M k : Int) := rfl
    rw [hMMj]
    -- (1·(4·(C₂·(1·1))))·(M·M·j) = C₂·(4·(j·(1·(M·M))))
    generalize (C2num e : Int) = C
    generalize (jdist M k : Int) = j
    generalize (M : Int) = m
    simp only [Int.one_mul, Int.mul_one, Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHSeqv) ?_
  -- (4) mkPos C₂ (M²·j) ≤ ¼·gradedRate ≈ mkPos cRateNum (4·(isqrt M·j²))
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv (ChebOrthoLegProof.quarter_gradedRate_eqv e M k hM hkn))
  refine ChebOrthoLegProof.mkPos_le_mkPos _ _ ?_
  -- C₂·(4·(isqrt M·j²)) ≤ cRateNum·(M²·j)
  -- key: 4·C₂·isqrt M·j ≤ cRateNum·M²  (then ·j on both, careful with shapes)
  have hisqM : 4 * C2num e ≤ isqrt M := by
    refine isqrt_ge ?_
    have : M0T e = (4 * C2num e) * (4 * C2num e) := rfl
    omega
  have hsqle : isqrt M * isqrt M ≤ M := isqrt_sq_le M
  have hjM : jdist M k ≤ M := jdist_le_M M k hkn
  have hcn1 : 1 ≤ ChebOrthoMidpointCore.cRateNum e := by
    unfold ChebOrthoMidpointCore.cRateNum; omega
  -- Nat key:  C₂·(4·(isqrt M·(j·j))) ≤ cRateNum·(M·M·j)
  have hkeyNat : C2num e * (4 * (isqrt M * (jdist M k * jdist M k)))
      ≤ ChebOrthoMidpointCore.cRateNum e * (M * M * jdist M k) := by
    -- 4C₂·isqrt M ≤ M  (since 4C₂ ≤ isqrt M and isqrt M·isqrt M ≤ M)
    have h4Cq : 4 * C2num e * isqrt M ≤ isqrt M * isqrt M := Nat.mul_le_mul_right _ hisqM
    have h4CqM : 4 * C2num e * isqrt M ≤ M := Nat.le_trans h4Cq hsqle
    -- LHS = (4C₂·isqrt M)·(j·j) ≤ M·(j·j) ≤ M·(M·j) = M²·j ≤ cRateNum·M²j
    have hLrw : C2num e * (4 * (isqrt M * (jdist M k * jdist M k)))
        = (4 * C2num e * isqrt M) * (jdist M k * jdist M k) := by ac_rfl
    rw [hLrw]
    have hjj : jdist M k * jdist M k ≤ M * jdist M k := Nat.mul_le_mul_right _ hjM
    have hb : (4 * C2num e * isqrt M) * (jdist M k * jdist M k) ≤ M * (M * jdist M k) :=
      Nat.mul_le_mul h4CqM hjj
    have hMMjeq : M * (M * jdist M k) = M * M * jdist M k := by ac_rfl
    have hc : M * M * jdist M k ≤ ChebOrthoMidpointCore.cRateNum e * (M * M * jdist M k) := by
      calc M * M * jdist M k = 1 * (M * M * jdist M k) := (Nat.one_mul _).symm
        _ ≤ ChebOrthoMidpointCore.cRateNum e * (M * M * jdist M k) := Nat.mul_le_mul_right _ hcn1
    refine Nat.le_trans hb ?_
    rw [hMMjeq]; exact hc
  -- cast to Int cross-mult
  show (C2num e : Int) * ((4 * (isqrt M * (jdist M k * jdist M k)) : Nat) : Int)
      ≤ (ChebOrthoMidpointCore.cRateNum e : Int) * ((M * M * jdist M k : Nat) : Int)
  have hLc : (C2num e : Int) * ((4 * (isqrt M * (jdist M k * jdist M k)) : Nat) : Int)
      = ((C2num e * (4 * (isqrt M * (jdist M k * jdist M k))) : Nat) : Int) :=
    (Int.natCast_mul (C2num e) (4 * (isqrt M * (jdist M k * jdist M k)))).symm
  have hRc : (ChebOrthoMidpointCore.cRateNum e : Int) * ((M * M * jdist M k : Nat) : Int)
      = ((ChebOrthoMidpointCore.cRateNum e * (M * M * jdist M k) : Nat) : Int) :=
    (Int.natCast_mul (ChebOrthoMidpointCore.cRateNum e) (M * M * jdist M k)).symm
  rw [hLc, hRc]
  exact Int.ofNat_le.mpr hkeyNat

/-- **T2 vs `¼·gradedRate`.**  `AbsLeRat T2 (¼·gradedRate)` for `M ≥ M0T e`. -/
theorem T2_le_quarter (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) (hj : 2 ≤ jdist M k) (hthr : M0T e ≤ M) :
    AbsLeRat (T2 e he M hM k) (ChebOrthoLegProof.quarter * ChebOrthoGraded.gradedRate e M hM k) :=
  ChebOrthoGradedClose.AbsLeRat.mono (T2_AbsLeRat e he M hM k hk0 hkn hk1n hj)
    (T2bound_le e M k hM hk0 hkn hk1n hj hthr)

/-! ## 5. The radical-leg assembly, reduced to the antisymmetric-rate residual

The T2 (bracket-quadratic-remainder) term closes eventually (`T2_le_quarter`).  The T1
(antisymmetric √-Hölder) term `antisymmTarget = ½B0·Δ₁''` is two-sidedly bounded by the
genuine `antisymmQuot` scale (`antisymmSecondDiff_AbsLeRat`, the crux PROVED result).

ADVERSARIAL FINDING (verified numerically).  The remaining cross-multiplication
`antisymmQuot ≤ ¼·gradedRate` does NOT hold at near-boundary interior cells (e.g.
`k = 1`, so `j = jdist = 2`, `|2k+1−M| ≈ M`) for large `M` under the crude bracket bound
`|B0| ≤ 2`: there `antisymmQuot ~ |2k+1−M| / (M·j³) ~ 1/j³ ~ 1/8`, while
`¼·gradedRate ~ cRateNum / (4·⌊√M⌋·j²) → 0`.  The fix requires a BOUNDARY-DECAY estimate
on the bracket, `|B0| = |B_e(x_k)| ≲ √(1−x_k²) ~ √(j/M)` (the bracket vanishes at `±1`:
e.g. `B_2(−1) = 0`), which is NOT among the available inputs.  Hence the radical leg is
reduced — axiom-clean, PROVED — to the SINGLE named residual below, STRICTLY SMALLER than
`EventualRadLegRemainder` (it drops the T2 term, the leg decomposition, and the antisymm
second-difference reduction, all PROVED, keeping only the antisymmetric-term-vs-rate
cross-mult that genuinely needs the boundary-decay bracket estimate). -/

/-- **NAMED-open: the eventual antisymmetric-term-vs-rate bound.**  There is a threshold
`M₀` such that at every interior cell with `M₀ ≤ N+1`, the antisymmetric √-Hölder term
`T1 = ½·B0·(s_+ − s_-) − LZB` is `≤ ¼·gradedRate`.  GENUINE residual: needs the
boundary-decay bracket bound `|B_e(x_k)| ≲ √(1−x_k²)` (the crude `|B0|≤2` is insufficient
near the boundary — see the adversarial finding above). -/
def EventualAntisymmRate (e : Nat) (he : 0 < e) : Prop :=
  ∃ M₀ : Nat, ∀ N k : Nat, M₀ ≤ N + 1 → 1 ≤ k → k ≤ N - 1 → ∀ hk : k < N + 1,
    ChebOrthoGradedClose.AbsLeRat
      (antisymmTarget e he (N + 1) (Nat.succ_pos N) k hk)
      (ChebOrthoLegProof.quarter * ChebOrthoGraded.gradedRate e (N + 1) (Nat.succ_pos N) k)

/-- `¼·g + ¼·g ≈ ½·g`. -/
private theorem quarter_add_quarter (g : Q') :
    (ChebOrthoLegProof.quarter * g + ChebOrthoLegProof.quarter * g)
      ≈ (ChebOrthoLegAssembly.half * g) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Cheb.add_mul_eqv ChebOrthoLegProof.quarter ChebOrthoLegProof.quarter g)) ?_
  refine Q'.mul_eqv_congr_right _ _ _ ?_
  decide

/-- **THE RADICAL-LEG REDUCTION.**  `EventualAntisymmRate e he → EventualRadLegRemainder e he`.
Assembles the PROVED T2 bound (`T2_le_quarter`, threshold `M0T e`) with the assumed
antisymmetric-term bound, adds them (`¼g + ¼g = ½g`), and transfers back along the PROVED
radical-leg decomposition `rad_decomp` (`legRad + (−LZB) ≈ antisymmTarget + T2`). -/
theorem eventualRadLegRemainder_of_antisymmRate (e : Nat) (he : 0 < e) (he2 : 2 ≤ e)
    (hAnti : EventualAntisymmRate e he) :
    ChebOrthoLegAssembly.EventualRadLegRemainder e he := by
  obtain ⟨M₀A, hA⟩ := hAnti
  refine ⟨max M₀A (M0T e), fun N k hN hk1 hkN hk => ?_⟩
  have hM : 0 < N + 1 := Nat.succ_pos N
  have hk0 : 0 < k := hk1
  have hkn : k < N + 1 := hk
  have hk1n : k + 1 < N + 1 := by omega
  have hj : 2 ≤ jdist (N + 1) k := by
    show 2 ≤ Nat.min (k + 1) ((N + 1) - k)
    exact Nat.le_min.mpr ⟨by omega, by omega⟩
  have hthrA : M₀A ≤ N + 1 := Nat.le_trans (Nat.le_max_left _ _) hN
  have hthrT : M0T e ≤ N + 1 := Nat.le_trans (Nat.le_max_right _ _) hN
  -- the two term bounds
  have hT1 := hA N k hthrA hk1 hkN hk
  have hT2 := T2_le_quarter e he (N + 1) hM k hk0 hkn hk1n hj hthrT
  -- add: AbsLeRat (antisymmTarget + T2) (¼g + ¼g)
  have hadd := ChebOrthoGradedClose.AbsLeRat.add hT1 hT2
  -- collapse ¼g+¼g = ½g
  have hcollapse := ChebOrthoGradedClose.AbsLeRat.mono hadd
    (Q'.le_of_eqv (quarter_add_quarter (ChebOrthoGraded.gradedRate e (N + 1) hM k)))
  -- transfer back along rad_decomp
  exact ChebOrthoCancelDiv.AbsLeRat.of_equiv (rad_decomp e he (N + 1) hM k hk) hcollapse

/-- **NAMED-open (smallest): the eventual antisymmetric-QUOTIENT-vs-rate cross-mult.**
Purely a rational inequality `antisymmQuot ≤ ¼·gradedRate` on the eventual window — the
single arithmetic obligation behind the radical leg.  GENUINE residual: false near the
boundary under `|B0|≤2`; needs the boundary-decay bracket bound `|B_e(x_k)| ≲ √(1−x_k²)`. -/
def EventualAntisymmQuotRate (e : Nat) : Prop :=
  ∃ M₀ : Nat, ∀ N k : Nat, M₀ ≤ N + 1 → 1 ≤ k → k ≤ N - 1 → ∀ hk : k < N + 1,
    ∀ hk0 : 0 < k, ∀ hk1n : k + 1 < N + 1, ∀ hj : 2 ≤ jdist (N + 1) k,
      antisymmQuot (N + 1) k (Nat.succ_pos N) hk hj
        ≤ ChebOrthoLegProof.quarter * ChebOrthoGraded.gradedRate e (N + 1) (Nat.succ_pos N) k

/-- **`EventualAntisymmQuotRate e → EventualAntisymmRate e he`.**  Via the PROVED
two-sided bound `antisymmSecondDiff_AbsLeRat` (`|antisymmTarget| ≤ antisymmQuot`) and
`AbsLeRat.mono`. -/
theorem eventualAntisymmRate_of_quotRate (e : Nat) (he : 0 < e)
    (hQ : EventualAntisymmQuotRate e) : EventualAntisymmRate e he := by
  obtain ⟨M₀, hQ⟩ := hQ
  refine ⟨M₀, fun N k hN hk1 hkN hk => ?_⟩
  have hk0 : 0 < k := hk1
  have hk1n : k + 1 < N + 1 := by omega
  have hj : 2 ≤ jdist (N + 1) k := by
    show 2 ≤ Nat.min (k + 1) ((N + 1) - k)
    exact Nat.le_min.mpr ⟨by omega, by omega⟩
  exact ChebOrthoGradedClose.AbsLeRat.mono
    (antisymmSecondDiff_AbsLeRat e he (N + 1) (Nat.succ_pos N) k hk0 hk hk1n hj)
    (hQ N k hN hk1 hkN hk hk0 hk1n hj)

end YMGap.Continuum.ChebOrthoRadLegProof

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.ChebOrthoRadLegProof.symmSecondDiff_sqrt_AbsLeRat
#print axioms YMGap.Continuum.ChebOrthoRadLegProof.antisymm_numer
#print axioms YMGap.Continuum.ChebOrthoRadLegProof.antisymmSecondDiff_AbsLeRat
#print axioms YMGap.Continuum.ChebOrthoRadLegProof.rad_decomp
#print axioms YMGap.Continuum.ChebOrthoRadLegProof.T2_le_quarter
#print axioms YMGap.Continuum.ChebOrthoRadLegProof.eventualRadLegRemainder_of_antisymmRate
#print axioms YMGap.Continuum.ChebOrthoRadLegProof.eventualAntisymmRate_of_quotRate
