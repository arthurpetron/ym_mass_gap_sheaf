/-
# The sum-side log-derivative limit `S'` as a convergent `CReal`
  (Wall-2 differentiation: the base-`q²` geometric-modulus realisation of the
   log-derivative series `S' = Σ_k σ_k`)

`ThetaDerivDriverClose` proves the θ-free per-factor log-derivative ratio bound
`sigmaRatio_abs_le : |σ_k| ≤ fourAmp q k · (1/(1−q)²)` and its geometric tail
`sigmaTail_le`.  What was still a FREE `CReal` parameter `(c S' : CReal)` at the
product-form residual is the *limit* `S'` of the partial sums
`Spart' M = Σ_{k<M} σ_k`.  This module builds that limit as a genuine `CReal`.

## What is genuinely proved here

* **`Spart'`** — the σ partial sum `Σ_{k<M} σ_k` (a `finSum`; `_succ` is `rfl`).
* **`sigmaRatio_le_geoIncr`** — the single per-term geometric-increment bound
  `|σ_l| ≤ geoIncrBase (Cfour·(1/(1−q)²)) (q²) l`, discharging BOTH the up- and the
  down-step of the increment engine.  Proof: `sigmaRatio_abs_le` chained with
  `fourAmp_le_geo` (times the nonneg constant `1/(1−q)²`) and the constant-pull
  reassociation.
* **`logDerivSumCReal`** — THE deliverable: `S'` as a `CReal` via
  `HKConvGen.crealOfGeoIncrementBase` at base `r = q²`, constant
  `C = Cfour·(1/(1−q)²)`.  `approx M = Spart' M` by `rfl`.
* **`logDerivSumCReal_convergesTo`** — the genuine `ConvergesTo` witness (the
  partial sums, lifted by `ofQ'`, converge to `S'`); one line via
  `CReal.convergesTo_self` since `.approx` is definitionally `Spart'`.

## Honest residual (AGENTS.md Rule 6)

This builds ONLY the sum-side limit `S'`, turning the previously-free
`(c S' : CReal)` parameter into a concrete base-`q²` geometric-modulus `CReal`
(partner of the already-built `Θ = ThetaConvGen.thetaConvCRealGen`).  It does NOT
discharge `DiffJTP`: the driver still needs the product-side comparison
`|P_M − Θ|` (`ThetaConvGen.incr_le_gen`) and the CReal interchange
`P_M·S_M − Θ·S'` (the named `DriverProductResidual`).  Building `S'` is the
precondition that makes that interchange well-typed.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (`Quot.sound` only via reused
`divPos`/`pow`/`finSum`/`num_pos_of_pos` helpers).  No `Classical.*`, no
`native_decide`, no `sorry`.
-/

import YMGap.Continuum.ThetaDerivDriverClose
import YMGap.Continuum.JTPInstance
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.HeatKernelConv
import YMGap.Continuum.HeatKernelPos
import YMGap.Constructive.RegularCRealArith
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.AbsQ
import YMGap.Constructive.RationalTail

namespace YMGap.Continuum.LogDerivSumCReal

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.JTPInstance
open YMGap.Continuum.ThetaDerivDriverClose
open YMGap.Constructive.RationalTail

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The σ partial sum `Spart'` -/

/-- **`Spart'` — the σ partial sum** `Σ_{k<M} σ_k` (mirror of `dPartial`).  The
successor step `Spart' … (M+1) = Spart' … M + σ_M` holds by `rfl` (via
`finSum_succ`). -/
def Spart' {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    {c : Q'} (hc : (-1 : Q') ≤ c) (s : Q') (M : Nat) : Q' :=
  finSum (sigmaRatio hq0 hq1 hc s) M

/-! ## 2. The per-term geometric-increment bound -/

/-- **`sigmaRatio_le_geoIncr` — the single per-term geometric-increment bound.**
For `0 < q < 1`, `−1 ≤ c`, `|s| ≤ 1`, the ratio magnitude is majorised by the
base-`q²` increment `geoIncrBase (Cfour·(1/(1−q)²)) (q²) l`.  Proof:
`sigmaRatio_abs_le` (`|σ_l| ≤ fourAmp q l · (1/(1−q)²)`) then `fourAmp_le_geo`
times the nonneg constant `invSqOneSubQ q`, then the constant-pull reassociation
`(Cfour·(q²)^l)·(1/(1−q)²) ≈ (Cfour·(1/(1−q)²))·(q²)^l`. -/
theorem sigmaRatio_le_geoIncr {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    {c : Q'} (hc : (-1 : Q') ≤ c) {s : Q'} (hs1 : (-1 : Q') ≤ s) (hs2 : s ≤ (1 : Q'))
    (l : Nat) :
    Q'.abs (sigmaRatio hq0 hq1 hc s l)
      ≤ HKConvGen.geoIncrBase (Cfour * invSqOneSubQ q) (q * q) l := by
  refine Q'.le_trans' _ _ _ (sigmaRatio_abs_le hq0 hq1 hc hs1 hs2 l) ?_
  -- fourAmp q l · invSqOneSubQ q ≤ (Cfour·(q²)^l)·invSqOneSubQ q
  have hmul : fourAmp q l * invSqOneSubQ q
      ≤ (Cfour * (q * q) ^ l) * invSqOneSubQ q :=
    Q'.mul_le_mul_of_nonneg_right (fourAmp q l) (Cfour * (q * q) ^ l) (invSqOneSubQ q)
      (fourAmp_le_geo (Q'.le_of_lt hq0) (Q'.le_of_lt hq1) l) (invSqOneSubQ_nonneg q)
  refine Q'.le_trans' _ _ _ hmul ?_
  -- reassociate: (Cfour·(q²)^l)·invSqOneSubQ q ≈ (Cfour·invSqOneSubQ q)·(q²)^l = geoIncrBase …
  show (Cfour * (q * q) ^ l) * invSqOneSubQ q
      ≤ (Cfour * invSqOneSubQ q) * (q * q) ^ l
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv Cfour ((q * q) ^ l) (invSqOneSubQ q)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left Cfour _ _ (Q'.mul_comm_eqv ((q * q) ^ l) (invSqOneSubQ q))) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv Cfour (invSqOneSubQ q) ((q * q) ^ l))

/-! ## 3. THE deliverable: `S'` as a convergent `CReal` -/

/-- **`logDerivSumCReal` — the sum-side log-derivative limit `S'` as a `CReal`.**
For `0 < q < 1`, `−1 ≤ c`, `|s| ≤ 1`, the partial sums `Spart' M = Σ_{k<M} σ_k`
have the two-sided single-step increment bound `|σ_l| ≤ Cfour·(1/(1−q)²)·(q²)^l`
(`sigmaRatio_le_geoIncr`), so the base-`q²` geometric-increment engine
`HKConvGen.crealOfGeoIncrementBase` realises the limit `S'` as a `CReal` with
`approx M = Spart' M`. -/
def logDerivSumCReal {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    {c : Q'} (hc : (-1 : Q') ≤ c) {s : Q'} (hs1 : (-1 : Q') ≤ s) (hs2 : s ≤ (1 : Q')) :
    CReal :=
  HKConvGen.crealOfGeoIncrementBase (Spart' hq0 hq1 hc s) (Cfour * invSqOneSubQ q) (q * q)
    (Q'.mul_nonneg _ _ Cfour_nonneg (invSqOneSubQ_nonneg q))
    (HKPos.q_mul_pos hq0 hq0)
    -- hr1 : q*q < 1  (clone of `sConvCReal_general`)
    (by
      have haa_le_a : q * q ≤ q := by
        refine Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right q 1 q (Q'.le_of_lt hq1) (Q'.le_of_lt hq0)) ?_
        exact Q'.le_of_eqv (Q'.one_mul_eqv q)
      exact HKPos.q_lt_of_le_of_lt haa_le_a hq1)
    -- hup : Spart' (l+1) ≤ Spart' l + geoIncrBase C r l
    (fun l => by
      show Spart' hq0 hq1 hc s l + sigmaRatio hq0 hq1 hc s l
          ≤ Spart' hq0 hq1 hc s l
            + HKConvGen.geoIncrBase (Cfour * invSqOneSubQ q) (q * q) l
      exact Q'.add_le_add_left (Spart' hq0 hq1 hc s l) (sigmaRatio hq0 hq1 hc s l)
        (HKConvGen.geoIncrBase (Cfour * invSqOneSubQ q) (q * q) l)
        (Q'.le_trans' _ _ _ (Q'.le_abs_self (sigmaRatio hq0 hq1 hc s l))
          (sigmaRatio_le_geoIncr hq0 hq1 hc hs1 hs2 l)))
    -- hlo : Spart' l ≤ Spart' (l+1) + geoIncrBase C r l  (via −σ_l ≤ |σ_l|)
    (fun l => by
      show Spart' hq0 hq1 hc s l
          ≤ (Spart' hq0 hq1 hc s l + sigmaRatio hq0 hq1 hc s l)
            + HKConvGen.geoIncrBase (Cfour * invSqOneSubQ q) (q * q) l
      -- −G_l ≤ σ_l
      have hσlo : -(HKConvGen.geoIncrBase (Cfour * invSqOneSubQ q) (q * q) l)
          ≤ sigmaRatio hq0 hq1 hc s l := by
        have hnegσ : -(sigmaRatio hq0 hq1 hc s l)
            ≤ HKConvGen.geoIncrBase (Cfour * invSqOneSubQ q) (q * q) l :=
          Q'.le_trans' _ _ _ (Q'.neg_le_abs (sigmaRatio hq0 hq1 hc s l))
            (sigmaRatio_le_geoIncr hq0 hq1 hc hs1 hs2 l)
        have h2 := Q'.neg_le_neg hnegσ
        exact Q'.le_trans' _ _ _ h2
          (Q'.le_of_eqv (Q'.neg_neg_eqv (sigmaRatio hq0 hq1 hc s l)))
      -- Spart' l ≤ Spart' l + (σ_l + G_l) ≤ (Spart' l + σ_l) + G_l
      refine Q'.le_trans' _ _ _ ?_
        (Q'.le_of_eqv (Q'.eqv_symm
          (Q'.add_assoc_eqv (Spart' hq0 hq1 hc s l) (sigmaRatio hq0 hq1 hc s l)
            (HKConvGen.geoIncrBase (Cfour * invSqOneSubQ q) (q * q) l))))
      refine Q'.add_le_self_of_nonneg (Spart' hq0 hq1 hc s l)
        (sigmaRatio hq0 hq1 hc s l
          + HKConvGen.geoIncrBase (Cfour * invSqOneSubQ q) (q * q) l) ?_
      -- 0 ≤ σ_l + G_l  from −G_l ≤ σ_l
      have h3 : -(HKConvGen.geoIncrBase (Cfour * invSqOneSubQ q) (q * q) l)
            + HKConvGen.geoIncrBase (Cfour * invSqOneSubQ q) (q * q) l
          ≤ sigmaRatio hq0 hq1 hc s l
            + HKConvGen.geoIncrBase (Cfour * invSqOneSubQ q) (q * q) l :=
        Q'.add_le_add_right _ _
          (HKConvGen.geoIncrBase (Cfour * invSqOneSubQ q) (q * q) l) hσlo
      refine Q'.le_trans' _ _ _ ?_ h3
      exact Q'.ge_of_eqv
        (Q'.neg_add_self_eqv (HKConvGen.geoIncrBase (Cfour * invSqOneSubQ q) (q * q) l)))
    -- modulus : clone of `dSeriesCReal` / `sConvCReal_general`
    (fun ε hε => by
      have hInvpos : (0 : Q') < invSqOneSubQ q := by
        unfold invSqOneSubQ
        exact HKConv.divPos_pos (by decide : (0 : Int) < (1 : Q').num)
      have hCIpos : (0 : Q') < Cfour * invSqOneSubQ q :=
        HKPos.q_mul_pos Cfour_pos hInvpos
      have hDpos : (0 : Q') < HKConv.divPos 1 (1 + (-(q * q))) :=
        HKConv.divPos_pos (by decide : (0 : Int) < (1 : Q').num)
      have hKpos : 0 < ((Cfour * invSqOneSubQ q)
          * HKConv.divPos 1 (1 + (-(q * q)))).num :=
        CReal.num_pos_of_pos (HKPos.q_mul_pos hCIpos hDpos)
      refine ⟨HKConv.divPos ε
          ((Cfour * invSqOneSubQ q) * HKConv.divPos 1 (1 + (-(q * q)))),
        HKConv.divPos_pos (CReal.num_pos_of_pos hε), ?_⟩
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
      exact HKConv.divPos_mul_eqv hKpos)

/-- `approx M = Spart' M` (definitional). -/
@[simp] theorem logDerivSumCReal_approx {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    {c : Q'} (hc : (-1 : Q') ≤ c) {s : Q'} (hs1 : (-1 : Q') ≤ s) (hs2 : s ≤ (1 : Q'))
    (M : Nat) :
    (logDerivSumCReal hq0 hq1 hc hs1 hs2).approx M = Spart' hq0 hq1 hc s M := rfl

/-! ## 4. The genuine `ConvergesTo` witness -/

/-- **`logDerivSumCReal_convergesTo` — the partial sums converge to `S'`.**  The
lifted partial-sum sequence `fun M => ofQ' (Spart' M)` converges to
`logDerivSumCReal`.  One line: `.approx M` is definitionally `Spart' M`, so the
two sequences are equal and `CReal.convergesTo_self` applies. -/
theorem logDerivSumCReal_convergesTo {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    {c : Q'} (hc : (-1 : Q') ≤ c) {s : Q'} (hs1 : (-1 : Q') ≤ s) (hs2 : s ≤ (1 : Q')) :
    CReal.ConvergesTo (fun M => CReal.ofQ' (Spart' hq0 hq1 hc s M))
      (logDerivSumCReal hq0 hq1 hc hs1 hs2) :=
  CReal.convergesTo_self (logDerivSumCReal hq0 hq1 hc hs1 hs2)

end YMGap.Continuum.LogDerivSumCReal

#print axioms YMGap.Continuum.LogDerivSumCReal.logDerivSumCReal
#print axioms YMGap.Continuum.LogDerivSumCReal.logDerivSumCReal_convergesTo
