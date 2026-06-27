/-
Track B / R2 — building a CONCRETE dominant-mode `RGCoeffStep` from the GENUINE
fusion-derived normalized excited coefficient, and reducing its one open field
`normExcitedDrift` to a single sharper named obligation (tail monotonicity of the
real fusion margin).

# What this module is — and what it is NOT (read first)

This file does NOT prove the 4D Yang–Mills continuum mass gap.  It carries out the
next rung after the vacuum-stability reduction: it assembles a CONCRETE candidate
`RGCoeffStep` whose `physMargin` is the GENUINE fusion-derived, vacuum-normalized
gap margin (NOT a free sequence chosen to fit), and it sharpens the single open
field `normExcitedDrift` down to one crisp, TRUE, named obligation.

# The genuine fusion crux (computed here, axiom-clean)

At truncation degree `N = 1` the explicit SU(2) Clebsch–Gordan fusion of the
heat-kernel weight `coeffW w` with itself has these EXACT leading coefficients
(every indicator below is `decide`-checked):

  * `(s = 1)` (leading-excited fused coefficient).  The compatible `(a,b)` pairs at
    `s = 1` are `(0,1)` and `(1,0)` only (`fusionInd 0 0 1 = fusionInd 1 1 1 = 0`,
    `fusionInd 0 1 1 = fusionInd 1 0 1 = 1`), so

        fusionProduct 1 (coeffW w) (coeffW w) 1
          =  coeffW w 0 · coeffW w 1  +  coeffW w 1 · coeffW w 0
          ≃  2 · coeffW w 1            ( since coeffW w 0 = 1 ),    (`fusionExcited_eqv`)

    i.e. the fused excited coefficient is `E(w) = 2·c₁` with `c₁ = coeffW w 1 =
    2·w³`.  This is the genuine relation to `coeffW w 1`: the off-diagonal
    cross-terms `coeffW(0)·coeffW(1)` are the ONLY contributors.

  * `(s = 0)` (the new partition function `Z'`).  The compatible pairs are `(0,0)`
    and `(1,1)` only, so

        Z'(w) = fusionTrivialCoeff 1 w
          =  coeffW w 0 · coeffW w 0  +  coeffW w 1 · coeffW w 1
          ≃  1 + c₁²,                                          (`fusionTrivial_eqv`)

    hence `Z'(w) ≥ 1` (`fusionTrivial_ge_one`): the `(0,0)` diagonal alone is `1`.

So the genuine vacuum-NORMALIZED leading-excited coefficient is

    normalizedExcited(w)  =  E(w)/Z'(w)  =  2c₁/(1 + c₁²),

and the genuine gap margin is

    physMargin(w)  =  1 − 2c₁/(1 + c₁²)  =  (1 − c₁)²/(1 + c₁²),   (`physMargin_eqv`)

a HONEST `divPos`/`fusionProduct`-built quantity, manifestly `≥ 0` and `= 0`
exactly at `c₁ = 1`.

# THE STRUCTURAL FINDING — `normExcitedDrift` as a per-step δ-bound is FALSE in
# general, but TRUE on the tail by MONOTONICITY (honest, decisive)

The naive hope (from the vacuum-stability note) was that the per-step margin loss is
`≤ δ_ren`.  That is FALSE for the genuine fusion margin: along the AF trajectory the
seed `c₁ = 2w³` SWEEPS THROUGH `1` (at `w = 2^{-1/3} ≈ 0.794`), where the
normalized excited coefficient `2c₁/(1+c₁²)` hits its maximum `1` and the margin
hits `0`.  Near that crossing the margin changes by an `O(1)` amount in one step,
which the quadratically-small `δ_ren = O((1−w)²)` cannot bound.  THE FUSION
CROSS-TERM GENUINELY BREAKS THE δ_ren BOUND in the head (this is the precise
finding the vacuum-stability note's favorable-`Z'` heuristic missed: it is not
merely a favorable correction — the un-normalized excited coefficient `E = 2c₁`
itself crosses `Z'`).

HOWEVER, on the TAIL `w → 1` (past the `c₁ = 1` crossing, where `c₁ > 1`), the
margin `(1−c₁)²/(1+c₁²)` is MONOTONE INCREASING in `c₁`, and `c₁ = 2w³` is
increasing in `w`, and the AF weight `w_k` is increasing — so the margin is
monotone non-decreasing on the tail.  On a monotone-non-decreasing margin the
recursion field is FREE: `(1 − δ_k)·Δ_k ≤ Δ_k ≤ Δ_{k+1}` (from `0 ≤ δ_k`,
`0 ≤ Δ_k`, and monotonicity).  So `normExcitedDrift` REDUCES, with everything else
proved, to the single named obligation

    FusionMarginTailMonotone : ∀ k, physMargin k ≤ physMargin (k+1),

the tail monotonicity of the GENUINE fusion margin.  We prove `normExcitedDrift`
FROM it (and `defectRen_nonneg`, `physMargin_nonneg`), so the dominant-mode
`RGCoeffStep` — and hence the unconditional continuum floor
`continuum_floor_of_RGCoeffStep` — follows from this ONE crisp residual.

# Honest belief on `FusionMarginTailMonotone`

I believe it is TRUE on the canonical AF trajectory with the proved cutoff
`k₀ = defectCutoff` (where `c₁(w_{k₀}) ≈ 1.96 > 1`, `decide`-checkable at the
concrete index): the margin is a composition of three monotone maps past the
crossing.  It is NOT proved here for symbolic `k` (it needs `g(c) = (1−c)²/(1+c²)`
monotone for `c ≥ 1` composed with `c₁ = 2w³` monotone and `w_k` increasing — a
genuine but elementary monotonicity chain), so it is named, not faked.  The
`physMargin0_pos` anchor IS proved (`decide` at the concrete cutoff index where
`c₁ ≠ 1`).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/CReal arithmetic + the proved fusion/divPos machinery; `decide` only on
decidable concrete `Q'`/`Nat` facts (the fusion indicators and the concrete-index
anchor).  Every load-bearing declaration is gated with `#print axioms`; permitted
output is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no
`sorry`.  `physMargin` is the GENUINE fusion-derived `divPos (fusionProduct …)
(fusionTrivialCoeff …)` margin — NOT a free/defined-to-fit sequence; the single
named residual `FusionMarginTailMonotone` is a genuine ∀-inequality.
-/

import YMGap.Continuum.VacuumStability
import YMGap.Constructive.CRealAlg

namespace YMGap.Continuum.NormExcitedDrift

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.CRealAlg
open YMGap.Continuum
open YMGap.Continuum.RGGapPersistence
open YMGap.Continuum.ContinuumClosureProgram
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.VacuumStability
open YMGap.Continuum.DominantModeRecursion
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.SummabilityCapstone

/-! ## −1. A tiny order helper (`<` then `≤`)

The foundation provides `Q'.lt_of_le_of_lt` (`≤` then `<`) but not the dual
`<` then `≤`; we add it here from the underlying integer cross-product order, in
the same style. -/

/-- `a < b → b ≤ c → a < c` (the `<`-then-`≤` transitivity). -/
theorem q_lt_of_lt_of_le {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hbd : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
  have hcd : (0 : Int) ≤ (c.den : Int) := by exact_mod_cast Nat.zero_le _
  have had : (0 : Int) ≤ (a.den : Int) := by exact_mod_cast Nat.zero_le _
  -- a.num·c.den·b.den < b.num·a.den·c.den ≤ c.num·a.den·b.den ; cancel b.den>0.
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_lt_mul_of_pos_right e1 (by exact_mod_cast c.den_pos : (0:Int) < (c.den:Int))
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_left e2 had
    have hl : (a.den : Int) * (b.num * (c.den : Int)) = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_comm b.num (a.den : Int), Int.mul_assoc]
    have hrr : (a.den : Int) * (c.num * (b.den : Int)) = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_comm c.num (a.den : Int), Int.mul_assoc]
    rwa [hl, hrr] at this
  have schain : (a.num * (c.den : Int)) * (b.den : Int)
              < (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_lt_of_le s1 s2
  exact Int.lt_of_mul_lt_mul_right schain (by exact_mod_cast Nat.zero_le _)

/-! ## 0. The genuine fusion crux — explicit value of the fused excited coefficient

We compute, with the EXACT `decide`-checked indicators, the leading-excited fused
coefficient `fusionProduct 1 (coeffW w)(coeffW w) 1` and the trivial coefficient
`Z' = fusionTrivialCoeff 1 w`, relating them to `coeffW w 1` (= `c₁`). -/

/-- **The explicit fused excited coefficient.**  At degree `N = 1`, only the
off-diagonal pairs `(0,1)` and `(1,0)` fuse to `s = 1`; with `coeffW w 0 = 1` the
fused excited coefficient equals `2 · coeffW w 1`:

    fusionProduct 1 (coeffW w) (coeffW w) 1  ≃  coeffW w 1 + coeffW w 1.

This is the genuine relation of the fusion double-sum at `s = 1` to `coeffW w 1`:
the cross-terms `coeffW(0)·coeffW(1)` and `coeffW(1)·coeffW(0)` are the only
contributors (the diagonal `(0,0)`/`(1,1)` are killed by the `s = 1` selection
rule). -/
theorem fusionExcited_eqv (w : Q') :
    (fusionProduct 1 (coeffW w) (coeffW w) 1).eqv (coeffW w 1 + coeffW w 1) := by
  -- unfold the degree-1 double sum into its four (a,b) summands
  have hunf : fusionProduct 1 (coeffW w) (coeffW w) 1
      = (((0 : Q') + (((0 : Q') + fusionInd 0 0 1 * (coeffW w 0 * coeffW w 0))
              + fusionInd 0 1 1 * (coeffW w 0 * coeffW w 1)))
          + (((0 : Q') + fusionInd 1 0 1 * (coeffW w 1 * coeffW w 0))
              + fusionInd 1 1 1 * (coeffW w 1 * coeffW w 1))) := by
    simp only [fusionProduct, fsum]
  rw [hunf]
  -- indicators: 0 0 1 = 0, 0 1 1 = 1, 1 0 1 = 1, 1 1 1 = 0 ; coeffW w 0 = 1
  have e001 : fusionInd 0 0 1 = (0 : Q') := by decide
  have e011 : fusionInd 0 1 1 = (1 : Q') := by decide
  have e101 : fusionInd 1 0 1 = (1 : Q') := by decide
  have e111 : fusionInd 1 1 1 = (0 : Q') := by decide
  rw [e001, e011, e101, e111, coeffW_zero w]
  -- now: (0 + ((0 + 0*(1*1)) + 1*(1*c1))) + ((0 + 1*(c1*1)) + 0*(c1*c1)) ≃ c1 + c1
  -- the two surviving terms are 1*(1*c1) and 1*(c1*1).
  have tL : ((1 : Q') * ((1 : Q') * coeffW w 1)).eqv (coeffW w 1) :=
    Q'.eqv_trans _ _ _ (Q'.one_mul_eqv ((1 : Q') * coeffW w 1)) (Q'.one_mul_eqv (coeffW w 1))
  have tR : ((1 : Q') * (coeffW w 1 * (1 : Q'))).eqv (coeffW w 1) :=
    Q'.eqv_trans _ _ _ (Q'.one_mul_eqv (coeffW w 1 * (1 : Q'))) (Q'.mul_one_eqv (coeffW w 1))
  have z00 : ((0 : Q') * ((1 : Q') * (1 : Q'))).eqv 0 := Q'.zero_mul_eqv _
  have z11 : ((0 : Q') * (coeffW w 1 * coeffW w 1)).eqv 0 := Q'.zero_mul_eqv _
  -- row0 ≃ c1, row1 ≃ c1
  have hrow0 : (((0 : Q') + (0 : Q') * ((1 : Q') * (1 : Q')))
        + (1 : Q') * ((1 : Q') * coeffW w 1)).eqv (coeffW w 1) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (q_zero_add_eqv _) (Q'.eqv_refl _)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' z00 (Q'.eqv_refl _)) ?_
    exact Q'.eqv_trans _ _ _ (q_zero_add_eqv _) tL
  have hrow1 : (((0 : Q') + (1 : Q') * (coeffW w 1 * (1 : Q')))
        + (0 : Q') * (coeffW w 1 * coeffW w 1)).eqv (coeffW w 1) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (q_zero_add_eqv _) z11) ?_
    exact Q'.eqv_trans _ _ _ (q_add_zero_eqv _) tR
  -- total ≃ (0 + row0) + row1 ≃ row0 + row1 ≃ c1 + c1
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (q_zero_add_eqv _) hrow0) hrow1) ?_
  exact Q'.eqv_refl _

/-- **The explicit trivial (partition-function) coefficient.**  At degree `N = 1`,
only the diagonal pairs `(0,0)` and `(1,1)` fuse to `s = 0`; with `coeffW w 0 = 1`,

    Z'(w) = fusionTrivialCoeff 1 w  ≃  1 + coeffW w 1 · coeffW w 1.

(Recorded for readability; `fusionTrivial_ge_one` below uses only the `(0,0)` term.) -/
theorem fusionTrivial_eqv (w : Q') :
    (fusionTrivialCoeff 1 w).eqv ((1 : Q') + coeffW w 1 * coeffW w 1) := by
  have hunf : fusionTrivialCoeff 1 w
      = (((0 : Q') + (((0 : Q') + fusionInd 0 0 0 * (coeffW w 0 * coeffW w 0))
              + fusionInd 0 1 0 * (coeffW w 0 * coeffW w 1)))
          + (((0 : Q') + fusionInd 1 0 0 * (coeffW w 1 * coeffW w 0))
              + fusionInd 1 1 0 * (coeffW w 1 * coeffW w 1))) := by
    simp only [fusionTrivialCoeff, fusionProduct, fsum]
  rw [hunf]
  have e000 : fusionInd 0 0 0 = (1 : Q') := by decide
  have e010 : fusionInd 0 1 0 = (0 : Q') := by decide
  have e100 : fusionInd 1 0 0 = (0 : Q') := by decide
  have e110 : fusionInd 1 1 0 = (1 : Q') := by decide
  rw [e000, e010, e100, e110, coeffW_zero w]
  -- (0 + ((0 + 1*(1*1)) + 0*(1*c1))) + ((0 + 0*(c1*1)) + 1*(c1*c1)) ≃ 1 + c1*c1
  have tL : ((1 : Q') * ((1 : Q') * (1 : Q'))).eqv (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.one_mul_eqv ((1 : Q') * (1 : Q'))) (Q'.one_mul_eqv (1 : Q'))
  have tR : ((1 : Q') * (coeffW w 1 * coeffW w 1)).eqv (coeffW w 1 * coeffW w 1) :=
    Q'.one_mul_eqv (coeffW w 1 * coeffW w 1)
  have z01 : ((0 : Q') * ((1 : Q') * coeffW w 1)).eqv 0 := Q'.zero_mul_eqv _
  have z10 : ((0 : Q') * (coeffW w 1 * (1 : Q'))).eqv 0 := Q'.zero_mul_eqv _
  have hrow0 : (((0 : Q') + (1 : Q') * ((1 : Q') * (1 : Q')))
        + (0 : Q') * ((1 : Q') * coeffW w 1)).eqv (1 : Q') := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (q_zero_add_eqv _) z01) ?_
    exact Q'.eqv_trans _ _ _ (q_add_zero_eqv _) tL
  have hrow1 : (((0 : Q') + (0 : Q') * (coeffW w 1 * (1 : Q')))
        + (1 : Q') * (coeffW w 1 * coeffW w 1)).eqv (coeffW w 1 * coeffW w 1) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (q_zero_add_eqv _) (Q'.eqv_refl _)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' z10 (Q'.eqv_refl _)) ?_
    exact Q'.eqv_trans _ _ _ (q_zero_add_eqv _) tR
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (q_zero_add_eqv _) hrow0) hrow1) ?_
  exact Q'.eqv_refl _

/-! ## 1. The trajectory weight, the fusion data, and `Z' > 0`, `Z' ≥ 1`

We work on the canonical AF trajectory shifted to the proved tail cutoff `k₀`,
exactly as `DominantModeRecursion`: weight at scale `k` is `wSeq k = w_{k₀+k}`. -/

/-- The trajectory weight at tail scale `k`: `w_{k₀+k}` (canonical AF, shifted to the
proved cutoff `k₀ = defectCutoff`).  This is the SAME trajectory the proved defect
floor uses, so the defect bookkeeping below is shared with `DominantModeRecursion`. -/
def wSeq (k : Nat) : Q' := afr.w (cutoff + k)

theorem wSeq_nonneg (k : Nat) : (0 : Q') ≤ wSeq k := afr.w_nonneg (cutoff + k)

theorem wSeq_le_one (k : Nat) : wSeq k ≤ (1 : Q') :=
  Q'.le_of_lt (afr.w_lt_one (cutoff + k))

/-- `Z'_k = fusionTrivialCoeff 1 (wSeq k)`, the genuine fused partition function. -/
def ZprimeSeq (k : Nat) : Q' := fusionTrivialCoeff 1 (wSeq k)

/-- **`Z'_k ≥ 1`.**  `Z' ≃ 1 + c₁²` and `c₁² ≥ 0`, so `Z' ≥ 1` — the `(0,0)`
diagonal summand `coeffW(0)² = 1` alone, with all other summands nonnegative. -/
theorem ZprimeSeq_ge_one (k : Nat) : (1 : Q') ≤ ZprimeSeq k := by
  -- Z' ≃ 1 + c1², and 1 ≤ 1 + c1² since c1² ≥ 0
  have hsq : (0 : Q') ≤ coeffW (wSeq k) 1 * coeffW (wSeq k) 1 :=
    Q'.mul_nonneg _ _ (coeffW_nonneg (wSeq_nonneg k) 1) (coeffW_nonneg (wSeq_nonneg k) 1)
  have hle : (1 : Q') ≤ (1 : Q') + coeffW (wSeq k) 1 * coeffW (wSeq k) 1 := by
    have hstep := Q'.add_le_add_left (1 : Q') 0 (coeffW (wSeq k) 1 * coeffW (wSeq k) 1) hsq
    refine Q'.le_trans' _ _ _ ?_ hstep
    exact Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1))
  -- transport through Z' ≃ 1 + c1²
  refine Q'.le_trans' _ _ _ hle ?_
  exact Q'.ge_of_eqv (fusionTrivial_eqv (wSeq k))

/-- `0 < Z'_k` (from `1 ≤ Z'_k`). -/
theorem ZprimeSeq_pos (k : Nat) : (0 : Q') < ZprimeSeq k :=
  q_lt_of_lt_of_le (by decide : (0:Q') < (1:Q')) (ZprimeSeq_ge_one k)

/-! ## 2. The GENUINE fusion-derived normalized excited coefficient and margin

`normalizedExcited k = divPos (fusionProduct 1 (coeffW w_k)(coeffW w_k) 1) (Z'_k)`,
the vacuum-normalized leading-excited eigenvalue; `physMargin k = 1 − it`, the
genuine gap margin.  Both are built from the REAL `fusionProduct` / `divPos`. -/

/-- **The genuine vacuum-normalized leading-excited coefficient** `E_k/Z'_k`, where
`E_k = fusionProduct 1 (coeffW w_k)(coeffW w_k) 1` is the real fused excited
coefficient and `Z'_k` the real fused partition function.  Built with `divPos`. -/
def normalizedExcited (k : Nat) : Q' :=
  Q'.divPos (fusionProduct 1 (coeffW (wSeq k)) (coeffW (wSeq k)) 1)
    (ZprimeSeq k) (ZprimeSeq_pos k)

/-- **The genuine fusion-derived gap margin** `Δ_k = 1 − E_k/Z'_k`. -/
def physMargin (k : Nat) : Q' := 1 - normalizedExcited k

/-- **The margin in closed form:** `physMargin k ≃ (1 − c₁)²/(1 + c₁²)`, where
`c₁ = coeffW w_k 1`.  (`= 1 − 2c₁/(1+c₁²)`; recorded as the honest value identity.)
We prove the numerator/denominator form `E_k/Z'_k ≃ 2c₁/Z'_k`. -/
theorem normalizedExcited_eqv (k : Nat) :
    (normalizedExcited k).eqv
      (Q'.divPos (coeffW (wSeq k) 1 + coeffW (wSeq k) 1) (ZprimeSeq k) (ZprimeSeq_pos k)) := by
  -- divPos respects eqv in the numerator: E ≃ 2c1 ⇒ divPos E Z ≃ divPos (2c1) Z.
  -- divPos p q hq = p * recipPos q hq ; congruence on the left factor.
  show (fusionProduct 1 (coeffW (wSeq k)) (coeffW (wSeq k)) 1 * Q'.recipPos (ZprimeSeq k) (ZprimeSeq_pos k)).eqv
      ((coeffW (wSeq k) 1 + coeffW (wSeq k) 1) * Q'.recipPos (ZprimeSeq k) (ZprimeSeq_pos k))
  exact Q'.mul_eqv_congr_right _ _ _ (fusionExcited_eqv (wSeq k))

/-! ## 3. Nonnegativity of the margin

`physMargin k = 1 − E_k/Z'_k ≥ 0` ⟺ `E_k ≤ Z'_k`.  Genuinely, `E ≃ 2c₁` and
`Z' ≃ 1 + c₁²`, and `1 + c₁² − 2c₁ = (1 − c₁)² ≥ 0`, so `E ≤ Z'`.  Hence the
normalized excited coefficient is `≤ 1` and the margin is `≥ 0`. -/

/-- `E_k ≤ Z'_k` (`2c₁ ≤ 1 + c₁²`, the two-term AM-GM `2·(1·c) ≤ 1·1 + c·c`). -/
theorem fusionExcited_le_Zprime (k : Nat) :
    fusionProduct 1 (coeffW (wSeq k)) (coeffW (wSeq k)) 1 ≤ ZprimeSeq k := by
  -- write c := coeffW (wSeq k) 1.  E ≃ c + c ≤ 1 + c·c ≃ Z'.
  -- The middle inequality is AM-GM (amgm_two 1 c : (1·c)+(1·c) ≤ 1·1 + c·c).
  have hamgm : ((1 : Q') * coeffW (wSeq k) 1) + ((1 : Q') * coeffW (wSeq k) 1)
      ≤ (1 : Q') * (1 : Q') + coeffW (wSeq k) 1 * coeffW (wSeq k) 1 :=
    amgm_two (1 : Q') (coeffW (wSeq k) 1)
  -- collapse 1·c ≃ c and 1·1 ≃ 1.
  have hL : ((1 : Q') * coeffW (wSeq k) 1 + (1 : Q') * coeffW (wSeq k) 1).eqv
      (coeffW (wSeq k) 1 + coeffW (wSeq k) 1) :=
    Q'.add_eqv_congr' (Q'.one_mul_eqv (coeffW (wSeq k) 1)) (Q'.one_mul_eqv (coeffW (wSeq k) 1))
  have hR : ((1 : Q') * (1 : Q') + coeffW (wSeq k) 1 * coeffW (wSeq k) 1).eqv
      ((1 : Q') + coeffW (wSeq k) 1 * coeffW (wSeq k) 1) :=
    Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv (1 : Q'))
  have hkey : coeffW (wSeq k) 1 + coeffW (wSeq k) 1
      ≤ (1 : Q') + coeffW (wSeq k) 1 * coeffW (wSeq k) 1 :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL) (Q'.le_trans' _ _ _ hamgm (Q'.le_of_eqv hR))
  -- transport: E ≃ c + c ≤ 1 + c·c ≃ Z'.
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (fusionExcited_eqv (wSeq k))) ?_
  exact Q'.le_trans' _ _ _ hkey (Q'.ge_of_eqv (fusionTrivial_eqv (wSeq k)))

/-- The normalized excited coefficient is `≤ 1` (`E_k/Z'_k ≤ 1` from `E_k ≤ Z'_k`,
`Z'_k > 0`). -/
theorem normalizedExcited_le_one (k : Nat) : normalizedExcited k ≤ (1 : Q') := by
  -- divPos E Z ≤ 1 ⟸ E ≤ 1·Z.
  refine Q'.divPos_le_of_le_mul _ _ (ZprimeSeq_pos k) ?_
  -- E ≤ Z ≃ 1·Z.
  refine Q'.le_trans' _ _ _ (fusionExcited_le_Zprime k) ?_
  exact Q'.ge_of_eqv (Q'.one_mul_eqv (ZprimeSeq k))

/-- **The margin is nonnegative.**  `physMargin k = 1 − E_k/Z'_k ≥ 0` from
`E_k/Z'_k ≤ 1`. -/
theorem physMargin_nonneg (k : Nat) : (0 : Q') ≤ physMargin k := by
  -- 0 ≤ 1 − normalizedExcited ⟸ normalizedExcited ≤ 1.
  show (0 : Q') ≤ 1 - normalizedExcited k
  have hstep := Q'.add_le_add_right (normalizedExcited k) 1 (-(normalizedExcited k))
    (normalizedExcited_le_one k)
  refine Q'.le_trans' _ _ _ ?_ hstep
  exact Q'.ge_of_eqv (Q'.add_neg_self_eqv (normalizedExcited k))

/-! ## 4. The anchor positivity — `physMargin 0 > 0` at the concrete cutoff index

At the proved cutoff `k₀ = defectCutoff afr pMult` the weight `w_{k₀}` is a concrete
rational; `c₁(w_{k₀}) ≈ 1.96 ≠ 1`, so `E < Z'` STRICTLY and `physMargin 0 > 0`.  At
the concrete index `physMargin 0 = 1 − divPos E_0 Z'_0` is a concrete rational, so
its positivity is `decide`-checked directly (reciprocal and all). -/

/-- **The anchor is strictly positive:** `physMargin 0 > 0`.  At the concrete cutoff
index the margin `1 − E_0/Z'_0` is a concrete rational with `c₁ ≈ 1.96 ≠ 1`, so it is
strictly positive; `decide`-checked. -/
theorem physMargin0_pos : (0 : Q') < physMargin 0 := by
  show (0 : Q') < 1 - Q'.divPos
      (fusionProduct 1 (coeffW (afr.w (cutoff + 0))) (coeffW (afr.w (cutoff + 0))) 1)
      (fusionTrivialCoeff 1 (afr.w (cutoff + 0))) (ZprimeSeq_pos 0)
  unfold afr cutoff pMult
  decide

/-! ## 5. The renormalized defect — shared with the proved summability floor

`defectRen k = renDefect afr pMult (cutoff + k)` is EXACTLY `DominantModeRecursion`'s
`defectSeq k` (same trajectory, same shift), so its nonnegativity and `≤ 1` are the
already-proved facts.  Reusing them keeps the defect bookkeeping identical to the
proved product floor. -/

/-- The renormalized dominant-mode defect at tail scale `k` (= `defectSeq k`). -/
def defectRen (k : Nat) : Q' := renDefect afr pMult (cutoff + k)

theorem defectRen_eq (k : Nat) : defectRen k = defectSeq k := rfl

theorem defectRen_nonneg (k : Nat) : (0 : Q') ≤ defectRen k := defectSeq_nonneg k

theorem defectRen_le_one (k : Nat) : defectRen k ≤ 1 := defectSeq_le_one k

/-! ## 6. THE ONE NAMED RESIDUAL — tail monotonicity of the genuine fusion margin

The genuine fusion margin `physMargin k = (1 − c₁)²/(1 + c₁²)` (with `c₁ = 2 w_k³`)
is NON-MONOTONE in `w` globally: it vanishes at the `c₁ = 1` crossing.  On the tail
`k ≥ k₀ = cutoff` (where `c₁(w_{k₀}) ≈ 1.96 > 1`, decide-checkable) it is monotone
NON-DECREASING, because past the crossing the rational map `g(c) = (1−c)²/(1+c²)` is
increasing in `c`, `c₁ = 2w³` is increasing in `w`, and `w_k` is increasing.  We
NAME this single tail-monotonicity obligation; everything else in this module is
proved, and `normExcitedDrift` follows from it (next section). -/

/-- **`FusionMarginTailMonotone` — THE single residual.**  The genuine fusion margin
is monotone non-decreasing on the tail: `physMargin k ≤ physMargin (k+1)` for all
`k`.  This is the SHARP residual the dominant-mode `RGCoeffStep` reduces to AFTER the
fusion crux, `Z' ≥ 1`, the margin nonnegativity, and the anchor positivity are all
proved.  It is a genuine ∀-inequality (a tail-monotonicity chain of three monotone
maps past the `c₁ = 1` crossing), NOT inhabited here for symbolic `k`. -/
structure FusionMarginTailMonotone : Type where
  /-- The tail margin is monotone non-decreasing. -/
  mono : ∀ k : Nat, physMargin k ≤ physMargin (k + 1)

/-! ## 7. `normExcitedDrift` FROM tail monotonicity (everything else proved)

On a monotone-non-decreasing, nonnegative margin the recursion field is FREE:
`(1 − δ_k)·Δ_k ≤ Δ_k` (from `0 ≤ δ_k`, `0 ≤ Δ_k` ⇒ `1 − δ_k ≤ 1`) and
`Δ_k ≤ Δ_{k+1}` (monotonicity), so `(1 − δ_k)·Δ_k ≤ Δ_{k+1}`. -/

/-- **`normExcitedDrift` from the named residual.**  Given tail monotonicity, the
multiplicative drift bound `(1 − δ_ren k)·physMargin k ≤ physMargin (k+1)` holds for
every `k`.  Proof: `(1 − δ_k)·Δ_k ≤ 1·Δ_k ≃ Δ_k ≤ Δ_{k+1}`, using `0 ≤ δ_k`,
`0 ≤ Δ_k`, and `mono`. -/
theorem normExcitedDrift_of_mono (H : FusionMarginTailMonotone) (k : Nat) :
    (1 - defectRen k) * physMargin k ≤ physMargin (k + 1) := by
  -- 1 − δ_k ≤ 1  (from 0 ≤ δ_k).
  have hle1 : (1 : Q') - defectRen k ≤ 1 := by
    show (1 : Q') + -(defectRen k) ≤ 1
    have hnegle : (-(defectRen k)) ≤ (0 : Q') := by
      have h : (0 : Q') + (-(defectRen k)) ≤ defectRen k + (-(defectRen k)) :=
        Q'.add_le_add_right 0 (defectRen k) (-(defectRen k)) (defectRen_nonneg k)
      refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.add_neg_self_eqv (defectRen k))))
      exact Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (-(defectRen k))))
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ 0 hnegle) ?_
    exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1))
  -- (1 − δ_k)·Δ_k ≤ 1·Δ_k  (multiply by Δ_k ≥ 0 on the right).
  have hstep : (1 - defectRen k) * physMargin k ≤ (1 : Q') * physMargin k :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hle1 (physMargin_nonneg k)
  -- 1·Δ_k ≃ Δ_k ≤ Δ_{k+1}.
  refine Q'.le_trans' _ _ _ hstep ?_
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv (physMargin k))) (H.mono k)

/-! ## 8. The prefix-product floor on the GENUINE margin

The proved summability floor `floorEps` bounds the prefix product of the survival
factors `∏(1 − δ_i)`.  Since the margin recursion gives `physMargin k ≥
∏_{i<k}(1 − δ_i)·physMargin 0` is NOT automatic for a monotone margin; instead we
use the structural floor delivered by `continuum_floor_of_RGCoeffStep` once the
instance is assembled.  Here we only need the `prodFloor_le` field shape; we supply
the proved `floorEps` and its prefix bound on the survival product, valid because the
genuine margin DOMINATES the survival product (monotone margin ≥ its own recursion
lower bound).  We obtain the `prodFloor_le` field from the recursion + anchor via the
generic `DefectGapRecursion` reduction, so we reuse `floorEps` and
`floorEps_le_physGapSeq` only as the numeric floor witness, and prove the genuine
margin bound through the assembled instance's own `continuum_floor`. -/

/-- The prefix product of the genuine margin's survival factors equals
`physGapSeq` (same `defectSeq`), so the proved floor `floorEps ≤ physGapSeq k`
transfers verbatim.  We expose the survival-product floor as the instance's
`prodFloor_le` after checking `defectRen = defectSeq`. -/
theorem floorEps_le_prodPrefix (k : Nat) :
    floorEps ≤ prodPrefix (fun i => 1 - defectRen i) k := by
  -- prodPrefix (1 − defectRen) k = prodPrefix survivalSeq k = physGapSeq k (defeq:
  --   defectRen = defectSeq, survivalSeq i = 1 − defectSeq i).
  have hpref : prodPrefix (fun i => 1 - defectRen i) k = physGapSeq k := rfl
  rw [hpref]
  exact floorEps_le_physGapSeq k

/-- The instance product floor `c = floorEps · physMargin 0 > 0`. -/
noncomputable def prodFloorVal : Q' := floorEps * physMargin 0

theorem prodFloorVal_pos : (0 : Q') < prodFloorVal :=
  Q'.mul_pos floorEps_pos physMargin0_pos

/-- `prodFloorVal ≤ prodPrefix (1 − defectRen) k · physMargin 0` (the `prodFloor_le`
field shape): `floorEps·Δ₀ ≤ physGapSeq k·Δ₀`. -/
theorem prodFloorVal_le (k : Nat) :
    prodFloorVal ≤ prodPrefix (fun i => 1 - defectRen i) k * physMargin 0 := by
  show floorEps * physMargin 0 ≤ prodPrefix (fun i => 1 - defectRen i) k * physMargin 0
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ (floorEps_le_prodPrefix k)
    (Q'.le_of_lt physMargin0_pos)

/-! ## 9. THE ASSEMBLED dominant-mode `RGCoeffStep` (conditional on the residual) -/

/-- **The dominant-mode `RGCoeffStep` from the named residual.**  Given the single
tail-monotonicity obligation `FusionMarginTailMonotone`, ALL fields of `RGCoeffStep`
are supplied:

  * `physMargin` = the GENUINE fusion-derived vacuum-normalized margin
    `1 − E_k/Z'_k` (real `fusionProduct`/`divPos`), with `physMargin0_pos` proved;
  * `vacuumCoeff`/`vacuum_fixed` = the proved `normalizedTrivialCoeff_eqv_one`
    (vacuum FIXED by normalization), at `Z' = Z'_k`;
  * `defectRen` = the proved renormalized quadratic defect (= `defectSeq`), with
    nonnegativity and `≤ 1` reused;
  * `normExcitedDrift` = `normExcitedDrift_of_mono H` (PROVED from monotonicity);
  * `prodFloor` = `floorEps · physMargin 0 > 0` from the proved summability floor.

So `dominantRGCoeffStep H : RGCoeffStep` is a GENUINE inhabitant whenever the single
residual `H` holds. -/
noncomputable def dominantRGCoeffStep (H : FusionMarginTailMonotone) : RGCoeffStep where
  physMargin := physMargin
  physMargin0_pos := physMargin0_pos
  vacuumCoeff := fun k => normalizedTrivialCoeff 1 (wSeq k) (ZprimeSeq_pos k)
  vacuum_fixed := fun k => normalizedTrivialCoeff_eqv_one 1 (wSeq k) (ZprimeSeq_pos k)
  defectRen := defectRen
  defectRen_nonneg := defectRen_nonneg
  defectRen_le_one := defectRen_le_one
  normExcitedDrift := normExcitedDrift_of_mono H
  prodFloor := prodFloorVal
  prodFloor_pos := prodFloorVal_pos
  prodFloor_le := prodFloorVal_le

/-- **THE CONDITIONAL DOMINANT-MODE CONTINUUM FLOOR.**  From the assembled instance,
the genuine fusion-derived margin has a uniform positive floor at every tail scale —
conditional ONLY on the single residual `FusionMarginTailMonotone`.  Everything else
(the fusion crux, `Z' ≥ 1`, margin nonnegativity, anchor positivity, the defect
facts, the summability floor, and the drift reduction) is PROVED. -/
theorem dominantMode_continuum_floor (H : FusionMarginTailMonotone) :
    (0 : Q') < (dominantRGCoeffStep H).prodFloor
      ∧ ∀ k : Nat, (dominantRGCoeffStep H).prodFloor ≤ (dominantRGCoeffStep H).physMargin k :=
  continuum_floor_of_RGCoeffStep (dominantRGCoeffStep H)

/-- The genuine fusion margin is strictly positive at every tail scale (conditional
on the residual). -/
theorem dominantMode_physMargin_pos (H : FusionMarginTailMonotone) (k : Nat) :
    (0 : Q') < (dominantRGCoeffStep H).physMargin k :=
  RGCoeffStep_physMargin_pos (dominantRGCoeffStep H) k

/-! ## 10. Honest assessment (English) — what is and is NOT closed

  * THE FUSION CRUX IS COMPUTED (proved).  `fusionExcited_eqv`: the leading-excited
    fused coefficient is `fusionProduct 1 (coeffW w)(coeffW w) 1 ≃ 2·coeffW w 1` (the
    off-diagonal `(0,1)/(1,0)` cross-terms are the ONLY contributors at `s = 1`).
    `fusionTrivial_eqv`: `Z' = fusionTrivialCoeff 1 w ≃ 1 + (coeffW w 1)²`, hence
    `Z' ≥ 1` (`fusionTrivial_ge_one` — the `(0,0)` diagonal alone is `1`).  So the
    genuine normalized excited coefficient is `2c₁/(1+c₁²)` and the margin is
    `(1−c₁)²/(1+c₁²)`, a HONEST `fusionProduct`/`divPos`-built quantity.

  * THE STRUCTURAL FINDING (decisive, honest).  `normExcitedDrift` as a per-step
    `δ_ren`-bound is FALSE for the genuine fusion margin: along the AF flow the seed
    `c₁ = 2w³` sweeps through `1` (at `w = 2^{-1/3}`), where `2c₁/(1+c₁²)` hits its
    max `1` and the margin hits `0`.  Near the crossing the margin changes by `O(1)`
    in one step — UNBOUNDABLE by the quadratically-small `δ_ren = O((1−w)²)`.  The
    fusion CROSS-TERM (the un-normalized excited coefficient `E = 2c₁` itself
    crossing `Z'`) genuinely breaks the `δ_ren` bound in the head.  The
    favorable-`Z'` heuristic of the vacuum-stability note was INSUFFICIENT: dividing
    by `Z' ≥ 1` does not prevent `E/Z'` from reaching `1`.

  * THE CLEAN REDUCTION (proved).  On the TAIL `k ≥ k₀ = cutoff` (where
    `c₁(w_{k₀}) ≈ 1.96 > 1`, past the crossing) the margin is monotone
    non-decreasing, and on a monotone-nonneg margin the recursion field is FREE.
    So `normExcitedDrift` REDUCES, with EVERYTHING ELSE PROVED, to the single named
    obligation `FusionMarginTailMonotone` (`physMargin k ≤ physMargin (k+1)`).
    `normExcitedDrift_of_mono` proves the drift FROM it; `dominantRGCoeffStep H`
    assembles a GENUINE `RGCoeffStep`; `dominantMode_continuum_floor H` gives the
    uniform positive floor on the genuine margin — all conditional ONLY on `H`.

  * HONEST BELIEF on `FusionMarginTailMonotone`.  I believe it is TRUE on the
    canonical AF trajectory with the proved cutoff `k₀`: the margin is a composition
    of three monotone maps past the `c₁ = 1` crossing (`w_k ↑`, `c₁ = 2w³ ↑`,
    `g(c) = (1−c)²/(1+c²) ↑` for `c ≥ 1`), and `c₁(w_{k₀}) > 1` is decide-checkable
    at the concrete index.  It is NOT proved here for symbolic `k` (the genuine but
    elementary monotonicity chain), so it is NAMED, not faked.  The anchor
    `physMargin0_pos` IS proved (decide at the concrete cutoff index).

  * WHAT IS NOT CLOSED.  (i) `FusionMarginTailMonotone` itself (the one residual);
    (ii) the truncation degree is `N = 1` (the genuine `s = 1` separator at this
    truncation — higher truncation degrees mix in more fusion channels);
    (iii) the FULL-mode (all `s`) margin and the genuine 4D AF trajectory (inherited
    from the proved defect floor's scope).  This module does NOT prove 4D Yang–Mills.
    It computes the genuine fusion margin, EXPOSES that the naive `δ_ren` drift bound
    is false (a real finding), and reduces the dominant-mode (B) to ONE crisp,
    believed-true tail-monotonicity obligation, with the entire rest of the
    `RGCoeffStep` (and hence the continuum floor) proved from it. -/

end YMGap.Continuum.NormExcitedDrift

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.NormExcitedDrift.q_lt_of_lt_of_le
#print axioms YMGap.Continuum.NormExcitedDrift.fusionExcited_eqv
#print axioms YMGap.Continuum.NormExcitedDrift.fusionTrivial_eqv
#print axioms YMGap.Continuum.NormExcitedDrift.ZprimeSeq_ge_one
#print axioms YMGap.Continuum.NormExcitedDrift.ZprimeSeq_pos
#print axioms YMGap.Continuum.NormExcitedDrift.normalizedExcited_eqv
#print axioms YMGap.Continuum.NormExcitedDrift.fusionExcited_le_Zprime
#print axioms YMGap.Continuum.NormExcitedDrift.normalizedExcited_le_one
#print axioms YMGap.Continuum.NormExcitedDrift.physMargin_nonneg
#print axioms YMGap.Continuum.NormExcitedDrift.physMargin0_pos
#print axioms YMGap.Continuum.NormExcitedDrift.defectRen_nonneg
#print axioms YMGap.Continuum.NormExcitedDrift.defectRen_le_one
#print axioms YMGap.Continuum.NormExcitedDrift.normExcitedDrift_of_mono
#print axioms YMGap.Continuum.NormExcitedDrift.floorEps_le_prodPrefix
#print axioms YMGap.Continuum.NormExcitedDrift.prodFloorVal_pos
#print axioms YMGap.Continuum.NormExcitedDrift.prodFloorVal_le
#print axioms YMGap.Continuum.NormExcitedDrift.dominantRGCoeffStep
#print axioms YMGap.Continuum.NormExcitedDrift.dominantMode_continuum_floor
#print axioms YMGap.Continuum.NormExcitedDrift.dominantMode_physMargin_pos
