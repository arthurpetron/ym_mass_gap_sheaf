/-
# The TIGHT sub-second-difference √ CANCELLATION (the tightness fix)

The loose chain in `ChebOrthoRadSecondDiffSq` bounds the sub-second-difference
`D' = s_+·s_- − s_k²` by `subSecondQuot = (2M²+2A²+1)/M² ~ O(1)`, dividing the genuine
`δ²`-numerator `subSecondBound = (2M²+2A²+1)/M⁴ ~ 2δ²` by the VACUOUSLY small sum lower
bound `subSecondL = 1/M²` on `S' = s_+s_- + s_k²`.  But the TRUE size of `S'` is
`~ oms = oneMinusSqNode = 1−x_k² ~ jdist/M`, so the genuine bound is `|D'| ≤ ~δ²/oms ~
1/(M·jdist)`, and the symmetric second difference is `~1/jdist²`.

This module supplies the TIGHT versions, axiom-clean, mirroring the loose chain but with
the genuine sum lower bound `oms` in the denominator.

## What is PROVED here (GENUINE new content, all axiom-clean)

  * **`oms_ge`** — `oneMinusSqNode M k ≥ jdist/(2M)`, i.e. the genuine node-radicand
    floor `oms ~ jdist/M`.  Pure `Int`/`Nat` cross-multiplication: reduce to
    `jdist·M ≤ 2·omsNum` via `omsNum = (2(M−k)−1)(2k+1) ≥ (M−k)(k+1)` and
    `2(M−k)(k+1) ≥ jdist·M`.

  * **`subSecondSum_ptwise_tight`** — the TIGHT pointwise lower bound
    `oms_lb ≤ (s_+s_- + s_k²).approx n` with `oms_lb = jdist/(2M) ≤ oms`.  Uses
    `s_+s_- ≥ 0` and `s_k².approx n = heronSeq oms n · heronSeq oms n ≥ oms` (the
    Newton-from-above square floor `heronSeq_sq_ge`).

  * **`subSecondDiff_tight_AbsLeRat`** — `|s_+s_- − s_k²| ≤ subSecondQuot_tight` with
    `subSecondQuot_tight · oms_lb ≈ subSecondBound`, giving the genuine `1/(M·jdist)`
    scale (bounded by `(2M²+2A²+1)·2/(M³·jdist) ≤ C/(M·jdist)`).

  * **`symmSecondDiff_tight_AbsLeRat`** — `|s_+ + s_- − 2s_k| ≤ symmQuot_tight` with the
    genuine `1/jdist²` scale, by redoing the outer division with the tight inner bound.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on closed
`Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file.
-/

import YMGap.Continuum.ChebOrthoRadSecondDiffSq
import YMGap.Continuum.ChebOrthoLegClose
import YMGap.Continuum.ChebOrthoFinal
import YMGap.Continuum.ChebOrthoInterior
import YMGap.Continuum.ChebOrthoRadSecondDiff
import YMGap.Continuum.ChebOrthoLeadingModel
import YMGap.Continuum.Pivot2Moments
import YMGap.Continuum.Pivot3Form

namespace YMGap.Continuum.ChebOrthoTightModulus

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoMidpoint
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.ChebOrthoGraded (jdist jdist_pos)
open YMGap.Continuum.ChebOrthoRadSecondDiffSq
open YMGap.Continuum.ChebOrthoGradedClose (AbsLeRat)
open YMGap.Continuum.ChebOrthoCancelDiv

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

/-! ## 0. The genuine node-radicand floor `oms ≥ jdist/(2M)` -/

/-- The EXACT factorisation `omsNum M k = (2(M−k)−1)·(2k+1)` (`= (2q−1)(2p−1)` with
`p = k+1`, `q = M−k`), a pure `Int` identity from `int_sq_diff_factor`. -/
theorem omsNum_factor (M k : Nat) :
    omsNum M k = (2 * (M : Int) - 2 * (k : Int) - 1) * (2 * (k : Int) + 1) := by
  show (M : Int) * (M : Int)
      - (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int))
    = (2 * (M : Int) - 2 * (k : Int) - 1) * (2 * (k : Int) + 1)
  rw [SemicircleIntegral.int_sq_diff_factor (M : Int) (2 * (k : Int) + 1 - (M : Int))]
  -- (M − (2k+1−M))·(M + (2k+1−M)) = (2M−2k−1)·(2k+1)
  have h1 : (M : Int) - (2 * (k : Int) + 1 - (M : Int)) = 2 * (M : Int) - 2 * (k : Int) - 1 := by
    omega
  have h2 : (M : Int) + (2 * (k : Int) + 1 - (M : Int)) = 2 * (k : Int) + 1 := by omega
  rw [h1, h2]

/-- **The genuine `Int` floor `jdist·M ≤ 2·omsNum`.**  With `p = k+1`, `q = M−k`,
`omsNum = (2q−1)(2p−1) ≥ q·p` (each factor `≥` its halved value), and
`2·q·p ≥ jdist·M = min(p,q)·(p+q−1)` since `2qp − min(p,q)(p+q−1) = min(p,q)·(max−min+1)
≥ 0`.  Pure `Int`/`Nat` after the factorisation, splitting on the `min`. -/
theorem jdist_mul_M_le_two_omsNum (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) :
    (jdist M k : Int) * (M : Int) ≤ 2 * omsNum M k := by
  rw [omsNum_factor M k]
  -- p = k+1, q = M−k  (Int)
  have hp : (1 : Int) ≤ (k : Int) + 1 := by
    have : (0 : Int) ≤ (k : Int) := Int.natCast_nonneg _; omega
  have hk' : (k : Int) < (M : Int) := by exact_mod_cast hkn
  -- jdist = min (k+1) (M−k) ; case on which is the min.
  have hjd : jdist M k = Nat.min (k + 1) (M - k) := rfl
  -- two factors of omsNum, both ≥ their "p"/"q" lower halves
  -- 2M−2k−1 ≥ M−k   (since M−k ≥ 1)   and   2k+1 ≥ k+1
  rcases Nat.le_total (k + 1) (M - k) with hmin | hmin
  · -- jdist = k+1
    have hjeq : jdist M k = k + 1 := by rw [hjd]; exact Nat.min_eq_left hmin
    rw [hjeq]
    -- (k+1)·M ≤ 2·(2M−2k−1)(2k+1)
    -- use 2M−2k−1 ≥ M−k ≥ k+1 (from hmin as Int) ; so RHS ≥ 2(k+1)(k+1) ... but we need M.
    -- Cleaner: 2·(2M−2k−1)(2k+1) ≥ 2·(M−k)(k+1)  and  2(M−k)(k+1) ≥ (k+1)·M.
    have hf1 : (M : Int) - (k : Int) ≤ 2 * (M : Int) - 2 * (k : Int) - 1 := by omega
    have hf2 : (k : Int) + 1 ≤ 2 * (k : Int) + 1 := by omega
    have hpos1 : (0 : Int) < (M : Int) - (k : Int) := by omega
    have hpos2 : (0 : Int) < (k : Int) + 1 := by omega
    -- (M−k)(k+1) ≤ (2M−2k−1)(2k+1)
    have hprodle : ((M : Int) - (k : Int)) * ((k : Int) + 1)
        ≤ (2 * (M : Int) - 2 * (k : Int) - 1) * (2 * (k : Int) + 1) := by
      have ha : ((M : Int) - (k : Int)) * ((k : Int) + 1)
          ≤ (2 * (M : Int) - 2 * (k : Int) - 1) * ((k : Int) + 1) :=
        Int.mul_le_mul_of_nonneg_right hf1 (Int.le_of_lt hpos2)
      have hb : (2 * (M : Int) - 2 * (k : Int) - 1) * ((k : Int) + 1)
          ≤ (2 * (M : Int) - 2 * (k : Int) - 1) * (2 * (k : Int) + 1) :=
        Int.mul_le_mul_of_nonneg_left hf2 (by omega)
      exact Int.le_trans ha hb
    -- (k+1)·M ≤ 2·(M−k)(k+1) :  since min = k+1 ≤ M−k, p+q−1 = M, 2(M−k)≥ ...
    -- (k+1)·M ≤ 2(M−k)(k+1) ⟺ M ≤ 2(M−k) ⟺ 2k ≤ M ; and k+1 ≤ M−k ⟹ 2k+1 ≤ M ⟹ 2k ≤ M.
    have hkM : 2 * (k : Int) + 1 ≤ (M : Int) := by
      have : (k + 1 : Nat) ≤ M - k := hmin
      have hI : ((k + 1 : Nat) : Int) ≤ ((M - k : Nat) : Int) := by exact_mod_cast this
      have hsub : ((M - k : Nat) : Int) = (M : Int) - (k : Int) := by
        have : k ≤ M := Nat.le_of_lt hkn
        omega
      rw [hsub] at hI; push_cast at hI; omega
    have hbase : ((k : Int) + 1) * (M : Int) ≤ 2 * (((M : Int) - (k : Int)) * ((k : Int) + 1)) := by
      -- 2(M−k)(k+1) − (k+1)M = (k+1)(2(M−k) − M) = (k+1)(M−2k) ≥ 0
      have hfac : 2 * (((M : Int) - (k : Int)) * ((k : Int) + 1))
          = ((k : Int) + 1) * (2 * ((M : Int) - (k : Int))) := by
        rw [Int.mul_comm ((M : Int) - (k : Int)) ((k : Int) + 1)]
        rw [← Int.mul_assoc 2 ((k:Int)+1) ((M:Int)-(k:Int))]
        rw [Int.mul_comm 2 ((k:Int)+1), Int.mul_assoc]
      rw [hfac]
      have hMk : (M : Int) ≤ 2 * ((M : Int) - (k : Int)) := by omega
      exact Int.mul_le_mul_of_nonneg_left hMk (by omega)
    -- chain
    have h2le : 2 * (((M : Int) - (k : Int)) * ((k : Int) + 1))
        ≤ 2 * ((2 * (M : Int) - 2 * (k : Int) - 1) * (2 * (k : Int) + 1)) :=
      Int.mul_le_mul_of_nonneg_left hprodle (by decide)
    exact Int.le_trans hbase h2le
  · -- jdist = M−k
    have hjeq : jdist M k = M - k := by rw [hjd]; exact Nat.min_eq_right hmin
    rw [hjeq]
    have hsub : ((M - k : Nat) : Int) = (M : Int) - (k : Int) := by
      have : k ≤ M := Nat.le_of_lt hkn
      omega
    rw [hsub]
    -- (M−k)·M ≤ 2·(2M−2k−1)(2k+1)
    have hf1 : (M : Int) - (k : Int) ≤ 2 * (M : Int) - 2 * (k : Int) - 1 := by omega
    have hf2 : (k : Int) + 1 ≤ 2 * (k : Int) + 1 := by omega
    have hpos2 : (0 : Int) < (k : Int) + 1 := by omega
    -- (M−k)(k+1) ≤ (2M−2k−1)(2k+1)
    have hprodle : ((M : Int) - (k : Int)) * ((k : Int) + 1)
        ≤ (2 * (M : Int) - 2 * (k : Int) - 1) * (2 * (k : Int) + 1) := by
      have ha : ((M : Int) - (k : Int)) * ((k : Int) + 1)
          ≤ (2 * (M : Int) - 2 * (k : Int) - 1) * ((k : Int) + 1) :=
        Int.mul_le_mul_of_nonneg_right hf1 (Int.le_of_lt hpos2)
      have hb : (2 * (M : Int) - 2 * (k : Int) - 1) * ((k : Int) + 1)
          ≤ (2 * (M : Int) - 2 * (k : Int) - 1) * (2 * (k : Int) + 1) :=
        Int.mul_le_mul_of_nonneg_left hf2 (by omega)
      exact Int.le_trans ha hb
    -- (M−k)·M ≤ 2(M−k)(k+1) :  M ≤ 2(k+1) ⟺ M−2 ≤ 2k ; from M−k ≤ k+1 ⟹ M ≤ 2k+1 ⟹ M ≤ 2(k+1).
    have hkM : (M : Int) ≤ 2 * (k : Int) + 1 := by
      have : (M - k : Nat) ≤ k + 1 := hmin
      have hI : ((M - k : Nat) : Int) ≤ ((k + 1 : Nat) : Int) := by exact_mod_cast this
      rw [hsub] at hI; push_cast at hI; omega
    have hbase : ((M : Int) - (k : Int)) * (M : Int)
        ≤ 2 * (((M : Int) - (k : Int)) * ((k : Int) + 1)) := by
      -- 2(M−k)(k+1) − (M−k)M = (M−k)(2(k+1) − M) ≥ 0
      have hfac : 2 * (((M : Int) - (k : Int)) * ((k : Int) + 1))
          = ((M : Int) - (k : Int)) * (2 * ((k : Int) + 1)) := by
        rw [← Int.mul_assoc 2 ((M:Int)-(k:Int)) ((k:Int)+1)]
        rw [Int.mul_comm 2 ((M:Int)-(k:Int)), Int.mul_assoc]
      rw [hfac]
      have hMk : (M : Int) ≤ 2 * ((k : Int) + 1) := by omega
      exact Int.mul_le_mul_of_nonneg_left hMk (by omega)
    have h2le : 2 * (((M : Int) - (k : Int)) * ((k : Int) + 1))
        ≤ 2 * ((2 * (M : Int) - 2 * (k : Int) - 1) * (2 * (k : Int) + 1)) :=
      Int.mul_le_mul_of_nonneg_left hprodle (by decide)
    exact Int.le_trans hbase h2le

/-- The genuine rational node-radicand floor `oms_lb := jdist/(2M) ≤ oms`. -/
def oms_lb (M k : Nat) (hM : 0 < M) : Q' :=
  Q'.mkPos (jdist M k : Int) (2 * M) (by omega)

theorem oms_lb_pos (M k : Nat) (hM : 0 < M) (hk : k < M) : (0 : Q') < oms_lb M k hM := by
  show (0 : Int) * ((oms_lb M k hM).den : Int) < (oms_lb M k hM).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  show (0 : Int) < (Q'.mkPos (jdist M k : Int) (2 * M) (by omega)).num
  rw [Q'.mkPos_num]
  have : 0 < jdist M k := jdist_pos hk
  exact_mod_cast this

/-- **THE GENUINE NODE-RADICAND FLOOR.**  For an interior node `0 < k < M`,
`oms_lb M k = jdist/(2M) ≤ oneMinusSqNode M k = 1−x_k²`.  The `~jdist/M` scale of the
node radicand (vs the vacuous `1/M²`), via the `Int` floor `jdist·M ≤ 2·omsNum`. -/
theorem oms_ge (M : Nat) (hM : 0 < M) (k : Nat) (hk0 : 0 < k) (hkn : k < M) :
    oms_lb M k hM ≤ oneMinusSqNode M k hM hkn := by
  show (oms_lb M k hM).num * ((oneMinusSqNode M k hM hkn).den : Int)
      ≤ (oneMinusSqNode M k hM hkn).num * ((oms_lb M k hM).den : Int)
  have hLn : (oms_lb M k hM).num = (jdist M k : Int) := by
    show (Q'.mkPos (jdist M k : Int) (2 * M) (by omega)).num = (jdist M k : Int)
    rw [Q'.mkPos_num]
  have hLd : ((oms_lb M k hM).den : Int) = ((2 * M : Nat) : Int) := by
    show ((Q'.mkPos (jdist M k : Int) (2 * M) (by omega)).den : Int) = ((2 * M : Nat) : Int)
    rw [Q'.mkPos_den]
  have hRn : (oneMinusSqNode M k hM hkn).num = omsNum M k := by
    show (Q'.mkPos (omsNum M k) (omsDen M) (omsDen_pos hM)).num = omsNum M k
    rw [Q'.mkPos_num]
  have hRd : ((oneMinusSqNode M k hM hkn).den : Int) = ((M * M : Nat) : Int) := by
    show ((Q'.mkPos (omsNum M k) (omsDen M) (omsDen_pos hM)).den : Int) = ((M * M : Nat) : Int)
    rw [Q'.mkPos_den]; rfl
  rw [hLn, hLd, hRn, hRd]
  -- jdist·(M·M) ≤ omsNum·(2M)
  have h2M : ((2 * M : Nat) : Int) = 2 * (M : Int) := by push_cast; rfl
  have hMM : ((M * M : Nat) : Int) = (M : Int) * (M : Int) := by push_cast; rfl
  rw [h2M, hMM]
  -- jdist·(M·M) = (jdist·M)·M ≤ (2·omsNum)·M = omsNum·(2M)
  have hcore : (jdist M k : Int) * (M : Int) ≤ 2 * omsNum M k :=
    jdist_mul_M_le_two_omsNum M hM k hk0 hkn
  have hMnn : (0 : Int) ≤ (M : Int) := Int.natCast_nonneg _
  have hstep : ((jdist M k : Int) * (M : Int)) * (M : Int) ≤ (2 * omsNum M k) * (M : Int) :=
    Int.mul_le_mul_of_nonneg_right hcore hMnn
  -- rearrange both sides to match the goal shape
  have hL : (jdist M k : Int) * ((M : Int) * (M : Int))
      = ((jdist M k : Int) * (M : Int)) * (M : Int) := by rw [Int.mul_assoc]
  have hR : omsNum M k * (2 * (M : Int)) = (2 * omsNum M k) * (M : Int) := by
    rw [Int.mul_comm 2 (omsNum M k), Int.mul_assoc (omsNum M k) 2 (M : Int)]
  rw [hL, hR]
  exact hstep

#print axioms oms_ge

/-! ## 1. The TIGHT pointwise lower bound on the sub-second-difference sum -/

/-- **The genuine `oms` square floor at every Heron index.**  For an interior node,
`oneMinusSqNode M k ≤ (nodeWeight M k).approx n · (nodeWeight M k).approx n` — the
Newton-from-above square floor `heronSeq_sq_ge` (`oms ≤ heronSeq oms n²`), transferred
through `(nodeWeight).approx n = heronSeq oms n`. -/
theorem nodeSq_approx_ge_oms (M : Nat) (hM : 0 < M) (k : Nat) (hk : k < M) (n : Nat) :
    oneMinusSqNode M k hM hk
      ≤ (nodeWeight M hM k).approx n * (nodeWeight M hM k).approx n := by
  rw [ChebOrthoLeadingModel.nodeWeight_eq_sqrtFrom M hM k hk, CReal.sqrtFrom_approx]
  -- goal: oms ≤ heronSeq oms n · heronSeq oms n
  exact CReal.heronSeq_sq_ge (oneMinusSqNode M k hM hk) (oneMinusSqNode_pos hM hk) n

/-- **THE TIGHT pointwise lower bound on the sub-second-difference sum.**  For an
interior cell, at every Heron index:

    `oms_lb M k = jdist/(2M) ≤ (s_+ s_- + s_k²).approx n`.

PROOF: `s_+ s_-.approx n ≥ 0` (both radicals nonneg) and `s_k².approx n ≥ oms`
(`nodeSq_approx_ge_oms`); so the sum is `≥ 0 + oms ≥ oms_lb` (`oms_ge`).  This is the
genuine `~jdist/M` floor, NOT the vacuous `1/M²` of `subSecondSum_ptwise`. -/
theorem subSecondSum_ptwise_tight (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (n : Nat) :
    oms_lb M k hM
      ≤ (CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
          (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))).approx n := by
  show oms_lb M k hM
      ≤ (bdyRadical M hM (k + 1)).approx n * (bdyRadical M hM k).approx n
        + (nodeWeight M hM k).approx n * (nodeWeight M hM k).approx n
  -- s_+ s_- ≥ 0
  have hprod0 : (0 : Q')
      ≤ (bdyRadical M hM (k + 1)).approx n * (bdyRadical M hM k).approx n :=
    Q'.mul_nonneg _ _
      (ChebOrthoInterior.bdyRadical_approx_nonneg M hM (k + 1) n)
      (ChebOrthoInterior.bdyRadical_approx_nonneg M hM k n)
  -- s_k².approx n ≥ oms
  have hnodeSq : oneMinusSqNode M k hM hkn
      ≤ (nodeWeight M hM k).approx n * (nodeWeight M hM k).approx n :=
    nodeSq_approx_ge_oms M hM k hkn n
  -- oms_lb ≤ oms ≤ s_k² ≤ s_+s_- + s_k²
  refine Q'.le_trans' _ _ _ (oms_ge M hM k hk0 hkn) ?_
  refine Q'.le_trans' _ _ _ hnodeSq ?_
  -- s_k² ≤ s_+s_- + s_k²
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_zero_add_eqv _)) ?_
  exact Q'.add_le_add hprod0 (Q'.le_refl' _)

#print axioms subSecondSum_ptwise_tight

/-! ## 2. The TIGHT sub-second-difference √ cancellation -/

/-- The numerator `C = 2M² + 2A² + 1`, `A = 2k+1−M` (shared with `subSecondBound`). -/
def ssNumC (M k : Nat) : Int :=
  2 * (M : Int) * (M : Int)
    + 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int))) + 1

theorem ssNumC_nonneg (M k : Nat) : (0 : Int) ≤ ssNumC M k := by
  show (0 : Int) ≤ 2 * (M : Int) * (M : Int)
    + 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int))) + 1
  have hMM : (0 : Int) ≤ 2 * (M : Int) * (M : Int) :=
    Int.mul_nonneg (Int.mul_nonneg (by decide) (Int.natCast_nonneg _)) (Int.natCast_nonneg _)
  have hA2 : (0 : Int) ≤ (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)) := by
    rcases Int.le_total 0 (2 * (k : Int) + 1 - (M : Int)) with hj | hj
    · exact Int.mul_nonneg hj hj
    · have hneg : (0 : Int) ≤ -(2 * (k : Int) + 1 - (M : Int)) := by omega
      have hp : (0 : Int) ≤ (-(2 * (k : Int) + 1 - (M : Int)))
          * (-(2 * (k : Int) + 1 - (M : Int))) := Int.mul_nonneg hneg hneg
      have he : (-(2 * (k : Int) + 1 - (M : Int))) * (-(2 * (k : Int) + 1 - (M : Int)))
          = (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)) := by
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      rw [he] at hp; exact hp
  have h2A2 : (0 : Int) ≤ 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int))) :=
    Int.mul_nonneg (by decide) hA2
  omega

/-- `M³` (Nat). -/
def m3 (M : Nat) : Nat := M * M * M

theorem m3_pos {M : Nat} (hM : 0 < M) : 0 < m3 M :=
  Nat.mul_pos (Nat.mul_pos hM hM) hM

/-- **The TIGHT reciprocal-free quotient** `subSecondQuot_tight = K/L = subSecondBound/oms_lb
= (2M²+2A²+1)·2/(M³·jdist) ~ 1/(M·jdist)`. -/
def subSecondQuot_tight (M k : Nat) (hM : 0 < M) (hkn : k < M) : Q' :=
  Q'.mkPos (2 * ssNumC M k) (m3 M * jdist M k)
    (Nat.mul_pos (m3_pos hM) (jdist_pos hkn))

theorem subSecondQuot_tight_nonneg (M k : Nat) (hM : 0 < M) (hkn : k < M) :
    (0 : Q') ≤ subSecondQuot_tight M k hM hkn := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (Q'.mkPos (2 * ssNumC M k) (m3 M * jdist M k) _).num
  rw [Q'.mkPos_num]
  exact Int.mul_nonneg (by decide) (ssNumC_nonneg M k)

/-- `subSecondQuot_tight · oms_lb ≈ subSecondBound`: `(2C/(M³j))·(j/(2M)) = C/M⁴`
(cross-multiplication on `mkPos`; the `2`s and a `j` cancel against `M`). -/
theorem subSecondQuot_tight_mul_L (M k : Nat) (hM : 0 < M) (hk0 : 0 < k) (hkn : k < M) :
    (subSecondQuot_tight M k hM hkn * oms_lb M k hM) ≈ subSecondBound M k hM := by
  show (subSecondQuot_tight M k hM hkn * oms_lb M k hM).num * ((subSecondBound M k hM).den : Int)
      = (subSecondBound M k hM).num * ((subSecondQuot_tight M k hM hkn * oms_lb M k hM).den : Int)
  -- numerators / denominators
  have hQTn : (subSecondQuot_tight M k hM hkn).num = 2 * ssNumC M k := by
    show (Q'.mkPos (2 * ssNumC M k) (m3 M * jdist M k) _).num = 2 * ssNumC M k
    rw [Q'.mkPos_num]
  have hQTd : (subSecondQuot_tight M k hM hkn).den = m3 M * jdist M k := by
    show (Q'.mkPos (2 * ssNumC M k) (m3 M * jdist M k) _).den = m3 M * jdist M k
    rw [Q'.mkPos_den]
  have hLn : (oms_lb M k hM).num = (jdist M k : Int) := by
    show (Q'.mkPos (jdist M k : Int) (2 * M) _).num = (jdist M k : Int); rw [Q'.mkPos_num]
  have hLd : (oms_lb M k hM).den = 2 * M := by
    show (Q'.mkPos (jdist M k : Int) (2 * M) _).den = 2 * M; rw [Q'.mkPos_den]
  have hBn : (subSecondBound M k hM).num = ssNumC M k := by
    show (Q'.mkPos (ssNumC M k) (ChebOrthoRadSecondDiffSq.m4 M) _).num = ssNumC M k
    rw [Q'.mkPos_num]
  have hBd : (subSecondBound M k hM).den = ChebOrthoRadSecondDiffSq.m4 M := by
    show (Q'.mkPos (ssNumC M k) (ChebOrthoRadSecondDiffSq.m4 M) _).den = ChebOrthoRadSecondDiffSq.m4 M
    rw [Q'.mkPos_den]
  -- LHS num = (2C)·jdist ; LHS den = (M³·jdist)·(2M)
  have hLHSn : (subSecondQuot_tight M k hM hkn * oms_lb M k hM).num
      = (2 * ssNumC M k) * (jdist M k : Int) := by
    show (subSecondQuot_tight M k hM hkn).num * (oms_lb M k hM).num = _
    rw [hQTn, hLn]
  have hLHSd : ((subSecondQuot_tight M k hM hkn * oms_lb M k hM).den : Int)
      = ((m3 M * jdist M k : Nat) : Int) * ((2 * M : Nat) : Int) := by
    rw [Q'.mul_den_cast, hQTd, hLd]
  rw [hLHSn, hLHSd, hBn, hBd]
  -- (2C·jdist)·M⁴ = C·((M³·jdist)·(2M))
  have hm4 : ((ChebOrthoRadSecondDiffSq.m4 M : Nat) : Int)
      = (M : Int) * (M : Int) * ((M : Int) * (M : Int)) := by
    show ((((M * M) * (M * M)) : Nat) : Int) = _; push_cast; rfl
  have hm3 : ((m3 M * jdist M k : Nat) : Int)
      = ((M : Int) * (M : Int) * (M : Int)) * (jdist M k : Int) := by
    show (((M * M * M) * jdist M k : Nat) : Int) = _; push_cast; rfl
  have h2M : ((2 * M : Nat) : Int) = 2 * (M : Int) := by push_cast; rfl
  rw [hm4, hm3, h2M]
  -- now a pure Int identity:  (2C·j)·(M·M·(M·M)) = C·((M·M·M·j)·(2M)).
  -- AC-normalise with the core Int commutativity/associativity lemmas.
  generalize ssNumC M k = C
  generalize (jdist M k : Int) = j
  generalize (M : Int) = m
  simp only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]

/-- **THE TIGHT SUB-SECOND-DIFFERENCE √ CANCELLATION.**  For an interior cell `0 < k`,
`k+1 < M`, the genuine sub-second-difference `D' = s_+ s_- − s_k²` is two-sidedly bounded
by the TIGHT quotient

    `|s_+ s_- − s_k²| ≤ subSecondQuot_tight M k = (2M²+2A²+1)·2/(M³·jdist) ~ 1/(M·jdist)`.

This divides the genuine `δ²`-numerator `subSecondBound = (2M²+2A²+1)/M⁴` by the TRUE sum
lower bound `oms_lb = jdist/(2M)` (`oms_ge` + `subSecondSum_ptwise_tight`), NOT the vacuous
`1/M²` of the loose `subSecondDiff_AbsLeRat`.  Reciprocal-free; via
`AbsLeRat.div_of_mul_ge` with `K = subSecondBound` (`subSecondProdDiff_AbsLeRat`),
`L = oms_lb`, `KL = subSecondQuot_tight`. -/
theorem subSecondDiff_tight_AbsLeRat (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    AbsLeRat
      (CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
        (CReal.neg (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))))
      (subSecondQuot_tight M k hM hkn) :=
  AbsLeRat.div_of_mul_ge
    (D := CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
      (CReal.neg (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))))
    (S := CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
      (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k)))
    (K := subSecondBound M k hM) (L := oms_lb M k hM) (KL := subSecondQuot_tight M k hM hkn)
    (ChebOrthoRadSecondDiffSq.subSecondProdDiff_AbsLeRat M hM k hk0 hkn hk1n)
    (fun n => subSecondSum_ptwise_tight M hM k hk0 hkn n)
    (oms_lb_pos M k hM hkn)
    (subSecondQuot_tight_nonneg M k hM hkn)
    (subSecondQuot_tight_mul_L M k hM hk0 hkn)

/-- **The explicit `1/(M·jdist)` scale.**  `subSecondQuot_tight ≤ 10/(M·jdist)`.
Since `|A| = |2k+1−M| ≤ M` (interior), `A² ≤ M²`, so the numerator
`2C = 2(2M²+2A²+1) ≤ 2(2M²+2M²+1) ≤ 2·5M² = 10M²` (using `1 ≤ M²`), and dividing by
`M³·jdist` gives `≤ 10M²/(M³·jdist) = 10/(M·jdist)`.  Pure `Int` cross-multiplication
(mirror `sharpBound_le_recip_jdist`). -/
theorem subSecondQuot_tight_le_recip (M : Nat) (hM : 0 < M) (k : Nat)
    (hkn : k < M) (hk1n : k + 1 < M) :
    subSecondQuot_tight M k hM hkn
      ≤ Q'.mkPos 10 (M * jdist M k) (Nat.mul_pos hM (jdist_pos hkn)) := by
  show (subSecondQuot_tight M k hM hkn).num
        * ((Q'.mkPos 10 (M * jdist M k) (Nat.mul_pos hM (jdist_pos hkn))).den : Int)
      ≤ (Q'.mkPos 10 (M * jdist M k) (Nat.mul_pos hM (jdist_pos hkn))).num
        * ((subSecondQuot_tight M k hM hkn).den : Int)
  have hQTn : (subSecondQuot_tight M k hM hkn).num = 2 * ssNumC M k := by
    show (Q'.mkPos (2 * ssNumC M k) (m3 M * jdist M k) _).num = 2 * ssNumC M k
    rw [Q'.mkPos_num]
  have hQTd : ((subSecondQuot_tight M k hM hkn).den : Int) = ((m3 M * jdist M k : Nat) : Int) := by
    show ((Q'.mkPos (2 * ssNumC M k) (m3 M * jdist M k) _).den : Int) = _
    rw [Q'.mkPos_den]
  have hCn : (Q'.mkPos 10 (M * jdist M k) (Nat.mul_pos hM (jdist_pos hkn))).num = 10 := by
    rw [Q'.mkPos_num]
  have hCd : ((Q'.mkPos 10 (M * jdist M k) (Nat.mul_pos hM (jdist_pos hkn))).den : Int)
      = ((M * jdist M k : Nat) : Int) := by rw [Q'.mkPos_den]
  rw [hQTn, hQTd, hCn, hCd]
  -- (2C)·(M·j) ≤ 10·(M³·j)  ⟺  (2C)·M·j ≤ 10·M³·j ; cancel M·j > 0, reduce to 2C ≤ 10M².
  have hMj : ((M * jdist M k : Nat) : Int) = (M : Int) * (jdist M k : Int) := by push_cast; rfl
  have hM3j : ((m3 M * jdist M k : Nat) : Int)
      = ((M : Int) * (M : Int) * (M : Int)) * (jdist M k : Int) := by
    show (((M * M * M) * jdist M k : Nat) : Int) = _; push_cast; rfl
  rw [hMj, hM3j]
  -- 2C ≤ 10M² :  C = 2M²+2A²+1, A² ≤ M², so 2C = 4M²+4A²+2 ≤ 4M²+4M²+2 ≤ 8M²+2M² = 10M².
  have hAle : (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int))
      ≤ (M : Int) * (M : Int) := by
    -- |2k+1−M| ≤ M  ⟹  A² ≤ M².
    have hkI : (k : Int) < (M : Int) := by exact_mod_cast hkn
    have hk0 : (0 : Int) ≤ (k : Int) := Int.natCast_nonneg _
    have hM0 : (0 : Int) ≤ (M : Int) := Int.natCast_nonneg _
    -- A² ≤ M² from −M ≤ A ≤ M : (M−A)(M+A) ≥ 0.
    have h1 : (0 : Int) ≤ (M : Int) - (2 * (k : Int) + 1 - (M : Int)) := by omega
    have h2 : (0 : Int) ≤ (M : Int) + (2 * (k : Int) + 1 - (M : Int)) := by omega
    have hprod : (0 : Int) ≤ ((M : Int) - (2 * (k : Int) + 1 - (M : Int)))
        * ((M : Int) + (2 * (k : Int) + 1 - (M : Int))) := Int.mul_nonneg h1 h2
    have hexp : ((M : Int) - (2 * (k : Int) + 1 - (M : Int)))
        * ((M : Int) + (2 * (k : Int) + 1 - (M : Int)))
        = (M : Int) * (M : Int)
          - (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)) :=
      (SemicircleIntegral.int_sq_diff_factor (M : Int) (2 * (k : Int) + 1 - (M : Int))).symm
    rw [hexp] at hprod; omega
  have hM2_1 : (1 : Int) ≤ (M : Int) * (M : Int) := by
    have hM1 : (1 : Int) ≤ (M : Int) := by exact_mod_cast hM
    have hM0 : (0 : Int) ≤ (M : Int) := by omega
    -- M·M ≥ M·1 = M ≥ 1
    have hstep : (M : Int) * 1 ≤ (M : Int) * (M : Int) :=
      Int.mul_le_mul_of_nonneg_left hM1 hM0
    rw [Int.mul_one] at hstep
    exact Int.le_trans hM1 hstep
  have h2C : 2 * ssNumC M k ≤ 10 * ((M : Int) * (M : Int)) := by
    show 2 * (2 * (M : Int) * (M : Int)
        + 2 * ((2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int))) + 1)
      ≤ 10 * ((M : Int) * (M : Int))
    have hMM : (2 * (M : Int)) * (M : Int) = 2 * ((M : Int) * (M : Int)) := by
      rw [Int.mul_assoc]
    omega
  -- (2C)·(M·j) ≤ (10M²)·(M·j) = 10·(M³·j)
  have hMjnn : (0 : Int) ≤ (M : Int) * (jdist M k : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hstep : (2 * ssNumC M k) * ((M : Int) * (jdist M k : Int))
      ≤ (10 * ((M : Int) * (M : Int))) * ((M : Int) * (jdist M k : Int)) :=
    Int.mul_le_mul_of_nonneg_right h2C hMjnn
  refine Int.le_trans hstep ?_
  -- (10M²)·(M·j) = 10·(M³·j)
  have hfold : (10 * ((M : Int) * (M : Int))) * ((M : Int) * (jdist M k : Int))
      = 10 * (((M : Int) * (M : Int) * (M : Int)) * (jdist M k : Int)) := by
    generalize (M : Int) = m
    generalize (jdist M k : Int) = j
    simp only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]
  rw [hfold]
  exact Int.le_refl _

#print axioms subSecondQuot_tight_mul_L
#print axioms subSecondDiff_tight_AbsLeRat
#print axioms subSecondQuot_tight_le_recip

/-! ## 3. The symmetric second-difference TIGHT outer division

`ChebOrthoLegClose`'s outer-division chain (`symmD`, `symmS`, `DS_collapse`,
`symmS_lower`, …) is `private`, so we re-derive the load-bearing pieces here and feed the
TIGHT inner bound `subSecondDiff_tight_AbsLeRat` in place of the loose
`subSecondDiff_AbsLeRat`.  The Equiv `DS_collapse` is bound-independent (a pure ring
identity + the square collapses); only the numerator bound changes. -/

open YMGap.Continuum.ChebOrthoInterior (recipWitness recipWitness_pos recipWitness_sq_le)

local infix:50 " ≋ " => CReal.Equiv

/-- `s_+ + s_-`. -/
def radSum (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.add (bdyRadical M hM (k + 1)) (bdyRadical M hM k)

/-- `2 s_k = s_k + s_k`. -/
def twoNode (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.add (nodeWeight M hM k) (nodeWeight M hM k)

/-- The SYMMETRIC second difference `D = (s_+ + s_-) − 2 s_k`. -/
def symmD (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.add (radSum M hM k) (CReal.neg (twoNode M hM k))

/-- The SYMMETRIC sum `S = (s_+ + s_-) + 2 s_k`. -/
def symmS (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.add (radSum M hM k) (twoNode M hM k)

/-- `E = (s_+ s_- + s_+ s_-) + ((s_+² + s_-²) + (−(2 s_k)²))`. -/
def symmE (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.add
    (CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
      (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k)))
    (CReal.add
      (CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM (k + 1)))
        (CReal.mul (bdyRadical M hM k) (bdyRadical M hM k)))
      (CReal.neg (CReal.mul (twoNode M hM k) (twoNode M hM k))))

/-- `subDiff = s_+ s_- − s_k²`. -/
def subDiff (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
    (CReal.neg (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k)))

/-- **`D · S ≈ E`** (per-approximation `Q'` ring identity). -/
theorem DS_eq_E (M : Nat) (hM : 0 < M) (k : Nat) :
    CReal.Equiv (CReal.mul (symmD M hM k) (symmS M hM k)) (symmE M hM k) :=
  SumOfSquares.Equiv_of_approx_eqv (fun p => by
    show (((bdyRadical M hM (k + 1)).approx p + (bdyRadical M hM k).approx p)
            + (-((nodeWeight M hM k).approx p + (nodeWeight M hM k).approx p)))
          * (((bdyRadical M hM (k + 1)).approx p + (bdyRadical M hM k).approx p)
            + ((nodeWeight M hM k).approx p + (nodeWeight M hM k).approx p))
        ≈ (((bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM k).approx p
              + (bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM k).approx p)
            + (((bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM (k + 1)).approx p
                + (bdyRadical M hM k).approx p * (bdyRadical M hM k).approx p)
              + (-(((nodeWeight M hM k).approx p + (nodeWeight M hM k).approx p)
                  * ((nodeWeight M hM k).approx p + (nodeWeight M hM k).approx p)))))
    generalize (bdyRadical M hM (k + 1)).approx p = a
    generalize (bdyRadical M hM k).approx p = b
    generalize (nodeWeight M hM k).approx p = c
    show ((a + b) + (-(c + c))) * ((a + b) + (c + c))
        ≈ ((a * b + a * b) + ((a * a + b * b) + (-((c + c) * (c + c)))))
    refine Q'.eqv_trans _ _ _
      (ChebOrthoCancelDiv.diffOfSquares_eqv (a + b) (c + c)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (?_ : ((a + b) * (a + b))
        ≈ ((a * b + a * b) + (a * a + b * b)))) ?_
    · refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv a b (a + b)) ?_
      have e1 : (a * (a + b)) ≈ (a * a + a * b) := Q'.mul_add_eqv a a b
      have e2 : (b * (a + b)) ≈ (b * a + b * b) := Q'.mul_add_eqv b a b
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ e1)
          (Q'.add_eqv_congr_left _ _ _ e2)) ?_
      have e3 : (b * a) ≈ (a * b) := Q'.mul_comm_eqv b a
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_right _ _ _ e3)) ?_
      calc (a * a + a * b) + (a * b + b * b)
          ≈ a * a + (a * b + (a * b + b * b)) := Q'.add_assoc_eqv (a * a) (a * b) (a * b + b * b)
        _ ≈ a * a + ((a * b + a * b) + b * b) :=
            Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (a * b) (a * b) (b * b)))
        _ ≈ a * a + ((b * b) + (a * b + a * b)) :=
            Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv (a * b + a * b) (b * b))
        _ ≈ a * a + (b * b + (a * b + a * b)) := Q'.eqv_refl _
        _ ≈ (a * a + b * b) + (a * b + a * b) :=
            Q'.eqv_symm (Q'.add_assoc_eqv (a * a) (b * b) (a * b + a * b))
        _ ≈ (a * b + a * b) + (a * a + b * b) := Q'.add_comm_eqv (a * a + b * b) (a * b + a * b)
    · exact Q'.add_assoc_eqv (a * b + a * b) (a * a + b * b) (-((c + c) * (c + c))))

/-- The EXACT rational residue `residueVal = rad_+ + rad_- − 2·oms`. -/
def residueVal (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) : Q' :=
  bdyOneMinusSq M (k + 1) hM (Nat.succ_pos k) hk1n
    + bdyOneMinusSq M k hM hk0 hkn
    + (-(oneMinusSqNode M k hM hkn + oneMinusSqNode M k hM hkn))

/-- The explicit constant `−2/M²` that `residueVal` equals. -/
def negTwoDeltaSq (M : Nat) (hM : 0 < M) : Q' :=
  Q'.mkPos (-2) (M * M) (Nat.mul_pos hM hM)

/-- **`residueVal ≈ −2δ²`** (centered second difference of the radicand `= −2/M²`). -/
theorem residueVal_eq (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    residueVal M hM k hk0 hkn hk1n ≈ negTwoDeltaSq M hM := by
  have hbp : bdyOneMinusSq M (k + 1) hM (Nat.succ_pos k) hk1n
      = Q'.mkPos (bdyNum M (k + 1)) (M * M) (Nat.mul_pos hM hM) := rfl
  have hbm : bdyOneMinusSq M k hM hk0 hkn
      = Q'.mkPos (bdyNum M k) (M * M) (Nat.mul_pos hM hM) := rfl
  have hom : oneMinusSqNode M k hM hkn
      = Q'.mkPos (omsNum M k) (M * M) (Nat.mul_pos hM hM) := rfl
  have hnum : bdyNum M (k + 1) + bdyNum M k + (-(omsNum M k + omsNum M k)) = (-2 : Int) := by
    show ((M : Int) * (M : Int) - (2 * ((k + 1 : Nat) : Int) - (M : Int))
            * (2 * ((k + 1 : Nat) : Int) - (M : Int)))
        + ((M : Int) * (M : Int) - (2 * (k : Int) - (M : Int)) * (2 * (k : Int) - (M : Int)))
        + (-(((M : Int) * (M : Int)
              - (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)))
            + ((M : Int) * (M : Int)
              - (2 * (k : Int) + 1 - (M : Int)) * (2 * (k : Int) + 1 - (M : Int)))))
        = (-2 : Int)
    have hcast1 : (2 * ((k + 1 : Nat) : Int) - (M : Int))
        = ((2 * (k : Int) + 1 - (M : Int)) + 1) := by push_cast; omega
    have hcast2 : (2 * (k : Int) - (M : Int))
        = ((2 * (k : Int) + 1 - (M : Int)) - 1) := by omega
    rw [hcast1, hcast2]
    generalize hA : (2 * (k : Int) + 1 - (M : Int)) = A
    have e1 : (A + 1) * (A + 1) = A * A + 2 * A + 1 := by
      have h1 : (A + 1) * (A + 1) = A * (A + 1) + 1 * (A + 1) := Int.add_mul A 1 (A + 1)
      have h2 : A * (A + 1) = A * A + A * 1 := Int.mul_add A A 1
      omega
    have e2 : (A - 1) * (A - 1) = A * A - 2 * A + 1 := by
      have h1 : (A - 1) * (A - 1) = A * (A - 1) - 1 * (A - 1) := Int.sub_mul A 1 (A - 1)
      have h2 : A * (A - 1) = A * A - A * 1 := Int.mul_sub A A 1
      omega
    rw [e1, e2]; omega
  rw [residueVal, hbp, hbm, hom]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _
        (SemicircleIntegral.mkPos_add_same_den (omsNum M k) (omsNum M k) (M * M)
          (Nat.mul_pos hM hM)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (?_ : (-(Q'.mkPos (omsNum M k + omsNum M k) (M * M) (Nat.mul_pos hM hM)))
          ≈ Q'.mkPos (-(omsNum M k + omsNum M k)) (M * M) (Nat.mul_pos hM hM))) ?_
  · show (-(Q'.mkPos (omsNum M k + omsNum M k) (M * M) (Nat.mul_pos hM hM))).num
          * ((Q'.mkPos (-(omsNum M k + omsNum M k)) (M * M) (Nat.mul_pos hM hM)).den : Int)
        = (Q'.mkPos (-(omsNum M k + omsNum M k)) (M * M) (Nat.mul_pos hM hM)).num
          * ((-(Q'.mkPos (omsNum M k + omsNum M k) (M * M) (Nat.mul_pos hM hM))).den : Int)
    rfl
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (SemicircleIntegral.mkPos_add_same_den (bdyNum M (k + 1)) (bdyNum M k) (M * M)
        (Nat.mul_pos hM hM))) ?_
  refine Q'.eqv_trans _ _ _
    (SemicircleIntegral.mkPos_add_same_den (bdyNum M (k + 1) + bdyNum M k)
      (-(omsNum M k + omsNum M k)) (M * M) (Nat.mul_pos hM hM)) ?_
  show Q'.mkPos (bdyNum M (k + 1) + bdyNum M k + (-(omsNum M k + omsNum M k))) (M * M)
        (Nat.mul_pos hM hM)
      ≈ negTwoDeltaSq M hM
  rw [hnum]; exact Q'.eqv_refl _

/-- `(a + b) ≈ addNF [a, b]`. -/
theorem pair_addNF (a b : Q') : (a + b) ≈ Pivot3.addNF [a, b] := by
  show (a + b) ≈ (a + (b + 0))
  exact Q'.add_eqv_congr_left a b (b + 0) (Q'.eqv_symm (QPoly.q_add_zero_eqv b))

/-- `a + (b + c) ≈ addNF [a, b, c]`. -/
theorem triR_addNF (a b c : Q') : (a + (b + c)) ≈ Pivot3.addNF [a, b, c] := by
  show (a + (b + c)) ≈ (a + (b + (c + 0)))
  exact Q'.add_eqv_congr_left a (b + c) (b + (c + 0))
    (Q'.add_eqv_congr_left b c (c + 0) (Q'.eqv_symm (QPoly.q_add_zero_eqv c)))

/-- `addNF L1 + addNF L2 ≈ addNF (L1 ++ L2)`. -/
theorem addNF_combine (L1 L2 : List Q') :
    (Pivot3.addNF L1 + Pivot3.addNF L2) ≈ Pivot3.addNF (L1 ++ L2) :=
  Q'.eqv_symm (Pivot3.addNF_append L1 L2)

/-- The 8-atom reorder used in `symmE_sub_ring`. -/
theorem symmReorderProof (P aa bb q : Q') :
    (((P + P) + ((aa + bb) + ((-(q + q)) + (-(q + q)))))
        + (((-P) + q) + ((-P) + q)))
    ≈ (((aa + bb) + (((-(q + q)) + (-(q + q))) + (q + q)))
        + ((P + (-P)) + (P + (-P)))) := by
  have hL : (((P + P) + ((aa + bb) + ((-(q + q)) + (-(q + q)))))
        + (((-P) + q) + ((-P) + q)))
      ≈ Pivot3.addNF [P, P, aa + bb, -(q + q), -(q + q), -P, q, -P, q] := by
    have hB1 : ((P + P) + ((aa + bb) + ((-(q + q)) + (-(q + q)))))
        ≈ Pivot3.addNF [P, P, aa + bb, -(q + q), -(q + q)] := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (pair_addNF P P)
          (triR_addNF (aa + bb) (-(q + q)) (-(q + q)))) ?_
      exact addNF_combine [P, P] [aa + bb, -(q + q), -(q + q)]
    have hB2 : (((-P) + q) + ((-P) + q)) ≈ Pivot3.addNF [-P, q, -P, q] := by
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (pair_addNF (-P) q) (pair_addNF (-P) q)) ?_
      exact addNF_combine [-P, q] [-P, q]
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hB1 hB2) ?_
    exact addNF_combine [P, P, aa + bb, -(q + q), -(q + q)] [-P, q, -P, q]
  have hR : (((aa + bb) + (((-(q + q)) + (-(q + q))) + (q + q)))
        + ((P + (-P)) + (P + (-P))))
      ≈ Pivot3.addNF [aa + bb, -(q + q), -(q + q), q, q, P, -P, P, -P] := by
    have hB3 : ((aa + bb) + (((-(q + q)) + (-(q + q))) + (q + q)))
        ≈ Pivot3.addNF [aa + bb, -(q + q), -(q + q), q, q] := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.add_assoc_eqv (-(q + q)) (-(q + q)) (q + q))) ?_
      show ((aa + bb) + ((-(q + q)) + ((-(q + q)) + (q + q))))
          ≈ ((aa + bb) + ((-(q + q)) + ((-(q + q)) + (q + (q + 0)))))
      exact Q'.add_eqv_congr_left _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_symm (QPoly.q_add_zero_eqv q)))))
    have hB4 : ((P + (-P)) + (P + (-P))) ≈ Pivot3.addNF [P, -P, P, -P] := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (pair_addNF P (-P)) (pair_addNF P (-P))) ?_
      exact addNF_combine [P, -P] [P, -P]
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hB3 hB4) ?_
    exact addNF_combine [aa + bb, -(q + q), -(q + q), q, q] [P, -P, P, -P]
  refine Q'.eqv_trans _ _ _ hL ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hR)
  refine Pivot3.addNF_perm ?_
  refine List.Perm.trans (List.Perm.cons P
    (List.Perm.swap (aa + bb) P [-(q + q), -(q + q), -P, q, -P, q])) ?_
  refine List.Perm.trans (List.Perm.swap (aa + bb) P [P, -(q + q), -(q + q), -P, q, -P, q]) ?_
  refine List.Perm.cons (aa + bb) ?_
  refine List.Perm.trans (List.Perm.cons P
    (List.Perm.swap (-(q + q)) P [-(q + q), -P, q, -P, q])) ?_
  refine List.Perm.trans (List.Perm.swap (-(q + q)) P [P, -(q + q), -P, q, -P, q]) ?_
  refine List.Perm.cons (-(q + q)) ?_
  refine List.Perm.trans (List.Perm.cons P
    (List.Perm.swap (-(q + q)) P [-P, q, -P, q])) ?_
  refine List.Perm.trans (List.Perm.swap (-(q + q)) P [P, -P, q, -P, q]) ?_
  refine List.Perm.cons (-(q + q)) ?_
  refine List.Perm.trans (List.Perm.cons P
    (List.Perm.cons P (List.Perm.swap q (-P) [-P, q]))) ?_
  refine List.Perm.trans (List.Perm.cons P (List.Perm.swap q P [-P, -P, q])) ?_
  refine List.Perm.trans (List.Perm.swap q P [P, -P, -P, q]) ?_
  refine List.Perm.cons q ?_
  refine List.Perm.trans (List.Perm.cons P
    (List.Perm.cons P (List.Perm.cons (-P) (List.Perm.swap q (-P) [])))) ?_
  refine List.Perm.trans (List.Perm.cons P (List.Perm.cons P (List.Perm.swap q (-P) [-P]))) ?_
  refine List.Perm.trans (List.Perm.cons P (List.Perm.swap q P [-P, -P])) ?_
  refine List.Perm.trans (List.Perm.swap q P [P, -P, -P]) ?_
  refine List.Perm.cons q ?_
  refine List.Perm.cons P ?_
  exact (List.Perm.swap P (-P) [-P]).symm

/-- The pure abelian-group identity behind the cancellation. -/
theorem symmE_sub_ring (P aa bb q : Q') :
    (((P + P) + ((aa + bb) + (-((q + q) + (q + q)))))
      + (-((P + (-q)) + (P + (-q)))))
    ≈ ((aa + bb) + (-(q + q))) := by
  have hneg : (-((P + (-q)) + (P + (-q)))) ≈ (((-P) + q) + ((-P) + q)) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (P + (-q)) (P + (-q))) ?_
    have hn : (-(P + (-q))) ≈ ((-P) + q) :=
      Q'.eqv_trans _ _ _ (Q'.neg_add_eqv P (-q))
        (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv q))
    exact Q'.add_eqv_congr' hn hn
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hneg) ?_
  have hnq : (-((q + q) + (q + q))) ≈ ((-(q + q)) + (-(q + q))) :=
    Q'.neg_add_eqv (q + q) (q + q)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _ hnq))) ?_
  have hPP : (P + (-P)) ≈ (0 : Q') := Q'.add_neg_self_eqv P
  have hNq : ((-(q + q)) + (q + q)) ≈ (0 : Q') := Q'.neg_add_self_eqv (q + q)
  have hreorder :
      (((P + P) + ((aa + bb) + ((-(q + q)) + (-(q + q)))))
          + (((-P) + q) + ((-P) + q)))
      ≈ (((aa + bb) + (((-(q + q)) + (-(q + q))) + (q + q)))
          + ((P + (-P)) + (P + (-P)))) :=
    symmReorderProof P aa bb q
  calc (((P + P) + ((aa + bb) + ((-(q + q)) + (-(q + q)))))
          + (((-P) + q) + ((-P) + q)))
      ≈ ((aa + bb) + (((-(q + q)) + (-(q + q))) + (q + q)))
          + ((P + (-P)) + (P + (-P))) := hreorder
    _ ≈ ((aa + bb) + (-(q + q))) + ((0 : Q') + (0 : Q')) := by
        refine Q'.add_eqv_congr' ?_ (Q'.add_eqv_congr' hPP hPP)
        refine Q'.add_eqv_congr_left _ _ _ ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (-(q + q)) (-(q + q)) (q + q)) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hNq) ?_
        exact QPoly.q_add_zero_eqv (-(q + q))
    _ ≈ ((aa + bb) + (-(q + q))) := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (QPoly.q_add_zero_eqv (0 : Q'))) ?_
        exact QPoly.q_add_zero_eqv ((aa + bb) + (-(q + q)))

/-- `midReal = (s_+² + s_-²) − (s_k² + s_k²)`. -/
def midReal (M : Nat) (hM : 0 < M) (k : Nat) : CReal :=
  CReal.add
    (CReal.add (CReal.mul (bdyRadical M hM (k + 1)) (bdyRadical M hM (k + 1)))
      (CReal.mul (bdyRadical M hM k) (bdyRadical M hM k)))
    (CReal.neg (CReal.add (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))
      (CReal.mul (nodeWeight M hM k) (nodeWeight M hM k))))

/-- **`symmE + (−(subDiff + subDiff)) ≈ midReal`.** -/
theorem symmE_sub_eq_midReal (M : Nat) (hM : 0 < M) (k : Nat) :
    CReal.Equiv
      (CReal.add (symmE M hM k)
        (CReal.neg (CReal.add (subDiff M hM k) (subDiff M hM k))))
      (midReal M hM k) :=
  SumOfSquares.Equiv_of_approx_eqv (fun p => by
    show ((((bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM k).approx p)
            + ((bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM k).approx p))
          + ((((bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM (k + 1)).approx p)
              + ((bdyRadical M hM k).approx p * (bdyRadical M hM k).approx p))
            + (-(((nodeWeight M hM k).approx p + (nodeWeight M hM k).approx p)
                * ((nodeWeight M hM k).approx p + (nodeWeight M hM k).approx p)))))
        + (-((((bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM k).approx p)
                + (-((nodeWeight M hM k).approx p * (nodeWeight M hM k).approx p)))
            + (((bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM k).approx p)
                + (-((nodeWeight M hM k).approx p * (nodeWeight M hM k).approx p)))))
        ≈ ((((bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM (k + 1)).approx p)
              + ((bdyRadical M hM k).approx p * (bdyRadical M hM k).approx p))
            + (-(((nodeWeight M hM k).approx p * (nodeWeight M hM k).approx p)
                + ((nodeWeight M hM k).approx p * (nodeWeight M hM k).approx p))))
    generalize hc : (nodeWeight M hM k).approx p = c
    have hcc : ((c + c) * (c + c)) ≈ ((c * c + c * c) + (c * c + c * c)) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv c c (c + c)) ?_
      exact Q'.add_eqv_congr' (Q'.mul_add_eqv c c c) (Q'.mul_add_eqv c c c)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hcc)))) ?_
    generalize (bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM k).approx p = P
    generalize (bdyRadical M hM (k + 1)).approx p * (bdyRadical M hM (k + 1)).approx p = aa
    generalize (bdyRadical M hM k).approx p * (bdyRadical M hM k).approx p = bb
    generalize c * c = q
    exact symmE_sub_ring P aa bb q)

/-- **`midReal ≈ ofQ' residueVal`.** -/
theorem midReal_collapse (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    CReal.Equiv (midReal M hM k) (CReal.ofQ' (residueVal M hM k hk0 hkn hk1n)) := by
  have hsp := ChebOrthoRadSecondDiff.bdyRadical_sq_collapse M hM (k + 1) (Nat.succ_pos k) hk1n
  have hsm := ChebOrthoRadSecondDiff.bdyRadical_sq_collapse M hM k hk0 hkn
  have hnd := ChebOrthoLeadingModel.node_sq_collapse M hM k hkn
  unfold midReal
  refine CReal.Equiv.trans
    (Pivot2.add_congr (Pivot2.add_congr hsp hsm)
      (Pivot2.neg_congr (Pivot2.add_congr hnd hnd))) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  show ((bdyOneMinusSq M (k + 1) hM (Nat.succ_pos k) hk1n + bdyOneMinusSq M k hM hk0 hkn)
        + (-(oneMinusSqNode M k hM hkn + oneMinusSqNode M k hM hkn)))
      ≈ residueVal M hM k hk0 hkn hk1n
  exact Q'.eqv_refl _

/-- **`D · S ≈ (subDiff + subDiff) + ofQ'(−2δ²)`** (bound-independent Equiv). -/
theorem DS_collapse (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    CReal.Equiv (CReal.mul (symmD M hM k) (symmS M hM k))
      (CReal.add (CReal.add (subDiff M hM k) (subDiff M hM k))
        (CReal.ofQ' (negTwoDeltaSq M hM))) := by
  refine CReal.Equiv.trans (DS_eq_E M hM k) ?_
  have hsplit : CReal.Equiv (symmE M hM k)
      (CReal.add (CReal.add (subDiff M hM k) (subDiff M hM k)) (midReal M hM k)) := by
    refine CReal.Equiv.trans ?_
      (Pivot2.add_congr (Pivot2.equiv_refl _) (symmE_sub_eq_midReal M hM k))
    refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
    show (symmE M hM k).approx p
        ≈ (((subDiff M hM k).add (subDiff M hM k)).approx p
            + ((symmE M hM k).approx p + (-(((subDiff M hM k).add (subDiff M hM k)).approx p))))
    generalize (symmE M hM k).approx p = E
    generalize ((subDiff M hM k).add (subDiff M hM k)).approx p = T
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv E (-T))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv T (-T) E)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv T)) ?_
    exact QPoly.q_zero_add_eqv E
  refine CReal.Equiv.trans hsplit ?_
  refine Pivot2.add_congr (Pivot2.equiv_refl _) ?_
  refine CReal.Equiv.trans (midReal_collapse M hM k hk0 hkn hk1n) ?_
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => residueVal_eq M hM k hk0 hkn hk1n)

/-- `2δ² = 2/M²`. -/
def twoDeltaSq (M : Nat) (hM : 0 < M) : Q' :=
  Q'.mkPos 2 (M * M) (Nat.mul_pos hM hM)

theorem twoDeltaSq_nonneg (M : Nat) (hM : 0 < M) : (0 : Q') ≤ twoDeltaSq M hM := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (Q'.mkPos 2 (M * M) (Nat.mul_pos hM hM)).num
  rw [Q'.mkPos_num]; decide

/-- `|ofQ'(−2δ²)| ≤ 2δ²`. -/
theorem negTwoDeltaSq_AbsLeRat (M : Nat) (hM : 0 < M) :
    AbsLeRat (CReal.ofQ' (negTwoDeltaSq M hM)) (twoDeltaSq M hM) := by
  have hNn : (negTwoDeltaSq M hM).num = (-2 : Int) := by
    show (Q'.mkPos (-2) (M * M) (Nat.mul_pos hM hM)).num = (-2 : Int); rw [Q'.mkPos_num]
  have hNd : ((negTwoDeltaSq M hM).den : Int) = ((M * M : Nat) : Int) := by
    show ((Q'.mkPos (-2) (M * M) (Nat.mul_pos hM hM)).den : Int) = ((M * M : Nat) : Int)
    rw [Q'.mkPos_den]
  have hTn : (twoDeltaSq M hM).num = (2 : Int) := by
    show (Q'.mkPos 2 (M * M) (Nat.mul_pos hM hM)).num = (2 : Int); rw [Q'.mkPos_num]
  have hTd : ((twoDeltaSq M hM).den : Int) = ((M * M : Nat) : Int) := by
    show ((Q'.mkPos 2 (M * M) (Nat.mul_pos hM hM)).den : Int) = ((M * M : Nat) : Int)
    rw [Q'.mkPos_den]
  have hMM : (0 : Int) ≤ ((M * M : Nat) : Int) := Int.natCast_nonneg _
  refine ChebOrthoGradedClose.AbsLeRat.ofQ' ?_ ?_
  · show (negTwoDeltaSq M hM).num * ((twoDeltaSq M hM).den : Int)
        ≤ (twoDeltaSq M hM).num * ((negTwoDeltaSq M hM).den : Int)
    rw [hNn, hTd, hTn, hNd]
    exact Int.mul_le_mul_of_nonneg_right (by decide : (-2 : Int) ≤ 2) hMM
  · show (-(negTwoDeltaSq M hM)).num * ((twoDeltaSq M hM).den : Int)
        ≤ (twoDeltaSq M hM).num * ((-(negTwoDeltaSq M hM)).den : Int)
    have hnegn : (-(negTwoDeltaSq M hM)).num = -(negTwoDeltaSq M hM).num := rfl
    have hnegd : ((-(negTwoDeltaSq M hM)).den : Int) = ((negTwoDeltaSq M hM).den : Int) := rfl
    rw [hnegn, hnegd, hNn, hTd, hTn, hNd]
    exact Int.le_refl _

/-- **THE TIGHT NUMERATOR BOUND.**  `|D · S| ≤ 2·subSecondQuot_tight + 2δ²`.  Identical to
the loose `DS_AbsLeRat`, but with `subSecondDiff_tight_AbsLeRat` feeding the inner bound. -/
theorem DS_AbsLeRat_tight (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) :
    AbsLeRat (CReal.mul (symmD M hM k) (symmS M hM k))
      ((subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn) + twoDeltaSq M hM) := by
  have hsub : AbsLeRat (CReal.add (subDiff M hM k) (subDiff M hM k))
      (subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn) :=
    ChebOrthoGradedClose.AbsLeRat.add
      (subSecondDiff_tight_AbsLeRat M hM k hk0 hkn hk1n)
      (subSecondDiff_tight_AbsLeRat M hM k hk0 hkn hk1n)
  have hconst : AbsLeRat (CReal.ofQ' (negTwoDeltaSq M hM)) (twoDeltaSq M hM) :=
    negTwoDeltaSq_AbsLeRat M hM
  have hbnd : AbsLeRat
      (CReal.add (CReal.add (subDiff M hM k) (subDiff M hM k))
        (CReal.ofQ' (negTwoDeltaSq M hM)))
      ((subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn) + twoDeltaSq M hM) :=
    ChebOrthoGradedClose.AbsLeRat.add hsub hconst
  exact ChebOrthoCancelDiv.AbsLeRat.of_equiv (DS_collapse M hM k hk0 hkn hk1n) hbnd

/-- **Pointwise lower bound on the symmetric sum `S = s_+ + s_- + 2 s_k`.** -/
theorem symmS_lower (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hj : 2 ≤ jdist M k) :
    ∀ n, recipWitness M (jdist M k) hM ≤ (symmS M hM k).approx n := by
  intro n
  show recipWitness M (jdist M k) hM
      ≤ (((bdyRadical M hM (k + 1)).approx n + (bdyRadical M hM k).approx n)
          + ((nodeWeight M hM k).approx n + (nodeWeight M hM k).approx n))
  have hsm : recipWitness M (jdist M k) hM ≤ (bdyRadical M hM k).approx n := by
    rw [ChebOrthoRemainder.bdyRadical_interior M hM k hk0 hkn]
    show recipWitness M (jdist M k) hM
        ≤ (CReal.sqrtFrom (bdyOneMinusSq M k hM hk0 hkn) (SemicircleIntegral.nodeLB M hM)
            (ChebOrthoMidpoint.bdyOneMinusSq_pos hM hk0 hkn) (SemicircleIntegral.nodeLB_pos hM)
            (ChebOrthoMidpoint.bdyLB_sq_le hM hk0 hkn)).approx n
    rw [CReal.sqrtFrom_approx]
    exact CReal.heronSeq_lb (bdyOneMinusSq M k hM hk0 hkn) (recipWitness M (jdist M k) hM)
      (ChebOrthoMidpoint.bdyOneMinusSq_pos hM hk0 hkn)
      (recipWitness_pos M (jdist M k) hM hj)
      (recipWitness_sq_le M hM k hk0 hkn hj) n
  have hsp : (0 : Q') ≤ (bdyRadical M hM (k + 1)).approx n :=
    ChebOrthoInterior.bdyRadical_approx_nonneg M hM (k + 1) n
  have hnd : (0 : Q') ≤ (nodeWeight M hM k).approx n :=
    Q'.le_trans' _ _ _ (Q'.le_of_lt (SemicircleIntegral.nodeLB_pos hM))
      (ChebOrthoLeadingModel.nodeWeight_approx_ge M hM k hkn n)
  have hsum1 : recipWitness M (jdist M k) hM
      ≤ ((bdyRadical M hM (k + 1)).approx n + (bdyRadical M hM k).approx n) := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_zero_add_eqv _))) ?_
    exact Q'.add_le_add hsp hsm
  have hsum2 : (0 : Q') ≤ ((nodeWeight M hM k).approx n + (nodeWeight M hM k).approx n) :=
    Q'.zero_le_add _ _ hnd hnd
  refine Q'.le_trans' _ _ _ hsum1 ?_
  exact Q'.add_le_self_of_nonneg _ _ hsum2

/-- **THE TIGHT SYMMETRIC SECOND-DIFFERENCE BOUND (the tight outer division).**  For an
interior cell `0 < k`, `k+1 < M`, `2 ≤ jdist M k`,

    `|s_+ + s_- − 2 s_k| ≤ symmQuot_tight`,
    `symmQuot_tight = (2·subSecondQuot_tight + 2δ²)·(1/recipWitness)`.

The genuine `1/jdist²` scale: numerator `~1/(M·jdist)`, outer reciprocal `1/recipWitness
~ M/jdist`, product `~1/jdist²`.  Reciprocal-free, via `AbsLeRat.div_of_mul_ge` with the
TIGHT numerator bound `DS_AbsLeRat_tight`. -/
theorem symmSecondDiff_tight_AbsLeRat (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hk1n : k + 1 < M) (hj : 2 ≤ jdist M k) :
    AbsLeRat (symmD M hM k)
      (((subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn) + twoDeltaSq M hM)
        * Q'.recipPos (recipWitness M (jdist M k) hM) (recipWitness_pos M (jdist M k) hM hj)) := by
  refine ChebOrthoCancelDiv.AbsLeRat.div_of_mul_ge
    (D := symmD M hM k) (S := symmS M hM k)
    (K := (subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn) + twoDeltaSq M hM)
    (L := recipWitness M (jdist M k) hM)
    (KL := ((subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn) + twoDeltaSq M hM)
        * Q'.recipPos (recipWitness M (jdist M k) hM) (recipWitness_pos M (jdist M k) hM hj))
    (DS_AbsLeRat_tight M hM k hk0 hkn hk1n)
    (symmS_lower M hM k hk0 hkn hj)
    (recipWitness_pos M (jdist M k) hM hj)
    ?_ ?_
  · have hKnn : (0 : Q')
        ≤ (subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn) + twoDeltaSq M hM :=
      Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (subSecondQuot_tight_nonneg M k hM hkn)
        (subSecondQuot_tight_nonneg M k hM hkn)) (twoDeltaSq_nonneg M hM)
    have hRnn : (0 : Q') ≤ Q'.recipPos (recipWitness M (jdist M k) hM)
        (recipWitness_pos M (jdist M k) hM hj) :=
      Q'.le_of_lt (Q'.recipPos_pos _ _)
    exact Q'.mul_nonneg _ _ hKnn hRnn
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv
        ((subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn) + twoDeltaSq M hM)
        (Q'.recipPos (recipWitness M (jdist M k) hM) (recipWitness_pos M (jdist M k) hM hj))
        (recipWitness M (jdist M k) hM)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
          (Q'.mul_recipPos_eqv (recipWitness M (jdist M k) hM)
            (recipWitness_pos M (jdist M k) hM hj)))) ?_
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.one_mul_eqv _)

#print axioms DS_collapse
#print axioms symmS_lower
#print axioms DS_AbsLeRat_tight
#print axioms symmSecondDiff_tight_AbsLeRat

/-! ## 4. The explicit `1/jdist²` scale of the symmetric second difference -/

/-- `jdist M k ≤ M` (the boundary distance is at most the cell count). -/
theorem jdist_le_M (M k : Nat) (hkn : k < M) : jdist M k ≤ M := by
  show Nat.min (k + 1) (M - k) ≤ M
  have : Nat.min (k + 1) (M - k) ≤ M - k := Nat.min_le_right _ _
  omega

/-- `twoDeltaSq = 2/M² ≤ 2/(M·jdist)` (since `jdist ≤ M`). -/
theorem twoDeltaSq_le (M k : Nat) (hM : 0 < M) (hkn : k < M) :
    twoDeltaSq M hM ≤ Q'.mkPos 2 (M * jdist M k) (Nat.mul_pos hM (jdist_pos hkn)) := by
  show (twoDeltaSq M hM).num * ((Q'.mkPos 2 (M * jdist M k) _).den : Int)
      ≤ (Q'.mkPos 2 (M * jdist M k) _).num * ((twoDeltaSq M hM).den : Int)
  have hTn : (twoDeltaSq M hM).num = 2 := by
    show (Q'.mkPos 2 (M * M) (Nat.mul_pos hM hM)).num = 2; rw [Q'.mkPos_num]
  have hTd : ((twoDeltaSq M hM).den : Int) = ((M * M : Nat) : Int) := by
    show ((Q'.mkPos 2 (M * M) (Nat.mul_pos hM hM)).den : Int) = _; rw [Q'.mkPos_den]
  have hCn : (Q'.mkPos 2 (M * jdist M k) (Nat.mul_pos hM (jdist_pos hkn))).num = 2 := by
    rw [Q'.mkPos_num]
  have hCd : ((Q'.mkPos 2 (M * jdist M k) (Nat.mul_pos hM (jdist_pos hkn))).den : Int)
      = ((M * jdist M k : Nat) : Int) := by rw [Q'.mkPos_den]
  rw [hTn, hTd, hCn, hCd]
  -- 2·(M·jdist) ≤ 2·(M·M)  since jdist ≤ M.
  have hMj : ((M * jdist M k : Nat) : Int) = (M : Int) * (jdist M k : Int) := by push_cast; rfl
  have hMM : ((M * M : Nat) : Int) = (M : Int) * (M : Int) := by push_cast; rfl
  rw [hMj, hMM]
  have hjM : (jdist M k : Int) ≤ (M : Int) := by exact_mod_cast jdist_le_M M k hkn
  have hM0 : (0 : Int) ≤ (M : Int) := Int.natCast_nonneg _
  have hstep : (M : Int) * (jdist M k : Int) ≤ (M : Int) * (M : Int) :=
    Int.mul_le_mul_of_nonneg_left hjM hM0
  exact Int.mul_le_mul_of_nonneg_left hstep (by decide)

/-- `mkPos a D + mkPos b D ≈ mkPos (a+b) D` (same-denominator add). -/
theorem mkPos_add (a b : Int) (D : Nat) (hD : 0 < D) :
    (Q'.mkPos a D hD + Q'.mkPos b D hD) ≈ Q'.mkPos (a + b) D hD :=
  SemicircleIntegral.mkPos_add_same_den a b D hD

/-- **The explicit `1/jdist²` symmetric-second-difference scale.**  The symmetric-leg
quotient `symmQuot_tight = (2·subSecondQuot_tight + 2δ²)·(1/recipWitness)` is bounded by
`22/jdist²`:

    `(2·subSecondQuot_tight + 2δ²)·(1/recipWitness) ≤ 22/jdist²`.

PROOF: the numerator `≤ 22/(M·jdist)` (`subSecondQuot_tight ≤ 10/(M·jdist)` twice +
`twoDeltaSq ≤ 2/(M·jdist)`), the outer reciprocal `1/recipWitness = M/⌊√(4(j−1)j)⌋ ≤ M/jdist`
(`isqrt_jdistRad_ge_jdist`), and the product `22/(M·jdist)·M/jdist = 22M/(M·jdist²) ≤ 22/jdist²`
(`Int` cross-multiplication). -/
theorem symmQuot_tight_le_recip_sq (M : Nat) (hM : 0 < M) (k : Nat)
    (hkn : k < M) (hk1n : k + 1 < M) (hj : 2 ≤ jdist M k) :
    (((subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn) + twoDeltaSq M hM)
        * Q'.recipPos (recipWitness M (jdist M k) hM) (recipWitness_pos M (jdist M k) hM hj))
      ≤ Q'.mkPos 22 (jdist M k * jdist M k)
          (Nat.mul_pos (jdist_pos hkn) (jdist_pos hkn)) := by
  -- (1) numerator ≤ 22/(M·jdist)
  have hMjpos : 0 < M * jdist M k := Nat.mul_pos hM (jdist_pos hkn)
  have hq10 : subSecondQuot_tight M k hM hkn
      ≤ Q'.mkPos 10 (M * jdist M k) hMjpos :=
    subSecondQuot_tight_le_recip M hM k hkn hk1n
  have hsumQ : (subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn)
      ≤ Q'.mkPos 20 (M * jdist M k) hMjpos := by
    refine Q'.le_trans' _ _ _ (Q'.add_le_add hq10 hq10) ?_
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _ (mkPos_add 10 10 (M * jdist M k) hMjpos) ?_
    show (Q'.mkPos (10 + 10) (M * jdist M k) hMjpos).num
          * ((Q'.mkPos 20 (M * jdist M k) hMjpos).den : Int)
        = (Q'.mkPos 20 (M * jdist M k) hMjpos).num
          * ((Q'.mkPos (10 + 10) (M * jdist M k) hMjpos).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den,
      show (10 + 10 : Int) = 20 from by decide]
  have hnumLe : ((subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn)
        + twoDeltaSq M hM)
      ≤ Q'.mkPos 22 (M * jdist M k) hMjpos := by
    refine Q'.le_trans' _ _ _ (Q'.add_le_add hsumQ (twoDeltaSq_le M k hM hkn)) ?_
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _ (mkPos_add 20 2 (M * jdist M k) hMjpos) ?_
    show (Q'.mkPos (20 + 2) (M * jdist M k) hMjpos).num
          * ((Q'.mkPos 22 (M * jdist M k) hMjpos).den : Int)
        = (Q'.mkPos 22 (M * jdist M k) hMjpos).num
          * ((Q'.mkPos (20 + 2) (M * jdist M k) hMjpos).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den,
      show (20 + 2 : Int) = 22 from by decide]
  -- (2) reciprocal ≤ M/jdist
  have hrecLe : Q'.recipPos (recipWitness M (jdist M k) hM) (recipWitness_pos M (jdist M k) hM hj)
      ≤ Q'.mkPos (M : Int) (jdist M k) (jdist_pos hkn) := by
    show (Q'.recipPos (recipWitness M (jdist M k) hM) _).num
          * ((Q'.mkPos (M : Int) (jdist M k) (jdist_pos hkn)).den : Int)
        ≤ (Q'.mkPos (M : Int) (jdist M k) (jdist_pos hkn)).num
          * ((Q'.recipPos (recipWitness M (jdist M k) hM) _).den : Int)
    rw [Q'.recipPos_num, Q'.recipPos_den, Q'.mkPos_num, Q'.mkPos_den]
    -- recipWitness.den = M ; recipWitness.num = ⌊√(4(j−1)j)⌋.
    have hRWd : ((recipWitness M (jdist M k) hM).den : Int) = (M : Int) := by
      show ((Q'.mkPos ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k)) : Int) M hM).den : Int) = (M : Int)
      rw [Q'.mkPos_den]
    have hRWn : (recipWitness M (jdist M k) hM).num
        = ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k)) : Int) := by
      show (Q'.mkPos ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k)) : Int) M hM).num = _
      rw [Q'.mkPos_num]
    rw [hRWd, hRWn]
    -- goal: M·jdist ≤ M·⌊√(4(j−1)j)⌋   (jdist ≤ a)
    have hja : jdist M k ≤ ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) :=
      ChebOrthoFinal.isqrt_jdistRad_ge_jdist (jdist M k) hj
    have hjaI : (jdist M k : Int)
        ≤ ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int) := by
      exact_mod_cast hja
    have hjdcast : ((jdist M k : Nat) : Int) = (jdist M k : Int) := by rfl
    exact Int.mul_le_mul_of_nonneg_left hjaI (Int.natCast_nonneg _)
  -- (3) multiply the two bounds, both nonneg
  have hnum0 : (0 : Q') ≤ Q'.mkPos 22 (M * jdist M k) hMjpos := by
    rw [Q'.zero_le_iff_num_nonneg]; rw [Q'.mkPos_num]; decide
  have hrec0 : (0 : Q') ≤ Q'.recipPos (recipWitness M (jdist M k) hM)
      (recipWitness_pos M (jdist M k) hM hj) := Q'.le_of_lt (Q'.recipPos_pos _ _)
  have hprod : ((subSecondQuot_tight M k hM hkn + subSecondQuot_tight M k hM hkn) + twoDeltaSq M hM)
        * Q'.recipPos (recipWitness M (jdist M k) hM) (recipWitness_pos M (jdist M k) hM hj)
      ≤ Q'.mkPos 22 (M * jdist M k) hMjpos
          * Q'.mkPos (M : Int) (jdist M k) (jdist_pos hkn) :=
    Q'.mul_le_mul_of_nonneg hnumLe hrecLe hnum0 hrec0
  refine Q'.le_trans' _ _ _ hprod ?_
  -- (4) 22/(M·jdist) · M/jdist = 22M/(M·jdist²) ≤ 22/jdist²
  show (Q'.mkPos 22 (M * jdist M k) hMjpos * Q'.mkPos (M : Int) (jdist M k) (jdist_pos hkn)).num
        * ((Q'.mkPos 22 (jdist M k * jdist M k) _).den : Int)
      ≤ (Q'.mkPos 22 (jdist M k * jdist M k) _).num
        * ((Q'.mkPos 22 (M * jdist M k) hMjpos * Q'.mkPos (M : Int) (jdist M k) (jdist_pos hkn)).den : Int)
  have hPn : (Q'.mkPos 22 (M * jdist M k) hMjpos
        * Q'.mkPos (M : Int) (jdist M k) (jdist_pos hkn)).num = 22 * (M : Int) := by
    show (Q'.mkPos 22 (M * jdist M k) hMjpos).num * (Q'.mkPos (M : Int) (jdist M k) (jdist_pos hkn)).num = _
    rw [Q'.mkPos_num, Q'.mkPos_num]
  have hPd : ((Q'.mkPos 22 (M * jdist M k) hMjpos
        * Q'.mkPos (M : Int) (jdist M k) (jdist_pos hkn)).den : Int)
      = ((M * jdist M k : Nat) : Int) * ((jdist M k : Nat) : Int) := by
    rw [Q'.mul_den_cast, Q'.mkPos_den, Q'.mkPos_den]
  have hQn : (Q'.mkPos 22 (jdist M k * jdist M k) (Nat.mul_pos (jdist_pos hkn) (jdist_pos hkn))).num = 22 := by
    rw [Q'.mkPos_num]
  have hQd : ((Q'.mkPos 22 (jdist M k * jdist M k) (Nat.mul_pos (jdist_pos hkn) (jdist_pos hkn))).den : Int)
      = ((jdist M k * jdist M k : Nat) : Int) := by rw [Q'.mkPos_den]
  rw [hPn, hPd, hQn, hQd]
  -- (22·M)·(jdist²) ≤ 22·((M·jdist)·jdist)  : both = 22·M·jdist² ; equal.
  have hcast1 : ((jdist M k * jdist M k : Nat) : Int)
      = (jdist M k : Int) * (jdist M k : Int) := by push_cast; rfl
  have hcast2 : ((M * jdist M k : Nat) : Int) = (M : Int) * (jdist M k : Int) := by push_cast; rfl
  have hcast3 : ((jdist M k : Nat) : Int) = (jdist M k : Int) := rfl
  rw [hcast1, hcast2, hcast3]
  -- (22*M)*(j*j) = 22*((M*j)*j)
  generalize (M : Int) = m
  generalize (jdist M k : Int) = j
  have : (22 * m) * (j * j) = 22 * ((m * j) * j) := by
    simp only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]
  rw [this]; exact Int.le_refl _

#print axioms jdist_le_M
#print axioms twoDeltaSq_le
#print axioms symmQuot_tight_le_recip_sq

end YMGap.Continuum.ChebOrthoTightModulus
