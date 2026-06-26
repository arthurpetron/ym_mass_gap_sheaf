/-
# The UNCONDITIONAL even off-diagonal Chebyshev-`U` orthogonality.

Both EVENTUAL per-leg remainder bounds are PROVED:
  * `ChebOrthoLegProof.eventualBrLegRemainder` (the smooth-bracket leg), and
  * `ChebOrthoBracketDecay.eventualRadLegRemainder` (the radical leg).

This file WIRES them, through the PROVED per-cell assembly chain
(`split_leg_decomp` → `leadingCancellation` → `secondDiff_reduce` →
`cellAdjR_split_Equiv`), into an EVENTUAL graded per-cell bound on the genuine
adjusted cells, and combines it (PIECEWISE with a crude all-`M` constant bound)
into the SATISFIABLE `ChebOrthoMidpoint.RealPerCellBudget` for every even `e ≥ 2`.
Feeding that into the PROVED `ChebOrthoMidpoint.offdiag_closed_of_realPerCell` (odd
case already unconditional) yields the UNCONDITIONAL off-diagonal orthogonality

    `∀ e, 1 ≤ e → ∃ L, CReal.ConvergesTo (seqOrth e) L ∧ CReal.Equiv L CReal.czero`,

i.e. `∫ U_e √ = 0` for all `e ≥ 1`, with NO remaining named hypothesis.

## DELIVERABLES
  * `cellAdj_crude` — the crude all-`M` constant cell bound `|cellAdjR| ≤ 2e+4`.
  * `cellAdj_graded_eventual` — the per-cell graded bound for `M₀ ≤ N+1`, all `k`.
  * `realPerCellBudget` — `ChebOrthoMidpoint.RealPerCellBudget e he` (even `e ≥ 2`).
  * `offdiag_orthogonality_unconditional` — THE PRIZE.

Axiom-gate: `[propext]` / `[propext, Quot.sound]` only.
-/

import YMGap.Continuum.ChebOrthoLegProof
import YMGap.Continuum.ChebOrthoBracketDecay
import YMGap.Continuum.ChebOrthoGradedClose
import YMGap.Continuum.ChebOrthoSecondDiff
import YMGap.Continuum.ChebOrthoLeadingModel
import YMGap.Continuum.ChebOrthoTaylor
import YMGap.Continuum.ChebOrthoFinal

namespace YMGap.Continuum.ChebOrthoOffDiagFinal

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag (orthTerm uNode seqOrth Gbracket Gfun)
open YMGap.Continuum.ChebOrthoMidpoint (cellAdjR GsampR gIncrR bdyRadical bdyPoint
  bdyOneMinusSq bdyNum)
open YMGap.Continuum.ChebOrthoGraded (gradedRate)
open YMGap.Continuum.ChebOrthoGradedClose (AbsLeRat)

local infix:50 " ≈ " => Q'.eqv

/-- `0 ≤ t * t` over `Int` (square nonnegativity), by sign cases. -/
theorem int_sq_nonneg (t : Int) : (0 : Int) ≤ t * t := by
  rcases Int.lt_or_le t 0 with ht | ht
  · have ht' : t ≤ 0 := Int.le_of_lt ht
    have h := Int.mul_nonneg (Int.neg_nonneg.mpr ht') (Int.neg_nonneg.mpr ht')
    rwa [Int.neg_mul_neg] at h
  · exact Int.mul_nonneg ht ht

/-! ## 1. The crude all-`M` constant per-cell bound `|cellAdjR| ≤ 2e+4` -/

/-- `bdyOneMinusSq M k ≤ 1` (the cell radicand `(M²−(2k−M)²)/M² ≤ 1`). -/
theorem bdyOneMinusSq_le_one (M k : Nat) (hM : 0 < M) (hk0 : 0 < k) (hkn : k < M) :
    bdyOneMinusSq M k hM hk0 hkn ≤ (1 : Q') := by
  show (bdyOneMinusSq M k hM hk0 hkn).num * ((1 : Q').den : Int)
      ≤ (1 : Q').num * ((bdyOneMinusSq M k hM hk0 hkn).den : Int)
  show (Q'.mkPos (bdyNum M k) (SemicircleIntegral.omsDen M)
        (SemicircleIntegral.omsDen_pos hM)).num * ((1 : Q').den : Int)
      ≤ (1 : Q').num * ((Q'.mkPos (bdyNum M k) (SemicircleIntegral.omsDen M)
        (SemicircleIntegral.omsDen_pos hM)).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  have hd1 : ((1 : Q').den : Int) = 1 := rfl
  have hn1 : (1 : Q').num = 1 := rfl
  rw [hd1, hn1, Int.mul_one, Int.one_mul]
  -- bdyNum M k = M² − (…)² ≤ M² = omsDen M  (omsDen M = M*M)
  have hden : (SemicircleIntegral.omsDen M : Int) = (M : Int) * (M : Int) := by
    show ((M * M : Nat) : Int) = (M : Int) * (M : Int)
    push_cast; rfl
  rw [hden]
  show (M : Int) * (M : Int)
      - (2 * (k : Int) - (M : Int)) * (2 * (k : Int) - (M : Int))
      ≤ (M : Int) * (M : Int)
  have hsq : (0 : Int) ≤ (2 * (k : Int) - (M : Int)) * (2 * (k : Int) - (M : Int)) :=
    int_sq_nonneg _
  omega

/-- `bdyNum M k = M * M` rewriting helper used in `omsDen`. -/
theorem omsDen_cast (M : Nat) : (SemicircleIntegral.omsDen M : Int) = (M : Int) * (M : Int) := by
  show ((M * M : Nat) : Int) = (M : Int) * (M : Int)
  push_cast; rfl

/-- **Universal `GsampR` constant bound `|GsampR e he M k| ≤ 1`** for EVERY `k`
(interior, endpoint, out-of-range).  Interior `0<k<M`: `GsampR_AbsLeRat` with the
radical bound `cs = 1` (`bdyOneMinusSq ≤ 1`), the result `½·(1·2) = 1 ≤ 1`.
Endpoints `k = 0`, `k = M` and out-of-range `k > M`: the radical is `czero`, so
`GsampR ≈ 0 ≤ 1`. -/
theorem GsampR_crude (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) :
    AbsLeRat (GsampR e he M hM k) (Q'.ofNat 1) := by
  by_cases hk0 : 0 < k
  · by_cases hkn : k < M
    · -- interior
      have hcs : (0 : Q') < (1 : Q') := by decide
      have hac : bdyOneMinusSq M k hM hk0 hkn ≤ (1 : Q') * (1 : Q') := by
        refine Q'.le_trans' _ _ _ (bdyOneMinusSq_le_one M k hM hk0 hkn) ?_
        exact Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv (1 : Q')))
      have hG := ChebOrthoGradedClose.GsampR_AbsLeRat e he M hM k hk0 hkn (1 : Q') hcs hac
      refine ChebOrthoGradedClose.AbsLeRat.mono hG ?_
      -- ½·(1·2) ≤ ofNat 1
      show Q'.mkPos 1 2 (by decide) * ((1 : Q') * (2 : Q')) ≤ Q'.ofNat 1
      decide
    · -- k ≥ M : out of range, GsampR ≈ 0 (bdyRadical = czero)
      have hcz : AbsLeRat (GsampR e he M hM k) (0 : Q') := by
        refine ChebOrthoGradedClose.AbsLeRat_zero_of_approx_zero (fun p => ?_)
        show ((Q'.mkPos 1 2 (by decide))
              * ((bdyRadical M hM k).approx p * (Gbracket e he (bdyPoint M hM k)))) ≈ 0
        rw [ChebOrthoGradedClose.bdyRadical_outrange M hM k (by omega : M ≤ k)]
        have hcz0 : ((CReal.czero).approx p) = (0 : Q') := rfl
        rw [hcz0]
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv (Gbracket e he (bdyPoint M hM k)))) ?_
        exact Q'.mul_zero_eqv (Q'.mkPos 1 2 (by decide))
      refine ChebOrthoGradedClose.AbsLeRat.mono hcz ?_
      show (0 : Q') ≤ Q'.ofNat 1
      decide
  · -- k = 0 : endpoint
    have hk : k = 0 := by omega
    refine ChebOrthoGradedClose.AbsLeRat.mono
      (ChebOrthoGradedClose.GsampR_endpoint_AbsLeRat e he M hM k (Or.inl hk)) ?_
    show (0 : Q') ≤ Q'.ofNat 1
    decide

/-- `lebW M · (ofNat(e+1) · 1) ≤ ofNat(2(e+1))`  (`lebW = 2/M ≤ 2`). -/
theorem orthBound_crude_le (e M : Nat) (hM : 0 < M) :
    SemicircleIntegral.lebW M hM * (Q'.ofNat (e + 1) * (1 : Q'))
      ≤ Q'.ofNat (2 * (e + 1)) := by
  show (SemicircleIntegral.lebW M hM * (Q'.ofNat (e + 1) * (1 : Q'))).num
        * ((Q'.ofNat (2 * (e + 1))).den : Int)
      ≤ (Q'.ofNat (2 * (e + 1))).num
        * ((SemicircleIntegral.lebW M hM * (Q'.ofNat (e + 1) * (1 : Q'))).den : Int)
  -- LHS num = 2·((e+1)·1) = 2(e+1)
  have hLnum : (SemicircleIntegral.lebW M hM * (Q'.ofNat (e + 1) * (1 : Q'))).num
      = (2 : Int) * ((e + 1 : Nat) : Int) := by
    show (SemicircleIntegral.lebW M hM).num * (Q'.ofNat (e + 1) * (1 : Q')).num
        = (2 : Int) * ((e + 1 : Nat) : Int)
    show (Q'.mkPos 2 M hM).num * ((Q'.ofNat (e + 1)).num * (1 : Q').num)
        = (2 : Int) * ((e + 1 : Nat) : Int)
    rw [Q'.mkPos_num]
    have hof : (Q'.ofNat (e + 1)).num = ((e + 1 : Nat) : Int) := rfl
    have h1 : (1 : Q').num = 1 := rfl
    rw [hof, h1, Int.mul_one]
  have hLden : ((SemicircleIntegral.lebW M hM * (Q'.ofNat (e + 1) * (1 : Q'))).den : Int)
      = (M : Int) := by
    rw [Q'.mul_den_cast]
    show ((SemicircleIntegral.lebW M hM).den : Int) * ((Q'.ofNat (e + 1) * (1 : Q')).den : Int)
        = (M : Int)
    show ((Q'.mkPos 2 M hM).den : Int) * ((Q'.ofNat (e + 1) * (1 : Q')).den : Int) = (M : Int)
    rw [Q'.mkPos_den, Q'.mul_den_cast]
    show (M : Int) * (((Q'.ofNat (e + 1)).den : Int) * ((1 : Q').den : Int)) = (M : Int)
    have hd1 : ((Q'.ofNat (e + 1)).den : Int) = 1 := rfl
    have hd2 : ((1 : Q').den : Int) = 1 := rfl
    rw [hd1, hd2, Int.mul_one, Int.mul_one]
  rw [hLnum, hLden]
  have hRnum : (Q'.ofNat (2 * (e + 1))).num = (2 : Int) * ((e + 1 : Nat) : Int) := by
    show ((2 * (e + 1) : Nat) : Int) = (2 : Int) * ((e + 1 : Nat) : Int)
    push_cast; rfl
  have hRden : ((Q'.ofNat (2 * (e + 1))).den : Int) = 1 := rfl
  rw [hRnum, hRden, Int.mul_one]
  -- goal: 2(e+1) ≤ 2(e+1)·M
  have hM1 : (1 : Int) ≤ (M : Int) := by exact_mod_cast hM
  have h0 : (0 : Int) ≤ (2 : Int) * ((e + 1 : Nat) : Int) :=
    Int.mul_nonneg (by decide) (Int.natCast_nonneg _)
  calc (2 : Int) * ((e + 1 : Nat) : Int)
      = ((2 : Int) * ((e + 1 : Nat) : Int)) * 1 := by rw [Int.mul_one]
    _ ≤ ((2 : Int) * ((e + 1 : Nat) : Int)) * (M : Int) :=
        Int.mul_le_mul_of_nonneg_left hM1 h0

/-- **Universal `orthTerm` constant bound `|orthTerm e M k| ≤ 2(e+1)`** for EVERY
`k`.  Interior `k < M`: `orthTerm_AbsLeRat` with `cw = 1` (`oneMinusSqNode ≤ 1`),
collapsed by `orthBound_crude_le`.  Out-of-range `k ≥ M`: `nodeWeight = czero`, so
`orthTerm ≈ 0`. -/
theorem orthTerm_crude (e M : Nat) (hM : 0 < M) (k : Nat) :
    AbsLeRat (orthTerm e M hM k) (Q'.ofNat (2 * (e + 1))) := by
  by_cases hk : k < M
  · have hcw : (0 : Q') < (1 : Q') := by decide
    have haw : SemicircleIntegral.oneMinusSqNode M k hM hk ≤ (1 : Q') * (1 : Q') := by
      refine Q'.le_trans' _ _ _ (SemicircleIntegral.oneMinusSqNode_le_one hM hk) ?_
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv (1 : Q')))
    have hO := ChebOrthoGradedClose.orthTerm_AbsLeRat e M hM k hk (1 : Q') hcw haw
    exact ChebOrthoGradedClose.AbsLeRat.mono hO (orthBound_crude_le e M hM)
  · -- k ≥ M : nodeWeight czero ⇒ orthTerm ≈ 0
    have hcz : AbsLeRat (orthTerm e M hM k) (0 : Q') := by
      refine ChebOrthoGradedClose.AbsLeRat_zero_of_approx_zero (fun p => ?_)
      show ((SemicircleIntegral.lebW M hM)
          * ((uNode e M hM k) * ((SemicircleIntegral.nodeWeight M hM k).approx p))) ≈ 0
      have hnw : SemicircleIntegral.nodeWeight M hM k = CReal.czero := by
        unfold SemicircleIntegral.nodeWeight; rw [dif_neg hk]
      rw [hnw]
      have hcz0 : ((CReal.czero).approx p) = (0 : Q') := rfl
      rw [hcz0]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv (uNode e M hM k))) ?_
      exact Q'.mul_zero_eqv (SemicircleIntegral.lebW M hM)
    refine ChebOrthoGradedClose.AbsLeRat.mono hcz ?_
    show (0 : Q') ≤ Q'.ofNat (2 * (e + 1))
    rw [Q'.zero_le_iff_num_nonneg]
    show (0 : Int) ≤ (Q'.ofNat (2 * (e + 1))).num
    exact Int.natCast_nonneg _

/-- **DELIVERABLE 1 — the crude all-`M` constant per-cell bound.**  For every
`M ≥ 1`, every `k`, the genuine adjusted cell is two-sidedly bounded by the constant
`Ccrude e := 2e+4`:  `AbsLeRat (cellAdjR e he M k) (ofNat (2e+4))`.
Assembles `cellAdjR = orthTerm + (GsampR(k+1) + (−GsampR(k)))` from the universal
`orthTerm_crude` (`≤ 2(e+1)`) and two `GsampR_crude` (`≤ 1` each):
`2(e+1) + (1+1) = 2e+4`. -/
theorem cellAdj_crude (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) :
    AbsLeRat (cellAdjR e he M hM k) (Q'.ofNat (2 * e + 4)) := by
  -- cellAdjR = add orthTerm (add GsampR(k+1) (neg GsampR(k)))
  have hO := orthTerm_crude e M hM k
  have hGp := GsampR_crude e he M hM (k + 1)
  have hGm : AbsLeRat (CReal.neg (GsampR e he M hM k)) (Q'.ofNat 1) :=
    ChebOrthoGradedClose.AbsLeRat.neg (GsampR_crude e he M hM k)
  have hSum := ChebOrthoGradedClose.AbsLeRat.add hO
    (ChebOrthoGradedClose.AbsLeRat.add hGp hGm)
  -- hSum : AbsLeRat (cellAdjR) (ofNat(2(e+1)) + (ofNat 1 + ofNat 1))
  show AbsLeRat (CReal.add (orthTerm e M hM k)
      (CReal.add (GsampR e he M hM (k + 1)) (CReal.neg (GsampR e he M hM k))))
      (Q'.ofNat (2 * e + 4))
  refine ChebOrthoGradedClose.AbsLeRat.mono hSum ?_
  -- ofNat(2(e+1)) + (ofNat 1 + ofNat 1) ≤ ofNat(2e+4)
  show Q'.ofNat (2 * (e + 1)) + (Q'.ofNat 1 + Q'.ofNat 1) ≤ Q'.ofNat (2 * e + 4)
  -- both sides are integers: 2(e+1) + 2 = 2e+4
  show (Q'.ofNat (2 * (e + 1)) + (Q'.ofNat 1 + Q'.ofNat 1)).num
        * ((Q'.ofNat (2 * e + 4)).den : Int)
      ≤ (Q'.ofNat (2 * e + 4)).num
        * ((Q'.ofNat (2 * (e + 1)) + (Q'.ofNat 1 + Q'.ofNat 1)).den : Int)
  have hLnum : (Q'.ofNat (2 * (e + 1)) + (Q'.ofNat 1 + Q'.ofNat 1)).num
      = (2 * (e + 1) : Nat) + 2 := by
    show (Q'.ofNat (2 * (e + 1))).num * ((Q'.ofNat 1 + Q'.ofNat 1).den : Int)
        + (Q'.ofNat 1 + Q'.ofNat 1).num * ((Q'.ofNat (2 * (e + 1))).den : Int)
        = (2 * (e + 1) : Nat) + 2
    have h1 : (Q'.ofNat 1 + Q'.ofNat 1).num = 2 := by decide
    have h2 : ((Q'.ofNat 1 + Q'.ofNat 1).den : Int) = 1 := by decide
    have h3 : (Q'.ofNat (2 * (e + 1))).num = ((2 * (e + 1) : Nat) : Int) := rfl
    have h4 : ((Q'.ofNat (2 * (e + 1))).den : Int) = 1 := rfl
    rw [h1, h2, h3, h4, Int.mul_one, Int.mul_one]
  have hLden : ((Q'.ofNat (2 * (e + 1)) + (Q'.ofNat 1 + Q'.ofNat 1)).den : Int) = 1 := by
    rw [Q'.add_den_cast]
    show ((Q'.ofNat (2 * (e + 1))).den : Int) * ((Q'.ofNat 1 + Q'.ofNat 1).den : Int) = 1
    have h4 : ((Q'.ofNat (2 * (e + 1))).den : Int) = 1 := rfl
    have h2 : ((Q'.ofNat 1 + Q'.ofNat 1).den : Int) = 1 := by decide
    rw [h4, h2, Int.mul_one]
  rw [hLnum, hLden, Int.mul_one]
  have hRnum : (Q'.ofNat (2 * e + 4)).num = ((2 * e + 4 : Nat) : Int) := rfl
  have hRden : ((Q'.ofNat (2 * e + 4)).den : Int) = 1 := rfl
  rw [hRnum, hRden, Int.mul_one]
  -- (2(e+1)+2) ≤ (2e+4) as Int
  have : ((2 * (e + 1) : Nat) : Int) + 2 = ((2 * e + 4 : Nat) : Int) := by push_cast; omega
  rw [this]
  exact Int.le_refl _

/-! ## 2. The per-cell graded bound for `M₀ ≤ N+1` (all cells) -/

/-- `½·g + ½·g ≈ g` for the leg half `ChebOrthoLegAssembly.half = mkPos 1 2`. -/
theorem legHalf_add_half (g : Q') :
    (ChebOrthoLegAssembly.half * g + ChebOrthoLegAssembly.half * g) ≈ g := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_mul_eqv ChebOrthoLegAssembly.half ChebOrthoLegAssembly.half g)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (by decide : (ChebOrthoLegAssembly.half + ChebOrthoLegAssembly.half) ≈ (1 : Q'))) ?_
  exact Q'.one_mul_eqv g

/-- **The INTERIOR per-cell graded bound from the two per-cell leg bounds.**
For an interior cell `(N,k)` (`hk : k < N+1`) with the bracket-leg and radical-leg
remainders bounded by HALF the graded rate, the genuine adjusted cell is two-sidedly
bounded by the FULL graded rate.  Replicates, at the per-cell level, the PROVED chain
`split_leg_decomp` → `leadingCancellation` → `secondDiff_reduce` →
`cellAdjR_split_Equiv` (needs even `e ≥ 2` for `leadingCancellation`). -/
theorem cellAdj_interior_of_legs (e : Nat) (he : 0 < e) (he2 : 2 ≤ e) (N k : Nat)
    (hk : k < N + 1)
    (hBr : AbsLeRat
      (CReal.add (ChebOrthoSecondDiff.legBr e he (N + 1) (Nat.succ_pos N) k)
        (CReal.neg (ChebOrthoSecondDiff.LZA e he (N + 1) (Nat.succ_pos N) k)))
      (ChebOrthoLegAssembly.half * gradedRate e (N + 1) (Nat.succ_pos N) k))
    (hRad : AbsLeRat
      (CReal.add (ChebOrthoSecondDiff.legRad e he (N + 1) (Nat.succ_pos N) k)
        (CReal.neg (ChebOrthoSecondDiff.LZB e he (N + 1) (Nat.succ_pos N) k hk)))
      (ChebOrthoLegAssembly.half * gradedRate e (N + 1) (Nat.succ_pos N) k)) :
    AbsLeRat (cellAdjR e he (N + 1) (Nat.succ_pos N) k)
      (gradedRate e (N + 1) (Nat.succ_pos N) k) := by
  -- Step 1: add the two leg bounds, collapse ½g + ½g ≤ g.
  have hadd := ChebOrthoGradedClose.AbsLeRat.add hBr hRad
  have hadd' : AbsLeRat
      (CReal.add (CReal.add (ChebOrthoSecondDiff.legBr e he (N + 1) (Nat.succ_pos N) k)
          (CReal.neg (ChebOrthoSecondDiff.LZA e he (N + 1) (Nat.succ_pos N) k)))
        (CReal.add (ChebOrthoSecondDiff.legRad e he (N + 1) (Nat.succ_pos N) k)
          (CReal.neg (ChebOrthoSecondDiff.LZB e he (N + 1) (Nat.succ_pos N) k hk))))
      (gradedRate e (N + 1) (Nat.succ_pos N) k) :=
    ChebOrthoGradedClose.AbsLeRat.mono hadd
      (Q'.le_of_eqv (legHalf_add_half (gradedRate e (N + 1) (Nat.succ_pos N) k)))
  -- Step 2: transfer back along the EXACT leg decomposition → SecondDiffRemainderLeg2 cell.
  have hLeg2 : AbsLeRat
      (CReal.add (ChebOrthoRemainder.splitCReal e he (N + 1) (Nat.succ_pos N) k)
        (CReal.neg (ChebOrthoLeadingModel.LZ e he (N + 1) (Nat.succ_pos N) k hk)))
      (gradedRate e (N + 1) (Nat.succ_pos N) k) :=
    ChebOrthoCancelDiv.AbsLeRat.of_equiv
      (ChebOrthoSecondDiff.split_leg_decomp e he (N + 1) (Nat.succ_pos N) k hk) hadd'
  -- Step 3: leading cancellation Equiv (orthTerm + LZ) czero.
  have hcancel := ChebOrthoLeadingModel.leadingCancellation e he he2 (N + 1) (Nat.succ_pos N) k hk
  -- Step 4: secondDiff_reduce → InteriorSecondOrderRemainder cell (orthTerm + splitCReal ≤ g).
  have hSO : AbsLeRat
      (CReal.add (orthTerm e (N + 1) (Nat.succ_pos N) k)
        (ChebOrthoRemainder.splitCReal e he (N + 1) (Nat.succ_pos N) k))
      (gradedRate e (N + 1) (Nat.succ_pos N) k) :=
    ChebOrthoTaylor.secondDiff_reduce hcancel hLeg2
  -- Step 5: transfer to cellAdjR via cellAdjR_split_Equiv.
  exact ChebOrthoCancelDiv.AbsLeRat.of_equiv
    (ChebOrthoFinal.cellAdjR_split_Equiv e he (N + 1) (Nat.succ_pos N) k) hSO

/-- **DELIVERABLE 2 — the per-cell graded bound for `M₀ ≤ N+1` (all `k`).**
There is a threshold `M₀` past which EVERY genuine adjusted cell `cellAdjR e he (N+1) k`
is two-sidedly `≤` the graded rate.  Interior cells use `cellAdj_interior_of_legs`
fed by the two PROVED EVENTUAL leg bounds; boundary cells (`k ∈ {0, N}`) and
out-of-range cells (`k ≥ N+1`) are UNCONDITIONAL (`boundary_cell_bound`,
`outOfRange_cell_bound`).  Even `e ≥ 2`. -/
theorem cellAdj_graded_eventual (e : Nat) (he : 0 < e) (he2 : 2 ≤ e) :
    ∃ M₀ : Nat, ∀ N k : Nat, M₀ ≤ N + 1 →
      AbsLeRat (cellAdjR e he (N + 1) (Nat.succ_pos N) k)
        (gradedRate e (N + 1) (Nat.succ_pos N) k) := by
  obtain ⟨M0Br, hBr⟩ := ChebOrthoLegProof.eventualBrLegRemainder e he he2
  obtain ⟨M0Rad, hRad⟩ := ChebOrthoBracketDecay.eventualRadLegRemainder e he he2
  refine ⟨Nat.max M0Br M0Rad, fun N k hM0 => ?_⟩
  have hM0Br : M0Br ≤ N + 1 := Nat.le_trans (Nat.le_max_left M0Br M0Rad) hM0
  have hM0Rad : M0Rad ≤ N + 1 := Nat.le_trans (Nat.le_max_right M0Br M0Rad) hM0
  -- case split on cell position
  by_cases hkr : N + 1 ≤ k
  · exact ChebOrthoGradedClose.outOfRange_cell_bound e he (N + 1) (Nat.succ_pos N) k hkr
  · by_cases hk0 : k = 0
    · exact ChebOrthoGradedClose.boundary_cell_bound e he (N + 1) (Nat.succ_pos N) k (Or.inl hk0)
    · by_cases hktop : k = (N + 1) - 1
      · exact ChebOrthoGradedClose.boundary_cell_bound e he (N + 1) (Nat.succ_pos N) k
          (Or.inr hktop)
      · -- interior: 1 ≤ k ≤ N-1, k < N+1
        have hk1 : 1 ≤ k := by omega
        have hkN1 : k ≤ N - 1 := by omega
        have hk : k < N + 1 := by omega
        exact cellAdj_interior_of_legs e he he2 N k hk
          (hBr N k hM0Br hk1 hkN1)
          (hRad N k hM0Rad hk1 hkN1 hk)

/-! ## 3. The piecewise REAL per-cell budget -/

/-- **DELIVERABLE 3 — the SATISFIABLE `RealPerCellBudget` for even `e ≥ 2`.**
Witnessed by the PIECEWISE rate
  `r M k := if 0 < M then (if M₀ ≤ M then gradedRate e M k else 2e+4) else 2e+4`,
where `M₀` is the eventual threshold from `cellAdj_graded_eventual`.

  * Nonnegativity: both branches are `≥ 0` (`gradedRate_nonneg`, `ofNat ≥ 0`).
  * Per-cell `∀ N k`: for `N+1 ≥ M₀` the rate is `gradedRate` and `cellAdj_graded_eventual`
    applies; for `N+1 < M₀` the rate is the crude constant and `cellAdj_crude` applies.
  * Rate-limit (already EVENTUAL): for `ε>0`, past `max(M₀, threshold)` the rate is
    `gradedRate`, whose finite sum `→ 0` (`gradedRateSum_vanishes`). -/
theorem realPerCellBudget (e : Nat) (he : 0 < e) (he2 : 2 ≤ e) :
    ChebOrthoMidpoint.RealPerCellBudget e he := by
  obtain ⟨M₀, hgr⟩ := cellAdj_graded_eventual e he he2
  refine ⟨fun M k =>
      if hMpos : 0 < M then
        (if M₀ ≤ M then gradedRate e M hMpos k else Q'.ofNat (2 * e + 4))
      else Q'.ofNat (2 * e + 4), ?_, ?_, ?_⟩
  · -- nonnegativity
    intro M k
    show (0 : Q') ≤ (if hMpos : 0 < M then
        (if M₀ ≤ M then gradedRate e M hMpos k else Q'.ofNat (2 * e + 4))
      else Q'.ofNat (2 * e + 4))
    by_cases hMpos : 0 < M
    · rw [dif_pos hMpos]
      by_cases hle : M₀ ≤ M
      · rw [if_pos hle]; exact ChebOrthoGraded.gradedRate_nonneg e M hMpos k
      · rw [if_neg hle]
        rw [Q'.zero_le_iff_num_nonneg]; exact Int.natCast_nonneg _
    · rw [dif_neg hMpos]
      rw [Q'.zero_le_iff_num_nonneg]; exact Int.natCast_nonneg _
  · -- per-cell two-sided bound
    intro N k
    have hN1 : (0 : Nat) < N + 1 := Nat.succ_pos N
    have hcell : AbsLeRat (cellAdjR e he (N + 1) (Nat.succ_pos N) k)
        (if hMpos : 0 < N + 1 then
          (if M₀ ≤ N + 1 then gradedRate e (N + 1) hMpos k else Q'.ofNat (2 * e + 4))
        else Q'.ofNat (2 * e + 4)) := by
      rw [dif_pos hN1]
      by_cases hle : M₀ ≤ N + 1
      · rw [if_pos hle]; exact hgr N k hle
      · rw [if_neg hle]; exact cellAdj_crude e he (N + 1) (Nat.succ_pos N) k
    exact ⟨hcell.1, hcell.2⟩
  · -- rate-limit (eventual)
    intro ε hε
    obtain ⟨Mε, hMε⟩ := ChebOrthoGraded.gradedRateSum_vanishes e ε hε
    refine ⟨Nat.max M₀ Mε, fun N hN => ?_⟩
    have hN1 : (0 : Nat) < N + 1 := Nat.succ_pos N
    have hM0 : M₀ ≤ N + 1 :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_left M₀ Mε) hN) (Nat.le_succ N)
    have hMεle : Mε ≤ N + 1 :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_right M₀ Mε) hN) (Nat.le_succ N)
    -- the rate at (N+1) collapses to gradedRate
    show RationalTail.finSum
        (fun k => if hMpos : 0 < N + 1 then
          (if M₀ ≤ N + 1 then gradedRate e (N + 1) hMpos k else Q'.ofNat (2 * e + 4))
        else Q'.ofNat (2 * e + 4)) (N + 1) ≤ ε
    have hfun : (fun k => if hMpos : 0 < N + 1 then
          (if M₀ ≤ N + 1 then gradedRate e (N + 1) hMpos k else Q'.ofNat (2 * e + 4))
        else Q'.ofNat (2 * e + 4))
        = gradedRate e (N + 1) hN1 := by
      funext k
      rw [dif_pos hN1, if_pos hM0]
    rw [hfun]
    exact hMε (N + 1) hMεle hN1

/-! ## 4. THE PRIZE — the UNCONDITIONAL off-diagonal orthogonality -/

/-- **DELIVERABLE 4 — UNCONDITIONAL off-diagonal Chebyshev-`U` orthogonality.**
`∫ U_e √ = 0` for ALL `e ≥ 1`:

    `∀ e, 1 ≤ e → ∃ L, CReal.ConvergesTo (seqOrth e) L ∧ CReal.Equiv L CReal.czero`.

The EVEN case is supplied by `realPerCellBudget` (built unconditionally from the two
PROVED eventual leg bounds), the ODD case is already unconditional inside
`ChebOrthoMidpoint.offdiag_closed_of_realPerCell`.  NO remaining named hypothesis. -/
theorem offdiag_orthogonality_unconditional :
    ∀ (e : Nat), 1 ≤ e →
      ∃ L : CReal, CReal.ConvergesTo (seqOrth e) L ∧ CReal.Equiv L CReal.czero :=
  ChebOrthoMidpoint.offdiag_closed_of_realPerCell
    (fun e he he2 _heven => realPerCellBudget e he he2)

end YMGap.Continuum.ChebOrthoOffDiagFinal

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.ChebOrthoOffDiagFinal.cellAdj_crude
#print axioms YMGap.Continuum.ChebOrthoOffDiagFinal.cellAdj_graded_eventual
#print axioms YMGap.Continuum.ChebOrthoOffDiagFinal.realPerCellBudget
#print axioms YMGap.Continuum.ChebOrthoOffDiagFinal.offdiag_orthogonality_unconditional
