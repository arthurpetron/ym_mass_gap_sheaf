import YMGap.Continuum.ChebOrthoMatrix
import YMGap.Continuum.ChebOrthoOffDiagFinal

/-!
# The orthogonality matrix, UNCONDITIONALLY

`ChebOrthoMatrix.orthMatrix` (`∫U_cU_d√ = semiInt·δ_{cd}`) was stated conditional on
`ChebOrthoMatrix.OffDiagClosed` (`∀ e ≥ 1, ConvergesTo (seqOrth e) czero`).  That
hypothesis is now a THEOREM: `ChebOrthoOffDiagFinal.offdiag_orthogonality_unconditional`
proves, for every `e ≥ 1`, a limit `L` of `seqOrth e` with `L ≃ czero`; re-targeting
the limit along the `Equiv` (`convergesTo_retarget`) gives `ConvergesTo (seqOrth e)
czero`, i.e. `OffDiagClosed`.  Hence the orthogonality matrix holds unconditionally.

This discharges the FIRST of the three named analytic atoms of the all-order Gram-PSD
reduction (`OffDiagClosed`/`cellBoundExists`); `RProjection` and `SOSIntegral` remain.

PROVED here (axiom-clean, `[propext]`/`[propext, Quot.sound]`):
* `convergesTo_retarget` — re-target a limit along an `Equiv` (`s → L`, `L ≃ L'` ⇒
  `s → L'`).
* `offDiagClosed_unconditional` — `ChebOrthoMatrix.OffDiagClosed`, UNCONDITIONAL.
* `orthMatrix_unconditional` — `∫U_cU_d√ = semiInt·δ_{cd}` for all `c d`, UNCONDITIONAL.
-/

namespace YMGap.Continuum.ChebOrthoMatrixUncond

open YMGap.Constructive
open YMGap.Continuum

/-- **Re-target a limit along an `Equiv`.**  `s → L`, `L ≃ L'` ⇒ `s → L'`. -/
theorem convergesTo_retarget {s : Nat → CReal} {L L' : CReal}
    (hs : CReal.ConvergesTo s L) (hLL' : CReal.Equiv L L') :
    CReal.ConvergesTo s L' := by
  intro ε hε
  have hhε : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Nstage, hstage⟩ := hs (HalfPow.half * ε) hhε
  obtain ⟨NL, hNL⟩ := hLL' (HalfPow.half * ε) hhε
  refine ⟨Nstage, fun N hN => ?_⟩
  obtain ⟨Napx, hap⟩ := hstage N hN
  refine ⟨max Napx NL, fun n hn => ?_⟩
  have hn1 : Napx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : NL ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨hs1, hs2⟩ := hap n hn1
  obtain ⟨hL1, hL2⟩ := hNL n hn2
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _ hs1 ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) hL1) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (L'.approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left (L'.approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
      (ExpNeg.two_halves ε)
  · refine Q'.le_trans' _ _ _ hL2 ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) hs2) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv ((s N).approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left ((s N).approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
      (ExpNeg.two_halves ε)

/-- **`OffDiagClosed`, UNCONDITIONALLY.**  Each `seqOrth e` (`e ≥ 1`) converges to a
limit `L ≃ czero` by `ChebOrthoOffDiagFinal.offdiag_orthogonality_unconditional`;
re-target to `czero`. -/
theorem offDiagClosed_unconditional : ChebOrthoMatrix.OffDiagClosed := by
  intro e he
  obtain ⟨L, hConv, hLzero⟩ := ChebOrthoOffDiagFinal.offdiag_orthogonality_unconditional e he
  exact convergesTo_retarget hConv hLzero

/-- **The orthogonality matrix `∫U_cU_d√ = semiInt·δ_{cd}`, UNCONDITIONALLY.** -/
theorem orthMatrix_unconditional (c d : Nat) :
    CReal.ConvergesTo (ChebOrthoMatrix.seqOrth2 c d)
      (if c = d then SemicircleBoundClosed.semiInt else CReal.czero) :=
  ChebOrthoMatrix.orthMatrix offDiagClosed_unconditional c d

end YMGap.Continuum.ChebOrthoMatrixUncond

#print axioms YMGap.Continuum.ChebOrthoMatrixUncond.offDiagClosed_unconditional
#print axioms YMGap.Continuum.ChebOrthoMatrixUncond.orthMatrix_unconditional
