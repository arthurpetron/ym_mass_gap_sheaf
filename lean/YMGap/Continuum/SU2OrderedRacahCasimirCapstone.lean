/-
# Casimir capstone for the arbitrary-label ordered Racah residual

The pair-Casimir argument proves the complete right-channel Gram law.  This
file removes the last enumeration artifact from its Schur consequence: every
proof-carrying physical right channel is a valid canonical target, so its
factorial cross carrier is unconditionally the positive right Gram weight
times the inverse Schur coefficient.

This does not identify the inverse Schur coefficient with the explicit
factorial Racah kernel.  Instead, positive right weight cancellation proves
that the remaining squared factorial identity is *equivalent* to precisely
that corrected inverse Schur/Racah normalization.  A closed rational
countermodel records that positivity plus cross normalization alone cannot
force the missing kernel identity.
-/

import YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality

namespace YMGap.Continuum.SU2OrderedRacahCasimirCapstone

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputReconstruction
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FixedLeftRightAssociatorSchur
open YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge
open YMGap.Continuum.SU2OrderedRacahMultiplicityFence
open YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier
open YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge
open YMGap.Continuum.SU2OrderedRightGramOrthogonality
open YMGap.Continuum.SU2OrderedRightGramCasimirOrthogonality
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SixJKernel

local infix:50 " ≈ " => Q'.eqv

private theorem channelAt_exists_of_mem {a b c d : Nat}
    (fallback q : FixedRightCGChannel a b c d)
    (qs : List (FixedRightCGChannel a b c d)) (hq : q ∈ qs) :
    ∃ n, n < qs.length ∧ fixedRightChannelAt fallback qs n = q := by
  induction qs with
  | nil =>
      exact False.elim (List.not_mem_nil hq)
  | cons x xs ih =>
      rcases List.mem_cons.mp hq with hqx | hqxs
      · subst q
        refine ⟨0, by simp, ?_⟩
        rfl
      · obtain ⟨n, hn, hat⟩ := ih hqxs
        refine ⟨n + 1, by simp only [List.length_cons]; omega, ?_⟩
        simpa only [fixedRightChannelAt, List.getElem?_cons_succ] using hat

/-- Every proof-carrying right channel occurs at a valid total-lookup index in
the canonical enumeration used by the fixed-left Schur row. -/
theorem arbitrary_right_channel_is_enumerated {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    ∃ target, target < (fixedRightChannels a b c d).length ∧
      enumeratedRightChannel qL target = qR := by
  exact channelAt_exists_of_mem (fixedRightFallbackOfFixedLeft qL) qR
    (fixedRightChannels a b c d) (fixedRightChannels_complete qR)

/-- **Unconditional arbitrary-channel inverse cross normalization.**  The
Casimir Gram law removes both the off-diagonal hypothesis and the canonical
target-index restriction from the interior Schur bridge. -/
theorem collapsed_cross_inverse_normalization_arbitrary
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    collapsedFactorialCrossSum qL qR ≈
      triRightChannelWeight a b c d qR.intermediate *
        fixedLeftRightDiagonalCoeff qL qR 0 := by
  obtain ⟨target, htarget, htargetEq⟩ :=
    arbitrary_right_channel_is_enumerated qL qR
  have h := collapsed_cross_inverse_normalization_all qL target htarget
  simpa only [htargetEq] using h

/-- With the now-derived arbitrary-channel cross normalization and the strict
positivity of every physical right Gram weight, the explicit factorial square
is equivalent to the corrected inverse Schur/Racah bridge.  Thus the latter is
the exact remaining identity; Casimir orthogonality has discharged every
other hypothesis in the inverse route. -/
theorem collapsedRacahSquare_iff_inverseSchurGramRacahBridge
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    CollapsedRacahSquareAt qL qR ↔
      InverseSchurGramRacahBridgeAt qL qR := by
  constructor
  · intro hsquare
    exact inverseSchurGramRacahBridge_of_collapsed_square qL qR
      (right_channel_weight_pos_all qR)
      (collapsed_cross_inverse_normalization_arbitrary qL qR) hsquare
  · intro hbridge
    exact collapsedRacahSquare_of_inverse_normalization_and_bridge qL qR
      (collapsed_cross_inverse_normalization_arbitrary qL qR) hbridge

/-- Fully unfolded form of the arbitrary-label residual.  After Casimir
orthogonality, no Gram-row, enumeration, nonvanishing, or cross-carrier lemma
remains: closure is equivalent exactly to this one comparison between the
explicit factorial Racah kernel and the squared inverse Schur coefficient. -/
theorem collapsedRacahSquare_iff_explicit_inverse_kernel_identity
    {a b c d : Nat} (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    CollapsedRacahSquareAt qL qR ↔
      triLeftChannelWeight a b c d qL.intermediate *
          racahKernel6 a b c d qL.intermediate qR.intermediate ≈
        triRightChannelWeight a b c d qR.intermediate *
          (fixedLeftRightDiagonalCoeff qL qR 0 *
            fixedLeftRightDiagonalCoeff qL qR 0) := by
  simpa only [InverseSchurGramRacahBridgeAt, fixedLeftRightRawKernel] using
    collapsedRacahSquare_iff_inverseSchurGramRacahBridge qL qR

/-- Closed exact-rational fence: a positive target weight and the abstract
cross normalization do not algebraically force a chosen squared kernel
target.  Here `C=WR=K=WL=1` and `P=2`; the cross identity holds while the
square target does not. -/
theorem positive_inverse_cross_data_do_not_force_kernel_square :
    ¬ (∀ C WL WR K P : Q', (0 : Q') < WR → C ≈ WR * K →
      C * C ≈ WL * (WR * P)) := by
  intro h
  have hbad := h 1 1 1 1 2 (by decide) (by decide)
  exact (by decide : ¬ ((1 : Q') * 1 ≈ 1 * (1 * 2))) hbad

end YMGap.Continuum.SU2OrderedRacahCasimirCapstone

#print axioms YMGap.Continuum.SU2OrderedRacahCasimirCapstone.arbitrary_right_channel_is_enumerated
#print axioms YMGap.Continuum.SU2OrderedRacahCasimirCapstone.collapsed_cross_inverse_normalization_arbitrary
#print axioms YMGap.Continuum.SU2OrderedRacahCasimirCapstone.collapsedRacahSquare_iff_inverseSchurGramRacahBridge
#print axioms YMGap.Continuum.SU2OrderedRacahCasimirCapstone.collapsedRacahSquare_iff_explicit_inverse_kernel_identity
#print axioms YMGap.Continuum.SU2OrderedRacahCasimirCapstone.positive_inverse_cross_data_do_not_force_kernel_square
