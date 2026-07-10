/-
`BoxSumTailGeneral` — Milestone 13.2, step 5 (small brick): the GENERAL-`N`
mode tail of the box sum, replacing the per-`N` tail lemmas
(`boxSum2_tail`, `boxSum3_tail`, `boxSum4_tail`) with one statement:

    2N < s   →   boxSum w N s ≃ 0

(no `(a,b) ≤ N` pair reaches mode `s > 2N`: the fusion window demands
`s ≤ a + b ≤ 2N`).  Every future pointwise push of the direct box
Cauchy–Binet core (`UniformBoxLogConcave`, the corrected uniform residual
of the refuted `CoreStep` node) gets its tail channels for free from this
one lemma instead of a fresh per-`N` proof.

Also delivered: `boxSum_cross_tail_le` — for `2N ≤ s`, the Cauchy–Binet
cross product at mode `s` vanishes against any square
(`boxSum N s · boxSum N (s+2) ≤ boxSum N (s+1)²` holds trivially in the
tail), so any future all-`N` inhabitation only ever owes the FINITE window
`s < 2N`.

# Honest scope (AGENTS.md Rule 6)

A finite-combinatorial support lemma; it does NOT inhabit
`UniformBoxLogConcave` (the all-`N` finite window remains the open
heat-kernel local-CLT content) and touches no frontier type.  The Clay
problem remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / `admit` / new `axiom`.  Gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.FusionCoreStep

namespace YMGap.Continuum.BoxSumTailGeneral

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionCoreInduction

/-- **`boxSum_tail` (PROVED — the general-`N` mode tail).**  For `2N < s`,
no `(a, b) ≤ N` pair reaches mode `s`, and the box sum vanishes. -/
theorem boxSum_tail (w : Q') (N s : Nat) (hs : 2 * N < s) :
    (boxSum w N s).eqv 0 := by
  unfold boxSum
  refine fsum_zero_below (N + 1) (fun a ha => ?_)
  refine fsum_zero_below (N + 1) (fun b hb => ?_)
  have hind : fusionInd a b s = (0 : Q') := by
    unfold fusionInd
    have hok : fusionOK a b s = false := by
      rw [fusionOK_eq_false_iff]
      rintro ⟨_, h2, _⟩
      omega
    rw [hok]
    rfl
  rw [hind]
  exact Q'.zero_mul_eqv _

/-- **`boxSum_cross_tail_le` (PROVED).**  For `2N ≤ s`, the Cauchy–Binet
cross product at mode `s` is dominated by any square: the `s + 2` factor is
in the tail, so the cross product is `≃ 0 ≤` the (nonnegative) square.
Hence any all-`N` inhabitation of the box core only owes the finite window
`s < 2N`. -/
theorem boxSum_cross_tail_le {w : Q'} (hw : (0 : Q') ≤ w) (N s : Nat)
    (hs : 2 * N ≤ s) :
    boxSum w N s * boxSum w N (s + 2)
      ≤ boxSum w N (s + 1) * boxSum w N (s + 1) := by
  have hz : (boxSum w N (s + 2)).eqv 0 := boxSum_tail w N (s + 2) (by omega)
  have hLHS : (boxSum w N s * boxSum w N (s + 2)).eqv 0 := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hz) ?_
    exact Q'.mul_zero_eqv _
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) ?_
  exact Q'.mul_nonneg _ _ (FusionCoreInduction.boxSum_nonneg hw N (s + 1))
    (FusionCoreInduction.boxSum_nonneg hw N (s + 1))

end YMGap.Continuum.BoxSumTailGeneral

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BoxSumTailGeneral.boxSum_tail
#print axioms YMGap.Continuum.BoxSumTailGeneral.boxSum_cross_tail_le
