/-
Track 11.7-fusion / R2k -- a strong-Turan compiler for the all-cutoff p=2 tail.

# Result

The division-free retuned residual compares every pair of adjacent fused
coefficients.  This module replaces that linearly growing family by:

* the first genuinely open edge (`s = 1`); and
* one uniform, dimension-weighted strong Turan family on `1 <= s`.

The induction is a proof about computation rather than a mode scan.  At each
step the Turan inequality is followed by the preceding adjacent inequality;
the common positive factor is canceled using the full Clebsch-support
positivity theorem.  Thus an all-index inhabitant of the strong Turan family
compiles directly to `P2RetunedCoeffTailRatio` and then to the reviewed
`CanonicalBulkControl`.

The lower endpoint `s = 0` is deliberately excluded from the Turan family.
At near-continuum weights the cutoff box can violate even ordinary
log-concavity there (already at small cutoffs), while the required `s = 1`
edge remains true.  Keeping it as a separate field avoids strengthening the
frontier to a false statement.

# Constructivity

Pure `Q'`/`Nat` induction and positive-factor cancellation.  No `Classical`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.P2RetunedRatioCompiler
import YMGap.Continuum.SelfFusionLogConcave

namespace YMGap.Continuum.P2RetunedStrongTuranCompiler

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : (a * b) ≈ (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-- The exact strengthened Turan datum needed by the retuned adjacent-ratio
induction.  Its cross-multiplied form is

`D_(s+1)^2 g_s g_(s+2) <= q^2 D_s D_(s+2) g_(s+1)^2`,

with factors grouped to match the cancellation proof. -/
structure P2RetunedStrongTuran (N : Nat) (w : Q')
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) : Type where
  edge : 1 < 2 * N ->
    dimQ 1 * bondMovedCoeff N w 2 2 ≤
      qpow (p2RetunedWeight w) 5 *
        (dimQ 2 * bondMovedCoeff N w 2 1)
  turan : forall s, 1 ≤ s -> s + 2 ≤ 2 * N ->
    (dimQ (s + 1) * bondMovedCoeff N w 2 s) *
        (dimQ (s + 1) * bondMovedCoeff N w 2 (s + 2)) ≤
      (qpow (p2RetunedWeight w) 2 *
          (dimQ (s + 2) * bondMovedCoeff N w 2 (s + 1))) *
        (dimQ s * bondMovedCoeff N w 2 (s + 1))

/-- The same residual in the explicit weighted Clebsch-box coordinate.  This
is the canonical target for the existing ballot/interlacing machinery: no
fusion-power evaluator or vacuum quotient remains in either field. -/
structure P2RetunedBoxStrongTuran (N : Nat) (w : Q')
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) : Type where
  edge : 1 < 2 * N ->
    dimQ 1 * boxSum w N 2 ≤
      qpow (p2RetunedWeight w) 5 * (dimQ 2 * boxSum w N 1)
  turan : forall s, 1 ≤ s -> s + 2 ≤ 2 * N ->
    (dimQ (s + 1) * boxSum w N s) *
        (dimQ (s + 1) * boxSum w N (s + 2)) ≤
      (qpow (p2RetunedWeight w) 2 *
          (dimQ (s + 2) * boxSum w N (s + 1))) *
        (dimQ s * boxSum w N (s + 1))

/-- Exact Peter--Weyl reconstruction transports the weighted-box residual to
the physical two-fold bond-moved coefficients. -/
def strongTuran_of_box {N : Nat} {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (B : P2RetunedBoxStrongTuran N w hw0 hw1) :
    P2RetunedStrongTuran N w hw0 hw1 where
  edge := fun hN => by
    have hleft :
        (dimQ 1 * bondMovedCoeff N w 2 2) ≈ dimQ 1 * boxSum w N 2 :=
      Q'.mul_eqv_congr_left (dimQ 1) _ _ (bondMovedCoeff_eq_boxSum N 2)
    have hright :
        (qpow (p2RetunedWeight w) 5 *
            (dimQ 2 * bondMovedCoeff N w 2 1)) ≈
          qpow (p2RetunedWeight w) 5 * (dimQ 2 * boxSum w N 1) :=
      Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left (dimQ 2) _ _ (bondMovedCoeff_eq_boxSum N 1))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ (B.edge hN) (Q'.ge_of_eqv hright))
  turan := fun s hs hsupport => by
    have hs0 : (bondMovedCoeff N w 2 s) ≈ boxSum w N s :=
      bondMovedCoeff_eq_boxSum N s
    have hs1 : (bondMovedCoeff N w 2 (s + 1)) ≈ boxSum w N (s + 1) :=
      bondMovedCoeff_eq_boxSum N (s + 1)
    have hs2 : (bondMovedCoeff N w 2 (s + 2)) ≈ boxSum w N (s + 2) :=
      bondMovedCoeff_eq_boxSum N (s + 2)
    have hleft :
        ((dimQ (s + 1) * bondMovedCoeff N w 2 s) *
          (dimQ (s + 1) * bondMovedCoeff N w 2 (s + 2))) ≈
        ((dimQ (s + 1) * boxSum w N s) *
          (dimQ (s + 1) * boxSum w N (s + 2))) :=
      mul_eqv_both
        (Q'.mul_eqv_congr_left _ _ _ hs0)
        (Q'.mul_eqv_congr_left _ _ _ hs2)
    have hright :
        ((qpow (p2RetunedWeight w) 2 *
            (dimQ (s + 2) * bondMovedCoeff N w 2 (s + 1))) *
          (dimQ s * bondMovedCoeff N w 2 (s + 1))) ≈
        ((qpow (p2RetunedWeight w) 2 *
            (dimQ (s + 2) * boxSum w N (s + 1))) *
          (dimQ s * boxSum w N (s + 1))) :=
      mul_eqv_both
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hs1))
        (Q'.mul_eqv_congr_left _ _ _ hs1)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ (B.turan s hs hsupport) (Q'.ge_of_eqv hright))

/-- The strong Turan datum propagates its first edge across the complete
two-fold Clebsch support.  This is the cutoff-independent proof about the
otherwise expensive adjacent-ratio computation. -/
theorem coeffTailRatio_of_strongTuran {N : Nat} {w : Q'}
    (hwpos : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (T : P2RetunedStrongTuran N w (Q'.le_of_lt hwpos) hw1) :
    forall s, 1 ≤ s -> s < 2 * N ->
      dimQ s * bondMovedCoeff N w 2 (s + 1) ≤
        qpow (p2RetunedWeight w) (2 * s + 3) *
          (dimQ (s + 1) * bondMovedCoeff N w 2 s) := by
  intro s
  induction s with
  | zero =>
      intro hs
      exact absurd hs (by decide)
  | succ k ih =>
      intro _ hsupport
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        exact T.edge (by omega)
      · have hprev := ih hkpos (by omega)
        have ht := T.turan k hkpos (by omega)
        let q2 := qpow (p2RetunedWeight w) 2
        let qk := qpow (p2RetunedWeight w) (2 * k + 3)
        let qnext := qpow (p2RetunedWeight w) (2 * (k + 1) + 3)
        let g0 := bondMovedCoeff N w 2 k
        let g1 := bondMovedCoeff N w 2 (k + 1)
        let g2 := bondMovedCoeff N w 2 (k + 2)
        let d0 := dimQ k
        let d1 := dimQ (k + 1)
        let d2 := dimQ (k + 2)
        have hscale0 : (0 : Q') ≤ q2 * (d2 * g1) := by
          exact Q'.mul_nonneg _ _
            (qpow_nonneg _ (p2RetunedWeight_nonneg (Q'.le_of_lt hwpos)) 2)
            (Q'.mul_nonneg _ _ (dimQ_nonneg (k + 2))
              (bondMovedCoeff_nonneg N (Q'.le_of_lt hwpos) 2 (k + 1)))
        have hscaled :
            (q2 * (d2 * g1)) * (d0 * g1) ≤
              (q2 * (d2 * g1)) * (qk * (d1 * g0)) :=
          Q'.mul_le_mul_of_nonneg_left _ _ _ hprev hscale0
        have hpow : (q2 * qk) ≈ qnext := by
          unfold q2 qk qnext
          have hexp : 2 * (k + 1) + 3 = 2 + (2 * k + 3) := by omega
          rw [hexp]
          exact Q'.eqv_symm
            (qpow_add (p2RetunedWeight w) 2 (2 * k + 3))
        have hright :
            (q2 * (d2 * g1)) * (qk * (d1 * g0)) ≈
              (d1 * g0) * (qnext * (d2 * g1)) := by
          refine Q'.eqv_trans _ _ _
            (mul_four_regroup q2 (d2 * g1) qk (d1 * g0)) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left (q2 * qk) _ _
              (Q'.mul_comm_eqv (d2 * g1) (d1 * g0))) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv (q2 * qk) (d1 * g0) (d2 * g1))) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ (d2 * g1)
              (Q'.mul_comm_eqv (q2 * qk) (d1 * g0))) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_assoc_eqv (d1 * g0) (q2 * qk) (d2 * g1)) ?_
          exact Q'.mul_eqv_congr_left (d1 * g0) _ _
            (Q'.mul_eqv_congr_right _ _ (d2 * g1) hpow)
        have hmul :
            (d1 * g0) * (d1 * g2) ≤
              (d1 * g0) * (qnext * (d2 * g1)) :=
          Q'.le_trans' _ _ _ ht
            (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))
        have hfactor : (0 : Q') < d1 * g0 :=
          Q'.mul_pos (Q'.ofNat_succ_pos (k + 1))
            (bondMovedCoeff_p2_pos_full_support hwpos (by omega))
        exact Q'.le_of_mul_le_mul_left hmul hfactor

/-- Package the propagated family as the exact division-free residual expected
by the existing all-cutoff compiler. -/
def p2CoeffTailRatio_of_strongTuran {N : Nat} {w : Q'}
    (hwpos : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (T : P2RetunedStrongTuran N w (Q'.le_of_lt hwpos) hw1) :
    P2RetunedCoeffTailRatio N w (Q'.le_of_lt hwpos) hw1 where
  tail := coeffTailRatio_of_strongTuran hwpos hw1 T

/-- The strong Turan family plus its first edge compiles all the way to the
reviewed physical `p=2` carrier. -/
def canonicalBulkControl_p2_of_strongTuran {N : Nat} {w : Q'}
    (hN : 1 ≤ N) (hwpos : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (hnc : (1 : Q') - w ≤ SpectralLocalizationCrux.q112)
    (T : P2RetunedStrongTuran N w (Q'.le_of_lt hwpos) hw1) :
    RebasedBulkLocalizationBridge.CanonicalBulkControl N w 2 :=
  canonicalBulkControl_p2_of_coeffTail hN (Q'.le_of_lt hwpos) hw1 hnc
    (p2CoeffTailRatio_of_strongTuran hwpos hw1 T)

/-- Weighted-box form of the complete compiler.  This is the direct consumer
for a future all-cutoff interlacing theorem. -/
def canonicalBulkControl_p2_of_boxStrongTuran {N : Nat} {w : Q'}
    (hN : 1 ≤ N) (hwpos : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (hnc : (1 : Q') - w ≤ SpectralLocalizationCrux.q112)
    (B : P2RetunedBoxStrongTuran N w (Q'.le_of_lt hwpos) hw1) :
    RebasedBulkLocalizationBridge.CanonicalBulkControl N w 2 :=
  canonicalBulkControl_p2_of_strongTuran hN hwpos hw1 hnc
    (strongTuran_of_box (Q'.le_of_lt hwpos) hw1 B)

end YMGap.Continuum.P2RetunedStrongTuranCompiler

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedStrongTuranCompiler.coeffTailRatio_of_strongTuran
#print axioms YMGap.Continuum.P2RetunedStrongTuranCompiler.strongTuran_of_box
#print axioms YMGap.Continuum.P2RetunedStrongTuranCompiler.p2CoeffTailRatio_of_strongTuran
#print axioms YMGap.Continuum.P2RetunedStrongTuranCompiler.canonicalBulkControl_p2_of_strongTuran
#print axioms YMGap.Continuum.P2RetunedStrongTuranCompiler.canonicalBulkControl_p2_of_boxStrongTuran
