/-
`FusedSpectralCarrierBridge` — exact spectral identification and physical pin audit.

The corrected fused rate `lamPW` is not a new surrogate.  For every excited
channel it is EXACTLY the existing `p = 2` vacuum-normalized bond-moved
transfer eigenvalue `VacNormEigShift.vacNorm`.  Consequently the existing
vacuum-normalized defect `normEigShift` compares it to the multiplicity-free
retuned `effTransfer` eigenvalue, while `effTransfer_located_gap` supplies the
located gap at that retuned weight.

The comparison has the additive lattice-margin form

  (1 - retunedEigenvalue) - normEigShift <= 1 - lamPW.

Two explicit pin hypotheses then transport this exact spectral statement to
the `massLat` fields of `TrueMarginRecursionPhysical`; no legacy recursion atom
is used or inhabited.  The pins are deliberately hypotheses: identifying the
constructed finite-character spectrum with the physical carrier, including
its spacing law, remains the real frontier.

A kernel-decided fence shows why the retune is mandatory.  At the exact pilot
anchor, the same-weight `effTransfer` eigenvalue is not merely unequal to
`lamPW`: it fails to upper-bound it.

Constructive contract: exact `Q'`/`Nat`, finite character sums, proved
Peter--Weyl and quotient-collapse identities; no `Classical`, `Real`,
`native_decide`, axioms, or holes.
-/

import YMGap.Continuum.FusedPeterWeylNormalization
import YMGap.Continuum.VacNormEigShift
import YMGap.Continuum.MultiPlaquetteEffectiveTransfer
import YMGap.Continuum.CircleFourierPowerModel
import YMGap.Continuum.TrueMarginRecursionPhysical

namespace YMGap.Continuum.FusedSpectralCarrierBridge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusedRatioCorridor
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.PeterWeylRealWeight
open YMGap.Continuum.VacNormEigShift
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.EigenvalueShiftBridge
open YMGap.Continuum.MultiPlaquetteEffectiveTransfer
open YMGap.Continuum.ClusteringImpliesGap
open YMGap.Continuum.HeatKernelGap

/-! ## 1. Exact identification of the fused eigenvalue -/

/-- **Exact spectral identification.**  On every excited channel,
`lamPW = bondMovedCoeff(s) / (dim_s * bondMovedCoeff(0))`: the corrected fused
Peter--Weyl rate is exactly the existing `p = 2` vacuum-normalized transfer
eigenvalue.  Thus the representation dimension is outside the eigenvalue as a
multiplicity, and the blocked vacuum is divided out exactly once. -/
theorem lamPW_eq_vacNorm_p2 {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (N k : Nat) :
    (lamPW w N (k + 1)).eqv
      (vacNorm N 2 (by decide) hw0 hw1 (k + 1)) := by
  have hV : (0 : Q') < boxSum w N 0 :=
    FusedRatioCorridor.pos_of_one_le
      (FusedEnvelope.vacuum_ge_one hw0 N)
  have hdim :
      (dimQ (k + 1) * Q'.invSucc (k + 1)).eqv (1 : Q') :=
    Q'.ofNat_succ_mul_invSucc (k + 1)
  have h0 := bondMovedCoeff_eq_boxSum (w := w) N 0
  have hs := bondMovedCoeff_eq_boxSum (w := w) N (k + 1)
  have hpwden :
      (lamPW w N (k + 1) *
          (dimQ (k + 1) * bondMovedCoeff N w 2 0)).eqv
        (lamB w N (k + 1) * bondMovedCoeff N w 2 0) := by
    unfold lamPW
    rw [haarSubKernel_diag_excited]
    refine Q'.eqv_trans _
      ((lamB w N (k + 1) * Q'.invSucc (k + 1)) *
        (dimQ (k + 1) * bondMovedCoeff N w 2 0)) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv _))) ?_
    refine Q'.eqv_trans _
      ((dimQ (k + 1) * Q'.invSucc (k + 1)) *
        (lamB w N (k + 1) * bondMovedCoeff N w 2 0)) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hdim) ?_
    exact Q'.one_mul_eqv _
  have hlambmc :
      (lamB w N (k + 1) * bondMovedCoeff N w 2 0).eqv
        (boxSum w N (k + 1)) := by
    unfold lamB
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ h0) ?_
    refine Q'.eqv_trans _
      (boxSum w N (k + 1) *
        (boxSum w N 0 * Q'.recip (boxSum w N 0))) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recip_eqv _ hV)) ?_
    exact Q'.mul_one_eqv _
  have hnum :
      (bondMovedCoeff N w 2 (k + 1)).eqv
        (lamPW w N (k + 1) *
          (dimQ (k + 1) * bondMovedCoeff N w 2 0)) := by
    exact Q'.eqv_trans _ _ _ hs
      (Q'.eqv_symm (Q'.eqv_trans _ _ _ hpwden hlambmc))
  exact Q'.eqv_symm (divPos_eqv_of_eqv_mul _ hnum)

/-! ## 2. The same-weight mismatch and the mandatory retune -/

/-- The same-weight effective rate is not the fused rate at the exact anchor. -/
theorem bare_effTransfer_mismatch :
    ¬ (lamPW FusedRatioCorridor.w0 3 1).eqv
      ((effTransfer FusedRatioCorridor.w0 (by decide) 1).lam 0) := by decide

/-- Stronger fence: the same-weight effective eigenvalue does not even
upper-bound the fused eigenvalue at the exact anchor.  A next-scale retune (or
an explicit defect) is mathematically mandatory. -/
theorem bare_effTransfer_not_upper_anchor :
    ¬ (lamPW FusedRatioCorridor.w0 3 1 ≤
      (effTransfer FusedRatioCorridor.w0 (by decide) 1).lam 0) := by decide

/-- The multiplicity-free effective transfer at the `p = 2` retuned weight has
a located spectral gap for every `0 < w < 1`. -/
def retunedEffLocatedGap {w : Q'} (hwpos : (0 : Q') < w)
    (hw1 : w ≤ (1 : Q')) (hwlt : w < (1 : Q')) (M : Nat) :
    LocatedSpectralGap
      (effTransfer (renormWFix 2 (by decide) w)
        (Q'.le_of_lt
          (ClusteringImpliesGap.lt_of_lt_of_le hwpos
            (w_le_renormWFix (Q'.le_of_lt hwpos) hw1 2 (by decide))))
        (M + 1)) :=
  effTransfer_located_gap
    (ClusteringImpliesGap.lt_of_lt_of_le hwpos
      (w_le_renormWFix (Q'.le_of_lt hwpos) hw1 2 (by decide)))
    (renormWFix_le_one hw1 2 (by decide))
    (renormWFix_lt_one hwlt 2 (by decide)) M

/-- Its margin is definitionally the retuned heat-kernel margin. -/
theorem retunedEffLocatedGap_margin {w : Q'} (hwpos : (0 : Q') < w)
    (hw1 : w ≤ (1 : Q')) (hwlt : w < (1 : Q')) (M : Nat) :
    (retunedEffLocatedGap hwpos hw1 hwlt M).gapMargin =
      (1 : Q') - heatKernelSep (renormWFix 2 (by decide) w) := rfl

/-! ## 3. Exact defect comparison and additive lattice-margin erosion -/

/-- The corrected fused eigenvalue is bounded by the retuned effective
eigenvalue plus the already-defined genuine vacuum-normalized spectral defect.
No representation dimension occurs in either eigenvalue slot. -/
theorem lamPW_retuned_eff_upper {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (N k : Nat) :
    lamPW w N (k + 1) ≤
      normEigShift N 2 (by decide) hw0 hw1 (k + 1) +
        (effTransfer (renormWFix 2 (by decide) w)
          (renormWFix_nonneg hw0 2 (by decide)) (k + 1)).lam k := by
  have hlam := lamPW_eq_vacNorm_p2 hw0 hw1 N k
  have hdef :
      vacNorm N 2 (by decide) hw0 hw1 (k + 1) +
          -(retEig 2 (by decide) w (k + 1)) ≤
        normEigShift N 2 (by decide) hw0 hw1 (k + 1) :=
    FusionQuotientCollapse.le_absQ _
  have hvac :
      vacNorm N 2 (by decide) hw0 hw1 (k + 1) ≤
        normEigShift N 2 (by decide) hw0 hw1 (k + 1) +
          retEig 2 (by decide) w (k + 1) :=
    EigenvalueShiftBridge.le_add_of_sub_le hdef
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hlam) hvac

/-- The spectral comparison in the exact additive lattice-margin orientation:
the fused outgoing margin loses at most `normEigShift` from the retuned
effective incoming margin. -/
theorem fused_margin_after_retuned_erosion {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N k : Nat) :
    ((1 : Q') -
        (effTransfer (renormWFix 2 (by decide) w)
          (renormWFix_nonneg hw0 2 (by decide)) (k + 1)).lam k) -
      normEigShift N 2 (by decide) hw0 hw1 (k + 1) ≤
        (1 : Q') - lamPW w N (k + 1) := by
  let shift := normEigShift N 2 (by decide) hw0 hw1 (k + 1)
  let eig := (effTransfer (renormWFix 2 (by decide) w)
    (renormWFix_nonneg hw0 2 (by decide)) (k + 1)).lam k
  have hup : lamPW w N (k + 1) ≤ shift + eig :=
    lamPW_retuned_eff_upper hw0 hw1 N k
  have hneg : -(shift + eig) ≤ -(lamPW w N (k + 1)) := Q'.neg_le_neg hup
  have hadd : (1 : Q') + -(shift + eig) ≤
      (1 : Q') + -(lamPW w N (k + 1)) :=
    Q'.add_le_add_left 1 _ _ hneg
  have hleft : (((1 : Q') - eig) - shift).eqv
      ((1 : Q') + -(shift + eig)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv 1 (-eig) (-shift)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 1 _ _ (Q'.add_comm_eqv (-eig) (-shift))) ?_
    exact Q'.add_eqv_congr_left 1 _ _
      (Q'.eqv_symm (Q'.neg_add_eqv shift eig))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hadd

/-! ## 4. Honest connection to `TrueMarginRecursionPhysical` -/

/-- If consecutive physical lattice masses are explicitly pinned to the
retuned effective and fused spectral margins, the genuine spectral defect
gives their additive step.  These two pins are precisely the physical
identification still required; this theorem does not manufacture them from an
underconstrained carrier. -/
theorem physical_mass_step_of_spectral_pins
    (T : TrueMarginRecursionPhysical) (j : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N k : Nat)
    (hret : T.massLat j =
      (1 : Q') -
        (effTransfer (renormWFix 2 (by decide) w)
          (renormWFix_nonneg hw0 2 (by decide)) (k + 1)).lam k)
    (hfused : T.massLat (j + 1) =
      (1 : Q') - lamPW w N (k + 1)) :
    T.massLat j - normEigShift N 2 (by decide) hw0 hw1 (k + 1) ≤
      T.massLat (j + 1) := by
  rw [hret, hfused]
  exact fused_margin_after_retuned_erosion hw0 hw1 N k

/-- If a physical lattice mass is pinned to the constructed retuned located
gap, its physical margin is exactly that located margin divided by the actual
positive lattice spacing.  This exposes, rather than hides, the remaining
spacing-uniform comparison. -/
theorem physical_margin_of_retuned_gap_pin
    (T : TrueMarginRecursionPhysical) (j : Nat) {w : Q'}
    (hwpos : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (hwlt : w < (1 : Q')) (M : Nat)
    (hpin : T.massLat j = (retunedEffLocatedGap hwpos hw1 hwlt M).gapMargin) :
    T.margin j = Q'.divPos
      ((1 : Q') - heatKernelSep (renormWFix 2 (by decide) w))
      (T.spacing j) (T.spacing_pos j) := by
  rw [T.margin_def j, hpin, retunedEffLocatedGap_margin]

end YMGap.Continuum.FusedSpectralCarrierBridge

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.FusedSpectralCarrierBridge.lamPW_eq_vacNorm_p2
#print axioms YMGap.Continuum.FusedSpectralCarrierBridge.bare_effTransfer_mismatch
#print axioms YMGap.Continuum.FusedSpectralCarrierBridge.bare_effTransfer_not_upper_anchor
#print axioms YMGap.Continuum.FusedSpectralCarrierBridge.retunedEffLocatedGap
#print axioms YMGap.Continuum.FusedSpectralCarrierBridge.retunedEffLocatedGap_margin
#print axioms YMGap.Continuum.FusedSpectralCarrierBridge.lamPW_retuned_eff_upper
#print axioms YMGap.Continuum.FusedSpectralCarrierBridge.fused_margin_after_retuned_erosion
#print axioms YMGap.Continuum.FusedSpectralCarrierBridge.physical_mass_step_of_spectral_pins
#print axioms YMGap.Continuum.FusedSpectralCarrierBridge.physical_margin_of_retuned_gap_pin
