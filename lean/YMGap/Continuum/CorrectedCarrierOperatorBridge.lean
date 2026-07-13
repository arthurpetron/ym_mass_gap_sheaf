/-
Operator-level realization and spacing audit for the corrected cutoff-tail
carrier.

The fused rate is realized as the eigenvalue of a concrete one-channel finite
self-adjoint transfer operator.  The corrected carrier then gives a located
gap whenever its derived quadratic-plus-cutoff budget lies strictly inside the
refined retuned margin.  At fixed spacing the same lattice inequality transports
to a physical mass inequality by exact division.

Two kernel-checked fences isolate what this does not supply.  The fused and
refined spectra are not equal even at the exact endpoint, and a stationary
constructed operator gap does not imply the corresponding varying-spacing
physical inequality.  Thus the missing datum is an operator RG/spacing
intertwining law, not another scalar defect estimate.
-/

import YMGap.Continuum.CutoffTailRefinedCarrier
import YMGap.Continuum.CompactTransferGNS
import YMGap.Continuum.SpectralMarginBridge

namespace YMGap.Continuum.CorrectedCarrierOperatorBridge

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.CompactTransferGNS
open YMGap.Continuum.CutoffTailRefinedCarrier
open YMGap.Continuum.EndpointCutoffTailClose
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedRefinedSpectralBridge
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RefinedRetune
open YMGap.Continuum.SpectralMarginBridge
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.VacNormEigShift

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A concrete operator whose excited eigenvalue is exactly `lamPW` -/

/-- The single excited diagonal entry of the fused transfer operator. -/
def fusedChannelLam (w : Q') (N s : Nat) : QSeq := fun _ => lamPW w N s

/-- Unit Kallen--Lehmann weight for the selected channel. -/
def fusedChannelWeight : QSeq := fun _ => (1 : Q')

theorem fusedChannelWeight_nonneg : forall i, (0 : Q') <= fusedChannelWeight i := by
  intro i
  exact Q'.zero_le_one

/-- `lamPW` is nonnegative because it is exactly the vacuum-normalized finite
character-sum eigenvalue. -/
theorem lamPW_nonneg {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (N k : Nat) : (0 : Q') <= lamPW w N (k + 1) := by
  have hv :
      (0 : Q') <= vacNorm N 2 (by decide) hw0 hw1 (k + 1) := by
    unfold vacNorm Q'.divPos
    exact Q'.mul_nonneg _ _
      (bondMovedCoeff_nonneg N hw0 2 (k + 1))
      (Q'.le_of_lt (Q'.recipPos_pos _ _))
  exact Q'.le_trans' _ _ _ hv
    (Q'.ge_of_eqv (lamPW_eq_vacNorm_p2 hw0 hw1 N k))

theorem fusedChannelLam_nonneg {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) (N k : Nat) :
    forall i, (0 : Q') <= fusedChannelLam w N (k + 1) i := by
  intro i
  exact lamPW_nonneg hw0 hw1 N k

/-- The concrete one-channel self-adjoint finite transfer operator. -/
def fusedChannelOp (w : Q') (N s : Nat) : FiniteOp :=
  diagOp (fusedChannelLam w N s) 1

/-- Its realized positive spectral model. -/
def fusedChannelModel {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (N k : Nat) : SpectralGap.SpectralModel :=
  diagOp.toSpectralModel (fusedChannelLam w N (k + 1)) fusedChannelWeight 1
    fusedChannelWeight_nonneg (fusedChannelLam_nonneg hw0 hw1 N k)

/-- Exact operator-level spectral identification: the selected `lamPW` is the
diagonal operator eigenvalue, not merely a comparison sequence. -/
theorem fusedChannel_operator_eigen {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) (N k : Nat) :
    ((fusedChannelModel hw0 hw1 N k).lam 0) ≈
      ((fusedChannelOp w N (k + 1)).apply (basis 0) 0) := by
  exact toSpectralModel_lam_is_eigen
    (fusedChannelLam w N (k + 1)) fusedChannelWeight 1
    fusedChannelWeight_nonneg (fusedChannelLam_nonneg hw0 hw1 N k) 0 (by decide)

/-- The model eigenvalue is definitionally the corrected fused rate. -/
theorem fusedChannel_model_lam {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) (N k : Nat) :
    (fusedChannelModel hw0 hw1 N k).lam 0 = lamPW w N (k + 1) := rfl

/-! ## 2. The corrected carrier constructs a located operator gap -/

/-- The sharp separator obtained from the refined retuned eigenvalue and the
honest quadratic-plus-cutoff budget. -/
def correctedSep (w Cq : Q') (N s : Nat) : Q' :=
  retEig2 2 (by decide) (refineCoeff 2 (by decide)) w s +
    (Cq * (((1 : Q') - w) * ((1 : Q') - w)) + endpointTail N)

/-- The one-field corrected carrier bounds the actual operator eigenvalue by
`correctedSep`, with no spectral-identification pin. -/
theorem fusedChannel_lam_le_correctedSep
    (N k : Nat) {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (Cq : Q') (b : CutoffTailRefinedBound N hw0 hw1 Cq (k + 1)) :
    (fusedChannelModel hw0 hw1 N k).lam 0 <= correctedSep w Cq N (k + 1) := by
  rw [fusedChannel_model_lam hw0 hw1 N k]
  have hu := lamPW_refined_upper hw0 hw1 N k (refineCoeff 2 (by decide))
  have hs := b.quadratic_add_tail
  have hadd :
      normEigShift2 N 2 (by decide) hw0 hw1 (refineCoeff 2 (by decide)) (k + 1) +
          retEig2 2 (by decide) (refineCoeff 2 (by decide)) w (k + 1) <=
        (Cq * (((1 : Q') - w) * ((1 : Q') - w)) + endpointTail N) +
          retEig2 2 (by decide) (refineCoeff 2 (by decide)) w (k + 1) :=
    Q'.add_le_add_right _ _ _ hs
  exact Q'.le_trans' _ _ _ hu
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- Whenever the explicitly derived separator is below the vacuum eigenvalue,
the corrected carrier constructs a located spectral gap for the concrete
finite transfer operator. -/
def fusedChannelLocatedGap
    (N k : Nat) {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (Cq : Q') (b : CutoffTailRefinedBound N hw0 hw1 Cq (k + 1))
    (hsep : correctedSep w Cq N (k + 1) < (1 : Q')) :
    LocatedSpectralGap (fusedChannelModel hw0 hw1 N k) :=
  diagLocatedGap (fusedChannelLam w N (k + 1)) fusedChannelWeight 1
    fusedChannelWeight_nonneg (fusedChannelLam_nonneg hw0 hw1 N k)
    (correctedSep w Cq N (k + 1)) hsep
    (fun _ => fusedChannel_lam_le_correctedSep N k hw0 hw1 Cq b)

theorem fusedChannelLocatedGap_margin
    (N k : Nat) {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (Cq : Q') (b : CutoffTailRefinedBound N hw0 hw1 Cq (k + 1))
    (hsep : correctedSep w Cq N (k + 1) < (1 : Q')) :
    (fusedChannelLocatedGap N k hw0 hw1 Cq b hsep).gapMargin =
      (1 : Q') - correctedSep w Cq N (k + 1) := rfl

/-! ## 3. The moving defect modulus is an operator-spectrum modulus -/

private theorem absQ_eqv_abs_local (x : Q') : absQ x ≈ Q'.abs x := by
  unfold absQ Q'.abs
  by_cases hx : (0 : Int) <= x.num
  · rw [if_pos hx]
    have hx' : (0 : Q') <= x := by rw [Q'.zero_le_iff_num_nonneg]; exact hx
    rw [if_pos hx']
    exact Q'.eqv_refl _
  · rw [if_neg hx]
    have hx' : ¬ (0 : Q') <= x := by rw [Q'.zero_le_iff_num_nonneg]; exact hx
    rw [if_neg hx']
    exact Q'.eqv_refl _

private theorem absQ_eqv_congr_local {x y : Q'} (h : x ≈ y) : absQ x ≈ absQ y :=
  Q'.eqv_trans _ _ _ (absQ_eqv_abs_local x)
    (Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr h)
      (Q'.eqv_symm (absQ_eqv_abs_local y)))

/-- Absolute spectral deviation of the concrete fused operator from the
refined reference eigenvalue along the moving cutoff. -/
def movingOperatorDefect (w : Nat -> Q')
    (hw0 : forall k, (0 : Q') <= w k) (hw1 : forall k, w k <= (1 : Q'))
    (channel : Nat -> Nat) (k : Nat) : Q' :=
  absQ ((fusedChannelModel (hw0 k) (hw1 k) (Ncut k) (channel k)).lam 0 +
    -(retEig2 2 (by decide) (refineCoeff 2 (by decide))
      (w k) (channel k + 1)))

/-- The moving corrected defect is exactly the absolute eigenvalue deviation
of the constructed transfer operator. -/
theorem movingOperatorDefect_eq_refinedDefect (w : Nat -> Q')
    (hw0 : forall k, (0 : Q') <= w k) (hw1 : forall k, w k <= (1 : Q'))
    (channel : Nat -> Nat) (k : Nat) :
    movingOperatorDefect w hw0 hw1 channel k ≈
      movingRefinedDefect w hw0 hw1 (fun j => channel j + 1) k := by
  unfold movingOperatorDefect movingRefinedDefect normEigShift2
  apply absQ_eqv_congr_local
  exact Q'.add_eqv_congr_right _ _ _
    (lamPW_eq_vacNorm_p2 (hw0 k) (hw1 k) (Ncut k) (channel k))

/-- Consequently `movingRefinedDefect_window_modulus` is already a modulus
for genuine constructed-operator eigenvalue errors, not merely for a scalar
surrogate. -/
theorem movingOperatorDefect_window_modulus
    (w : Nat -> Q')
    (hw0 : forall k, (0 : Q') <= w k) (hw1 : forall k, w k <= (1 : Q'))
    (channel : Nat -> Nat) (r : Nat -> Q') (Cq Aq : Q')
    (hCq : (0 : Q') <= Cq) (hAq : (0 : Q') <= Aq)
    (hr : forall k, (1 : Q') - w k <= r k)
    (b : forall k, CutoffTailRefinedBound (Ncut k) (hw0 k) (hw1 k)
      Cq (channel k + 1))
    (hquad : forall k, Cq * (r k * r k) <= Aq * invSqTerm 2 (by decide) k)
    (N M : Nat) :
    tailSum (movingOperatorDefect w hw0 hw1 channel) N M <=
      Aq * pot 2 (by decide) N + Q'.ofNat 3 * pot 2 (by decide) N := by
  have hterm : forall k,
      movingOperatorDefect w hw0 hw1 channel k <=
        movingRefinedDefect w hw0 hw1 (fun j => channel j + 1) k :=
    fun k => Q'.le_of_eqv (movingOperatorDefect_eq_refinedDefect w hw0 hw1 channel k)
  exact Q'.le_trans' _ _ _ (tailSum_le_of_termwise hterm N M)
    (CutoffTailRefinedCarrier.movingRefinedDefect_window_modulus
      w hw0 hw1 (fun j => channel j + 1) r Cq Aq hCq hAq hr b hquad N M)

/-! ## 4. Exact fixed-spacing physical transport -/

/-- The constructed outgoing lattice mass is the actual operator gap. -/
def fusedLatticeMass (w : Q') (N s : Nat) : Q' := (1 : Q') - lamPW w N s

/-- At a fixed positive spacing, the corrected operator erosion transports
exactly to the dimensionful mass inequality.  Both masses are constructed from
the identified operator spectra; there are no scalar pin hypotheses. -/
theorem fixed_spacing_physical_transport
    (N k : Nat) {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (Cq a : Q') (ha : (0 : Q') < a)
    (b : CutoffTailRefinedBound N hw0 hw1 Cq (k + 1)) :
    Q'.divPos
        ((1 : Q') - retEig2 2 (by decide) (refineCoeff 2 (by decide)) w (k + 1))
        a ha -
      Q'.divPos
        (Cq * (((1 : Q') - w) * ((1 : Q') - w)) + endpointTail N) a ha <=
      Q'.divPos (fusedLatticeMass w N (k + 1)) a ha := by
  apply hadd_of_hlat_fixed
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left _ _ _ (Q'.neg_le_neg b.quadratic_add_tail))
    (fused_margin_after_refined_erosion hw0 hw1 N k (refineCoeff 2 (by decide)))

/-! ## 5. Machine fences: the exact operator/spacing law still missing -/

/-- Same-scale spectral matching is false already at the exact endpoint:
the finite fused eigenvalue is `2/3`, while the refined retuned eigenvalue is
`1`.  A genuine RG intertwiner must include the cutoff tail. -/
theorem no_same_scale_refined_spectral_identity :
    not ((lamPW (1 : Q') 3 1) ≈
      retEig2 2 (by decide) (refineCoeff 2 (by decide)) (1 : Q') 1) := by
  decide

/-- Exact endpoint operator mass used by the spacing fence. -/
theorem endpoint_operator_mass_N3 :
    fusedLatticeMass (1 : Q') 3 1 ≈ Q'.mkPos 1 3 (by decide) := by
  decide

/-- The stationary endpoint operator obeys the zero-erosion lattice step. -/
theorem endpoint_stationary_lattice_step :
    fusedLatticeMass (1 : Q') 3 1 - (0 : Q') <=
      fusedLatticeMass (1 : Q') 3 1 := by
  decide

/-- **Spacing fence.**  The preceding true lattice step does not survive an
arbitrary change from spacing `1` to spacing `2`: the physical margin would
fall from `1/3` to `1/6`.  Therefore the operator defect/window modulus alone
cannot construct the varying-spacing physical recursion; the missing theorem
is precisely an RG operator/spacing cross-multiplication law. -/
theorem stationary_operator_not_varying_spacing_step :
    not (Q'.divPos (fusedLatticeMass (1 : Q') 3 1) (1 : Q') (by decide) -
        Q'.divPos (0 : Q') (2 : Q') (by decide) <=
      Q'.divPos (fusedLatticeMass (1 : Q') 3 1) (2 : Q') (by decide)) := by
  decide

end YMGap.Continuum.CorrectedCarrierOperatorBridge

#print axioms YMGap.Continuum.CorrectedCarrierOperatorBridge.lamPW_nonneg
#print axioms YMGap.Continuum.CorrectedCarrierOperatorBridge.fusedChannel_operator_eigen
#print axioms YMGap.Continuum.CorrectedCarrierOperatorBridge.fusedChannel_lam_le_correctedSep
#print axioms YMGap.Continuum.CorrectedCarrierOperatorBridge.fusedChannelLocatedGap
#print axioms YMGap.Continuum.CorrectedCarrierOperatorBridge.movingOperatorDefect_eq_refinedDefect
#print axioms YMGap.Continuum.CorrectedCarrierOperatorBridge.movingOperatorDefect_window_modulus
#print axioms YMGap.Continuum.CorrectedCarrierOperatorBridge.fixed_spacing_physical_transport
#print axioms YMGap.Continuum.CorrectedCarrierOperatorBridge.no_same_scale_refined_spectral_identity
#print axioms YMGap.Continuum.CorrectedCarrierOperatorBridge.endpoint_operator_mass_N3
#print axioms YMGap.Continuum.CorrectedCarrierOperatorBridge.endpoint_stationary_lattice_step
#print axioms YMGap.Continuum.CorrectedCarrierOperatorBridge.stationary_operator_not_varying_spacing_step
