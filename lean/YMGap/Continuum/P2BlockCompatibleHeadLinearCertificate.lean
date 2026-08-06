/-
Track 11.7-fusion / R3h -- sparse linear-time certificates for the physical
coefficient head.

The generic integral certificate evaluates a Clebsch double sum.  At the sole
parity head `s=1`, however, the two required channels have proved sparse
forms: channel one is the adjacent band, while channel two is one diagonal
and the two orientations of the distance-two band.  This module reflects
those formulas into `Nat`, proves that the resulting linear-size evaluator is
exactly the generic coefficient evaluator, and exposes the same sound target.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleIntegralTailCertificate
import YMGap.Continuum.P2RetunedEdgeFormula

namespace YMGap.Continuum.P2BlockCompatibleHeadLinearCertificate

set_option maxHeartbeats 12000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 850000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.EndpointCutoffTailFormula
open YMGap.Continuum.P2BlockCompatibleIntegralTailCertificate
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2RetunedEdgeFormula
open YMGap.Continuum.P2RetunedFenceIntegralCertificate
open YMGap.Continuum.P2VacNormIntegralCertificate
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

/-- Cleared one-orientation adjacent band for channel one. -/
def scaledHeadAdjAt (num den N : Nat) : Nat :=
  natSum (fun a => scaledTermAt num den N 1 a (a + 1)) N

/-- Cleared diagonal band for channel two. -/
def scaledHeadDiagAt (num den N : Nat) : Nat :=
  natSum (fun a => scaledTermAt num den N 2 (a + 1) (a + 1)) N

/-- Cleared one-orientation distance-two band for channel two. -/
def scaledHeadJumpAt (num den N : Nat) : Nat :=
  natSum (fun a => scaledTermAt num den N 2 a (a + 2)) (N - 1)

/-- Sparse cleared channel-one coefficient. -/
def scaledHeadOneAt (num den N : Nat) : Nat :=
  2 * scaledHeadAdjAt num den N

/-- Sparse cleared channel-two coefficient. -/
def scaledHeadTwoAt (num den N : Nat) : Nat :=
  scaledHeadDiagAt num den N + 2 * scaledHeadJumpAt num den N

private theorem scaledAdjTermAt_eqv
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (N a : Nat) (ha : a < N) :
    Q'.ofNat (den ^ (2 * c4 N)) *
        (coeffW w a * coeffW w (a + 1)) ≈
      Q'.ofNat (scaledTermAt num den N 1 a (a + 1)) := by
  have hterm := scaledTermAt_eqv num den hden w hw N 1 a (a + 1)
    (by omega) (by omega)
  rw [fusionInd_prev_top_one] at hterm
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.one_mul_eqv _))) hterm

private theorem scaledDiagTermAt_eqv
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (N a : Nat) (ha : a < N) :
    Q'.ofNat (den ^ (2 * c4 N)) *
        (coeffW w (a + 1) * coeffW w (a + 1)) ≈
      Q'.ofNat (scaledTermAt num den N 2 (a + 1) (a + 1)) := by
  have hf : fusionOK (a + 1) (a + 1) 2 = true :=
    (fusionOK_two_iff (a + 1) (a + 1)).2
      (Or.inl ⟨rfl, by omega⟩)
  have hone : fusionInd (a + 1) (a + 1) 2 = (1 : Q') := by
    unfold fusionInd
    rw [if_pos hf]
  have hterm := scaledTermAt_eqv num den hden w hw N 2
    (a + 1) (a + 1) (by omega) (by omega)
  rw [hone] at hterm
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.one_mul_eqv _))) hterm

private theorem scaledJumpTermAt_eqv
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (N a : Nat) (ha : a < N - 1) :
    Q'.ofNat (den ^ (2 * c4 N)) *
        (coeffW w a * coeffW w (a + 2)) ≈
      Q'.ofNat (scaledTermAt num den N 2 a (a + 2)) := by
  have hf : fusionOK a (a + 2) 2 = true :=
    (fusionOK_two_iff a (a + 2)).2 (Or.inr (Or.inl (by omega)))
  have hone : fusionInd a (a + 2) 2 = (1 : Q') := by
    unfold fusionInd
    rw [if_pos hf]
  have hterm := scaledTermAt_eqv num den hden w hw N 2
    a (a + 2) (by omega) (by omega)
  rw [hone] at hterm
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.one_mul_eqv _))) hterm

theorem scaledHeadAdjAt_reconstruct
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden) (N : Nat) :
    Q'.ofNat (den ^ (2 * c4 N)) * adjCorr w N ≈
      Q'.ofNat (scaledHeadAdjAt num den N) := by
  unfold adjCorr scaledHeadAdjAt
  apply scale_fsum_eqv
  intro a ha
  exact scaledAdjTermAt_eqv num den hden w hw N a ha

theorem scaledHeadDiagAt_reconstruct
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden) (N : Nat) :
    Q'.ofNat (den ^ (2 * c4 N)) *
        fsum (channelTwoDiag w) N ≈
      Q'.ofNat (scaledHeadDiagAt num den N) := by
  unfold channelTwoDiag scaledHeadDiagAt
  apply scale_fsum_eqv
  intro a ha
  exact scaledDiagTermAt_eqv num den hden w hw N a ha

theorem scaledHeadJumpAt_reconstruct
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden) (N : Nat) :
    Q'.ofNat (den ^ (2 * c4 N)) *
        fsum (channelTwoJump w) (N - 1) ≈
      Q'.ofNat (scaledHeadJumpAt num den N) := by
  unfold channelTwoJump scaledHeadJumpAt
  apply scale_fsum_eqv
  intro a ha
  exact scaledJumpTermAt_eqv num den hden w hw N a ha

private theorem ofNat_eqv_injective {left right : Nat}
    (h : Q'.ofNat left ≈ Q'.ofNat right) : left = right := by
  unfold Q'.eqv Q'.ofNat Q'.den at h
  simpa using (Int.ofNat.inj h)

theorem scaledHeadOneAt_reconstruct
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden) (N : Nat) :
    Q'.ofNat (den ^ (2 * c4 N)) * boxSum w N 1 ≈
      Q'.ofNat (scaledHeadOneAt num den N) := by
  let scale := Q'.ofNat (den ^ (2 * c4 N))
  have hbox := boxSum_one_eq_twice_adjCorr w N
  change boxSum w N 1 ≈ Q'.ofNat 2 * adjCorr w N at hbox
  have hAdj := scaledHeadAdjAt_reconstruct num den hden w hw N
  have halg :
      scale * (Q'.ofNat 2 * adjCorr w N) ≈
        Q'.ofNat 2 * (scale * adjCorr w N) := by
    ring_qeqv
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left scale _ _ hbox) ?_
  refine Q'.eqv_trans _ _ _ halg ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hAdj) ?_
  unfold scaledHeadOneAt
  exact Q'.eqv_symm
    (YMGap.Continuum.FusionRDFactor.ofNat_mul_eqv 2
      (scaledHeadAdjAt num den N))

theorem scaledHeadTwoAt_reconstruct
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden) (N : Nat) :
    Q'.ofNat (den ^ (2 * c4 N)) * boxSum w N 2 ≈
      Q'.ofNat (scaledHeadTwoAt num den N) := by
  let scale := Q'.ofNat (den ^ (2 * c4 N))
  have hbox := boxSum_two_eq_formula w N
  have hDiag := scaledHeadDiagAt_reconstruct num den hden w hw N
  have hJump := scaledHeadJumpAt_reconstruct num den hden w hw N
  have halg :
      scale * channelTwoFormula w N ≈
        scale * fsum (channelTwoDiag w) N +
          Q'.ofNat 2 *
            (scale * fsum (channelTwoJump w) (N - 1)) := by
    unfold channelTwoFormula
    ring_qeqv
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left scale _ _ hbox) ?_
  refine Q'.eqv_trans _ _ _ halg ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hDiag
      (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hJump)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (YMGap.Continuum.FusionRDFactor.ofNat_mul_eqv 2
          (scaledHeadJumpAt num den N)))) ?_
  unfold scaledHeadTwoAt
  exact Q'.eqv_symm
    (Q'.ofNat_add_eqv (scaledHeadDiagAt num den N)
      (2 * scaledHeadJumpAt num den N))

theorem scaledCoeffAt_one_eq_headOne
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden) (N : Nat) :
    scaledCoeffAt num den N 1 = scaledHeadOneAt num den N := by
  apply ofNat_eqv_injective
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (scaledCoeffAt_reconstruct num den hden w hw N 1)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (bondMovedCoeff_eq_boxSum N 1)) ?_
  exact scaledHeadOneAt_reconstruct num den hden w hw N

theorem scaledCoeffAt_two_eq_headTwo
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden) (N : Nat) :
    scaledCoeffAt num den N 2 = scaledHeadTwoAt num den N := by
  apply ofNat_eqv_injective
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (scaledCoeffAt_reconstruct num den hden w hw N 2)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (bondMovedCoeff_eq_boxSum N 2)) ?_
  exact scaledHeadTwoAt_reconstruct num den hden w hw N

/-- Linear-size cleared comparison for the `s=1` adjacent coefficient atom. -/
def linearHeadAt (num den qnum qden N : Nat) : Prop :=
  2 * scaledHeadTwoAt num den N * qden ^ 5 ≤
    qnum ^ 5 * (3 * scaledHeadOneAt num den N)

instance linearHeadAtDecidable (num den qnum qden N : Nat) :
    Decidable (linearHeadAt num den qnum qden N) := by
  unfold linearHeadAt
  infer_instance

theorem integralTailAt_one_of_linearHeadAt
    (num den qnum qden N : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (h : linearHeadAt num den qnum qden N) :
    P2BlockCompatibleIntegralTailCertificate.integralTailAt
      num den qnum qden N 1 := by
  unfold linearHeadAt at h
  unfold P2BlockCompatibleIntegralTailCertificate.integralTailAt
  rw [scaledCoeffAt_one_eq_headOne num den hden w hw N,
    scaledCoeffAt_two_eq_headTwo num den hden w hw N]
  simpa only using h

/-- Sparse schedule-native head atom. -/
def physicalLinearHeadAt (k : Nat) : Prop :=
  linearHeadAt
    (physicalWeightNum k) (physicalWeightDen k)
    (physicalRetunedNum k) (physicalRetunedDen k)
    (blockNcut k)

instance physicalLinearHeadAtDecidable (k : Nat) :
    Decidable (physicalLinearHeadAt k) := by
  unfold physicalLinearHeadAt
  infer_instance

theorem physicalIntegralTailAt_one_of_linearHeadAt (k : Nat)
    (h : physicalLinearHeadAt k) : physicalIntegralTailAt k 1 := by
  unfold physicalLinearHeadAt at h
  unfold physicalIntegralTailAt
  exact integralTailAt_one_of_linearHeadAt _ _ _ _ _
    (physicalWeightDen_pos k) (blockWeight k)
    (blockWeight_eqv_closed k) h

/-! ## Sparse exact physical head cells -/

/-- The sparse evaluator makes the previously intractable scale-six head a
single axiom-free kernel comparison. -/
theorem physicalLinearHeadCheck_six : physicalLinearHeadAt 6 := by decide

/-- Scale seven remains feasible with the same proved linear representation. -/
theorem physicalLinearHeadCheck_seven : physicalLinearHeadAt 7 := by decide

theorem physicalIntegralHeadCheck_six : physicalIntegralTailAt 6 1 :=
  physicalIntegralTailAt_one_of_linearHeadAt 6 physicalLinearHeadCheck_six

theorem physicalIntegralHeadCheck_seven : physicalIntegralTailAt 7 1 :=
  physicalIntegralTailAt_one_of_linearHeadAt 7 physicalLinearHeadCheck_seven

#print axioms scaledHeadOneAt_reconstruct
#print axioms scaledHeadTwoAt_reconstruct
#print axioms scaledCoeffAt_one_eq_headOne
#print axioms scaledCoeffAt_two_eq_headTwo
#print axioms integralTailAt_one_of_linearHeadAt
#print axioms physicalIntegralTailAt_one_of_linearHeadAt
#print axioms physicalLinearHeadCheck_six
#print axioms physicalLinearHeadCheck_seven
#print axioms physicalIntegralHeadCheck_six
#print axioms physicalIntegralHeadCheck_seven

end YMGap.Continuum.P2BlockCompatibleHeadLinearCertificate
