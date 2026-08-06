/-
Track 11.7-fusion / R2y -- integral certificates for physical mode one.

Direct reduction of `p2VacNorm` makes the rational denominator grow once per
summand.  This module instead clears the single denominator

    den^(2*C4(N))

from the two-fold fusion coefficient and evaluates the resulting expression
in `Nat`.  The reconstruction theorem is uniform in the rational heat weight,
so finite trajectory cells require only one integer comparison rather than a
large rational normalization.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2DyadicVacLipPolynomial
import YMGap.Continuum.P2RetunedFenceIntegralCertificate

namespace YMGap.Continuum.P2VacNormIntegralCertificate

set_option maxRecDepth 30000
set_option exponentiation.threshold 10000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionMarginMono
open YMGap.Continuum.P2DyadicFusionGapEnvelope
open YMGap.Continuum.P2RetunedFenceIntegralCertificate
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RGTransport
open YMGap.Continuum.VacNormEigShift

local infix:50 " ≈ " => Q'.eqv

/-- One fusion summand after clearing `den^(2*C4(N))`. -/
def scaledTermAt (num den N s a b : Nat) : Nat :=
  if fusionOK a b s then
    (a + 1) * (b + 1) * num ^ (c4 a + c4 b) *
      den ^ (2 * c4 N - (c4 a + c4 b))
  else 0

/-- The cleared two-fold fusion coefficient. -/
def scaledCoeffAt (num den N s : Nat) : Nat :=
  natSum
    (fun a => natSum (fun b => scaledTermAt num den N s a b) (N + 1))
    (N + 1)

theorem qpow_mkPosNat_eqv (num den : Nat) (hden : 0 < den) :
    forall n : Nat,
      qpow (Q'.mkPos num den hden) n ≈
        Q'.mkPos ((num ^ n : Nat) : Int) (den ^ n)
          (Nat.pow_pos hden)
  | 0 => by
      change (1 : Q').eqv (Q'.mkPos 1 1 (by decide))
      decide
  | n + 1 => by
      unfold qpow
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (qpow_mkPosNat_eqv num den hden n)) ?_
      simpa only [Nat.pow_succ, Int.natCast_mul] using
        mkPos_mul_mkPos ((num ^ n : Nat) : Int) num (den ^ n) den
          (Nat.pow_pos hden) hden

theorem scale_monomialAt_eqv (num den E e C : Nat)
    (hden : 0 < den) (he : e <= E) :
    Q'.ofNat (den ^ E) *
        (Q'.ofNat C * qpow (Q'.mkPos num den hden) e) ≈
      Q'.ofNat (C * num ^ e * den ^ (E - e)) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (qpow_mkPosNat_eqv num den hden e))) ?_
  have hE : E = e + (E - e) := by omega
  have hpow : den ^ E = den ^ e * den ^ (E - e) := by
    calc
      den ^ E = den ^ (e + (E - e)) := congrArg (fun n => den ^ n) hE
      _ = den ^ e * den ^ (E - e) := Nat.pow_add den e (E - e)
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den]
  rw [hpow]
  push_cast
  simp only [Int.mul_one, Int.one_mul]
  ac_rfl

theorem scaledTermAt_eqv (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (N s a b : Nat) (ha : a < N + 1) (hb : b < N + 1) :
    Q'.ofNat (den ^ (2 * c4 N)) *
        (fusionInd a b s * (coeffW w a * coeffW w b)) ≈
      Q'.ofNat (scaledTermAt num den N s a b) := by
  have hac : c4 a <= c4 N :=
    YMGap.Continuum.SpectralLocalizationCrux.c4_le_c4 (by omega)
  have hbc : c4 b <= c4 N :=
    YMGap.Continuum.SpectralLocalizationCrux.c4_le_c4 (by omega)
  have he : c4 a + c4 b <= 2 * c4 N := by omega
  unfold fusionInd scaledTermAt
  by_cases h : fusionOK a b s
  · simp only [if_pos h]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ ?_) (scale_monomialAt_eqv _ _ _ _ _ hden he)
    refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
    refine Q'.eqv_trans _ _ _
      (YMGap.Continuum.FusionRDFactor.coeffW_mul_rd_sym a b) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (BondMovingRelResidual.qpow_eqv_congr_base hw (c4 a + c4 b))
  · simp only [if_neg h]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _)) ?_
    exact YMGap.Constructive.QPoly.q_mul_zero _

/-- Uniform reconstruction of one cleared physical fusion coefficient. -/
theorem scaledCoeffAt_reconstruct (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden) (N s : Nat) :
    Q'.ofNat (den ^ (2 * c4 N)) * bondMovedCoeff N w 2 s ≈
      Q'.ofNat (scaledCoeffAt num den N s) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (YMGap.Continuum.FusionRDFactor.bondMovedCoeff_p2_doubleSum N s)) ?_
  apply scale_fsum_eqv
  intro a ha
  apply scale_fsum_eqv
  intro b hb
  exact scaledTermAt_eqv num den hden w hw N s a b ha hb

theorem scaledDimCoeffAt_reconstruct (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (N mode coeffMode : Nat) :
    Q'.ofNat (den ^ (2 * c4 N)) *
        (dimQ mode * bondMovedCoeff N w 2 coeffMode) ≈
      Q'.ofNat ((mode + 1) * scaledCoeffAt num den N coeffMode) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (scaledCoeffAt_reconstruct num den hden w hw N coeffMode)) ?_
  exact Q'.eqv_symm
    (YMGap.Continuum.FusionRDFactor.ofNat_mul_eqv (mode + 1)
      (scaledCoeffAt num den N coeffMode))

private theorem ofNat_pos_of_pos {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  show (0 : Int) * (1 : Int) < (n : Int) * (1 : Int)
  simp only [Int.mul_one]
  exact_mod_cast hn

private theorem qeqv_of_le_of_ge {a b : Q'}
    (hab : a <= b) (hba : b <= a) : a ≈ b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

private theorem divPos_eqv_congr {a a' b b' : Q'}
    (hb : (0 : Q') < b) (hb' : (0 : Q') < b')
    (haEq : a ≈ a') (hbEq : b ≈ b') :
    Q'.divPos a b hb ≈ Q'.divPos a' b' hb' := by
  apply qeqv_of_le_of_ge
  · apply Q'.le_divPos_of_mul_le a' b' hb'
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a b hb) b' b
          (Q'.eqv_symm hbEq))
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a b hb) haEq))
  · apply Q'.le_divPos_of_mul_le a b hb
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a' b' hb') b b' hbEq)
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a' b' hb')
          (Q'.eqv_symm haEq)))

private theorem divPos_eqv_of_cross {p q p' q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : p * q' ≈ p' * q) :
    Q'.divPos p q hq ≈ Q'.divPos p' q' hq' := by
  let c := Q'.divPos p' q' hq'
  have hright : (c * q) * q' ≈ p' * q := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c q q') ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left c _ _ (Q'.mul_comm_eqv q q')) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv c q' q)) ?_
    exact Q'.mul_eqv_congr_right _ _ q (Q'.divPos_mul_eqv p' q' hq')
  have hmul : p * q' ≈ (c * q) * q' :=
    Q'.eqv_trans _ _ _ hcross (Q'.eqv_symm hright)
  have hcancel : p ≈ c * q := by
    apply Q'.mul_left_cancel_of_pos hq'
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q' p) ?_
    refine Q'.eqv_trans _ _ _ hmul ?_
    exact Q'.mul_comm_eqv (c * q) q'
  apply Q'.mul_left_cancel_of_pos hq
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q (Q'.divPos p q hq)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv p q hq) ?_
  refine Q'.eqv_trans _ _ _ hcancel ?_
  exact Q'.mul_comm_eqv c q

private theorem divPos_eqv_scaled {p q scale : Q'}
    (hq : (0 : Q') < q) (hscale : (0 : Q') < scale) :
    Q'.divPos p q hq ≈
      Q'.divPos (scale * p) (scale * q) (Q'.mul_pos hscale hq) := by
  apply divPos_eqv_of_cross
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv p scale q)) ?_
  exact Q'.mul_eqv_congr_right _ _ q (Q'.mul_comm_eqv p scale)

/-- The integral mode-one quotient.  Its denominator is positive whenever the
cleared vacuum coefficient is positive. -/
def scaledModeOne (num den N : Nat)
    (hzero : 0 < scaledCoeffAt num den N 0) : Q' :=
  Q'.divPos
    (Q'.ofNat (scaledCoeffAt num den N 1))
    (Q'.ofNat (2 * scaledCoeffAt num den N 0))
    (ofNat_pos_of_pos (Nat.mul_pos (by decide) hzero))

/-- Reconstruction of physical `p2VacNorm` from the integral evaluator. -/
theorem p2VacNorm_one_eqv_scaled (num den : Nat) (hden : 0 < den)
    (w : Q') (hwEq : w ≈ Q'.mkPos num den hden)
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) (N : Nat)
    (hzero : 0 < scaledCoeffAt num den N 0) :
    p2VacNorm N hw0 hw1 1 ≈ scaledModeOne num den N hzero := by
  let scale := Q'.ofNat (den ^ (2 * c4 N))
  let numerator := bondMovedCoeff N w 2 1
  let denominator := dimQ 1 * bondMovedCoeff N w 2 0
  have hscale : (0 : Q') < scale :=
    ofNat_pos_of_pos (Nat.pow_pos hden)
  have hdenominator : (0 : Q') < denominator :=
    p2DenomPos N hw0 hw1 1
  have hscaledDenominator : (0 : Q') < scale * denominator :=
    Q'.mul_pos hscale hdenominator
  have hnatDenominator :
      (0 : Q') < Q'.ofNat (2 * scaledCoeffAt num den N 0) :=
    ofNat_pos_of_pos (Nat.mul_pos (by decide) hzero)
  have hnumEq : scale * numerator ≈
      Q'.ofNat (scaledCoeffAt num den N 1) :=
    scaledCoeffAt_reconstruct num den hden w hwEq N 1
  have hdenEq : scale * denominator ≈
      Q'.ofNat (2 * scaledCoeffAt num den N 0) := by
    simpa only [denominator, dimQ] using
      scaledDimCoeffAt_reconstruct num den hden w hwEq N 1 0
  unfold p2VacNorm vacNorm scaledModeOne
  exact Q'.eqv_trans _ _ _
    (divPos_eqv_scaled hdenominator hscale)
    (divPos_eqv_congr hscaledDenominator hnatDenominator hnumEq hdenEq)

end YMGap.Continuum.P2VacNormIntegralCertificate

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2VacNormIntegralCertificate.scaledCoeffAt_reconstruct
#print axioms YMGap.Continuum.P2VacNormIntegralCertificate.p2VacNorm_one_eqv_scaled
