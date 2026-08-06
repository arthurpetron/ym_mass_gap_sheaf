/-
Track 11.7-fusion / R3f -- direct integral certificates for the physical
block-compatible coefficient tail.

The strengthened Turan routes are constructively false on the physical
schedule, although the actual adjacent coefficient inequalities remain true
in every tested cell.  This module compiles the exact target directly from a
single common-denominator natural-number comparison.  It checks the complete
supports at the first four physical cutoffs and leaves only scales `k>=4` as
the honest schedule-wide coefficient input.  Closed schedule coordinates
further identify that residual with one pure-`Nat` family, eliminating
per-scale rational witnesses from the analytic frontier.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleScheduleCells
import YMGap.Continuum.P2BlockCompatibleScheduleClosed
import YMGap.Continuum.P2BlockCompatiblePhysicalBridge
import YMGap.Continuum.P2VacNormIntegralCertificate

namespace YMGap.Continuum.P2BlockCompatibleIntegralTailCertificate

set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option exponentiation.threshold 10000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.P2BlockCompatiblePhysicalBridge
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleCells
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2RetunedFenceIntegralCertificate
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.P2VacNormIntegralCertificate
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- Cleared form of the exact adjacent coefficient target for arbitrary
rational heat and retuned weights. -/
def integralTailAt (num den qnum qden N s : Nat) : Prop :=
  (s + 1) * scaledCoeffAt num den N (s + 1) * qden ^ (2 * s + 3) ≤
    qnum ^ (2 * s + 3) * ((s + 2) * scaledCoeffAt num den N s)

instance integralTailAtDecidable (num den qnum qden N s : Nat) :
    Decidable (integralTailAt num den qnum qden N s) := by
  unfold integralTailAt
  infer_instance

def integralTailBlockCheck
    (num den qnum qden N start length : Nat) : Bool :=
  (List.range length).all fun i =>
    decide (integralTailAt num den qnum qden N (start + i))

private theorem scaleRetunedDimCoeffAt_reconstruct
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (N s : Nat) :
    Q'.ofNat (den ^ (2 * c4 N)) *
        (qpow (p2RetunedWeight w) (2 * s + 3) *
          (dimQ (s + 1) * bondMovedCoeff N w 2 s)) ≈
      qpow (p2RetunedWeight w) (2 * s + 3) *
        Q'.ofNat ((s + 2) * scaledCoeffAt num den N s) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (scaledDimCoeffAt_reconstruct num den hden w hw N (s + 1) s)

/-- Soundness of one direct proof-about-computation cell. -/
theorem integralTailAt_sound
    (num den qnum qden N s : Nat)
    (hden : 0 < den) (hqden : 0 < qden)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (hq : p2RetunedWeight w ≈ Q'.mkPos qnum qden hqden)
    (h : integralTailAt num den qnum qden N s) :
    dimQ s * bondMovedCoeff N w 2 (s + 1) ≤
      qpow (p2RetunedWeight w) (2 * s + 3) *
        (dimQ (s + 1) * bondMovedCoeff N w 2 s) := by
  let scale := Q'.ofNat (den ^ (2 * c4 N))
  let k := 2 * s + 3
  have hcross :
      (s + 1) * scaledCoeffAt num den N (s + 1) * qden ^ k ≤
        qnum ^ k * ((s + 2) * scaledCoeffAt num den N s) := by
    simpa only [k] using h
  have hrat := ofNat_le_mkPos_mul_of_cross
    ((s + 1) * scaledCoeffAt num den N (s + 1))
    ((s + 2) * scaledCoeffAt num den N s)
    (qnum ^ k) (qden ^ k) (Nat.pow_pos hqden) hcross
  have hqpow : qpow (p2RetunedWeight w) k ≈
      Q'.mkPos ((qnum ^ k : Nat) : Int) (qden ^ k)
        (Nat.pow_pos hqden) :=
    Q'.eqv_trans _ _ _
      (BondMovingRelResidual.qpow_eqv_congr_base hq k)
      (qpow_mkPosNat_eqv qnum qden hqden k)
  have hcore :
      Q'.ofNat ((s + 1) * scaledCoeffAt num den N (s + 1)) ≤
        qpow (p2RetunedWeight w) k *
          Q'.ofNat ((s + 2) * scaledCoeffAt num den N s) :=
    Q'.le_trans' _ _ _ hrat (Q'.le_of_eqv
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hqpow)))
  have hl := scaledDimCoeffAt_reconstruct
    num den hden w hw N s (s + 1)
  have hr := scaleRetunedDimCoeffAt_reconstruct num den hden w hw N s
  have hscaled :
      scale * (dimQ s * bondMovedCoeff N w 2 (s + 1)) ≤
        scale * (qpow (p2RetunedWeight w) k *
          (dimQ (s + 1) * bondMovedCoeff N w 2 s)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
      (Q'.le_trans' _ _ _ hcore (Q'.le_of_eqv (Q'.eqv_symm hr)))
  have hscale : (0 : Q') < scale := by
    show (0 : Int) * (1 : Int) <
      ((den ^ (2 * c4 N) : Nat) : Int) * (1 : Int)
    simp only [Int.mul_one]
    exact_mod_cast (Nat.pow_pos hden)
  exact Q'.le_of_mul_le_mul_left hscaled hscale

theorem integralTailBlockCheck_sound
    (num den qnum qden N start length s : Nat)
    (hden : 0 < den) (hqden : 0 < qden)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (hq : p2RetunedWeight w ≈ Q'.mkPos qnum qden hqden)
    (hcheck : integralTailBlockCheck
      num den qnum qden N start length = true)
    (hlo : start ≤ s) (hhi : s < start + length) :
    dimQ s * bondMovedCoeff N w 2 (s + 1) ≤
      qpow (p2RetunedWeight w) (2 * s + 3) *
        (dimQ (s + 1) * bondMovedCoeff N w 2 s) := by
  have hi : s - start < length := by omega
  have hmem : s - start ∈ List.range length := List.mem_range.mpr hi
  have hrow := List.all_eq_true.mp hcheck (s - start) hmem
  have hsEq : start + (s - start) = s := by omega
  apply integralTailAt_sound num den qnum qden N s hden hqden w hw hq
  simpa only [hsEq] using of_decide_eq_true hrow

def coeffTailRatio_of_integralCheck
    (num den qnum qden N : Nat)
    (hden : 0 < den) (hqden : 0 < qden)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hw : w ≈ Q'.mkPos num den hden)
    (hq : p2RetunedWeight w ≈ Q'.mkPos qnum qden hqden)
    (hcheck : integralTailBlockCheck
      num den qnum qden N 1 (2 * N - 1) = true) :
    P2RetunedCoeffTailRatio N w hw0 hw1 where
  tail := fun s hs hsN =>
    integralTailBlockCheck_sound num den qnum qden N 1 (2 * N - 1) s
      hden hqden w hw hq hcheck hs (by omega)

/-! ## Schedule-native arithmetic frontier -/

/-- The exact physical adjacent-tail atom written solely in natural-number
coordinates.  All rational data are supplied by the closed schedule formulas
`blockWeight_eqv_closed` and `blockRetunedWeight_eqv_closed`. -/
def physicalIntegralTailAt (k s : Nat) : Prop :=
  integralTailAt
    (physicalWeightNum k) (physicalWeightDen k)
    (physicalRetunedNum k) (physicalRetunedDen k)
    (blockNcut k) s

instance physicalIntegralTailAtDecidable (k s : Nat) :
    Decidable (physicalIntegralTailAt k s) := by
  unfold physicalIntegralTailAt
  infer_instance

/-- Soundness of the schedule-native arithmetic atom. -/
theorem physicalIntegralTailAt_sound (k s : Nat)
    (h : physicalIntegralTailAt k s) :
    dimQ s * bondMovedCoeff (blockNcut k) (blockWeight k) 2 (s + 1) ≤
      qpow (p2RetunedWeight (blockWeight k)) (2 * s + 3) *
        (dimQ (s + 1) *
          bondMovedCoeff (blockNcut k) (blockWeight k) 2 s) :=
  integralTailAt_sound
    (physicalWeightNum k) (physicalWeightDen k)
    (physicalRetunedNum k) (physicalRetunedDen k)
    (blockNcut k) s
    (physicalWeightDen_pos k) (physicalRetunedDen_pos k)
    (blockWeight k) (blockWeight_eqv_closed k)
    (blockRetunedWeight_eqv_closed k) h

/-- One executable full-support scan in the closed physical coordinates. -/
def physicalIntegralTailCheck (k : Nat) : Bool :=
  integralTailBlockCheck
    (physicalWeightNum k) (physicalWeightDen k)
    (physicalRetunedNum k) (physicalRetunedDen k)
    (blockNcut k) 1 (2 * blockNcut k - 1)

/-- A successful schedule-native scan compiles directly to the physical
coefficient-tail carrier at that cutoff. -/
def blockCoeffTail_of_physicalIntegralTailCheck (k : Nat)
    (hcheck : physicalIntegralTailCheck k = true) :
    P2RetunedCoeffTailRatio (blockNcut k) (blockWeight k)
      (blockWeight_nonneg k) (blockWeight_le_one k) :=
  coeffTailRatio_of_integralCheck
    (physicalWeightNum k) (physicalWeightDen k)
    (physicalRetunedNum k) (physicalRetunedDen k)
    (blockNcut k)
    (physicalWeightDen_pos k) (physicalRetunedDen_pos k)
    (blockWeight k) (blockWeight_nonneg k) (blockWeight_le_one k)
    (blockWeight_eqv_closed k) (blockRetunedWeight_eqv_closed k) hcheck

theorem blockRetunedWeight_zero_eqv :
    p2RetunedWeight (blockWeight 0) ≈ Q'.mkPos 23 24 (by decide) := by
  unfold p2RetunedWeight renormWFix renormTauFix blockWeight blockMargin
    SpectralLocalizationCrux.q112 blockQuarter qpow
  decide

theorem blockRetunedWeight_one_eqv :
    p2RetunedWeight (blockWeight 1) ≈ Q'.mkPos 95 96 (by decide) := by
  unfold p2RetunedWeight renormWFix renormTauFix blockWeight blockMargin
    SpectralLocalizationCrux.q112 blockQuarter qpow
  decide

theorem blockRetunedWeight_two_eqv :
    p2RetunedWeight (blockWeight 2) ≈ Q'.mkPos 383 384 (by decide) := by
  unfold p2RetunedWeight renormWFix renormTauFix blockWeight blockMargin
    SpectralLocalizationCrux.q112 blockQuarter qpow
  decide

theorem blockRetunedWeight_three_eqv :
    p2RetunedWeight (blockWeight 3) ≈ Q'.mkPos 1535 1536 (by decide) := by
  unfold p2RetunedWeight renormWFix renormTauFix blockWeight blockMargin
    SpectralLocalizationCrux.q112 blockQuarter qpow
  decide

theorem blockIntegralTailCheck_zero :
    integralTailBlockCheck 11 12 23 24 4 1 7 = true := by decide

theorem blockIntegralTailCheck_one :
    integralTailBlockCheck 47 48 95 96 9 1 17 = true := by decide

theorem blockIntegralTailCheck_two :
    integralTailBlockCheck 191 192 383 384 19 1 37 = true := by decide

theorem blockIntegralTailCheck_three :
    integralTailBlockCheck 767 768 1535 1536 39 1 77 = true := by decide

def blockCoeffTail_zero :
    P2RetunedCoeffTailRatio (blockNcut 0) (blockWeight 0)
      (blockWeight_nonneg 0) (blockWeight_le_one 0) := by
  rw [show blockNcut 0 = 4 by decide]
  exact coeffTailRatio_of_integralCheck 11 12 23 24 4
    (by decide) (by decide) (blockWeight 0)
    (blockWeight_nonneg 0) (blockWeight_le_one 0)
    blockWeight_zero_eqv blockRetunedWeight_zero_eqv
    blockIntegralTailCheck_zero

def blockCoeffTail_one :
    P2RetunedCoeffTailRatio (blockNcut 1) (blockWeight 1)
      (blockWeight_nonneg 1) (blockWeight_le_one 1) := by
  rw [show blockNcut 1 = 9 by decide]
  exact coeffTailRatio_of_integralCheck 47 48 95 96 9
    (by decide) (by decide) (blockWeight 1)
    (blockWeight_nonneg 1) (blockWeight_le_one 1)
    blockWeight_one_eqv blockRetunedWeight_one_eqv
    blockIntegralTailCheck_one

def blockCoeffTail_two :
    P2RetunedCoeffTailRatio (blockNcut 2) (blockWeight 2)
      (blockWeight_nonneg 2) (blockWeight_le_one 2) := by
  rw [show blockNcut 2 = 19 by decide]
  exact coeffTailRatio_of_integralCheck 191 192 383 384 19
    (by decide) (by decide) (blockWeight 2)
    (blockWeight_nonneg 2) (blockWeight_le_one 2)
    blockWeight_two_eqv blockRetunedWeight_two_eqv
    blockIntegralTailCheck_two

def blockCoeffTail_three :
    P2RetunedCoeffTailRatio (blockNcut 3) (blockWeight 3)
      (blockWeight_nonneg 3) (blockWeight_le_one 3) := by
  rw [show blockNcut 3 = 39 by decide]
  exact coeffTailRatio_of_integralCheck 767 768 1535 1536 39
    (by decide) (by decide) (blockWeight 3)
    (blockWeight_nonneg 3) (blockWeight_le_one 3)
    blockWeight_three_eqv blockRetunedWeight_three_eqv
    blockIntegralTailCheck_three

/-- Honest coefficient frontier after discharging every supported adjacent
mode at physical scales zero, one, and two. -/
structure BlockCompatibleP2CoeffTailFromThree : Type where
  tail : forall k, 3 ≤ k →
    P2RetunedCoeffTailRatio (blockNcut k) (blockWeight k)
      (blockWeight_nonneg k) (blockWeight_le_one k)

def BlockCompatibleP2CoeffTailFromThree.toAllScale
    (T : BlockCompatibleP2CoeffTailFromThree) :
    BlockCompatibleP2CoeffTailData where
  coeffTailRatio := fun k => by
    by_cases h0 : k = 0
    · subst k
      exact blockCoeffTail_zero
    by_cases h1 : k = 1
    · subst k
      exact blockCoeffTail_one
    by_cases h2 : k = 2
    · subst k
      exact blockCoeffTail_two
    exact T.tail k (by omega)

/-- After one further complete-support certificate, the exact coefficient
frontier begins only at physical scale four. -/
structure BlockCompatibleP2CoeffTailFromFour : Type where
  tail : forall k, 4 ≤ k →
    P2RetunedCoeffTailRatio (blockNcut k) (blockWeight k)
      (blockWeight_nonneg k) (blockWeight_le_one k)

/-- Pure-arithmetic form of the remaining physical coefficient frontier.
Unlike `BlockCompatibleP2CoeffTailFromFour`, this carrier contains no `Q'`
terms: its only field is the exact common-denominator `Nat` inequality at
every supported adjacent mode and every scale `k>=4`. -/
structure BlockCompatibleP2IntegralTailFromFour : Type where
  tail : forall k s, 4 ≤ k → 1 ≤ s → s < 2 * blockNcut k →
    physicalIntegralTailAt k s

/-- Compile the pure-`Nat` schedule theorem to the rational coefficient
carrier consumed by `CanonicalBulkControl`. -/
def BlockCompatibleP2IntegralTailFromFour.toCoeffTailFromFour
    (T : BlockCompatibleP2IntegralTailFromFour) :
    BlockCompatibleP2CoeffTailFromFour where
  tail := fun k hk =>
    { tail := fun s hs hsN =>
        physicalIntegralTailAt_sound k s (T.tail k s hk hs hsN) }

def BlockCompatibleP2CoeffTailFromFour.toFromThree
    (T : BlockCompatibleP2CoeffTailFromFour) :
    BlockCompatibleP2CoeffTailFromThree where
  tail := fun k hk => by
    by_cases h3 : k = 3
    · subst k
      exact blockCoeffTail_three
    exact T.tail k (by omega)

def BlockCompatibleP2CoeffTailFromFour.toAllScale
    (T : BlockCompatibleP2CoeffTailFromFour) :
    BlockCompatibleP2CoeffTailData :=
  T.toFromThree.toAllScale

#print axioms integralTailAt_sound
#print axioms integralTailBlockCheck_sound
#print axioms blockIntegralTailCheck_zero
#print axioms blockIntegralTailCheck_one
#print axioms blockIntegralTailCheck_two
#print axioms blockIntegralTailCheck_three
#print axioms blockCoeffTail_zero
#print axioms blockCoeffTail_one
#print axioms blockCoeffTail_two
#print axioms blockCoeffTail_three
#print axioms physicalIntegralTailAt_sound
#print axioms blockCoeffTail_of_physicalIntegralTailCheck
#print axioms BlockCompatibleP2IntegralTailFromFour.toCoeffTailFromFour
#print axioms BlockCompatibleP2CoeffTailFromThree.toAllScale
#print axioms BlockCompatibleP2CoeffTailFromFour.toAllScale

end YMGap.Continuum.P2BlockCompatibleIntegralTailCertificate
