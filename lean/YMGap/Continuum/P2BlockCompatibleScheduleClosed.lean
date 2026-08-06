/-
Track 11.7-fusion / R3f -- closed rational coordinates for the physical
block-compatible schedule.

The finite coefficient compiler should not carry a separate rational witness
at every scale.  This module proves once and for all that, with

    D_k = 12 * 4^k,

the physical heat weight and its canonical two-fold retune are exactly

    w_k = (D_k - 1) / D_k,
    q_k = (2 * D_k - 1) / (2 * D_k).

The proofs use semantic equality of the constructive rationals and ordinary
natural-number arithmetic.  No normalization, division algorithm, classical
choice, or large closed computation is involved.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleSchedule

namespace YMGap.Continuum.P2BlockCompatibleScheduleClosed

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2RetunedFenceIntegralCertificate
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.P2VacNormIntegralCertificate
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SpectralLocalizationCrux

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

/-- Common denominator of the physical heat weight at scale `k`. -/
def physicalWeightDen (k : Nat) : Nat := 12 * 4 ^ k

/-- Numerator of the physical heat weight at scale `k`. -/
def physicalWeightNum (k : Nat) : Nat := physicalWeightDen k - 1

/-- Common denominator of the two-fold retuned weight at scale `k`. -/
def physicalRetunedDen (k : Nat) : Nat := 2 * physicalWeightDen k

/-- Numerator of the two-fold retuned weight at scale `k`. -/
def physicalRetunedNum (k : Nat) : Nat := physicalRetunedDen k - 1

theorem physicalWeightDen_pos (k : Nat) : 0 < physicalWeightDen k := by
  unfold physicalWeightDen
  exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))

theorem physicalRetunedDen_pos (k : Nat) : 0 < physicalRetunedDen k := by
  unfold physicalRetunedDen
  exact Nat.mul_pos (by decide) (physicalWeightDen_pos k)

/-- Subtracting a positive unit fraction from one produces the predecessor
numerator over the same denominator. -/
private theorem one_sub_unit_fraction_eqv (D : Nat) (hD : 0 < D) :
    ((1 : Q') - Q'.mkPos 1 D hD) ≈
      Q'.mkPos ((D - 1 : Nat) : Int) D hD := by
  change ((1 : Q') + (-Q'.mkPos 1 D hD)) ≈
    Q'.mkPos ((D - 1 : Nat) : Int) D hD
  show
    ((1 : Q') + (-Q'.mkPos 1 D hD)).num *
        ((Q'.mkPos ((D - 1 : Nat) : Int) D hD).den : Int) =
      (Q'.mkPos ((D - 1 : Nat) : Int) D hD).num *
        (((1 : Q') + (-Q'.mkPos 1 D hD)).den : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mkPos_num,
    Q'.mkPos_den, Q'.neg_den, neg_num]
  change ((1 : Int) * (D : Int) + (-1 : Int) * (1 : Int)) * (D : Int) =
    ((D - 1 : Nat) : Int) * ((1 : Int) * (D : Int))
  have hpred : ((D - 1 : Nat) : Int) = (D : Int) - 1 := by
    omega
  rw [hpred]
  simp [Int.sub_eq_add_neg]

/-- The geometric heat-time margin has denominator `12*4^k`. -/
theorem blockMargin_eqv_closed (k : Nat) :
    blockMargin k ≈
      Q'.mkPos 1 (physicalWeightDen k) (physicalWeightDen_pos k) := by
  have hquarter : qpow blockQuarter k ≈
      Q'.mkPos 1 (4 ^ k) (Nat.pow_pos (by decide)) := by
    simpa only [blockQuarter, Nat.one_pow] using
      qpow_mkPosNat_eqv 1 4 (by decide) k
  unfold blockMargin
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left q112 _ _ hquarter) ?_
  simpa only [q112, physicalWeightDen, Int.one_mul] using
    mkPos_mul_mkPos 1 1 12 (4 ^ k) (by decide)
      (Nat.pow_pos (by decide))

/-- Closed rational coordinate of the physical heat weight. -/
theorem blockWeight_eqv_closed (k : Nat) :
    blockWeight k ≈
      Q'.mkPos (physicalWeightNum k) (physicalWeightDen k)
        (physicalWeightDen_pos k) := by
  unfold blockWeight
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (1 : Q') _ _
      (Q'.neg_eqv_congr _ _ (blockMargin_eqv_closed k))) ?_
  exact one_sub_unit_fraction_eqv
    (physicalWeightDen k) (physicalWeightDen_pos k)

/-- Closed rational coordinate of the canonical two-fold retuned weight. -/
theorem blockRetunedWeight_eqv_closed (k : Nat) :
    p2RetunedWeight (blockWeight k) ≈
      Q'.mkPos (physicalRetunedNum k) (physicalRetunedDen k)
        (physicalRetunedDen_pos k) := by
  have hmarginHalf :
      ((1 : Q') - blockWeight k) * Q'.mkPos 1 2 (by decide) ≈
        Q'.mkPos 1 (physicalRetunedDen k) (physicalRetunedDen_pos k) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (Q'.mkPos 1 2 (by decide))
        (one_sub_blockWeight_eqv_margin k)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (Q'.mkPos 1 2 (by decide))
        (blockMargin_eqv_closed k)) ?_
    simpa only [physicalRetunedDen, Int.one_mul, Nat.mul_comm] using
      mkPos_mul_mkPos 1 1 (physicalWeightDen k) 2
        (physicalWeightDen_pos k) (by decide)
  unfold p2RetunedWeight renormWFix renormTauFix
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (1 : Q') _ _
      (Q'.neg_eqv_congr _ _ hmarginHalf)) ?_
  exact one_sub_unit_fraction_eqv
    (physicalRetunedDen k) (physicalRetunedDen_pos k)

#print axioms blockMargin_eqv_closed
#print axioms blockWeight_eqv_closed
#print axioms blockRetunedWeight_eqv_closed

end YMGap.Continuum.P2BlockCompatibleScheduleClosed
