/-
# Explicit all-nome tails of the original polynomial heat characters

For each rational `0 < w < 1` and each actual polynomial `p`, the supplied
cutoff pays for its computed coefficient growth radius R(p). Above that
cutoff, the exact heat-character coefficient-L1 majorant contracts by at
most one half. Both the starting label and the tail head depend on w and p.

Finite sums of coefficient norms have an explicit closed tail and a
Type-level tolerance cutoff. This is representation-cutoff control, NOT a
beta-uniform spectral estimate. The moving-anchor slab/GNS product estimate,
physical stationary vacuum and continuum passage remain open.
-/

import YMGap.Continuum.SU2HeatCharacterPolynomialMajorant
import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion

namespace YMGap.Continuum.SU2HeatCharacterPolynomialTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HeatCharacterPolynomialMajorant
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion (qpow_eqv_pow)

local infix:50 " ≈ " => Q'.eqv

private theorem right_swap (a b c : Q') : (a * b) * c ≈ (a * c) * b :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b c)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (Q'.mul_comm_eqv b c))
      (Q'.eqv_symm (Q'.mul_assoc_eqv a c b)))

private theorem middle_swap (a b c d : Q') : (a * b) * (c * d) ≈ (a * c) * (b * d) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv c d))
    (mul_four_swap a b d c)

private theorem twice_radius_pos (p : RatPoly) : (0 : Q') < 2 * characterRadius p :=
  HKPos.q_mul_pos (by decide) (lt_of_lt_of_le (by decide : (0 : Q') < 1) (one_le_characterRadius p))

/-- The required Casimir gain: half divided by the actual doubled radius. -/
def polynomialGainTarget (p : RatPoly) : Q' := HKConv.divPos HalfPow.half (2 * characterRadius p)

/-- Computed starting label; depends on BOTH heat nome and polynomial. -/
def polynomialLabelCutoff (w : Q') (p : RatPoly) : Nat := powBaseCutoff w (polynomialGainTarget p)

theorem polynomialGainTarget_pos (p : RatPoly) : (0 : Q') < polynomialGainTarget p :=
  HKConv.divPos_pos (by decide)

theorem polynomialLabelCutoff_gain {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (p : RatPoly) :
    qpow w (2 * polynomialLabelCutoff w p + 3) ≤ polynomialGainTarget p :=
  Q'.le_trans' _ _ _ (qpow_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) _ _ (by omega))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (qpow_eqv_pow w (polynomialLabelCutoff w p)))
      (pow_base_le_cutoff hw0 hw1 (polynomialGainTarget_pos p)))

theorem polynomialTailRatio_le_half {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (p : RatPoly) :
    (2 * qpow w (2 * polynomialLabelCutoff w p + 3)) * characterRadius p ≤ HalfPow.half :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (right_swap _ _ _))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (polynomialLabelCutoff_gain hw0 hw1 p)
        (Q'.le_of_lt (twice_radius_pos p)))
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
        (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (twice_radius_pos p))))))

theorem heatCharacterMajorant_ratio {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (p : RatPoly) (N s : Nat) (hNs : N ≤ s) :
    heatCharacterMajorant w p (s + 1) ≤
      ((2 * qpow w (2 * N + 3)) * characterRadius p) * heatCharacterMajorant w p s := by
  have hc : coeffW w (s + 1) ≤ (2 * qpow w (2 * N + 3)) * coeffW w s := by
    simpa only [tailTerm, Nat.pow_one, coeffW, dimQ] using (tailTerm_ratio_gen hw0 hw1 1 N s hNs)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hc (Q'.pow_nonneg _ (characterRadius_nonnegative p) (s + 1)))
    (Q'.le_of_eqv (middle_swap _ _ _ _))

theorem shiftedMajorant_half_step {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (p : RatPoly) (k : Nat) :
    heatCharacterMajorant w p (polynomialLabelCutoff w p + (k + 1)) ≤
      HalfPow.half * heatCharacterMajorant w p (polynomialLabelCutoff w p + k) := by
  rw [← Nat.add_assoc]
  exact Q'.le_trans' _ _ _
    (heatCharacterMajorant_ratio (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) p _ _ (by omega))
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (polynomialTailRatio_le_half hw0 hw1 p)
      (heatCharacterMajorant_nonnegative (Q'.le_of_lt hw0) p _))

def polynomialTailHead (w : Q') (p : RatPoly) : Q' :=
  heatCharacterMajorant w p (polynomialLabelCutoff w p)

theorem shiftedMajorant_geometric {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (p : RatPoly) (k : Nat) :
    heatCharacterMajorant w p (polynomialLabelCutoff w p + k) ≤ polynomialTailHead w p * HalfPow.half ^ k :=
  CharacterTail.geom_dom _ _ _ HalfPow.half_nonneg (Q'.le_refl' _)
    (shiftedMajorant_half_step hw0 hw1 p) k

def polynomialClosedTail (w : Q') (p : RatPoly) (M : Nat) : Q' :=
  geoTailBase (polynomialTailHead w p) HalfPow.half M

/-- Finite blocks of the ORIGINAL polynomial coefficient norms, not scalar evaluations. -/
theorem heatCharacter_coefficientL1_block {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (p : RatPoly) (M L : Nat) :
    finSum (fun i => polynomialCoefficientL1
      (polySmul (coeffW w (polynomialLabelCutoff w p + (M + i)))
        (characterPolynomial p (polynomialLabelCutoff w p + (M + i))))) L ≤
      polynomialClosedTail w p M :=
  Q'.le_trans' _ _ _
    (ExpNeg.finSum_le_finSum_of_termwise _ _ (fun i => Q'.le_trans' _ _ _
      (heatCharacter_coefficientL1 (Q'.le_of_lt hw0) p _) (shiftedMajorant_geometric hw0 hw1 p (M + i))) L)
    (geoTailBase_series_le (heatCharacterMajorant_nonnegative (Q'.le_of_lt hw0) p _) (by decide) (by decide) M L)

def polynomialTailScale (w : Q') (p : RatPoly) : Q' :=
  polynomialTailHead w p * HKConv.divPos 1 (1 + (-HalfPow.half))

/-- Type-level tolerance cutoff for the closed tail, beyond its starting label. -/
def polynomialTailModulus (w : Q') (p : RatPoly) (ε : Q') : Nat :=
  powBaseCutoff HalfPow.half (HKConv.divPos ε (polynomialTailScale w p + 1))

theorem polynomialClosedTail_small {w : Q'} (hw0 : (0 : Q') < w) (p : RatPoly)
    (ε : Q') (hε : (0 : Q') < ε) (M : Nat) (hM : polynomialTailModulus w p ε ≤ M) :
    polynomialClosedTail w p M ≤ ε := by
  have hscale : (0 : Q') ≤ polynomialTailScale w p := Q'.mul_nonneg _ _
    (heatCharacterMajorant_nonnegative (Q'.le_of_lt hw0) p _) (HKConv.divPos_nonneg Q'.zero_le_one)
  have hpos : (0 : Q') < polynomialTailScale w p + 1 :=
    lt_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ hscale)
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  have hd : (0 : Q') < HKConv.divPos ε (polynomialTailScale w p + 1) :=
    HKConv.divPos_pos (CReal.num_pos_of_pos hε)
  have hp := Q'.le_trans' _ _ _ (pow_base_antitone (by decide) (by decide) hM)
    (pow_base_le_cutoff (by decide) (by decide) hd)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (right_swap _ _ _))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hp hscale)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one) (Q'.le_of_lt hd))
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
          (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hpos))))))

end YMGap.Continuum.SU2HeatCharacterPolynomialTail

#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialTail.polynomialGainTarget
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialTail.polynomialLabelCutoff
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialTail.polynomialGainTarget_pos
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialTail.polynomialLabelCutoff_gain
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialTail.polynomialTailRatio_le_half
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialTail.heatCharacterMajorant_ratio
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialTail.shiftedMajorant_half_step
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialTail.polynomialTailHead
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialTail.shiftedMajorant_geometric
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialTail.polynomialClosedTail
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialTail.heatCharacter_coefficientL1_block
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialTail.polynomialTailScale
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialTail.polynomialTailModulus
#print axioms YMGap.Continuum.SU2HeatCharacterPolynomialTail.polynomialClosedTail_small
