/-
# An explicit degree-thirteen face envelope at every subunit heat nome

The fixed `1/400` BF4 carrier estimate uses the degree-thirteen Casimir
sequence

  `(spin + 1)^13 * w^(spin * (spin + 2))`.

Its summability is not special to that anchor.  For every rational
`0 < w < 1`, the general-base power modulus supplies an explicit spin at
which the existing Casimir ratio is at most one half.  The complete finite
prefix plus twice the first tail term is therefore a cutoff-independent
one-face ceiling.

This file performs only that one-dimensional analytic compilation.  It does
not assert a uniform ceiling as `w -> 1`; the returned rational ceiling is
allowed to depend on the literal nome.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Constructive.FinSumGeom
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.Z4SpinSummedFaceActivityBound

namespace YMGap.Continuum.Z4SpinSummedFaceActivityParametricEnvelope

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4SpinSummedFaceActivityBound

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The literal parametric one-face sequence -/

def fixedNomeDecoratedFaceActivity (w : Q') (spin : Nat) : Q' :=
  tailTerm w 13 spin

def fixedNomeDecoratedPlaqActivity (w : Q') (cutoff : Nat) : Q' :=
  finSum (fun offset => fixedNomeDecoratedFaceActivity w (1 + offset)) cutoff

def fixedNomeDecoratedTailRatio (w : Q') (offsetStart : Nat) : Q' :=
  Q'.ofNat 8192 * qpow w (2 * (1 + offsetStart) + 3)

def fixedNomeDecoratedFaceCeiling (w : Q') (offsetStart : Nat) : Q' :=
  fixedNomeDecoratedPlaqActivity w offsetStart +
    (fixedNomeDecoratedFaceActivity w (1 + offsetStart) +
      fixedNomeDecoratedFaceActivity w (1 + offsetStart))

theorem fixedNomeDecoratedFaceActivity_nonnegative
    {w : Q'} (hw0 : (0 : Q') <= w) (spin : Nat) :
    (0 : Q') <= fixedNomeDecoratedFaceActivity w spin :=
  tailTerm_nonneg hw0 13 spin

theorem fixedNomeDecoratedPlaqActivity_nonnegative
    {w : Q'} (hw0 : (0 : Q') <= w) (cutoff : Nat) :
    (0 : Q') <= fixedNomeDecoratedPlaqActivity w cutoff := by
  unfold fixedNomeDecoratedPlaqActivity
  induction cutoff with
  | zero => exact Q'.le_refl' 0
  | succ cutoff ih =>
      rw [finSum_succ]
      exact Q'.zero_le_add _ _ ih
        (fixedNomeDecoratedFaceActivity_nonnegative hw0 (1 + cutoff))

theorem fixedNomeDecoratedFaceCeiling_nonnegative
    {w : Q'} (hw0 : (0 : Q') <= w) (offsetStart : Nat) :
    (0 : Q') <= fixedNomeDecoratedFaceCeiling w offsetStart := by
  unfold fixedNomeDecoratedFaceCeiling
  exact Q'.zero_le_add _ _
    (fixedNomeDecoratedPlaqActivity_nonnegative hw0 offsetStart)
    (Q'.zero_le_add _ _
      (fixedNomeDecoratedFaceActivity_nonnegative hw0 (1 + offsetStart))
      (fixedNomeDecoratedFaceActivity_nonnegative hw0 (1 + offsetStart)))

theorem fixedNomeDecoratedFaceActivity_zero_eqv_one (w : Q') :
    fixedNomeDecoratedFaceActivity w 0 ≈ 1 := by
  unfold fixedNomeDecoratedFaceActivity tailTerm
  dsimp [c4, qpow]
  exact Q'.mul_one_eqv 1

/-! ## 2. A supplied ratio cutoff bounds every representation cutoff -/

private theorem half_mul_double_eqv (x : Q') :
    HalfPow.half * (x + x) ≈ x := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv HalfPow.half x x) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_mul_eqv HalfPow.half HalfPow.half x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ x (by decide :
      HalfPow.half + HalfPow.half ≈ (1 : Q'))) ?_
  exact Q'.one_mul_eqv x

/-- Once the exact degree-thirteen ratio is at most one half, the finite
prefix plus twice the first tail term bounds every finite spin sum. -/
theorem fixedNomeDecoratedPlaqActivity_le_ceiling_of_ratio
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (offsetStart : Nat)
    (hratio : fixedNomeDecoratedTailRatio w offsetStart <= HalfPow.half) :
    forall cutoff,
      fixedNomeDecoratedPlaqActivity w cutoff <=
        fixedNomeDecoratedFaceCeiling w offsetStart := by
  let g : Nat -> Q' := fun offset =>
    fixedNomeDecoratedFaceActivity w (1 + offset)
  have hg : forall offset, (0 : Q') <= g offset := by
    intro offset
    exact fixedNomeDecoratedFaceActivity_nonnegative
      (Q'.le_of_lt hw0) (1 + offset)
  have hdom : forall k,
      g (offsetStart + (k + 1)) <=
        HalfPow.half * g (offsetStart + k) := by
    intro k
    have hindexLeft :
        1 + (offsetStart + (k + 1)) =
          (1 + (offsetStart + k)) + 1 := by omega
    have hbase : 1 + offsetStart <= 1 + (offsetStart + k) := by omega
    have hraw := tailTerm_ratio_gen
      (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
      13 (1 + offsetStart) (1 + (offsetStart + k)) hbase
    have hterm0 :
        (0 : Q') <= tailTerm w 13 (1 + (offsetStart + k)) :=
      tailTerm_nonneg (Q'.le_of_lt hw0) 13 _
    have hscaled :
        (Q'.ofNat 8192 *
            qpow w (2 * (1 + offsetStart) + 3)) *
            tailTerm w 13 (1 + (offsetStart + k)) <=
          HalfPow.half * tailTerm w 13 (1 + (offsetStart + k)) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _
        (by simpa [fixedNomeDecoratedTailRatio] using hratio) hterm0
    unfold g fixedNomeDecoratedFaceActivity
    rw [hindexLeft]
    exact Q'.le_trans' _ _ _ hraw hscaled
  have hhead0 : (0 : Q') <= g offsetStart := hg offsetStart
  have hH0 : (0 : Q') <= g offsetStart + g offsetStart :=
    Q'.zero_le_add _ _ hhead0 hhead0
  have hrec :
      g offsetStart +
          HalfPow.half * (g offsetStart + g offsetStart) <=
        g offsetStart + g offsetStart := by
    exact Q'.le_of_eqv
      (Q'.add_eqv_congr_left (g offsetStart) _ _
        (half_mul_double_eqv (g offsetStart)))
  have huniform := finSum_geom_uniform g offsetStart
    (g offsetStart) HalfPow.half
    (g offsetStart + g offsetStart)
    hg HalfPow.half_nonneg hH0 (Q'.le_refl' _)
    hdom hrec
  intro cutoff
  unfold fixedNomeDecoratedPlaqActivity fixedNomeDecoratedFaceCeiling
  exact huniform cutoff

/-! ## 3. The ratio cutoff is explicit for every positive subunit nome -/

/-- `2^-14`, the power target that absorbs the degree-thirteen factor
`2^13` and leaves ratio `1/2`. -/
def decoratedFacePowerTarget : Q' :=
  Q'.mkPos 1 16384 (by decide)

/-- The number of positive-spin terms retained before the geometric tail.
It is computed from the existing general-base rational power modulus. -/
def explicitDecoratedFaceOffsetCutoff (w : Q') : Nat :=
  HKConvGen.powBaseCutoff w decoratedFacePowerTarget

private theorem qpow_eqv_pow (w : Q') : forall exponent,
    qpow w exponent ≈ w ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      have ih := qpow_eqv_pow w exponent
      show qpow w exponent * w ≈ w * w ^ exponent
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ w ih)
        (Q'.mul_comm_eqv (w ^ exponent) w)

theorem explicitDecoratedFaceTailRatio_le_half
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    fixedNomeDecoratedTailRatio w
        (explicitDecoratedFaceOffsetCutoff w) <= HalfPow.half := by
  let n0 := HKConvGen.powBaseCutoff w decoratedFacePowerTarget
  have htarget : w ^ n0 <= decoratedFacePowerTarget := by
    exact HKConvGen.pow_base_le_cutoff hw0 hw1 (by
      unfold decoratedFacePowerTarget
      decide)
  have hexponent :
      n0 <= 2 * (1 + explicitDecoratedFaceOffsetCutoff w) + 3 := by
    unfold explicitDecoratedFaceOffsetCutoff
    dsimp [n0]
    omega
  have hqtarget : qpow w n0 <= decoratedFacePowerTarget :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (qpow_eqv_pow w n0)) htarget
  have hpower :
      qpow w (2 * (1 + explicitDecoratedFaceOffsetCutoff w) + 3) <=
        qpow w n0 :=
    qpow_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
      n0 (2 * (1 + explicitDecoratedFaceOffsetCutoff w) + 3) hexponent
  have hscaled :
      Q'.ofNat 8192 *
          qpow w (2 * (1 + explicitDecoratedFaceOffsetCutoff w) + 3) <=
        Q'.ofNat 8192 * decoratedFacePowerTarget :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.le_trans' _ _ _ hpower hqtarget) (by decide)
  unfold fixedNomeDecoratedTailRatio
  exact Q'.le_trans'
    (Q'.ofNat 8192 *
      qpow w (2 * (1 + explicitDecoratedFaceOffsetCutoff w) + 3))
    (Q'.ofNat 8192 * decoratedFacePowerTarget)
    HalfPow.half hscaled (Q'.le_of_eqv (by decide))

def explicitFixedNomeDecoratedFaceCeiling (w : Q') : Q' :=
  fixedNomeDecoratedFaceCeiling w (explicitDecoratedFaceOffsetCutoff w)

theorem fixedNomeDecoratedPlaqActivity_le_explicitCeiling
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    forall cutoff,
      fixedNomeDecoratedPlaqActivity w cutoff <=
        explicitFixedNomeDecoratedFaceCeiling w :=
  fixedNomeDecoratedPlaqActivity_le_ceiling_of_ratio
    hw0 hw1 (explicitDecoratedFaceOffsetCutoff w)
    (explicitDecoratedFaceTailRatio_le_half hw0 hw1)

theorem explicitFixedNomeDecoratedFaceCeiling_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') <= explicitFixedNomeDecoratedFaceCeiling w :=
  fixedNomeDecoratedFaceCeiling_nonnegative
    (Q'.le_of_lt hw0) (explicitDecoratedFaceOffsetCutoff w)

/-! ## 4. Cartesian spin-vector factorization at the same nome -/

def fixedNomeSpinVectorWeight (w : Q') : List Nat -> Q'
  | [] => 1
  | spin :: rest =>
      fixedNomeDecoratedFaceActivity w spin *
        fixedNomeSpinVectorWeight w rest

theorem fixedNomeSpinVectorWeight_nonnegative
    {w : Q'} (hw0 : (0 : Q') <= w) : forall vector : List Nat,
    (0 : Q') <= fixedNomeSpinVectorWeight w vector
  | [] => Q'.zero_le_one
  | spin :: rest => Q'.mul_nonneg _ _
      (fixedNomeDecoratedFaceActivity_nonnegative hw0 spin)
      (fixedNomeSpinVectorWeight_nonnegative hw0 rest)

private theorem listQSum_range_eqv_finSum (value : Nat -> Q') :
    forall cutoff : Nat,
      listQSum value (List.range cutoff) ≈ finSum value cutoff
  | 0 => Q'.eqv_refl 0
  | cutoff + 1 => by
      rw [List.range_succ, finSum_succ]
      exact Q'.eqv_trans _ _ _
        (listQSum_append value (List.range cutoff) [cutoff])
        (Q'.add_eqv_congr'
          (listQSum_range_eqv_finSum value cutoff)
          (Q'.eqv_of_eq (Q'.add_zero' (value cutoff))))

theorem positiveSpinValues_fixedNome_weight_sum
    (w : Q') (cutoff : Nat) :
    listQSum (fixedNomeDecoratedFaceActivity w)
        (positiveSpinValues cutoff) ≈
      fixedNomeDecoratedPlaqActivity w cutoff := by
  unfold positiveSpinValues fixedNomeDecoratedPlaqActivity
  rw [listQSum_map]
  exact listQSum_range_eqv_finSum _ cutoff

end YMGap.Continuum.Z4SpinSummedFaceActivityParametricEnvelope

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedFaceActivityParametricEnvelope.fixedNomeDecoratedPlaqActivity_le_ceiling_of_ratio
#print axioms YMGap.Continuum.Z4SpinSummedFaceActivityParametricEnvelope.explicitDecoratedFaceTailRatio_le_half
#print axioms YMGap.Continuum.Z4SpinSummedFaceActivityParametricEnvelope.fixedNomeDecoratedPlaqActivity_le_explicitCeiling
#print axioms YMGap.Continuum.Z4SpinSummedFaceActivityParametricEnvelope.positiveSpinValues_fixedNome_weight_sum
