/-
# The current arbitrary-nome cutoff modulus misses every AF terminal cutoff

The arbitrary-nome corrected-slab tail is valid once the cutoff exceeds its
executable retained stage.  On the AF schedule, however, the current retained
stage is built from raw, deliberately unreduced `Q'` denominators.  Its
head-burn offset is already strictly larger than the prescribed terminal
cutoff `4^(depth+1)` at every outer depth.

Thus the new fixed-nome tail theorem cannot be applied directly on the actual
AF terminal diagonal.  This is an obstruction to the present modulus, not to
the existence of a sharper cutoff estimate and not a non-Cauchy theorem for
the terminal laws.

Constructive contract: exact `Nat`, `Int`, and raw-rational representation
arithmetic only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffNomeTail
import YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalGuardSeparation

namespace
  YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalNomeModulusObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffNomeTail
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalCarrier
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance
open YMGap.Continuum.SU2PhysicalOuterCutoffTensorTail

/-! ## 1. Raw denominator formulas -/

private theorem one_sub_den (w : Q') :
    ((1 : Q') + (-w)).den = w.den := by
  apply Int.ofNat_inj.mp
  rw [Q'.add_den_cast, Q'.neg_den]
  change (1 : Int) * (w.den : Int) = (w.den : Int)
  omega

private theorem mul_den_nat (left right : Q') :
    (left * right).den = left.den * right.den := by
  apply Int.ofNat_inj.mp
  rw [Q'.mul_den_cast]
  exact Int.natCast_mul left.den right.den

private theorem rgQpow_den (w : Q') :
    ∀ exponent : Nat,
      (qpow w exponent).den = w.den ^ exponent
  | 0 => rfl
  | exponent + 1 => by
      rw [qpow, mul_den_nat, rgQpow_den w exponent,
        Nat.pow_succ]

private theorem tailTerm_den
    (w : Q') (degree spin : Nat) :
    (tailTerm w degree spin).den =
      w.den ^ c4 spin := by
  unfold tailTerm
  rw [mul_den_nat, rgQpow_den]
  have hofNatDen :
      (Q'.ofNat ((spin + 1) ^ degree)).den = 1 := rfl
  rw [hofNatDen, Nat.one_mul]

theorem physicalNomeRawPowerCutoff_eq_den_mul_target
    (w : Q') :
    physicalNomeRawPowerCutoff w =
      w.den * (2 ^ (physicalFacePolynomialDegree + 1)) := by
  unfold physicalNomeRawPowerCutoff powBaseCutoff
  rw [HKConv.divPos_num]
  have honeNum : (1 : Q').num = 1 := rfl
  rw [honeNum, Int.one_mul]
  change Int.toNat
    (((1 + -w) * physicalDegreeRatioPowerTarget).den : Int) =
      w.den * (2 ^ (physicalFacePolynomialDegree + 1))
  have hden :
      (((1 + -w) * physicalDegreeRatioPowerTarget).den : Int) =
        ((w.den *
          (2 ^ (physicalFacePolynomialDegree + 1)) : Nat) : Int) := by
    rw [Q'.mul_den_cast, one_sub_den]
    unfold physicalDegreeRatioPowerTarget
    rw [Q'.mkPos_den]
    exact Int.natCast_mul w.den
      (2 ^ (physicalFacePolynomialDegree + 1))
  rw [hden]
  apply Int.ofNat_inj.mp
  exact Int.toNat_of_nonneg (Int.natCast_nonneg _)

theorem afNomeSchedule_nome_den (stage : Nat) :
    (afNomeSchedule.nome stage).den =
      1000 * afE stage := by
  unfold afNomeSchedule
  change ((1 : Q') + (-afGap stage)).den =
    1000 * afE stage
  rw [one_sub_den, afGap_den]

/-! ## 2. The denominator-driven head offset -/

private theorem physicalNomeHeadCoefficient_num_ge_powerDen
    {w : Q'} (hw0 : (0 : Q') < w) :
    ((w.den ^
        c4 (physicalNomeRatioStart w) : Nat) : Int) ≤
      (physicalNomeHeadCoefficient w).num := by
  have hheadNonnegative :
      (0 : Int) ≤ (physicalNomeRatioHead w).num :=
    (Q'.zero_le_iff_num_nonneg
      (physicalNomeRatioHead w)).mp
      (by
        unfold physicalNomeRatioHead
        exact tailTerm_nonneg
          (Q'.le_of_lt hw0)
          physicalFacePolynomialDegree
          (physicalNomeRatioStart w))
  have hheadDen :
      ((physicalNomeRatioHead w).den : Int) =
        ((w.den ^
          c4 (physicalNomeRatioStart w) : Nat) : Int) := by
    exact_mod_cast
      tailTerm_den w physicalFacePolynomialDegree
        (physicalNomeRatioStart w)
  have hcoefficient :
      (physicalNomeHeadCoefficient w).num =
        ((physicalNomeRatioHead w).den : Int) +
          (physicalNomeRatioHead w).num := by
    unfold physicalNomeHeadCoefficient
    change
      (1 : Int) * ((physicalNomeRatioHead w).den : Int) +
          (physicalNomeRatioHead w).num * 1 =
        ((physicalNomeRatioHead w).den : Int) +
          (physicalNomeRatioHead w).num
    omega
  rw [hcoefficient, hheadDen]
  omega

theorem physicalNomeHeadOffset_ge_two_powerDen
    {w : Q'} (hw0 : (0 : Q') < w) :
    2 * w.den ^ c4 (physicalNomeRatioStart w) ≤
      physicalNomeHeadOffset w := by
  have hcoefficientPos :
      (0 : Q') < physicalNomeHeadCoefficient w :=
    physicalNomeHeadCoefficient_pos hw0
  have hcoefficientNum :
      (0 : Int) < (physicalNomeHeadCoefficient w).num :=
    CReal.num_pos_of_pos hcoefficientPos
  have hoffset :
      ((physicalNomeHeadOffset w : Nat) : Int) =
        2 * (physicalNomeHeadCoefficient w).num := by
    unfold physicalNomeHeadOffset
      physicalNomeHeadScaledTolerance
    rw [HKConv.divPos_den_cast hcoefficientNum]
    rfl
  have hpower :=
    physicalNomeHeadCoefficient_num_ge_powerDen hw0
  have hscaled :
      (2 : Int) *
          ((w.den ^ c4 (physicalNomeRatioStart w) : Nat) : Int) ≤
        2 * (physicalNomeHeadCoefficient w).num :=
    Int.mul_le_mul_of_nonneg_left hpower (by decide)
  rw [← hoffset] at hscaled
  exact_mod_cast hscaled

/-! ## 3. Every prescribed AF terminal cutoff is too early -/

private theorem afTerminalRatioStart_ge_depth (depth : Nat) :
    depth + 1 ≤
      physicalNomeRatioStart
        (afNomeSchedule.nome (depth + 1)) := by
  rw [physicalNomeRatioStart,
    physicalNomeRawPowerCutoff_eq_den_mul_target,
    afNomeSchedule_nome_den]
  unfold afE physicalFacePolynomialDegree
  omega

theorem afTerminalCutoff_lt_physicalNomeHeadOffset
    (depth : Nat) :
    (afTerminalData depth).cutoff <
      physicalNomeHeadOffset
        (afNomeSchedule.nome (depth + 1)) := by
  let w := afNomeSchedule.nome (depth + 1)
  let spin := physicalNomeRatioStart w
  have hw0 : (0 : Q') < w :=
    afNomeSchedule.nome_pos (depth + 1)
  have hbase : 4 ≤ w.den := by
    dsimp only [w]
    rw [afNomeSchedule_nome_den]
    unfold afE
    omega
  have hspin : depth + 1 ≤ spin := by
    dsimp only [spin, w]
    exact afTerminalRatioStart_ge_depth depth
  have hspinExponent : spin ≤ c4 spin := by
    unfold c4
    simpa using
      Nat.mul_le_mul_left spin
        (show 1 ≤ spin + 2 by omega)
  have hdepthExponent : depth + 1 ≤ c4 spin :=
    Nat.le_trans hspin hspinExponent
  have hbasePower :
      4 ^ (depth + 1) ≤ w.den ^ (depth + 1) :=
    Nat.pow_le_pow_left hbase (depth + 1)
  have hexponentPower :
      w.den ^ (depth + 1) ≤ w.den ^ c4 spin :=
    Nat.pow_le_pow_right
      (Nat.zero_lt_of_lt hbase)
      hdepthExponent
  have hpower :
      4 ^ (depth + 1) ≤ w.den ^ c4 spin :=
    Nat.le_trans hbasePower hexponentPower
  have hpowerPos : 0 < w.den ^ c4 spin :=
    Nat.pow_pos (Q'.den_pos w)
  have hstrict :
      4 ^ (depth + 1) <
        2 * w.den ^ c4 spin := by
    omega
  have hoffset :
      2 * w.den ^ c4 spin ≤
        physicalNomeHeadOffset w := by
    dsimp only [spin]
    exact physicalNomeHeadOffset_ge_two_powerDen hw0
  rw [afTerminalData_cutoff]
  exact Nat.lt_of_lt_of_le hstrict hoffset

theorem afTerminalCutoff_lt_slabNomeModulus
    (depth : Nat) (ε : Q') :
    (afTerminalData depth).cutoff <
      slabNomeCutoffEventProbabilityModulus
        (afTerminalData depth).coupling 1 ε := by
  have hhead :=
    afTerminalCutoff_lt_physicalNomeHeadOffset depth
  rw [afTerminalData_coupling]
  refine Nat.lt_of_lt_of_le hhead ?_
  unfold slabNomeCutoffEventProbabilityModulus
    physicalNomeTensorToleranceRetainedCutoff
    physicalNomeRetainedCutoff
    physicalNomeBaseCutoff
  have hratio :=
    physicalNomeRatioStart_pos
      (afNomeSchedule.nome (depth + 1))
  omega

theorem afTerminalCutoff_not_past_slabNomeModulus
    (depth : Nat) (ε : Q') :
    ¬ (slabNomeCutoffEventProbabilityModulus
        (afTerminalData depth).coupling 1 ε ≤
      (afTerminalData depth).cutoff) := by
  exact Nat.not_le_of_lt
    (afTerminalCutoff_lt_slabNomeModulus depth ε)

/-! ## Axiom audit -/

#print axioms physicalNomeRawPowerCutoff_eq_den_mul_target
#print axioms afNomeSchedule_nome_den
#print axioms physicalNomeHeadOffset_ge_two_powerDen
#print axioms afTerminalCutoff_lt_physicalNomeHeadOffset
#print axioms afTerminalCutoff_lt_slabNomeModulus
#print axioms afTerminalCutoff_not_past_slabNomeModulus

end
  YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalNomeModulusObstruction
