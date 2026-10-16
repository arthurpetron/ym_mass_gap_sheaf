/-
# Value-level 96-face cutoff tail on the AF terminal slab

The one-face AF terminal tail is exponentially small at the prescribed
cutoff `4^stage`, but the finite-Fubini consumer also needs to pay the other
95 face coordinates.  This module supplies that payment without returning to
raw rational numerators or denominators.

The retained one-face mass is bounded by `2^(28*stage+15)`: there are at most
`4^stage+1` retained labels, each degree-thirteen polynomial weight is bounded
by the corresponding endpoint power, and every heat factor is at most one.
A direct induction on the tensor outside-union recurrence spends one extra
dyadic bit per coordinate in addition to that ceiling.  For 96 ambient faces
the burn is `(28*stage+16)*96`, which is strictly contained in the available
`4^stage+15` one-face precision from stage nine onward.

The final theorem bounds the literal corrected-slab new-label mass at the
exact AF terminal cutoff, uniformly in every later cutoff, and transfers the
same rate to every normalized Boolean event at the same nome.  It does not
compare consecutive AF nomes or control the block-spin remainder sequence.

Constructive contract: exact finite `Nat`/`Q'` bounds only; no choice,
`Classical`, `native_decide`, `sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalValueTail
import YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffNomeTail
import YMGap.Continuum.BF4PhysicalAnchorPartitionCeiling
import YMGap.Continuum.HeatKernelGap

namespace
  YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalSlabTail

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy
open YMGap.Continuum.BF4PhysicalAnchorPartitionCeiling
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffNomeTail
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.ClusterCount
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalCarrier
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalValueTail
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.PartitionUpperBound
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2PhysicalOuterCutoffFiniteFubiniTail
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeInteractingTolerance
open YMGap.Continuum.SU2PhysicalOuterCutoffTensorTail
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution

local infix:50 " ≈ " => Q'.eqv

private theorem dyad_antitone {earlier later : Nat}
    (h : earlier ≤ later) :
    dyad later ≤ dyad earlier := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold dyad
  exact ExpNeg.pow_half_antitone earlier offset

private theorem range_nodup (count : Nat) :
    (List.range count).Nodup := by
  induction count with
  | zero => exact List.nodup_nil
  | succ count ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
          ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = count := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl count)

private theorem shuffle_three (left middle right : Q') :
    left * (middle * right) ≈
      middle * (right * left) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem ofNat_twoPow_pays_dyad
    (paid remaining : Nat) :
    Q'.ofNat (2 ^ paid) * dyad (paid + remaining) ≈
      dyad remaining := by
  unfold dyad
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      (Q'.ofNat (2 ^ paid)) _ _
      (Q'.pow_add_eqv HalfPow.half paid remaining)) ?_
  refine Q'.eqv_trans _ _ _
    (shuffle_three
      (Q'.ofNat (2 ^ paid))
      (HalfPow.half ^ paid)
      (HalfPow.half ^ remaining)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      (HalfPow.half ^ paid) _ _
      (Q'.mul_comm_eqv
        (HalfPow.half ^ remaining)
        (Q'.ofNat (2 ^ paid)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (HalfPow.half ^ paid)
        (Q'.ofNat (2 ^ paid))
        (HalfPow.half ^ remaining))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (HalfPow.half ^ remaining)
      (half_power_normalizes paid)) ?_
  exact Q'.one_mul_eqv _

private theorem two_dyad_succ_le (precision : Nat) :
    dyad (precision + 1) + dyad (precision + 1) ≤
      dyad precision := by
  simpa only [dyad, Q'.pow_succ] using
    (dyad_recurrence precision)

private theorem ofNat_pow_eqv (base : Nat) :
    ∀ exponent : Nat,
      Q'.ofNat base ^ exponent ≈
        Q'.ofNat (base ^ exponent)
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      have ih := ofNat_pow_eqv base exponent
      change
        Q'.ofNat base * Q'.ofNat base ^ exponent ≈
          Q'.ofNat (base ^ (exponent + 1))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat base) _ _ ih) ?_
      rw [Nat.pow_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv
          (Q'.ofNat base)
          (Q'.ofNat (base ^ exponent))) ?_
      exact Q'.eqv_symm
        (ClusterCount.ofNat_mul_eqv (base ^ exponent) base)

private theorem twoPow_power_eqv (burn dimension : Nat) :
    Q'.ofNat (2 ^ burn) ^ dimension ≈
      Q'.ofNat (2 ^ (burn * dimension)) := by
  refine Q'.eqv_trans _ _ _
    (ofNat_pow_eqv (2 ^ burn) dimension) ?_
  have hpower :
      (2 ^ burn) ^ dimension =
        2 ^ (burn * dimension) := by
    rw [Nat.pow_mul]
  rw [hpower]
  exact Q'.eqv_refl _

/-! ## 1. A dyadic ceiling for the retained one-face mass -/

private theorem finSum_le_constant
    (term : Nat → Q') (bound : Q') :
    ∀ length : Nat,
      (∀ index, index < length → term index ≤ bound) →
      finSum term length ≤ Q'.ofNat length * bound
  | 0, _ =>
      Q'.ge_of_eqv (Q'.zero_mul_eqv bound)
  | length + 1, hterm => by
      have hprefix := finSum_le_constant term bound length
        (fun index hindex => hterm index (Nat.lt_succ_of_lt hindex))
      have hlast := hterm length (Nat.lt_succ_self length)
      have hadd := Q'.add_le_add hprefix hlast
      have hsucc :
          Q'.ofNat (length + 1) ≈
            Q'.ofNat length + 1 :=
        Q'.ofNat_add_eqv length 1
      have hidentify :
          Q'.ofNat length * bound + bound ≈
            Q'.ofNat (length + 1) * bound := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_symm (Q'.one_mul_eqv bound))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.add_mul_eqv
              (Q'.ofNat length) 1 bound)) ?_
        exact Q'.mul_eqv_congr_right _ _ bound
          (Q'.eqv_symm hsucc)
      exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hidentify)

private theorem physicalTailTerm_le_endpointPower
    {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q'))
    {spin endpoint : Nat} (hspin : spin < endpoint) :
    tailTerm w physicalFacePolynomialDegree spin ≤
      Q'.ofNat (endpoint ^ 13) := by
  have hspinSucc : spin + 1 ≤ endpoint := by omega
  have hpolyNat : (spin + 1) ^ 13 ≤ endpoint ^ 13 :=
    Nat.pow_le_pow_left hspinSucc 13
  have hpoly :
      Q'.ofNat ((spin + 1) ^ 13) ≤
        Q'.ofNat (endpoint ^ 13) :=
    ClusterCount.ofNat_le_ofNat hpolyNat
  have hpower0 :
      (0 : Q') ≤ qpow w (c4 spin) :=
    qpow_nonneg w hw0 _
  have hpower1 : qpow w (c4 spin) ≤ (1 : Q') :=
    HeatKernelGap.qpow_le_one hw0 hw1 _
  unfold tailTerm physicalFacePolynomialDegree
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hpoly hpower0)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hpower1
        (zero_le_ofNat _))
      (Q'.le_of_eqv
        (Q'.mul_one_eqv (Q'.ofNat (endpoint ^ 13)))))

private theorem physicalPrefix_le_fourteenthPower
    {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (endpoint : Nat) :
    finSum (tailTerm w physicalFacePolynomialDegree) endpoint ≤
      Q'.ofNat (endpoint ^ 14) := by
  have hsum := finSum_le_constant
    (tailTerm w physicalFacePolynomialDegree)
    (Q'.ofNat (endpoint ^ 13)) endpoint
    (fun spin hspin =>
      physicalTailTerm_le_endpointPower hw0 hw1 hspin)
  have hproduct :
      Q'.ofNat endpoint * Q'.ofNat (endpoint ^ 13) ≤
        Q'.ofNat (endpoint ^ 14) := by
    have hpow : endpoint * endpoint ^ 13 = endpoint ^ 14 := by
      calc
        endpoint * endpoint ^ 13 =
            endpoint ^ 13 * endpoint := Nat.mul_comm _ _
        _ = endpoint ^ (13 + 1) := (Nat.pow_succ _ _).symm
        _ = endpoint ^ 14 := by rfl
    rw [← hpow]
    exact Q'.ge_of_eqv
      (ClusterCount.ofNat_mul_eqv endpoint (endpoint ^ 13))
  exact Q'.le_trans' _ _ _ hsum hproduct

private theorem terminalCeilingNaturalBound (stage : Nat) :
    (4 ^ stage + 1) ^ 14 + 1 ≤
      2 ^ (28 * stage + 15) := by
  let block := 4 ^ stage
  have hblockPositive : 0 < block := by
    dsimp only [block]
    exact Nat.pow_pos (by decide)
  have hendpoint : block + 1 ≤ 2 * block := by omega
  have hpower :
      (block + 1) ^ 14 ≤ (2 * block) ^ 14 :=
    Nat.pow_le_pow_left hendpoint 14
  have hblockTwo : block = 2 ^ (2 * stage) := by
    dsimp only [block]
    change (2 ^ 2) ^ stage = 2 ^ (2 * stage)
    rw [Nat.pow_mul]
  have hdyadic :
      (2 * block) ^ 14 = 2 ^ (28 * stage + 14) := by
    rw [hblockTwo, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_add]
    congr 1
    omega
  have hmain :
      (block + 1) ^ 14 ≤ 2 ^ (28 * stage + 14) := by
    exact Nat.le_trans hpower (Nat.le_of_eq hdyadic)
  have hdyadicPositive : 0 < 2 ^ (28 * stage + 14) :=
    Nat.pow_pos (by decide)
  calc
    (4 ^ stage + 1) ^ 14 + 1 =
        (block + 1) ^ 14 + 1 := by rfl
    _ ≤ 2 ^ (28 * stage + 14) + 1 :=
      Nat.add_le_add_right hmain 1
    _ ≤ 2 * 2 ^ (28 * stage + 14) := by omega
    _ = 2 ^ (28 * stage + 15) := by
      calc
        2 * 2 ^ (28 * stage + 14) =
            2 ^ (28 * stage + 14) * 2 := Nat.mul_comm _ _
        _ = 2 ^ ((28 * stage + 14) + 1) :=
          (Nat.pow_succ _ _).symm
        _ = 2 ^ (28 * stage + 15) := by congr 1 <;> omega

/-- Value-level ceiling for the complete retained one-face mass at the AF
terminal cutoff.  Its exponent is linear in the AF stage. -/
theorem afTerminalHeatCeiling_le_twoPow (stage : Nat) :
    su2PhysicalHeatCeiling
        (afNomeSchedule.nome stage) (4 ^ stage + 1) ≤
      Q'.ofNat (2 ^ (28 * stage + 15)) := by
  have hw0 : (0 : Q') ≤ afNomeSchedule.nome stage :=
    Q'.le_of_lt (afNomeSchedule.nome_pos stage)
  have hw1 : afNomeSchedule.nome stage ≤ (1 : Q') :=
    Q'.le_of_lt (afNomeSchedule.nome_lt_one stage)
  have hprefix :=
    physicalPrefix_le_fourteenthPower hw0 hw1 (4 ^ stage + 1)
  unfold su2PhysicalHeatCeiling
  have hadd := Q'.add_le_add hprefix (Q'.le_refl' (1 : Q'))
  have hidentify :
      Q'.ofNat ((4 ^ stage + 1) ^ 14) + 1 ≈
        Q'.ofNat ((4 ^ stage + 1) ^ 14 + 1) :=
    Q'.eqv_symm
      (Q'.ofNat_add_eqv ((4 ^ stage + 1) ^ 14) 1)
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hidentify)
      (ClusterCount.ofNat_le_ofNat
        (terminalCeilingNaturalBound stage)))

/-- Every finite one-face partial at the AF terminal nome is bounded by the
same stage-linear dyadic ceiling, uniformly in its later cutoff. -/
theorem afTerminalLabelPartial_le_twoPow
    {stage : Nat} (hstage : 9 ≤ stage) (later : Nat) :
    su2PhysicalLabelPartial
        (afNomeSchedule.nome stage) later ≤
      Q'.ofNat (2 ^ (28 * stage + 15)) := by
  have hhead :
      tailTerm (afNomeSchedule.nome stage)
          physicalFacePolynomialDegree (4 ^ stage + 1) ≤
        dyad 1 :=
    Q'.le_trans' _ _ _
      (afTerminalFirstOmittedHead_le hstage)
      (dyad_antitone
        (Nat.le_trans (by decide : 1 ≤ 16)
          (Nat.le_add_left 16 (4 ^ stage))))
  exact Q'.le_trans' _ _ _
    (su2PhysicalLabelPartial_le_heatCeiling
      (afNomeSchedule.nome_pos stage)
      (afNomeSchedule.nome_lt_one stage)
      (4 ^ stage + 1)
      (afTerminalRatioCondition hstage)
      hhead later)
    (afTerminalHeatCeiling_le_twoPow stage)

/-! ## 2. Paying a fixed-dimensional tensor union -/

private theorem tensorMass_le_twoPow
    {w : Q'} (hw0 : (0 : Q') < w)
    {K burn : Nat}
    (hpartial : su2PhysicalLabelPartial w K ≤
      Q'.ofNat (2 ^ burn)) :
    ∀ dimension : Nat,
      su2PhysicalTensorMass w K dimension ≤
        Q'.ofNat (2 ^ burn) ^ dimension
  | 0 => Q'.le_refl' 1
  | dimension + 1 => by
      have ih := tensorMass_le_twoPow hw0 hpartial dimension
      have hmass0 :=
        su2PhysicalTensorMass_nonnegative hw0 K dimension
      have hbound0 :
          (0 : Q') ≤ Q'.ofNat (2 ^ burn) :=
        zero_le_ofNat _
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hpartial hmass0)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ ih hbound0)

private theorem tensorOutside_le_dyad
    {w : Q'} (hw0 : (0 : Q') < w)
    {M K burn : Nat}
    (hpartial : su2PhysicalLabelPartial w K ≤
      Q'.ofNat (2 ^ burn)) :
    ∀ dimension target : Nat,
      su2PhysicalOuterShellMass w M K ≤
          dyad (target + (burn + 1) * dimension) →
      su2PhysicalTensorOutsideUnionMass w M K dimension ≤
        dyad target
  | 0, target, _ =>
      Q'.le_trans' _ _ _ (Q'.le_refl' 0)
        (dyad_nonneg target)
  | dimension + 1, target, hshell => by
      let bound := Q'.ofNat (2 ^ burn)
      let precision := target + (burn + 1) * (dimension + 1)
      have hprecision :
          precision =
            burn * dimension + (target + dimension + burn + 1) := by
        dsimp only [precision]
        rw [Nat.mul_succ, Nat.add_mul]
        simp only [Nat.one_mul]
        omega
      have hmass := tensorMass_le_twoPow hw0 hpartial dimension
      have hmass0 :=
        su2PhysicalTensorMass_nonnegative hw0 K dimension
      have hfirstRaw :
          su2PhysicalOuterShellMass w M K *
              su2PhysicalTensorMass w K dimension ≤
            dyad precision * bound ^ dimension :=
        Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hshell hmass0)
          (Q'.mul_le_mul_of_nonneg_left _ _ _ hmass
            (dyad_nonneg precision))
      have hfirstIdentify :
          dyad precision * bound ^ dimension ≈
            dyad (target + dimension + burn + 1) := by
        dsimp only [bound]
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (dyad precision) _ _
            (twoPow_power_eqv burn dimension)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_comm_eqv
            (dyad precision)
            (Q'.ofNat (2 ^ (burn * dimension)))) ?_
        rw [hprecision]
        exact ofNat_twoPow_pays_dyad
          (burn * dimension)
          (target + dimension + burn + 1)
      have hfirst :
          su2PhysicalOuterShellMass w M K *
              su2PhysicalTensorMass w K dimension ≤
            dyad (target + 1) :=
        Q'.le_trans' _ _ _ hfirstRaw
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfirstIdentify)
            (dyad_antitone (by omega)))
      have hrecursivePrecision :
          target + (burn + 1) * (dimension + 1) =
            (target + burn + 1) +
              (burn + 1) * dimension := by
        rw [Nat.mul_succ]
        omega
      have hshellRecursive :
          su2PhysicalOuterShellMass w M K ≤
            dyad ((target + burn + 1) +
              (burn + 1) * dimension) := by
        rw [← hrecursivePrecision]
        exact hshell
      have hrecursive :=
        tensorOutside_le_dyad hw0 hpartial
          dimension (target + burn + 1) hshellRecursive
      have houtside0 :=
        su2PhysicalTensorOutsideUnionMass_nonnegative
          hw0 M K dimension
      have hbound0 : (0 : Q') ≤ bound := by
        dsimp only [bound]
        exact zero_le_ofNat _
      have hsecondRaw :
          su2PhysicalLabelPartial w K *
              su2PhysicalTensorOutsideUnionMass
                w M K dimension ≤
            bound * dyad (target + burn + 1) :=
        Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hpartial houtside0)
          (Q'.mul_le_mul_of_nonneg_left _ _ _ hrecursive hbound0)
      have hsecondIdentify :
          bound * dyad (target + burn + 1) ≈
            dyad (target + 1) := by
        dsimp only [bound]
        rw [show target + burn + 1 = burn + (target + 1) by omega]
        exact ofNat_twoPow_pays_dyad burn (target + 1)
      have hsecond :
          su2PhysicalLabelPartial w K *
              su2PhysicalTensorOutsideUnionMass
                w M K dimension ≤
            dyad (target + 1) :=
        Q'.le_trans' _ _ _ hsecondRaw
          (Q'.le_of_eqv hsecondIdentify)
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add hfirst hsecond)
        (two_dyad_succ_le target)

/-! ## 3. The exact 96-face AF terminal slab tail -/

def afTerminalTensorBurn (stage : Nat) : Nat :=
  (28 * stage + 16) * 96

def afTerminalSlabTailPrecision (stage : Nat) : Nat :=
  4 ^ stage + 15 - afTerminalTensorBurn stage

private theorem terminalTensorBurnBudgetFromNine :
    ∀ offset : Nat,
      afTerminalTensorBurn (9 + offset) ≤
        4 ^ (9 + offset) + 15
  | 0 => by decide
  | offset + 1 => by
      have ih := terminalTensorBurnBudgetFromNine offset
      have hpower : 896 ≤ 4 ^ (9 + offset) := by
        exact Nat.le_trans (by decide : 896 ≤ 4 ^ 9)
          (Nat.pow_le_pow_right (by decide)
            (by omega : 9 ≤ 9 + offset))
      unfold afTerminalTensorBurn at ih ⊢
      rw [show 9 + (offset + 1) = (9 + offset) + 1 by omega,
        Nat.pow_succ]
      omega

theorem afTerminalTensorBurn_le
    {stage : Nat} (hstage : 9 ≤ stage) :
    afTerminalTensorBurn stage ≤ 4 ^ stage + 15 := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hstage
  exact terminalTensorBurnBudgetFromNine offset

theorem afTerminalSlabTailPrecision_add_burn
    {stage : Nat} (hstage : 9 ≤ stage) :
    afTerminalSlabTailPrecision stage +
        afTerminalTensorBurn stage =
      4 ^ stage + 15 := by
  unfold afTerminalSlabTailPrecision
  exact Nat.sub_add_cancel
    (afTerminalTensorBurn_le hstage)

/-- The literal corrected-slab new-label sector above the exact AF terminal
cutoff has an explicit vanishing dyadic bound, uniformly in every later
cutoff. -/
theorem afTerminalSlabCutoffIncrement_le
    {depth later : Nat} (hdepth : 8 ≤ depth)
    (hlater : (afTerminalData depth).cutoff ≤ later) :
    slabParametricKCutoffIncrement
        (afTerminalData depth).coupling
        (afTerminalData depth).cutoff
        later 1 ≤
      dyad (afTerminalSlabTailPrecision (depth + 1)) := by
  let stage := depth + 1
  let block := 4 ^ stage
  let burn := 28 * stage + 15
  let target := afTerminalSlabTailPrecision stage
  have hstage : 9 ≤ stage := by
    dsimp only [stage]
    omega
  have hw0 : (0 : Q') < afNomeSchedule.nome stage :=
    afNomeSchedule.nome_pos stage
  have hcutoff : block ≤ later := by
    dsimp only [block, stage]
    simpa only [afTerminalData_cutoff] using hlater
  have hpartial :
      su2PhysicalLabelPartial
          (afNomeSchedule.nome stage) later ≤
        Q'.ofNat (2 ^ burn) := by
    dsimp only [burn]
    exact afTerminalLabelPartial_le_twoPow hstage later
  have hprecision :
      target + (burn + 1) * 96 = block + 15 := by
    dsimp only [target, burn, block]
    rw [← afTerminalSlabTailPrecision_add_burn hstage]
    unfold afTerminalTensorBurn
    omega
  have hshell :
      su2PhysicalOuterShellMass
          (afNomeSchedule.nome stage) block later ≤
        dyad (target + (burn + 1) * 96) := by
    rw [hprecision]
    simpa only [stage, block,
      afTerminalData_coupling, afTerminalData_cutoff] using
      (afTerminalOneFaceOuterShellMass_le hdepth later)
  have htensor :
      su2PhysicalTensorOutsideUnionMass
          (afNomeSchedule.nome stage) block later 96 ≤
        dyad target :=
    tensorOutside_le_dyad hw0 hpartial 96 target hshell
  rw [afTerminalData_coupling, afTerminalData_cutoff]
  refine Q'.le_trans' _ _ _
    (slabParametricKCutoffIncrement_le_ambient
      (w := afNomeSchedule.nome stage)
      (Q'.le_of_lt hw0)) ?_
  refine Q'.le_trans' _ _ _
    (physicalCutoffIncrement_le_outsideFaceMass
      (w := afNomeSchedule.nome stage)
      (Q'.le_of_lt hw0)) ?_
  refine Q'.le_trans' _ _ _
    (boundedSU2PhysicalOutsideFaceMass_le_unionMass
      hw0 hcutoff
      (List.range (plaquetteEdgeCount 2))
      (range_nodup _)) ?_
  rw [List.length_range, ambientTwo_plaquetteCount]
  exact htensor

/-- Same-nome normalized Boolean events inherit the exact AF terminal slab
cutoff tail.  This does not compare the event law at the next AF nome. -/
theorem afTerminalSlabEventProbability_abs_le
    {depth later : Nat} (hdepth : 8 ≤ depth)
    (hlater : (afTerminalData depth).cutoff ≤ later)
    (event : EdgeLabelling → Bool) :
    absQ
        (slabNomeCutoffEventProbability
            (afTerminalData depth).coupling
            (afTerminalData depth).coupling_nonnegative
            (afTerminalData depth).cutoff 1 event +
          -slabNomeCutoffEventProbability
            (afTerminalData depth).coupling
            (afTerminalData depth).coupling_nonnegative
            later 1 event) ≤
      dyad (afTerminalSlabTailPrecision (depth + 1)) := by
  exact Q'.le_trans' _ _ _
    (slabNomeCutoffEventProbability_abs_le_increment
      (afTerminalData depth).coupling_nonnegative
      hlater event)
    (afTerminalSlabCutoffIncrement_le hdepth hlater)

/-! ## Axiom audit -/

#print axioms afTerminalHeatCeiling_le_twoPow
#print axioms afTerminalLabelPartial_le_twoPow
#print axioms afTerminalTensorBurn
#print axioms afTerminalSlabTailPrecision
#print axioms afTerminalTensorBurn_le
#print axioms afTerminalSlabTailPrecision_add_burn
#print axioms afTerminalSlabCutoffIncrement_le
#print axioms afTerminalSlabEventProbability_abs_le

end
  YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalSlabTail
