/-
# Moving rational centering reaches the completed BF4 vacuum pairing

A finite root-sector cylinder is rational-linear, while its cutoff-removed
vacuum coefficient is generally a Bishop real.  Exact subtraction of that
coefficient therefore need not remain a dense cylinder.  The legal
replacement is to center the same finite coefficient against the pulled
stationary law at cutoff `stage`, changing only its rational root coordinate.

This module proves that the resulting dense cylinders have actual completed
vacuum-pairing representatives converging to zero.  The proof retains one
fixed base coefficient throughout.  It identifies the cutoff-Cauchy head
correction `C`, pulled root weight `R`, and pulled mean `M` by the exact limit
identity `C * R = M`, then contracts the rational centered means to zero.

This is the vacuum-pairing half of a concrete observable path.  It does not
yet construct an explicit-modulus Cauchy sequence in the completed carrier,
prove that its limit is nonzero, identify all completed transfer moments with
rationals, or inhabit the dynamic observable pin.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Constructive.TrigSignedAdd
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseVacuumPairing
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseVacuumPairing
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The legal moving rational cylinder -/

/-- The same fixed finite cylinder coefficient, centered against the pulled
stationary law at one representation cutoff. -/
def centralPhysicalVacuumSectorMovingCenteredPresentation
    {w : Q'} (hw0 : (0 : Q') < w)
    (base half : Nat) (coefficient : Nat -> Q') (stage : Nat) :
    CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half where
  base := base
  coefficient :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
      w (Q'.le_of_lt hw0) base stage half coefficient

/-- At its selected cutoff, the moving presentation is exactly centered on
the pulled old component. -/
theorem centralPhysicalVacuumSectorMovingCenteredPresentation_meanZero
    {w : Q'} (hw0 : (0 : Q') < w)
    (base half : Nat) (coefficient : Nat -> Q') (stage : Nat) :
    centralPhysicalFinitePulledVacuumSectorWeightedMean
        w (Q'.le_of_lt hw0) base stage half
        (centralPhysicalVacuumSectorMovingCenteredPresentation
          hw0 base half coefficient stage).coefficient ≈
      0 := by
  exact
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient_meanZero
      w (Q'.le_of_lt hw0) base stage half coefficient

/-! ## 2. The head correction is the exact limiting mean/root ratio -/

@[simp] theorem centralPhysicalHeadCorrectionCutoffLimit_approx
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat -> Q') (stage : Nat) :
    (centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffLimit
      hw0 hw1 base half coefficient).approx stage =
      centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
        hw0 base half coefficient stage := rfl

@[simp] theorem centralPhysicalPulledWeightCutoffLimit_approx
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half index : Nat)
    (hindex : index <
      centralPhysicalFiniteCarrierSize w (Q'.le_of_lt hw0) base half)
    (stage : Nat) :
    (centralPhysicalFinitePulledWeightCutoffLimit
      hw0 hw1 base half index hindex).approx stage =
      centralPhysicalFinitePulledWeight
        w (Q'.le_of_lt hw0) base stage half index := rfl

@[simp] theorem centralPhysicalPulledVacuumSectorMeanCutoffLimit_approx
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat -> Q') (stage : Nat) :
    (centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
      hw0 hw1 base half coefficient).approx stage =
      centralPhysicalFinitePulledVacuumSectorWeightedMean
        w (Q'.le_of_lt hw0) base stage half coefficient := rfl

/-- The cutoff-Cauchy head correction times the cutoff-limit root weight is
the cutoff-limit pulled mean.  This is an equality of genuine Bishop reals,
proved from the exact rational division identity at every matched cutoff. -/
theorem centralPhysicalHeadCorrection_mul_root_equiv_mean
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat -> Q') :
    CReal.Equiv
      (CReal.mul
        (centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffLimit
          hw0 hw1 base half coefficient)
        (centralPhysicalFinitePulledWeightCutoffLimit
          hw0 hw1 base half 0
          (centralPhysicalFiniteVacuumSectorIndex_lt
            w (Q'.le_of_lt hw0) base half
            (zero_mem_centralPhysicalFiniteVacuumSectorIndices
              w (Q'.le_of_lt hw0) base half))))
      (centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
        hw0 hw1 base half coefficient) := by
  apply YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
  intro stage
  change
    centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
        hw0 base half coefficient stage *
      centralPhysicalFinitePulledWeight
        w (Q'.le_of_lt hw0) base stage half 0 ≈
    centralPhysicalFinitePulledVacuumSectorWeightedMean
      w (Q'.le_of_lt hw0) base stage half coefficient
  exact Q'.divPos_mul_eqv
    (centralPhysicalFinitePulledVacuumSectorWeightedMean
      w (Q'.le_of_lt hw0) base stage half coefficient)
    (centralPhysicalFinitePulledWeight
      w (Q'.le_of_lt hw0) base stage half 0)
    (centralPhysicalFinitePulledWeight_zero_pos
      w (Q'.le_of_lt hw0) base stage half)

/-! ## 3. A fixed rational centering has an exact completed-mean expansion -/

private theorem listQSum_ite_root_local
    (value : Nat -> Q') : forall states : List Nat,
    states.Nodup -> 0 ∈ states ->
    listQSum (fun index => if index = 0 then value index else 0) states ≈
      value 0
  | [], _hnodup, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [listQSum]
        have htailZero :
            listQSum (fun index => if index = 0 then value index else 0)
                tail ≈ 0 := by
          refine Q'.eqv_trans _
            (listQSum (fun _ => (0 : Q')) tail) _ ?_ ?_
          · apply listQSum_congr_on
            intro index hindex
            rw [if_neg]
            exact Q'.eqv_refl 0
            intro hzero
            subst index
            exact hparts.1 hindex
          · exact listQSum_zero tail
        exact Q'.eqv_trans _ (value 0 + 0) _
          (Q'.add_eqv_congr_left _ _ _ htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · have hhead : head ≠ 0 := by
          intro hzero
          subst head
          exact hparts.1 htail
        simp only [listQSum, if_neg hhead]
        exact Q'.eqv_trans _ (0 + value 0) _
          (Q'.add_eqv_congr'
            (Q'.eqv_refl 0)
            (listQSum_ite_root_local value tail hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' _))

theorem finiteListRootShiftedWeightedMean
    (states : List Nat) (weight coefficient : Nat -> Q')
    (hnodup : states.Nodup) (hroot : 0 ∈ states)
    (scalar : Q') :
    listQSum
        (fun index =>
          (coefficient index + if index = 0 then scalar else 0) *
            weight index)
        states ≈
      listQSum (fun index => coefficient index * weight index) states +
        scalar * weight 0 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun index => coefficient index * weight index +
        (if index = 0 then scalar else 0) * weight index)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro index _hindex
    exact Q'.add_mul_eqv _ _ _
  refine Q'.eqv_trans _
    (listQSum (fun index => coefficient index * weight index) states +
      listQSum
        (fun index => (if index = 0 then scalar else 0) * weight index)
        states) _ (listQSum_add _ _ states) ?_
  apply Q'.add_eqv_congr_left
  refine Q'.eqv_trans _
    (listQSum
      (fun index => if index = 0 then scalar * weight index else 0)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro index _hindex
    by_cases hzero : index = 0
    · simp only [if_pos hzero]
      exact Q'.eqv_refl _
    · simp only [if_neg hzero]
      exact Q'.zero_mul_eqv _
  exact listQSum_ite_root_local
    (fun index => scalar * weight index) states hnodup hroot

/-- For one rational centering stage, the fixed-presentation pulled mean
limit is the raw pulled mean plus that rational root shift times the pulled
root-weight limit. -/
theorem centralPhysicalMovingCenteredMeanLimit_equiv_expansion
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat -> Q') (stage : Nat) :
    let correction :=
      centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffLimit
        hw0 hw1 base half coefficient
    let root := centralPhysicalFinitePulledWeightCutoffLimit
      hw0 hw1 base half 0
      (centralPhysicalFiniteVacuumSectorIndex_lt
        w (Q'.le_of_lt hw0) base half
        (zero_mem_centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw0) base half))
    let mean :=
      centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
        hw0 hw1 base half coefficient
    CReal.Equiv
      (centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
        hw0 hw1 base half
        (centralPhysicalVacuumSectorMovingCenteredPresentation
          hw0 base half coefficient stage).coefficient)
      (CReal.add mean
        (CReal.mul (CReal.ofQ' (-(correction.approx stage))) root)) := by
  dsimp only
  apply YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
  intro later
  let states := centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw0) base half
  let weight := centralPhysicalFinitePulledWeight
    w (Q'.le_of_lt hw0) base later half
  have hfinite := finiteListRootShiftedWeightedMean
    states weight coefficient
    (centralPhysicalFiniteVacuumSectorIndices_nodup
      w (Q'.le_of_lt hw0) base half)
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half)
    (-(centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
      hw0 base half coefficient stage))
  simpa only [
    centralPhysicalVacuumSectorMovingCenteredPresentation,
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient,
    finiteListRootCenteredCoefficient,
    centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox,
    centralPhysicalFinitePulledVacuumSectorWeightedMean,
    centralPhysicalHeadCorrectionCutoffLimit_approx,
    centralPhysicalPulledWeightCutoffLimit_approx,
    centralPhysicalPulledVacuumSectorMeanCutoffLimit_approx,
    CReal.add_approx, CReal.mul,
    CReal.ofQ', weight, states] using hfinite

/-! ## 4. Contraction to the zero completed vacuum pairing -/

/-- The pulled-mean representatives of the actual completed vacuum pairings
of the moving rationally centered cylinders converge to zero. -/
theorem centralPhysicalMovingCenteredMeanLimit_converges_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat -> Q') :
    CReal.ConvergesTo
      (fun stage =>
        centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
          hw0 hw1 base half
          (centralPhysicalVacuumSectorMovingCenteredPresentation
            hw0 base half coefficient stage).coefficient)
      CReal.czero := by
  let correction :=
    centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffLimit
      hw0 hw1 base half coefficient
  let root := centralPhysicalFinitePulledWeightCutoffLimit
    hw0 hw1 base half 0
    (centralPhysicalFiniteVacuumSectorIndex_lt
      w (Q'.le_of_lt hw0) base half
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) base half))
  let mean :=
    centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
      hw0 hw1 base half coefficient
  let expansion := fun stage => CReal.add mean
    (CReal.mul (CReal.ofQ' (-(correction.approx stage))) root)
  have hscalar : CReal.ConvergesTo
      (fun stage => CReal.ofQ' (-(correction.approx stage)))
      (CReal.neg correction) := by
    simpa only [CReal.ofQ'_neg] using
      (CReal.convergesTo_neg (CReal.convergesTo_self correction))
  have hexpansion : CReal.ConvergesTo expansion
      (CReal.add mean (CReal.mul (CReal.neg correction) root)) :=
    CReal.convergesTo_add (CReal.convergesTo_const mean)
      (CReal.convergesTo_mul_general hscalar
        (CReal.convergesTo_const root))
  have hproduct : CReal.Equiv (CReal.mul correction root) mean :=
    centralPhysicalHeadCorrection_mul_root_equiv_mean
      hw0 hw1 base half coefficient
  have hnegative : CReal.Equiv
      (CReal.mul (CReal.neg correction) root) (CReal.neg mean) :=
    CReal.Equiv.trans
      (YMGap.Constructive.TrigSignedAdd.neg_mul correction root)
      (CReal.neg_congr hproduct)
  have hzero : CReal.Equiv
      (CReal.add mean (CReal.mul (CReal.neg correction) root))
      CReal.czero :=
    CReal.Equiv.trans (CReal.add_congr_right hnegative)
      (CReal.sub_self_eqv_zero mean)
  have hexpansionZero : CReal.ConvergesTo expansion CReal.czero :=
    CReal.convergesTo_limit_congr hexpansion hzero
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := expansion)
  · intro stage
    exact CReal.Equiv.symm
      (centralPhysicalMovingCenteredMeanLimit_equiv_expansion
        hw0 hw1 base half coefficient stage)
  · exact hexpansionZero

/-- At every rational centering stage, the actual completed global-vacuum
pairing of the embedded dense cylinder is represented by the corresponding
pulled mean used in the convergence theorem above. -/
theorem centralPhysicalMovingCentered_completedVacuumPairing_eq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat -> Q') (stage : Nat) :
    let presentation :=
      centralPhysicalVacuumSectorMovingCenteredPresentation
        hw0 base half coefficient stage
    centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep presentation))
        (centralPhysicalCutoffCompletedVacuum hw0 hw1 half) =
      Quotient.mk CReal.crealSetoid
        (centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
          hw0 hw1 base half presentation.coefficient) := by
  dsimp only
  exact
    centralPhysicalVacuumSectorCylinder_completedVacuumPairing_embedRep_eq_pulled
      hw0 hw1 half
      (centralPhysicalVacuumSectorMovingCenteredPresentation
        hw0 base half coefficient stage)

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing.centralPhysicalVacuumSectorMovingCenteredPresentation_meanZero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing.centralPhysicalHeadCorrection_mul_root_equiv_mean
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing.centralPhysicalMovingCenteredMeanLimit_equiv_expansion
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing.centralPhysicalMovingCenteredMeanLimit_converges_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing.centralPhysicalMovingCentered_completedVacuumPairing_eq
