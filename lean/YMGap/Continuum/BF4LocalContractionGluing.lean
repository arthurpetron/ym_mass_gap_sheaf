/-
# Direct BF4 sixteenth from local contraction and full-carrier gluing

On the complete positive BF4 half-state carrier, suppose a genuine
one-step stationary density:

* glues by exact all-word convolution to the physical whole-slab density;
* has weighted centered-row `L1` norm at most `qS`; and
* satisfies `qS <= 1/4`.

The same local norm controls both endpoint buffers.  The signed-kernel
tensorization theorem controls the middle by `qS^(depth-2)`.  At every depth
at least three,

    qS^2 qS^(depth-2) <= 1/16.

Thus the physical centered row is at most `pi(source)/16`, without paying a
separate Faraut endpoint spread.

The only Yang--Mills-specific inputs left in the final structure are the
full-carrier density gluing identity and the local `qS <= 1/4` estimate for
the genuine BF4 slice kernel.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4StationaryDensityBufferSplit
import YMGap.Continuum.RcQuadResidualClose

namespace YMGap.Continuum.BF4LocalContractionGluing

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4BufferedPerronRowConvergence
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4PhysicalConditionalDensity
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSignedKernelL1
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.CasimirMoment
open YMGap.Continuum.RcQuadResidualClose
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-- Moving a nonnegative stationary weight through absolute value converts
the weighted centered transition norm into the more familiar weighted
absolute density row. -/
theorem finiteWeightedCenteredRowMass_eq_weight_abs
    {State : Type}
    (states : List State) (weight : State → Q')
    (kernel : State → State → Q')
    (weight_nonnegative :
      ∀ state, state ∈ states →
        (0 : Q') ≤ weight state)
    (source : State) :
    finiteWeightedCenteredRowMass
        states weight kernel source ≈
      listQSum
        (fun target =>
          weight target *
            Q'.abs
              (finiteCenteredDensity
                kernel source target))
        states := by
  unfold finiteWeightedCenteredRowMass finiteL1Norm
    finiteWeightedCenteredTransition
  apply listQSum_congr_on
  intro target htarget
  refine Q'.eqv_trans _
    (Q'.abs (weight target) *
      Q'.abs
        (finiteCenteredDensity
          kernel source target)) _ ?_ ?_
  · exact q_abs_mul_eqv
      (weight target)
      (finiteCenteredDensity kernel source target)
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_of_eq
        (abs_of_nonneg
          (weight_nonnegative target htarget)))

/-- The fully reduced physical input: exact density gluing on the complete
positive carrier and a local centered contraction. -/
structure PhysicalBF4LocalContractionGluingRow
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat)
    (source : EdgeLabelling)
    (depth : Nat)
    (oneStep : EdgeLabelling → EdgeLabelling → Q')
    (qS : Q') : Type where
  source_mem :
    source ∈
      centralPositiveHalfStates
        w hw K halfExtent
  depth_at_least_three :
    3 ≤ depth
  qS_nonnegative :
    (0 : Q') ≤ qS
  oneStep_row :
    ∀ row,
      listQSum
          (fun state =>
            centralPhysicalRowMarginal
                w hw K halfExtent state *
              oneStep row state)
          (centralPositiveHalfStates
            w hw K halfExtent) ≈
        1
  oneStep_column :
    ∀ column,
      listQSum
          (fun state =>
            centralPhysicalRowMarginal
                w hw K halfExtent state *
              oneStep state column)
          (centralPositiveHalfStates
            w hw K halfExtent) ≈
        1
  density_gluing :
    ∀ target,
      target ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        centralPhysicalConditionalDensity
            w hw K halfExtent source target ≈
          finiteWeightedDensityCompose
            (centralPositiveHalfStates
              w hw K halfExtent)
            (centralPhysicalRowMarginal
              w hw K halfExtent)
            oneStep
            (finiteWeightedDensityCompose
              (centralPositiveHalfStates
                w hw K halfExtent)
              (centralPhysicalRowMarginal
                w hw K halfExtent)
              (finiteWeightedDensityPower
                (centralPositiveHalfStates
                  w hw K halfExtent)
                (centralPhysicalRowMarginal
                  w hw K halfExtent)
                oneStep (depth - 3))
              oneStep)
            source target
  one_step_centered_bound :
    ∀ first,
      first ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        finiteWeightedCenteredRowMass
            (centralPositiveHalfStates
              w hw K halfExtent)
            (centralPhysicalRowMarginal
              w hw K halfExtent)
            oneStep first ≤
          qS

namespace PhysicalBF4LocalContractionGluingRow

/-- The local centered norm pays both endpoint buffers. -/
def toOneStepContractionGluingRow
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source : EdgeLabelling}
    {depth : Nat}
    {oneStep : EdgeLabelling → EdgeLabelling → Q'}
    {qS : Q'}
    (data :
      PhysicalBF4LocalContractionGluingRow
        hw K halfExtent source depth oneStep qS) :
    PhysicalBF4OneStepContractionGluingRow
      hw K halfExtent source depth oneStep qS qS where
  source_mem :=
    data.source_mem
  depth_at_least_three :=
    data.depth_at_least_three
  endpointBound_nonnegative :=
    data.qS_nonnegative
  qS_nonnegative :=
    data.qS_nonnegative
  oneStep_row :=
    data.oneStep_row
  oneStep_column :=
    data.oneStep_column
  density_gluing :=
    data.density_gluing
  one_step_centered_bound :=
    data.one_step_centered_bound
  left_bound := by
    exact data.one_step_centered_bound
      source data.source_mem
  right_bound := by
    intro first hfirst
    let states :=
      centralPositiveHalfStates
        w hw K halfExtent
    let weight :=
      centralPhysicalRowMarginal
        w hw K halfExtent
    have hrow :=
      data.one_step_centered_bound first hfirst
    have heq :
        finiteWeightedCenteredRowMass
            states weight oneStep first ≈
          listQSum
            (fun target =>
              weight target *
                Q'.abs
                  (finiteCenteredDensity
                    oneStep first target))
            states :=
      finiteWeightedCenteredRowMass_eq_weight_abs
        states weight oneStep
        (fun state _ =>
          centralPhysicalRowMarginal_nonnegative
            hw K halfExtent state)
        first
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm heq)) hrow

/-- Exact carrier-free bound before inserting the numeric quarter. -/
theorem physical_centered_row_le_local_power
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source : EdgeLabelling}
    {depth : Nat}
    {oneStep : EdgeLabelling → EdgeLabelling → Q'}
    {qS : Q'}
    (data :
      PhysicalBF4LocalContractionGluingRow
        hw K halfExtent source depth oneStep qS) :
    physicalCenteredPhysicalRowMass
        w hw K halfExtent source ≤
      ((qS * qS) * (qS ^ (depth - 2))) *
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
  data.toOneStepContractionGluingRow
    |>.toDensityPowerGluingRow
    |>.physical_centered_row_le

private theorem qsq_le_sixteenth
    {qS : Q'} (qS_nonnegative : (0 : Q') ≤ qS)
    (qS_le_quarter : qS ≤ quarter) :
    qS * qS ≤ Q'.mkPos 1 16 (by decide) := by
  have hquarterNonnegative :
      (0 : Q') ≤ quarter := by
    decide
  have hmul :
      qS * qS ≤ quarter * quarter :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right
        qS quarter qS qS_le_quarter qS_nonnegative)
      (Q'.mul_le_mul_of_nonneg_left
        qS quarter quarter qS_le_quarter
        hquarterNonnegative)
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_of_eqv (by decide))

/-- A local quarter contraction plus genuine all-label gluing proves the
physical centered `1/16` row directly. -/
theorem physical_centered_row_le_sixteenth
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source : EdgeLabelling}
    {depth : Nat}
    {oneStep : EdgeLabelling → EdgeLabelling → Q'}
    {qS : Q'}
    (qS_le_quarter : qS ≤ quarter)
    (data :
      PhysicalBF4LocalContractionGluingRow
        hw K halfExtent source depth oneStep qS) :
    physicalCenteredPhysicalRowMass
        w hw K halfExtent source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          w hw K halfExtent source := by
  have hqOne : qS ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ qS_le_quarter (by decide)
  have hpow :
      qS ^ (depth - 2) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (pow_base_mono qS 1
        data.qS_nonnegative hqOne (depth - 2))
      (Q'.le_of_eqv
        (one_pow_eqv (depth - 2)))
  have hcoefficient :
      (qS * qS) * (qS ^ (depth - 2)) ≤
        Q'.mkPos 1 16 (by decide) := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hpow
        (Q'.mul_nonneg _ _
          data.qS_nonnegative data.qS_nonnegative)) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_one_eqv (qS * qS))) ?_
    exact qsq_le_sixteenth
      data.qS_nonnegative qS_le_quarter
  exact Q'.le_trans' _ _ _
    data.physical_centered_row_le_local_power
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      hcoefficient
      (centralPhysicalRowMarginal_nonnegative
        hw K halfExtent source))

end PhysicalBF4LocalContractionGluingRow

end YMGap.Continuum.BF4LocalContractionGluing

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4LocalContractionGluing.finiteWeightedCenteredRowMass_eq_weight_abs
#print axioms YMGap.Continuum.BF4LocalContractionGluing.PhysicalBF4LocalContractionGluingRow.toOneStepContractionGluingRow
#print axioms YMGap.Continuum.BF4LocalContractionGluing.PhysicalBF4LocalContractionGluingRow.physical_centered_row_le_local_power
#print axioms YMGap.Continuum.BF4LocalContractionGluing.PhysicalBF4LocalContractionGluingRow.physical_centered_row_le_sixteenth
