/-
# The executable `1/32` BF4 density core

For a finite stationary density `k(x,y)` relative to `pi`, retain exactly
the targets on which

    |k(x,y) - 1| <= 1/32.

This source-dependent predicate is executable over the rational BF4 carrier.
Its pointwise window is true by construction.  A full weighted centered-row
bound `<= 1/4096` forces the complement to have stationary mass at most
`1/128`, and its conditional mass at most `33/4096`; both are below `1/64`.

Thus the stronger scalar Perron remainder `1/4096` constructs, rather than
postulates, the exact `1/32 + 1/64 + 1/64` core/tail certificate.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalConditionalDensityContraction

namespace YMGap.Continuum.BF4PhysicalDensityThresholdCore

set_option maxRecDepth 100000
set_option maxHeartbeats 200000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalConditionalDensity
open YMGap.Continuum.BF4PhysicalConditionalDensityContraction
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSignedKernelL1
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RcQuadResidualClose
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-- Pointwise core tolerance. -/
def densityCoreTolerance : Q' :=
  Q'.mkPos 1 32 (by decide)

/-- Strong row tolerance used to pay both tails. -/
def densityCoreRowTolerance : Q' :=
  Q'.mkPos 1 4096 (by decide)

/-- Common tail tolerance. -/
def densityCoreTailTolerance : Q' :=
  Q'.mkPos 1 64 (by decide)

/-- The literal source-dependent threshold core of a rational density. -/
def finiteDensityThirtySecondCore
    {State : Type}
    (kernel : State → State → Q')
    (source target : State) : Bool :=
  decide
    (Q'.abs (kernel source target + (-1)) ≤
      densityCoreTolerance)

theorem finiteDensityThirtySecondCore_pointwise
    {State : Type}
    (kernel : State → State → Q')
    (source target : State)
    (hcore :
      finiteDensityThirtySecondCore
        kernel source target = true) :
    Q'.abs (kernel source target + (-1)) ≤
      densityCoreTolerance := by
  unfold finiteDensityThirtySecondCore at hcore
  simpa only [decide_eq_true_eq] using hcore

private theorem weighted_abs_centered_eqv
    (weight value : Q')
    (weight_nonnegative : (0 : Q') ≤ weight) :
    Q'.abs (weight * value) ≈
      weight * Q'.abs value := by
  refine Q'.eqv_trans _ _ _
    (q_abs_mul_eqv weight value) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_of_eq (abs_of_nonneg weight_nonnegative))

private theorem one_le_thirtyTwo_mul_abs_of_tail
    {value : Q'}
    (htail :
      ¬ Q'.abs value ≤ densityCoreTolerance) :
    (1 : Q') ≤
      Q'.ofNat 32 * Q'.abs value := by
  have hweak :
      densityCoreTolerance ≤ Q'.abs value :=
    Q'.le_of_not_le' htail
  have hscaled :
      Q'.ofNat 32 * densityCoreTolerance ≤
        Q'.ofNat 32 * Q'.abs value :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      hweak (by decide)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (by
    unfold densityCoreTolerance
    decide)) hscaled

private theorem tailWeight_pointwise_le
    {State : Type}
    {weight : State → Q'}
    {kernel : State → State → Q'}
    {source target : State}
    (weight_nonnegative : (0 : Q') ≤ weight target) :
    (if finiteDensityThirtySecondCore
          kernel source target = true then 0
      else weight target) ≤
      Q'.ofNat 32 *
        (weight target *
          Q'.abs (kernel source target + (-1))) := by
  by_cases hcore :
      finiteDensityThirtySecondCore
        kernel source target = true
  · rw [if_pos hcore]
    exact Q'.mul_nonneg _ _
      (by decide)
      (Q'.mul_nonneg _ _
        weight_nonnegative
        (Q'.abs_nonneg _))
  · rw [if_neg hcore]
    have htail :
        ¬ Q'.abs
            (kernel source target + (-1)) ≤
          densityCoreTolerance := by
      intro hwindow
      apply hcore
      unfold finiteDensityThirtySecondCore
      simpa only [decide_eq_true_eq] using hwindow
    have hone :=
      one_le_thirtyTwo_mul_abs_of_tail htail
    have hscaled :
        weight target * 1 ≤
          weight target *
            (Q'.ofNat 32 *
              Q'.abs
                (kernel source target + (-1))) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        hone weight_nonnegative
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm
        (Q'.mul_one_eqv (weight target))))
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (by
          calc
            weight target *
                  (Q'.ofNat 32 *
                    Q'.abs
                      (kernel source target + (-1))) ≈
                (weight target * Q'.ofNat 32) *
                  Q'.abs
                    (kernel source target + (-1)) :=
              Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
            _ ≈
                (Q'.ofNat 32 * weight target) *
                  Q'.abs
                    (kernel source target + (-1)) :=
              Q'.mul_eqv_congr_right _ _ _
                (Q'.mul_comm_eqv
                  (weight target) (Q'.ofNat 32))
            _ ≈
                Q'.ofNat 32 *
                  (weight target *
                    Q'.abs
                      (kernel source target + (-1))) :=
              Q'.mul_assoc_eqv _ _ _)))

private theorem kernel_le_one_add_abs_centered
    {value : Q'} (value_nonnegative : (0 : Q') ≤ value) :
    value ≤ (1 : Q') + Q'.abs (value + (-1)) := by
  have htriangle :=
    Q'.abs_le_abs_add_abs_sub value 1
  have habsValue :
      Q'.abs value ≈ value :=
    Q'.eqv_of_eq (abs_of_nonneg value_nonnegative)
  have habsOne :
      Q'.abs (1 : Q') ≈ 1 := by decide
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv habsValue)
    (Q'.le_trans' _ _ _ htriangle
      (Q'.le_of_eqv
        (Q'.add_eqv_congr_right _ _ _ habsOne)))

private theorem tailKernel_pointwise_le
    {State : Type}
    {weight : State → Q'}
    {kernel : State → State → Q'}
    {source target : State}
    (weight_nonnegative : (0 : Q') ≤ weight target)
    (kernel_nonnegative : (0 : Q') ≤ kernel source target) :
    (if finiteDensityThirtySecondCore
          kernel source target = true then 0
      else weight target * kernel source target) ≤
      (if finiteDensityThirtySecondCore
            kernel source target = true then 0
        else weight target) +
        weight target *
          Q'.abs (kernel source target + (-1)) := by
  by_cases hcore :
      finiteDensityThirtySecondCore
        kernel source target = true
  · rw [if_pos hcore, if_pos hcore]
    exact Q'.le_trans'
      0
      (weight target *
        Q'.abs (kernel source target + (-1)))
      (0 +
        weight target *
          Q'.abs (kernel source target + (-1)))
      (Q'.mul_nonneg _ _
        weight_nonnegative (Q'.abs_nonneg _))
      (Q'.ge_of_eqv
        (Q'.eqv_of_eq
          (Q'.zero_add'
            (weight target *
              Q'.abs
                (kernel source target + (-1))))))
  · rw [if_neg hcore, if_neg hcore]
    have hkernel :=
      kernel_le_one_add_abs_centered
        kernel_nonnegative
    have hscaled :
        weight target * kernel source target ≤
          weight target *
            ((1 : Q') +
              Q'.abs
                (kernel source target + (-1))) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        hkernel weight_nonnegative
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (by
        calc
          weight target *
                ((1 : Q') +
                  Q'.abs
                    (kernel source target + (-1))) ≈
              weight target * 1 +
                weight target *
                  Q'.abs
                    (kernel source target + (-1)) :=
            Q'.mul_add_eqv _ _ _
          _ ≈
              weight target +
                weight target *
                  Q'.abs
                    (kernel source target + (-1)) :=
            Q'.add_eqv_congr_right _ _ _
              (Q'.mul_one_eqv _)))

private theorem centeredRowMass_eqv_sum_weight_abs
    {State : Type}
    (states : List State)
    (weight : State → Q')
    (kernel : State → State → Q')
    (source : State)
    (weight_nonnegative :
      ∀ state, state ∈ states →
        (0 : Q') ≤ weight state) :
    finiteWeightedCenteredRowMass
        states weight kernel source ≈
      listQSum
        (fun target =>
          weight target *
            Q'.abs
              (kernel source target + (-1)))
        states := by
  unfold finiteWeightedCenteredRowMass finiteL1Norm
    finiteWeightedCenteredTransition finiteCenteredDensity
  apply listQSum_congr_on
  intro target htarget
  exact weighted_abs_centered_eqv
    (weight target)
    (kernel source target + (-1))
    (weight_nonnegative target htarget)

/-- A `1/4096` weighted centered row constructs the executable threshold
core with its `1/32` pointwise window and both `1/64` tail bounds. -/
def finiteDensityThirtySecondCoreWindow
    {State : Type}
    (states : List State)
    (weight : State → Q')
    (kernel : State → State → Q')
    (source : State)
    (weight_nonnegative :
      ∀ state, state ∈ states →
        (0 : Q') ≤ weight state)
    (kernel_nonnegative :
      ∀ target, target ∈ states →
        (0 : Q') ≤ kernel source target)
    (weight_total :
      listQSum weight states ≈ 1)
    (centered_row :
      finiteWeightedCenteredRowMass
          states weight kernel source ≤
        densityCoreRowTolerance) :
    FiniteWeightedDensityCoreTailWindow
      states weight kernel source
      (finiteDensityThirtySecondCore kernel source)
      densityCoreTolerance densityCoreTailTolerance where
  weight_nonnegative := weight_nonnegative
  kernel_nonnegative := kernel_nonnegative
  weight_total := weight_total
  coreTolerance_nonnegative := by
    unfold densityCoreTolerance
    decide
  core_pointwise := by
    intro target _ hcore
    exact finiteDensityThirtySecondCore_pointwise
      kernel source target hcore
  tail_weight := by
    let error := fun target =>
      weight target *
        Q'.abs (kernel source target + (-1))
    have hsum :
        listQSum
            (fun target =>
              if finiteDensityThirtySecondCore
                    kernel source target = true then 0
              else weight target)
            states ≤
          listQSum
            (fun target => Q'.ofNat 32 * error target)
            states :=
      listQSum_mono _ _ states
        (fun target htarget =>
          tailWeight_pointwise_le
            (weight_nonnegative target htarget))
    have hfactor :
        listQSum
            (fun target => Q'.ofNat 32 * error target)
            states ≈
          Q'.ofNat 32 * listQSum error states :=
      listQSum_mul_left
        (Q'.ofNat 32) error states
    have herror :
        listQSum error states ≤
          densityCoreRowTolerance := by
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (centeredRowMass_eqv_sum_weight_abs
              states weight kernel source
              weight_nonnegative)))
        centered_row
    have hscaled :
        Q'.ofNat 32 * listQSum error states ≤
          Q'.ofNat 32 * densityCoreRowTolerance :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        herror (by decide)
    exact Q'.le_trans' _ _ _ hsum
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv hfactor)
        (Q'.le_trans' _ _ _ hscaled
          (by
            unfold densityCoreRowTolerance
              densityCoreTailTolerance
            decide)))
  tail_kernel := by
    let error := fun target =>
      weight target *
        Q'.abs (kernel source target + (-1))
    let tailWeight := fun target =>
      if finiteDensityThirtySecondCore
            kernel source target = true then 0
      else weight target
    have hpoint :
        ∀ target, target ∈ states →
          (if finiteDensityThirtySecondCore
                kernel source target = true then 0
            else weight target * kernel source target) ≤
          tailWeight target + error target := by
      intro target htarget
      exact tailKernel_pointwise_le
        (weight_nonnegative target htarget)
        (kernel_nonnegative target htarget)
    have hsum :
        listQSum
            (fun target =>
              if finiteDensityThirtySecondCore
                    kernel source target = true then 0
              else weight target * kernel source target)
            states ≤
          listQSum
            (fun target =>
              tailWeight target + error target)
            states :=
      listQSum_mono _ _ states hpoint
    have hsplit :
        listQSum
            (fun target =>
              tailWeight target + error target)
            states ≈
          listQSum tailWeight states +
            listQSum error states :=
      listQSum_add tailWeight error states
    have htailWeight :
        listQSum tailWeight states ≤
          Q'.mkPos 1 128 (by decide) := by
      have hsumWeight :
          listQSum tailWeight states ≤
            listQSum
              (fun target =>
                Q'.ofNat 32 * error target)
              states :=
        listQSum_mono _ _ states
          (fun target htarget =>
            tailWeight_pointwise_le
              (weight_nonnegative target htarget))
      have hfactor :
          listQSum
              (fun target =>
                Q'.ofNat 32 * error target)
              states ≈
            Q'.ofNat 32 * listQSum error states :=
        listQSum_mul_left
          (Q'.ofNat 32) error states
      have herror :
          listQSum error states ≤
            densityCoreRowTolerance := by
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (Q'.eqv_symm
              (centeredRowMass_eqv_sum_weight_abs
                states weight kernel source
                weight_nonnegative)))
          centered_row
      exact Q'.le_trans' _ _ _ hsumWeight
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv hfactor)
          (Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_left _ _ _
              herror (by decide))
            (Q'.le_of_eqv (by
              unfold densityCoreRowTolerance
              decide))))
    have herror :
        listQSum error states ≤
          densityCoreRowTolerance := by
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (centeredRowMass_eqv_sum_weight_abs
              states weight kernel source
              weight_nonnegative)))
        centered_row
    exact Q'.le_trans' _ _ _ hsum
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv hsplit)
        (Q'.le_trans' _ _ _
          (Q'.add_le_add htailWeight herror)
          (by
            unfold densityCoreRowTolerance
              densityCoreTailTolerance
            decide)))

/-! ## BF4 specialization -/

/-- The actual scale-local BF4 core, expressed directly in terms of the
canonical conditional density on the exact positive-row carrier. -/
def centralPhysicalThirtySecondCore
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (source target : EdgeLabelling) : Bool :=
  finiteDensityThirtySecondCore
    (centralPhysicalConditionalDensity w hw K half)
    source target

/-- A literal canonical-density row bound `<=1/4096` inhabits the requested
BF4 `1/32 + 1/64 + 1/64` core/tail window. -/
def centralPhysicalThirtySecondCoreTailWindow
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half)
    (centered_row :
      finiteWeightedCenteredRowMass
          (centralPositiveHalfStates w hw K half)
          (centralPhysicalRowMarginal w hw K half)
          (centralPhysicalConditionalDensity w hw K half)
          source ≤
        densityCoreRowTolerance) :
    PhysicalConditionalDensityCoreTailWindow
      w hw K half source
      (centralPhysicalThirtySecondCore
        w hw K half source) where
  source_mem := source_mem
  window := ⟨
    finiteDensityThirtySecondCoreWindow
      (centralPositiveHalfStates w hw K half)
      (centralPhysicalRowMarginal w hw K half)
      (centralPhysicalConditionalDensity w hw K half)
      source
      (fun state _ =>
        centralPhysicalRowMarginal_nonnegative
          hw K half state)
      (fun target _ =>
        centralPhysicalConditionalDensity_nonnegative
          hw K half source target)
      (centralPositiveRowMarginal_total_one
        w hw K half)
      centered_row⟩

end YMGap.Continuum.BF4PhysicalDensityThresholdCore

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalDensityThresholdCore.finiteDensityThirtySecondCore_pointwise
#print axioms YMGap.Continuum.BF4PhysicalDensityThresholdCore.finiteDensityThirtySecondCoreWindow
#print axioms YMGap.Continuum.BF4PhysicalDensityThresholdCore.centralPhysicalThirtySecondCoreTailWindow
