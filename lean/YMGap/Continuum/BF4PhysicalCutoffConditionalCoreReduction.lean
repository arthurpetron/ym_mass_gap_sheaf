/-
# Old-row joint-kernel reduction for physical BF4 conditioning

The completed atomic Markov frontier now separates into an old source/target
core and moving shells.  This file contracts the already-proved entrywise
degree-thirteen cutoff estimate across one complete old target row.

For an old carrier of size `N`, ask every normalized joint-kernel entry for
tolerance `epsilon / N`.  Summing the absolute differences over the `N` old
targets then gives exactly `epsilon`.  The source and every target are proved
to occur in both later carriers by the explicit support/bound description of
the Cartesian enumeration.

This is an inhabited consequence of the existing physical cutoff theory.  It
does not yet divide by the row marginal: a positive old-row floor and target
shell bounds are still required to turn this joint-row estimate into the
conditional Markov core estimate.

## Axiom gate

Only finite lists, exact rational order/algebra, and the proved normalized
joint-kernel cutoff theorem are used.  There is no classical choice,
noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicCoreTailCauchy
import YMGap.Continuum.BF4SU2FixedMagneticPhysicalHSCauchy

namespace YMGap.Continuum.BF4PhysicalCutoffConditionalCoreReduction

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalHSCauchy
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem centralHalfStates_mem_of_le_local
    {base later half : Nat}
    (hcutoff : base <= later)
    {state : EdgeLabelling}
    (hstate : state ∈ centralHalfStates base half) :
    state ∈ centralHalfStates later half := by
  unfold centralHalfStates at hstate ⊢
  have hsound :=
    boundedEdgeLabellings_sound
      base (centralLowerFaceIds half) state hstate
  apply boundedEdgeLabellings_complete
  · intro id hid
    have hbound := hsound.1 id hid
    omega
  · exact hsound.2

private theorem listQSum_le_length_mul_local
    {A : Type} (value : A -> Q')
    {bound : Q'} (hbound0 : (0 : Q') <= bound) :
    forall items : List A,
      (forall item, item ∈ items -> value item <= bound) ->
      listQSum value items <= Q'.ofNat items.length * bound
  | [], _ =>
      Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound => by
      have hhead := hbound head List.mem_cons_self
      have htail := listQSum_le_length_mul_local value hbound0 tail
        (fun item hitem =>
          hbound item (List.mem_cons_of_mem head hitem))
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add hhead htail) ?_
      refine Q'.le_of_eqv (Q'.eqv_symm ?_)
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * bound) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ bound
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * bound +
          (1 : Q') * bound) _
        (Q'.add_mul_eqv
          (Q'.ofNat tail.length) 1 bound) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + bound) _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.one_mul_eqv bound))
        (Q'.add_comm_eqv
          (Q'.ofNat tail.length * bound) bound)

/-- Absolute normalized joint-kernel cutoff difference summed over one exact
old target row. -/
def centralOldRowCutoffDifferenceL1
    (w : Q') (hw : (0 : Q') <= w)
    (base first second half : Nat)
    (source : EdgeLabelling) : Q' :=
  listQSum
    (fun target =>
      Q'.abs
        (centralNormalizedPhysicalReflectedKernel
            w hw first half source target +
          -centralNormalizedPhysicalReflectedKernel
            w hw second half source target))
    (centralHalfStates base half)

/-- The executable degree-thirteen entry modulus contracts to an `l1` bound
on every old joint-kernel row, with the old carrier dimension paid exactly. -/
theorem centralOldRowCutoffDifferenceL1_le
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (base half : Nat)
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    {first second : Nat}
    (hfirst :
      centralOldCarrierHSCutoff w base half epsilon <= first)
    (hsecond :
      centralOldCarrierHSCutoff w base half epsilon <= second)
    (source : EdgeLabelling)
    (hsource : source ∈ centralHalfStates base half) :
    centralOldRowCutoffDifferenceL1
        w (Q'.le_of_lt hw0) base first second half source <=
      epsilon := by
  let tolerance :=
    centralOldCarrierEntryTolerance base half epsilon
  have htolerance0 : (0 : Q') <= tolerance :=
    Q'.le_of_lt
      (centralOldCarrierEntryTolerance_pos
        base half hepsilon)
  have hbaseFirst : base <= first :=
    Nat.le_trans (Nat.le_max_left _ _) hfirst
  have hbaseSecond : base <= second :=
    Nat.le_trans (Nat.le_max_left _ _) hsecond
  have hmodulusFirst :
      slabNomeBoundedObservableModulus
          w (centralExtent half) tolerance <= first :=
    Nat.le_trans (Nat.le_max_right _ _) hfirst
  have hmodulusSecond :
      slabNomeBoundedObservableModulus
          w (centralExtent half) tolerance <= second :=
    Nat.le_trans (Nat.le_max_right _ _) hsecond
  have hsourceFirst :=
    centralHalfStates_mem_of_le_local hbaseFirst hsource
  have hsourceSecond :=
    centralHalfStates_mem_of_le_local hbaseSecond hsource
  have hsum :
      centralOldRowCutoffDifferenceL1
          w (Q'.le_of_lt hw0) base first second half source <=
        Q'.ofNat (centralHalfStates base half).length * tolerance := by
    unfold centralOldRowCutoffDifferenceL1
    apply listQSum_le_length_mul_local _ htolerance0
    intro target htarget
    have htargetFirst :=
      centralHalfStates_mem_of_le_local hbaseFirst htarget
    have htargetSecond :=
      centralHalfStates_mem_of_le_local hbaseSecond htarget
    have htwo :=
      centralNormalizedPhysicalReflectedKernel_twoSided_of_modulus
        hw0 hw1 half source target
        (centralOldCarrierEntryTolerance_pos
          base half hepsilon)
        hmodulusFirst hmodulusSecond
        hsourceFirst htargetFirst hsourceSecond htargetSecond
    exact CReal.abs_sub_le_of_bounds htwo.1 htwo.2
  refine Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _
    (tolerance *
      Q'.ofNat (centralHalfStates base half).length) _
    (Q'.mul_comm_eqv _ _) ?_
  unfold tolerance centralOldCarrierEntryTolerance
  exact Q'.divPos_mul_eqv _ _ _

/-! ## 2. Constructive stability of positive conditioning -/

private theorem divPos_one_sided_conditioning_stability
    (numeratorLeft numeratorRight denominatorLeft denominatorRight : Q')
    (numeratorError denominatorError floor : Q')
    (hdenominatorLeft : (0 : Q') < denominatorLeft)
    (hdenominatorRight : (0 : Q') < denominatorRight)
    (hfloor : (0 : Q') < floor)
    (hnumeratorRight0 : (0 : Q') <= numeratorRight)
    (hnumeratorRightLe : numeratorRight <= denominatorRight)
    (hnumerator : numeratorLeft <= numeratorRight + numeratorError)
    (hdenominator : denominatorRight <= denominatorLeft + denominatorError)
    (hnumeratorError0 : (0 : Q') <= numeratorError)
    (hdenominatorError0 : (0 : Q') <= denominatorError)
    (hfloorLeft : floor <= denominatorLeft) :
    Q'.divPos numeratorLeft denominatorLeft hdenominatorLeft <=
      Q'.divPos numeratorRight denominatorRight hdenominatorRight +
        Q'.divPos (numeratorError + denominatorError) floor hfloor := by
  let rightRatio :=
    Q'.divPos numeratorRight denominatorRight hdenominatorRight
  let errorRatio :=
    Q'.divPos (numeratorError + denominatorError) floor hfloor
  have hrightRatio0 : (0 : Q') <= rightRatio := by
    unfold rightRatio Q'.divPos
    exact Q'.mul_nonneg _ _ hnumeratorRight0
      (Q'.le_of_lt
        (Q'.recipPos_pos denominatorRight hdenominatorRight))
  have hrightRatioLeOne : rightRatio <= (1 : Q') := by
    apply Q'.divPos_le_of_le_mul
    exact Q'.le_trans' _ denominatorRight _ hnumeratorRightLe
      (Q'.ge_of_eqv (Q'.one_mul_eqv denominatorRight))
  have herrorSum0 :
      (0 : Q') <= numeratorError + denominatorError :=
    Q'.zero_le_add _ _ hnumeratorError0 hdenominatorError0
  have herrorRatio0 : (0 : Q') <= errorRatio := by
    unfold errorRatio Q'.divPos
    exact Q'.mul_nonneg _ _ herrorSum0
      (Q'.le_of_lt (Q'.recipPos_pos floor hfloor))
  have hrightDenominator :
      numeratorRight <=
        rightRatio * denominatorRight :=
    Q'.ge_of_eqv
      (Q'.divPos_mul_eqv
        numeratorRight denominatorRight hdenominatorRight)
  have hratioDenominator :
      rightRatio * denominatorRight <=
        rightRatio * (denominatorLeft + denominatorError) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      hdenominator hrightRatio0
  have hratioError :
      rightRatio * denominatorError <= denominatorError := by
    refine Q'.le_trans' _ ((1 : Q') * denominatorError) _
      (Q'.mul_le_mul_of_nonneg_right _ _ denominatorError
        hrightRatioLeOne hdenominatorError0) ?_
    exact Q'.le_of_eqv (Q'.one_mul_eqv denominatorError)
  have hrightExpanded :
      numeratorRight <=
        rightRatio * denominatorLeft + denominatorError := by
    refine Q'.le_trans' _ _ _ hrightDenominator ?_
    refine Q'.le_trans' _ _ _ hratioDenominator ?_
    refine Q'.le_trans' _
      (rightRatio * denominatorLeft +
        rightRatio * denominatorError) _
      (Q'.le_of_eqv
        (Q'.mul_add_eqv rightRatio denominatorLeft denominatorError)) ?_
    exact Q'.add_le_add_left _ _ _ hratioError
  have herrorFloor :
      numeratorError + denominatorError <=
        errorRatio * floor :=
    Q'.ge_of_eqv
      (Q'.divPos_mul_eqv
        (numeratorError + denominatorError) floor hfloor)
  have herrorFloorToLeft :
      errorRatio * floor <=
        errorRatio * denominatorLeft :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hfloorLeft herrorRatio0
  have herrorToLeft :
      numeratorError + denominatorError <=
        errorRatio * denominatorLeft :=
    Q'.le_trans' _ _ _ herrorFloor herrorFloorToLeft
  have hnumeratorCombined :
      numeratorLeft <=
        rightRatio * denominatorLeft +
          errorRatio * denominatorLeft := by
    refine Q'.le_trans' _ _ _ hnumerator ?_
    refine Q'.le_trans' _
      (rightRatio * denominatorLeft +
        denominatorError + numeratorError) _
      (Q'.add_le_add_right _ _ numeratorError hrightExpanded) ?_
    refine Q'.le_trans' _
      (rightRatio * denominatorLeft +
        (numeratorError + denominatorError)) _
      (Q'.le_of_eqv ?_) ?_
    · exact Q'.eqv_trans _
        (rightRatio * denominatorLeft +
          (denominatorError + numeratorError)) _
        (Q'.add_assoc_eqv
          (rightRatio * denominatorLeft)
          denominatorError numeratorError)
        (Q'.add_eqv_congr_left
          (rightRatio * denominatorLeft)
          (denominatorError + numeratorError)
          (numeratorError + denominatorError)
          (Q'.add_comm_eqv denominatorError numeratorError))
    · exact Q'.add_le_add_left _ _ _ herrorToLeft
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _ hnumeratorCombined
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.add_mul_eqv rightRatio errorRatio denominatorLeft)))

/-- Quantitative ratio stability without field tactics or cancellation.
Two nonnegative numerators bounded by their positive denominators inherit the
sum of the numerator and denominator errors, divided by a common positive
denominator floor. -/
theorem divPos_conditioning_abs_sub_le
    (numeratorLeft numeratorRight denominatorLeft denominatorRight : Q')
    (numeratorError denominatorError floor : Q')
    (hdenominatorLeft : (0 : Q') < denominatorLeft)
    (hdenominatorRight : (0 : Q') < denominatorRight)
    (hfloor : (0 : Q') < floor)
    (hnumeratorLeft0 : (0 : Q') <= numeratorLeft)
    (hnumeratorRight0 : (0 : Q') <= numeratorRight)
    (hnumeratorLeftLe : numeratorLeft <= denominatorLeft)
    (hnumeratorRightLe : numeratorRight <= denominatorRight)
    (hnumeratorForward :
      numeratorLeft <= numeratorRight + numeratorError)
    (hnumeratorBackward :
      numeratorRight <= numeratorLeft + numeratorError)
    (hdenominatorForward :
      denominatorLeft <= denominatorRight + denominatorError)
    (hdenominatorBackward :
      denominatorRight <= denominatorLeft + denominatorError)
    (hnumeratorError0 : (0 : Q') <= numeratorError)
    (hdenominatorError0 : (0 : Q') <= denominatorError)
    (hfloorLeft : floor <= denominatorLeft)
    (hfloorRight : floor <= denominatorRight) :
    Q'.abs
        (Q'.divPos numeratorLeft denominatorLeft hdenominatorLeft +
          -Q'.divPos numeratorRight denominatorRight hdenominatorRight) <=
      Q'.divPos (numeratorError + denominatorError) floor hfloor := by
  apply CReal.abs_sub_le_of_bounds
  · exact divPos_one_sided_conditioning_stability
      numeratorLeft numeratorRight denominatorLeft denominatorRight
      numeratorError denominatorError floor
      hdenominatorLeft hdenominatorRight hfloor
      hnumeratorRight0 hnumeratorRightLe hnumeratorForward
      hdenominatorBackward hnumeratorError0 hdenominatorError0 hfloorLeft
  · exact divPos_one_sided_conditioning_stability
      numeratorRight numeratorLeft denominatorRight denominatorLeft
      numeratorError denominatorError floor
      hdenominatorRight hdenominatorLeft hfloor
      hnumeratorLeft0 hnumeratorLeftLe hnumeratorBackward
      hdenominatorForward hnumeratorError0 hdenominatorError0 hfloorRight

/-! ## Axiom audit -/

#print axioms centralOldRowCutoffDifferenceL1
#print axioms centralOldRowCutoffDifferenceL1_le
#print axioms divPos_conditioning_abs_sub_le

end YMGap.Continuum.BF4PhysicalCutoffConditionalCoreReduction
