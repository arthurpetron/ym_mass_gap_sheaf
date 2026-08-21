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

/-! ## Axiom audit -/

#print axioms centralOldRowCutoffDifferenceL1
#print axioms centralOldRowCutoffDifferenceL1_le

end YMGap.Continuum.BF4PhysicalCutoffConditionalCoreReduction
