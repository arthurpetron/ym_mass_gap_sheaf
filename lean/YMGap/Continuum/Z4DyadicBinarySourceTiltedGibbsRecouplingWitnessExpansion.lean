/-
# Recoupling-witness expansion of the localized tilted Gibbs weight

The localized binary-source Gibbs weight contains two natural-number
factors: the lowering multiplicity on faces where the two fine sources agree
and the lowering multiplicity on their finite disagreement carrier.  The
preceding witness theorem turns either product into a dependent word of
supported SU(2) pair channels.

Here the two words are kept separate and then paired.  This separation is
load-bearing for the next geometric step: the disagreement word belongs to
the component that will be peeled, while the agreement word belongs to the
terminal exterior.  The full localized raw weight is exactly a constant
physical weight summed over this duplicate-free witness-pair carrier.

Constructive contract: literal finite lists, structural cardinality, and
exact rational setoid algebra only; no classical choice, proof hole, trusted
external computation, computability escape, heartbeat increase, or new
axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourLoweringWitnessCarrier

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRecouplingWitnessExpansion

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSupportSwapResponse
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSpinFourLoweringWitnessCarrier

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exterior and component witness words -/

/-- Supported lowering choices on faces where the two fine packet totals
agree.  These choices form the common exterior word. -/
def finePacketCommonExteriorLoweringWitnessCarrier
    (S : SlabScalePair) (first second targetState : EdgeLabelling) :
    List (List PairChannelState) :=
  spinFourLoweringWitnessCarrier
    (wholeSlabFinePacketTotalLabelling S first) targetState
    (finePacketTotalAgreementCoarseFaces S first second)

/-- Supported lowering choices on the packet-total disagreement faces of one
selected source. -/
def finePacketDisagreementLoweringWitnessCarrier
    (S : SlabScalePair) (source first second targetState : EdgeLabelling) :
    List (List PairChannelState) :=
  spinFourLoweringWitnessCarrier
    (wholeSlabFinePacketTotalLabelling S source) targetState
    (finePacketTotalDisagreementCoarseFaces S first second)

/-- The common-exterior witness count is exactly its existing multiplicity
factor. -/
theorem finePacketCommonExteriorLoweringWitnessCarrier_length
    (S : SlabScalePair) (first second targetState : EdgeLabelling) :
    (finePacketCommonExteriorLoweringWitnessCarrier
      S first second targetState).length =
        finePacketCommonExteriorMultiplicityProduct
          S first second targetState := by
  unfold finePacketCommonExteriorLoweringWitnessCarrier
    finePacketCommonExteriorMultiplicityProduct
  exact spinFourLoweringWitnessCarrier_length _ _ _

/-- The disagreement witness count is exactly its existing local
multiplicity factor. -/
theorem finePacketDisagreementLoweringWitnessCarrier_length
    (S : SlabScalePair) (source first second targetState : EdgeLabelling) :
    (finePacketDisagreementLoweringWitnessCarrier
      S source first second targetState).length =
        finePacketDisagreementMultiplicityProduct
          S source first second targetState := by
  unfold finePacketDisagreementLoweringWitnessCarrier
    finePacketDisagreementMultiplicityProduct
  exact spinFourLoweringWitnessCarrier_length _ _ _

/-- Both witness lists are duplicate-free. -/
theorem finePacketCommonExteriorLoweringWitnessCarrier_nodup
    (S : SlabScalePair) (first second targetState : EdgeLabelling) :
    (finePacketCommonExteriorLoweringWitnessCarrier
      S first second targetState).Nodup := by
  unfold finePacketCommonExteriorLoweringWitnessCarrier
  exact spinFourLoweringWitnessCarrier_nodup _ _ _

theorem finePacketDisagreementLoweringWitnessCarrier_nodup
    (S : SlabScalePair) (source first second targetState : EdgeLabelling) :
    (finePacketDisagreementLoweringWitnessCarrier
      S source first second targetState).Nodup := by
  unfold finePacketDisagreementLoweringWitnessCarrier
  exact spinFourLoweringWitnessCarrier_nodup _ _ _

/-! ## 2. The separated witness pair -/

/-- One common-exterior word paired with one connected-disagreement word. -/
abbrev FinePacketLoweringWitnessPair :=
  List PairChannelState × List PairChannelState

/-- The complete explicit recoupling carrier of a localized tilted Gibbs
term. -/
def finePacketLocalizedLoweringWitnessPairCarrier
    (S : SlabScalePair) (source first second targetState : EdgeLabelling) :
    List FinePacketLoweringWitnessPair :=
  cartesian
    (finePacketCommonExteriorLoweringWitnessCarrier
      S first second targetState)
    (finePacketDisagreementLoweringWitnessCarrier
      S source first second targetState)

private theorem cartesian_length_local
    {A B : Type} (left : List A) (right : List B) :
    (cartesian left right).length = left.length * right.length := by
  induction left with
  | nil => simp [cartesian]
  | cons head tail ih =>
      unfold cartesian at ih ⊢
      simp only [List.flatMap_cons, List.length_append,
        List.length_map, List.length_cons]
      rw [ih, Nat.succ_mul]
      exact Nat.add_comm _ _

/-- The paired carrier has exactly the product of the exterior and
disagreement multiplicities. -/
theorem finePacketLocalizedLoweringWitnessPairCarrier_length
    (S : SlabScalePair) (source first second targetState : EdgeLabelling) :
    (finePacketLocalizedLoweringWitnessPairCarrier
      S source first second targetState).length =
      finePacketCommonExteriorMultiplicityProduct
          S first second targetState *
        finePacketDisagreementMultiplicityProduct
          S source first second targetState := by
  unfold finePacketLocalizedLoweringWitnessPairCarrier
  rw [cartesian_length_local,
    finePacketCommonExteriorLoweringWitnessCarrier_length,
    finePacketDisagreementLoweringWitnessCarrier_length]

/-- Pair membership retains the semantic distinction between exterior and
component lowering paths. -/
theorem mem_finePacketLocalizedLoweringWitnessPairCarrier_iff
    (S : SlabScalePair) (source first second targetState : EdgeLabelling)
    (pair : FinePacketLoweringWitnessPair) :
    pair ∈ finePacketLocalizedLoweringWitnessPairCarrier
        S source first second targetState ↔
      SpinFourLoweringWitnessFits
          (wholeSlabFinePacketTotalLabelling S first) targetState
          (finePacketTotalAgreementCoarseFaces S first second) pair.1 ∧
        SpinFourLoweringWitnessFits
          (wholeSlabFinePacketTotalLabelling S source) targetState
          (finePacketTotalDisagreementCoarseFaces S first second) pair.2 := by
  unfold finePacketLocalizedLoweringWitnessPairCarrier
  rw [mem_cartesian_iff]
  exact and_congr
    (mem_spinFourLoweringWitnessCarrier_iff _ _ _ _)
    (mem_spinFourLoweringWitnessCarrier_iff _ _ _ _)

/-- The paired recoupling carrier has no duplicate witness. -/
theorem finePacketLocalizedLoweringWitnessPairCarrier_nodup
    (S : SlabScalePair) (source first second targetState : EdgeLabelling) :
    (finePacketLocalizedLoweringWitnessPairCarrier
      S source first second targetState).Nodup := by
  unfold finePacketLocalizedLoweringWitnessPairCarrier
  exact cartesian_nodup _ _
    (finePacketCommonExteriorLoweringWitnessCarrier_nodup
      S first second targetState)
    (finePacketDisagreementLoweringWitnessCarrier_nodup
      S source first second targetState)

/-! ## 3. Exact expansion of the localized Gibbs term -/

private theorem listQSum_const_local {A : Type} (constant : Q') :
    ∀ items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _head :: tail => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat tail.length * constant) _ ?_ ?_
      · exact Q'.add_eqv_congr_left constant _ _
          (listQSum_const_local constant tail)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv _ constant)

/-- Both natural multiplicities in the localized raw weight are exactly
replaced by a finite sum of literal SU(2) recoupling witnesses. -/
theorem finePacketLocalizedTiltedGibbsRawWeight_eqv_loweringWitnessSum
    (S : SlabScalePair) (source first second targetState : EdgeLabelling) :
    finePacketLocalizedTiltedGibbsRawWeight
        S source first second targetState ≈
      listQSum (fun _pair => S.coarse.physicalTerm targetState)
        (finePacketLocalizedLoweringWitnessPairCarrier
          S source first second targetState) := by
  let exterior := finePacketCommonExteriorMultiplicityProduct
    S first second targetState
  let component := finePacketDisagreementMultiplicityProduct
    S source first second targetState
  let carrier := finePacketLocalizedLoweringWitnessPairCarrier
    S source first second targetState
  have hlength : carrier.length = exterior * component :=
    finePacketLocalizedLoweringWitnessPairCarrier_length
      S source first second targetState
  unfold finePacketLocalizedTiltedGibbsRawWeight
  change Q'.ofNat exterior *
      (Q'.ofNat component * S.coarse.physicalTerm targetState) ≈ _
  refine Q'.eqv_trans _
    ((Q'.ofNat exterior * Q'.ofNat component) *
      S.coarse.physicalTerm targetState) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (exterior * component) *
      S.coarse.physicalTerm targetState) _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (ofNat_mul_eqv exterior component))) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat carrier.length * S.coarse.physicalTerm targetState) _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_of_eq (congrArg Q'.ofNat hlength.symm))) ?_
  exact Q'.eqv_symm
    (listQSum_const_local (S.coarse.physicalTerm targetState) carrier)

#print axioms finePacketCommonExteriorLoweringWitnessCarrier_length
#print axioms finePacketDisagreementLoweringWitnessCarrier_length
#print axioms finePacketCommonExteriorLoweringWitnessCarrier_nodup
#print axioms finePacketDisagreementLoweringWitnessCarrier_nodup
#print axioms finePacketLocalizedLoweringWitnessPairCarrier_length
#print axioms mem_finePacketLocalizedLoweringWitnessPairCarrier_iff
#print axioms finePacketLocalizedLoweringWitnessPairCarrier_nodup
#print axioms finePacketLocalizedTiltedGibbsRawWeight_eqv_loweringWitnessSum

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRecouplingWitnessExpansion
