/-
# Active carrier of the localized tilted-row response determinant

The antisymmetric response formula has two independent exact cancellation
tests.  A pair contributes only when its Boolean observable values differ and
when the two packet-local multiplicity products have nonzero determinant.
This file filters the complete square carrier by those two decidable tests.

For every surviving pair it also returns, as constructive data, a coarse face
in the source packet-disagreement carrier on which the two coarse target
states differ.  Thus a surviving response term has one observable endpoint
and one source-component endpoint before any activity estimate is applied.

This remains a finite support theorem.  It does not connect those endpoints
by a polymer, estimate their total weight, prove volume-uniform smallness,
construct a continuum measure, or prove a mass gap.

Constructive contract: finite Boolean filtering and explicit sigma witnesses
only; no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseDeterminant
import YMGap.Continuum.Z4DyadicBinarySourceSupportSwapPacketComponent

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseActiveCarrier

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseDeterminant
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSupportSwapResponse
open YMGap.Continuum.Z4DyadicSpinFourLoweringKernel
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

private theorem sub_eqv_zero_of_eqv_local {left right : Q'}
    (heq : left ≈ right) : left - right ≈ 0 := by
  exact Q'.eqv_trans _ (right + -right) _
    (Q'.add_eqv_congr' heq (Q'.eqv_refl _))
    (Q'.add_neg_self_eqv right)

private theorem mul_eqv_zero_of_left_local
    (left right : Q') (hleft : left ≈ 0) :
    left * right ≈ 0 := by
  refine Q'.eqv_trans _ (0 * right) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hleft
  · exact Q'.zero_mul_eqv right

private theorem mul_eqv_zero_of_right_local
    (left right : Q') (hright : right ≈ 0) :
    left * right ≈ 0 := by
  refine Q'.eqv_trans _ (left * 0) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _ hright
  · exact Q'.mul_zero_eqv left

private theorem listQSum_eq_filter_of_zero_local
    {A : Type} (value : A → Q') (test : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items → test item = false → value item ≈ 0) →
      listQSum value items ≈ listQSum value (items.filter test)
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      have htail :
          ∀ item, item ∈ tail → test item = false → value item ≈ 0 := by
        intro item hitem htest
        exact hzero item (List.mem_cons_of_mem head hitem) htest
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _
            (0 + listQSum value (tail.filter test)) _
            (Q'.add_eqv_congr'
              (hzero head List.mem_cons_self htest)
              (listQSum_eq_filter_of_zero_local value test tail htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero_local value test tail htail)

/-! ## 1. Two decidable cancellation tests -/

/-- Forward product in the local multiplicity determinant. -/
def finePacketForwardDisagreementMultiplicityProduct
    (S : SlabScalePair) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Nat :=
  finePacketDisagreementMultiplicityProduct
      S first first second pair.1 *
    finePacketDisagreementMultiplicityProduct
      S second first second pair.2

/-- Reverse product in the local multiplicity determinant. -/
def finePacketReverseDisagreementMultiplicityProduct
    (S : SlabScalePair) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Nat :=
  finePacketDisagreementMultiplicityProduct
      S second first second pair.1 *
    finePacketDisagreementMultiplicityProduct
      S first first second pair.2

/-- A pair survives exactly when both its local source determinant and its
observable difference are nonzero. -/
def finePacketLocalizedResponsePairActiveB
    (S : SlabScalePair) (first second : EdgeLabelling)
    (event : EdgeLabelling → Bool)
    (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  decide
      (finePacketForwardDisagreementMultiplicityProduct
          S first second pair ≠
        finePacketReverseDisagreementMultiplicityProduct
          S first second pair) &&
    decide (event pair.1 ≠ event pair.2)

/-- The exact finite carrier remaining after both pointwise cancellations. -/
def finePacketLocalizedResponseActivePairs
    (S : SlabScalePair) (first second : EdgeLabelling)
    (event : EdgeLabelling → Bool) :
    List (EdgeLabelling × EdgeLabelling) :=
  (cartesian S.coarse.physicalLabellings
      S.coarse.physicalLabellings).filter
    (finePacketLocalizedResponsePairActiveB S first second event)

private theorem disagreementTiltProducts_eqv_of_nat_eq
    (S : SlabScalePair) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling)
    (heq : finePacketForwardDisagreementMultiplicityProduct
        S first second pair =
      finePacketReverseDisagreementMultiplicityProduct
        S first second pair) :
    finePacketDisagreementTilt S first first second pair.1 *
          finePacketDisagreementTilt S second first second pair.2 ≈
      finePacketDisagreementTilt S second first second pair.1 *
          finePacketDisagreementTilt S first first second pair.2 := by
  refine Q'.eqv_trans _
    (Q'.ofNat
      (finePacketForwardDisagreementMultiplicityProduct
        S first second pair)) _ ?_ ?_
  · unfold finePacketDisagreementTilt
      finePacketForwardDisagreementMultiplicityProduct
    exact Q'.eqv_symm (ofNat_mul_eqv _ _)
  rw [heq]
  unfold finePacketDisagreementTilt
    finePacketReverseDisagreementMultiplicityProduct
  exact ofNat_mul_eqv _ _

/-- Failure of either active test makes the completely factored pair term
exactly zero. -/
theorem finePacketLocalizedAntisymmetricResponsePairTerm_eqv_zero_of_inactive
    (S : SlabScalePair) (first second : EdgeLabelling)
    (event : EdgeLabelling → Bool)
    (pair : EdgeLabelling × EdgeLabelling)
    (hinactive : finePacketLocalizedResponsePairActiveB
      S first second event pair = false) :
    finePacketLocalizedAntisymmetricResponsePairTerm
        S first second event pair ≈ 0 := by
  by_cases hskew :
      finePacketForwardDisagreementMultiplicityProduct
          S first second pair =
        finePacketReverseDisagreementMultiplicityProduct
          S first second pair
  · have htilts := disagreementTiltProducts_eqv_of_nat_eq
      S first second pair hskew
    have hdet :
        finePacketDisagreementTilt S first first second pair.1 *
              finePacketDisagreementTilt S second first second pair.2 -
            finePacketDisagreementTilt S second first second pair.1 *
              finePacketDisagreementTilt S first first second pair.2 ≈
          0 := sub_eqv_zero_of_eqv_local htilts
    unfold finePacketLocalizedAntisymmetricResponsePairTerm
    exact mul_eqv_zero_of_right_local _ _
      (mul_eqv_zero_of_left_local _ _ hdet)
  · by_cases hevent : event pair.1 = event pair.2
    · have hindicator :
          booleanEventIndicator event pair.1 -
              booleanEventIndicator event pair.2 ≈ 0 := by
        unfold booleanEventIndicator
        rw [hevent]
        exact sub_eqv_zero_of_eqv_local (Q'.eqv_refl _)
      unfold finePacketLocalizedAntisymmetricResponsePairTerm
      exact mul_eqv_zero_of_right_local _ _
        (mul_eqv_zero_of_right_local _ _ hindicator)
    · have hactive : finePacketLocalizedResponsePairActiveB
          S first second event pair = true := by
        unfold finePacketLocalizedResponsePairActiveB
        simp [hskew, hevent]
      rw [hactive] at hinactive
      exact Bool.noConfusion hinactive

/-- The complete factored pair sum can be pruned to the active carrier with
no inequality and no loss. -/
theorem localizedAntisymmetricResponsePairSum_eqv_activeCarrier
    (S : SlabScalePair) (first second : EdgeLabelling)
    (event : EdgeLabelling → Bool) :
    listQSum
        (finePacketLocalizedAntisymmetricResponsePairTerm
          S first second event)
        (cartesian S.coarse.physicalLabellings
          S.coarse.physicalLabellings) ≈
      listQSum
        (finePacketLocalizedAntisymmetricResponsePairTerm
          S first second event)
        (finePacketLocalizedResponseActivePairs
          S first second event) := by
  unfold finePacketLocalizedResponseActivePairs
  exact listQSum_eq_filter_of_zero_local
    (finePacketLocalizedAntisymmetricResponsePairTerm
      S first second event)
    (finePacketLocalizedResponsePairActiveB S first second event)
    (cartesian S.coarse.physicalLabellings
      S.coarse.physicalLabellings)
    (fun pair _ hinactive =>
      finePacketLocalizedAntisymmetricResponsePairTerm_eqv_zero_of_inactive
        S first second event pair hinactive)

/-- Twice the actual raw response cross is supported exactly on the active
pair carrier. -/
theorem two_mul_positivePhysicalTiltedGibbsRawCross_eqv_activePairSum
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (event : EdgeLabelling → Bool) :
    (2 : Q') *
        positivePhysicalTiltedGibbsTwoRowRawCrossNumerator
          S first second event ≈
      listQSum
        (finePacketLocalizedAntisymmetricResponsePairTerm
          S first.1 second.1 event)
        (finePacketLocalizedResponseActivePairs
          S first.1 second.1 event) := by
  exact Q'.eqv_trans _ _ _
    (two_mul_positivePhysicalTiltedGibbsRawCross_eqv_localizedPairSum
      S hfineCutoff first second event)
    (localizedAntisymmetricResponsePairSum_eqv_activeCarrier
      S first.1 second.1 event)

/-! ## 2. A surviving pair returns a changed carrier face -/

/-- Two target states agree on the source packet-disagreement carrier. -/
def coarseTargetsAgreeOnFinePacketDisagreementFaces
    (S : SlabScalePair) (first second x y : EdgeLabelling) : Prop :=
  ∀ faceId,
    faceId ∈ finePacketTotalDisagreementCoarseFaces S first second →
      x faceId = y faceId

/-- Agreement of target spins on the local carrier makes every
source-specific disagreement multiplicity product equal. -/
theorem finePacketDisagreementMultiplicityProduct_eq_of_targetsAgree
    (S : SlabScalePair) (source first second x y : EdgeLabelling)
    (hagree : coarseTargetsAgreeOnFinePacketDisagreementFaces
      S first second x y) :
    finePacketDisagreementMultiplicityProduct S source first second x =
      finePacketDisagreementMultiplicityProduct S source first second y := by
  unfold finePacketDisagreementMultiplicityProduct
    spinFourLoweringMultiplicityProductOn
  apply natListProduct_congr
  intro faceId hface
  rw [hagree faceId hface]

/-- If the two target states agree throughout the source-local carrier, the
local multiplicity determinant vanishes as a natural-number identity. -/
theorem finePacketDisagreementProducts_eq_of_targetsAgree
    (S : SlabScalePair) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling)
    (hagree : coarseTargetsAgreeOnFinePacketDisagreementFaces
      S first second pair.1 pair.2) :
    finePacketForwardDisagreementMultiplicityProduct
        S first second pair =
      finePacketReverseDisagreementMultiplicityProduct
        S first second pair := by
  have hfirst :=
    finePacketDisagreementMultiplicityProduct_eq_of_targetsAgree
      S first first second pair.1 pair.2 hagree
  have hsecond :=
    finePacketDisagreementMultiplicityProduct_eq_of_targetsAgree
      S second first second pair.1 pair.2 hagree
  unfold finePacketForwardDisagreementMultiplicityProduct
    finePacketReverseDisagreementMultiplicityProduct
  rw [hfirst, hsecond]
  exact Nat.mul_comm _ _

/-- Constructively search a finite list for the first point where two
natural-valued functions disagree. -/
def finiteTargetDisagreementWitness
    (left right : Nat → Nat) :
    ∀ faces : List Nat,
      (¬ ∀ faceId, faceId ∈ faces → left faceId = right faceId) →
      { faceId : Nat //
        faceId ∈ faces ∧ left faceId ≠ right faceId }
  | [], hnot => False.elim
      (hnot (fun faceId hmem =>
        False.elim (List.not_mem_nil hmem)))
  | head :: tail, hnot => by
      by_cases heq : left head = right head
      · let witness := finiteTargetDisagreementWitness left right tail
          (fun htail =>
            hnot (fun faceId hmem => by
              rcases List.mem_cons.mp hmem with hhead | htailMem
              · rw [hhead]
                exact heq
              · exact htail faceId htailMem))
        exact ⟨witness.1,
          List.mem_cons_of_mem head witness.2.1, witness.2.2⟩
      · exact ⟨head, List.mem_cons_self, heq⟩

/-- Every active response pair returns a concrete source-disagreement face
on which its two coarse target states differ. -/
def activePairTargetDisagreementWitness
    (S : SlabScalePair) (first second : EdgeLabelling)
    (event : EdgeLabelling → Bool)
    (pair : EdgeLabelling × EdgeLabelling)
    (hactive : finePacketLocalizedResponsePairActiveB
      S first second event pair = true) :
    { faceId : Nat //
      faceId ∈ finePacketTotalDisagreementCoarseFaces S first second ∧
        pair.1 faceId ≠ pair.2 faceId } := by
  have hparts := (Bool.and_eq_true _ _).mp hactive
  have hskew :
      finePacketForwardDisagreementMultiplicityProduct
          S first second pair ≠
        finePacketReverseDisagreementMultiplicityProduct
          S first second pair := of_decide_eq_true hparts.1
  apply finiteTargetDisagreementWitness pair.1 pair.2
    (finePacketTotalDisagreementCoarseFaces S first second)
  intro hagree
  exact hskew
    (finePacketDisagreementProducts_eq_of_targetsAgree
      S first second pair hagree)

/-- The second active test is also returned explicitly for later observable
endpoint specialization. -/
theorem activePair_event_ne
    (S : SlabScalePair) (first second : EdgeLabelling)
    (event : EdgeLabelling → Bool)
    (pair : EdgeLabelling × EdgeLabelling)
    (hactive : finePacketLocalizedResponsePairActiveB
      S first second event pair = true) :
    event pair.1 ≠ event pair.2 := by
  exact of_decide_eq_true ((Bool.and_eq_true _ _).mp hactive).2

/-! ## 3. Axiom audit -/

#print axioms finePacketLocalizedResponsePairActiveB
#print axioms finePacketLocalizedAntisymmetricResponsePairTerm_eqv_zero_of_inactive
#print axioms localizedAntisymmetricResponsePairSum_eqv_activeCarrier
#print axioms two_mul_positivePhysicalTiltedGibbsRawCross_eqv_activePairSum
#print axioms coarseTargetsAgreeOnFinePacketDisagreementFaces
#print axioms finePacketDisagreementMultiplicityProduct_eq_of_targetsAgree
#print axioms finePacketDisagreementProducts_eq_of_targetsAgree
#print axioms finiteTargetDisagreementWitness
#print axioms activePairTargetDisagreementWitness
#print axioms activePair_event_ne

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseActiveCarrier
