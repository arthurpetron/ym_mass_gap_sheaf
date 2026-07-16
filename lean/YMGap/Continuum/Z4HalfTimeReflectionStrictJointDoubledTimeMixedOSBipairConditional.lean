/-
# Two-code support fibers as corrected-slab conditional events

The oriented two-code support entry is identified with one literal physical
conditional event.  The lower restriction is read through the source code;
the reflected upper restriction is read through the independently supplied
target code.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSFiniteEntries

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBipairConditional

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCoefficientZeroExtension
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalFamilyFaceSupportDecoder
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLocalPairConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientPartition
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBipushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSFiniteEntries
open YMGap.Continuum.Z4HalfTimeReflectionSupportPairConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_mask_eq_filter_local {A : Type}
    (weight : A → Q') (event : A → Bool) : ∀ source : List A,
    listQSum (fun item => if event item then weight item else 0) source ≈
      listQSum weight (source.filter event)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases hevent : event head with
      | false =>
          simp only [hevent, Bool.false_eq_true, if_false,
            List.filter_cons, listQSum]
          exact Q'.eqv_trans _
            (0 + listQSum weight (tail.filter event)) _
            (Q'.add_eqv_congr' (Q'.eqv_refl 0)
              (listQSum_mask_eq_filter_local weight event tail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [hevent, if_true, List.filter_cons, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_mask_eq_filter_local weight event tail)

private theorem bipairMask_eqv_pointProduct
    {Target : Type} [DecidableEq Target]
    (leftTarget leftCode rightTarget rightCode : Target)
    (weight : Q') :
    (if decide ((leftTarget, rightTarget) = (leftCode, rightCode))
      then weight else 0) ≈
      ((if leftTarget = leftCode then 1 else 0) *
        (if rightTarget = rightCode then 1 else 0)) * weight := by
  by_cases hleft : leftTarget = leftCode
  · by_cases hright : rightTarget = rightCode
    · have hpair : (leftTarget, rightTarget) =
          (leftCode, rightCode) := Prod.ext hleft hright
      rw [if_pos (decide_eq_true hpair), if_pos hleft, if_pos hright]
      apply Q'.eqv_symm
      refine Q'.eqv_trans _ ((1 : Q') * weight) _ ?_
        (Q'.one_mul_eqv weight)
      exact Q'.mul_eqv_congr_right _ _ weight (Q'.one_mul_eqv 1)
    · have hpair : (leftTarget, rightTarget) ≠
          (leftCode, rightCode) := fun heq =>
        hright (congrArg Prod.snd heq)
      rw [decide_eq_false hpair, if_pos hleft, if_neg hright]
      apply Q'.eqv_symm
      refine Q'.eqv_trans _ ((0 : Q') * weight) _ ?_
        (Q'.zero_mul_eqv weight)
      exact Q'.mul_eqv_congr_right _ _ weight (Q'.one_mul_eqv 0)
  · have hpair : (leftTarget, rightTarget) ≠
        (leftCode, rightCode) := fun heq =>
      hleft (congrArg Prod.fst heq)
    rw [decide_eq_false hpair, if_neg hleft]
    apply Q'.eqv_symm
    refine Q'.eqv_trans _ ((0 : Q') * weight) _ ?_
      (Q'.zero_mul_eqv weight)
    exact Q'.mul_eqv_congr_right _ _ weight (Q'.zero_mul_eqv _)

def centralSupportBipairReflectedKernel
    (coupling : Q') (cutoff half : Nat)
    (leftCode rightCode : List Nat → List Bool)
    (left right : List Bool) : Q' :=
  finiteJointKernelBipushforward
    (centralHalfSupportSpace half)
    (centralSupportReflectedKernel coupling cutoff half)
    leftCode rightCode left right

theorem centralSupportBipairReflectedKernel_eq_directFiber
    (coupling : Q') (cutoff half : Nat)
    (leftCode rightCode : List Nat → List Bool)
    (left right : List Bool) :
    centralSupportBipairReflectedKernel
        coupling cutoff half leftCode rightCode left right ≈
      fiberWeight (centralHalfStatePairs cutoff half)
        (fun pair => centralPhysicalReflectedKernel
          coupling cutoff half pair.1 pair.2)
        (fun pair =>
          (leftCode (centralHalfSupportCode half pair.1),
            rightCode (centralHalfSupportCode half pair.2)))
        (left, right) := by
  unfold centralSupportBipairReflectedKernel
    finiteJointKernelBipushforward centralSupportReflectedKernel
    centralHalfSupportPairCode
  exact fiberWeight_comp_eqv
    (centralHalfStatePairs cutoff half)
    (fun pair => centralPhysicalReflectedKernel
      coupling cutoff half pair.1 pair.2)
    (fun pair =>
      (centralHalfSupportCode half pair.1,
        centralHalfSupportCode half pair.2))
    (cartesian (centralHalfSupportSpace half)
      (centralHalfSupportSpace half))
    (centralHalfSupportPairs_nodup half)
    (centralHalfSupportPairCode_mem cutoff half)
    (fun pair => (leftCode pair.1, rightCode pair.2))
    (left, right)

def centralBipairSupportPointCoefficient
    (half : Nat) (code : List Nat → List Bool)
    (target : List Bool) (state : EdgeLabelling) : Q' :=
  if target = code (centralHalfSupportCode half state) then 1 else 0

theorem centralSupportBipairReflectedKernel_eq_bilinear
    (coupling : Q') (cutoff half : Nat)
    (leftCode rightCode : List Nat → List Bool)
    (left right : List Bool) :
    centralSupportBipairReflectedKernel
        coupling cutoff half leftCode rightCode left right ≈
      centralPhysicalReflectionBilinear coupling cutoff half
        (centralBipairSupportPointCoefficient half leftCode left)
        (centralBipairSupportPointCoefficient half rightCode right) := by
  let pairWeight : EdgeLabelling × EdgeLabelling → Q' := fun pair =>
    centralPhysicalReflectedKernel coupling cutoff half pair.1 pair.2
  let pairCode : EdgeLabelling × EdgeLabelling →
      List Bool × List Bool := fun pair =>
    (leftCode (centralHalfSupportCode half pair.1),
      rightCode (centralHalfSupportCode half pair.2))
  let event : EdgeLabelling × EdgeLabelling → Bool := fun pair =>
    decide ((left, right) = pairCode pair)
  have hdirect := centralSupportBipairReflectedKernel_eq_directFiber
    coupling cutoff half leftCode rightCode left right
  have hmask :
      listQSum pairWeight
          ((centralHalfStatePairs cutoff half).filter event) ≈
        listQSum (fun pair => if event pair then pairWeight pair else 0)
          (centralHalfStatePairs cutoff half) :=
    Q'.eqv_symm
      (listQSum_mask_eq_filter_local pairWeight event
        (centralHalfStatePairs cutoff half))
  have hpointwise :
      listQSum (fun pair => if event pair then pairWeight pair else 0)
          (centralHalfStatePairs cutoff half) ≈
        listQSum (fun pair =>
          (centralBipairSupportPointCoefficient
              half leftCode left pair.1 *
            centralBipairSupportPointCoefficient
              half rightCode right pair.2) * pairWeight pair)
          (centralHalfStatePairs cutoff half) := by
    apply listQSum_congr
    intro pair
    exact bipairMask_eqv_pointProduct
      left (leftCode (centralHalfSupportCode half pair.1))
      right (rightCode (centralHalfSupportCode half pair.2))
      (pairWeight pair)
  have hcartesian :
      listQSum (fun pair =>
          (centralBipairSupportPointCoefficient
              half leftCode left pair.1 *
            centralBipairSupportPointCoefficient
              half rightCode right pair.2) * pairWeight pair)
          (centralHalfStatePairs cutoff half) ≈
        centralPhysicalReflectionBilinear coupling cutoff half
          (centralBipairSupportPointCoefficient half leftCode left)
          (centralBipairSupportPointCoefficient half rightCode right) := by
    unfold centralHalfStatePairs centralPhysicalReflectionBilinear pairWeight
    exact listQSum_cartesian_eq_nested
      (fun pair =>
        (centralBipairSupportPointCoefficient half leftCode left pair.1 *
          centralBipairSupportPointCoefficient half rightCode right pair.2) *
            centralPhysicalReflectedKernel
              coupling cutoff half pair.1 pair.2)
      (centralHalfStates cutoff half) (centralHalfStates cutoff half)
  unfold fiberWeight at hdirect
  exact Q'.eqv_trans _ _ _ hdirect
    (Q'.eqv_trans _ _ _ hmask
      (Q'.eqv_trans _ _ _ hpointwise hcartesian))

def centralLocalSupportBipairFamilyEvent
    (half : Nat) (leftCode rightCode : List Nat → List Bool)
    (left right : List Bool) (family : List (List Nat)) : Bool :=
  decide
    (leftCode (centralFamilyLowerSupportCode half family) = left ∧
      rightCode (centralFamilyReflectedUpperSupportCode half family) = right)

theorem centralLocalSupportBipairFamilyEvent_physical
    (half : Nat) (leftCode rightCode : List Nat → List Bool)
    (left right : List Bool) (physical : EdgeLabelling) :
    centralLocalSupportBipairFamilyEvent half leftCode rightCode left right
        (physicalCanonicalAmbientFamily (centralAmbient half) physical) =
      decide
        (leftCode
              (centralHalfSupportCode half
                (centralLowerRestriction half
                  (ambientToSlabPhysical (centralExtent half) physical))) =
            left ∧
          rightCode
              (centralHalfSupportCode half
                (centralReflectedUpperRestriction half
                  (ambientToSlabPhysical (centralExtent half) physical))) =
            right) := by
  unfold centralLocalSupportBipairFamilyEvent
  rw [centralFamilyLowerSupportCode_physical,
    centralFamilyReflectedUpperSupportCode_physical]

def centralLocalSupportBipairSlabObservable
    (half : Nat) (leftCode rightCode : List Nat → List Bool)
    (left right : List Bool) (physical : EdgeLabelling) : Q' :=
  centralBipairSupportPointCoefficient half leftCode left
      (centralLowerRestriction half physical) *
    centralBipairSupportPointCoefficient half rightCode right
      (centralReflectedUpperRestriction half physical)

private theorem pointProduct_eqv_localIndicator
    {Target : Type} [DecidableEq Target]
    (leftTarget leftCode rightTarget rightCode : Target) :
    (if leftTarget = leftCode then (1 : Q') else 0) *
        (if rightTarget = rightCode then (1 : Q') else 0) ≈
      (if decide (leftCode = leftTarget ∧ rightCode = rightTarget)
        then 1 else 0) := by
  by_cases hleft : leftTarget = leftCode
  · by_cases hright : rightTarget = rightCode
    · have hpair : leftCode = leftTarget ∧ rightCode = rightTarget :=
        ⟨hleft.symm, hright.symm⟩
      rw [if_pos hleft, if_pos hright, if_pos (decide_eq_true hpair)]
      exact Q'.one_mul_eqv 1
    · have hpair : ¬(leftCode = leftTarget ∧ rightCode = rightTarget) :=
        fun h => hright h.2.symm
      rw [if_pos hleft, if_neg hright, decide_eq_false hpair]
      exact Q'.one_mul_eqv 0
  · have hpair : ¬(leftCode = leftTarget ∧ rightCode = rightTarget) :=
      fun h => hleft h.1.symm
    rw [if_neg hleft, decide_eq_false hpair]
    exact Q'.zero_mul_eqv _

theorem centralLocalSupportBipairSlabObservable_eqv_indicator
    (half : Nat) (leftCode rightCode : List Nat → List Bool)
    (left right : List Bool) (physical : EdgeLabelling) :
    centralLocalSupportBipairSlabObservable
        half leftCode rightCode left right physical ≈
      (if decide
          (leftCode
                (centralHalfSupportCode half
                  (centralLowerRestriction half physical)) = left ∧
            rightCode
                (centralHalfSupportCode half
                  (centralReflectedUpperRestriction half physical)) = right)
        then 1 else 0) := by
  unfold centralLocalSupportBipairSlabObservable
    centralBipairSupportPointCoefficient
  exact pointProduct_eqv_localIndicator
    left (leftCode (centralHalfSupportCode half
      (centralLowerRestriction half physical)))
    right (rightCode (centralHalfSupportCode half
      (centralReflectedUpperRestriction half physical)))

theorem centralSupportBipairReflectedKernel_eq_slabWeighted
    (coupling : Q') (cutoff half : Nat)
    (leftCode rightCode : List Nat → List Bool)
    (left right : List Bool) :
    centralSupportBipairReflectedKernel
        coupling cutoff half leftCode rightCode left right ≈
      slabWeightedPhysicalSum coupling cutoff (centralExtent half)
        (centralLocalSupportBipairSlabObservable
          half leftCode rightCode left right) := by
  refine Q'.eqv_trans _ _ _
    (centralSupportBipairReflectedKernel_eq_bilinear
      coupling cutoff half leftCode rightCode left right) ?_
  refine Q'.eqv_trans _ _ _
    (centralPhysicalReflectionBilinear_eq_full coupling cutoff half
      (centralBipairSupportPointCoefficient half leftCode left)
      (centralBipairSupportPointCoefficient half rightCode right)) ?_
  exact Q'.eqv_refl _

private theorem ambientLocalSupportBipairWeightedSum_eq_eventNumerator
    (coupling : Q') (cutoff half : Nat)
    (leftCode rightCode : List Nat → List Bool)
    (left right : List Bool) :
    ambientSlabSupportedWeightedSum coupling cutoff (centralExtent half)
        (centralLocalSupportBipairSlabObservable
          half leftCode rightCode left right) ≈
      parametricKEventNumerator coupling cutoff (centralAmbient half)
        (fun physical =>
          ambientSlabSupportedB (centralExtent half) physical &&
            cutoffOneLiftedFamilyEvent (centralAmbient half)
              (centralLocalSupportBipairFamilyEvent
                half leftCode rightCode left right) physical) := by
  let full := boundedEdgeLabellings cutoff
    (List.range (plaquetteEdgeCount (centralAmbient half)))
  let supported := ambientSlabSupportedLabellings cutoff (centralExtent half)
  let familyEvent := centralLocalSupportBipairFamilyEvent
    half leftCode rightCode left right
  let eventTerm : EdgeLabelling → Q' := fun physical =>
    if cutoffOneLiftedFamilyEvent (centralAmbient half) familyEvent physical
    then parametricKPhysicalTerm coupling cutoff
      (centralAmbient half) physical
    else 0
  have hsupportedTerms :
      ambientSlabSupportedWeightedSum coupling cutoff (centralExtent half)
          (centralLocalSupportBipairSlabObservable
            half leftCode rightCode left right) ≈
        listQSum eventTerm supported := by
    unfold ambientSlabSupportedWeightedSum supported
    apply listQSum_congr_on
    intro physical _
    have hevent : cutoffOneLiftedFamilyEvent (centralAmbient half)
          familyEvent physical =
        decide
          (leftCode
                (centralHalfSupportCode half
                  (centralLowerRestriction half
                    (ambientToSlabPhysical (centralExtent half) physical))) =
              left ∧
            rightCode
                (centralHalfSupportCode half
                  (centralReflectedUpperRestriction half
                    (ambientToSlabPhysical (centralExtent half) physical))) =
              right) := by
      unfold cutoffOneLiftedFamilyEvent familyEvent
      exact centralLocalSupportBipairFamilyEvent_physical
        half leftCode rightCode left right physical
    let pairEvent := decide
      (leftCode
            (centralHalfSupportCode half
              (centralLowerRestriction half
                (ambientToSlabPhysical (centralExtent half) physical))) = left ∧
        rightCode
            (centralHalfSupportCode half
              (centralReflectedUpperRestriction half
                (ambientToSlabPhysical (centralExtent half) physical))) = right)
    have hobservable :=
      centralLocalSupportBipairSlabObservable_eqv_indicator
        half leftCode rightCode left right
        (ambientToSlabPhysical (centralExtent half) physical)
    unfold eventTerm
    rw [hevent]
    refine Q'.eqv_trans _
      ((if pairEvent then 1 else 0) *
        parametricKPhysicalTerm coupling cutoff
          (centralAmbient half) physical) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hobservable
    · change
        ((if pairEvent = true then 1 else 0) *
            parametricKPhysicalTerm coupling cutoff
              (centralAmbient half) physical) ≈
          (if pairEvent = true then
            parametricKPhysicalTerm coupling cutoff
              (centralAmbient half) physical else 0)
      cases pairEvent with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          exact Q'.zero_mul_eqv _
      | true =>
          simp only [if_true]
          exact Q'.one_mul_eqv _
  have hmask := listQSum_mask_eq_filter_local eventTerm
    (ambientSlabSupportedB (centralExtent half)) full
  have hmasked :
      listQSum (fun physical =>
          if ambientSlabSupportedB (centralExtent half) physical then
            eventTerm physical else 0) full ≈
        parametricKEventNumerator coupling cutoff (centralAmbient half)
          (fun physical =>
            ambientSlabSupportedB (centralExtent half) physical &&
              cutoffOneLiftedFamilyEvent (centralAmbient half)
                familyEvent physical) := by
    unfold parametricKEventNumerator parametricKEventTerm eventTerm full
    apply listQSum_congr
    intro physical
    cases hs : ambientSlabSupportedB (centralExtent half) physical <;>
      cases he : cutoffOneLiftedFamilyEvent (centralAmbient half)
        familyEvent physical <;>
      simp only [hs, he, Bool.false_and, Bool.true_and,
        Bool.false_eq_true, if_false, if_true] <;>
      exact Q'.eqv_refl _
  have hmaskSupported :
      listQSum (fun physical =>
          if ambientSlabSupportedB (centralExtent half) physical then
            eventTerm physical else 0) full ≈
        listQSum eventTerm supported := by
    unfold full supported ambientSlabSupportedLabellings
    exact hmask
  exact Q'.eqv_trans _ _ _ hsupportedTerms
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hmaskSupported) hmasked)

theorem centralSupportBipairReflectedKernel_eq_physicalEventNumerator
    (coupling : Q') (cutoff half : Nat)
    (leftCode rightCode : List Nat → List Bool)
    (left right : List Bool) :
    centralSupportBipairReflectedKernel
        coupling cutoff half leftCode rightCode left right ≈
      parametricKEventNumerator coupling cutoff (centralAmbient half)
        (fun physical =>
          ambientSlabSupportedB (centralExtent half) physical &&
            cutoffOneLiftedFamilyEvent (centralAmbient half)
              (centralLocalSupportBipairFamilyEvent
                half leftCode rightCode left right) physical) := by
  exact Q'.eqv_trans _ _ _
    (centralSupportBipairReflectedKernel_eq_slabWeighted
      coupling cutoff half leftCode rightCode left right)
    (Q'.eqv_trans _ _ _
      (slabWeightedPhysicalSum_eq_ambientSupported
        coupling cutoff (centralExtent half)
        (centralLocalSupportBipairSlabObservable
          half leftCode rightCode left right))
      (ambientLocalSupportBipairWeightedSum_eq_eventNumerator
        coupling cutoff half leftCode rightCode left right))

theorem finiteJointKernelBipushforward_divPos
    {Source Target : Type} [DecidableEq Target]
    (source : List Source) (joint : Source → Source → Q')
    (leftCode rightCode : Source → Target) (left right : Target)
    (denominator : Q') (hdenominator : (0 : Q') < denominator) :
    finiteJointKernelBipushforward source
        (fun first second =>
          Q'.divPos (joint first second) denominator hdenominator)
        leftCode rightCode left right ≈
      Q'.divPos
        (finiteJointKernelBipushforward
          source joint leftCode rightCode left right)
        denominator hdenominator := by
  unfold finiteJointKernelBipushforward fiberWeight Q'.divPos
  exact listQSum_mul_right
    (fun pair => joint pair.1 pair.2)
    (Q'.recipPos denominator hdenominator)
    ((cartesian source source).filter
      (fun pair => decide ((left, right) =
        (leftCode pair.1, rightCode pair.2))))

theorem centralNormalizedSupportBipairLaw_eq_divRaw
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat) (leftCode rightCode : List Nat → List Bool)
    (left right : List Bool) :
    centralNormalizedSupportBipairLaw
        coupling hcoupling cutoff half leftCode rightCode left right ≈
      Q'.divPos
        (centralSupportBipairReflectedKernel
          coupling cutoff half leftCode rightCode left right)
        (slabParametricKPhysicalPartition
          coupling cutoff (centralExtent half))
        (slabParametricKPhysicalPartition_pos
          hcoupling cutoff (centralExtent half)) := by
  unfold centralNormalizedSupportBipairLaw
    centralNormalizedSupportPairLaw centralSupportBipairReflectedKernel
  exact finiteJointKernelBipushforward_divPos
    (centralHalfSupportSpace half)
    (centralSupportReflectedKernel coupling cutoff half)
    leftCode rightCode left right
    (slabParametricKPhysicalPartition
      coupling cutoff (centralExtent half))
    (slabParametricKPhysicalPartition_pos
      hcoupling cutoff (centralExtent half))

/-- The normalized oriented bipushed entry is exactly the corrected-slab
conditional probability of the two-code family event. -/
theorem centralNormalizedSupportBipairLaw_eq_physicalGivenSlab
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat) (leftCode rightCode : List Nat → List Bool)
    (left right : List Bool) :
    centralNormalizedSupportBipairLaw
        coupling hcoupling cutoff half leftCode rightCode left right ≈
      couplingParametricKPhysicalGivenSlabProbability
        coupling hcoupling cutoff (centralExtent half)
        (centralLocalSupportBipairFamilyEvent
          half leftCode rightCode left right) := by
  refine Q'.eqv_trans _
    (Q'.divPos
      (centralSupportBipairReflectedKernel
        coupling cutoff half leftCode rightCode left right)
      (slabParametricKPhysicalPartition
        coupling cutoff (centralExtent half))
      (slabParametricKPhysicalPartition_pos
        hcoupling cutoff (centralExtent half))) _
    (centralNormalizedSupportBipairLaw_eq_divRaw
      coupling hcoupling cutoff half leftCode rightCode left right) ?_
  unfold couplingParametricKPhysicalGivenSlabProbability
  exact divPos_eqv_congr
    (slabParametricKPhysicalPartition_pos
      hcoupling cutoff (centralExtent half))
    (couplingParametricKPhysicalSlabSupportNumerator_pos
      hcoupling cutoff (centralExtent half))
    (centralSupportBipairReflectedKernel_eq_physicalEventNumerator
      coupling cutoff half leftCode rightCode left right)
    (slabParametricKPhysicalPartition_eqv_physicalSupportNumerator
      coupling cutoff (centralExtent half))

#print axioms centralSupportBipairReflectedKernel_eq_directFiber
#print axioms centralSupportBipairReflectedKernel_eq_bilinear
#print axioms centralSupportBipairReflectedKernel_eq_physicalEventNumerator
#print axioms centralNormalizedSupportBipairLaw_eq_physicalGivenSlab

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBipairConditional
