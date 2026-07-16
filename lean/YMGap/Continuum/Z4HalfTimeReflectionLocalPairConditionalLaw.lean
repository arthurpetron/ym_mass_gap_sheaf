/-
# Local support fibers as an exact corrected-slab conditional joint law

The normalized support Gram has already been pushed to finite local Boolean
fingerprints.  Here we identify each pushed entry, not only its quadratic,
with one literal corrected-slab conditional event.  The event reads the same
local code from the lower restriction and the reflected-upper restriction;
all complete supports in each local fiber are summed exactly.
-/

import YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
import YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry

namespace YMGap.Continuum.Z4HalfTimeReflectionLocalPairConditionalLaw

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCoefficientZeroExtension
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteJointKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalFamilyFaceSupportDecoder
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientPartition
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSupportPairConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Deterministic fiber composition -/

/-- Summing first over complete fibers and then over fibers of a coarser code
is exactly one pushforward through the composite code. -/
theorem fiberWeight_comp_eqv
    {Source Middle Target : Type}
    [DecidableEq Middle] [DecidableEq Target]
    (source : List Source) (weight : Source → Q')
    (first : Source → Middle)
    (middle : List Middle) (hmiddle : middle.Nodup)
    (hcoverage : ∀ item, item ∈ source → first item ∈ middle)
    (second : Middle → Target) (target : Target) :
    fiberWeight middle
        (fiberWeight source weight first) second target ≈
      fiberWeight source weight (fun item => second (first item)) target := by
  refine Q'.eqv_trans _
    (kernelPushforwardWeight middle
      (fiberWeight source weight first) second target) _
    (Q'.eqv_symm
      (kernelPushforwardWeight_eqv_fiberWeight
        (fiberWeight source weight first) second target middle)) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun item =>
        weight item *
          deterministicKernel second (first item) target)
      source) _ ?_ ?_
  · unfold kernelPushforwardWeight
    exact finiteCoefficientZeroExtension_reindex_mul
      source weight first middle hmiddle hcoverage
      (fun item => deterministicKernel second item target)
  · exact kernelPushforwardWeight_eqv_fiberWeight
      weight (fun item => second (first item)) target source

/-! ## 2. The unnormalized local support-pair kernel -/

def centralLocalSupportReflectedKernel
    (w : Q') (K half : Nat) (code : List Nat → List Bool)
    (left right : List Bool) : Q' :=
  finiteJointKernelPushforward
    (centralHalfSupportSpace half)
    (centralSupportReflectedKernel w K half)
    code left right

theorem centralLocalSupportReflectedKernel_eq_directFiber
    (w : Q') (K half : Nat) (code : List Nat → List Bool)
    (left right : List Bool) :
    centralLocalSupportReflectedKernel w K half code left right ≈
      fiberWeight
        (centralHalfStatePairs K half)
        (fun pair => centralPhysicalReflectedKernel
          w K half pair.1 pair.2)
        (fun pair =>
          (code (centralHalfSupportCode half pair.1),
            code (centralHalfSupportCode half pair.2)))
        (left, right) := by
  unfold centralLocalSupportReflectedKernel
    finiteJointKernelPushforward centralSupportReflectedKernel
    centralHalfSupportPairCode
  exact fiberWeight_comp_eqv
    (centralHalfStatePairs K half)
    (fun pair => centralPhysicalReflectedKernel
      w K half pair.1 pair.2)
    (fun pair =>
      (centralHalfSupportCode half pair.1,
        centralHalfSupportCode half pair.2))
    (cartesian (centralHalfSupportSpace half)
      (centralHalfSupportSpace half))
    (centralHalfSupportPairs_nodup half)
    (centralHalfSupportPairCode_mem K half)
    (fun pair => (code pair.1, code pair.2))
    (left, right)

/-! ## 3. The direct local fiber is one physical bilinear entry -/

def centralLocalSupportPointCoefficient
    (half : Nat) (code : List Nat → List Bool)
    (target : List Bool) (state : EdgeLabelling) : Q' :=
  if target = code (centralHalfSupportCode half state) then 1 else 0

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

private theorem localPairMask_eqv_pointProduct
    {Target : Type} [DecidableEq Target]
    (leftTarget leftCode rightTarget rightCode : Target)
    (weight : Q') :
    (if decide
        ((leftTarget, rightTarget) = (leftCode, rightCode))
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
    exact Q'.mul_eqv_congr_right _ _ weight
      (Q'.zero_mul_eqv _)

theorem centralLocalSupportReflectedKernel_eq_bilinear
    (w : Q') (K half : Nat) (code : List Nat → List Bool)
    (left right : List Bool) :
    centralLocalSupportReflectedKernel w K half code left right ≈
      centralPhysicalReflectionBilinear w K half
        (centralLocalSupportPointCoefficient half code left)
        (centralLocalSupportPointCoefficient half code right) := by
  let pairWeight : EdgeLabelling × EdgeLabelling → Q' := fun pair =>
    centralPhysicalReflectedKernel w K half pair.1 pair.2
  let pairCode : EdgeLabelling × EdgeLabelling →
      List Bool × List Bool := fun pair =>
    (code (centralHalfSupportCode half pair.1),
      code (centralHalfSupportCode half pair.2))
  let event : EdgeLabelling × EdgeLabelling → Bool := fun pair =>
    decide ((left, right) = pairCode pair)
  have hdirect := centralLocalSupportReflectedKernel_eq_directFiber
    w K half code left right
  have hmask :
      listQSum pairWeight
          ((centralHalfStatePairs K half).filter event) ≈
        listQSum
          (fun pair => if event pair then pairWeight pair else 0)
          (centralHalfStatePairs K half) :=
    Q'.eqv_symm
      (listQSum_mask_eq_filter_local pairWeight event
        (centralHalfStatePairs K half))
  have hpointwise :
      listQSum
          (fun pair => if event pair then pairWeight pair else 0)
          (centralHalfStatePairs K half) ≈
        listQSum
          (fun pair =>
            (centralLocalSupportPointCoefficient
                half code left pair.1 *
              centralLocalSupportPointCoefficient
                half code right pair.2) * pairWeight pair)
          (centralHalfStatePairs K half) := by
    apply listQSum_congr
    intro pair
    exact localPairMask_eqv_pointProduct
      left (code (centralHalfSupportCode half pair.1))
      right (code (centralHalfSupportCode half pair.2))
      (pairWeight pair)
  have hcartesian :
      listQSum
          (fun pair =>
            (centralLocalSupportPointCoefficient
                half code left pair.1 *
              centralLocalSupportPointCoefficient
                half code right pair.2) * pairWeight pair)
          (centralHalfStatePairs K half) ≈
        centralPhysicalReflectionBilinear w K half
          (centralLocalSupportPointCoefficient half code left)
          (centralLocalSupportPointCoefficient half code right) := by
    unfold centralHalfStatePairs centralPhysicalReflectionBilinear
    exact listQSum_cartesian_eq_nested
      (fun pair =>
        (centralLocalSupportPointCoefficient half code left pair.1 *
          centralLocalSupportPointCoefficient half code right pair.2) *
            centralPhysicalReflectedKernel w K half pair.1 pair.2)
      (centralHalfStates K half) (centralHalfStates K half)
  unfold fiberWeight at hdirect
  exact Q'.eqv_trans _ _ _ hdirect
    (Q'.eqv_trans _ _ _ hmask
      (Q'.eqv_trans _ _ _ hpointwise hcartesian))

/-! ## 4. The literal family event on the two slab restrictions -/

def centralLocalSupportPairFamilyEvent
    (half : Nat) (code : List Nat → List Bool)
    (left right : List Bool) (family : List (List Nat)) : Bool :=
  decide
    (code (centralFamilyLowerSupportCode half family) = left ∧
      code (centralFamilyReflectedUpperSupportCode half family) = right)

theorem centralLocalSupportPairFamilyEvent_physical
    (half : Nat) (code : List Nat → List Bool)
    (left right : List Bool) (physical : EdgeLabelling) :
    centralLocalSupportPairFamilyEvent half code left right
        (physicalCanonicalAmbientFamily (centralAmbient half) physical) =
      decide
        (code
              (centralHalfSupportCode half
                (centralLowerRestriction half
                  (ambientToSlabPhysical (centralExtent half) physical))) =
            left ∧
          code
              (centralHalfSupportCode half
                (centralReflectedUpperRestriction half
                  (ambientToSlabPhysical (centralExtent half) physical))) =
            right) := by
  unfold centralLocalSupportPairFamilyEvent
  rw [centralFamilyLowerSupportCode_physical,
    centralFamilyReflectedUpperSupportCode_physical]

def centralLocalSupportPairSlabObservable
    (half : Nat) (code : List Nat → List Bool)
    (left right : List Bool) (physical : EdgeLabelling) : Q' :=
  centralLocalSupportPointCoefficient half code left
      (centralLowerRestriction half physical) *
    centralLocalSupportPointCoefficient half code right
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
      rw [if_pos hleft, if_pos hright,
        if_pos (decide_eq_true hpair)]
      exact Q'.one_mul_eqv 1
    · have hpair : ¬(leftCode = leftTarget ∧
          rightCode = rightTarget) := fun h => hright h.2.symm
      rw [if_pos hleft, if_neg hright, decide_eq_false hpair]
      exact Q'.one_mul_eqv 0
  · have hpair : ¬(leftCode = leftTarget ∧
        rightCode = rightTarget) := fun h => hleft h.1.symm
    rw [if_neg hleft, decide_eq_false hpair]
    exact Q'.zero_mul_eqv _

theorem centralLocalSupportPairSlabObservable_eqv_indicator
    (half : Nat) (code : List Nat → List Bool)
    (left right : List Bool) (physical : EdgeLabelling) :
    centralLocalSupportPairSlabObservable half code left right physical ≈
      (if decide
          (code
                (centralHalfSupportCode half
                  (centralLowerRestriction half physical)) = left ∧
            code
                (centralHalfSupportCode half
                  (centralReflectedUpperRestriction half physical)) = right)
        then 1 else 0) := by
  unfold centralLocalSupportPairSlabObservable
    centralLocalSupportPointCoefficient
  exact pointProduct_eqv_localIndicator
    left
      (code (centralHalfSupportCode half
        (centralLowerRestriction half physical)))
    right
      (code (centralHalfSupportCode half
        (centralReflectedUpperRestriction half physical)))

theorem centralLocalSupportReflectedKernel_eq_slabWeighted
    (w : Q') (K half : Nat) (code : List Nat → List Bool)
    (left right : List Bool) :
    centralLocalSupportReflectedKernel w K half code left right ≈
      slabWeightedPhysicalSum w K (centralExtent half)
        (centralLocalSupportPairSlabObservable
          half code left right) := by
  refine Q'.eqv_trans _ _ _
    (centralLocalSupportReflectedKernel_eq_bilinear
      w K half code left right) ?_
  refine Q'.eqv_trans _ _ _
    (centralPhysicalReflectionBilinear_eq_full w K half
      (centralLocalSupportPointCoefficient half code left)
      (centralLocalSupportPointCoefficient half code right)) ?_
  exact Q'.eqv_refl _

private theorem ambientLocalSupportPairWeightedSum_eq_eventNumerator
    (w : Q') (K half : Nat) (code : List Nat → List Bool)
    (left right : List Bool) :
    ambientSlabSupportedWeightedSum w K (centralExtent half)
        (centralLocalSupportPairSlabObservable half code left right) ≈
      parametricKEventNumerator w K (centralAmbient half)
        (fun physical =>
          ambientSlabSupportedB (centralExtent half) physical &&
            cutoffOneLiftedFamilyEvent (centralAmbient half)
              (centralLocalSupportPairFamilyEvent
                half code left right) physical) := by
  let full := boundedEdgeLabellings K
    (List.range (plaquetteEdgeCount (centralAmbient half)))
  let supported := ambientSlabSupportedLabellings K (centralExtent half)
  let familyEvent := centralLocalSupportPairFamilyEvent
    half code left right
  let eventTerm : EdgeLabelling → Q' := fun physical =>
    if cutoffOneLiftedFamilyEvent (centralAmbient half)
        familyEvent physical
    then parametricKPhysicalTerm w K (centralAmbient half) physical
    else 0
  have hsupportedTerms :
      ambientSlabSupportedWeightedSum w K (centralExtent half)
          (centralLocalSupportPairSlabObservable
            half code left right) ≈
        listQSum eventTerm supported := by
    unfold ambientSlabSupportedWeightedSum supported
    apply listQSum_congr_on
    intro physical _hphysical
    have hevent : cutoffOneLiftedFamilyEvent (centralAmbient half)
          familyEvent physical =
        decide
          (code
                (centralHalfSupportCode half
                  (centralLowerRestriction half
                    (ambientToSlabPhysical (centralExtent half) physical))) =
              left ∧
            code
                (centralHalfSupportCode half
                  (centralReflectedUpperRestriction half
                    (ambientToSlabPhysical (centralExtent half) physical))) =
              right) := by
      unfold cutoffOneLiftedFamilyEvent familyEvent
      exact centralLocalSupportPairFamilyEvent_physical
        half code left right physical
    let pairEvent := decide
      (code
            (centralHalfSupportCode half
              (centralLowerRestriction half
                (ambientToSlabPhysical (centralExtent half) physical))) =
          left ∧
        code
            (centralHalfSupportCode half
              (centralReflectedUpperRestriction half
                (ambientToSlabPhysical (centralExtent half) physical))) =
          right)
    have hobservable :=
      centralLocalSupportPairSlabObservable_eqv_indicator
        half code left right
        (ambientToSlabPhysical (centralExtent half) physical)
    unfold eventTerm
    rw [hevent]
    refine Q'.eqv_trans _
      ((if pairEvent then 1 else 0) *
        parametricKPhysicalTerm w K (centralAmbient half) physical) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ hobservable
    · change
        ((if pairEvent = true then 1 else 0) *
            parametricKPhysicalTerm w K (centralAmbient half) physical) ≈
          (if pairEvent = true then
            parametricKPhysicalTerm w K (centralAmbient half) physical
          else 0)
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
      listQSum
          (fun physical =>
            if ambientSlabSupportedB (centralExtent half) physical then
              eventTerm physical else 0)
          full ≈
        parametricKEventNumerator w K (centralAmbient half)
          (fun physical =>
            ambientSlabSupportedB (centralExtent half) physical &&
              cutoffOneLiftedFamilyEvent (centralAmbient half)
                familyEvent physical) := by
    unfold parametricKEventNumerator parametricKEventTerm
      eventTerm full
    apply listQSum_congr
    intro physical
    cases hs : ambientSlabSupportedB (centralExtent half) physical <;>
      cases he : cutoffOneLiftedFamilyEvent (centralAmbient half)
        familyEvent physical <;>
      simp only [hs, he, Bool.false_and, Bool.true_and,
        Bool.false_eq_true, if_false, if_true] <;>
      exact Q'.eqv_refl _
  have hmaskSupported :
      listQSum
          (fun physical =>
            if ambientSlabSupportedB (centralExtent half) physical then
              eventTerm physical else 0)
          full ≈
        listQSum eventTerm supported := by
    unfold full supported ambientSlabSupportedLabellings
    exact hmask
  exact Q'.eqv_trans _ _ _ hsupportedTerms
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hmaskSupported) hmasked)

theorem centralLocalSupportReflectedKernel_eq_physicalEventNumerator
    (w : Q') (K half : Nat) (code : List Nat → List Bool)
    (left right : List Bool) :
    centralLocalSupportReflectedKernel w K half code left right ≈
      parametricKEventNumerator w K (centralAmbient half)
        (fun physical =>
          ambientSlabSupportedB (centralExtent half) physical &&
            cutoffOneLiftedFamilyEvent (centralAmbient half)
              (centralLocalSupportPairFamilyEvent
                half code left right) physical) := by
  exact Q'.eqv_trans _ _ _
    (centralLocalSupportReflectedKernel_eq_slabWeighted
      w K half code left right)
    (Q'.eqv_trans _ _ _
      (slabWeightedPhysicalSum_eq_ambientSupported
        w K (centralExtent half)
        (centralLocalSupportPairSlabObservable half code left right))
      (ambientLocalSupportPairWeightedSum_eq_eventNumerator
        w K half code left right))

/-! ## 5. Normalization commutes with the finite local pushforward -/

theorem finiteJointKernelPushforward_divPos
    {Source Target : Type} [DecidableEq Target]
    (source : List Source) (joint : Source → Source → Q')
    (code : Source → Target) (left right : Target)
    (denominator : Q') (hdenominator : (0 : Q') < denominator) :
    finiteJointKernelPushforward source
        (fun first second =>
          Q'.divPos (joint first second) denominator hdenominator)
        code left right ≈
      Q'.divPos
        (finiteJointKernelPushforward source joint code left right)
        denominator hdenominator := by
  unfold finiteJointKernelPushforward fiberWeight Q'.divPos
  exact listQSum_mul_right
    (fun pair => joint pair.1 pair.2)
    (Q'.recipPos denominator hdenominator)
    ((cartesian source source).filter
      (fun pair => decide ((left, right) =
        (code pair.1, code pair.2))))

theorem centralNormalizedLocalSupportPairLaw_eq_divRaw
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (code : List Nat → List Bool) (left right : List Bool) :
    centralNormalizedLocalSupportPairLaw
        w hw K half code left right ≈
      Q'.divPos
        (centralLocalSupportReflectedKernel
          w K half code left right)
        (slabParametricKPhysicalPartition w K (centralExtent half))
        (slabParametricKPhysicalPartition_pos
          hw K (centralExtent half)) := by
  unfold centralNormalizedLocalSupportPairLaw
    centralNormalizedSupportPairLaw
  exact finiteJointKernelPushforward_divPos
    (centralHalfSupportSpace half)
    (centralSupportReflectedKernel w K half)
    code left right
    (slabParametricKPhysicalPartition w K (centralExtent half))
    (slabParametricKPhysicalPartition_pos hw K (centralExtent half))

/-- Entrywise local conditional-law identity.  The left side sums all complete
lower/reflected-upper supports having the prescribed local fingerprints; the
right side is the literal corrected-slab conditional probability of exactly
that joint family event. -/
theorem centralNormalizedLocalSupportPairLaw_eq_physicalGivenSlab
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (code : List Nat → List Bool) (left right : List Bool) :
    centralNormalizedLocalSupportPairLaw
        w hw K half code left right ≈
      couplingParametricKPhysicalGivenSlabProbability
        w hw K (centralExtent half)
        (centralLocalSupportPairFamilyEvent
          half code left right) := by
  refine Q'.eqv_trans _
    (Q'.divPos
      (centralLocalSupportReflectedKernel w K half code left right)
      (slabParametricKPhysicalPartition w K (centralExtent half))
      (slabParametricKPhysicalPartition_pos
        hw K (centralExtent half))) _
    (centralNormalizedLocalSupportPairLaw_eq_divRaw
      w hw K half code left right) ?_
  unfold couplingParametricKPhysicalGivenSlabProbability
  exact divPos_eqv_congr
    (slabParametricKPhysicalPartition_pos hw K (centralExtent half))
    (couplingParametricKPhysicalSlabSupportNumerator_pos
      hw K (centralExtent half))
    (centralLocalSupportReflectedKernel_eq_physicalEventNumerator
      w K half code left right)
    (slabParametricKPhysicalPartition_eqv_physicalSupportNumerator
      w K (centralExtent half))

#print axioms fiberWeight_comp_eqv
#print axioms centralLocalSupportReflectedKernel_eq_directFiber
#print axioms centralLocalSupportReflectedKernel_eq_bilinear
#print axioms centralLocalSupportPairFamilyEvent_physical
#print axioms centralLocalSupportPairSlabObservable_eqv_indicator
#print axioms centralLocalSupportReflectedKernel_eq_slabWeighted
#print axioms centralLocalSupportReflectedKernel_eq_physicalEventNumerator
#print axioms finiteJointKernelPushforward_divPos
#print axioms centralNormalizedLocalSupportPairLaw_eq_divRaw
#print axioms centralNormalizedLocalSupportPairLaw_eq_physicalGivenSlab

end YMGap.Continuum.Z4HalfTimeReflectionLocalPairConditionalLaw
