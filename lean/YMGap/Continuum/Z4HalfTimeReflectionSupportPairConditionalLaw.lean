/-
# Support-pushed Gram entries as exhaustive conditional cylinders

Each entry of the support-pushed corrected-slab Gram is the normalized weight
of one prescribed lower/reflected-upper occupied-support pair.  We identify
that entry with the literal physical law conditioned on corrected-slab
support.  The event is expressed on the finite list of all slab-supported
canonical polymers, using the exhaustive decoder from
`Z4CanonicalFamilyFaceSupportDecoder`.

The proof retains the ordered pair entry, rather than recovering it by
polarization: a bilinear version of the existing full-slab reindexing sends
the deterministic support fibre directly to the full corrected-slab weighted
sum.  Consequently there is no hidden factor of two.
-/

import YMGap.Continuum.Z4CanonicalFamilyFaceSupportDecoder
import YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStabilityGeneral
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.Z4HalfTimeReflectionSupportPairConditionalLaw

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalFamilyFaceSupportDecoder
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientPartition
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStability
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStabilityGeneral
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Bilinear full-slab reindexing -/

def centralPhysicalReflectionBilinear
    (w : Q') (K half : Nat)
    (leftCoefficient rightCoefficient : EdgeLabelling → Q') : Q' :=
  listQSum
    (fun left => listQSum
      (fun right =>
        (leftCoefficient left * rightCoefficient right) *
          centralPhysicalReflectedKernel w K half left right)
      (centralHalfStates K half))
    (centralHalfStates K half)

def centralFullPhysicalReflectionBilinear
    (w : Q') (K half : Nat)
    (leftCoefficient rightCoefficient : EdgeLabelling → Q') : Q' :=
  listQSum
    (fun physical =>
      (leftCoefficient (centralLowerRestriction half physical) *
        rightCoefficient
          (centralReflectedUpperRestriction half physical)) *
        slabParametricKPhysicalTerm w K (centralExtent half) physical)
    (boundedEdgeLabellings K
      (slabPhysicalFaceEdges (centralExtent half)))

private def centralTripleBilinearTerm
    (w : Q') (K half : Nat)
    (leftCoefficient rightCoefficient : EdgeLabelling → Q')
    (triple : CentralReflectionTriple) : Q' :=
  (leftCoefficient triple.1 * rightCoefficient triple.2.1) *
    slabParametricKPhysicalTerm w K (centralExtent half)
      (assembleCentralReflectionTriple half triple)

private theorem listQSumCongrMemLocal {A : Type} {left right : A → Q'} :
    ∀ xs : List A, (∀ x, x ∈ xs → left x ≈ right x) →
      listQSum left xs ≈ listQSum right xs
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hagree =>
      Q'.add_eqv_congr'
        (hagree head List.mem_cons_self)
        (listQSumCongrMemLocal tail
          (fun x hx => hagree x (List.mem_cons_of_mem head hx)))

private theorem centralTripleBilinearSum_eq_nested
    (w : Q') (K half : Nat)
    (leftCoefficient rightCoefficient : EdgeLabelling → Q') :
    listQSum
        (centralTripleBilinearTerm w K half
          leftCoefficient rightCoefficient)
        (centralReflectionTriples K half) ≈
      listQSum
        (fun left => listQSum
          (fun right => listQSum
            (fun boundary =>
              (leftCoefficient left * rightCoefficient right) *
                slabParametricKPhysicalTerm w K (centralExtent half)
                  (assembleReflectedSlabLabelling half
                    left boundary right))
            (centralBoundaryChannels K half))
          (centralHalfStates K half))
        (centralHalfStates K half) := by
  unfold centralReflectionTriples
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap
      (centralTripleBilinearTerm w K half
        leftCoefficient rightCoefficient)
      (fun left =>
        (centralHalfStates K half).flatMap (fun right =>
          (centralBoundaryChannels K half).map (fun boundary =>
            (left, (right, boundary)))))
      (centralHalfStates K half)) ?_
  apply listQSum_congr
  intro left
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap
      (centralTripleBilinearTerm w K half
        leftCoefficient rightCoefficient)
      (fun right =>
        (centralBoundaryChannels K half).map (fun boundary =>
          (left, (right, boundary))))
      (centralHalfStates K half)) ?_
  apply listQSum_congr
  intro right
  rw [listQSum_map]
  exact Q'.eqv_refl _

private theorem centralPhysicalReflectionBilinear_eq_tripleSum
    (w : Q') (K half : Nat)
    (leftCoefficient rightCoefficient : EdgeLabelling → Q') :
    centralPhysicalReflectionBilinear w K half
        leftCoefficient rightCoefficient ≈
      listQSum
        (centralTripleBilinearTerm w K half
          leftCoefficient rightCoefficient)
        (centralReflectionTriples K half) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun left => listQSum
        (fun right => listQSum
          (fun boundary =>
            (leftCoefficient left * rightCoefficient right) *
              slabParametricKPhysicalTerm w K (centralExtent half)
                (assembleReflectedSlabLabelling half
                  left boundary right))
          (centralBoundaryChannels K half))
        (centralHalfStates K half))
      (centralHalfStates K half)) _ ?_ ?_
  · unfold centralPhysicalReflectionBilinear
    apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    unfold centralPhysicalReflectedKernel
    exact Q'.eqv_symm
      (listQSum_mul_left
        (leftCoefficient left * rightCoefficient right)
        (fun boundary =>
          slabParametricKPhysicalTerm w K (centralExtent half)
            (assembleReflectedSlabLabelling half left boundary right))
        (centralBoundaryChannels K half))
  · exact Q'.eqv_symm
      (centralTripleBilinearSum_eq_nested
        w K half leftCoefficient rightCoefficient)

private theorem centralTripleBilinearSum_eq_assembled
    (w : Q') (K half : Nat)
    (leftCoefficient rightCoefficient : EdgeLabelling → Q') :
    listQSum
        (centralTripleBilinearTerm w K half
          leftCoefficient rightCoefficient)
        (centralReflectionTriples K half) ≈
      listQSum
        (fun physical =>
          (leftCoefficient (centralLowerRestriction half physical) *
            rightCoefficient
              (centralReflectedUpperRestriction half physical)) *
            slabParametricKPhysicalTerm w K
              (centralExtent half) physical)
        (centralAssembledSlabLabellings K half) := by
  unfold centralAssembledSlabLabellings
  rw [listQSum_map]
  apply listQSumCongrMemLocal
  intro triple htriple
  have hparts := mem_centralReflectionTriples.mp htriple
  unfold centralTripleBilinearTerm assembleCentralReflectionTriple
  rw [centralLowerRestriction_assemble (K := K) (half := half) hparts.1,
    centralReflectedUpperRestriction_assemble
      (K := K) (half := half) hparts.2.1]
  exact Q'.eqv_refl _

/-- Ordered bilinear version of the full corrected-slab reindexing. -/
theorem centralPhysicalReflectionBilinear_eq_full
    (w : Q') (K half : Nat)
    (leftCoefficient rightCoefficient : EdgeLabelling → Q') :
    centralPhysicalReflectionBilinear w K half
        leftCoefficient rightCoefficient ≈
      centralFullPhysicalReflectionBilinear w K half
        leftCoefficient rightCoefficient := by
  refine Q'.eqv_trans _ _ _
    (centralPhysicalReflectionBilinear_eq_tripleSum
      w K half leftCoefficient rightCoefficient) ?_
  refine Q'.eqv_trans _ _ _
    (centralTripleBilinearSum_eq_assembled
      w K half leftCoefficient rightCoefficient) ?_
  unfold centralFullPhysicalReflectionBilinear
  exact listQSum_centralAssembledSlabLabellings _ K half

/-! ## 2. One deterministic support fibre is one bilinear entry -/

def centralSupportPointCoefficient
    (half : Nat) (support : List Nat)
    (state : EdgeLabelling) : Q' :=
  if support = centralHalfSupportCode half state then 1 else 0

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

private theorem pairMask_eqv_pointProductGeneric
    {A B : Type} [DecidableEq A] [DecidableEq B]
    (leftTarget leftCode : A) (rightTarget rightCode : B)
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
    exact Q'.mul_eqv_congr_right _ _ weight
      (Q'.zero_mul_eqv _)

private theorem pairMask_eqv_pointProduct
    (half : Nat) (leftSupport rightSupport : List Nat)
    (pair : EdgeLabelling × EdgeLabelling)
    (weight : Q') :
    (if decide
        ((leftSupport, rightSupport) =
          centralHalfSupportPairCode half pair)
      then weight else 0) ≈
      (centralSupportPointCoefficient half leftSupport pair.1 *
        centralSupportPointCoefficient half rightSupport pair.2) *
          weight := by
  unfold centralHalfSupportPairCode centralSupportPointCoefficient
  exact pairMask_eqv_pointProductGeneric
    leftSupport (centralHalfSupportCode half pair.1)
    rightSupport (centralHalfSupportCode half pair.2) weight

theorem centralSupportReflectedKernel_eq_bilinear
    (w : Q') (K half : Nat)
    (leftSupport rightSupport : List Nat) :
    centralSupportReflectedKernel w K half
        leftSupport rightSupport ≈
      centralPhysicalReflectionBilinear w K half
        (centralSupportPointCoefficient half leftSupport)
        (centralSupportPointCoefficient half rightSupport) := by
  let pairWeight : EdgeLabelling × EdgeLabelling → Q' := fun pair =>
    centralPhysicalReflectedKernel w K half pair.1 pair.2
  let event : EdgeLabelling × EdgeLabelling → Bool := fun pair =>
    decide ((leftSupport, rightSupport) =
      centralHalfSupportPairCode half pair)
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
            (centralSupportPointCoefficient half leftSupport pair.1 *
              centralSupportPointCoefficient half rightSupport pair.2) *
                pairWeight pair)
          (centralHalfStatePairs K half) := by
    apply listQSum_congr
    intro pair
    exact pairMask_eqv_pointProduct
      half leftSupport rightSupport pair (pairWeight pair)
  have hcartesian :
      listQSum
          (fun pair =>
            (centralSupportPointCoefficient half leftSupport pair.1 *
              centralSupportPointCoefficient half rightSupport pair.2) *
                pairWeight pair)
          (centralHalfStatePairs K half) ≈
        centralPhysicalReflectionBilinear w K half
          (centralSupportPointCoefficient half leftSupport)
          (centralSupportPointCoefficient half rightSupport) := by
    unfold centralHalfStatePairs centralPhysicalReflectionBilinear pairWeight
    exact listQSum_cartesian_eq_nested
      (fun pair =>
        (centralSupportPointCoefficient half leftSupport pair.1 *
          centralSupportPointCoefficient half rightSupport pair.2) *
            centralPhysicalReflectedKernel w K half pair.1 pair.2)
      (centralHalfStates K half) (centralHalfStates K half)
  unfold centralSupportReflectedKernel fiberWeight
  exact Q'.eqv_trans _ _ _ hmask
    (Q'.eqv_trans _ _ _ hpointwise hcartesian)

def centralSupportPairSlabObservable
    (half : Nat) (leftSupport rightSupport : List Nat)
    (physical : EdgeLabelling) : Q' :=
  centralSupportPointCoefficient half leftSupport
      (centralLowerRestriction half physical) *
    centralSupportPointCoefficient half rightSupport
      (centralReflectedUpperRestriction half physical)

theorem centralSupportReflectedKernel_eq_slabWeighted
    (w : Q') (K half : Nat)
    (leftSupport rightSupport : List Nat) :
    centralSupportReflectedKernel w K half
        leftSupport rightSupport ≈
      slabWeightedPhysicalSum w K (centralExtent half)
        (centralSupportPairSlabObservable
          half leftSupport rightSupport) := by
  refine Q'.eqv_trans _ _ _
    (centralSupportReflectedKernel_eq_bilinear
      w K half leftSupport rightSupport) ?_
  refine Q'.eqv_trans _ _ _
    (centralPhysicalReflectionBilinear_eq_full w K half
      (centralSupportPointCoefficient half leftSupport)
      (centralSupportPointCoefficient half rightSupport)) ?_
  exact Q'.eqv_refl _

/-! ## 3. Entrywise identification with the physical conditional law -/

private theorem pointProduct_eqv_reverseAndIndicatorGeneric
    {A B : Type} [DecidableEq A] [DecidableEq B]
    (leftTarget leftCode : A) (rightTarget rightCode : B) :
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

private theorem centralSupportPairSlabObservable_eqv_indicator
    (half : Nat) (leftSupport rightSupport : List Nat)
    (physical : EdgeLabelling) :
    centralSupportPairSlabObservable half leftSupport rightSupport physical ≈
      (if decide
          (centralHalfSupportCode half
                (centralLowerRestriction half physical) = leftSupport ∧
            centralHalfSupportCode half
                (centralReflectedUpperRestriction half physical) = rightSupport)
        then 1 else 0) := by
  unfold centralSupportPairSlabObservable centralSupportPointCoefficient
  exact pointProduct_eqv_reverseAndIndicatorGeneric
    leftSupport
      (centralHalfSupportCode half
        (centralLowerRestriction half physical))
    rightSupport
      (centralHalfSupportCode half
        (centralReflectedUpperRestriction half physical))

private theorem ambientSupportPairWeightedSum_eq_eventNumerator
    (w : Q') (K half : Nat)
    (leftSupport rightSupport : List Nat) :
    ambientSlabSupportedWeightedSum w K (centralExtent half)
        (centralSupportPairSlabObservable
          half leftSupport rightSupport) ≈
      parametricKEventNumerator w K (centralAmbient half)
        (fun physical =>
          ambientSlabSupportedB (centralExtent half) physical &&
            cutoffOneLiftedFamilyEvent (centralAmbient half)
              (slabMarkedCylinderEvent
                (centralSlabCanonicalAtoms half)
                (centralSlabSupportPairCylinderPredicate
                  half leftSupport rightSupport)) physical) := by
  let full := boundedEdgeLabellings K
    (List.range (plaquetteEdgeCount (centralAmbient half)))
  let supported := ambientSlabSupportedLabellings K (centralExtent half)
  let cylinder := slabMarkedCylinderEvent
    (centralSlabCanonicalAtoms half)
    (centralSlabSupportPairCylinderPredicate
      half leftSupport rightSupport)
  let eventTerm : EdgeLabelling → Q' := fun physical =>
    if cutoffOneLiftedFamilyEvent (centralAmbient half)
        cylinder physical
    then parametricKPhysicalTerm w K (centralAmbient half) physical
    else 0
  have hsupportedTerms :
      ambientSlabSupportedWeightedSum w K (centralExtent half)
          (centralSupportPairSlabObservable
            half leftSupport rightSupport) ≈
        listQSum eventTerm supported := by
    unfold ambientSlabSupportedWeightedSum supported
    apply listQSum_congr_on
    intro physical hphysical
    have hsupported := (List.mem_filter.mp hphysical).2
    have hevent : cutoffOneLiftedFamilyEvent (centralAmbient half)
          cylinder physical =
        decide
          (centralHalfSupportCode half
                (centralLowerRestriction half
                  (ambientToSlabPhysical (centralExtent half) physical)) =
              leftSupport ∧
            centralHalfSupportCode half
                (centralReflectedUpperRestriction half
              (ambientToSlabPhysical (centralExtent half) physical)) =
              rightSupport) := by
      unfold cutoffOneLiftedFamilyEvent cylinder slabMarkedCylinderEvent
      change sourceCylinderEvent
          ((centralSlabCanonicalAtoms half).map Subtype.val)
          (centralSlabSupportPairCylinderPredicate
            half leftSupport rightSupport)
          (physicalCanonicalAmbientFamily (centralAmbient half) physical) = _
      rw [centralSlabCanonicalAtoms_values half]
      exact centralSlabSupportPairCylinderEvent_physical
        half leftSupport rightSupport physical hsupported
    let pairEvent := decide
      (centralHalfSupportCode half
            (centralLowerRestriction half
              (ambientToSlabPhysical (centralExtent half) physical)) =
          leftSupport ∧
        centralHalfSupportCode half
            (centralReflectedUpperRestriction half
              (ambientToSlabPhysical (centralExtent half) physical)) =
          rightSupport)
    have hobservable := centralSupportPairSlabObservable_eqv_indicator
      half leftSupport rightSupport
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
                cylinder physical) := by
    unfold parametricKEventNumerator parametricKEventTerm
      eventTerm full
    apply listQSum_congr
    intro physical
    cases hs : ambientSlabSupportedB (centralExtent half) physical <;>
      cases he : cutoffOneLiftedFamilyEvent (centralAmbient half)
        cylinder physical <;>
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

theorem centralSupportReflectedKernel_eq_physicalEventNumerator
    (w : Q') (K half : Nat)
    (leftSupport rightSupport : List Nat) :
    centralSupportReflectedKernel w K half
        leftSupport rightSupport ≈
      parametricKEventNumerator w K (centralAmbient half)
        (fun physical =>
          ambientSlabSupportedB (centralExtent half) physical &&
            cutoffOneLiftedFamilyEvent (centralAmbient half)
              (slabMarkedCylinderEvent
                (centralSlabCanonicalAtoms half)
                (centralSlabSupportPairCylinderPredicate
                  half leftSupport rightSupport)) physical) := by
  exact Q'.eqv_trans _ _ _
    (centralSupportReflectedKernel_eq_slabWeighted
      w K half leftSupport rightSupport)
    (Q'.eqv_trans _ _ _
      (slabWeightedPhysicalSum_eq_ambientSupported
        w K (centralExtent half)
        (centralSupportPairSlabObservable
          half leftSupport rightSupport))
      (ambientSupportPairWeightedSum_eq_eventNumerator
        w K half leftSupport rightSupport))

def centralNormalizedSupportPairLaw
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (leftSupport rightSupport : List Nat) : Q' :=
  Q'.divPos
    (centralSupportReflectedKernel w K half
      leftSupport rightSupport)
    (slabParametricKPhysicalPartition w K (centralExtent half))
    (slabParametricKPhysicalPartition_pos hw K (centralExtent half))

/-- Every normalized support-pushed Gram entry is exactly one exhaustive
finite joint Boolean cylinder probability in the literal corrected-slab
physical conditional law. -/
theorem centralNormalizedSupportPairLaw_eq_physicalGivenSlab
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (leftSupport rightSupport : List Nat) :
    centralNormalizedSupportPairLaw w hw K half
        leftSupport rightSupport ≈
      couplingParametricKPhysicalGivenSlabProbability
        w hw K (centralExtent half)
        (slabMarkedCylinderEvent
          (centralSlabCanonicalAtoms half)
          (centralSlabSupportPairCylinderPredicate
            half leftSupport rightSupport)) := by
  unfold centralNormalizedSupportPairLaw
    couplingParametricKPhysicalGivenSlabProbability
  exact divPos_eqv_congr
    (slabParametricKPhysicalPartition_pos hw K (centralExtent half))
    (couplingParametricKPhysicalSlabSupportNumerator_pos
      hw K (centralExtent half))
    (centralSupportReflectedKernel_eq_physicalEventNumerator
      w K half leftSupport rightSupport)
    (slabParametricKPhysicalPartition_eqv_physicalSupportNumerator
      w K (centralExtent half))

/-! ## 4. Normalized support quadratic as a joint-law quadratic -/

theorem centralNormalizedSupportReflectionQuadratic_eq_jointLaw
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : List Nat → Q') :
    centralNormalizedSupportReflectionQuadratic
        w hw K half coefficient ≈
      finiteJointQuadratic (centralHalfSupportSpace half) coefficient
        (centralNormalizedSupportPairLaw w hw K half) := by
  let denominator := slabParametricKPhysicalPartition
    w K (centralExtent half)
  let hdenominator := slabParametricKPhysicalPartition_pos
    hw K (centralExtent half)
  let reciprocal := Q'.recipPos denominator hdenominator
  unfold centralNormalizedSupportReflectionQuadratic
    centralSupportReflectionQuadratic finiteJointQuadratic
    centralNormalizedSupportPairLaw Q'.divPos
  change
    centralSupportReflectionQuadratic w K half coefficient * reciprocal ≈
      listQSum
        (fun left => listQSum
          (fun right =>
            (coefficient left * coefficient right) *
              (centralSupportReflectedKernel w K half left right *
                reciprocal))
          (centralHalfSupportSpace half))
        (centralHalfSupportSpace half)
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right =>
            (coefficient left * coefficient right) *
              centralSupportReflectedKernel w K half left right)
          (centralHalfSupportSpace half) * reciprocal)
      (centralHalfSupportSpace half)) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_mul_right
        (fun left => listQSum
          (fun right =>
            (coefficient left * coefficient right) *
              centralSupportReflectedKernel w K half left right)
          (centralHalfSupportSpace half))
        reciprocal (centralHalfSupportSpace half))
  · apply listQSum_congr
    intro left
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (listQSum_mul_right
        (fun right =>
          (coefficient left * coefficient right) *
            centralSupportReflectedKernel w K half left right)
        reciprocal (centralHalfSupportSpace half))) ?_
    apply listQSum_congr
    intro right
    exact Q'.mul_assoc_eqv
      (coefficient left * coefficient right)
      (centralSupportReflectedKernel w K half left right)
      reciprocal

#print axioms centralPhysicalReflectionBilinear_eq_full
#print axioms centralSupportReflectedKernel_eq_bilinear
#print axioms centralSupportReflectedKernel_eq_slabWeighted
#print axioms centralSupportReflectedKernel_eq_physicalEventNumerator
#print axioms centralNormalizedSupportPairLaw_eq_physicalGivenSlab
#print axioms centralNormalizedSupportReflectionQuadratic_eq_jointLaw

end YMGap.Continuum.Z4HalfTimeReflectionSupportPairConditionalLaw
