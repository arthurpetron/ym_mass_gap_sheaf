/-
# Completion-injection producer for the fixed-reference Harnack gate

The fixed/adaptive raw-row Harnack comparison is a comparison of complete
reflected rows, not merely of their common six-face production factors.  This
module exposes a concrete sufficient producer: at every volume, inject every
positive target/boundary completion of the literal slice-zero source into a
completion of the adaptive minimum-row source, with one volume-independent
weight ceiling.

Constructive finite weighted summation then gives the required raw-row
Harnack inequality and feeds it directly into the fixed-reference tail-zero
gate.  The injection and its pointwise physical-weight bound are not
constructed here.  No time-translation symmetry, fixed spin-ray identity,
cofinal gap, continuum limit, or Clay theorem is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceHarnackGate
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceCompletionInjectionGate

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4LowSpinGrowingVolumeAdaptiveMinimumReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceHarnackGate
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal positive target/boundary completions -/

/-- The complete carrier summed by one positive raw row, flattened into
`(target, boundary)` pairs. -/
def lowSpinCentralCompletionPairs
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    List (EdgeLabelling × EdgeLabelling) :=
  cartesian
    (centralPositiveHalfStates
      w (Q'.le_of_lt hw) 1 (volume + 1))
    (centralBoundaryChannels 1 (volume + 1))

/-- The literal complete physical summand associated with a source and a
positive-target/boundary completion pair. -/
def lowSpinCentralCompletionWeight
    (w : Q') (volume : Nat) (source : EdgeLabelling)
    (completion : EdgeLabelling × EdgeLabelling) : Q' :=
  slabParametricKPhysicalTerm w 1 (centralExtent (volume + 1))
    (assembleReflectedSlabLabelling
      (volume + 1) source completion.2 completion.1)

theorem lowSpinCentralCompletionPairs_nodup
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    (lowSpinCentralCompletionPairs w hw volume).Nodup := by
  unfold lowSpinCentralCompletionPairs
  exact cartesian_nodup _ _
    (centralPositiveHalfStates_nodup
      w (Q'.le_of_lt hw) 1 (volume + 1))
    (centralBoundaryChannels_nodup 1 (volume + 1))

theorem lowSpinCentralCompletionWeight_nonnegative
    {w : Q'} (hw : (0 : Q') < w) (volume : Nat)
    (source : EdgeLabelling)
    (completion : EdgeLabelling × EdgeLabelling) :
    (0 : Q') ≤
      lowSpinCentralCompletionWeight w volume source completion := by
  unfold lowSpinCentralCompletionWeight
  exact slabParametricKPhysicalTerm_nonnegative
    (Q'.le_of_lt hw) 1 (centralExtent (volume + 1)) _

private theorem listQSum_cartesian_eq_nested_local
    {A B : Type} (value : A × B → Q')
    (left : List A) (right : List B) :
    listQSum value (cartesian left right) ≈
      listQSum
        (fun a => listQSum (fun b => value (a, b)) right)
        left := by
  unfold cartesian
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap value
      (fun a => right.map (fun b => (a, b))) left) ?_
  apply listQSum_congr
  intro a
  rw [listQSum_map]
  exact Q'.eqv_refl _

/-- The nested positive raw row is exactly the flattened completion sum. -/
theorem centralPhysicalPositiveRawRowMass_eqv_completionSum
    {w : Q'} (hw : (0 : Q') < w) (volume : Nat)
    (source : EdgeLabelling) :
    centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw) 1 (volume + 1) source ≈
      listQSum
        (lowSpinCentralCompletionWeight w volume source)
        (lowSpinCentralCompletionPairs w hw volume) := by
  unfold centralPhysicalPositiveRawRowMass
    lowSpinCentralCompletionPairs
    lowSpinCentralCompletionWeight
    centralPhysicalReflectedKernel
  exact Q'.eqv_symm
    (listQSum_cartesian_eq_nested_local
      (fun completion : EdgeLabelling × EdgeLabelling =>
        slabParametricKPhysicalTerm w 1
          (centralExtent (volume + 1))
          (assembleReflectedSlabLabelling
            (volume + 1) source completion.2 completion.1))
      (centralPositiveHalfStates
        w (Q'.le_of_lt hw) 1 (volume + 1))
      (centralBoundaryChannels 1 (volume + 1)))

/-! ## 2. The concrete uniform producer interface -/

/-- A volume-uniform weighted injection from all complete physical summands
of the literal slice-zero row into complete summands of the adaptive
minimum-row source. -/
structure LowSpinCentralFixedAdaptiveCompletionInjection
    (w : Q') (hw : (0 : Q') < w) : Type where
  ceiling : Q'
  one_le_ceiling : (1 : Q') ≤ ceiling
  encode : Nat →
    (EdgeLabelling × EdgeLabelling) →
      EdgeLabelling × EdgeLabelling
  encode_mem : ∀ volume completion,
    completion ∈ lowSpinCentralCompletionPairs w hw volume →
      encode volume completion ∈
        lowSpinCentralCompletionPairs w hw volume
  encode_injective : ∀ volume first,
    first ∈ lowSpinCentralCompletionPairs w hw volume →
      ∀ second,
        second ∈ lowSpinCentralCompletionPairs w hw volume →
          encode volume first = encode volume second →
            first = second
  fixedWeight_le : ∀ volume completion,
    completion ∈ lowSpinCentralCompletionPairs w hw volume →
      lowSpinCentralCompletionWeight w volume
          (lowSpinCentralReferenceState volume) completion ≤
        ceiling *
          lowSpinCentralCompletionWeight w volume
            (lowSpinCentralAdaptiveReferenceState w hw volume)
            (encode volume completion)

namespace LowSpinCentralFixedAdaptiveCompletionInjection

/-- A pointwise comparison on the identical target/boundary completion is a
special case of the completion-injection producer.  This is the endpoint for
an exact isolated-component factorization of the two low-spin sources. -/
def ofSameCompletionWeightBound
    {w : Q'} {hw : (0 : Q') < w}
    (ceiling : Q') (one_le_ceiling : (1 : Q') ≤ ceiling)
    (weight_le : ∀ volume completion,
      completion ∈ lowSpinCentralCompletionPairs w hw volume →
        lowSpinCentralCompletionWeight w volume
            (lowSpinCentralReferenceState volume) completion ≤
          ceiling *
            lowSpinCentralCompletionWeight w volume
              (lowSpinCentralAdaptiveReferenceState w hw volume)
              completion) :
    LowSpinCentralFixedAdaptiveCompletionInjection w hw where
  ceiling := ceiling
  one_le_ceiling := one_le_ceiling
  encode := fun _ completion => completion
  encode_mem := by
    intro _ completion hcompletion
    exact hcompletion
  encode_injective := by
    intro _ first _ second _ heq
    exact heq
  fixedWeight_le := weight_le

theorem ceiling_nonnegative
    {w : Q'} {hw : (0 : Q') < w}
    (injection :
      LowSpinCentralFixedAdaptiveCompletionInjection w hw) :
    (0 : Q') ≤ injection.ceiling :=
  Q'.le_trans' _ _ _ (by decide) injection.one_le_ceiling

/-- Finite weighted injectivity sums the pointwise producer into the desired
complete raw-row comparison. -/
theorem fixedRawRow_le_ceiling_mul_adaptive
    {w : Q'} {hw : (0 : Q') < w}
    (injection :
      LowSpinCentralFixedAdaptiveCompletionInjection w hw)
    (volume : Nat) :
    centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw) 1 (volume + 1)
          (lowSpinCentralReferenceState volume) ≤
      injection.ceiling *
        centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw) 1 (volume + 1)
          (lowSpinCentralAdaptiveReferenceState w hw volume) := by
  let completions := lowSpinCentralCompletionPairs w hw volume
  let fixedWeight := lowSpinCentralCompletionWeight w volume
    (lowSpinCentralReferenceState volume)
  let adaptiveWeight := lowSpinCentralCompletionWeight w volume
    (lowSpinCentralAdaptiveReferenceState w hw volume)
  have hsum :
      listQSum fixedWeight completions ≤
        listQSum
          (fun completion =>
            injection.ceiling *
              adaptiveWeight completion)
          completions := by
    apply listQSum_le_of_injective_nodup
      completions completions fixedWeight
      (fun completion =>
        injection.ceiling * adaptiveWeight completion)
      (injection.encode volume)
    · exact lowSpinCentralCompletionPairs_nodup w hw volume
    · exact lowSpinCentralCompletionPairs_nodup w hw volume
    · intro completion hcompletion
      exact injection.encode_mem volume completion hcompletion
    · intro first hfirst second hsecond heq
      exact injection.encode_injective volume first hfirst second hsecond heq
    · intro completion hcompletion
      exact injection.fixedWeight_le volume completion hcompletion
    · intro completion _hcompletion
      exact Q'.mul_nonneg _ _ injection.ceiling_nonnegative
        (lowSpinCentralCompletionWeight_nonnegative
          hw volume
          (lowSpinCentralAdaptiveReferenceState w hw volume)
          completion)
  have hfixed :=
    centralPhysicalPositiveRawRowMass_eqv_completionSum
      hw volume (lowSpinCentralReferenceState volume)
  have hadaptive :=
    centralPhysicalPositiveRawRowMass_eqv_completionSum
      hw volume
        (lowSpinCentralAdaptiveReferenceState w hw volume)
  have hfactor :
      listQSum
          (fun completion =>
            injection.ceiling * adaptiveWeight completion)
          completions ≈
        injection.ceiling * listQSum adaptiveWeight completions :=
    listQSum_mul_left injection.ceiling adaptiveWeight completions
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfixed)
    (Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ hfactor
          (Q'.mul_eqv_congr_left injection.ceiling _ _
            (Q'.eqv_symm hadaptive)))))

/-- A uniform completion injection is a producer for the previously isolated
fixed/adaptive raw-row Harnack input. -/
def toRawRowHarnack
    {w : Q'} {hw : (0 : Q') < w}
    (injection :
      LowSpinCentralFixedAdaptiveCompletionInjection w hw) :
    LowSpinCentralFixedAdaptiveRawRowHarnack w hw where
  ceiling := injection.ceiling
  one_le_ceiling := injection.one_le_ceiling
  fixed_le_ceiling_mul_adaptive :=
    injection.fixedRawRow_le_ceiling_mul_adaptive

end LowSpinCentralFixedAdaptiveCompletionInjection

end YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceCompletionInjectionGate

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceCompletionInjectionGate.centralPhysicalPositiveRawRowMass_eqv_completionSum
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceCompletionInjectionGate.LowSpinCentralFixedAdaptiveCompletionInjection.ofSameCompletionWeightBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceCompletionInjectionGate.LowSpinCentralFixedAdaptiveCompletionInjection.fixedRawRow_le_ceiling_mul_adaptive
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceCompletionInjectionGate.LowSpinCentralFixedAdaptiveCompletionInjection.toRawRowHarnack
