/-
# Retained Feynman--Kac Harnack to the physical BF4 half-amplitude

The literal spin-foam half-amplitude can contain fusion zeros.  Therefore
the useful analytic statement is not strict positivity of every microscopic
entry, but a zero-tolerant division-free cross-ratio estimate after the
complete retained carrier has been conditionally integrated.

This file proves two closure steps:

* symmetric retained kinetic Harnack order survives an arbitrary
  nonnegative interior Feynman--Kac potential as a matrix cross-ratio bound;
* an exact entrywise identification of that grouped kernel with the physical
  BF4 half-amplitude transfers the bound without division or positivity.

The spacing-uniform package then feeds the one-field consumer from
`BF4PhysicalHalfAmplitudeProjectiveClosure`, and hence both requested
physical rowwise eighths.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure
import YMGap.Continuum.BF4RetainedPathConditionalOrder

namespace YMGap.Continuum.BF4PhysicalHalfAmplitudeRetainedHarnackBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure
open YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4RetainedPathConditionalOrder
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem mul_swap4_local
    (a b c d : Q') :
    (a * b) * (c * d) ≈
      (a * c) * (b * d) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _
    ?_ (Q'.eqv_symm
      (Q'.mul_assoc_eqv a c (b * d)))
  apply Q'.mul_eqv_congr_left
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv b c d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ d
      (Q'.mul_comm_eqv b c)) ?_
  exact Q'.mul_assoc_eqv c b d

/-! ## 1. Zero-tolerant grouped cross-ratio closure -/

/-- Symmetric retained kinetic Harnack order gives a division-free matrix
cross-ratio bound after conditional integration.  Unlike the strict
certificate constructor, this theorem permits structural zero entries. -/
theorem feynmanKac_crossRatio_of_retainedKineticHarnack
    {Source Target State : Type}
    (paths : List (List State))
    (kineticWeight :
      Source → Target → List State → Q')
    (potential : State → Q')
    (sources : List Source) (targets : List Target)
    (data :
      RetainedKineticHarnackData
        paths kineticWeight sources targets)
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state) :
    ∀ first, first ∈ sources →
      ∀ second, second ∈ sources →
        ∀ left, left ∈ targets →
          ∀ right, right ∈ targets →
            feynmanKacPathKernel
                  paths kineticWeight potential first left *
                feynmanKacPathKernel
                  paths kineticWeight potential second right ≤
              (data.spread * data.spread) *
                (feynmanKacPathKernel
                    paths kineticWeight potential first right *
                  feynmanKacPathKernel
                    paths kineticWeight potential second left) := by
  intro first first_mem second second_mem
    left left_mem right right_mem
  have hfirstLeft :=
    feynmanKac_of_retainedKineticDomination
      paths kineticWeight potential sources targets
      data potential_nonnegative
      first first_mem second second_mem
      left left_mem
  have hsecondRight :=
    feynmanKac_of_retainedKineticDomination
      paths kineticWeight potential sources targets
      data potential_nonnegative
      second second_mem first first_mem
      right right_mem
  have hsecondRight_nonnegative :
      (0 : Q') ≤
        feynmanKacPathKernel
          paths kineticWeight potential second right :=
    retainedPathFeynmanKac_nonnegative
      paths kineticWeight potential sources targets
      data potential_nonnegative
      second second_mem right right_mem
  have hscaledSecondLeft_nonnegative :
      (0 : Q') ≤
        data.spread *
          feynmanKacPathKernel
            paths kineticWeight potential second left :=
    Q'.mul_nonneg _ _
      data.spread_nonnegative
      (retainedPathFeynmanKac_nonnegative
        paths kineticWeight potential sources targets
        data potential_nonnegative
        second second_mem left left_mem)
  have hproduct :
      feynmanKacPathKernel
            paths kineticWeight potential first left *
          feynmanKacPathKernel
            paths kineticWeight potential second right ≤
        (data.spread *
            feynmanKacPathKernel
              paths kineticWeight potential second left) *
          (data.spread *
            feynmanKacPathKernel
              paths kineticWeight potential first right) :=
    Q'.mul_le_mul_of_nonneg
      hfirstLeft hsecondRight
      hscaledSecondLeft_nonnegative
      hsecondRight_nonnegative
  exact Q'.le_trans' _ _ _ hproduct
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (mul_swap4_local
          data.spread
          (feynmanKacPathKernel
            paths kineticWeight potential second left)
          data.spread
          (feynmanKacPathKernel
            paths kineticWeight potential first right))
        (Q'.mul_eqv_congr_left
          (data.spread * data.spread) _ _
          (Q'.mul_comm_eqv
            (feynmanKacPathKernel
              paths kineticWeight potential second left)
            (feynmanKacPathKernel
              paths kineticWeight potential first right)))))

/-- Entrywise setoid identification transfers a grouped cross-ratio bound
to the physical kernel. -/
theorem crossRatio_of_entrywise_grouped_identification
    {Source Target : Type}
    (physical grouped : Source → Target → Q')
    (sources : List Source) (targets : List Target)
    (spread : Q')
    (grouped_cross_ratio :
      ∀ first, first ∈ sources →
        ∀ second, second ∈ sources →
          ∀ left, left ∈ targets →
            ∀ right, right ∈ targets →
              grouped first left * grouped second right ≤
                (spread * spread) *
                  (grouped first right *
                    grouped second left))
    (identification :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          physical source target ≈
            grouped source target) :
    ∀ first, first ∈ sources →
      ∀ second, second ∈ sources →
        ∀ left, left ∈ targets →
          ∀ right, right ∈ targets →
            physical first left * physical second right ≤
              (spread * spread) *
                (physical first right *
                  physical second left) := by
  intro first first_mem second second_mem
    left left_mem right right_mem
  have hforward :
      physical first left * physical second right ≈
        grouped first left * grouped second right :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        (physical first left)
        (grouped first left)
        (physical second right)
        (identification first first_mem left left_mem))
      (Q'.mul_eqv_congr_left
        (grouped first left)
        (physical second right)
        (grouped second right)
        (identification second second_mem right right_mem))
  have hreverse :
      grouped first right * grouped second left ≈
        physical first right * physical second left :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        (grouped first right)
        (physical first right)
        (grouped second left)
        (Q'.eqv_symm
          (identification first first_mem right right_mem)))
      (Q'.mul_eqv_congr_left
        (physical first right)
        (grouped second left)
        (physical second left)
        (Q'.eqv_symm
          (identification second second_mem left left_mem)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hforward)
    (Q'.le_trans' _ _ _
      (grouped_cross_ratio
        first first_mem second second_mem
        left left_mem right right_mem)
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          (spread * spread) _ _ hreverse)))

/-- A retained Feynman--Kac realization of the physical half-amplitude
inherits the retained kinetic spread, with structural zeros allowed. -/
theorem physicalHalfAmplitude_crossRatio_of_retainedRealization
    {Source Target State : Type}
    (physical : Source → Target → Q')
    (paths : List (List State))
    (kineticWeight :
      Source → Target → List State → Q')
    (potential : State → Q')
    (sources : List Source) (targets : List Target)
    (data :
      RetainedKineticHarnackData
        paths kineticWeight sources targets)
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (identification :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          physical source target ≈
            feynmanKacPathKernel
              paths kineticWeight potential source target) :
    ∀ first, first ∈ sources →
      ∀ second, second ∈ sources →
        ∀ left, left ∈ targets →
          ∀ right, right ∈ targets →
            physical first left * physical second right ≤
              (data.spread * data.spread) *
                (physical first right *
                  physical second left) :=
  crossRatio_of_entrywise_grouped_identification
    physical
    (feynmanKacPathKernel
      paths kineticWeight potential)
    sources targets data.spread
    (feynmanKac_crossRatio_of_retainedKineticHarnack
      paths kineticWeight potential sources targets
      data potential_nonnegative)
    identification

/-! ## 2. Spacing-uniform physical consumer -/

/-- Exact physical realization plus a spacing-uniform retained kinetic
Harnack window.  The retained state type may change with the spacing scale,
which permits the genuine cutoff-dependent joint carrier. -/
structure MatchedPhysicalHalfAmplitudeRetainedHarnackRows
    (PathState : Nat → Type)
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  calibrated_harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale) 0
  paths :
    ∀ scale, List (List (PathState scale))
  kinetic :
    ∀ scale,
      EdgeLabelling → EdgeLabelling →
        List (PathState scale) → Q'
  potential :
    ∀ scale, PathState scale → Q'
  retained_harnack :
    ∀ scale,
      RetainedKineticHarnackData
        (paths scale)
        (kinetic scale)
        (centralPositiveHalfStates
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (centralBoundaryChannels
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
  potential_nonnegative :
    ∀ scale state,
      (0 : Q') ≤ potential scale state
  spread_square_le :
    ∀ scale,
      (retained_harnack scale).spread *
          (retained_harnack scale).spread ≤
        anchoredProjectiveCeiling
  physical_identification :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        ∀ boundary,
          boundary ∈
              centralBoundaryChannels
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) →
            centralHalfAmplitude
                (matchedAllSpinWeight family coupling scale)
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) source boundary ≈
              feynmanKacPathKernel
                (paths scale)
                (kinetic scale)
                (potential scale)
                source boundary

namespace MatchedPhysicalHalfAmplitudeRetainedHarnackRows

/-- The retained physical realization inhabits the single half-amplitude
projective field. -/
def toHalfAmplitudeProjectiveRows
    {PathState : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalHalfAmplitudeRetainedHarnackRows
        PathState family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedHalfAmplitudeProjectiveRows
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  harnack := data.calibrated_harnack
  spread := fun scale =>
    (data.retained_harnack scale).spread
  spread_square_le := data.spread_square_le
  half_amplitude_cross_ratio := by
    intro scale
    exact
      physicalHalfAmplitude_crossRatio_of_retainedRealization
        (centralHalfAmplitude
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (data.paths scale)
        (data.kinetic scale)
        (data.potential scale)
        (centralPositiveHalfStates
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (centralBoundaryChannels
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (data.retained_harnack scale)
        (data.potential_nonnegative scale)
        (data.physical_identification scale)

/-- The complete grouped-kernel route to both spacing-uniform physical
rowwise eighths. -/
def toRowwiseEighthEstimates
    {PathState : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalHalfAmplitudeRetainedHarnackRows
        PathState family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  data.toHalfAmplitudeProjectiveRows
    |>.toRowwiseEighthEstimates

end MatchedPhysicalHalfAmplitudeRetainedHarnackRows

end YMGap.Continuum.BF4PhysicalHalfAmplitudeRetainedHarnackBridge

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeRetainedHarnackBridge.feynmanKac_crossRatio_of_retainedKineticHarnack
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeRetainedHarnackBridge.crossRatio_of_entrywise_grouped_identification
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeRetainedHarnackBridge.physicalHalfAmplitude_crossRatio_of_retainedRealization
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeRetainedHarnackBridge.MatchedPhysicalHalfAmplitudeRetainedHarnackRows.toHalfAmplitudeProjectiveRows
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeRetainedHarnackBridge.MatchedPhysicalHalfAmplitudeRetainedHarnackRows.toRowwiseEighthEstimates
