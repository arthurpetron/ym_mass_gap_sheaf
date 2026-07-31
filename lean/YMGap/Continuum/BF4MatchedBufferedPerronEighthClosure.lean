/-
# Spacing-uniform closure of the support-safe BF4 buffered Perron rows

The half-amplitude cross-ratio route is intentionally stronger than needed:
a strictly positive terminal comparison would force every selected
source/boundary half-amplitude entry to be positive.  The physical BF4
carrier can instead contain fusion zeros.

`BF4BufferedPerronRowConvergence` supplies the support-safe argument.  It
factors the centered, conditionally integrated physical Choi row through

  endpoint buffer -> contracted middle -> endpoint buffer

and proves the sharp row estimate

  C_bits^2 q^(depth-2) * pi(source).

This file packages one witness-bearing factorization for every retained row
and every AF scale.  The existing Faraut depth theorem then supplies the
physical centered `1/16`; calibrated cross-zero Harnack combines with it to
inhabit both requested rowwise `1/8` fields.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4BufferedPerronRowConvergence
import YMGap.Continuum.BF4LocalContractionGluing

namespace YMGap.Continuum.BF4MatchedBufferedPerronEighthClosure

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4BufferedPerronRowConvergence
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4FarautJointCarrierAFBudget
open YMGap.Continuum.BF4LocalContractionGluing
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## One complete spacing-uniform buffered family -/

/-- The exact remaining support-safe analytic datum.

The carrier of each row factorization is witness-bearing inside
`PhysicalBF4FarautBufferedRow`; hence the `Left` and `Middle` types can be
chosen constructively and independently at every row and scale without
choice. -/
structure MatchedPhysicalBF4FarautBufferedRows
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
  bits :
    Nat → Nat
  depth :
    Nat → Nat
  nonlinearRate :
    Nat → Q'
  nonlinearRate_nonnegative :
    ∀ scale, (0 : Q') ≤ nonlinearRate scale
  nonlinearRate_le_quarter :
    ∀ scale, nonlinearRate scale ≤ quarter
  depth_available :
    ∀ scale,
      farautHarnackRequiredDepth (bits scale) ≤
        depth scale
  bufferedRow_exists :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        Nonempty
          (PhysicalBF4FarautBufferedRow
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)
            source
            (bits scale)
            (depth scale)
            (nonlinearRate scale))

namespace MatchedPhysicalBF4FarautBufferedRows

/-- Every witness-bearing physical row factorization gives the common
spacing-uniform physical centered `1/16` field. -/
theorem physical_centered_row_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalBF4FarautBufferedRows
        family law spacing coupling
        halfExtent diagonalOrder)
    (scale : Nat) (source : EdgeLabelling)
    (source_mem :
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)) :
    physicalCenteredPhysicalRowMass
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale) source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale) source := by
  obtain ⟨row⟩ :=
    data.bufferedRow_exists
      scale source source_mem
  exact row.centered_row_le_sixteenth
      (data.nonlinearRate_nonnegative scale)
      (data.nonlinearRate_le_quarter scale)
      (data.depth_available scale)

/-- The matched buffered family forgets to the exact two-field consumer
without changing the physical kernel, AF trajectory, or row carrier. -/
def toCrossZeroPhysicalSixteenthRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalBF4FarautBufferedRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedCrossZeroPhysicalSixteenthRows
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  harnack := data.calibrated_harnack
  physical_centered_row_sixteenth :=
    data.physical_centered_row_sixteenth

/-- Therefore the support-safe buffered physical construction inhabits both
spacing-uniform `1/8` fields. -/
def toRowwiseEighthEstimates
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalBF4FarautBufferedRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  data.toCrossZeroPhysicalSixteenthRows
    |>.toRowwiseEighthEstimates

/-- The two proved row eighths give the physical mean-zero quarter
contraction at every spacing scale. -/
theorem physical_quarter_uniform
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalBF4FarautBufferedRows
        family law spacing coupling
        halfExtent diagonalOrder)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (mean_zero :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        observable) :
    Q'.abs
        (centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)
            observable)) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable observable :=
  data.toRowwiseEighthEstimates
    |>.physical_quarter_uniform
      scale observable mean_zero

end MatchedPhysicalBF4FarautBufferedRows

/-! ## Reduction to one genuine stationary BF4 slice -/

/-- A spacing-uniform family of genuine local BF4 transfer densities.

Unlike `MatchedPhysicalBF4FarautBufferedRows`, this structure does not ask
for an already-centered buffer factorization or any endpoint Harnack
constant.  At each retained row it asks only for:

* one stationary one-slice density on the exact positive physical carrier;
* exact all-label gluing of its full transfer power to the physical
  conditional density; and
* a local weighted centered-row contraction.

`BF4LocalContractionGluing` proves that the same local contraction pays both
endpoint buffers and every middle power.  Thus `q <= 1/4` already gives the
physical `1/16` row, with no carrier-size or minimum-marginal loss.

The witness is wrapped in `Nonempty` because every consumer below is a
proposition.  This permits constructive elimination without selecting a
scale-indexed family of kernels. -/
structure MatchedPhysicalBF4LocalContractionRows
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
  depth :
    Nat → Nat
  localRate :
    Nat → Q'
  localRate_le_quarter :
    ∀ scale, localRate scale ≤ quarter
  localRow_exists :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        Nonempty
          (Σ oneStep :
              EdgeLabelling → EdgeLabelling → Q',
            PhysicalBF4LocalContractionGluingRow
              (matchedAllSpinWeight_nonnegative
                family coupling scale)
              (matchedAllSpinCutoff family coupling scale)
              (halfExtent scale)
              source
              (depth scale)
              oneStep
              (localRate scale))

namespace MatchedPhysicalBF4LocalContractionRows

/-- Local quarter contraction plus exact physical transfer gluing gives the
spacing-uniform physical centered `1/16` row. -/
theorem physical_centered_row_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalBF4LocalContractionRows
        family law spacing coupling
        halfExtent diagonalOrder)
    (scale : Nat) (source : EdgeLabelling)
    (source_mem :
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)) :
    physicalCenteredPhysicalRowMass
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale) source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale) source := by
  obtain ⟨⟨oneStep, row⟩⟩ :=
    data.localRow_exists scale source source_mem
  exact row.physical_centered_row_le_sixteenth
    (data.localRate_le_quarter scale)

/-- Forgetting the explicit one-slice witness yields the exact two-field
consumer used by the physical quarter theorem. -/
def toCrossZeroPhysicalSixteenthRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalBF4LocalContractionRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedCrossZeroPhysicalSixteenthRows
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  harnack := data.calibrated_harnack
  physical_centered_row_sixteenth :=
    data.physical_centered_row_sixteenth

/-- The local physical transfer construction inhabits both requested
spacing-uniform rowwise `1/8` estimates. -/
def toRowwiseEighthEstimates
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalBF4LocalContractionRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  data.toCrossZeroPhysicalSixteenthRows
    |>.toRowwiseEighthEstimates

/-- Consequently the exact BF4 transfer power has uniform physical
mean-zero contraction at most `1/4`. -/
theorem physical_quarter_uniform
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalBF4LocalContractionRows
        family law spacing coupling
        halfExtent diagonalOrder)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (mean_zero :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        observable) :
    Q'.abs
        (centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)
            observable)) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable observable :=
  data.toRowwiseEighthEstimates
    |>.physical_quarter_uniform
      scale observable mean_zero

end MatchedPhysicalBF4LocalContractionRows

end YMGap.Continuum.BF4MatchedBufferedPerronEighthClosure

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4MatchedBufferedPerronEighthClosure.MatchedPhysicalBF4FarautBufferedRows.physical_centered_row_sixteenth
#print axioms YMGap.Continuum.BF4MatchedBufferedPerronEighthClosure.MatchedPhysicalBF4FarautBufferedRows.toCrossZeroPhysicalSixteenthRows
#print axioms YMGap.Continuum.BF4MatchedBufferedPerronEighthClosure.MatchedPhysicalBF4FarautBufferedRows.toRowwiseEighthEstimates
#print axioms YMGap.Continuum.BF4MatchedBufferedPerronEighthClosure.MatchedPhysicalBF4FarautBufferedRows.physical_quarter_uniform
#print axioms YMGap.Continuum.BF4MatchedBufferedPerronEighthClosure.MatchedPhysicalBF4LocalContractionRows.physical_centered_row_sixteenth
#print axioms YMGap.Continuum.BF4MatchedBufferedPerronEighthClosure.MatchedPhysicalBF4LocalContractionRows.toCrossZeroPhysicalSixteenthRows
#print axioms YMGap.Continuum.BF4MatchedBufferedPerronEighthClosure.MatchedPhysicalBF4LocalContractionRows.toRowwiseEighthEstimates
#print axioms YMGap.Continuum.BF4MatchedBufferedPerronEighthClosure.MatchedPhysicalBF4LocalContractionRows.physical_quarter_uniform
