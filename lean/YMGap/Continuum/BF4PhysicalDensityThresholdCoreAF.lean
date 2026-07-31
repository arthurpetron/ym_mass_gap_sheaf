/-
# AF/Faraut construction of the physical BF4 threshold core

The executable core in `BF4PhysicalDensityThresholdCore` needs a weighted
centered-density row bound `1/4096`.  The retained BF4 Faraut spread costs
`4^(46 bits)`.  At nonlinear rate `q <= 1/4`, physical depth

    46 * bits + 8

leaves six quarter powers after the spread is paid, hence the exact
`1/4096` remainder.

This file proves that payment, cancels the strictly positive physical source
marginal, and constructs the scale-dependent `1/32` core with its two
`1/64` tails from the literal buffered physical BF4 row.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalDensityThresholdCore
import YMGap.Continuum.BF4MatchedBufferedPerronEighthClosure
import YMGap.Continuum.BF4FarautAnchoredProfileHarnack

namespace YMGap.Continuum.BF4PhysicalDensityThresholdCoreAF

set_option maxRecDepth 100000
set_option maxHeartbeats 200000

open YMGap.Constructive
open YMGap.Continuum.BF4BufferedPerronRowConvergence
open YMGap.Continuum.BF4CalibratedAnchoredProjectiveHarnack
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4FarautAnchoredProfileHarnack
open YMGap.Continuum.BF4FarautJointCarrierAFBudget
open YMGap.Continuum.BF4MatchedBufferedPerronEighthClosure
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalConditionalDensity
open YMGap.Continuum.BF4PhysicalConditionalDensityContraction
open YMGap.Continuum.BF4PhysicalDensityThresholdCore
open YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSignedKernelL1
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Six uncancelled quarter powers -/

/-- Depth leaving six quarter powers after the `46*bits` spread cost. -/
def farautCoreTailRequiredDepth (bits : Nat) : Nat :=
  46 * bits + 8

theorem farautCoreTailRequiredDepth_sub_two (bits : Nat) :
    farautCoreTailRequiredDepth bits - 2 =
      46 * bits + 6 := by
  unfold farautCoreTailRequiredDepth
  omega

/-- Three powers beyond the profile-Harnack budget sharpen `1/64` to
`1/4096`. -/
theorem fourPow_mul_qPow_le_coreRowTolerance
    {q : Q'} (hq0 : (0 : Q') ≤ q)
    (hqQuarter : q ≤ quarter)
    (K r : Nat) (hKr : K + 6 ≤ r) :
    four ^ K * q ^ r ≤ densityCoreRowTolerance := by
  have hstrong :
      four ^ (K + 3) * q ^ r ≤
        farautHarnackTolerance :=
    fourPow_mul_qPow_le_harnackTolerance
      hq0 hqQuarter (K + 3) r (by omega)
  have hscaled :
      farautHarnackTolerance *
          (four ^ (K + 3) * q ^ r) ≤
        farautHarnackTolerance *
          farautHarnackTolerance :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      hstrong (by
        unfold farautHarnackTolerance
        decide)
  have hcancelPower :
      farautHarnackTolerance * four ^ (K + 3) ≈
        four ^ K := by
    calc
      farautHarnackTolerance * four ^ (K + 3) ≈
          farautHarnackTolerance *
            (four ^ K * four ^ 3) :=
        Q'.mul_eqv_congr_left
          farautHarnackTolerance _ _
          (Q'.pow_add_eqv four K 3)
      _ ≈
          (farautHarnackTolerance * four ^ K) *
            four ^ 3 :=
        Q'.eqv_symm
          (Q'.mul_assoc_eqv
            farautHarnackTolerance
            (four ^ K) (four ^ 3))
      _ ≈
          (four ^ K * farautHarnackTolerance) *
            four ^ 3 :=
        Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_comm_eqv
            farautHarnackTolerance (four ^ K))
      _ ≈
          four ^ K *
            (farautHarnackTolerance * four ^ 3) :=
        Q'.mul_assoc_eqv
          (four ^ K) farautHarnackTolerance
          (four ^ 3)
      _ ≈ four ^ K * 1 :=
        Q'.mul_eqv_congr_left
          (four ^ K) _ _ (by
            unfold farautHarnackTolerance four
            decide)
      _ ≈ four ^ K :=
        Q'.mul_one_eqv _
  have hleft :
      farautHarnackTolerance *
          (four ^ (K + 3) * q ^ r) ≈
        four ^ K * q ^ r := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          farautHarnackTolerance
          (four ^ (K + 3))
          (q ^ r)))
      (Q'.mul_eqv_congr_right _ _ _
        hcancelPower)
  have hright :
      farautHarnackTolerance *
          farautHarnackTolerance ≈
        densityCoreRowTolerance := by
    unfold farautHarnackTolerance
      densityCoreRowTolerance
    decide
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv hright))

/-- The exact retained Faraut spread is paid down to `1/4096` at the new
depth. -/
theorem faraut_perron_coreTail_requiredDepth
    (bits : Nat) (qS : Q')
    (qS_nonnegative : (0 : Q') ≤ qS)
    (qS_le_quarter : qS ≤ quarter) :
    farautPerronSquare bits *
        qS ^ (farautCoreTailRequiredDepth bits - 2) ≤
      densityCoreRowTolerance := by
  have hcap := farautPerronSquare_le_cap bits
  have hqpow :
      (0 : Q') ≤
        qS ^ (farautCoreTailRequiredDepth bits - 2) :=
    Q'.pow_nonneg qS qS_nonnegative _
  have hproduct :
      farautPerronSquare bits *
          qS ^ (farautCoreTailRequiredDepth bits - 2) ≤
        four ^ (46 * bits) *
          qS ^ (farautCoreTailRequiredDepth bits - 2) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hcap hqpow
  have hdepth :
      46 * bits + 6 ≤
        farautCoreTailRequiredDepth bits - 2 := by
    rw [farautCoreTailRequiredDepth_sub_two]
    exact Nat.le_refl _
  exact Q'.le_trans' _ _ _ hproduct
    (fourPow_mul_qPow_le_coreRowTolerance
      qS_nonnegative qS_le_quarter
      (46 * bits)
      (farautCoreTailRequiredDepth bits - 2)
      hdepth)

/-- Every larger physical depth inherits the `1/4096` remainder. -/
theorem faraut_perron_coreTail_of_available_depth
    (bits : Nat) (qS : Q') (depth : Nat)
    (qS_nonnegative : (0 : Q') ≤ qS)
    (qS_le_quarter : qS ≤ quarter)
    (depth_available :
      farautCoreTailRequiredDepth bits ≤ depth) :
    farautPerronSquare bits *
        qS ^ (depth - 2) ≤
      densityCoreRowTolerance := by
  have hcap := farautPerronSquare_le_cap bits
  have hqpow :
      (0 : Q') ≤ qS ^ (depth - 2) :=
    Q'.pow_nonneg qS qS_nonnegative _
  have hproduct :
      farautPerronSquare bits * qS ^ (depth - 2) ≤
        four ^ (46 * bits) * qS ^ (depth - 2) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hcap hqpow
  have hdepth :
      46 * bits + 6 ≤ depth - 2 := by
    unfold farautCoreTailRequiredDepth at depth_available
    omega
  exact Q'.le_trans' _ _ _ hproduct
    (fourPow_mul_qPow_le_coreRowTolerance
      qS_nonnegative qS_le_quarter
      (46 * bits) (depth - 2) hdepth)

/-! ## 2. Cancel the positive physical source marginal -/

/-- A source-relative physical row bound is exactly the corresponding
canonical-density bound when the source belongs to the positive carrier. -/
theorem densityCenteredRowMass_le_of_physical
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half)
    {rate : Q'}
    (physical_bound :
      physicalCenteredPhysicalRowMass
          w hw K half source ≤
        rate *
          centralPhysicalRowMarginal
            w hw K half source) :
    finiteWeightedCenteredRowMass
        (centralPositiveHalfStates w hw K half)
        (centralPhysicalRowMarginal w hw K half)
        (centralPhysicalConditionalDensity w hw K half)
        source ≤
      rate := by
  let marginal :=
    centralPhysicalRowMarginal w hw K half source
  let densityMass :=
    finiteWeightedCenteredRowMass
      (centralPositiveHalfStates w hw K half)
      (centralPhysicalRowMarginal w hw K half)
      (centralPhysicalConditionalDensity w hw K half)
      source
  have hmarginal :
      (0 : Q') < marginal :=
    (mem_centralPositiveHalfStates_iff).1 source_mem |>.2
  have hidentity :=
    physicalCenteredPhysicalRowMass_eqv_densityCenteredRowMass
      source_mem
  have hscaled :
      marginal * densityMass ≤ marginal * rate := by
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hidentity)
      (Q'.le_trans' _ _ _ physical_bound
        (Q'.le_of_eqv
          (Q'.mul_comm_eqv rate marginal)))
  exact Q'.le_of_mul_le_mul_left hscaled hmarginal

/-- A literal buffered BF4 row at depth `46*bits+8` supplies the
`1/4096` canonical-density input of the threshold-core theorem. -/
theorem PhysicalBF4FarautBufferedRow.density_centered_row_le_coreTolerance
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    {bits depth : Nat} {qS : Q'}
    (row :
      PhysicalBF4FarautBufferedRow
        w hw K half source bits depth qS)
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half)
    (qS_nonnegative : (0 : Q') ≤ qS)
    (qS_le_quarter : qS ≤ quarter)
    (depth_available :
      farautCoreTailRequiredDepth bits ≤ depth) :
    finiteWeightedCenteredRowMass
        (centralPositiveHalfStates w hw K half)
        (centralPhysicalRowMarginal w hw K half)
        (centralPhysicalConditionalDensity w hw K half)
        source ≤
      densityCoreRowTolerance := by
  have hphysical :=
    physicalCenteredPhysicalRowMass_le_of_buffered
      row.certificate
  have hfaraut :=
    faraut_perron_coreTail_of_available_depth
      bits qS depth
      qS_nonnegative qS_le_quarter
      depth_available
  have hsourceNonnegative :
      (0 : Q') ≤
        centralPhysicalRowMarginal
          w hw K half source :=
    centralPhysicalRowMarginal_nonnegative
      hw K half source
  have hphysicalTolerance :
      physicalCenteredPhysicalRowMass
          w hw K half source ≤
        densityCoreRowTolerance *
          centralPhysicalRowMarginal
            w hw K half source :=
    Q'.le_trans' _ _ _ hphysical
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        hfaraut hsourceNonnegative)
  exact densityCenteredRowMass_le_of_physical
    source_mem hphysicalTolerance

/-- The same buffered row now constructs all three requested physical
core/tail fields. -/
def PhysicalBF4FarautBufferedRow.toThirtySecondCoreTailWindow
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    {bits depth : Nat} {qS : Q'}
    (row :
      PhysicalBF4FarautBufferedRow
        w hw K half source bits depth qS)
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half)
    (qS_nonnegative : (0 : Q') ≤ qS)
    (qS_le_quarter : qS ≤ quarter)
    (depth_available :
      farautCoreTailRequiredDepth bits ≤ depth) :
    PhysicalConditionalDensityCoreTailWindow
      w hw K half source
      (centralPhysicalThirtySecondCore
        w hw K half source) :=
  centralPhysicalThirtySecondCoreTailWindow
    source_mem
    (PhysicalBF4FarautBufferedRow.density_centered_row_le_coreTolerance
      row
      source_mem qS_nonnegative qS_le_quarter
      depth_available)

/-! ## 3. Scale-uniform construction on the matched AF carrier -/

/-- Existing matched buffered data at the deeper core-tail depth construct
the literal scale- and source-dependent threshold-core family. -/
def matchedThirtySecondCoreTailRows_of_buffered
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalBF4FarautBufferedRows
        family law spacing coupling
        halfExtent diagonalOrder)
    (core_depth_available :
      ∀ scale,
        farautCoreTailRequiredDepth
            (data.bits scale) ≤
          data.depth scale) :
    MatchedPhysicalConditionalDensityCoreTailRows
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  calibrated_harnack := data.calibrated_harnack
  inCore := fun scale source =>
    centralPhysicalThirtySecondCore
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale)
      source
  coreTail_exists := by
    intro scale source source_mem
    obtain ⟨row⟩ :=
      data.bufferedRow_exists
        scale source source_mem
    exact ⟨
      PhysicalBF4FarautBufferedRow.toThirtySecondCoreTailWindow
      row
        source_mem
        (data.nonlinearRate_nonnegative scale)
        (data.nonlinearRate_le_quarter scale)
        (core_depth_available scale)⟩

/-! ## 4. Calibrated profile Harnack on the identical trajectory -/

/-- Raw grouped-kernel data at one physical BF4 scale.

The output `CalibratedEmptyProfileHarnackData` is not a field.  It is
constructed below from this common positive-kernel action, the exact Faraut
spread, and the same `bits`, `depth`, and nonlinear rate used by the
threshold-core row. -/
structure BF4CalibratedProfileFarautAt
    {Source : Type}
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder bits depth : Nat)
    (qS : Q') : Type where
  kernel : Source → EdgeLabelling → Q'
  sources : List Source
  candidate : Source → Q'
  physical : Source → Q'
  certificate :
    FiniteCrossRatioDiameterCertificate
      kernel sources
      (BF4RetainedProfileStates
        w hw K halfExtent)
  candidateActivity :
    FiniteCrossRatioDiameterCertificate.NonzeroNonnegativeActivity
      sources candidate
  physicalActivity :
    FiniteCrossRatioDiameterCertificate.NonzeroNonnegativeActivity
      sources physical
  qS_nonnegative :
    (0 : Q') ≤ qS
  qS_le_quarter :
    qS ≤ quarter
  depth_available :
    farautCoreTailRequiredDepth bits ≤ depth
  projectivePerron :
    certificate.spread * certificate.spread ≤
      (1 : Q') +
        farautPerronSquare bits * qS ^ (depth - 2)
  candidate_identification :
    ∀ state,
      state ∈
          BF4RetainedProfileStates
            w hw K halfExtent →
        BF4CalibratedRightProfile
            w hw K halfExtent diagonalOrder state ≈
          FiniteCrossRatioDiameterCertificate.finiteKernelAction
            kernel sources candidate state
  physical_identification :
    ∀ state,
      state ∈
          BF4RetainedProfileStates
            w hw K halfExtent →
        BF4PhysicalProfile
            w hw K halfExtent state ≈
          FiniteCrossRatioDiameterCertificate.finiteKernelAction
            kernel sources physical state

namespace BF4CalibratedProfileFarautAt

/-- The deeper threshold-core depth automatically contains the calibrated
profile-Harnack depth. -/
theorem harnack_depth_available
    {Source : Type}
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder bits depth : Nat}
    {qS : Q'}
    (data :
      BF4CalibratedProfileFarautAt
        (Source := Source)
        w hw K halfExtent diagonalOrder
        bits depth qS) :
    farautHarnackRequiredDepth bits ≤ depth := by
  have hdepth := data.depth_available
  unfold farautCoreTailRequiredDepth at hdepth
  unfold farautHarnackRequiredDepth
  omega

/-- Instantiate both calibrated cross-zero pointwise `1/64` profile windows
from the common grouped kernel on this exact physical scale. -/
def toCalibratedHarnack
    {Source : Type}
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder bits depth : Nat}
    {qS : Q'}
    (data :
      BF4CalibratedProfileFarautAt
        (Source := Source)
        w hw K halfExtent diagonalOrder
        bits depth qS) :
    CalibratedEmptyProfileHarnackData
      w hw K halfExtent diagonalOrder 0 :=
  calibratedEmptyCrossZeroProfileHarnackData_of_farautKernelActions
    w hw K halfExtent diagonalOrder
    data.kernel data.sources
    data.candidate data.physical
    data.certificate
    data.candidateActivity
    data.physicalActivity
    bits qS depth
    data.qS_nonnegative
    data.qS_le_quarter
    data.harnack_depth_available
    data.projectivePerron
    data.candidate_identification
    data.physical_identification

end BF4CalibratedProfileFarautAt

/-- One common matched-AF construction containing:

* raw common-kernel data that construct the calibrated profile Harnack
  certificate;
* the literal buffered physical BF4 row at every retained source; and
* one shared bit/depth/nonlinear-rate schedule.

There is no `calibrated_harnack`, pointwise-core, or tail-bound field. -/
structure MatchedBF4ThresholdCoreFarautRows
    (ProfileSource : Nat → Type)
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  bits :
    Nat → Nat
  depth :
    Nat → Nat
  nonlinearRate :
    Nat → Q'
  profileAt :
    ∀ scale,
      BF4CalibratedProfileFarautAt
        (Source := ProfileSource scale)
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale)
        (bits scale)
        (depth scale)
        (nonlinearRate scale)
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

namespace MatchedBF4ThresholdCoreFarautRows

/-- The profile Harnack certificate at a scale is constructed from the same
bit/depth/rate data that pay the physical threshold-core tails. -/
def calibratedHarnackAt
    {ProfileSource : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedBF4ThresholdCoreFarautRows
        ProfileSource family law spacing coupling
        halfExtent diagonalOrder)
    (scale : Nat) :
    CalibratedEmptyProfileHarnackData
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale)
      (diagonalOrder scale) 0 :=
  (data.profileAt scale).toCalibratedHarnack

/-- **Combined construction.**  On the exact matched BF4 AF carrier this
inhabits:

* the calibrated profile Harnack certificate;
* the executable scale/source `1/32` physical density core;
* the stationary `1/64` tail; and
* the conditional `1/64` tail.

The Harnack and core use definitionally identical physical weight, cutoff,
bit schedule, nonlinear rate, and depth. -/
def toMatchedCoreTailRows
    {ProfileSource : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedBF4ThresholdCoreFarautRows
        ProfileSource family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicalConditionalDensityCoreTailRows
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  calibrated_harnack := data.calibratedHarnackAt
  inCore := fun scale source =>
    centralPhysicalThirtySecondCore
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale)
      source
  coreTail_exists := by
    intro scale source source_mem
    obtain ⟨row⟩ :=
      data.bufferedRow_exists
        scale source source_mem
    let profile := data.profileAt scale
    exact ⟨
      PhysicalBF4FarautBufferedRow.toThirtySecondCoreTailWindow
        row source_mem
        profile.qS_nonnegative
        profile.qS_le_quarter
        profile.depth_available⟩

/-- Consequently the constructed core and calibrated profile Harnack
inhabit both matched rowwise eighth estimates. -/
def toRowwiseEighthEstimates
    {ProfileSource : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedBF4ThresholdCoreFarautRows
        ProfileSource family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  data.toMatchedCoreTailRows.toRowwiseEighthEstimates

end MatchedBF4ThresholdCoreFarautRows

end YMGap.Continuum.BF4PhysicalDensityThresholdCoreAF

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalDensityThresholdCoreAF.fourPow_mul_qPow_le_coreRowTolerance
#print axioms YMGap.Continuum.BF4PhysicalDensityThresholdCoreAF.faraut_perron_coreTail_of_available_depth
#print axioms YMGap.Continuum.BF4PhysicalDensityThresholdCoreAF.densityCenteredRowMass_le_of_physical
#print axioms YMGap.Continuum.BF4PhysicalDensityThresholdCoreAF.PhysicalBF4FarautBufferedRow.density_centered_row_le_coreTolerance
#print axioms YMGap.Continuum.BF4PhysicalDensityThresholdCoreAF.PhysicalBF4FarautBufferedRow.toThirtySecondCoreTailWindow
#print axioms YMGap.Continuum.BF4PhysicalDensityThresholdCoreAF.matchedThirtySecondCoreTailRows_of_buffered
#print axioms YMGap.Continuum.BF4PhysicalDensityThresholdCoreAF.BF4CalibratedProfileFarautAt.toCalibratedHarnack
#print axioms YMGap.Continuum.BF4PhysicalDensityThresholdCoreAF.MatchedBF4ThresholdCoreFarautRows.calibratedHarnackAt
#print axioms YMGap.Continuum.BF4PhysicalDensityThresholdCoreAF.MatchedBF4ThresholdCoreFarautRows.toMatchedCoreTailRows
#print axioms YMGap.Continuum.BF4PhysicalDensityThresholdCoreAF.MatchedBF4ThresholdCoreFarautRows.toRowwiseEighthEstimates
