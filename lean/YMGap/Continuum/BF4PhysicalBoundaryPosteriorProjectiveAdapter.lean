/-
# BF4 adapter from normalized projective order to posterior quarters

This file specializes the dimension-free normalized-projective theorem to
the two genuine physical BF4 boundary posteriors.  It uses the argument-form
interface so that Lean does not construct or normalize a giant dependent
certificate record.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4NormalizedProjectivePosteriorHarnack

namespace YMGap.Continuum.BF4PhysicalBoundaryPosteriorProjectiveAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
open YMGap.Continuum.BF4BufferedPerronRowConvergence
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4NormalizedProjectivePosteriorHarnack
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryPosterior
open YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-- Squared projective spread at most `65/64` for the raw half-amplitude
ray against the physical marginal implies the unnormalized target-profile
quarter.  On positive interfaces this passes through the normalized
posterior; zero-mass interfaces are discharged by nonnegativity. -/
theorem centralBoundaryTargetProfileDeviation_le_quarter_of_rawProjective
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K half : Nat} {boundary : EdgeLabelling}
    (spread : Q')
    (spreadSquare_le :
      spread * spread ≤ anchoredProjectiveCeiling)
    (rawProjective :
      FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
        spread
        (centralPositiveHalfStates w hw K half)
        (fun target =>
          centralHalfAmplitude w K half target boundary)
        (centralPhysicalRowMarginal w hw K half)) :
    centralBoundaryTargetProfileDeviation
        w hw K half boundary ≤
      quarter *
        centralPositiveBoundaryTotalHalfAmplitude
          w hw K half boundary := by
  apply
    centralBoundaryTargetProfileDeviation_le_quarter_of_posteriorL1
  intro boundaryTotal_pos
  unfold centralTargetGivenBoundaryL1
  apply finiteL1Distance_le_quarter_of_normalized_projective
    (centralPositiveHalfStates w hw K half)
    (centralTargetGivenBoundary
      w hw K half boundary boundaryTotal_pos)
    (centralPhysicalRowMarginal w hw K half)
    spread
  · intro target _
    exact centralTargetGivenBoundary_nonnegative
      hw K half boundary boundaryTotal_pos target
  · intro target _
    exact centralPhysicalRowMarginal_nonnegative
      hw K half target
  · exact centralTargetGivenBoundary_total_one
      boundaryTotal_pos
  · exact centralPositiveRowMarginal_total_one
      w hw K half
  · exact spreadSquare_le
  · intro left left_mem right right_mem
    have hraw :=
      rawProjective
        left left_mem right right_mem
    have hscaled :=
      Q'.mul_le_mul_of_nonneg_right _ _ _
        hraw
        (Q'.le_of_lt
          (Q'.recipPos_pos _ boundaryTotal_pos))
    unfold centralTargetGivenBoundary
      finiteStateGivenChannel Q'.divPos
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv ?_)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv ?_))
    · q_ring
    · q_ring

/-- Squared projective spread at most `65/64` implies the boundary-given-
source posterior quarter. -/
theorem centralBoundaryGivenSourceL1_le_quarter_of_projective
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K half : Nat} {source : EdgeLabelling}
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half)
    (spread : Q')
    (spreadSquare_le :
      spread * spread ≤ anchoredProjectiveCeiling)
    (projective :
      FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
        spread
        (centralBoundaryChannels K half)
        (centralBoundaryGivenSource
          w hw K half source source_mem)
        (centralBoundaryPrior w hw K half)) :
    centralBoundaryGivenSourceL1
        w hw K half source source_mem ≤
      quarter := by
  unfold centralBoundaryGivenSourceL1
  apply finiteL1Distance_le_quarter_of_normalized_projective
    (centralBoundaryChannels K half)
    (centralBoundaryGivenSource
      w hw K half source source_mem)
    (centralBoundaryPrior w hw K half)
    spread
  · intro boundary boundary_mem
    exact centralBoundaryGivenSource_nonnegative_on
      hw source_mem boundary_mem
  · intro boundary boundary_mem
    exact centralBoundaryPrior_nonnegative_on
      hw boundary_mem
  · exact centralBoundaryGivenSource_total_one
      source_mem
  · exact centralBoundaryPrior_total_one
      w hw K half
  · exact spreadSquare_le
  · exact projective

/-! ## Raw numerator rays -/

/-- Unnormalized numerator of the interface posterior conditioned on a
retained lower source. -/
def centralBoundaryGivenSourceNumerator
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (source boundary : EdgeLabelling) : Q' :=
  centralBoundaryWeight w K half boundary *
    (centralHalfAmplitude w K half source boundary *
      centralPositiveBoundaryTotalHalfAmplitude
        w hw K half boundary)

/-- Unnormalized numerator of the square-amplitude boundary prior. -/
def centralBoundaryPriorNumerator
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (boundary : EdgeLabelling) : Q' :=
  centralBoundaryWeight w K half boundary *
    (centralPositiveBoundaryTotalHalfAmplitude
        w hw K half boundary *
      centralPositiveBoundaryTotalHalfAmplitude
        w hw K half boundary)

/-- Projective control of the two raw boundary numerator rays implies the
second unnormalized physical quarter profile.  Both global partition
normalizations cancel from the cross ratio. -/
theorem centralSourceBoundaryProfileDeviation_le_quarter_of_rawProjective
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K half : Nat} {source : EdgeLabelling}
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half)
    (spread : Q')
    (spreadSquare_le :
      spread * spread ≤ anchoredProjectiveCeiling)
    (rawProjective :
      FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
        spread
        (centralBoundaryChannels K half)
        (centralBoundaryGivenSourceNumerator
          w hw K half source)
        (centralBoundaryPriorNumerator
          w hw K half)) :
    centralSourceBoundaryProfileDeviation
        w hw K half source ≤
      quarter *
        (slabParametricKPhysicalPartition
            w K (centralExtent half) *
          centralPhysicalRowMarginal
            w hw K half source) := by
  apply
    centralSourceBoundaryProfileDeviation_le_quarter_of_posteriorL1
      source_mem
  apply centralBoundaryGivenSourceL1_le_quarter_of_projective
    hw source_mem spread spreadSquare_le
  intro left left_mem right right_mem
  have hraw :=
    rawProjective
      left left_mem right right_mem
  let rowMass :=
    slabParametricKPhysicalPartition
        w K (centralExtent half) *
      centralPhysicalRowMarginal
        w hw K half source
  let rowMass_pos :=
    Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        hw K (centralExtent half))
      ((mem_centralPositiveHalfStates_iff.mp source_mem).2)
  let partition :=
    slabParametricKPhysicalPartition
      w K (centralExtent half)
  let partition_pos :=
    slabParametricKPhysicalPartition_pos
      hw K (centralExtent half)
  let scale :=
    Q'.recipPos rowMass rowMass_pos *
      Q'.recipPos partition partition_pos
  have hscale : (0 : Q') ≤ scale :=
    Q'.mul_nonneg _ _
      (Q'.le_of_lt
        (Q'.recipPos_pos rowMass rowMass_pos))
      (Q'.le_of_lt
        (Q'.recipPos_pos partition partition_pos))
  have hscaled :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hraw hscale
  unfold scale rowMass partition at hscaled
  unfold centralBoundaryGivenSourceNumerator
    centralBoundaryPriorNumerator at hscaled
  unfold centralBoundaryGivenSource
    centralBoundaryPrior
    Q'.divPos
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv ?_)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv ?_))
  · q_ring
  · q_ring

/-- **Physical raw-projective sixteenth.**  Division-free projective
diameter `65/64` bounds for every target half-amplitude ray and for the
source/prior boundary numerator rays imply the exact physical centered-row
sixteenth. -/
theorem physicalCenteredPhysicalRowMass_le_sixteenth_of_rawProjective
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K half : Nat} {source : EdgeLabelling}
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half)
    (targetSpread : EdgeLabelling → Q')
    (targetSpreadSquare_le :
      ∀ boundary,
        boundary ∈ centralBoundaryChannels K half →
          targetSpread boundary * targetSpread boundary ≤
            anchoredProjectiveCeiling)
    (targetRawProjective :
      ∀ boundary,
        boundary ∈ centralBoundaryChannels K half →
          FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
            (targetSpread boundary)
            (centralPositiveHalfStates w hw K half)
            (fun target =>
              centralHalfAmplitude w K half target boundary)
            (centralPhysicalRowMarginal w hw K half))
    (sourceSpread : Q')
    (sourceSpreadSquare_le :
      sourceSpread * sourceSpread ≤ anchoredProjectiveCeiling)
    (sourceRawProjective :
      FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
        sourceSpread
        (centralBoundaryChannels K half)
        (centralBoundaryGivenSourceNumerator
          w hw K half source)
        (centralBoundaryPriorNumerator
          w hw K half)) :
    physicalCenteredPhysicalRowMass
        w hw K half source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          w hw K half source := by
  apply physicalCenteredPhysicalRowMass_le_sixteenth_of_quarterProfiles
    source_mem
  · intro boundary boundary_mem
    exact
      centralBoundaryTargetProfileDeviation_le_quarter_of_rawProjective
        hw
        (targetSpread boundary)
        (targetSpreadSquare_le boundary boundary_mem)
        (targetRawProjective boundary boundary_mem)
  · exact
      centralSourceBoundaryProfileDeviation_le_quarter_of_rawProjective
        hw source_mem sourceSpread sourceSpreadSquare_le
        sourceRawProjective

/-! ## Spacing-uniform AF trajectory consumer -/

/-- The spacing-uniform Yang--Mills input in literal division-free form.
Every field is stated on the genuine BF4 state or interface carrier. -/
structure MatchedBoundaryRawProjectiveRows
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale) 0
  target_spread :
    Nat → EdgeLabelling → Q'
  target_spread_square_le :
    ∀ scale boundary,
      boundary ∈
          centralBoundaryChannels
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        target_spread scale boundary *
            target_spread scale boundary ≤
          anchoredProjectiveCeiling
  target_raw_projective :
    ∀ scale boundary,
      boundary ∈
          centralBoundaryChannels
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
          (target_spread scale boundary)
          (centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale))
          (fun target =>
            centralHalfAmplitude
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinCutoff family coupling scale)
              (halfExtent scale) target boundary)
          (centralPhysicalRowMarginal
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale))
  source_spread :
    Nat → EdgeLabelling → Q'
  source_spread_square_le :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        source_spread scale source *
            source_spread scale source ≤
          anchoredProjectiveCeiling
  source_raw_projective :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
          (source_spread scale source)
          (centralBoundaryChannels
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale))
          (centralBoundaryGivenSourceNumerator
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) source)
          (centralBoundaryPriorNumerator
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale))

namespace MatchedBoundaryRawProjectiveRows

/-- The raw projective fields supply the existing cross-zero physical
sixteenth package. -/
def toCrossZeroPhysicalSixteenthRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedBoundaryRawProjectiveRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedCrossZeroPhysicalSixteenthRows
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  harnack := data.harnack
  physical_centered_row_sixteenth := by
    intro scale source source_mem
    exact
      physicalCenteredPhysicalRowMass_le_sixteenth_of_rawProjective
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        source_mem
        (data.target_spread scale)
        (data.target_spread_square_le scale)
        (data.target_raw_projective scale)
        (data.source_spread scale source)
        (data.source_spread_square_le
          scale source source_mem)
        (data.source_raw_projective
          scale source source_mem)

/-- Therefore the division-free BF4 projective estimates inhabit both
requested spacing-uniform rowwise eighths. -/
def toRowwiseEighthEstimates
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedBoundaryRawProjectiveRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  data.toCrossZeroPhysicalSixteenthRows
    |>.toRowwiseEighthEstimates

end MatchedBoundaryRawProjectiveRows

end YMGap.Continuum.BF4PhysicalBoundaryPosteriorProjectiveAdapter

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosteriorProjectiveAdapter.centralBoundaryTargetProfileDeviation_le_quarter_of_rawProjective
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosteriorProjectiveAdapter.centralBoundaryGivenSourceL1_le_quarter_of_projective
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosteriorProjectiveAdapter.centralSourceBoundaryProfileDeviation_le_quarter_of_rawProjective
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosteriorProjectiveAdapter.physicalCenteredPhysicalRowMass_le_sixteenth_of_rawProjective
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosteriorProjectiveAdapter.MatchedBoundaryRawProjectiveRows.toCrossZeroPhysicalSixteenthRows
#print axioms YMGap.Continuum.BF4PhysicalBoundaryPosteriorProjectiveAdapter.MatchedBoundaryRawProjectiveRows.toRowwiseEighthEstimates
