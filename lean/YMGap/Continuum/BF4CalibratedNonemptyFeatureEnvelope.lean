/-
# Factorial row envelope for the calibrated nonempty BF4 feature Gram

The nonempty part of the positive BF4 Mehler endpoint is a finite weighted
Gram over ordered kinetic-feature words.  This module moves absolute values
inside that Gram and exchanges the target/word sums.  The resulting exact
majorant is

  pi0^2 sum_{word != empty} normalizedWeight(word)
    |A_source(word)| sum_target |A_target(word)|.

It retains the literal factorial word coefficient and introduces no carrier
cardinality or minimum-marginal factor.  A `1/16` bound on this executable
envelope is therefore sufficient for the nonempty half of the corrected
spectral `1/8`.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CalibratedEmptyProfileWindow

namespace YMGap.Continuum.BF4CalibratedNonemptyFeatureEnvelope

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4CalibratedEmptyProfileWindow
open YMGap.Continuum.BF4CalibratedFeatureGramCoreTail
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4PhysicalRecenteredEndpointRate
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Entrywise absolute feature envelope -/

/-- Absolute feature-word envelope for one normalized nonempty Gram entry. -/
def normalizedNonemptyFeatureEntryAbsEnvelope
    (diagonalOrder crossOrder : Nat)
    (source target : EdgeLabelling) : Q' :=
  listQSum
    (fun word =>
      normalizedBF4FeatureWordWeight
          (shiftedDiagonalVacuumCertificate diagonalOrder)
          crossOrder word *
        (Q'.abs
            (bf4MehlerHalfAmplitude
              (diagonalOrder + 1) source word) *
          Q'.abs
            (bf4MehlerHalfAmplitude
              (diagonalOrder + 1) target word)))
    (bf4NonemptyFeatureWordsAtMost crossOrder)

/-- Calibrated entrywise envelope, including the exact physical vacuum
square. -/
def calibratedNonemptyFeatureEntryAbsEnvelope
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (source target : EdgeLabelling) : Q' :=
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent zeroEdgeLabelling
  (pi0 * pi0) *
    normalizedNonemptyFeatureEntryAbsEnvelope
      diagonalOrder crossOrder source target

/-- Absolute value of the calibrated nonempty Gram entry is controlled by
the wordwise absolute envelope. -/
theorem calibratedNonemptyFeatureJoint_abs_le_entryEnvelope
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (source target : EdgeLabelling) :
    Q'.abs
        (calibratedBF4NonemptyFeatureJoint
          w hw K halfExtent diagonalOrder crossOrder
          source target) ≤
      calibratedNonemptyFeatureEntryAbsEnvelope
        w hw K halfExtent diagonalOrder crossOrder
        source target := by
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent zeroEdgeLabelling
  let scale := pi0 * pi0
  let words :=
    bf4NonemptyFeatureWordsAtMost crossOrder
  let weight :=
    normalizedBF4FeatureWordWeight
      (shiftedDiagonalVacuumCertificate diagonalOrder)
      crossOrder
  let amplitude :=
    bf4MehlerHalfAmplitude (diagonalOrder + 1)
  let term := fun word =>
    weight word *
      (amplitude source word * amplitude target word)
  let absoluteTerm := fun word =>
    weight word *
      (Q'.abs (amplitude source word) *
        Q'.abs (amplitude target word))
  have hscale : (0 : Q') ≤ scale :=
    YMGap.Constructive.SumOfSquares.q_mul_self_nonneg pi0
  have hterm :
      ∀ word,
        Q'.abs (term word) ≤ absoluteTerm word := by
    intro word
    have hweight :
        (0 : Q') ≤ weight word :=
      normalizedBF4FeatureWordWeight_nonnegative
        (shiftedDiagonalVacuumCertificate diagonalOrder)
        crossOrder word
    have houter :=
      YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
        (weight word)
        (amplitude source word *
          amplitude target word)
    have hinner :=
      YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
        (amplitude source word)
        (amplitude target word)
    rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
      hweight] at houter
    exact Q'.le_trans' _ _ _ houter
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        hinner hweight)
  have hgram :
      Q'.abs
          (listQSum term words) ≤
        listQSum absoluteTerm words := by
    exact Q'.le_trans' _ _ _
      (abs_listQSum_le_sum_abs term words)
      (listQSum_mono
        (fun word => Q'.abs (term word))
        absoluteTerm words
        (fun word _ => hterm word))
  have hscaledAbs :=
    YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
      scale (listQSum term words)
  rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
    hscale] at hscaledAbs
  unfold calibratedBF4NonemptyFeatureJoint
    normalizedBF4NonemptyFeatureJoint
    weightedGram
    calibratedNonemptyFeatureEntryAbsEnvelope
    normalizedNonemptyFeatureEntryAbsEnvelope
  exact Q'.le_trans' _ _ _ hscaledAbs
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      hgram hscale)

/-! ## 2. Target/word regrouping -/

/-- Absolute image mass of one feature-word half-amplitude over the retained
physical carrier. -/
def bf4FeatureWordImageAbsMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder : Nat)
    (word : List BF4KineticFeature) : Q' :=
  listQSum
    (fun target =>
      Q'.abs
        (bf4MehlerHalfAmplitude
          (diagonalOrder + 1) target word))
    (centralPositiveHalfStates w hw K halfExtent)

/-- Word-first factorial envelope for one calibrated nonempty source row. -/
def calibratedNonemptyFeatureFactorialRowEnvelope
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (source : EdgeLabelling) : Q' :=
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent zeroEdgeLabelling
  (pi0 * pi0) *
    listQSum
      (fun word =>
        normalizedBF4FeatureWordWeight
            (shiftedDiagonalVacuumCertificate diagonalOrder)
            crossOrder word *
          (Q'.abs
              (bf4MehlerHalfAmplitude
                (diagonalOrder + 1) source word) *
            bf4FeatureWordImageAbsMass
              w hw K halfExtent diagonalOrder word))
      (bf4NonemptyFeatureWordsAtMost crossOrder)

/-- Summing the entry envelopes over targets is exactly the word-first
factorial row envelope. -/
theorem entryEnvelope_row_eqv_factorialEnvelope
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (source : EdgeLabelling) :
    listQSum
        (calibratedNonemptyFeatureEntryAbsEnvelope
          w hw K halfExtent diagonalOrder crossOrder source)
        (centralPositiveHalfStates w hw K halfExtent) ≈
      calibratedNonemptyFeatureFactorialRowEnvelope
        w hw K halfExtent diagonalOrder crossOrder source := by
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent zeroEdgeLabelling
  let scale := pi0 * pi0
  let states :=
    centralPositiveHalfStates w hw K halfExtent
  let words :=
    bf4NonemptyFeatureWordsAtMost crossOrder
  let weight :=
    normalizedBF4FeatureWordWeight
      (shiftedDiagonalVacuumCertificate diagonalOrder)
      crossOrder
  let amplitude :=
    bf4MehlerHalfAmplitude (diagonalOrder + 1)
  let mixed := fun target word =>
    weight word *
      (Q'.abs (amplitude source word) *
        Q'.abs (amplitude target word))
  have hinner :
      ∀ word,
        listQSum
            (fun target => mixed target word)
            states ≈
          weight word *
            (Q'.abs (amplitude source word) *
              listQSum
                (fun target =>
                  Q'.abs (amplitude target word))
                states) := by
    intro word
    refine Q'.eqv_trans _
      (listQSum
        (fun target =>
          (weight word *
            Q'.abs (amplitude source word)) *
              Q'.abs (amplitude target word))
        states) _ ?_ ?_
    · apply listQSum_congr
      intro target
      exact Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (weight word)
          (Q'.abs (amplitude source word))
          (Q'.abs (amplitude target word)))
    · refine Q'.eqv_trans _
        ((weight word *
            Q'.abs (amplitude source word)) *
          listQSum
            (fun target =>
              Q'.abs (amplitude target word))
            states) _ ?_ ?_
      · exact listQSum_mul_left
          (weight word *
            Q'.abs (amplitude source word))
          (fun target =>
            Q'.abs (amplitude target word))
          states
      · exact Q'.mul_assoc_eqv
          (weight word)
          (Q'.abs (amplitude source word))
          (listQSum
            (fun target =>
              Q'.abs (amplitude target word))
            states)
  unfold calibratedNonemptyFeatureEntryAbsEnvelope
    normalizedNonemptyFeatureEntryAbsEnvelope
    calibratedNonemptyFeatureFactorialRowEnvelope
  refine Q'.eqv_trans _
    (scale *
      listQSum
        (fun target =>
          listQSum (mixed target) words)
        states) _ ?_ ?_
  · exact listQSum_mul_left
      scale
      (fun target =>
        listQSum (mixed target) words)
      states
  refine Q'.eqv_trans _
    (scale *
      listQSum
        (fun word =>
          listQSum
            (fun target => mixed target word)
            states)
        words) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left scale _ _
      (listQSum_swap
        (fun word target => mixed target word)
        words states)
  · exact Q'.mul_eqv_congr_left scale _ _
      (listQSum_congr hinner words)

/-! ## 3. Exact nonempty row criterion -/

/-- The literal calibrated nonempty row is bounded by its factorial
word-first envelope. -/
theorem calibratedNonemptyFeatureAbsRowMass_le_factorialEnvelope
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (source : EdgeLabelling) :
    calibratedNonemptyFeatureAbsRowMass
        w hw K halfExtent diagonalOrder crossOrder source ≤
      calibratedNonemptyFeatureFactorialRowEnvelope
        w hw K halfExtent diagonalOrder crossOrder source := by
  unfold calibratedNonemptyFeatureAbsRowMass
  refine Q'.le_trans' _ _ _
    (listQSum_mono
      (fun target =>
        Q'.abs
          (calibratedBF4NonemptyFeatureJoint
            w hw K halfExtent diagonalOrder crossOrder
            source target))
      (calibratedNonemptyFeatureEntryAbsEnvelope
        w hw K halfExtent diagonalOrder crossOrder source)
      (centralPositiveHalfStates w hw K halfExtent)
      (fun target _ =>
        calibratedNonemptyFeatureJoint_abs_le_entryEnvelope
          w hw K halfExtent diagonalOrder crossOrder
          source target)) ?_
  exact Q'.le_of_eqv
    (entryEnvelope_row_eqv_factorialEnvelope
      w hw K halfExtent diagonalOrder crossOrder source)

/-- A `1/16` factorial envelope proves the required nonempty-feature row
budget. -/
theorem calibratedNonemptyFeatureAbsRowMass_le_sixteenth_of_factorial
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder crossOrder : Nat}
    {source : EdgeLabelling}
    (henvelope :
      calibratedNonemptyFeatureFactorialRowEnvelope
          w hw K halfExtent diagonalOrder crossOrder source ≤
        Q'.mkPos 1 16 (by decide) *
          centralPhysicalRowMarginal
            w hw K halfExtent source) :
    calibratedNonemptyFeatureAbsRowMass
        w hw K halfExtent diagonalOrder crossOrder source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
  Q'.le_trans' _ _ _
    (calibratedNonemptyFeatureAbsRowMass_le_factorialEnvelope
      w hw K halfExtent diagonalOrder crossOrder source)
    henvelope

/-- At cross order zero the nonempty feature carrier is literally empty, so
its complete factorial row envelope vanishes. -/
theorem calibratedNonemptyFeatureFactorialRowEnvelope_crossZero
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder : Nat)
    (source : EdgeLabelling) :
    calibratedNonemptyFeatureFactorialRowEnvelope
        w hw K halfExtent diagonalOrder 0 source ≈
      0 := by
  unfold calibratedNonemptyFeatureFactorialRowEnvelope
    bf4NonemptyFeatureWordsAtMost
  exact Q'.mul_zero_eqv _

/-- Hence the nonempty `1/16` field is unconditionally inhabited at cross
order zero. -/
theorem calibratedNonemptyFeatureFactorialRowEnvelope_crossZero_le_sixteenth
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder : Nat)
    (source : EdgeLabelling) :
    calibratedNonemptyFeatureFactorialRowEnvelope
        w hw K halfExtent diagonalOrder 0 source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          w hw K halfExtent source := by
  exact Q'.le_trans' _ 0 _
    (Q'.le_of_eqv
      (calibratedNonemptyFeatureFactorialRowEnvelope_crossZero
        w hw K halfExtent diagonalOrder source))
    (Q'.mul_nonneg _ _
      (by decide)
      (centralPhysicalRowMarginal_nonnegative
        hw K halfExtent source))

/-- The physical prefix/image `1/16` and the factorial feature-envelope
`1/16` imply the corrected spectral row `1/8`. -/
theorem physicalCenteredEndpointRowMass_le_eighth_of_profile_and_factorial
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder crossOrder : Nat}
    {source : EdgeLabelling}
    (hprofile :
      calibratedEmptyLeftProfileMismatch
              w hw K halfExtent diagonalOrder crossOrder source *
            calibratedEmptyRightProfileAbsMass
              w hw K halfExtent diagonalOrder +
          centralPhysicalRowMarginal
              w hw K halfExtent source *
            calibratedEmptyRightProfileMismatchMass
              w hw K halfExtent diagonalOrder ≤
        Q'.mkPos 1 16 (by decide) *
          centralPhysicalRowMarginal
            w hw K halfExtent source)
    (henvelope :
      calibratedNonemptyFeatureFactorialRowEnvelope
          w hw K halfExtent diagonalOrder crossOrder source ≤
        Q'.mkPos 1 16 (by decide) *
          centralPhysicalRowMarginal
            w hw K halfExtent source) :
    physicalCenteredEndpointRowMass
        (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
          w hw K halfExtent diagonalOrder crossOrder)
        source ≤
      Q'.mkPos 1 8 (by decide) *
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
  physicalCenteredEndpointRowMass_le_eighth_of_profile_and_nonempty
    hprofile
    (calibratedNonemptyFeatureAbsRowMass_le_sixteenth_of_factorial
      henvelope)

/-- **Cross-zero sharpening.**  When the feature-word order is zero, the
nonempty Gram is exactly absent.  Hence a `1/16` empty-profile payment gives
a `1/16`, rather than merely `1/8`, physical-centered endpoint row. -/
theorem physicalCenteredEndpointRowMass_crossZero_le_sixteenth_of_profile
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder : Nat}
    {source : EdgeLabelling}
    (hprofile :
      calibratedEmptyLeftProfileMismatch
              w hw K halfExtent diagonalOrder 0 source *
            calibratedEmptyRightProfileAbsMass
              w hw K halfExtent diagonalOrder +
          centralPhysicalRowMarginal
              w hw K halfExtent source *
            calibratedEmptyRightProfileMismatchMass
              w hw K halfExtent diagonalOrder ≤
        Q'.mkPos 1 16 (by decide) *
          centralPhysicalRowMarginal
            w hw K halfExtent source) :
    physicalCenteredEndpointRowMass
        (vacuumCalibratedExactCenteredMehlerGramRawEndpoint
          w hw K halfExtent diagonalOrder 0)
        source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          w hw K halfExtent source := by
  have hcore :
      calibratedEmptyPhysicalMismatchRowMass
          w hw K halfExtent diagonalOrder 0 source ≤
        Q'.mkPos 1 16 (by decide) *
          centralPhysicalRowMarginal
            w hw K halfExtent source :=
    calibratedEmptyPhysicalMismatchRowMass_le_of_profile_budget
      hprofile
  have htailZero :
      calibratedNonemptyFeatureAbsRowMass
          w hw K halfExtent diagonalOrder 0 source ≤
        (0 : Q') := by
    refine Q'.le_trans' _ _ _
      (calibratedNonemptyFeatureAbsRowMass_le_factorialEnvelope
        w hw K halfExtent diagonalOrder 0 source) ?_
    exact Q'.le_of_eqv
      (calibratedNonemptyFeatureFactorialRowEnvelope_crossZero
        w hw K halfExtent diagonalOrder source)
  have htail :
      calibratedNonemptyFeatureAbsRowMass
          w hw K halfExtent diagonalOrder 0 source ≤
        (0 : Q') *
          centralPhysicalRowMarginal
            w hw K halfExtent source := by
    exact Q'.le_trans' _ _ _ htailZero
      (Q'.ge_of_eqv
        (Q'.zero_mul_eqv
          (centralPhysicalRowMarginal
            w hw K halfExtent source)))
  refine Q'.le_trans' _ _ _
    (physicalCenteredEndpointRowMass_le_of_core_tail
      (Q'.mkPos 1 16 (by decide)) 0
      hcore htail) ?_
  exact Q'.le_of_eqv
    (Q'.mul_eqv_congr_right
      (Q'.mkPos 1 16 (by decide) + 0)
      (Q'.mkPos 1 16 (by decide))
      (centralPhysicalRowMarginal
        w hw K halfExtent source)
      (Q'.eqv_of_eq
        (Q'.add_zero'
          (Q'.mkPos 1 16 (by decide)))))

end YMGap.Continuum.BF4CalibratedNonemptyFeatureEnvelope

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4CalibratedNonemptyFeatureEnvelope.calibratedNonemptyFeatureJoint_abs_le_entryEnvelope
#print axioms YMGap.Continuum.BF4CalibratedNonemptyFeatureEnvelope.entryEnvelope_row_eqv_factorialEnvelope
#print axioms YMGap.Continuum.BF4CalibratedNonemptyFeatureEnvelope.calibratedNonemptyFeatureAbsRowMass_le_factorialEnvelope
#print axioms YMGap.Continuum.BF4CalibratedNonemptyFeatureEnvelope.calibratedNonemptyFeatureFactorialRowEnvelope_crossZero_le_sixteenth
#print axioms YMGap.Continuum.BF4CalibratedNonemptyFeatureEnvelope.physicalCenteredEndpointRowMass_le_eighth_of_profile_and_factorial
#print axioms YMGap.Continuum.BF4CalibratedNonemptyFeatureEnvelope.physicalCenteredEndpointRowMass_crossZero_le_sixteenth_of_profile
