/-
# BF4 adapter for anchored projective profile Harnack control

The generic theorem in `BF4AnchoredProjectiveProfileHarnack` removes the
scalar ambiguity in a projective estimate by matching one strictly positive
anchor.  This file specializes that theorem to the calibrated BF4 empty
left-prefix and right-image profiles.

Thus the remaining analytic task can be supplied in its natural form:
positive-kernel/projective control of each profile, normalized at the
physical vacuum.  No minimum marginal and no carrier cardinality appear.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
import YMGap.Continuum.BF4CalibratedProfileHarnack

namespace YMGap.Continuum.BF4CalibratedAnchoredProjectiveHarnack

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
open YMGap.Continuum.BF4CalibratedEmptyProfileWindow
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RationalCrossRatioDiameter

local infix:50 " ≈ " => Q'.eqv

abbrev BF4RetainedProfileStates
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) : List EdgeLabelling :=
  centralPositiveHalfStates w hw K halfExtent

abbrev BF4PhysicalProfile
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) : EdgeLabelling → Q' :=
  centralPhysicalRowMarginal w hw K halfExtent

abbrev BF4CalibratedLeftProfile
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) :
    EdgeLabelling → Q' :=
  calibratedEmptyLeftProfile
    w hw K halfExtent diagonalOrder crossOrder

abbrev BF4CalibratedRightProfile
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder : Nat) :
    EdgeLabelling → Q' :=
  calibratedEmptyRightProfile
    w hw K halfExtent diagonalOrder

theorem anchoredProjectiveTolerance_eq_profileTolerance :
    anchoredProjectiveTolerance ≈
      profileHarnackSixtyFourth := by
  decide

/-- At cross order zero the vacuum partition is exactly the square of the
empty-channel vacuum half-amplitude. -/
theorem bf4MehlerGramVacuumPartition_crossZero_eqv_square
    (diagonalOrder : Nat) :
    bf4MehlerGramVacuumPartition diagonalOrder 0 ≈
      bf4MehlerHalfAmplitude
          diagonalOrder zeroEdgeLabelling [] *
        bf4MehlerHalfAmplitude
          diagonalOrder zeroEdgeLabelling [] := by
  unfold bf4MehlerGramVacuumPartition
    bf4MehlerGramNumerator weightedGram
    bf4FeatureWordsAtMost listQSum
    bf4FeatureWordWeight
  change
    1 *
        (bf4MehlerHalfAmplitude
            diagonalOrder zeroEdgeLabelling [] *
          bf4MehlerHalfAmplitude
            diagonalOrder zeroEdgeLabelling []) +
      0 ≈
    bf4MehlerHalfAmplitude
        diagonalOrder zeroEdgeLabelling [] *
      bf4MehlerHalfAmplitude
        diagonalOrder zeroEdgeLabelling []
  rw [Q'.add_zero']
  exact Q'.one_mul_eqv _

private theorem qeqv_of_le_of_ge_local
    {a b : Q'} (hab : a ≤ b) (hba : b ≤ a) :
    a ≈ b := by
  show a.num * (b.den : Int) =
    b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

private theorem divPos_eqv_congr_local
    {a a' b b' : Q'}
    (hb : (0 : Q') < b)
    (hb' : (0 : Q') < b')
    (ha : a ≈ a') (hden : b ≈ b') :
    Q'.divPos a b hb ≈
      Q'.divPos a' b' hb' := by
  apply qeqv_of_le_of_ge_local
  · apply Q'.le_divPos_of_mul_le
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos a b hb) b' b
          (Q'.eqv_symm hden))
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv a b hb) ha))
  · apply Q'.le_divPos_of_mul_le
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos a' b' hb') b b' hden)
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv a' b' hb')
          (Q'.eqv_symm ha)))

private theorem eqv_divPos_of_mul_local
    {a numerator denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hmul : a * denominator ≈ numerator) :
    a ≈
      Q'.divPos numerator denominator
        hdenominator := by
  apply Q'.mul_left_cancel_of_pos hdenominator
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv denominator a) ?_
  refine Q'.eqv_trans _ _ _ hmul ?_
  exact Q'.eqv_symm
    (Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv denominator
        (Q'.divPos numerator denominator
          hdenominator))
      (Q'.divPos_mul_eqv
        numerator denominator hdenominator))

/-- At cross order zero the two asymmetric rational empty profiles coincide
pointwise.  Hence only one normalized positive projective-ray estimate is
needed in that exact truncation. -/
theorem calibratedEmptyLeftProfile_crossZero_eqv_right
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder : Nat)
    (state : EdgeLabelling) :
    calibratedEmptyLeftProfile
        w hw K halfExtent diagonalOrder 0 state ≈
      calibratedEmptyRightProfile
        w hw K halfExtent diagonalOrder state := by
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent zeroEdgeLabelling
  let h0 :=
    bf4VacuumEmptyHalf diagonalOrder
  let hs :=
    bf4MehlerHalfAmplitude
      (diagonalOrder + 1) state []
  let partition :=
    bf4MehlerGramVacuumPartition
      (diagonalOrder + 1) 0
  let hpartition :=
    bf4MehlerGramVacuumPartition_pos
      (shiftedDiagonalVacuumCertificate diagonalOrder) 0
  let hh0 : (0 : Q') < h0 :=
    bf4VacuumEmptyHalf_pos diagonalOrder
  let hh0sq : (0 : Q') < h0 * h0 :=
    Q'.mul_pos hh0 hh0
  have hpartitionEq :
      partition ≈ h0 * h0 := by
    exact
      bf4MehlerGramVacuumPartition_crossZero_eqv_square
        (diagonalOrder + 1)
  have hleftSquare :
      Q'.divPos
          ((pi0 * h0) * hs)
          partition hpartition ≈
        Q'.divPos
          ((pi0 * h0) * hs)
          (h0 * h0) hh0sq :=
    divPos_eqv_congr_local
      hpartition hh0sq
      (Q'.eqv_refl _) hpartitionEq
  have hrightTimesSquare :
      Q'.divPos (pi0 * hs) h0 hh0 *
          (h0 * h0) ≈
        (pi0 * h0) * hs := by
    refine Q'.eqv_trans _
      ((Q'.divPos (pi0 * hs) h0 hh0 * h0) *
        h0) _ ?_ ?_
    · exact Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (Q'.divPos (pi0 * hs) h0 hh0)
          h0 h0)
    refine Q'.eqv_trans _
      ((pi0 * hs) * h0) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ h0
        (Q'.divPos_mul_eqv
          (pi0 * hs) h0 hh0)
    · exact Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv pi0 hs h0)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left pi0 _ _
            (Q'.mul_comm_eqv hs h0))
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv pi0 h0 hs)))
  have hrightSquare :
      Q'.divPos (pi0 * hs) h0 hh0 ≈
        Q'.divPos
          ((pi0 * h0) * hs)
          (h0 * h0) hh0sq :=
    eqv_divPos_of_mul_local
      hh0sq hrightTimesSquare
  unfold calibratedEmptyLeftProfile
    calibratedEmptyRightProfile
  change
    Q'.divPos
        ((pi0 * h0) * hs)
        partition hpartition ≈
      Q'.divPos (pi0 * hs) h0 hh0
  exact Q'.eqv_trans _ _ _
    hleftSquare (Q'.eqv_symm hrightSquare)

/-- Build the normalized BF4 right-profile certificate from its genuine
positive-kernel and projective-spread estimates.  Vacuum membership,
strictly positive vacuum marginal, and exact vacuum normalization are
already theorems. -/
def calibratedEmptyRightAnchoredProjective
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder : Nat)
    (spread : Q')
    (profile_nonnegative :
      ∀ state,
        state ∈
            BF4RetainedProfileStates
              w hw K halfExtent →
          (0 : Q') ≤
            BF4CalibratedRightProfile
              w hw K halfExtent diagonalOrder state)
    (spreadSquare_le :
      spread * spread ≤ anchoredProjectiveCeiling)
    (projective :
      FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
        spread
        (BF4RetainedProfileStates
          w hw K halfExtent)
        (BF4CalibratedRightProfile
          w hw K halfExtent diagonalOrder)
        (BF4PhysicalProfile
          w hw K halfExtent)) :
    AnchoredProjectiveProfile
      (BF4RetainedProfileStates
        w hw K halfExtent)
      (BF4CalibratedRightProfile
        w hw K halfExtent diagonalOrder)
      (BF4PhysicalProfile
        w hw K halfExtent) where
  spread := spread
  anchor := zeroEdgeLabelling
  anchor_mem :=
    zeroEdgeLabelling_mem_centralPositiveHalfStates
      hw K halfExtent
  marginal_anchor_pos :=
    centralPhysicalRowMarginal_vacuum_pos
      hw K halfExtent
  anchor_match :=
    calibratedEmptyRightProfile_vacuum
      w hw K halfExtent diagonalOrder
  profile_nonnegative := profile_nonnegative
  spreadSquare_le := spreadSquare_le
  projective := projective

/-- **Grouped positive-kernel constructor for the BF4 right profile.**

If the calibrated right profile and physical marginal are two nonzero
nonnegative activities propagated by the same strictly positive finite
kernel, the kernel's cross-ratio certificate supplies the full anchored
profile certificate.  The vacuum normalization is discharged by the exact
BF4 theorem rather than assumed. -/
def calibratedEmptyRightAnchoredProjective_of_kernelActions
    {Source : Type}
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder : Nat)
    (kernel : Source → EdgeLabelling → Q')
    (sources : List Source)
    (candidate physical : Source → Q')
    (certificate :
      FiniteCrossRatioDiameterCertificate
        kernel sources
        (BF4RetainedProfileStates
          w hw K halfExtent))
    (candidateActivity :
      FiniteCrossRatioDiameterCertificate.NonzeroNonnegativeActivity
        sources candidate)
    (physicalActivity :
      FiniteCrossRatioDiameterCertificate.NonzeroNonnegativeActivity
        sources physical)
    (spreadSquare_le :
      certificate.spread * certificate.spread ≤
        anchoredProjectiveCeiling)
    (candidate_identification :
      ∀ state,
        state ∈
            BF4RetainedProfileStates
              w hw K halfExtent →
          BF4CalibratedRightProfile
              w hw K halfExtent diagonalOrder state ≈
            FiniteCrossRatioDiameterCertificate.finiteKernelAction
              kernel sources candidate state)
    (physical_identification :
      ∀ state,
        state ∈
            BF4RetainedProfileStates
              w hw K halfExtent →
          BF4PhysicalProfile
              w hw K halfExtent state ≈
            FiniteCrossRatioDiameterCertificate.finiteKernelAction
              kernel sources physical state) :
    AnchoredProjectiveProfile
      (BF4RetainedProfileStates
        w hw K halfExtent)
      (BF4CalibratedRightProfile
        w hw K halfExtent diagonalOrder)
      (BF4PhysicalProfile
        w hw K halfExtent) := by
  let anchor := zeroEdgeLabelling
  let anchorMem :
      anchor ∈
        BF4RetainedProfileStates
          w hw K halfExtent :=
    zeroEdgeLabelling_mem_centralPositiveHalfStates
      hw K halfExtent
  have hactionAnchor :
      FiniteCrossRatioDiameterCertificate.finiteKernelAction
          kernel sources candidate anchor ≈
        FiniteCrossRatioDiameterCertificate.finiteKernelAction
          kernel sources physical anchor := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (candidate_identification anchor anchorMem))
      (Q'.eqv_trans _ _ _
        (calibratedEmptyRightProfile_vacuum
          w hw K halfExtent diagonalOrder)
        (physical_identification anchor anchorMem))
  let actionData :=
    AnchoredProjectiveProfile.ofKernelActions
      certificate candidate physical
      candidateActivity physicalActivity
      anchor anchorMem hactionAnchor
      spreadSquare_le
  let profileData :=
    actionData.profileEqv candidate_identification
  exact profileData.marginalEqv physical_identification

/-- Cross order zero transports the single right-profile certificate to the
identical left profile. -/
def calibratedEmptyLeftCrossZeroAnchoredProjective
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder : Nat}
    (right :
      AnchoredProjectiveProfile
        (BF4RetainedProfileStates
          w hw K halfExtent)
        (BF4CalibratedRightProfile
          w hw K halfExtent diagonalOrder)
        (BF4PhysicalProfile
          w hw K halfExtent)) :
    AnchoredProjectiveProfile
      (BF4RetainedProfileStates
        w hw K halfExtent)
      (BF4CalibratedLeftProfile
        w hw K halfExtent diagonalOrder 0)
      (BF4PhysicalProfile
        w hw K halfExtent) :=
  right.profileEqv
    (fun state _ =>
      calibratedEmptyLeftProfile_crossZero_eqv_right
        w hw K halfExtent diagonalOrder state)

/-- **BF4 anchored-projective Harnack adapter.**  Two positive normalized
projective-ray certificates with squared spread at most `65/64` inhabit the
two spacing-local `1/64` profile fields used by the calibrated empty-channel
budget. -/
def calibratedEmptyProfileHarnackData_of_anchoredProjective
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder crossOrder : Nat}
    (left :
      AnchoredProjectiveProfile
        (BF4RetainedProfileStates
          w hw K halfExtent)
        (BF4CalibratedLeftProfile
          w hw K halfExtent diagonalOrder crossOrder)
        (BF4PhysicalProfile
          w hw K halfExtent))
    (right :
      AnchoredProjectiveProfile
        (BF4RetainedProfileStates
          w hw K halfExtent)
        (BF4CalibratedRightProfile
          w hw K halfExtent diagonalOrder)
        (BF4PhysicalProfile
          w hw K halfExtent)) :
    CalibratedEmptyProfileHarnackData
      w hw K halfExtent diagonalOrder crossOrder where
  left_relative := by
    intro source hsource
    unfold calibratedEmptyLeftProfileMismatch
    have hrelative :=
      left.relative_sixtyFourth
        source hsource
        (centralPhysicalRowMarginal_nonnegative
          hw K halfExtent source)
    refine Q'.le_trans' _ _ _ hrelative
      (Q'.le_of_eqv ?_)
    exact Q'.mul_eqv_congr_right _ _
      (centralPhysicalRowMarginal
        w hw K halfExtent source)
      anchoredProjectiveTolerance_eq_profileTolerance

  right_relative := by
    intro state hstate
    have hrelative :=
      right.relative_sixtyFourth
        state hstate
        (centralPhysicalRowMarginal_nonnegative
          hw K halfExtent state)
    refine Q'.le_trans' _ _ _ hrelative
      (Q'.le_of_eqv ?_)
    exact Q'.mul_eqv_congr_right _ _
      (centralPhysicalRowMarginal
        w hw K halfExtent state)
      anchoredProjectiveTolerance_eq_profileTolerance

/-- **One-ray cross-zero Harnack theorem.**  At cross order zero a single
positive, vacuum-normalized projective estimate supplies both pointwise
`1/64` BF4 profile windows. -/
def calibratedEmptyCrossZeroProfileHarnackData_of_rightAnchoredProjective
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder : Nat}
    (right :
      AnchoredProjectiveProfile
        (BF4RetainedProfileStates
          w hw K halfExtent)
        (BF4CalibratedRightProfile
          w hw K halfExtent diagonalOrder)
        (BF4PhysicalProfile
          w hw K halfExtent)) :
    CalibratedEmptyProfileHarnackData
      w hw K halfExtent diagonalOrder 0 :=
  calibratedEmptyProfileHarnackData_of_anchoredProjective
    (calibratedEmptyLeftCrossZeroAnchoredProjective right)
    right

/-- **Common-kernel cross-zero Harnack theorem.**

This is the direct BF4 analytic interface: identify the calibrated profile
and physical marginal as two activities propagated by one strictly positive
grouped kernel, and prove the squared projective spread cap `65/64`.  The
vacuum calibration and the equality of the cross-zero left/right profiles
then produce both pointwise `1/64` Harnack windows. -/
def calibratedEmptyCrossZeroProfileHarnackData_of_kernelActions
    {Source : Type}
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder : Nat)
    (kernel : Source → EdgeLabelling → Q')
    (sources : List Source)
    (candidate physical : Source → Q')
    (certificate :
      FiniteCrossRatioDiameterCertificate
        kernel sources
        (BF4RetainedProfileStates
          w hw K halfExtent))
    (candidateActivity :
      FiniteCrossRatioDiameterCertificate.NonzeroNonnegativeActivity
        sources candidate)
    (physicalActivity :
      FiniteCrossRatioDiameterCertificate.NonzeroNonnegativeActivity
        sources physical)
    (spreadSquare_le :
      certificate.spread * certificate.spread ≤
        anchoredProjectiveCeiling)
    (candidate_identification :
      ∀ state,
        state ∈
            BF4RetainedProfileStates
              w hw K halfExtent →
          BF4CalibratedRightProfile
              w hw K halfExtent diagonalOrder state ≈
            FiniteCrossRatioDiameterCertificate.finiteKernelAction
              kernel sources candidate state)
    (physical_identification :
      ∀ state,
        state ∈
            BF4RetainedProfileStates
              w hw K halfExtent →
          BF4PhysicalProfile
              w hw K halfExtent state ≈
            FiniteCrossRatioDiameterCertificate.finiteKernelAction
              kernel sources physical state) :
    CalibratedEmptyProfileHarnackData
      w hw K halfExtent diagonalOrder 0 :=
  calibratedEmptyCrossZeroProfileHarnackData_of_rightAnchoredProjective
    (calibratedEmptyRightAnchoredProjective_of_kernelActions
      w hw K halfExtent diagonalOrder
      kernel sources candidate physical
      certificate candidateActivity physicalActivity
      spreadSquare_le
      candidate_identification physical_identification)

end YMGap.Continuum.BF4CalibratedAnchoredProjectiveHarnack

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4CalibratedAnchoredProjectiveHarnack.calibratedEmptyProfileHarnackData_of_anchoredProjective
#print axioms YMGap.Continuum.BF4CalibratedAnchoredProjectiveHarnack.calibratedEmptyLeftProfile_crossZero_eqv_right
#print axioms YMGap.Continuum.BF4CalibratedAnchoredProjectiveHarnack.calibratedEmptyRightAnchoredProjective_of_kernelActions
#print axioms YMGap.Continuum.BF4CalibratedAnchoredProjectiveHarnack.calibratedEmptyCrossZeroProfileHarnackData_of_rightAnchoredProjective
#print axioms YMGap.Continuum.BF4CalibratedAnchoredProjectiveHarnack.calibratedEmptyCrossZeroProfileHarnackData_of_kernelActions
