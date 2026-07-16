/-
# Dyadic comparison for the signed spatial route

The three finite-law edges are first combined at one arbitrary representation
cutoff.  Their exact boundary scales fit inside one standard cylinder
coefficient because the time and uniform shifts retain the two extra dyadic
powers present in the connected-carrier estimate.  The two scheduled cutoffs
are then aligned by their sum, yielding the prescribed signed-presentation
comparison modulus without a new law hypothesis.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialFiniteBounds

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCutoffTail
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialFiniteBounds
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialLaw
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialStageRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4SignedCenteredRecedingPresentation
open YMGap.Continuum.Z4SpinSummedCylinderCofinal
open YMGap.Continuum.Z4SpinSummedCylinderJointCofinal
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4TimeShiftedTargetCylinderStability
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open YMGap.Continuum.Z4UniformShiftTargetCylinderStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

private theorem ofNat_nonnegative_local (n : Nat) :
    (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg n

private theorem qpow_base_mono_local {x y : Q'}
    (hx : (0 : Q') ≤ x) (hxy : x ≤ y) :
    ∀ exponent : Nat, x ^ exponent ≤ y ^ exponent
  | 0 => Q'.le_refl' 1
  | exponent + 1 => by
      change x * x ^ exponent ≤ y * y ^ exponent
      exact Q'.mul_le_mul_of_nonneg
        hxy (qpow_base_mono_local hx hxy exponent)
        (Q'.le_trans' _ _ _ hx hxy)
        (Q'.pow_nonneg x hx exponent)

/-! ## 1. Retaining the two unused dyadic powers -/

theorem spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow_add_two
    (rootCount distance : Nat) :
    spinSummedCylinderBoundaryEpsilon rootCount distance ≤
      spinSummedCylinderBoundaryCoefficient rootCount *
        HalfPow.half ^ (distance + 2) := by
  have hpow :
      anchorDecoratedEffectiveRatio ^ (distance + 2) ≤
        HalfPow.half ^ (distance + 2) :=
    qpow_base_mono_local anchorDecoratedEffectiveRatio_nonnegative
      anchorDecoratedEffectiveRatio_le_half (distance + 2)
  have hterm :
      anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2 ≤
        HalfPow.half ^ (distance + 2) * Q'.ofNat 2 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpow
      (ofNat_nonnegative_local 2)
  have hsum := Q'.add_le_add hterm hterm
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hsum
    (ofNat_nonnegative_local rootCount)
  have hreorder :
      Q'.ofNat rootCount *
          (HalfPow.half ^ (distance + 2) * Q'.ofNat 2 +
            HalfPow.half ^ (distance + 2) * Q'.ofNat 2) ≈
        spinSummedCylinderBoundaryCoefficient rootCount *
          HalfPow.half ^ (distance + 2) := by
    refine Q'.eqv_trans _
      (Q'.ofNat rootCount *
        (Q'.ofNat 2 * HalfPow.half ^ (distance + 2) +
          Q'.ofNat 2 * HalfPow.half ^ (distance + 2))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_comm_eqv _ _) (Q'.mul_comm_eqv _ _))
    refine Q'.eqv_trans _
      (Q'.ofNat rootCount *
        ((Q'.ofNat 2 + Q'.ofNat 2) *
          HalfPow.half ^ (distance + 2))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm
          (Q'.add_mul_eqv (Q'.ofNat 2) (Q'.ofNat 2)
            (HalfPow.half ^ (distance + 2))))
    unfold spinSummedCylinderBoundaryCoefficient
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv (Q'.ofNat rootCount)
        (Q'.ofNat 2 + Q'.ofNat 2)
        (HalfPow.half ^ (distance + 2)))
  unfold spinSummedCylinderBoundaryEpsilon at hscaled ⊢
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hreorder)

theorem timeShiftSpinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow_add_two
    (rootCount distance : Nat) :
    timeShiftSpinSummedCylinderBoundaryEpsilon rootCount distance ≤
      spinSummedCylinderBoundaryCoefficient rootCount *
        HalfPow.half ^ (distance + 2) := by
  exact Q'.le_trans' _ _ _
    (timeShiftSpinSummedCylinderBoundaryEpsilon_le_standard
      rootCount distance)
    (spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow_add_two
      rootCount distance)

theorem uniformShiftSpinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow_add_two
    (rootCount distance : Nat) :
    uniformShiftSpinSummedCylinderBoundaryEpsilon rootCount distance ≤
      spinSummedCylinderBoundaryCoefficient rootCount *
        HalfPow.half ^ (distance + 2) := by
  exact Q'.le_trans' _ _ _
    (YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge.uniformShiftSpinSummedCylinderBoundaryEpsilon_le_standard
      rootCount distance)
    (spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow_add_two
      rootCount distance)

/-! ## 2. Three-edge comparison at one arbitrary cutoff -/

private theorem reassoc_cancel_local (u middle residual : Q') :
    ((u + (-middle)) + (middle + residual)) ≈ u + residual := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv u (-middle) (middle + residual)) ?_
  refine Q'.add_eqv_congr_left u
    ((-middle) + (middle + residual)) residual ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-middle) middle residual)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-middle) + middle) 0 residual
      (Q'.neg_add_self_eqv middle)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' residual)

private theorem abs_sub_triangle_local (a b c : Q') :
    Q'.abs (a - b) ≤ Q'.abs (a - c) + Q'.abs (c - b) := by
  have hdecompose : a - b ≈ (a - c) + (c - b) := by
    exact Q'.eqv_symm (reassoc_cancel_local a c (-b))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.abs_add_le' (a - c) (c - b))

private theorem three_edge_abs_sub_le_local
    (a b c d epsilonAC epsilonCD epsilonDB : Q')
    (hAC : Q'.abs (a - c) ≤ epsilonAC)
    (hCD : Q'.abs (c - d) ≤ epsilonCD)
    (hDB : Q'.abs (d - b) ≤ epsilonDB) :
    Q'.abs (a - b) ≤ epsilonAC + (epsilonCD + epsilonDB) := by
  have hAB := abs_sub_triangle_local a b c
  have hCB := abs_sub_triangle_local c b d
  exact Q'.le_trans' _ _ _ hAB
    (Q'.add_le_add hAC
      (Q'.le_trans' _ _ _ hCB (Q'.add_le_add hCD hDB)))

theorem couplingParametricK_signedSpatial_target_abs_sub_source_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base shift stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (signedSpatialTargetStageBase base shift stage)
            (cylinderEvent
              (signedSpatialTargetStageRoots base shift stage roots)
              predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (signedSpatialSourceStageBase base stage)
            (cylinderEvent
              (signedSpatialSourceStageRoots base stage roots)
              predicate)) ≤
      spinSummedCylinderBoundaryCoefficient roots.length *
        HalfPow.half ^ stage := by
  let target := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling cutoff
    (signedSpatialTargetStageBase base shift stage)
    (cylinderEvent
      (signedSpatialTargetStageRoots base shift stage roots) predicate)
  let time := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling cutoff
    (signedSpatialTimeStageBase base shift stage)
    (cylinderEvent
      (signedSpatialTimeStageRoots base shift stage roots) predicate)
  let common := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling cutoff
    (signedSpatialCommonStageBase base shift stage)
    (cylinderEvent
      (signedSpatialCommonUniformRoots base shift stage roots) predicate)
  let source := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling cutoff
    (signedSpatialSourceStageBase base stage)
    (cylinderEvent
      (signedSpatialSourceStageRoots base stage roots) predicate)
  have hTargetTimeRaw :=
    couplingParametricK_signedSpatial_time_abs_sub_target_le
      hcoupling hle cutoff hroots predicate
      (shift := shift) (stage := stage)
  have hTargetTime : Q'.abs (target - time) ≤
      timeShiftSpinSummedCylinderBoundaryEpsilon
        roots.length stage := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm target time))
      hTargetTimeRaw
  have hTimeCommonRaw :=
    couplingParametricK_signedSpatial_common_abs_sub_time_le
      hcoupling hle cutoff hroots predicate
      (shift := shift) (stage := stage)
  have hTimeCommon : Q'.abs (time - common) ≤
      spinSummedCylinderBoundaryEpsilon roots.length (stage + 1) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm time common))
      hTimeCommonRaw
  have hCommonSource :=
    couplingParametricK_signedSpatial_common_abs_sub_source_le_epsilon
      hcoupling hle cutoff hroots predicate
      (shift := shift) (stage := stage)
  have hTargetTimeDyadic : Q'.abs (target - time) ≤
      spinSummedCylinderBoundaryCoefficient roots.length *
        HalfPow.half ^ (stage + 2) :=
    Q'.le_trans' _ _ _ hTargetTime
      (timeShiftSpinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow_add_two
        roots.length stage)
  have hTimeCommonDyadic : Q'.abs (time - common) ≤
      spinSummedCylinderBoundaryCoefficient roots.length *
        HalfPow.half ^ (stage + 1) :=
    Q'.le_trans' _ _ _ hTimeCommon
      (spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
        roots.length (stage + 1))
  have hCommonSourceDyadic : Q'.abs (common - source) ≤
      spinSummedCylinderBoundaryCoefficient roots.length *
        HalfPow.half ^ (stage + 2) :=
    Q'.le_trans' _ _ _ hCommonSource
      (uniformShiftSpinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow_add_two
        roots.length stage)
  have hchain := three_edge_abs_sub_le_local target source time common
    (spinSummedCylinderBoundaryCoefficient roots.length *
      HalfPow.half ^ (stage + 2))
    (spinSummedCylinderBoundaryCoefficient roots.length *
      HalfPow.half ^ (stage + 1))
    (spinSummedCylinderBoundaryCoefficient roots.length *
      HalfPow.half ^ (stage + 2))
    hTargetTimeDyadic hTimeCommonDyadic hCommonSourceDyadic
  have hreorder :
      spinSummedCylinderBoundaryCoefficient roots.length *
          HalfPow.half ^ (stage + 2) +
        (spinSummedCylinderBoundaryCoefficient roots.length *
            HalfPow.half ^ (stage + 1) +
          spinSummedCylinderBoundaryCoefficient roots.length *
            HalfPow.half ^ (stage + 2)) ≈
      spinSummedCylinderBoundaryCoefficient roots.length *
        HalfPow.half ^ stage := by
    let x := spinSummedCylinderBoundaryCoefficient roots.length *
      HalfPow.half ^ stage
    let y := HalfPow.half * x
    have hshape :
        spinSummedCylinderBoundaryCoefficient roots.length *
            HalfPow.half ^ (stage + 2) +
          (spinSummedCylinderBoundaryCoefficient roots.length *
              HalfPow.half ^ (stage + 1) +
            spinSummedCylinderBoundaryCoefficient roots.length *
              HalfPow.half ^ (stage + 2)) ≈
        HalfPow.half * y + (y + HalfPow.half * y) := by
      dsimp only [x, y]
      rw [show stage + 2 = (stage + 1) + 1 by omega,
        Q'.pow_succ, Q'.pow_succ]
      ring_qeqv
    have hfirst :
        HalfPow.half * y + (y + HalfPow.half * y) ≈ y + y := by
      refine Q'.eqv_trans _
        ((HalfPow.half * y + HalfPow.half * y) + y) _
        (by ring_qeqv) ?_
      exact Q'.add_eqv_congr_right
        (HalfPow.half * y + HalfPow.half * y) y y
        (ExpNeg.two_halves y)
    have hsecond : y + y ≈ x := by
      dsimp only [y]
      exact ExpNeg.two_halves x
    exact Q'.eqv_trans _ _ _ hshape
      (Q'.eqv_trans _ _ _ hfirst hsecond)
  change Q'.abs (target - source) ≤
    spinSummedCylinderBoundaryCoefficient roots.length *
      HalfPow.half ^ stage
  exact Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv hreorder)

/-! ## 3. Scheduled-cutoff alignment for signed presentations -/

theorem signedSpatialPresentationComparisonModulus_of_data
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {shift : Nat}
    {source target : SignedCenteredCylinderPresentation}
    (hbase : signedCenteredPresentationDiagonalBase target =
      signedSpatialTargetBase
        (signedCenteredPresentationDiagonalBase source) shift)
    (hroots : target.chart.roots =
      signedSpatialTargetRoots
        (signedCenteredPresentationDiagonalBase source) shift
        source.chart.roots)
    (hpredicate : target.predicate = source.predicate) :
    SignedCenteredPresentationComparisonModulus
      coupling hcoupling target source := by
  intro stage
  let sourceBase := signedCenteredPresentationDiagonalBase source
  let targetBase := signedCenteredPresentationDiagonalBase target
  let sourceCutoff := centeredRecedingStageCutoff sourceBase stage
  let targetCutoff := centeredRecedingStageCutoff targetBase stage
  let commonCutoff := sourceCutoff + targetCutoff
  have hsourceCutoff : sourceCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  have htargetCutoff : targetCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  let a := couplingParametricSignedCenteredPresentationSequence
    coupling hcoupling target stage
  let b := couplingParametricSignedCenteredPresentationSequence
    coupling hcoupling source stage
  let c := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling commonCutoff
    (centeredRecedingStageBase targetBase stage)
    (centeredRecedingCylinderEvent targetBase stage
      target.chart.roots target.predicate)
  let d := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling commonCutoff
    (centeredRecedingStageBase sourceBase stage)
    (centeredRecedingCylinderEvent sourceBase stage
      source.chart.roots source.predicate)
  have hACRaw :=
    couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
      hcoupling hle
      (centeredRecedingCylinderEvent targetBase stage
        target.chart.roots target.predicate)
      htargetCutoff
  have hAC : Q'.abs (a - c) ≤ HalfPow.half ^ stage := by
    dsimp only [a, c, targetCutoff,
      couplingParametricSignedCenteredPresentationSequence,
      couplingParametricCenteredRecedingCylinderSequence] at ⊢
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm _ _))
      hACRaw
  have hCD : Q'.abs (c - d) ≤
      spinSummedCylinderBoundaryCoefficient source.chart.roots.length *
        HalfPow.half ^ stage := by
    have hsourceRoots := signedCenteredPresentation_rootsCanonical source
    have hraw := couplingParametricK_signedSpatial_target_abs_sub_source_le
      hcoupling hle commonCutoff
      (shift := shift) (stage := stage)
      hsourceRoots source.predicate
    dsimp only [c, d, targetBase, sourceBase]
    rw [hbase, hroots, hpredicate]
    simpa only [signedSpatialTargetStageBase_eq_centered,
      signedSpatialSourceStageBase_eq_centered,
      signedSpatialTargetCylinderEvent_eq_centered,
      signedSpatialSourceCylinderEvent_eq_centered] using hraw
  have hDB : Q'.abs (d - b) ≤ HalfPow.half ^ stage := by
    have hraw :=
      couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
        hcoupling hle
        (centeredRecedingCylinderEvent sourceBase stage
          source.chart.roots source.predicate)
        hsourceCutoff
    dsimp only [d, b, sourceCutoff,
      couplingParametricSignedCenteredPresentationSequence,
      couplingParametricCenteredRecedingCylinderSequence] at ⊢
    exact hraw
  have hchain := three_edge_abs_sub_le_local a b c d
    (HalfPow.half ^ stage)
    (spinSummedCylinderBoundaryCoefficient source.chart.roots.length *
      HalfPow.half ^ stage)
    (HalfPow.half ^ stage) hAC hCD hDB
  let h := HalfPow.half ^ stage
  let joint := spinSummedJointCylinderCoefficient
    source.chart.roots.length
  have hreorder :
      h +
          (spinSummedCylinderBoundaryCoefficient
              source.chart.roots.length * h + h) ≈
        joint * h := by
    dsimp only [joint]
    unfold spinSummedJointCylinderCoefficient
    ring_qeqv
  have htargetLength : target.chart.roots.length =
      source.chart.roots.length := by
    rw [hroots]
    unfold signedSpatialTargetRoots
    simp only [List.length_map]
  have hjointNonnegative : (0 : Q') ≤ joint :=
    spinSummedJointCylinderCoefficient_nonnegative
      source.chart.roots.length
  have hcoefficient : joint ≤
      signedCenteredPresentationComparisonCoefficient target source := by
    unfold signedCenteredPresentationComparisonCoefficient
    rw [htargetLength]
    exact Q'.add_le_self_of_nonneg joint joint hjointNonnegative
  have hscaled : joint * h ≤
      signedCenteredPresentationComparisonCoefficient target source * h :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcoefficient
      (Q'.pow_nonneg HalfPow.half (by decide) stage)
  change Q'.abs (a - b) ≤
    signedCenteredPresentationComparisonCoefficient target source * h
  exact Q'.le_trans' _ _ _ hchain
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder) hscaled)

/-! ## 4. The strict doubled-time pair -/

theorem strictJointDoubledTime_signedSpatial_targetDiagonalBase_eq
    (base shift stage : Nat) (roots : List (List Nat))
    (hstage : shift + shift ≤ stage)
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    signedCenteredPresentationDiagonalBase
        (timeTranslatedStrictJointSignedPresentation
          base shift stage roots (fun _ => true) hroots) =
      signedSpatialTargetBase
        (signedCenteredPresentationDiagonalBase
          (strictJointDoubledTimeMixedSignedPresentation
            base shift stage roots (fun _ => true)
            hstage hroots)) shift := by
  unfold signedCenteredPresentationDiagonalBase
    timeTranslatedStrictJointSignedPresentation
    timeTranslatedStrictJointSignedChart
    strictJointDoubledTimeMixedSignedPresentation
    strictJointDoubledTimeMixedSignedChart signedSpatialTargetBase
  exact (uniformPaddedBase_centeredBoxBase
    (strictQueryBase base + stage) shift).symm

theorem strictJointDoubledTime_signedSpatialPresentationComparisonModulus
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    SignedCenteredPresentationComparisonModulus coupling hcoupling
      (timeTranslatedStrictJointSignedPresentation
        base shift stage roots predicate hroots)
      (strictJointDoubledTimeMixedSignedPresentation
        base shift stage roots predicate hstage hroots) := by
  let source := strictJointDoubledTimeMixedSignedPresentation
    base shift stage roots predicate hstage hroots
  let target := timeTranslatedStrictJointSignedPresentation
    base shift stage roots predicate hroots
  apply signedSpatialPresentationComparisonModulus_of_data
    hcoupling hle (shift := shift)
  · dsimp only [source, target, signedCenteredPresentationDiagonalBase,
      timeTranslatedStrictJointSignedPresentation,
      timeTranslatedStrictJointSignedChart,
      strictJointDoubledTimeMixedSignedPresentation,
      strictJointDoubledTimeMixedSignedChart, signedSpatialTargetBase]
    exact (uniformPaddedBase_centeredBoxBase
      (strictQueryBase base + stage) shift).symm
  · dsimp only [source, target]
    change (timeTranslatedStrictJointSignedChart
        base shift stage roots hroots).roots =
      signedSpatialTargetRoots
        (centeredBoxBase (strictQueryBase base + stage)) shift
        (strictJointDoubledTimeMixedSignedChart
          base shift stage roots hstage hroots).roots
    rw [timeTranslatedStrictJointSignedChart_roots_eq_spatialMixed
      hstage hroots]
    rfl
  · rfl

#print axioms spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow_add_two
#print axioms timeShiftSpinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow_add_two
#print axioms uniformShiftSpinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow_add_two
#print axioms couplingParametricK_signedSpatial_target_abs_sub_source_le
#print axioms signedSpatialPresentationComparisonModulus_of_data
#print axioms strictJointDoubledTime_signedSpatial_targetDiagonalBase_eq
#print axioms strictJointDoubledTime_signedSpatialPresentationComparisonModulus

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialComparison
