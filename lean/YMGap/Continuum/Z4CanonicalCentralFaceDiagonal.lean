/-
# A simultaneous truncation-volume-cutoff diagonal for the central face

At precision `s`, use component-size floor `s`.  The finite chart has an
explicit root-count boundary coefficient, so its box radius is enlarged past
the truncation floor by a computable margin that pays that coefficient.  The
representation cutoff is then chosen by the existing joint cutoff schedule.

Two diagonal stages are compared through one common cutoff and one common
outer box.  The causal chain has exactly five error legs: later cutoff, later
volume, same-law truncation, earlier volume, and earlier cutoff.  No monotonicity
of the derived radius or cutoff schedules is required; their maxima provide
the common comparison objects constructively.
-/

import YMGap.Continuum.Z4CouplingParametricFaceTruncationComparison
import YMGap.Continuum.Z4CanonicalCentralFaceTruncationVolumeComparison

namespace YMGap.Continuum.Z4CanonicalCentralFaceDiagonal

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalCentralFaceFixedCylinder
open YMGap.Continuum.Z4CanonicalCentralFaceTruncationNesting
open YMGap.Continuum.Z4CanonicalCentralFaceTruncationVolumeComparison
open YMGap.Continuum.Z4CanonicalFaceEventPinnedTail
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CouplingParametricCutoffTail
open YMGap.Continuum.Z4CouplingParametricCylinderCofinal
open YMGap.Continuum.Z4CouplingParametricFaceTruncationComparison
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4SpinSummedCutoffTail
open YMGap.Continuum.Z4SpinSummedCylinderCofinal
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge
open YMGap.Continuum.Z4UniformShiftTargetCylinderStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, neg_num_cast_local,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-! ## 1. The coefficient-paying volume schedule -/

def pinnedFaceDiagonalBoundaryCoefficient (sizeFloor : Nat) : Q' :=
  spinSummedCylinderBoundaryCoefficient
    (pinnedFaceFixedRoots sizeFloor).length

def pinnedFaceDiagonalBoundaryTolerance
    (precision sizeFloor : Nat) : Q' :=
  HalfPow.half ^ precision *
    Q'.invSucc
      (pinnedFaceDiagonalBoundaryCoefficient sizeFloor).num.toNat

def pinnedFaceDiagonalMargin (precision sizeFloor : Nat) : Nat :=
  (pinnedFaceDiagonalBoundaryTolerance precision sizeFloor).den

def pinnedFaceDiagonalRadius (precision sizeFloor : Nat) : Nat :=
  sizeFloor + pinnedFaceDiagonalMargin precision sizeFloor

theorem pinnedFaceDiagonal_floor_le_radius
    (precision sizeFloor : Nat) :
    sizeFloor ≤ pinnedFaceDiagonalRadius precision sizeFloor := by
  unfold pinnedFaceDiagonalRadius
  omega

theorem pinnedFaceDiagonalRadius_sub_floor
    (precision sizeFloor : Nat) :
    pinnedFaceDiagonalRadius precision sizeFloor - sizeFloor =
      pinnedFaceDiagonalMargin precision sizeFloor := by
  unfold pinnedFaceDiagonalRadius
  omega

theorem pinnedFaceCommonSmallRoots_length
    (sizeFloor boxRadius : Nat) :
    (pinnedFaceCommonSmallRoots sizeFloor boxRadius).length =
      (pinnedFaceFixedRoots sizeFloor).length := by
  unfold pinnedFaceCommonSmallRoots pinnedFaceStageRoots
  simp only [List.length_map]

private theorem half_pow_pos_local :
    ∀ exponent : Nat, (0 : Q') < HalfPow.half ^ exponent
  | 0 => by decide
  | exponent + 1 => by
      change (0 : Q') < HalfPow.half * HalfPow.half ^ exponent
      exact Q'.mul_pos (by decide) (half_pow_pos_local exponent)

theorem pinnedFaceDiagonalBoundaryTolerance_pos
    (precision sizeFloor : Nat) :
    (0 : Q') < pinnedFaceDiagonalBoundaryTolerance
      precision sizeFloor := by
  unfold pinnedFaceDiagonalBoundaryTolerance
  exact Q'.mul_pos (half_pow_pos_local precision)
    (Q'.invSucc_pos _)

theorem pinnedFaceDiagonalBoundaryCoefficient_nonnegative
    (sizeFloor : Nat) :
    (0 : Q') ≤ pinnedFaceDiagonalBoundaryCoefficient sizeFloor :=
  spinSummedCylinderBoundaryCoefficient_nonnegative _

/-- The chosen volume margin absorbs the entire root-count coefficient. -/
theorem pinnedFaceDiagonalBoundaryEpsilon_le_half_pow
    (precision sizeFloor : Nat) :
    uniformShiftSpinSummedCylinderBoundaryEpsilon
        (pinnedFaceCommonSmallRoots sizeFloor
          (pinnedFaceDiagonalRadius precision sizeFloor)).length
        (pinnedFaceDiagonalRadius precision sizeFloor - sizeFloor) ≤
      HalfPow.half ^ precision := by
  rw [pinnedFaceCommonSmallRoots_length,
    pinnedFaceDiagonalRadius_sub_floor]
  refine Q'.le_trans' _ _ _
    (uniformShiftSpinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
      (pinnedFaceFixedRoots sizeFloor).length
      (pinnedFaceDiagonalMargin precision sizeFloor)) ?_
  let coefficient := pinnedFaceDiagonalBoundaryCoefficient sizeFloor
  let tolerance := pinnedFaceDiagonalBoundaryTolerance precision sizeFloor
  have hcoefficient : (0 : Q') ≤ coefficient :=
    pinnedFaceDiagonalBoundaryCoefficient_nonnegative sizeFloor
  have htolerance : (0 : Q') < tolerance :=
    pinnedFaceDiagonalBoundaryTolerance_pos precision sizeFloor
  have hhalf : HalfPow.half ^ tolerance.den ≤ tolerance :=
    HalfPow.pow_half_le tolerance htolerance
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (HalfPow.half ^ tolerance.den) tolerance coefficient
    hhalf hcoefficient
  have hfinal : coefficient * tolerance ≤ HalfPow.half ^ precision := by
    dsimp only [coefficient, tolerance,
      pinnedFaceDiagonalBoundaryTolerance]
    exact ExpNeg.mul_le_of_mul_invSucc_toNat
      (pinnedFaceDiagonalBoundaryCoefficient sizeFloor)
      (HalfPow.half ^ precision)
      (pinnedFaceDiagonalBoundaryCoefficient_nonnegative sizeFloor)
      (Q'.pow_nonneg HalfPow.half HalfPow.half_nonneg precision)
  change coefficient * HalfPow.half ^ tolerance.den ≤
    HalfPow.half ^ precision
  exact Q'.le_trans' _ _ _ hscaled hfinal

/-! ## 2. Exact rational diagonal stages -/

def pinnedFaceDiagonalBase (stage : Nat) : Nat :=
  pinnedFaceSourceBase (pinnedFaceDiagonalRadius stage stage)

def pinnedFaceDiagonalEvent (stage : Nat) : List (List Nat) → Bool :=
  pinnedFaceCommonSmallEvent stage
    (pinnedFaceDiagonalRadius stage stage)

def pinnedFaceDiagonalCutoff (stage : Nat) : Nat :=
  spinSummedJointCutoff stage (pinnedFaceDiagonalBase stage)

def couplingParametricPinnedFaceDiagonalSequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (stage : Nat) : Q' :=
  couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling (pinnedFaceDiagonalCutoff stage)
    (pinnedFaceDiagonalBase stage) (pinnedFaceDiagonalEvent stage)

theorem couplingParametricPinnedFaceDiagonalSequence_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (stage : Nat) :
    (0 : Q') ≤ couplingParametricPinnedFaceDiagonalSequence
      coupling hcoupling stage :=
  couplingParametricKCompatibleSupportEventProbability_nonnegative
    hcoupling (pinnedFaceDiagonalCutoff stage)
      (pinnedFaceDiagonalBase stage) (pinnedFaceDiagonalEvent stage)

theorem couplingParametricPinnedFaceDiagonalSequence_le_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (stage : Nat) :
    couplingParametricPinnedFaceDiagonalSequence
        coupling hcoupling stage ≤ (1 : Q') :=
  couplingParametricKCompatibleSupportEventProbability_le_one
    hcoupling (pinnedFaceDiagonalCutoff stage)
      (pinnedFaceDiagonalBase stage) (pinnedFaceDiagonalEvent stage)

/-- Moving one scheduled truncation to any larger radius costs at most its
requested dyadic precision. -/
theorem couplingParametricKPinnedFaceDiagonalVolume_abs_sub_le_half_pow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (cutoff precision sizeFloor targetRadius : Nat)
    (hradius : pinnedFaceDiagonalRadius precision sizeFloor ≤ targetRadius) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (pinnedFaceSourceBase targetRadius)
            (pinnedFaceCommonSmallEvent sizeFloor targetRadius) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (pinnedFaceSourceBase
              (pinnedFaceDiagonalRadius precision sizeFloor))
            (pinnedFaceCommonSmallEvent sizeFloor
              (pinnedFaceDiagonalRadius precision sizeFloor))) ≤
      HalfPow.half ^ precision := by
  have hraw := couplingParametricKPinnedFaceCommonVolume_abs_sub_le
    hcoupling hle cutoff
    (pinnedFaceDiagonal_floor_le_radius precision sizeFloor) hradius
  exact Q'.le_trans' _ _ _ hraw
    (pinnedFaceDiagonalBoundaryEpsilon_le_half_pow
      precision sizeFloor)

/-! ## 3. The five-leg comparison between two diagonal stages -/

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
  have hdecompose : a - b ≈ (a - c) + (c - b) :=
    Q'.eqv_symm (reassoc_cancel_local a c (-b))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.abs_add_le' (a - c) (c - b))

private theorem two_sided_add_of_abs_sub_le_local
    {a b epsilon : Q'} (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

private theorem half_pow_antitone_of_le
    {earlier later : Nat} (hstage : earlier ≤ later) :
    HalfPow.half ^ later ≤ HalfPow.half ^ earlier := by
  obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hstage
  rw [hoffset]
  exact ExpNeg.pow_half_antitone earlier offset

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

private theorem pinned_face_tail_le_two_mul_half_pow (stage : Nat) :
    Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ stage ≤
      Q'.ofNat 2 * HalfPow.half ^ stage := by
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (qpow_base_mono_local anchorDecoratedEffectiveRatio_nonnegative
      anchorDecoratedEffectiveRatio_le_half stage)
    (by decide)

def pinnedFaceDiagonalPairCoefficient : Q' :=
  (1 : Q') + ((1 : Q') +
    (((1 : Q') + (1 : Q')) + ((1 : Q') + (1 : Q'))))

theorem pinnedFaceDiagonalPairCoefficient_nonnegative :
    (0 : Q') ≤ pinnedFaceDiagonalPairCoefficient := by
  unfold pinnedFaceDiagonalPairCoefficient
  decide

/-- The five explicit comparison legs contract to one stage-uniform geometric
bound.  The common box and common cutoff are maxima/sums, so no monotonicity of
the derived schedules is assumed. -/
theorem couplingParametricPinnedFaceDiagonalSequence_pair_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {earlier later : Nat} (hstage : earlier ≤ later) :
    Q'.abs
        (couplingParametricPinnedFaceDiagonalSequence
            coupling hcoupling later -
          couplingParametricPinnedFaceDiagonalSequence
            coupling hcoupling earlier) ≤
      pinnedFaceDiagonalPairCoefficient * HalfPow.half ^ earlier := by
  let earlierRadius := pinnedFaceDiagonalRadius earlier earlier
  let laterRadius := pinnedFaceDiagonalRadius later later
  let commonRadius := max earlierRadius laterRadius
  let earlierBase := pinnedFaceSourceBase earlierRadius
  let laterBase := pinnedFaceSourceBase laterRadius
  let commonBase := pinnedFaceSourceBase commonRadius
  let earlierEvent := pinnedFaceCommonSmallEvent earlier earlierRadius
  let laterEvent := pinnedFaceCommonSmallEvent later laterRadius
  let commonEarlierEvent := pinnedFaceCommonSmallEvent earlier commonRadius
  let commonLaterEvent := pinnedFaceCommonSmallEvent later commonRadius
  let earlierCutoff := pinnedFaceDiagonalCutoff earlier
  let laterCutoff := pinnedFaceDiagonalCutoff later
  let commonCutoff := earlierCutoff + laterCutoff
  let a := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling laterCutoff laterBase laterEvent
  let b := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling earlierCutoff earlierBase earlierEvent
  let c := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling commonCutoff laterBase laterEvent
  let d := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling commonCutoff commonBase commonLaterEvent
  let e := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling commonCutoff commonBase commonEarlierEvent
  let f := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling commonCutoff earlierBase earlierEvent
  have hlaterCutoff : laterCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  have hearlierCutoff : earlierCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  have hlaterRadius : laterRadius ≤ commonRadius := by
    dsimp only [commonRadius]
    exact Nat.le_max_right _ _
  have hearlierRadius : earlierRadius ≤ commonRadius := by
    dsimp only [commonRadius]
    exact Nat.le_max_left _ _
  have hhalfLater : HalfPow.half ^ later ≤
      HalfPow.half ^ earlier := half_pow_antitone_of_le hstage
  have hca : Q'.abs (c - a) ≤ HalfPow.half ^ later := by
    dsimp only [c, a, laterCutoff, laterBase, laterEvent]
    exact
      couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
        hcoupling hle (pinnedFaceDiagonalEvent later) hlaterCutoff
  have hac : Q'.abs (a - c) ≤ HalfPow.half ^ earlier :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm a c))
      (Q'.le_trans' _ _ _ hca hhalfLater)
  have hdc : Q'.abs (d - c) ≤ HalfPow.half ^ later := by
    dsimp only [d, c, commonBase, laterBase, commonLaterEvent,
      laterEvent, laterRadius, commonRadius]
    exact
      couplingParametricKPinnedFaceDiagonalVolume_abs_sub_le_half_pow
        hcoupling hle commonCutoff later later
          (max (pinnedFaceDiagonalRadius earlier earlier)
            (pinnedFaceDiagonalRadius later later)) hlaterRadius
  have hcd : Q'.abs (c - d) ≤ HalfPow.half ^ earlier :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm c d))
      (Q'.le_trans' _ _ _ hdc hhalfLater)
  have hearlierFloorCommon : earlier ≤ commonRadius := by
    exact Nat.le_trans
      (pinnedFaceDiagonal_floor_le_radius earlier earlier)
      hearlierRadius
  have hlaterFloorCommon : later ≤ commonRadius := by
    exact Nat.le_trans
      (pinnedFaceDiagonal_floor_le_radius later later)
      hlaterRadius
  have hcommonEarlierEvent : commonEarlierEvent =
      canonicalFaceTruncatedCylinderEvent commonBase
        (pinnedFaceId commonRadius 0) earlier := by
    funext family
    dsimp only [commonEarlierEvent, commonBase]
    exact pinnedFaceCommonSmallEvent_eq_truncated
      hearlierFloorCommon family
  have hcommonLaterEvent : commonLaterEvent =
      canonicalFaceTruncatedCylinderEvent commonBase
        (pinnedFaceId commonRadius 0) later := by
    funext family
    dsimp only [commonLaterEvent, commonBase]
    exact pinnedFaceCommonSmallEvent_eq_truncated
      hlaterFloorCommon family
  have hde : Q'.abs (d - e) ≤
      Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ earlier := by
    dsimp only [d, e]
    rw [hcommonLaterEvent, hcommonEarlierEvent]
    exact
      couplingParametricKCanonicalFaceTruncatedProbability_abs_sub_le_tail
        hcoupling hle commonCutoff commonBase
          (pinnedFaceId commonRadius 0) hstage
  have hdeHalf : Q'.abs (d - e) ≤
      HalfPow.half ^ earlier + HalfPow.half ^ earlier :=
    Q'.le_trans' _ _ _ hde
      (Q'.le_trans' _ _ _
        (pinned_face_tail_le_two_mul_half_pow earlier)
        (Q'.le_of_eqv
          (ExpNeg.two_mul_eqv (HalfPow.half ^ earlier))))
  have hef : Q'.abs (e - f) ≤ HalfPow.half ^ earlier := by
    dsimp only [e, f, commonBase, earlierBase, commonEarlierEvent,
      earlierEvent, earlierRadius, commonRadius]
    exact
      couplingParametricKPinnedFaceDiagonalVolume_abs_sub_le_half_pow
        hcoupling hle commonCutoff earlier earlier
          (max (pinnedFaceDiagonalRadius earlier earlier)
            (pinnedFaceDiagonalRadius later later)) hearlierRadius
  have hfb : Q'.abs (f - b) ≤ HalfPow.half ^ earlier := by
    dsimp only [f, b, earlierCutoff, earlierBase, earlierEvent]
    exact
      couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
        hcoupling hle (pinnedFaceDiagonalEvent earlier) hearlierCutoff
  have heToB := abs_sub_triangle_local e b f
  have heToBBound : Q'.abs (e - b) ≤
      HalfPow.half ^ earlier + HalfPow.half ^ earlier :=
    Q'.le_trans' _ _ _ heToB (Q'.add_le_add hef hfb)
  have hdToB := abs_sub_triangle_local d b e
  have hdToBBound : Q'.abs (d - b) ≤
      (HalfPow.half ^ earlier + HalfPow.half ^ earlier) +
        (HalfPow.half ^ earlier + HalfPow.half ^ earlier) :=
    Q'.le_trans' _ _ _ hdToB
      (Q'.add_le_add hdeHalf heToBBound)
  have hcToB := abs_sub_triangle_local c b d
  have hcToBBound : Q'.abs (c - b) ≤
      HalfPow.half ^ earlier +
        ((HalfPow.half ^ earlier + HalfPow.half ^ earlier) +
          (HalfPow.half ^ earlier + HalfPow.half ^ earlier)) :=
    Q'.le_trans' _ _ _ hcToB
      (Q'.add_le_add hcd hdToBBound)
  have haToB := abs_sub_triangle_local a b c
  have htotal : Q'.abs (a - b) ≤
      HalfPow.half ^ earlier +
        (HalfPow.half ^ earlier +
          ((HalfPow.half ^ earlier + HalfPow.half ^ earlier) +
            (HalfPow.half ^ earlier + HalfPow.half ^ earlier))) :=
    Q'.le_trans' _ _ _ haToB
      (Q'.add_le_add hac hcToBBound)
  have hreorder :
      HalfPow.half ^ earlier +
          (HalfPow.half ^ earlier +
            ((HalfPow.half ^ earlier + HalfPow.half ^ earlier) +
              (HalfPow.half ^ earlier + HalfPow.half ^ earlier))) ≈
        pinnedFaceDiagonalPairCoefficient *
          HalfPow.half ^ earlier := by
    unfold pinnedFaceDiagonalPairCoefficient
    ring_qeqv
  have hfinal : Q'.abs (a - b) ≤
      pinnedFaceDiagonalPairCoefficient * HalfPow.half ^ earlier :=
    Q'.le_trans' _ _ _ htotal (Q'.le_of_eqv hreorder)
  simpa only [a, b, laterCutoff, earlierCutoff, laterBase, earlierBase,
    laterEvent, earlierEvent,
    couplingParametricPinnedFaceDiagonalSequence,
    pinnedFaceDiagonalCutoff, pinnedFaceDiagonalBase,
    pinnedFaceDiagonalEvent] using hfinal

/-! ## 4. The full central-face thermodynamic constructive real -/

/-- The untruncated central-face thermodynamic value, constructed directly as
the simultaneous component-truncation / volume / representation-cutoff
diagonal throughout the proved strong-coupling interval. -/
def couplingParametricPinnedFaceThermodynamicValue
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) : CReal where
  approx := couplingParametricPinnedFaceDiagonalSequence coupling hcoupling
  cauchy := by
    intro epsilon hepsilon
    let coefficient := pinnedFaceDiagonalPairCoefficient
    let scaledTolerance :=
      epsilon * Q'.invSucc coefficient.num.toNat
    have hcoefficient : (0 : Q') ≤ coefficient :=
      pinnedFaceDiagonalPairCoefficient_nonnegative
    have hscaledPositive : (0 : Q') < scaledTolerance :=
      Q'.mul_pos hepsilon (Q'.invSucc_pos coefficient.num.toNat)
    have hscaledFinal : coefficient * scaledTolerance ≤ epsilon :=
      ExpNeg.mul_le_of_mul_invSucc_toNat coefficient epsilon
        hcoefficient (Q'.le_of_lt hepsilon)
    refine ⟨scaledTolerance.den, fun m n hm hn => ?_⟩
    rcases Nat.le_total m n with hmn | hnm
    · have hpair :=
        couplingParametricPinnedFaceDiagonalSequence_pair_abs_le
          hcoupling hle hmn
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hm
      have hhalf : HalfPow.half ^ m ≤
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
          scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ m) scaledTolerance coefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs : Q'.abs
          (couplingParametricPinnedFaceDiagonalSequence
              coupling hcoupling n -
            couplingParametricPinnedFaceDiagonalSequence
              coupling hcoupling m) ≤ epsilon :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      have htwo := two_sided_add_of_abs_sub_le_local habs
      exact ⟨htwo.2, htwo.1⟩
    · have hpair :=
        couplingParametricPinnedFaceDiagonalSequence_pair_abs_le
          hcoupling hle hnm
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hn
      have hhalf : HalfPow.half ^ n ≤
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
          scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ n) scaledTolerance coefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs : Q'.abs
          (couplingParametricPinnedFaceDiagonalSequence
              coupling hcoupling m -
            couplingParametricPinnedFaceDiagonalSequence
              coupling hcoupling n) ≤ epsilon :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      exact two_sided_add_of_abs_sub_le_local habs

@[simp] theorem couplingParametricPinnedFaceThermodynamicValue_approx
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (stage : Nat) :
    (couplingParametricPinnedFaceThermodynamicValue
      coupling hcoupling hle).approx stage =
      couplingParametricPinnedFaceDiagonalSequence
        coupling hcoupling stage := rfl

theorem couplingParametricPinnedFaceThermodynamicValue_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) :
    CReal.ofQ' 0 ≤ couplingParametricPinnedFaceThermodynamicValue
      coupling hcoupling hle := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  exact couplingParametricPinnedFaceDiagonalSequence_nonnegative
    hcoupling stage

theorem couplingParametricPinnedFaceThermodynamicValue_le_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) :
    couplingParametricPinnedFaceThermodynamicValue
        coupling hcoupling hle ≤ CReal.ofQ' 1 := by
  apply CReal.le_ofQ'_of_approx_le
  intro stage
  exact couplingParametricPinnedFaceDiagonalSequence_le_one
    hcoupling stage

/-! ## 5. Exact full-face approximants and their thermodynamic CReal -/

def pinnedFaceDiagonalFace (stage : Nat) : Nat :=
  pinnedFaceId (pinnedFaceDiagonalRadius stage stage) 0

def couplingParametricPinnedFullFaceDiagonalSequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (stage : Nat) : Q' :=
  couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling (pinnedFaceDiagonalCutoff stage)
    (pinnedFaceDiagonalBase stage)
    (familyContainsFaceB (pinnedFaceDiagonalFace stage))

theorem couplingParametricPinnedFullFaceDiagonalSequence_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (stage : Nat) :
    (0 : Q') ≤ couplingParametricPinnedFullFaceDiagonalSequence
      coupling hcoupling stage :=
  couplingParametricKCompatibleSupportEventProbability_nonnegative
    hcoupling (pinnedFaceDiagonalCutoff stage)
      (pinnedFaceDiagonalBase stage)
      (familyContainsFaceB (pinnedFaceDiagonalFace stage))

theorem couplingParametricPinnedFullFaceDiagonalSequence_le_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (stage : Nat) :
    couplingParametricPinnedFullFaceDiagonalSequence
        coupling hcoupling stage ≤ (1 : Q') :=
  couplingParametricKCompatibleSupportEventProbability_le_one
    hcoupling (pinnedFaceDiagonalCutoff stage)
      (pinnedFaceDiagonalBase stage)
      (familyContainsFaceB (pinnedFaceDiagonalFace stage))

/-- At every diagonal stage the auxiliary finite chart differs from the exact
full central-face event by the explicit omitted-component tail. -/
theorem couplingParametricPinnedFullFaceDiagonalSequence_abs_sub_truncated_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (stage : Nat) :
    Q'.abs
        (couplingParametricPinnedFullFaceDiagonalSequence
            coupling hcoupling stage -
          couplingParametricPinnedFaceDiagonalSequence
            coupling hcoupling stage) ≤
      Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ stage := by
  have hevent : pinnedFaceDiagonalEvent stage =
      canonicalFaceTruncatedCylinderEvent
        (pinnedFaceDiagonalBase stage)
        (pinnedFaceDiagonalFace stage) stage := by
    funext family
    unfold pinnedFaceDiagonalEvent pinnedFaceDiagonalBase
      pinnedFaceDiagonalFace
    exact pinnedFaceCommonSmallEvent_eq_truncated
      (pinnedFaceDiagonal_floor_le_radius stage stage) family
  unfold couplingParametricPinnedFullFaceDiagonalSequence
    couplingParametricPinnedFaceDiagonalSequence
  rw [hevent]
  exact
    couplingParametricKCanonicalFaceFullProbability_abs_sub_truncated_le_tail
      hcoupling hle (pinnedFaceDiagonalCutoff stage)
        (pinnedFaceDiagonalBase stage) (pinnedFaceDiagonalFace stage) stage

def pinnedFullFaceDiagonalPairCoefficient : Q' :=
  ((1 : Q') + (1 : Q')) +
    (pinnedFaceDiagonalPairCoefficient + ((1 : Q') + (1 : Q')))

theorem pinnedFullFaceDiagonalPairCoefficient_nonnegative :
    (0 : Q') ≤ pinnedFullFaceDiagonalPairCoefficient := by
  unfold pinnedFullFaceDiagonalPairCoefficient
    pinnedFaceDiagonalPairCoefficient
  decide

theorem couplingParametricPinnedFullFaceDiagonalSequence_pair_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {earlier later : Nat} (hstage : earlier ≤ later) :
    Q'.abs
        (couplingParametricPinnedFullFaceDiagonalSequence
            coupling hcoupling later -
          couplingParametricPinnedFullFaceDiagonalSequence
            coupling hcoupling earlier) ≤
      pinnedFullFaceDiagonalPairCoefficient *
        HalfPow.half ^ earlier := by
  let fullLater := couplingParametricPinnedFullFaceDiagonalSequence
    coupling hcoupling later
  let truncatedLater := couplingParametricPinnedFaceDiagonalSequence
    coupling hcoupling later
  let truncatedEarlier := couplingParametricPinnedFaceDiagonalSequence
    coupling hcoupling earlier
  let fullEarlier := couplingParametricPinnedFullFaceDiagonalSequence
    coupling hcoupling earlier
  have hhalfLater := half_pow_antitone_of_le hstage
  have hlaterRaw : Q'.abs (fullLater - truncatedLater) ≤
      Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ later := by
    dsimp only [fullLater, truncatedLater]
    exact
      couplingParametricPinnedFullFaceDiagonalSequence_abs_sub_truncated_le
        hcoupling hle later
  have hlaterTail : Q'.abs (fullLater - truncatedLater) ≤
      HalfPow.half ^ earlier + HalfPow.half ^ earlier := by
    have htwoHalf : Q'.ofNat 2 * HalfPow.half ^ later ≤
        Q'.ofNat 2 * HalfPow.half ^ earlier :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hhalfLater (by decide)
    exact Q'.le_trans' _ _ _ hlaterRaw
      (Q'.le_trans' _ _ _
        (pinned_face_tail_le_two_mul_half_pow later)
        (Q'.le_trans' _ _ _ htwoHalf
          (Q'.le_of_eqv
            (ExpNeg.two_mul_eqv (HalfPow.half ^ earlier)))))
  have htruncated : Q'.abs (truncatedLater - truncatedEarlier) ≤
      pinnedFaceDiagonalPairCoefficient * HalfPow.half ^ earlier := by
    dsimp only [truncatedLater, truncatedEarlier]
    exact couplingParametricPinnedFaceDiagonalSequence_pair_abs_le
      hcoupling hle hstage
  have hearlierRaw : Q'.abs (fullEarlier - truncatedEarlier) ≤
      Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ earlier := by
    dsimp only [fullEarlier, truncatedEarlier]
    exact
      couplingParametricPinnedFullFaceDiagonalSequence_abs_sub_truncated_le
        hcoupling hle earlier
  have hearlierTail : Q'.abs (truncatedEarlier - fullEarlier) ≤
      HalfPow.half ^ earlier + HalfPow.half ^ earlier := by
    have horiented : Q'.abs (truncatedEarlier - fullEarlier) ≤
        Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ earlier :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
            truncatedEarlier fullEarlier)) hearlierRaw
    exact Q'.le_trans' _ _ _ horiented
      (Q'.le_trans' _ _ _
        (pinned_face_tail_le_two_mul_half_pow earlier)
        (Q'.le_of_eqv
          (ExpNeg.two_mul_eqv (HalfPow.half ^ earlier))))
  have hmiddleTriangle :=
    abs_sub_triangle_local truncatedLater fullEarlier truncatedEarlier
  have hmiddle : Q'.abs (truncatedLater - fullEarlier) ≤
      pinnedFaceDiagonalPairCoefficient * HalfPow.half ^ earlier +
        (HalfPow.half ^ earlier + HalfPow.half ^ earlier) :=
    Q'.le_trans' _ _ _ hmiddleTriangle
      (Q'.add_le_add htruncated hearlierTail)
  have houterTriangle :=
    abs_sub_triangle_local fullLater fullEarlier truncatedLater
  have htotal : Q'.abs (fullLater - fullEarlier) ≤
      (HalfPow.half ^ earlier + HalfPow.half ^ earlier) +
        (pinnedFaceDiagonalPairCoefficient * HalfPow.half ^ earlier +
          (HalfPow.half ^ earlier + HalfPow.half ^ earlier)) :=
    Q'.le_trans' _ _ _ houterTriangle
      (Q'.add_le_add hlaterTail hmiddle)
  have hreorder :
      (HalfPow.half ^ earlier + HalfPow.half ^ earlier) +
          (pinnedFaceDiagonalPairCoefficient * HalfPow.half ^ earlier +
            (HalfPow.half ^ earlier + HalfPow.half ^ earlier)) ≈
        pinnedFullFaceDiagonalPairCoefficient *
          HalfPow.half ^ earlier := by
    unfold pinnedFullFaceDiagonalPairCoefficient
      pinnedFaceDiagonalPairCoefficient
    ring_qeqv
  have hfinal : Q'.abs (fullLater - fullEarlier) ≤
      pinnedFullFaceDiagonalPairCoefficient *
        HalfPow.half ^ earlier :=
    Q'.le_trans' _ _ _ htotal (Q'.le_of_eqv hreorder)
  simpa only [fullLater, fullEarlier] using hfinal

/-- The thermodynamic `CReal` whose approximants are literal full central-face
probabilities in finite SU(2) compatible-support laws. -/
def couplingParametricPinnedFullFaceThermodynamicValue
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) : CReal where
  approx := couplingParametricPinnedFullFaceDiagonalSequence
    coupling hcoupling
  cauchy := by
    intro epsilon hepsilon
    let coefficient := pinnedFullFaceDiagonalPairCoefficient
    let scaledTolerance :=
      epsilon * Q'.invSucc coefficient.num.toNat
    have hcoefficient : (0 : Q') ≤ coefficient :=
      pinnedFullFaceDiagonalPairCoefficient_nonnegative
    have hscaledPositive : (0 : Q') < scaledTolerance :=
      Q'.mul_pos hepsilon (Q'.invSucc_pos coefficient.num.toNat)
    have hscaledFinal : coefficient * scaledTolerance ≤ epsilon :=
      ExpNeg.mul_le_of_mul_invSucc_toNat coefficient epsilon
        hcoefficient (Q'.le_of_lt hepsilon)
    refine ⟨scaledTolerance.den, fun m n hm hn => ?_⟩
    rcases Nat.le_total m n with hmn | hnm
    · have hpair :=
        couplingParametricPinnedFullFaceDiagonalSequence_pair_abs_le
          hcoupling hle hmn
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hm
      have hhalf : HalfPow.half ^ m ≤
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
          scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ m) scaledTolerance coefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs : Q'.abs
          (couplingParametricPinnedFullFaceDiagonalSequence
              coupling hcoupling n -
            couplingParametricPinnedFullFaceDiagonalSequence
              coupling hcoupling m) ≤ epsilon :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      have htwo := two_sided_add_of_abs_sub_le_local habs
      exact ⟨htwo.2, htwo.1⟩
    · have hpair :=
        couplingParametricPinnedFullFaceDiagonalSequence_pair_abs_le
          hcoupling hle hnm
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hn
      have hhalf : HalfPow.half ^ n ≤
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
          scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ n) scaledTolerance coefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs : Q'.abs
          (couplingParametricPinnedFullFaceDiagonalSequence
              coupling hcoupling m -
            couplingParametricPinnedFullFaceDiagonalSequence
              coupling hcoupling n) ≤ epsilon :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      exact two_sided_add_of_abs_sub_le_local habs

@[simp] theorem couplingParametricPinnedFullFaceThermodynamicValue_approx
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (stage : Nat) :
    (couplingParametricPinnedFullFaceThermodynamicValue
      coupling hcoupling hle).approx stage =
      couplingParametricPinnedFullFaceDiagonalSequence
        coupling hcoupling stage := rfl

theorem couplingParametricPinnedFullFaceThermodynamicValue_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) :
    CReal.ofQ' 0 ≤ couplingParametricPinnedFullFaceThermodynamicValue
      coupling hcoupling hle := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  exact couplingParametricPinnedFullFaceDiagonalSequence_nonnegative
    hcoupling stage

theorem couplingParametricPinnedFullFaceThermodynamicValue_le_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) :
    couplingParametricPinnedFullFaceThermodynamicValue
        coupling hcoupling hle ≤ CReal.ofQ' 1 := by
  apply CReal.le_ofQ'_of_approx_le
  intro stage
  exact couplingParametricPinnedFullFaceDiagonalSequence_le_one
    hcoupling stage

/-- Removing the component truncation does not change the thermodynamic
constructive real.  The two diagonal sequences differ at stage `s` by the
explicit omitted-component tail, and that tail tends to zero with a witnessed
dyadic modulus. -/
theorem couplingParametricPinnedFullFaceThermodynamicValue_equiv_truncationDiagonal
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) :
    CReal.Equiv
      (couplingParametricPinnedFullFaceThermodynamicValue
        coupling hcoupling hle)
      (couplingParametricPinnedFaceThermodynamicValue
        coupling hcoupling hle) := by
  intro epsilon hepsilon
  let tolerance := HalfPow.half * epsilon
  have htolerance : (0 : Q') < tolerance :=
    ExpNeg.half_mul_pos epsilon hepsilon
  refine ⟨tolerance.den, fun stage hstage => ?_⟩
  obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hstage
  have hhalf : HalfPow.half ^ stage ≤
      HalfPow.half ^ tolerance.den := by
    rw [hoffset]
    exact ExpNeg.pow_half_antitone tolerance.den offset
  have hhalfTolerance : HalfPow.half ^ tolerance.den ≤ tolerance :=
    HalfPow.pow_half_le tolerance htolerance
  have htwoHalf : Q'.ofNat 2 * HalfPow.half ^ stage ≤
      Q'.ofNat 2 * tolerance :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.le_trans' _ _ _ hhalf hhalfTolerance) (by decide)
  have hcollapse : Q'.ofNat 2 * tolerance ≈ epsilon := by
    refine Q'.eqv_trans _ (tolerance + tolerance) _
      (ExpNeg.two_mul_eqv tolerance) ?_
    dsimp only [tolerance]
    exact ExpNeg.two_halves epsilon
  have htail :
      Q'.abs
          (couplingParametricPinnedFullFaceDiagonalSequence
              coupling hcoupling stage -
            couplingParametricPinnedFaceDiagonalSequence
              coupling hcoupling stage) ≤ epsilon := by
    refine Q'.le_trans' _ _ _
      (couplingParametricPinnedFullFaceDiagonalSequence_abs_sub_truncated_le
        hcoupling hle stage)
      (Q'.le_trans' _ _ _
        (pinned_face_tail_le_two_mul_half_pow stage)
        (Q'.le_trans' _ _ _ htwoHalf (Q'.le_of_eqv hcollapse)))
  change
    couplingParametricPinnedFullFaceDiagonalSequence
        coupling hcoupling stage ≤
      couplingParametricPinnedFaceDiagonalSequence
          coupling hcoupling stage + epsilon ∧
    couplingParametricPinnedFaceDiagonalSequence
        coupling hcoupling stage ≤
      couplingParametricPinnedFullFaceDiagonalSequence
          coupling hcoupling stage + epsilon
  exact two_sided_add_of_abs_sub_le_local htail

#print axioms pinnedFaceCommonSmallRoots_length
#print axioms pinnedFaceDiagonalBoundaryTolerance_pos
#print axioms pinnedFaceDiagonalBoundaryEpsilon_le_half_pow
#print axioms couplingParametricPinnedFaceDiagonalSequence_nonnegative
#print axioms couplingParametricKPinnedFaceDiagonalVolume_abs_sub_le_half_pow
#print axioms couplingParametricPinnedFaceDiagonalSequence_pair_abs_le
#print axioms couplingParametricPinnedFaceThermodynamicValue
#print axioms couplingParametricPinnedFaceThermodynamicValue_nonnegative
#print axioms couplingParametricPinnedFaceThermodynamicValue_le_one
#print axioms couplingParametricPinnedFullFaceDiagonalSequence_abs_sub_truncated_le
#print axioms couplingParametricPinnedFullFaceDiagonalSequence_pair_abs_le
#print axioms couplingParametricPinnedFullFaceThermodynamicValue
#print axioms couplingParametricPinnedFullFaceThermodynamicValue_nonnegative
#print axioms couplingParametricPinnedFullFaceThermodynamicValue_le_one
#print axioms couplingParametricPinnedFullFaceThermodynamicValue_equiv_truncationDiagonal

end YMGap.Continuum.Z4CanonicalCentralFaceDiagonal
