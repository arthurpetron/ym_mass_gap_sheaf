/-
# Rational prefix/image windows for the calibrated empty BF4 feature

The empty feature word is rank one.  Splitting its normalization symmetrically
would introduce a square root of the vacuum partition.  That is unnecessary:
two asymmetric rational profiles `L` and `R` factor the calibrated empty
joint exactly.

For the physical marginal `pi`, the elementary identity

  L(x)R(y) - pi(x)pi(y)
    = (L(x)-pi(x))R(y) + pi(x)(R(y)-pi(y))

gives the row estimate

  rowAbs(empty - pi tensor pi)(x)
    <= |L(x)-pi(x)| sum_y |R(y)|
       + pi(x) sum_y |R(y)-pi(y)|.

This is the constructive prefix/image window needed for the empty-channel
`1/16` estimate.  All quantities are finite rational sums.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CalibratedFeatureGramCoreTail
import YMGap.Continuum.DiffProduct

namespace YMGap.Continuum.BF4CalibratedEmptyProfileWindow

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4CalibratedFeatureGramCoreTail
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4PhysicalRecenteredEndpointRate
open YMGap.Continuum.DiffProduct
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

/-- Cancellation-free rational polynomial normalization. -/
local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Exact rational factorization -/

/-- Vacuum empty-channel half-amplitude. -/
def bf4VacuumEmptyHalf
    (diagonalOrder : Nat) : Q' :=
  bf4MehlerHalfAmplitude
    (diagonalOrder + 1) zeroEdgeLabelling []

theorem bf4VacuumEmptyHalf_pos
    (diagonalOrder : Nat) :
    (0 : Q') <
      bf4VacuumEmptyHalf diagonalOrder :=
  (shiftedDiagonalVacuumCertificate
    diagonalOrder).empty_half_pos

/-- Right image profile.  Its vacuum value is exactly `pi0`. -/
def calibratedEmptyRightProfile
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder : Nat)
    (state : EdgeLabelling) : Q' :=
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent zeroEdgeLabelling
  Q'.divPos
    (pi0 *
      bf4MehlerHalfAmplitude
        (diagonalOrder + 1) state [])
    (bf4VacuumEmptyHalf diagonalOrder)
    (bf4VacuumEmptyHalf_pos diagonalOrder)

/-- Left prefix profile.  Its normalization contains the full finite
feature-Gram vacuum partition. -/
def calibratedEmptyLeftProfile
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (state : EdgeLabelling) : Q' :=
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent zeroEdgeLabelling
  Q'.divPos
    ((pi0 * bf4VacuumEmptyHalf diagonalOrder) *
      bf4MehlerHalfAmplitude
        (diagonalOrder + 1) state [])
    (bf4MehlerGramVacuumPartition
      (diagonalOrder + 1) crossOrder)
    (bf4MehlerGramVacuumPartition_pos
      (shiftedDiagonalVacuumCertificate diagonalOrder)
      crossOrder)

/-- The asymmetric rational profiles multiply to the exact calibrated empty
feature joint. -/
theorem calibratedEmptyFeatureJoint_eqv_profiles
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (left right : EdgeLabelling) :
    calibratedBF4EmptyFeatureJoint
        w hw K halfExtent diagonalOrder crossOrder
        left right ≈
      calibratedEmptyLeftProfile
          w hw K halfExtent diagonalOrder crossOrder left *
        calibratedEmptyRightProfile
          w hw K halfExtent diagonalOrder right := by
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent zeroEdgeLabelling
  let h0 := bf4VacuumEmptyHalf diagonalOrder
  let hleft :=
    bf4MehlerHalfAmplitude
      (diagonalOrder + 1) left []
  let hright :=
    bf4MehlerHalfAmplitude
      (diagonalOrder + 1) right []
  let partition :=
    bf4MehlerGramVacuumPartition
      (diagonalOrder + 1) crossOrder
  let hpartition :=
    bf4MehlerGramVacuumPartition_pos
      (shiftedDiagonalVacuumCertificate diagonalOrder)
      crossOrder
  let rh0 :=
    Q'.recipPos h0
      (bf4VacuumEmptyHalf_pos diagonalOrder)
  let rpartition :=
    Q'.recipPos partition hpartition
  have hcancel : h0 * rh0 ≈ 1 :=
    Q'.mul_recipPos_eqv h0
      (bf4VacuumEmptyHalf_pos diagonalOrder)
  unfold calibratedBF4EmptyFeatureJoint
    normalizedBF4EmptyFeatureJoint
    normalizedBF4FeatureWordWeight
    bf4FeatureWordWeight
    calibratedEmptyLeftProfile
    calibratedEmptyRightProfile
    Q'.divPos
  change
    (pi0 * pi0) *
          ((1 * rpartition) * (hleft * hright)) ≈
      (((pi0 * h0) * hleft) * rpartition) *
        ((pi0 * hright) * rh0)
  refine Q'.eqv_trans _
    (1 *
      ((pi0 * pi0) *
        (rpartition * (hleft * hright)))) _ ?_ ?_
  · q_ring
  refine Q'.eqv_trans _
    ((h0 * rh0) *
      ((pi0 * pi0) *
        (rpartition * (hleft * hright)))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm hcancel)
  · q_ring

/-- The right profile sends the vacuum state exactly to the physical vacuum
marginal. -/
theorem calibratedEmptyRightProfile_vacuum
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder : Nat) :
    calibratedEmptyRightProfile
        w hw K halfExtent diagonalOrder
        zeroEdgeLabelling ≈
      centralPhysicalRowMarginal
        w hw K halfExtent zeroEdgeLabelling := by
  unfold calibratedEmptyRightProfile
    bf4VacuumEmptyHalf
    Q'.divPos
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent zeroEdgeLabelling
  let h0 :=
    bf4MehlerHalfAmplitude
      (diagonalOrder + 1) zeroEdgeLabelling []
  let rh0 :=
    Q'.recipPos h0
      (bf4VacuumEmptyHalf_pos diagonalOrder)
  refine Q'.eqv_trans _
    (pi0 * (h0 * rh0)) _ ?_ ?_
  · exact Q'.mul_assoc_eqv pi0 h0 rh0
  refine Q'.eqv_trans _ (pi0 * 1) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left pi0 _ _
      (Q'.mul_recipPos_eqv h0
        (bf4VacuumEmptyHalf_pos diagonalOrder))
  · exact Q'.mul_one_eqv pi0

/-! ## 2. Finite image and mismatch masses -/

/-- Complete absolute mass of the right image profile on the retained
physical carrier. -/
def calibratedEmptyRightProfileAbsMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder : Nat) : Q' :=
  listQSum
    (fun state =>
      Q'.abs
        (calibratedEmptyRightProfile
          w hw K halfExtent diagonalOrder state))
    (centralPositiveHalfStates w hw K halfExtent)

/-- Complete `L1` mismatch between the right image profile and the physical
stationary marginal. -/
def calibratedEmptyRightProfileMismatchMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder : Nat) : Q' :=
  listQSum
    (fun state =>
      Q'.abs
        (calibratedEmptyRightProfile
            w hw K halfExtent diagonalOrder state +
          (-centralPhysicalRowMarginal
            w hw K halfExtent state)))
    (centralPositiveHalfStates w hw K halfExtent)

/-- Pointwise left-prefix mismatch. -/
def calibratedEmptyLeftProfileMismatch
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (source : EdgeLabelling) : Q' :=
  Q'.abs
    (calibratedEmptyLeftProfile
        w hw K halfExtent diagonalOrder crossOrder source +
      (-centralPhysicalRowMarginal
        w hw K halfExtent source))

/-! ## 3. Prefix/image row theorem -/

/-- The empty-feature row mismatch is paid exactly by one source-prefix
window and two finite right-image masses. -/
theorem calibratedEmptyPhysicalMismatchRowMass_le_profile_windows
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (source : EdgeLabelling) :
    calibratedEmptyPhysicalMismatchRowMass
        w hw K halfExtent diagonalOrder crossOrder source ≤
      calibratedEmptyLeftProfileMismatch
          w hw K halfExtent diagonalOrder crossOrder source *
        calibratedEmptyRightProfileAbsMass
          w hw K halfExtent diagonalOrder +
      centralPhysicalRowMarginal
          w hw K halfExtent source *
        calibratedEmptyRightProfileMismatchMass
          w hw K halfExtent diagonalOrder := by
  let states :=
    centralPositiveHalfStates w hw K halfExtent
  let leftProfile :=
    calibratedEmptyLeftProfile
      w hw K halfExtent diagonalOrder crossOrder
  let rightProfile :=
    calibratedEmptyRightProfile
      w hw K halfExtent diagonalOrder
  let marginal :=
    centralPhysicalRowMarginal
      w hw K halfExtent
  let leftMismatch :=
    Q'.abs
      (leftProfile source + (-marginal source))
  let rightAbs := fun target =>
    Q'.abs (rightProfile target)
  let rightMismatch := fun target =>
    Q'.abs
      (rightProfile target + (-marginal target))
  have hentry :
      ∀ target,
        Q'.abs
            (calibratedBF4EmptyFeatureJoint
                w hw K halfExtent diagonalOrder crossOrder
                source target +
              (-(marginal source * marginal target))) ≤
          leftMismatch * rightAbs target +
            marginal source * rightMismatch target := by
    intro target
    have hfactor :=
      calibratedEmptyFeatureJoint_eqv_profiles
        w hw K halfExtent diagonalOrder crossOrder
        source target
    have hrewrite :
        calibratedBF4EmptyFeatureJoint
              w hw K halfExtent diagonalOrder crossOrder
              source target +
            (-(marginal source * marginal target)) ≈
          (leftProfile source + (-marginal source)) *
              rightProfile target +
            marginal source *
              (rightProfile target +
                (-marginal target)) := by
      refine Q'.eqv_trans _
        (leftProfile source * rightProfile target +
          (-(marginal source * marginal target))) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _ hfactor
      · refine Q'.eqv_trans _
          (rightProfile target * leftProfile source +
            (-(marginal target * marginal source))) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (Q'.mul_comm_eqv _ _)
            (Q'.neg_eqv_congr _ _
              (Q'.mul_comm_eqv _ _))
        refine Q'.eqv_trans _
          ((rightProfile target + (-marginal target)) *
                marginal source +
              rightProfile target *
                (leftProfile source +
                  (-marginal source))) _ ?_ ?_
        · exact DiffProduct.split_core
            (rightProfile target)
            (marginal target)
            (leftProfile source)
            (marginal source)
        refine Q'.eqv_trans _
          (marginal source *
                (rightProfile target +
                  (-marginal target)) +
              (leftProfile source +
                  (-marginal source)) *
                rightProfile target) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (Q'.mul_comm_eqv _ _)
            (Q'.mul_comm_eqv _ _)
        · exact Q'.add_comm_eqv _ _
    have htriangle :=
      Q'.abs_add_le'
        ((leftProfile source + (-marginal source)) *
          rightProfile target)
        (marginal source *
          (rightProfile target +
            (-marginal target)))
    have hleftProduct :=
      YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
        (leftProfile source + (-marginal source))
        (rightProfile target)
    have hrightProduct :=
      YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
        (marginal source)
        (rightProfile target + (-marginal target))
    have hmarginalNonnegative :
        (0 : Q') ≤ marginal source :=
      centralPhysicalRowMarginal_nonnegative
        hw K halfExtent source
    rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
      hmarginalNonnegative] at hrightProduct
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr hrewrite))
      (Q'.le_trans' _ _ _ htriangle ?_)
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add hleftProduct hrightProduct) ?_
    exact Q'.le_refl' _
  unfold calibratedEmptyPhysicalMismatchRowMass
    finiteJointDifferenceAbsRowMass
    centralPhysicalVacuumJoint
  refine Q'.le_trans' _ _ _
    (listQSum_mono
      (fun target =>
        Q'.abs
          (calibratedBF4EmptyFeatureJoint
              w hw K halfExtent diagonalOrder crossOrder
              source target +
            (-(marginal source * marginal target))))
      (fun target =>
        leftMismatch * rightAbs target +
          marginal source * rightMismatch target)
      states
      (fun target _ => hentry target)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (listQSum_add
        (fun target => leftMismatch * rightAbs target)
        (fun target =>
          marginal source * rightMismatch target)
        states)) ?_
  refine Q'.le_of_eqv
    (Q'.add_eqv_congr' ?_ ?_)
  · exact listQSum_mul_left
      leftMismatch rightAbs states
  · exact listQSum_mul_left
      (marginal source) rightMismatch states

/-- Any direct prefix/image payment proves the empty-channel row budget. -/
theorem calibratedEmptyPhysicalMismatchRowMass_le_of_profile_budget
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder crossOrder : Nat}
    {source : EdgeLabelling}
    {epsilon : Q'}
    (hbudget :
      calibratedEmptyLeftProfileMismatch
            w hw K halfExtent diagonalOrder crossOrder source *
          calibratedEmptyRightProfileAbsMass
            w hw K halfExtent diagonalOrder +
        centralPhysicalRowMarginal
            w hw K halfExtent source *
          calibratedEmptyRightProfileMismatchMass
            w hw K halfExtent diagonalOrder ≤
        epsilon *
          centralPhysicalRowMarginal
            w hw K halfExtent source) :
    calibratedEmptyPhysicalMismatchRowMass
        w hw K halfExtent diagonalOrder crossOrder source ≤
      epsilon *
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
  Q'.le_trans' _ _ _
    (calibratedEmptyPhysicalMismatchRowMass_le_profile_windows
      w hw K halfExtent diagonalOrder crossOrder source)
    hbudget

/-- A spacing-uniform `1/16` prefix/image payment together with a `1/16`
nonempty-feature row tail proves the corrected spectral `1/8` row. -/
theorem physicalCenteredEndpointRowMass_le_eighth_of_profile_and_nonempty
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
    (hnonempty :
      calibratedNonemptyFeatureAbsRowMass
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
          w hw K halfExtent source := by
  exact physicalCenteredEndpointRowMass_le_eighth_of_sixteenths
    (calibratedEmptyPhysicalMismatchRowMass_le_of_profile_budget
      hprofile)
    hnonempty

end YMGap.Continuum.BF4CalibratedEmptyProfileWindow

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4CalibratedEmptyProfileWindow.calibratedEmptyFeatureJoint_eqv_profiles
#print axioms YMGap.Continuum.BF4CalibratedEmptyProfileWindow.calibratedEmptyRightProfile_vacuum
#print axioms YMGap.Continuum.BF4CalibratedEmptyProfileWindow.calibratedEmptyPhysicalMismatchRowMass_le_profile_windows
#print axioms YMGap.Continuum.BF4CalibratedEmptyProfileWindow.calibratedEmptyPhysicalMismatchRowMass_le_of_profile_budget
#print axioms YMGap.Continuum.BF4CalibratedEmptyProfileWindow.physicalCenteredEndpointRowMass_le_eighth_of_profile_and_nonempty
