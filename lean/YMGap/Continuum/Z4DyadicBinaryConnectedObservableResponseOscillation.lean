/-
# Sharp normalized oscillation for the connected remainder observable

For fixed blocked and coarse face moments `beta,gamma` in the unit interval,
the connected remainder observable takes the four values

  `0`, `beta`, `gamma`, `beta + gamma - 1`.

Their diameter is at most one.  This file combines that sharp range fact with
the exact rational-observable two-row determinant and its connected-carrier
envelope.  The intended endpoint is a normalized pairwise response estimate
that both has absolute value at most one and is dominated by the sum of the
root and target one-face connected-envelope fractions.

No posterior variance, dense form bound, completed spectral gap,
thermodynamic limit, continuum theory, or Clay theorem is asserted here.

Constructive contract: Boolean case analysis, finite rational sums, explicit
positive-denominator cancellation, and previously proved SU(2)-specific
envelopes only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, enlarged heartbeat
budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedObservableTwoRowDeterminant
import YMGap.Continuum.Z4DyadicBinaryGlobalConnectedResponseOscillation

namespace YMGap.Continuum.Z4DyadicBinaryConnectedObservableResponseOscillation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderL1Bound
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryConnectedObservableTwoRowDeterminant
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedResponseOscillation
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelope
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelopeNormalization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseDeterminant
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private theorem unitInterval_abs_le_one (value : Q')
    (hvalue : (0 : Q') ≤ value ∧ value ≤ (1 : Q')) :
    Q'.abs value ≤ (1 : Q') :=
  Q'.abs_le_of_bounds
    (Q'.le_trans' _ _ _ (by decide) hvalue.1) hvalue.2

private theorem unitInterval_difference_abs_le_one (left right : Q')
    (hleft : (0 : Q') ≤ left ∧ left ≤ (1 : Q'))
    (hright : (0 : Q') ≤ right ∧ right ≤ (1 : Q')) :
    Q'.abs (left - right) ≤ (1 : Q') := by
  apply Q'.abs_le_of_bounds
  · have hadd := Q'.add_le_add
      (Q'.neg_le_neg hright.2) hleft.1
    rw [Q'.add_zero'] at hadd
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (Q'.add_comm_eqv (-right) left))
  · have hadd := Q'.add_le_add hleft.2
      (Q'.nonpos_neg_of_nonneg hright.1)
    rwa [Q'.add_zero'] at hadd

private theorem unitInterval_sum_sub_one_abs_le_one (left right : Q')
    (hleft : (0 : Q') ≤ left ∧ left ≤ (1 : Q'))
    (hright : (0 : Q') ≤ right ∧ right ≤ (1 : Q')) :
    Q'.abs ((-1 : Q') + (left + right)) ≤ (1 : Q') := by
  apply Q'.abs_le
  · have hsumNonnegative : (0 : Q') ≤ left + right :=
      Q'.zero_le_add _ _ hleft.1 hright.1
    have hadd := Q'.add_le_add_left
      (-1) 0 (left + right) hsumNonnegative
    exact Q'.le_trans' _ _ _ (by decide) hadd
  · have hsumLeTwo : left + right ≤ (1 : Q') + 1 :=
      Q'.add_le_add hleft.2 hright.2
    have hadd := Q'.add_le_add_left
      (-1) (left + right) ((1 : Q') + 1) hsumLeTwo
    exact Q'.le_trans' _ _ _ hadd (by decide)

private theorem abs_le_one_of_abs_eqv {value reference : Q'}
    (heqv : Q'.abs value ≈ Q'.abs reference)
    (hreference : Q'.abs reference ≤ (1 : Q')) :
    Q'.abs value ≤ (1 : Q') :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv) hreference

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → lower item ≤ upper item) →
      listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle => by
      simp only [listQSum]
      exact Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

private theorem abs_mul_nonnegative_left_eqv_local
    (factor value : Q') (hfactor : (0 : Q') ≤ factor) :
    Q'.abs (factor * value) ≈ factor * Q'.abs value := by
  refine Q'.eqv_trans _ (Q'.abs (value * factor)) _
    (Q'.abs_eqv_congr (Q'.mul_comm_eqv factor value)) ?_
  refine Q'.eqv_trans _ (Q'.abs value * factor) _
    (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right value hfactor) ?_
  exact Q'.mul_comm_eqv (Q'.abs value) factor

private theorem abs_response_mul_two_scale_eqv_two_cross_abs_local
    (response scale rawCross : Q')
    (hscale : (0 : Q') ≤ scale)
    (hclear : response * scale ≈ rawCross) :
    Q'.abs response * ((2 : Q') * scale) ≈
      Q'.abs ((2 : Q') * rawCross) := by
  refine Q'.eqv_trans _
    ((2 : Q') * (Q'.abs response * scale)) _ ?_ ?_
  · refine Q'.eqv_trans _
      ((Q'.abs response * (2 : Q')) * scale) _ ?_ ?_
    · exact Q'.eqv_symm
        (Q'.mul_assoc_eqv (Q'.abs response) (2 : Q') scale)
    refine Q'.eqv_trans _
      (((2 : Q') * Q'.abs response) * scale) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ scale
        (Q'.mul_comm_eqv (Q'.abs response) (2 : Q'))
    · exact Q'.mul_assoc_eqv (2 : Q') (Q'.abs response) scale
  refine Q'.eqv_trans _
    ((2 : Q') * Q'.abs (response * scale)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right response hscale))
  refine Q'.eqv_trans _
    ((2 : Q') * Q'.abs rawCross) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.abs_eqv_congr hclear)
  exact Q'.eqv_symm
    (abs_mul_nonnegative_left_eqv_local
      (2 : Q') rawCross (Q'.le_of_lt (Q'.ofNat_succ_pos 1)))

private theorem divPos_add_eqv_add_divPos
    (left right denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos (left + right) denominator hdenominator ≈
      Q'.divPos left denominator hdenominator +
        Q'.divPos right denominator hdenominator := by
  unfold Q'.divPos
  exact Q'.add_mul_eqv left right
    (Q'.recipPos denominator hdenominator)

private theorem zero_sub_eqv_neg_local (value : Q') :
    (0 : Q') - value ≈ -value := by
  change (0 : Q') + (-value) ≈ -value
  exact Q'.eqv_of_eq (Q'.zero_add' (-value))

private theorem sub_self_eqv_zero_local (value : Q') :
    value - value ≈ 0 := by
  change value + (-value) ≈ 0
  exact Q'.add_neg_self_eqv value

private theorem left_sub_left_add_eqv_neg_right_local
    (left right : Q') :
    left - (left + right) ≈ -right := by
  change left + -(left + right) ≈ -right
  refine Q'.eqv_trans _ (left + ((-left) + (-right))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left left _ _
      (Q'.neg_add_eqv left right)
  refine Q'.eqv_trans _ ((left + (-left)) + (-right)) _
    (Q'.eqv_symm (Q'.add_assoc_eqv left (-left) (-right))) ?_
  refine Q'.eqv_trans _ (0 + (-right)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ (-right)
      (Q'.add_neg_self_eqv left)
  · exact Q'.eqv_of_eq (Q'.zero_add' (-right))

private theorem left_add_right_sub_left_eqv_right_local
    (left right : Q') :
    (left + right) - left ≈ right := by
  change (left + right) + (-left) ≈ right
  refine Q'.eqv_trans _ ((-left) + (left + right)) _
    (Q'.add_comm_eqv (left + right) (-left)) ?_
  refine Q'.eqv_trans _ (((-left) + left) + right) _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-left) left right)) ?_
  refine Q'.eqv_trans _ (0 + right) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ right
      (Q'.neg_add_self_eqv left)
  · exact Q'.eqv_of_eq (Q'.zero_add' right)

private theorem sub_eqv_neg_other_of_joint_eqv_left_add
    (left other joint : Q') (hjoint : joint ≈ left + other) :
    left - joint ≈ -other := by
  change left + (-joint) ≈ -other
  refine Q'.eqv_trans _ (left + -(left + other)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left left _ _
      (Q'.neg_eqv_congr _ _ hjoint)
  · exact left_sub_left_add_eqv_neg_right_local left other

private theorem sub_eqv_other_of_joint_eqv_left_add
    (left other joint : Q') (hjoint : joint ≈ left + other) :
    joint - left ≈ other := by
  change joint + (-left) ≈ other
  refine Q'.eqv_trans _ ((left + other) + (-left)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ (-left) hjoint
  · exact left_add_right_sub_left_eqv_right_local left other

/-- The four-value presentation of the connected Boolean polynomial. -/
def connectedBinaryValue
    (beta gamma : Q') (rootBit targetBit : Bool) : Q' :=
  if rootBit then
    if targetBit then (-1 : Q') + (beta + gamma) else beta
  else
    if targetBit then gamma else 0

/-- Any two of the four connected-polynomial values are at distance at most
one when both moment coefficients lie in the unit interval. -/
theorem connectedBinaryValue_pairDifference_abs_le_one
    (beta gamma : Q')
    (hbeta : (0 : Q') ≤ beta ∧ beta ≤ (1 : Q'))
    (hgamma : (0 : Q') ≤ gamma ∧ gamma ≤ (1 : Q'))
    (leftRoot leftTarget rightRoot rightTarget : Bool) :
    Q'.abs
        (connectedBinaryValue beta gamma leftRoot leftTarget -
          connectedBinaryValue beta gamma rightRoot rightTarget) ≤
      (1 : Q') := by
  have hbetaGamma := unitInterval_difference_abs_le_one
    beta gamma hbeta hgamma
  have hgammaBeta := unitInterval_difference_abs_le_one
    gamma beta hgamma hbeta
  have hbetaOne := unitInterval_difference_abs_le_one
    beta (1 : Q') hbeta ⟨by decide, by decide⟩
  have hgammaOne := unitInterval_difference_abs_le_one
    gamma (1 : Q') hgamma ⟨by decide, by decide⟩
  have hjoint := unitInterval_sum_sub_one_abs_le_one
    beta gamma hbeta hgamma
  have hnegJoint : Q'.abs (-((-1 : Q') + (beta + gamma))) ≤ (1 : Q') :=
    abs_le_one_of_abs_eqv
      (Q'.abs_neg' ((-1 : Q') + (beta + gamma)))
      hjoint
  have hjointGamma : (-1 : Q') + (beta + gamma) ≈
      gamma + (beta - (1 : Q')) := by
    change (-1 : Q') + (beta + gamma) ≈
      gamma + (beta + (-1 : Q'))
    refine Q'.eqv_trans _ (((-1 : Q') + beta) + gamma) _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-1 : Q') beta gamma)) ?_
    refine Q'.eqv_trans _ (gamma + ((-1 : Q') + beta)) _
      (Q'.add_comm_eqv ((-1 : Q') + beta) gamma) ?_
    exact Q'.add_eqv_congr_left gamma _ _
      (Q'.add_comm_eqv (-1 : Q') beta)
  have hjointBeta : (-1 : Q') + (beta + gamma) ≈
      beta + (gamma - (1 : Q')) := by
    change (-1 : Q') + (beta + gamma) ≈
      beta + (gamma + (-1 : Q'))
    refine Q'.eqv_trans _ ((-1 : Q') + (gamma + beta)) _ ?_ ?_
    · exact Q'.add_eqv_congr_left (-1 : Q') _ _
        (Q'.add_comm_eqv beta gamma)
    refine Q'.eqv_trans _ (((-1 : Q') + gamma) + beta) _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-1 : Q') gamma beta)) ?_
    refine Q'.eqv_trans _ (beta + ((-1 : Q') + gamma)) _
      (Q'.add_comm_eqv ((-1 : Q') + gamma) beta) ?_
    exact Q'.add_eqv_congr_left beta _ _
      (Q'.add_comm_eqv (-1 : Q') gamma)
  cases leftRoot <;> cases leftTarget <;>
      cases rightRoot <;> cases rightTarget <;>
      simp only [connectedBinaryValue, Bool.false_eq_true, if_false, if_true]
  · exact unitInterval_difference_abs_le_one
      0 0 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  · exact unitInterval_difference_abs_le_one
      0 gamma ⟨by decide, by decide⟩ hgamma
  · exact unitInterval_difference_abs_le_one
      0 beta ⟨by decide, by decide⟩ hbeta
  · exact abs_le_one_of_abs_eqv
      (Q'.abs_eqv_congr
        (zero_sub_eqv_neg_local ((-1 : Q') + (beta + gamma)))) hnegJoint
  · exact unitInterval_difference_abs_le_one
      gamma 0 hgamma ⟨by decide, by decide⟩
  · exact unitInterval_difference_abs_le_one gamma gamma hgamma hgamma
  · exact hgammaBeta
  · exact abs_le_one_of_abs_eqv
      (Q'.eqv_trans _ (Q'.abs (-(beta - (1 : Q')))) _
        (Q'.abs_eqv_congr
          (sub_eqv_neg_other_of_joint_eqv_left_add
            gamma (beta - (1 : Q'))
            ((-1 : Q') + (beta + gamma)) hjointGamma))
        (Q'.abs_neg' (beta - (1 : Q')))) hbetaOne
  · exact unitInterval_difference_abs_le_one
      beta 0 hbeta ⟨by decide, by decide⟩
  · exact hbetaGamma
  · exact unitInterval_difference_abs_le_one beta beta hbeta hbeta
  · exact abs_le_one_of_abs_eqv
      (Q'.eqv_trans _ (Q'.abs (-(gamma - (1 : Q')))) _
        (Q'.abs_eqv_congr
          (sub_eqv_neg_other_of_joint_eqv_left_add
            beta (gamma - (1 : Q'))
            ((-1 : Q') + (beta + gamma)) hjointBeta))
        (Q'.abs_neg' (gamma - (1 : Q')))) hgammaOne
  · exact abs_le_one_of_abs_eqv
      (Q'.abs_eqv_congr (Q'.eqv_of_eq (Q'.sub_zero' _))) hjoint
  · exact abs_le_one_of_abs_eqv
      (Q'.abs_eqv_congr
        (sub_eqv_other_of_joint_eqv_left_add
          gamma (beta - (1 : Q'))
          ((-1 : Q') + (beta + gamma)) hjointGamma)) hbetaOne
  · exact abs_le_one_of_abs_eqv
      (Q'.abs_eqv_congr
        (sub_eqv_other_of_joint_eqv_left_add
          beta (gamma - (1 : Q'))
          ((-1 : Q') + (beta + gamma)) hjointBeta)) hgammaOne
  · exact abs_le_one_of_abs_eqv
      (Q'.abs_eqv_congr
        (sub_self_eqv_zero_local ((-1 : Q') + (beta + gamma)))) (by decide)

/-- The concrete connected remainder observable has diameter at most one on
the complete coarse carrier. -/
theorem connectedRemainderObservable_pairDifference_abs_le_one
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (left right : EdgeLabelling) :
    Q'.abs
        (connectedRemainderObservable K M left -
          connectedRemainderObservable K M right) ≤ (1 : Q') := by
  let beta := blockedFaceMoment K M.coarseTarget
  let gamma := coarseFaceMoment K M.coarseRoot
  let rootBit := slabPhysicalFacePositiveB M.coarseRoot
  let targetBit := slabPhysicalFacePositiveB M.coarseTarget
  have hbeta : (0 : Q') ≤ beta ∧ beta ≤ (1 : Q') :=
    ⟨blockedFaceMoment_nonnegative K M.coarseTarget,
      blockedFaceMoment_le_one K M.coarseTarget⟩
  have hgamma : (0 : Q') ≤ gamma ∧ gamma ≤ (1 : Q') :=
    ⟨coarseFaceMoment_nonnegative K M.coarseRoot,
      coarseFaceMoment_le_one K M.coarseRoot⟩
  have hleft : connectedRemainderObservable K M left ≈
      connectedBinaryValue beta gamma (rootBit left) (targetBit left) := by
    cases hroot : rootBit left <;> cases htarget : targetBit left <;>
      try simp only [connectedRemainderObservable, weightedCylinderObservable,
        slabPhysicalFacePairPositiveB, rootBit, targetBit, hroot, htarget,
        Bool.false_and, Bool.true_and, Bool.false_eq_true, if_false, if_true,
        Q'.zero_add', Q'.add_zero', connectedBinaryValue, beta, gamma]
    all_goals exact Q'.eqv_refl _
  have hright : connectedRemainderObservable K M right ≈
      connectedBinaryValue beta gamma (rootBit right) (targetBit right) := by
    cases hroot : rootBit right <;> cases htarget : targetBit right <;>
      try simp only [connectedRemainderObservable, weightedCylinderObservable,
        slabPhysicalFacePairPositiveB, rootBit, targetBit, hroot, htarget,
        Bool.false_and, Bool.true_and, Bool.false_eq_true, if_false, if_true,
        Q'.zero_add', Q'.add_zero', connectedBinaryValue, beta, gamma]
    all_goals exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (Q'.add_eqv_congr' hleft
          (Q'.neg_eqv_congr _ _ hright))))
    (connectedBinaryValue_pairDifference_abs_le_one
      beta gamma hbeta hgamma
      (rootBit left) (targetBit left) (rootBit right) (targetBit right))

/-! ## 2. Two normalized tilted-row responses -/

/-- The expectation of the connected remainder observable under one actual
positive tilted-Gibbs source row. -/
def positivePhysicalSourceTiltedGibbsConnectedResponse
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (source : PositivePhysicalSource S) : Q' :=
  Q'.divPos
    (positivePhysicalSourceTiltedGibbsFullRawObservableNumerator
      S source (connectedRemainderObservable K M))
    (positivePhysicalSourceTiltedGibbsRowMass S source)
    (positivePhysicalSourceTiltedGibbsRowMass_pos
      S hfineCutoff hcoarseCoupling source)

/-- Clearing both positive row masses from the normalized connected-response
difference gives the exact rational-observable raw cross. -/
theorem positivePhysicalTiltedGibbsConnectedResponseDifference_mul_masses_eqv_rawCross
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (first second : PositivePhysicalSource S) :
    (positivePhysicalSourceTiltedGibbsConnectedResponse
          K hfineCutoff hcoarseCoupling M first -
        positivePhysicalSourceTiltedGibbsConnectedResponse
          K hfineCutoff hcoarseCoupling M second) *
      (positivePhysicalSourceTiltedGibbsRowMass S first *
        positivePhysicalSourceTiltedGibbsRowMass S second) ≈
    positivePhysicalTiltedGibbsTwoRowRawObservableCrossNumerator
      S first second (connectedRemainderObservable K M) := by
  let firstNumerator :=
    positivePhysicalSourceTiltedGibbsFullRawObservableNumerator
      S first (connectedRemainderObservable K M)
  let secondNumerator :=
    positivePhysicalSourceTiltedGibbsFullRawObservableNumerator
      S second (connectedRemainderObservable K M)
  let firstMass := positivePhysicalSourceTiltedGibbsRowMass S first
  let secondMass := positivePhysicalSourceTiltedGibbsRowMass S second
  let hfirst := positivePhysicalSourceTiltedGibbsRowMass_pos
    S hfineCutoff hcoarseCoupling first
  let hsecond := positivePhysicalSourceTiltedGibbsRowMass_pos
    S hfineCutoff hcoarseCoupling second
  change
    twoPositiveRatioResponseDefect
        firstNumerator secondNumerator firstMass secondMass hfirst hsecond *
      (firstMass * secondMass) ≈
    twoPositiveRatioResponseCrossNumerator
      firstNumerator secondNumerator firstMass secondMass
  exact twoPositiveRatioResponseDefect_mul_masses_eqv_crossNumerator
    firstNumerator secondNumerator firstMass secondMass hfirst hsecond

private theorem orientedPairDifferenceTerm_abs_le_weightProduct
    {A : Type} (firstWeight secondWeight observable : A → Q')
    (pair : A × A)
    (hfirst : (0 : Q') ≤ firstWeight pair.1)
    (hsecond : (0 : Q') ≤ secondWeight pair.2)
    (hdifference : Q'.abs
      (observable pair.1 - observable pair.2) ≤ (1 : Q')) :
    Q'.abs
        (orientedPairDifferenceTerm
          firstWeight secondWeight observable pair) ≤
      firstWeight pair.1 * secondWeight pair.2 := by
  let difference := observable pair.1 - observable pair.2
  let firstValue := firstWeight pair.1
  let secondValue := secondWeight pair.2
  have habs : Q'.abs (firstValue * (secondValue * difference)) ≈
      firstValue * (secondValue * Q'.abs difference) := by
    refine Q'.eqv_trans _ (firstValue * Q'.abs (secondValue * difference)) _
      (abs_mul_nonnegative_left_eqv_local
        firstValue (secondValue * difference) hfirst) ?_
    exact Q'.mul_eqv_congr_left firstValue _ _
      (abs_mul_nonnegative_left_eqv_local
        secondValue difference hsecond)
  have hinner : secondValue * Q'.abs difference ≤
      secondValue * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdifference hsecond
  have houter : firstValue * (secondValue * Q'.abs difference) ≤
      firstValue * (secondValue * (1 : Q')) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hinner hfirst
  unfold orientedPairDifferenceTerm
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv habs)
    (Q'.le_trans' _ _ _ houter
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left firstValue _ _
          (Q'.mul_one_eqv secondValue))))

private theorem finiteWeightedObservableCross_abs_le_massProduct_of_diameterOne
    {A : Type} (firstWeight secondWeight : A → Q')
    (states : List A) (observable : A → Q')
    (hfirst : ∀ state, state ∈ states → (0 : Q') ≤ firstWeight state)
    (hsecond : ∀ state, state ∈ states → (0 : Q') ≤ secondWeight state)
    (hdiameter : ∀ left, left ∈ states → ∀ right, right ∈ states →
      Q'.abs (observable left - observable right) ≤ (1 : Q')) :
    Q'.abs
        (finiteWeightedObservableCrossNumerator
          firstWeight secondWeight states observable) ≤
      listQSum firstWeight states * listQSum secondWeight states := by
  let oriented := orientedPairDifferenceTerm
    firstWeight secondWeight observable
  let product := fun pair : A × A =>
    firstWeight pair.1 * secondWeight pair.2
  have hcross :
      finiteWeightedObservableCrossNumerator
          firstWeight secondWeight states observable ≈
        listQSum oriented (cartesian states states) :=
    Q'.eqv_symm
      (finiteWeightedObservableOrientedPairSum_eqv_crossNumerator
        firstWeight secondWeight states observable)
  have htriangle : Q'.abs (listQSum oriented (cartesian states states)) ≤
      listQSum (fun pair => Q'.abs (oriented pair))
        (cartesian states states) :=
    abs_listQSum_le_sum_abs oriented (cartesian states states)
  have hpointwise :
      listQSum (fun pair => Q'.abs (oriented pair))
          (cartesian states states) ≤
        listQSum product (cartesian states states) := by
    apply listQSum_mono_local
    intro pair hpair
    have hmem := (mem_cartesian_iff states states pair).mp hpair
    exact orientedPairDifferenceTerm_abs_le_weightProduct
      firstWeight secondWeight observable pair
      (hfirst pair.1 hmem.1) (hsecond pair.2 hmem.2)
      (hdiameter pair.1 hmem.1 pair.2 hmem.2)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hcross))
    (Q'.le_trans' _ _ _ htriangle
      (Q'.le_trans' _ _ _ hpointwise
        (Q'.le_of_eqv
          (listQSum_cartesian_product
            firstWeight secondWeight states states))))

/-- The connected raw cross is at most the product of the two positive row
masses because the underlying four-value observable has diameter one. -/
theorem positivePhysicalTiltedGibbsConnectedRawCross_abs_le_rowMassProduct
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (M : SlabFaceBlockMap S) (first second : PositivePhysicalSource S) :
    Q'.abs
        (positivePhysicalTiltedGibbsTwoRowRawObservableCrossNumerator
          S first second (connectedRemainderObservable K M)) ≤
      positivePhysicalSourceTiltedGibbsRowMass S first *
        positivePhysicalSourceTiltedGibbsRowMass S second := by
  let firstWeight := finePacketLocalizedTiltedGibbsRawWeight
    S first.1 first.1 second.1
  let secondWeight := finePacketLocalizedTiltedGibbsRawWeight
    S second.1 first.1 second.1
  let states := S.coarse.physicalLabellings
  let observable := connectedRemainderObservable K M
  have hlocalized :
      positivePhysicalTiltedGibbsTwoRowRawObservableCrossNumerator
          S first second observable ≈
        finiteWeightedObservableCrossNumerator
          firstWeight secondWeight states observable :=
    positivePhysicalTiltedGibbsTwoRowRawObservableCross_eqv_localized
      S hfineCutoff first second observable
  have hbound : Q'.abs
      (finiteWeightedObservableCrossNumerator
        firstWeight secondWeight states observable) ≤
      listQSum firstWeight states * listQSum secondWeight states :=
    finiteWeightedObservableCross_abs_le_massProduct_of_diameterOne
      firstWeight secondWeight states observable
      (fun state _ =>
        finePacketLocalizedTiltedGibbsRawWeight_nonnegative
          S first.1 first.1 second.1 state)
      (fun state _ =>
        finePacketLocalizedTiltedGibbsRawWeight_nonnegative
          S second.1 first.1 second.1 state)
      (fun left _ right _ =>
        connectedRemainderObservable_pairDifference_abs_le_one
          K M left right)
  have hmasses : listQSum firstWeight states * listQSum secondWeight states ≈
      positivePhysicalSourceTiltedGibbsRowMass S first *
        positivePhysicalSourceTiltedGibbsRowMass S second := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm
          (firstTiltedGibbsRowMass_eqv_localizedSum
            S hfineCutoff first second)))
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm
          (secondTiltedGibbsRowMass_eqv_localizedSum
            S hfineCutoff first second)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hlocalized))
    (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hmasses))

/-- The difference of any two normalized connected responses has absolute
value at most one. -/
theorem positivePhysicalTiltedGibbsConnectedResponseDifference_abs_le_one
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (first second : PositivePhysicalSource S) :
    Q'.abs
        (positivePhysicalSourceTiltedGibbsConnectedResponse
            K hfineCutoff hcoarseCoupling M first -
          positivePhysicalSourceTiltedGibbsConnectedResponse
            K hfineCutoff hcoarseCoupling M second) ≤ (1 : Q') := by
  let response :=
    positivePhysicalSourceTiltedGibbsConnectedResponse
        K hfineCutoff hcoarseCoupling M first -
      positivePhysicalSourceTiltedGibbsConnectedResponse
        K hfineCutoff hcoarseCoupling M second
  let scale := positivePhysicalSourceTiltedGibbsRowMass S first *
    positivePhysicalSourceTiltedGibbsRowMass S second
  let cross := positivePhysicalTiltedGibbsTwoRowRawObservableCrossNumerator
    S first second (connectedRemainderObservable K M)
  have hscalePos : (0 : Q') < scale :=
    Q'.mul_pos
      (positivePhysicalSourceTiltedGibbsRowMass_pos
        S hfineCutoff hcoarseCoupling first)
      (positivePhysicalSourceTiltedGibbsRowMass_pos
        S hfineCutoff hcoarseCoupling second)
  have hclear : response * scale ≈ cross :=
    positivePhysicalTiltedGibbsConnectedResponseDifference_mul_masses_eqv_rawCross
      K hfineCutoff hcoarseCoupling M first second
  have habsClear : Q'.abs response * scale ≈ Q'.abs cross := by
    refine Q'.eqv_trans _ (Q'.abs (response * scale)) _ ?_ ?_
    · exact Q'.eqv_symm
        (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right
          response (Q'.le_of_lt hscalePos))
    · exact Q'.abs_eqv_congr hclear
  have hraw : Q'.abs cross ≤ scale :=
    positivePhysicalTiltedGibbsConnectedRawCross_abs_le_rowMassProduct
      K hfineCutoff M first second
  have hmul : Q'.abs response * scale ≤ scale :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv habsClear) hraw
  have hscaled : scale * Q'.abs response ≤ scale * (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv scale (Q'.abs response)))
      (Q'.le_trans' _ _ _ hmul
        (Q'.ge_of_eqv (Q'.mul_one_eqv scale)))
  exact Q'.le_of_mul_le_mul_left hscaled hscalePos

/-- The same normalized response difference is bounded by the sum of the
root- and target-face connected-envelope fractions. -/
theorem positivePhysicalTiltedGibbsConnectedResponseDifference_abs_le_envelopeFractions
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (first second : PositivePhysicalSource S) :
    Q'.abs
        (positivePhysicalSourceTiltedGibbsConnectedResponse
            K hfineCutoff hcoarseCoupling M first -
          positivePhysicalSourceTiltedGibbsConnectedResponse
            K hfineCutoff hcoarseCoupling M second) ≤
      finePacketConnectedEnvelopeFraction
          S hfineCutoff hcoarseCoupling first second M.coarseRoot +
        finePacketConnectedEnvelopeFraction
          S hfineCutoff hcoarseCoupling first second M.coarseTarget := by
  let response :=
    positivePhysicalSourceTiltedGibbsConnectedResponse
        K hfineCutoff hcoarseCoupling M first -
      positivePhysicalSourceTiltedGibbsConnectedResponse
        K hfineCutoff hcoarseCoupling M second
  let scale := positivePhysicalSourceTiltedGibbsRowMass S first *
    positivePhysicalSourceTiltedGibbsRowMass S second
  let cross := positivePhysicalTiltedGibbsTwoRowRawObservableCrossNumerator
    S first second (connectedRemainderObservable K M)
  let rootMass := listQSum
    (finePacketLocalizedResponsePairEnvelope S first.1 second.1)
    (finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 M.coarseRoot)
  let targetMass := listQSum
    (finePacketLocalizedResponsePairEnvelope S first.1 second.1)
    (finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 M.coarseTarget)
  let normalization := finePacketConnectedEnvelopeNormalizationMass
    S first second
  have hscalePos : (0 : Q') < scale :=
    Q'.mul_pos
      (positivePhysicalSourceTiltedGibbsRowMass_pos
        S hfineCutoff hcoarseCoupling first)
      (positivePhysicalSourceTiltedGibbsRowMass_pos
        S hfineCutoff hcoarseCoupling second)
  have hnormalization : (0 : Q') < normalization :=
    finePacketConnectedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling first second
  have hclear : response * scale ≈ cross :=
    positivePhysicalTiltedGibbsConnectedResponseDifference_mul_masses_eqv_rawCross
      K hfineCutoff hcoarseCoupling M first second
  have habsClear : Q'.abs response * normalization ≈
      Q'.abs ((2 : Q') * cross) := by
    unfold normalization finePacketConnectedEnvelopeNormalizationMass
    exact abs_response_mul_two_scale_eqv_two_cross_abs_local
      response scale cross (Q'.le_of_lt hscalePos) hclear
  have hraw : Q'.abs ((2 : Q') * cross) ≤ rootMass + targetMass :=
    two_mul_positivePhysicalTiltedGibbsConnectedRawCross_abs_le_envelopeSums
      K hfineCutoff M first second
  have hmul : Q'.abs response * normalization ≤ rootMass + targetMass :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv habsClear) hraw
  have hdiv : Q'.abs response ≤
      Q'.divPos (rootMass + targetMass) normalization hnormalization :=
    Q'.le_divPos_of_mul_le _ _ hnormalization hmul
  have hsplit :
      Q'.divPos (rootMass + targetMass) normalization hnormalization ≈
        finePacketConnectedEnvelopeFraction
            S hfineCutoff hcoarseCoupling first second M.coarseRoot +
          finePacketConnectedEnvelopeFraction
            S hfineCutoff hcoarseCoupling first second M.coarseTarget := by
    unfold finePacketConnectedEnvelopeFraction rootMass targetMass normalization
    exact divPos_add_eqv_add_divPos rootMass targetMass
      normalization hnormalization
  exact Q'.le_trans' _ _ _ hdiv (Q'.le_of_eqv hsplit)

#print axioms connectedBinaryValue
#print axioms connectedBinaryValue_pairDifference_abs_le_one
#print axioms connectedRemainderObservable_pairDifference_abs_le_one
#print axioms positivePhysicalSourceTiltedGibbsConnectedResponse
#print axioms positivePhysicalTiltedGibbsConnectedResponseDifference_mul_masses_eqv_rawCross
#print axioms positivePhysicalTiltedGibbsConnectedRawCross_abs_le_rowMassProduct
#print axioms positivePhysicalTiltedGibbsConnectedResponseDifference_abs_le_one
#print axioms positivePhysicalTiltedGibbsConnectedResponseDifference_abs_le_envelopeFractions

end YMGap.Continuum.Z4DyadicBinaryConnectedObservableResponseOscillation
