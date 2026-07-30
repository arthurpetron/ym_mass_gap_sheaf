/-
# The exact physical BF4 boundary-centered Gram

The reflected BF4 joint already has a genuine heterogeneous carrier:

* its source and target are complete lower-half configurations;
* its channel is the complete fixed-time interface labelling; and
* its half-amplitudes and channel weights are the literal physical ones.

For the positive lower-state carrier, let

    B(b)   = sum_x A(x,b),
    D(x,b) = A(x,b) - pi(x) B(b).

Finite Fubini and the exact physical normalization give

    sum_b W(b) B(b)^2 = Z,
    sum_b W(b) A(x,b) B(b) = Z pi(x).

Consequently the physical centered joint is exactly

    J(x,y) - pi(x)pi(y)
      = Z^{-1} sum_b W(b) D(x,b)D(y,b).

The final theorem applies the triangle inequality only after this exact
all-interface-label regrouping.  It bounds the physical centered row by the
explicit CP-order/Tonelli majorant

    Z^{-1} sum_b |W(b)D(x,b)| sum_y |D(y,b)|.

Thus the remaining Yang--Mills estimate is a concrete statement about
centered physical half-amplitudes on the genuine interface carrier.  No
same-carrier transfer-power identification is assumed.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4LocalContractionGluing
import YMGap.Continuum.BF4PhysicalSameCarrierRowCPDomination

namespace YMGap.Continuum.BF4PhysicalBoundaryCenteredGram

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4BufferedPerronRowConvergence
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalSameCarrierRowCPDomination
open YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

private theorem one_num_local : (1 : Q').num = 1 := rfl

private theorem one_den_local : (1 : Q').den = 1 := rfl

/-- Cancellation-free rational-semantic polynomial normalization. -/
local macro "ac_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.ofInt, Q'.ofNat, Q'.neg,
               one_num_local, one_den_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try simp;
             try omega;
             try ac_rfl))

private theorem listQSum_neg_local
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      listQSum (fun item => -(value item)) items ≈
        -(listQSum value items)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      unfold listQSum
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (-(value head)) _ _
          (listQSum_neg_local value tail)) ?_
      exact Q'.eqv_symm
        (Q'.neg_add_eqv
          (value head) (listQSum value tail))

/-! ## 1. Generic finite Gram centering -/

/-- Total half-amplitude visible in one channel. -/
def finiteChannelTotalAmplitude
    {State Channel : Type}
    (states : List State)
    (amplitude : State → Channel → Q')
    (channel : Channel) : Q' :=
  listQSum (fun state => amplitude state channel) states

/-- Half-amplitude centered against a supplied state marginal. -/
def finiteMarginalCenteredAmplitude
    {State Channel : Type}
    (states : List State)
    (amplitude : State → Channel → Q')
    (marginal : State → Q')
    (state : State) (channel : Channel) : Q' :=
  amplitude state channel +
    (-(marginal state *
      finiteChannelTotalAmplitude states amplitude channel))

/-- Summing a Gram row first over states and then over channels inserts the
channel-total half-amplitude exactly. -/
theorem weightedGram_row_eq_channelTotal
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (source : State) :
    listQSum
        (weightedGram channels weight amplitude source)
        states ≈
      listQSum
        (fun channel =>
          weight channel *
            (amplitude source channel *
              finiteChannelTotalAmplitude
                states amplitude channel))
        channels := by
  unfold weightedGram finiteChannelTotalAmplitude
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        listQSum
          (fun channel =>
            weight channel *
              (amplitude source channel *
                amplitude target channel))
          channels)
      states) _ (Q'.eqv_refl _) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun channel =>
        listQSum
          (fun target =>
            weight channel *
              (amplitude source channel *
                amplitude target channel))
          states)
      channels) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_swap
        (fun target channel =>
          weight channel *
            (amplitude source channel *
              amplitude target channel))
        states channels)
  apply listQSum_congr
  intro channel
  refine Q'.eqv_trans _
    ((weight channel * amplitude source channel) *
      listQSum
        (fun target => amplitude target channel)
        states) _ ?_ ?_
  · refine Q'.eqv_trans _
      (listQSum
        (fun target =>
          (weight channel * amplitude source channel) *
            amplitude target channel)
        states) _ ?_ ?_
    · apply listQSum_congr
      intro target
      exact Q'.eqv_symm (Q'.mul_assoc_eqv
        (weight channel)
        (amplitude source channel)
        (amplitude target channel))
    · exact listQSum_mul_left
        (weight channel * amplitude source channel)
        (fun target => amplitude target channel)
        states
  · exact Q'.mul_assoc_eqv
        (weight channel)
        (amplitude source channel)
        (listQSum
          (fun target => amplitude target channel)
          states)

/-- The complete Gram mass is the channel-weighted square of the total
half-amplitude. -/
theorem weightedGram_total_eq_channelTotalSquare
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (weight : Channel → Q')
    (amplitude : State → Channel → Q') :
    listQSum
        (fun source =>
          listQSum
            (weightedGram channels weight amplitude source)
            states)
        states ≈
      listQSum
        (fun channel =>
          weight channel *
            (finiteChannelTotalAmplitude states amplitude channel *
              finiteChannelTotalAmplitude states amplitude channel))
        channels := by
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun channel =>
            weight channel *
              (amplitude source channel *
                finiteChannelTotalAmplitude
                  states amplitude channel))
          channels)
      states) _ ?_ ?_
  · apply listQSum_congr
    intro source
    exact weightedGram_row_eq_channelTotal
      states channels weight amplitude source
  refine Q'.eqv_trans _
    (listQSum
      (fun channel =>
        listQSum
          (fun source =>
            weight channel *
              (amplitude source channel *
                finiteChannelTotalAmplitude
                  states amplitude channel))
          states)
      channels) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_swap
        (fun source channel =>
          weight channel *
            (amplitude source channel *
              finiteChannelTotalAmplitude
                states amplitude channel))
        states channels)
  apply listQSum_congr
  intro channel
  let total :=
    finiteChannelTotalAmplitude states amplitude channel
  refine Q'.eqv_trans _
    ((weight channel * total) * total) _ ?_ ?_
  · refine Q'.eqv_trans _
      (listQSum
        (fun source =>
          (weight channel * amplitude source channel) *
            total)
        states) _ ?_ ?_
    · apply listQSum_congr
      intro source
      exact Q'.eqv_symm (Q'.mul_assoc_eqv
        (weight channel)
        (amplitude source channel)
        total)
    refine Q'.eqv_trans _
      (listQSum
        (fun source =>
          weight channel * amplitude source channel)
        states * total) _ ?_ ?_
    · exact listQSum_mul_right
        (fun source =>
          weight channel * amplitude source channel)
        total states
    exact Q'.mul_eqv_congr_right _ _ total
      (listQSum_mul_left
        (weight channel)
        (fun source => amplitude source channel)
        states)
  · exact Q'.mul_assoc_eqv
      (weight channel) total total

/-- Exact covariance identity for a finite weighted Gram. -/
theorem weightedGram_centered_eq_raw_sub_rankOne
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (marginal : State → Q')
    (partition : Q')
    (left right : State)
    (moment_left :
      listQSum
          (fun channel =>
            weight channel *
              (amplitude left channel *
                finiteChannelTotalAmplitude
                  states amplitude channel))
          channels ≈
        partition * marginal left)
    (moment_right :
      listQSum
          (fun channel =>
            weight channel *
              (amplitude right channel *
                finiteChannelTotalAmplitude
                  states amplitude channel))
          channels ≈
        partition * marginal right)
    (squareMass :
      listQSum
          (fun channel =>
            weight channel *
              (finiteChannelTotalAmplitude
                    states amplitude channel *
                finiteChannelTotalAmplitude
                    states amplitude channel))
          channels ≈
        partition) :
    weightedGram
        channels weight
        (finiteMarginalCenteredAmplitude
          states amplitude marginal)
        left right ≈
      weightedGram channels weight amplitude left right +
        (-(partition *
          (marginal left * marginal right))) := by
  let total := finiteChannelTotalAmplitude states amplitude
  let raw := fun channel =>
    weight channel *
      (amplitude left channel * amplitude right channel)
  let leftMoment := fun channel =>
    weight channel *
      (amplitude left channel * total channel)
  let rightMoment := fun channel =>
    weight channel *
      (amplitude right channel * total channel)
  let totalSquare := fun channel =>
    weight channel * (total channel * total channel)
  have hpoint :
      ∀ channel,
        weight channel *
            (finiteMarginalCenteredAmplitude
                  states amplitude marginal left channel *
              finiteMarginalCenteredAmplitude
                  states amplitude marginal right channel) ≈
          ((raw channel +
              (-(marginal right * leftMoment channel))) +
            (-(marginal left * rightMoment channel))) +
          (marginal left * marginal right) *
            totalSquare channel := by
    intro channel
    unfold finiteMarginalCenteredAmplitude
      raw leftMoment rightMoment totalSquare total
    ac_qeqv
  unfold weightedGram
  refine Q'.eqv_trans _
    (listQSum
      (fun channel =>
        ((raw channel +
            (-(marginal right * leftMoment channel))) +
          (-(marginal left * rightMoment channel))) +
        (marginal left * marginal right) *
          totalSquare channel)
      channels) _ ?_ ?_
  · exact listQSum_congr hpoint channels
  refine Q'.eqv_trans _
    (((listQSum raw channels +
        listQSum
          (fun channel =>
            -(marginal right * leftMoment channel))
          channels) +
      listQSum
        (fun channel =>
          -(marginal left * rightMoment channel))
        channels) +
      listQSum
        (fun channel =>
          (marginal left * marginal right) *
            totalSquare channel)
        channels) _ ?_ ?_
  · refine Q'.eqv_trans _ _ _
      (listQSum_add
        (fun channel =>
          (raw channel +
            (-(marginal right * leftMoment channel))) +
          (-(marginal left * rightMoment channel)))
        (fun channel =>
          (marginal left * marginal right) *
            totalSquare channel)
        channels) ?_
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _
        (listQSum_add
          (fun channel =>
            raw channel +
              (-(marginal right * leftMoment channel)))
          (fun channel =>
            -(marginal left * rightMoment channel))
          channels)
        (Q'.add_eqv_congr_right _ _ _
          (listQSum_add
            raw
            (fun channel =>
              -(marginal right * leftMoment channel))
            channels)))
  refine Q'.eqv_trans _
    (((listQSum raw channels +
        (-(marginal right *
          listQSum leftMoment channels))) +
      (-(marginal left *
        listQSum rightMoment channels))) +
      (marginal left * marginal right) *
        listQSum totalSquare channels) _ ?_ ?_
  · apply Q'.add_eqv_congr'
    · apply Q'.add_eqv_congr'
      · apply Q'.add_eqv_congr_left
        exact Q'.eqv_trans _ _ _
          (listQSum_neg_local
            (fun channel =>
              marginal right * leftMoment channel)
            channels)
          (Q'.neg_eqv_congr _ _
            (listQSum_mul_left
              (marginal right)
              leftMoment channels))
      · exact Q'.eqv_trans _ _ _
          (listQSum_neg_local
            (fun channel =>
              marginal left * rightMoment channel)
            channels)
          (Q'.neg_eqv_congr _ _
            (listQSum_mul_left
              (marginal left)
              rightMoment channels))
    · exact listQSum_mul_left
        (marginal left * marginal right)
        totalSquare channels
  have hleft :
      listQSum leftMoment channels ≈
        partition * marginal left :=
    moment_left
  have hright :
      listQSum rightMoment channels ≈
        partition * marginal right :=
    moment_right
  refine Q'.eqv_trans _
    (((listQSum raw channels +
        (-(marginal right *
          (partition * marginal left)))) +
      (-(marginal left *
        (partition * marginal right)))) +
      (marginal left * marginal right) *
        partition) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr_left _ _ _
          (Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_left
              (marginal right) _ _ hleft)))
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left
            (marginal left) _ _ hright)))
      (Q'.mul_eqv_congr_left
        (marginal left * marginal right) _ _
        squareMass)
  have hrightTerm :
      marginal right * (partition * marginal left) ≈
        partition * (marginal left * marginal right) := by
    ac_qeqv
  have hleftTerm :
      marginal left * (partition * marginal right) ≈
        partition * (marginal left * marginal right) := by
    ac_qeqv
  have hpositiveTerm :
      (marginal left * marginal right) * partition ≈
        partition * (marginal left * marginal right) :=
    Q'.mul_comm_eqv _ _
  let rankOne :=
    partition * (marginal left * marginal right)
  unfold raw
  refine Q'.eqv_trans _
    (((weightedGram channels weight amplitude left right +
        (-rankOne)) + (-rankOne)) + rankOne) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr_left _ _ _
          (Q'.neg_eqv_congr _ _ hrightTerm))
        (Q'.neg_eqv_congr _ _ hleftTerm))
      hpositiveTerm
  change
    (((weightedGram channels weight amplitude left right +
        (-rankOne)) + (-rankOne)) + rankOne) ≈
      weightedGram channels weight amplitude left right +
        (-rankOne)
  refine Q'.eqv_trans _
    ((weightedGram channels weight amplitude left right +
        (-rankOne)) + ((-rankOne) + rankOne)) _ ?_ ?_
  · exact Q'.add_assoc_eqv
      (weightedGram channels weight amplitude left right +
        (-rankOne))
      (-rankOne) rankOne
  refine Q'.eqv_trans _
    ((weightedGram channels weight amplitude left right +
        (-rankOne)) + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_add_self_eqv rankOne)
  exact Q'.eqv_of_eq
    (Q'.add_zero'
      (weightedGram channels weight amplitude left right +
        (-rankOne)))

/-- Tonelli/CP-order row majorant for a centered weighted Gram. -/
theorem weightedGram_centered_row_abs_le
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (weight : Channel → Q')
    (centeredAmplitude : State → Channel → Q')
    (source : State) :
    listQSum
        (fun target =>
          Q'.abs
            (weightedGram
              channels weight centeredAmplitude
              source target))
        states ≤
      listQSum
        (fun channel =>
          Q'.abs
              (weight channel *
                centeredAmplitude source channel) *
            listQSum
              (fun target =>
                Q'.abs
                  (centeredAmplitude target channel))
              states)
        channels := by
  unfold weightedGram
  refine Q'.le_trans' _ _ _
    (listQSum_mono _ _ states
      (fun target _ =>
        abs_listQSum_le_sum_abs
          (fun channel =>
            weight channel *
              (centeredAmplitude source channel *
                centeredAmplitude target channel))
          channels)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (listQSum_swap
        (fun target channel =>
          Q'.abs
            (weight channel *
              (centeredAmplitude source channel *
                centeredAmplitude target channel)))
        states channels))) ?_
  apply listQSum_mono
  intro channel _
  refine Q'.le_trans' _ _ _
    (listQSum_mono _ _ states
      (fun target _ =>
        Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (Q'.abs_eqv_congr
              (Q'.eqv_symm
                (Q'.mul_assoc_eqv
                  (weight channel)
                  (centeredAmplitude source channel)
                  (centeredAmplitude target channel)))))
          (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
            (weight channel *
              centeredAmplitude source channel)
            (centeredAmplitude target channel)))) ?_
  exact Q'.le_of_eqv
    (listQSum_mul_left
      (Q'.abs
        (weight channel *
          centeredAmplitude source channel))
      (fun target =>
        Q'.abs (centeredAmplitude target channel))
      states)

/-- Named form of the finite Tonelli majorant. -/
def finiteWeightedGramCenteredRowMajorant
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (weight : Channel → Q')
    (centeredAmplitude : State → Channel → Q')
    (source : State) : Q' :=
  listQSum
    (fun channel =>
      Q'.abs
          (weight channel *
            centeredAmplitude source channel) *
        listQSum
          (fun target =>
            Q'.abs (centeredAmplitude target channel))
          states)
    channels

/-- A pointwise identification with a partition-normalized centered Gram
passes through the complete absolute row sum and then through CP/Tonelli
order. -/
theorem finiteJointDifferenceAbsRowMass_le_normalizedCenteredGramMajorant
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (weight : Channel → Q')
    (centeredAmplitude : State → Channel → Q')
    (partition : Q') (partition_pos : (0 : Q') < partition)
    (joint rankOne : State → State → Q')
    (source : State)
    (entry :
      ∀ target, target ∈ states →
        joint source target + (-rankOne source target) ≈
          Q'.divPos
            (weightedGram
              channels weight centeredAmplitude
              source target)
            partition partition_pos) :
    finiteJointDifferenceAbsRowMass
        states joint rankOne source ≤
      Q'.divPos
        (finiteWeightedGramCenteredRowMajorant
          states channels weight centeredAmplitude source)
        partition partition_pos := by
  let reciprocal :=
    Q'.recipPos partition partition_pos
  have hentryAbs :
      ∀ target,
        target ∈ states →
          Q'.abs
              (joint source target +
                (-rankOne source target)) ≈
            Q'.abs
                (weightedGram
                  channels weight centeredAmplitude
                  source target) *
              reciprocal := by
    intro target htarget
    refine Q'.eqv_trans _ _ _
      (Q'.abs_eqv_congr (entry target htarget)) ?_
    unfold Q'.divPos
    exact
      YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right
        (weightedGram
          channels weight centeredAmplitude
          source target)
        (Q'.le_of_lt
          (Q'.recipPos_pos partition partition_pos))
  unfold finiteJointDifferenceAbsRowMass
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_trans _
        (listQSum
          (fun target =>
            Q'.abs
                (weightedGram
                  channels weight centeredAmplitude
                  source target) *
              reciprocal)
          states) _
        (listQSum_congr_on
          (fun target =>
            Q'.abs
              (joint source target +
                (-rankOne source target)))
          (fun target =>
            Q'.abs
                (weightedGram
                  channels weight centeredAmplitude
                  source target) *
              reciprocal)
          states hentryAbs)
        (listQSum_mul_right
          (fun target =>
            Q'.abs
              (weightedGram
                channels weight centeredAmplitude
                source target))
          reciprocal states))) ?_
  unfold finiteWeightedGramCenteredRowMajorant Q'.divPos
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (weightedGram_centered_row_abs_le
      states channels weight centeredAmplitude source)
    (Q'.le_of_lt
      (Q'.recipPos_pos partition partition_pos))

/-! ## 2. Genuine BF4 interface specialization -/

/-- Sum of the physical half-amplitude over every positive lower-half
configuration, at one complete fixed-interface labelling. -/
def centralPositiveBoundaryTotalHalfAmplitude
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (boundary : EdgeLabelling) : Q' :=
  finiteChannelTotalAmplitude
    (centralPositiveHalfStates w hw K half)
    (centralHalfAmplitude w K half)
    boundary

/-- The physical half-amplitude centered against its exact lower-state
marginal. -/
def centralMarginalCenteredHalfAmplitude
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (state boundary : EdgeLabelling) : Q' :=
  finiteMarginalCenteredAmplitude
    (centralPositiveHalfStates w hw K half)
    (centralHalfAmplitude w K half)
    (centralPhysicalRowMarginal w hw K half)
    state boundary

/-- Exact first-moment identity on the genuine interface carrier. -/
theorem centralBoundaryMoment_eq_partition_mul_marginal
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates w hw K half) :
    listQSum
        (fun boundary =>
          centralBoundaryWeight w K half boundary *
            (centralHalfAmplitude w K half source boundary *
              centralPositiveBoundaryTotalHalfAmplitude
                w hw K half boundary))
        (centralBoundaryChannels K half) ≈
      slabParametricKPhysicalPartition
          w K (centralExtent half) *
        centralPhysicalRowMarginal
          w hw K half source := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (weightedGram_row_eq_channelTotal
        (centralPositiveHalfStates w hw K half)
        (centralBoundaryChannels K half)
        (centralBoundaryWeight w K half)
        (centralHalfAmplitude w K half)
        source))
    (centralPhysicalWeightedGram_positiveRow_eqv_partition_mul_marginal
      hsource)

/-- Exact interface square-mass identity.  This is the physical partition,
not an independently chosen reference normalization. -/
theorem centralBoundaryTotalSquareMass_eq_partition
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) :
    listQSum
        (fun boundary =>
          centralBoundaryWeight w K half boundary *
            (centralPositiveBoundaryTotalHalfAmplitude
                  w hw K half boundary *
              centralPositiveBoundaryTotalHalfAmplitude
                  w hw K half boundary))
        (centralBoundaryChannels K half) ≈
      slabParametricKPhysicalPartition
        w K (centralExtent half) := by
  let states :=
    centralPositiveHalfStates w hw K half
  let partition :=
    slabParametricKPhysicalPartition
      w K (centralExtent half)
  let marginal :=
    centralPhysicalRowMarginal w hw K half
  have htotal :=
    weightedGram_total_eq_channelTotalSquare
      states
      (centralBoundaryChannels K half)
      (centralBoundaryWeight w K half)
      (centralHalfAmplitude w K half)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm htotal) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun source => partition * marginal source)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro source hsource
    exact
      centralPhysicalWeightedGram_positiveRow_eqv_partition_mul_marginal
        hsource
  refine Q'.eqv_trans _
    (partition * listQSum marginal states) _ ?_ ?_
  · exact listQSum_mul_left partition marginal states
  exact Q'.eqv_trans _
    (partition * 1) _
    (Q'.mul_eqv_congr_left partition _ _
      (centralPositiveRowMarginal_total_one
        w hw K half))
    (Q'.mul_one_eqv partition)

/-- The unnormalized centered physical interface Gram is exactly the raw
physical Gram minus `Z pi tensor pi`. -/
theorem centralCenteredBoundaryGram_eq_raw_sub_partitionVacuum
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    {left right : EdgeLabelling}
    (hleft :
      left ∈ centralPositiveHalfStates w hw K half)
    (hright :
      right ∈ centralPositiveHalfStates w hw K half) :
    weightedGram
        (centralBoundaryChannels K half)
        (centralBoundaryWeight w K half)
        (centralMarginalCenteredHalfAmplitude
          w hw K half)
        left right ≈
      centralPhysicalReflectedKernel w K half left right +
        (-(slabParametricKPhysicalPartition
              w K (centralExtent half) *
          centralPhysicalVacuumJoint
            w hw K half left right)) := by
  refine Q'.eqv_trans _ _ _
    (weightedGram_centered_eq_raw_sub_rankOne
      (centralPositiveHalfStates w hw K half)
      (centralBoundaryChannels K half)
      (centralBoundaryWeight w K half)
      (centralHalfAmplitude w K half)
      (centralPhysicalRowMarginal w hw K half)
      (slabParametricKPhysicalPartition
        w K (centralExtent half))
      left right
      (centralBoundaryMoment_eq_partition_mul_marginal
        hleft)
      (centralBoundaryMoment_eq_partition_mul_marginal
        hright)
      (centralBoundaryTotalSquareMass_eq_partition
        w hw K half)) ?_
  apply Q'.add_eqv_congr'
  · exact Q'.eqv_symm
      (centralPhysicalReflectedKernel_eq_weightedGram
        w
        (mem_centralPositiveHalfStates_iff.mp hleft).1
        (mem_centralPositiveHalfStates_iff.mp hright).1)
  · exact Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left
        (slabParametricKPhysicalPartition
          w K (centralExtent half)) _ _
        (Q'.eqv_refl _))

/-- After the unique physical partition normalization, the centered
interface Gram is exactly `J - pi tensor pi`. -/
theorem centralNormalizedCenteredBoundaryGram_eq_physicalCentered
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    {left right : EdgeLabelling}
    (hleft :
      left ∈ centralPositiveHalfStates w hw K half)
    (hright :
      right ∈ centralPositiveHalfStates w hw K half) :
    Q'.divPos
        (weightedGram
          (centralBoundaryChannels K half)
          (centralBoundaryWeight w K half)
          (centralMarginalCenteredHalfAmplitude
            w hw K half)
          left right)
        (slabParametricKPhysicalPartition
          w K (centralExtent half))
        (slabParametricKPhysicalPartition_pos
          hw K (centralExtent half)) ≈
      centralNormalizedPhysicalReflectedKernel
            w hw K half left right +
        (-centralPhysicalVacuumJoint
          w hw K half left right) := by
  let partition :=
    slabParametricKPhysicalPartition
      w K (centralExtent half)
  let hpartition :=
    slabParametricKPhysicalPartition_pos
      hw K (centralExtent half)
  let reciprocal :=
    Q'.recipPos partition hpartition
  have hraw :=
    centralCenteredBoundaryGram_eq_raw_sub_partitionVacuum
      hleft hright
  unfold Q'.divPos
  refine Q'.eqv_trans _
    ((centralPhysicalReflectedKernel w K half left right +
        (-(partition *
          centralPhysicalVacuumJoint
            w hw K half left right))) *
      reciprocal) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ reciprocal hraw
  unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
  let vacuum :=
    centralPhysicalVacuumJoint
      w hw K half left right
  have hcancel :
      (partition * vacuum) * reciprocal ≈ vacuum := by
    refine Q'.eqv_trans _
      ((vacuum * partition) * reciprocal) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ reciprocal
        (Q'.mul_comm_eqv partition vacuum)
    refine Q'.eqv_trans _
      (vacuum * (partition * reciprocal)) _ ?_ ?_
    · exact Q'.mul_assoc_eqv
        vacuum partition reciprocal
    refine Q'.eqv_trans _
      (vacuum * 1) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left vacuum _ _
        (Q'.mul_recipPos_eqv partition hpartition)
    exact Q'.mul_one_eqv vacuum
  refine Q'.eqv_trans _
    (centralPhysicalReflectedKernel
          w K half left right * reciprocal +
      (-(partition * vacuum)) * reciprocal) _ ?_ ?_
  · exact Q'.add_mul_eqv
      (centralPhysicalReflectedKernel w K half left right)
      (-(partition * vacuum)) reciprocal
  refine Q'.eqv_trans _
    (centralPhysicalReflectedKernel
          w K half left right * reciprocal +
      (-((partition * vacuum) * reciprocal))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_mul_eqv
        (partition * vacuum) reciprocal)
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.neg_eqv_congr _ _ hcancel)

/-- The literal interface CP/Tonelli majorant for one physical source row. -/
def centralBoundaryCenteredRowMajorant
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (source : EdgeLabelling) : Q' :=
  finiteWeightedGramCenteredRowMajorant
    (centralPositiveHalfStates w hw K half)
    (centralBoundaryChannels K half)
    (centralBoundaryWeight w K half)
    (centralMarginalCenteredHalfAmplitude
      w hw K half)
    source

/-- Absolute centered lower-state profile carried by one interface label. -/
def centralBoundaryTargetProfileDeviation
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (boundary : EdgeLabelling) : Q' :=
  listQSum
    (fun target =>
      Q'.abs
        (centralMarginalCenteredHalfAmplitude
          w hw K half target boundary))
    (centralPositiveHalfStates w hw K half)

/-- Absolute centered interface profile visible from one lower source,
weighted by the physical channel weight and the total target
half-amplitude. -/
def centralSourceBoundaryProfileDeviation
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (source : EdgeLabelling) : Q' :=
  listQSum
    (fun boundary =>
      Q'.abs
          (centralBoundaryWeight w K half boundary *
            centralMarginalCenteredHalfAmplitude
              w hw K half source boundary) *
        centralPositiveBoundaryTotalHalfAmplitude
          w hw K half boundary)
    (centralBoundaryChannels K half)

/-- A target-profile Harnack bound factors the CP/Tonelli majorant into the
same scalar times the source-profile deviation. -/
theorem centralBoundaryCenteredRowMajorant_le_profile_mul_sourceDeviation
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (profileBound : Q')
    (hprofile :
      ∀ boundary,
        boundary ∈ centralBoundaryChannels K half →
          centralBoundaryTargetProfileDeviation
              w hw K half boundary ≤
            profileBound *
              centralPositiveBoundaryTotalHalfAmplitude
                w hw K half boundary) :
    centralBoundaryCenteredRowMajorant
        w hw K half source ≤
      profileBound *
        centralSourceBoundaryProfileDeviation
          w hw K half source := by
  unfold centralBoundaryCenteredRowMajorant
    finiteWeightedGramCenteredRowMajorant
    centralSourceBoundaryProfileDeviation
  refine Q'.le_trans' _ _ _
    (listQSum_mono _ _
      (centralBoundaryChannels K half)
      (fun boundary hboundary => by
        have hp := hprofile boundary hboundary
        unfold centralBoundaryTargetProfileDeviation at hp
        exact Q'.mul_le_mul_of_nonneg_left _ _ _
          hp
          (Q'.abs_nonneg
            (centralBoundaryWeight w K half boundary *
              centralMarginalCenteredHalfAmplitude
                w hw K half source boundary)))) ?_
  refine Q'.le_of_eqv
    (Q'.eqv_trans _
      (listQSum
        (fun boundary =>
          profileBound *
            (Q'.abs
                (centralBoundaryWeight w K half boundary *
                  centralMarginalCenteredHalfAmplitude
                    w hw K half source boundary) *
              centralPositiveBoundaryTotalHalfAmplitude
                w hw K half boundary))
        (centralBoundaryChannels K half)) _ ?_ ?_)
  · apply listQSum_congr
    intro boundary
    ac_qeqv
  exact listQSum_mul_left
    profileBound
    (fun boundary =>
      Q'.abs
          (centralBoundaryWeight w K half boundary *
            centralMarginalCenteredHalfAmplitude
              w hw K half source boundary) *
        centralPositiveBoundaryTotalHalfAmplitude
          w hw K half boundary)
    (centralBoundaryChannels K half)

/-- Two literal physical quarter-profile estimates pay the exact interface
majorant down to `Z pi(source)/16`. -/
theorem centralBoundaryCenteredRowMajorant_le_sixteenth_of_quarterProfiles
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hprofile :
      ∀ boundary,
        boundary ∈ centralBoundaryChannels K half →
          centralBoundaryTargetProfileDeviation
              w hw K half boundary ≤
            quarter *
              centralPositiveBoundaryTotalHalfAmplitude
                w hw K half boundary)
    (hsource :
      centralSourceBoundaryProfileDeviation
          w hw K half source ≤
        quarter *
          (slabParametricKPhysicalPartition
              w K (centralExtent half) *
            centralPhysicalRowMarginal
              w hw K half source)) :
    centralBoundaryCenteredRowMajorant
        w hw K half source ≤
      slabParametricKPhysicalPartition
          w K (centralExtent half) *
        (Q'.mkPos 1 16 (by decide) *
          centralPhysicalRowMarginal
            w hw K half source) := by
  have hfactor :=
    centralBoundaryCenteredRowMajorant_le_profile_mul_sourceDeviation
      (source := source) quarter hprofile
  refine Q'.le_trans' _ _ _ hfactor
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        hsource (by decide)) ?_)
  let partition :=
    slabParametricKPhysicalPartition
      w K (centralExtent half)
  let marginal :=
    centralPhysicalRowMarginal
      w hw K half source
  let sixteenth := Q'.mkPos 1 16 (by decide)
  have hquarterSquare :
      quarter * quarter ≈ sixteenth := by
    decide
  refine Q'.le_of_eqv
    (Q'.eqv_trans _
      ((quarter * quarter) *
        (partition * marginal)) _ ?_ ?_)
  · exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        quarter quarter (partition * marginal))
  refine Q'.eqv_trans _
    (sixteenth * (partition * marginal)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _
      (partition * marginal) hquarterSquare
  refine Q'.eqv_trans _
    ((sixteenth * partition) * marginal) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        sixteenth partition marginal)
  refine Q'.eqv_trans _
    ((partition * sixteenth) * marginal) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ marginal
      (Q'.mul_comm_eqv sixteenth partition)
  exact Q'.mul_assoc_eqv
    partition sixteenth marginal

/-- **Exact physical all-label contraction followed by CP-order
domination.**  The physical centered row is bounded by the partition-
normalized genuine interface majorant. -/
theorem physicalCenteredPhysicalRowMass_le_boundaryMajorant
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates w hw K half) :
    physicalCenteredPhysicalRowMass
        w hw K half source ≤
      Q'.divPos
        (centralBoundaryCenteredRowMajorant
          w hw K half source)
        (slabParametricKPhysicalPartition
          w K (centralExtent half))
        (slabParametricKPhysicalPartition_pos
          hw K (centralExtent half)) := by
  unfold physicalCenteredPhysicalRowMass
    centralBoundaryCenteredRowMajorant
  apply
    finiteJointDifferenceAbsRowMass_le_normalizedCenteredGramMajorant
  intro target htarget
  exact Q'.eqv_symm
    (centralNormalizedCenteredBoundaryGram_eq_physicalCentered
      hsource htarget)

/-- A spacing-uniform bound on the genuine interface majorant immediately
inhabits the physical `1/16` row field. -/
theorem physicalCenteredPhysicalRowMass_le_sixteenth_of_boundaryMajorant
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates w hw K half)
    (hmajorant :
      centralBoundaryCenteredRowMajorant
          w hw K half source ≤
        slabParametricKPhysicalPartition
            w K (centralExtent half) *
          (Q'.mkPos 1 16 (by decide) *
            centralPhysicalRowMarginal
              w hw K half source)) :
    physicalCenteredPhysicalRowMass
        w hw K half source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          w hw K half source := by
  let partition :=
    slabParametricKPhysicalPartition
      w K (centralExtent half)
  let hpartition :=
    slabParametricKPhysicalPartition_pos
      hw K (centralExtent half)
  refine Q'.le_trans' _ _ _
    (physicalCenteredPhysicalRowMass_le_boundaryMajorant
      hsource) ?_
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _ hmajorant
    (Q'.le_of_eqv
      (Q'.mul_comm_eqv
        partition
        (Q'.mkPos 1 16 (by decide) *
          centralPhysicalRowMarginal
            w hw K half source)))

/-- The physical row-sixteenth theorem in the two-profile form consumed by
positive-kernel/Harnack estimates. -/
theorem physicalCenteredPhysicalRowMass_le_sixteenth_of_quarterProfiles
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hsourceMem :
      source ∈ centralPositiveHalfStates w hw K half)
    (htargetProfile :
      ∀ boundary,
        boundary ∈ centralBoundaryChannels K half →
          centralBoundaryTargetProfileDeviation
              w hw K half boundary ≤
            quarter *
              centralPositiveBoundaryTotalHalfAmplitude
                w hw K half boundary)
    (hsourceProfile :
      centralSourceBoundaryProfileDeviation
          w hw K half source ≤
        quarter *
          (slabParametricKPhysicalPartition
              w K (centralExtent half) *
            centralPhysicalRowMarginal
              w hw K half source)) :
    physicalCenteredPhysicalRowMass
        w hw K half source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          w hw K half source :=
  physicalCenteredPhysicalRowMass_le_sixteenth_of_boundaryMajorant
    hsourceMem
    (centralBoundaryCenteredRowMajorant_le_sixteenth_of_quarterProfiles
      htargetProfile hsourceProfile)

/-! ## 3. Spacing-uniform AF trajectory consumer -/

/-- The remaining physical estimate on the matched AF trajectory, stated
directly on the genuine centered interface Gram.

Together with the already constructed cross-zero endpoint Harnack datum,
this single majorant field supplies both literal rowwise eighths and hence
the physical quarter theorem. -/
structure MatchedBoundaryCenteredGramSixteenthRows
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
  boundary_majorant_sixteenth :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        centralBoundaryCenteredRowMajorant
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) source ≤
          slabParametricKPhysicalPartition
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinCutoff family coupling scale)
              (centralExtent (halfExtent scale)) *
            (Q'.mkPos 1 16 (by decide) *
              centralPhysicalRowMarginal
                (matchedAllSpinWeight family coupling scale)
                (matchedAllSpinWeight_nonnegative
                  family coupling scale)
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) source)

namespace MatchedBoundaryCenteredGramSixteenthRows

/-- The interface majorant certificate supplies the already proved
cross-zero physical-sixteenth package. -/
def toCrossZeroPhysicalSixteenthRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedBoundaryCenteredGramSixteenthRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedCrossZeroPhysicalSixteenthRows
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  harnack := data.harnack
  physical_centered_row_sixteenth := by
    intro scale source hsource
    exact
      physicalCenteredPhysicalRowMass_le_sixteenth_of_boundaryMajorant
        hsource
        (data.boundary_majorant_sixteenth
          scale source hsource)

/-- Both requested spacing-uniform eighth fields are now downstream of the
one explicit interface-profile estimate. -/
def toRowwiseEighthEstimates
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedBoundaryCenteredGramSixteenthRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  data.toCrossZeroPhysicalSixteenthRows
    |>.toRowwiseEighthEstimates

end MatchedBoundaryCenteredGramSixteenthRows

end YMGap.Continuum.BF4PhysicalBoundaryCenteredGram

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCenteredGram.weightedGram_row_eq_channelTotal
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCenteredGram.weightedGram_total_eq_channelTotalSquare
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCenteredGram.weightedGram_centered_eq_raw_sub_rankOne
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCenteredGram.weightedGram_centered_row_abs_le
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCenteredGram.finiteJointDifferenceAbsRowMass_le_normalizedCenteredGramMajorant
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCenteredGram.centralBoundaryMoment_eq_partition_mul_marginal
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCenteredGram.centralBoundaryTotalSquareMass_eq_partition
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCenteredGram.centralCenteredBoundaryGram_eq_raw_sub_partitionVacuum
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCenteredGram.centralNormalizedCenteredBoundaryGram_eq_physicalCentered
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCenteredGram.centralBoundaryCenteredRowMajorant_le_profile_mul_sourceDeviation
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCenteredGram.centralBoundaryCenteredRowMajorant_le_sixteenth_of_quarterProfiles
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCenteredGram.physicalCenteredPhysicalRowMass_le_boundaryMajorant
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCenteredGram.physicalCenteredPhysicalRowMass_le_sixteenth_of_boundaryMajorant
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCenteredGram.physicalCenteredPhysicalRowMass_le_sixteenth_of_quarterProfiles
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCenteredGram.MatchedBoundaryCenteredGramSixteenthRows.toCrossZeroPhysicalSixteenthRows
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCenteredGram.MatchedBoundaryCenteredGramSixteenthRows.toRowwiseEighthEstimates
