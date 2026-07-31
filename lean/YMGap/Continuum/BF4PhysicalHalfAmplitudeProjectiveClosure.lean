/-
# One BF4 half-amplitude diameter controls both boundary posteriors

Let `A(x,b)` be a nonnegative finite state/channel amplitude and
`B(b)=sum_x A(x,b)`.  A single cross-ratio bound for the matrix `A` is
preserved by the two positive summations needed by the physical reflected
Gram:

* every column `A(·,b)` is projectively comparable with the weighted row
  numerator `sum_c W(c) A(·,c) B(c)`;
* every row `A(x,·)` is projectively comparable with `B`, and hence the two
  raw Bayes numerator rays `W A_x B` and `W B²` are comparable.

The BF4 specialization identifies the first weighted row numerator with
`Z pi` exactly.  Thus one division-free diameter estimate for the genuine
half-amplitude matrix supplies both raw projective hypotheses from
`BF4PhysicalBoundaryPosteriorProjectiveAdapter`.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryPosteriorProjectiveAdapter

namespace YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryPosterior
open YMGap.Continuum.BF4PhysicalBoundaryPosteriorProjectiveAdapter
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
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

private theorem int_swap_inner_local (x y z w : Int) :
    (x * y) * (z * w) = (x * z) * (y * w) := by
  rw [Int.mul_assoc x y (z * w), ← Int.mul_assoc y z w,
    Int.mul_comm y z, Int.mul_assoc z y w,
    ← Int.mul_assoc x z (y * w)]

/-- Local constructive cancellation of a positive rational factor from an
inequality. -/
private theorem le_of_left_scale_le_left_scale_pos
    {scale left right : Q'}
    (scale_pos : (0 : Q') < scale)
    (h : scale * left ≤ scale * right) :
    left ≤ right := by
  have hscale' :
      (0 : Int) * (scale.den : Int) <
        scale.num * (((0 : Q').den) : Int) :=
    scale_pos
  have hnum : (0 : Int) < scale.num := by
    have h :
        (0 : Int) * (scale.den : Int) <
          scale.num * (1 : Int) :=
      hscale'
    rw [Int.zero_mul, Int.mul_one] at h
    exact h
  have hfactor :
      (0 : Int) < scale.num * (scale.den : Int) :=
    Int.mul_pos hnum
      (Int.ofNat_lt.mpr (Q'.den_pos scale))
  have h' :
      (scale * left).num *
          (((scale * right).den) : Int) ≤
        (scale * right).num *
          (((scale * left).den) : Int) :=
    h
  rw [show (scale * left).num =
        scale.num * left.num by rfl,
      show (scale * right).num =
        scale.num * right.num by rfl,
      Q'.mul_den_cast scale right,
      Q'.mul_den_cast scale left] at h'
  rw [int_swap_inner_local
        scale.num left.num (scale.den : Int)
          (right.den : Int),
      int_swap_inner_local
        scale.num right.num (scale.den : Int)
          (left.den : Int)] at h'
  show left.num * ((right.den) : Int) ≤
    right.num * ((left.den) : Int)
  exact Int.le_of_mul_le_mul_left h' hfactor

/-! ## 1. Generic finite positive-summation closure -/

/-- Weighted row numerator of a reflected finite Gram. -/
def finiteGramRowNumerator
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (state : State) : Q' :=
  listQSum
    (fun channel =>
      weight channel *
        (amplitude state channel *
          finiteChannelTotalAmplitude
            states amplitude channel))
    channels

/-- Raw numerator of `channel | state`. -/
def finiteSourceChannelNumerator
    {State Channel : Type}
    (states : List State)
    (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (state : State) (channel : Channel) : Q' :=
  weight channel *
    (amplitude state channel *
      finiteChannelTotalAmplitude states amplitude channel)

/-- Raw square-amplitude channel prior numerator. -/
def finiteChannelPriorNumerator
    {State Channel : Type}
    (states : List State)
    (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (channel : Channel) : Q' :=
  weight channel *
    (finiteChannelTotalAmplitude states amplitude channel *
      finiteChannelTotalAmplitude states amplitude channel)

/-- Every channel total is nonnegative when the matrix is nonnegative on
the selected state carrier. -/
theorem finiteChannelTotalAmplitude_nonnegative
    {State Channel : Type}
    (states : List State)
    (amplitude : State → Channel → Q')
    (amplitude_nonnegative :
      ∀ state, state ∈ states →
        ∀ channel, (0 : Q') ≤ amplitude state channel)
    (channel : Channel) :
    (0 : Q') ≤
      finiteChannelTotalAmplitude states amplitude channel := by
  unfold finiteChannelTotalAmplitude
  apply listQSum_nonnegative_on
  intro state state_mem
  exact amplitude_nonnegative state state_mem channel

/-- A matrix cross-ratio bound is preserved when its second ray is a
positive weighted mixture of columns. -/
theorem finiteColumn_projective_gramRowNumerator
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (spread : Q')
    (amplitude_nonnegative :
      ∀ state, state ∈ states →
        ∀ channel, (0 : Q') ≤ amplitude state channel)
    (weight_nonnegative :
      ∀ channel, channel ∈ channels →
        (0 : Q') ≤ weight channel)
    (crossRatio :
      ∀ left, left ∈ states →
        ∀ right, right ∈ states →
          ∀ first, first ∈ channels →
            ∀ second, second ∈ channels →
              amplitude left first * amplitude right second ≤
                (spread * spread) *
                  (amplitude left second *
                    amplitude right first))
    (fixed : Channel) (fixed_mem : fixed ∈ channels) :
    FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
      spread states
      (fun state => amplitude state fixed)
      (finiteGramRowNumerator
        states channels weight amplitude) := by
  intro left left_mem right right_mem
  let total := fun channel =>
    finiteChannelTotalAmplitude states amplitude channel
  have hsum :
      listQSum
          (fun channel =>
            amplitude left fixed *
              (weight channel *
                (amplitude right channel * total channel)))
          channels ≤
        listQSum
          (fun channel =>
            (spread * spread) *
              ((weight channel *
                  (amplitude left channel * total channel)) *
                amplitude right fixed))
          channels := by
    apply listQSum_mono
    intro channel channel_mem
    let scale := weight channel * total channel
    have hscale : (0 : Q') ≤ scale :=
      Q'.mul_nonneg _ _
        (weight_nonnegative channel channel_mem)
        (finiteChannelTotalAmplitude_nonnegative
          states amplitude amplitude_nonnegative channel)
    have hcross :=
      crossRatio
        left left_mem right right_mem
        fixed fixed_mem channel channel_mem
    have hscaled :=
      Q'.mul_le_mul_of_nonneg_right _ _ _
        hcross hscale
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv ?_)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv ?_))
    · dsimp [scale]
      q_ring
    · dsimp [scale]
      q_ring
  unfold finiteGramRowNumerator
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (listQSum_mul_left
          (amplitude left fixed)
          (fun channel =>
            weight channel *
              (amplitude right channel * total channel))
          channels))) ?_
  refine Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _
    ((spread * spread) *
      listQSum
        (fun channel =>
          (weight channel *
            (amplitude left channel * total channel)) *
              amplitude right fixed)
        channels) _ ?_ ?_
  · exact listQSum_mul_left
      (spread * spread)
      (fun channel =>
        (weight channel *
          (amplitude left channel * total channel)) *
            amplitude right fixed)
      channels
  refine Q'.eqv_trans _
    ((spread * spread) *
      (listQSum
        (fun channel =>
          weight channel *
            (amplitude left channel * total channel))
        channels *
      amplitude right fixed)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left
      (spread * spread) _ _
      (listQSum_mul_right
        (fun channel =>
          weight channel *
            (amplitude left channel * total channel))
        (amplitude right fixed) channels)
  q_ring

/-- A matrix cross-ratio bound is preserved when a fixed row is compared
with the sum of all rows. -/
theorem finiteRow_projective_channelTotal
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (amplitude : State → Channel → Q')
    (spread : Q')
    (crossRatio :
      ∀ left, left ∈ states →
        ∀ right, right ∈ states →
          ∀ first, first ∈ channels →
            ∀ second, second ∈ channels →
              amplitude left first * amplitude right second ≤
                (spread * spread) *
                  (amplitude left second *
                    amplitude right first))
    (fixed : State) (fixed_mem : fixed ∈ states) :
    FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
      spread channels
      (amplitude fixed)
      (finiteChannelTotalAmplitude states amplitude) := by
  intro first first_mem second second_mem
  have hsum :
      listQSum
          (fun state =>
            amplitude fixed first * amplitude state second)
          states ≤
        listQSum
          (fun state =>
            (spread * spread) *
              (amplitude fixed second * amplitude state first))
          states := by
    apply listQSum_mono
    intro state state_mem
    exact crossRatio
      fixed fixed_mem state state_mem
      first first_mem second second_mem
  unfold finiteChannelTotalAmplitude
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (listQSum_mul_left
          (amplitude fixed first)
          (fun state => amplitude state second)
          states))) ?_
  refine Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _
    ((spread * spread) *
      listQSum
        (fun state =>
          amplitude fixed second * amplitude state first)
        states) _ ?_ ?_
  · exact listQSum_mul_left
      (spread * spread)
      (fun state =>
        amplitude fixed second * amplitude state first)
      states
  exact Q'.mul_eqv_congr_left
    (spread * spread) _ _
    (listQSum_mul_left
      (amplitude fixed second)
      (fun state => amplitude state first)
      states)

/-- After multiplying by the common nonnegative weight and total factors,
the raw source-channel and channel-prior numerator rays retain the same
projective spread. -/
theorem finiteSourceChannel_projective_channelPrior
    {State Channel : Type}
    (states : List State) (channels : List Channel)
    (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (spread : Q')
    (amplitude_nonnegative :
      ∀ state, state ∈ states →
        ∀ channel, (0 : Q') ≤ amplitude state channel)
    (weight_nonnegative :
      ∀ channel, channel ∈ channels →
        (0 : Q') ≤ weight channel)
    (crossRatio :
      ∀ left, left ∈ states →
        ∀ right, right ∈ states →
          ∀ first, first ∈ channels →
            ∀ second, second ∈ channels →
              amplitude left first * amplitude right second ≤
                (spread * spread) *
                  (amplitude left second *
                    amplitude right first))
    (fixed : State) (fixed_mem : fixed ∈ states) :
    FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
      spread channels
      (finiteSourceChannelNumerator
        states weight amplitude fixed)
      (finiteChannelPriorNumerator
        states weight amplitude) := by
  have hrow :=
    finiteRow_projective_channelTotal
      states channels amplitude spread
      crossRatio fixed fixed_mem
  intro first first_mem second second_mem
  let firstTotal :=
    finiteChannelTotalAmplitude states amplitude first
  let secondTotal :=
    finiteChannelTotalAmplitude states amplitude second
  let scale :=
    (weight first * weight second) *
      (firstTotal * secondTotal)
  have hscale : (0 : Q') ≤ scale := by
    apply Q'.mul_nonneg
    · exact Q'.mul_nonneg _ _
        (weight_nonnegative first first_mem)
        (weight_nonnegative second second_mem)
    · exact Q'.mul_nonneg _ _
        (finiteChannelTotalAmplitude_nonnegative
          states amplitude amplitude_nonnegative first)
        (finiteChannelTotalAmplitude_nonnegative
          states amplitude amplitude_nonnegative second)
  have hbase :=
    hrow first first_mem second second_mem
  have hscaled :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hbase hscale
  unfold finiteSourceChannelNumerator
    finiteChannelPriorNumerator
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv ?_)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv ?_))
  · dsimp [scale, firstTotal, secondTotal]
    q_ring
  · dsimp [scale, firstTotal, secondTotal]
    q_ring

/-! ## 2. Positive common-scale cancellation -/

/-- If the second ray of a projective pair is a common positive multiple
of a target ray, that common multiple can be cancelled constructively. -/
theorem projectiveSpreadBound_of_common_scale
    {Index : Type}
    (carrier : List Index)
    (first raw target : Index → Q')
    (spread scale : Q')
    (scale_pos : (0 : Q') < scale)
    (rawBound :
      FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
        spread carrier first raw)
    (raw_eq_scale_mul :
      ∀ index, index ∈ carrier →
        raw index ≈ scale * target index) :
    FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
      spread carrier first target := by
  intro left left_mem right right_mem
  have hraw :=
    rawBound left left_mem right right_mem
  have hleft :=
    raw_eq_scale_mul left left_mem
  have hright :=
    raw_eq_scale_mul right right_mem
  have hstart :
      scale * (first left * target right) ≈
        first left * raw right := by
    refine Q'.eqv_trans _
      (first left * (scale * target right)) _ ?_ ?_
    · q_ring
    exact Q'.eqv_symm
      (Q'.mul_eqv_congr_left
        (first left) _ _ hright)
  have hend :
      (spread * spread) *
          (first right * raw left) ≈
        scale *
          ((spread * spread) *
            (first right * target left)) := by
    refine Q'.eqv_trans _
      ((spread * spread) *
        (first right * (scale * target left))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left
        (spread * spread) _ _
        (Q'.mul_eqv_congr_left
          (first right) _ _ hleft)
    q_ring
  have hscaled :
      scale * (first left * target right) ≤
        scale *
          ((spread * spread) *
            (first right * target left)) := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv hstart)
      (Q'.le_trans' _ _ _ hraw
        (Q'.le_of_eqv hend))
  exact le_of_left_scale_le_left_scale_pos
    scale_pos hscaled

/-! ## 3. Physical BF4 specialization -/

/-- One half-amplitude matrix cross-ratio estimate supplies every target
raw-projective estimate against the exact physical marginal. -/
theorem centralHalfAmplitude_targetRawProjective
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (spread : Q')
    (crossRatio :
      ∀ left,
        left ∈ centralPositiveHalfStates w hw K half →
          ∀ right,
            right ∈ centralPositiveHalfStates w hw K half →
              ∀ first,
                first ∈ centralBoundaryChannels K half →
                  ∀ second,
                    second ∈ centralBoundaryChannels K half →
                      centralHalfAmplitude w K half left first *
                          centralHalfAmplitude w K half right second ≤
                        (spread * spread) *
                          (centralHalfAmplitude
                              w K half left second *
                            centralHalfAmplitude
                              w K half right first))
    (fixed : EdgeLabelling)
    (fixed_mem : fixed ∈ centralBoundaryChannels K half) :
    FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
      spread
      (centralPositiveHalfStates w hw K half)
      (fun state =>
        centralHalfAmplitude w K half state fixed)
      (centralPhysicalRowMarginal w hw K half) := by
  let states := centralPositiveHalfStates w hw K half
  let channels := centralBoundaryChannels K half
  let weight := centralBoundaryWeight w K half
  let amplitude := centralHalfAmplitude w K half
  have hcolumns :
      FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
        spread states
        (fun state => amplitude state fixed)
        (finiteGramRowNumerator
          states channels weight amplitude) :=
    finiteColumn_projective_gramRowNumerator
      states channels weight amplitude spread
      (fun state _ channel =>
        centralHalfAmplitude_nonnegative
          hw K half state channel)
      (fun channel channel_mem =>
        centralBoundaryWeight_nonnegative_on
          hw channel channel_mem)
      crossRatio fixed fixed_mem
  exact projectiveSpreadBound_of_common_scale
    states
    (fun state => amplitude state fixed)
    (finiteGramRowNumerator
      states channels weight amplitude)
    (centralPhysicalRowMarginal w hw K half)
    spread
    (slabParametricKPhysicalPartition
      w K (centralExtent half))
    (slabParametricKPhysicalPartition_pos
      hw K (centralExtent half))
    hcolumns
    (fun _ state_mem =>
      centralBoundaryMoment_eq_partition_mul_marginal
        state_mem)

/-- The same half-amplitude matrix estimate supplies every source/prior raw
projective estimate on the physical interface carrier. -/
theorem centralHalfAmplitude_sourceRawProjective
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (spread : Q')
    (crossRatio :
      ∀ left,
        left ∈ centralPositiveHalfStates w hw K half →
          ∀ right,
            right ∈ centralPositiveHalfStates w hw K half →
              ∀ first,
                first ∈ centralBoundaryChannels K half →
                  ∀ second,
                    second ∈ centralBoundaryChannels K half →
                      centralHalfAmplitude w K half left first *
                          centralHalfAmplitude w K half right second ≤
                        (spread * spread) *
                          (centralHalfAmplitude
                              w K half left second *
                            centralHalfAmplitude
                              w K half right first))
    (source : EdgeLabelling)
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half) :
    FiniteCrossRatioDiameterCertificate.ProjectiveSpreadBound
      spread
      (centralBoundaryChannels K half)
      (centralBoundaryGivenSourceNumerator
        w hw K half source)
      (centralBoundaryPriorNumerator
        w hw K half) := by
  let states :=
    centralPositiveHalfStates w hw K half
  let channels :=
    centralBoundaryChannels K half
  let weight :=
    centralBoundaryWeight w K half
  let amplitude :=
    centralHalfAmplitude w K half
  have hgeneric :=
    finiteSourceChannel_projective_channelPrior
      states channels weight amplitude spread
      (fun state _ channel =>
        centralHalfAmplitude_nonnegative
          hw K half state channel)
      (fun channel channel_mem =>
        centralBoundaryWeight_nonnegative_on
          hw channel channel_mem)
      crossRatio source source_mem
  intro first first_mem second second_mem
  exact hgeneric first first_mem second second_mem

/-! ## 4. Spacing-uniform one-field consumer -/

/-- A single spacing-uniform cross-ratio field for the genuine physical
half-amplitude matrix.  Unlike the downstream raw-posterior package, this
does not ask separately for a spread at every row and every column. -/
structure MatchedHalfAmplitudeProjectiveRows
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
  spread :
    Nat → Q'
  spread_square_le :
    ∀ scale,
      spread scale * spread scale ≤
        anchoredProjectiveCeiling
  half_amplitude_cross_ratio :
    ∀ scale left,
      left ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        ∀ right,
          right ∈
              centralPositiveHalfStates
                (matchedAllSpinWeight family coupling scale)
                (matchedAllSpinWeight_nonnegative
                  family coupling scale)
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) →
            ∀ first,
              first ∈
                  centralBoundaryChannels
                    (matchedAllSpinCutoff family coupling scale)
                    (halfExtent scale) →
                ∀ second,
                  second ∈
                      centralBoundaryChannels
                        (matchedAllSpinCutoff family coupling scale)
                        (halfExtent scale) →
                    centralHalfAmplitude
                          (matchedAllSpinWeight family coupling scale)
                          (matchedAllSpinCutoff family coupling scale)
                          (halfExtent scale) left first *
                        centralHalfAmplitude
                          (matchedAllSpinWeight family coupling scale)
                          (matchedAllSpinCutoff family coupling scale)
                          (halfExtent scale) right second ≤
                      (spread scale * spread scale) *
                        (centralHalfAmplitude
                            (matchedAllSpinWeight family coupling scale)
                            (matchedAllSpinCutoff family coupling scale)
                            (halfExtent scale) left second *
                          centralHalfAmplitude
                            (matchedAllSpinWeight family coupling scale)
                            (matchedAllSpinCutoff family coupling scale)
                            (halfExtent scale) right first)

namespace MatchedHalfAmplitudeProjectiveRows

/-- Positive-summation closure turns the single half-amplitude diameter
field into both raw posterior projective fields. -/
def toBoundaryRawProjectiveRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedHalfAmplitudeProjectiveRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedBoundaryRawProjectiveRows
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  harnack := data.harnack
  target_spread := fun scale _ => data.spread scale
  target_spread_square_le := by
    intro scale _ _
    exact data.spread_square_le scale
  target_raw_projective := by
    intro scale boundary boundary_mem
    exact centralHalfAmplitude_targetRawProjective
      (data.spread scale)
      (data.half_amplitude_cross_ratio scale)
      boundary boundary_mem
  source_spread := fun scale _ => data.spread scale
  source_spread_square_le := by
    intro scale _ _
    exact data.spread_square_le scale
  source_raw_projective := by
    intro scale source source_mem
    exact centralHalfAmplitude_sourceRawProjective
      (data.spread scale)
      (data.half_amplitude_cross_ratio scale)
      source source_mem

/-- Hence one spacing-uniform physical half-amplitude cross-ratio estimate
inhabits both requested spacing-uniform rowwise eighths. -/
def toRowwiseEighthEstimates
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedHalfAmplitudeProjectiveRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  data.toBoundaryRawProjectiveRows
    |>.toRowwiseEighthEstimates

end MatchedHalfAmplitudeProjectiveRows

end YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure.finiteColumn_projective_gramRowNumerator
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure.finiteRow_projective_channelTotal
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure.finiteSourceChannel_projective_channelPrior
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure.centralHalfAmplitude_targetRawProjective
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure.centralHalfAmplitude_sourceRawProjective
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure.MatchedHalfAmplitudeProjectiveRows.toBoundaryRawProjectiveRows
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure.MatchedHalfAmplitudeProjectiveRows.toRowwiseEighthEstimates
