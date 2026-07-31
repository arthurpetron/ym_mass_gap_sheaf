/-
# Canonical BF4 density contraction is exactly the physical centered row

The normalized reflected BF4 joint `J` has stationary marginal `pi`, and
`BF4PhysicalConditionalDensity` defines its density

    k(x,y) = J(x,y) / (pi(x) pi(y))

on the exact positive physical carrier.  This file proves the literal
identity

    sum_y |J(x,y) - pi(x)pi(y)|
      = pi(x) sum_y pi(y) |k(x,y) - 1|.

Consequently the remaining physical `1/16` estimate can be stated directly
as convergence of the genuine canonical Yang--Mills density to the constant
Perron density one.  A pointwise positive-kernel window implies the weighted
row bound without a carrier-cardinality or minimum-marginal loss.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4StationaryDensityBufferSplit
import YMGap.Continuum.RationalCrossRatioDiameter
import YMGap.Continuum.RcQuadResidualClose

namespace YMGap.Continuum.BF4PhysicalConditionalDensityContraction

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4BufferedPerronRowConvergence
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalConditionalDensity
open YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSignedKernelL1
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.RcQuadResidualClose
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
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

/-! ## 1. Exact density/physical-row identity -/

/-- On the retained carrier, one centered physical joint entry is the
source marginal times the corresponding weighted centered density entry. -/
theorem centeredPhysicalEntry_eqv_source_mul_densityEntry
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source target : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates w hw K half)
    (htarget :
      target ∈ centralPositiveHalfStates w hw K half) :
    centralNormalizedPhysicalReflectedKernel
          w hw K half source target +
        (-centralPhysicalVacuumJoint
          w hw K half source target) ≈
      centralPhysicalRowMarginal w hw K half source *
        finiteWeightedCenteredTransition
          (centralPhysicalRowMarginal w hw K half)
          (centralPhysicalConditionalDensity w hw K half)
          source target := by
  have hjoint :=
    normalizedJoint_eq_marginals_mul_density
      hsource htarget
  unfold centralPhysicalVacuumJoint
    finiteWeightedCenteredTransition finiteCenteredDensity
  refine Q'.eqv_trans _
    (((centralPhysicalRowMarginal w hw K half source *
        centralPhysicalRowMarginal w hw K half target) *
          centralPhysicalConditionalDensity
            w hw K half source target) +
      (-(centralPhysicalRowMarginal w hw K half source *
        centralPhysicalRowMarginal w hw K half target))) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _ hjoint
  · ac_qeqv

/-- **Exact canonical-density identity.**  The physical centered joint-row
mass is the source marginal times the weighted `L1` distance of the
canonical conditional density from the Perron density one. -/
theorem physicalCenteredPhysicalRowMass_eqv_densityCenteredRowMass
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates w hw K half) :
    physicalCenteredPhysicalRowMass
        w hw K half source ≈
      centralPhysicalRowMarginal w hw K half source *
        finiteWeightedCenteredRowMass
          (centralPositiveHalfStates w hw K half)
          (centralPhysicalRowMarginal w hw K half)
          (centralPhysicalConditionalDensity w hw K half)
          source := by
  let states := centralPositiveHalfStates w hw K half
  let pi := centralPhysicalRowMarginal w hw K half
  let density := centralPhysicalConditionalDensity w hw K half
  have hpi :
      (0 : Q') ≤ pi source :=
    centralPhysicalRowMarginal_nonnegative
      hw K half source
  unfold physicalCenteredPhysicalRowMass
    finiteJointDifferenceAbsRowMass
    finiteWeightedCenteredRowMass finiteL1Norm
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        pi source *
          Q'.abs
            (finiteWeightedCenteredTransition
              pi density source target))
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro target htarget
    refine Q'.eqv_trans _
      (Q'.abs
        (pi source *
          finiteWeightedCenteredTransition
            pi density source target)) _ ?_ ?_
    · exact Q'.abs_eqv_congr
        (centeredPhysicalEntry_eqv_source_mul_densityEntry
          hsource htarget)
    refine Q'.eqv_trans _
      (Q'.abs (pi source) *
        Q'.abs
          (finiteWeightedCenteredTransition
            pi density source target)) _ ?_ ?_
    · exact
        q_abs_mul_eqv
          (pi source)
          (finiteWeightedCenteredTransition
            pi density source target)
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_of_eq (abs_of_nonneg hpi))
  · exact listQSum_mul_left
      (pi source)
      (fun target =>
        Q'.abs
          (finiteWeightedCenteredTransition
            pi density source target))
      states

/-- Any weighted centered-density row bound transports to the physical
joint with the exact source-relative normalization. -/
theorem physicalCenteredPhysicalRowMass_le_of_densityCenteredRowMass
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates w hw K half)
    {rate : Q'}
    (density_bound :
      finiteWeightedCenteredRowMass
          (centralPositiveHalfStates w hw K half)
          (centralPhysicalRowMarginal w hw K half)
          (centralPhysicalConditionalDensity w hw K half)
          source ≤
        rate) :
    physicalCenteredPhysicalRowMass
        w hw K half source ≤
      rate *
        centralPhysicalRowMarginal
          w hw K half source := by
  have hpi :
      (0 : Q') ≤
        centralPhysicalRowMarginal
          w hw K half source :=
    centralPhysicalRowMarginal_nonnegative
      hw K half source
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (physicalCenteredPhysicalRowMass_eqv_densityCenteredRowMass
        hsource)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      density_bound hpi) ?_
  exact Q'.le_of_eqv
    (Q'.mul_comm_eqv
      (centralPhysicalRowMarginal
        w hw K half source)
      rate)

/-! ## 2. Stationary cross-ratio order implies positive-kernel convergence -/

/-- A strictly positive stationary density with finite cross-ratio diameter.
Both normalizations use the same probability weight. -/
structure FiniteStationaryCrossRatioDensity
    {State : Type}
    (states : List State) (weight : State → Q')
    (kernel : State → State → Q') : Type where
  certificate :
    FiniteCrossRatioDiameterCertificate
      kernel states states
  weight_nonnegative :
    ∀ state, state ∈ states →
      (0 : Q') ≤ weight state
  weight_total :
    listQSum weight states ≈ 1
  row_normalized :
    ∀ source, source ∈ states →
      listQSum
          (fun target =>
            weight target * kernel source target)
          states ≈
        1
  column_normalized :
    ∀ target, target ∈ states →
      listQSum
          (fun source =>
            weight source * kernel source target)
          states ≈
        1

namespace FiniteStationaryCrossRatioDensity

/-- Weighted row normalization cancels the free reference column in the
cross-ratio inequality.  Hence any two selected rows are pointwise ordered
with factor `spread^2`. -/
theorem row_domination
    {State : Type}
    {states : List State} {weight : State → Q'}
    {kernel : State → State → Q'}
    (data :
      FiniteStationaryCrossRatioDensity
        states weight kernel)
    (first : State) (hfirst : first ∈ states)
    (second : State) (hsecond : second ∈ states)
    (target : State) (htarget : target ∈ states) :
    kernel first target ≤
      (data.certificate.spread *
          data.certificate.spread) *
        kernel second target := by
  let square :=
    data.certificate.spread *
      data.certificate.spread
  have hterm :
      ∀ reference,
        reference ∈ states →
          weight reference *
              (kernel first target *
                kernel second reference) ≤
            weight reference *
              (square *
                (kernel first reference *
                  kernel second target)) := by
    intro reference hreference
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (data.certificate.crossRatioBound
        first hfirst second hsecond
        target htarget reference hreference)
      (data.weight_nonnegative reference hreference)
  have hsum :=
    listQSum_mono
      (fun reference =>
        weight reference *
          (kernel first target *
            kernel second reference))
      (fun reference =>
        weight reference *
          (square *
            (kernel first reference *
              kernel second target)))
      states hterm
  have hleft :
      listQSum
          (fun reference =>
            weight reference *
              (kernel first target *
                kernel second reference))
          states ≈
        kernel first target := by
    refine Q'.eqv_trans _
      (kernel first target *
        listQSum
          (fun reference =>
            weight reference *
              kernel second reference)
          states) _ ?_ ?_
    · refine Q'.eqv_trans _
        (listQSum
          (fun reference =>
            kernel first target *
              (weight reference *
                kernel second reference))
          states) _ ?_ ?_
      · apply listQSum_congr_on
        intro reference _
        ac_qeqv
      · exact listQSum_mul_left
          (kernel first target)
          (fun reference =>
            weight reference *
              kernel second reference)
          states
    exact Q'.eqv_trans _
      (kernel first target * 1) _
      (Q'.mul_eqv_congr_left
        (kernel first target) _ _
        (data.row_normalized second hsecond))
      (Q'.mul_one_eqv _)
  have hright :
      listQSum
          (fun reference =>
            weight reference *
              (square *
                (kernel first reference *
                  kernel second target)))
          states ≈
        square * kernel second target := by
    refine Q'.eqv_trans _
      ((square * kernel second target) *
        listQSum
          (fun reference =>
            weight reference *
              kernel first reference)
          states) _ ?_ ?_
    · refine Q'.eqv_trans _
        (listQSum
          (fun reference =>
            (square * kernel second target) *
              (weight reference *
                kernel first reference))
          states) _ ?_ ?_
      · apply listQSum_congr_on
        intro reference _
        ac_qeqv
      · exact listQSum_mul_left
          (square * kernel second target)
          (fun reference =>
            weight reference *
              kernel first reference)
          states
    exact Q'.eqv_trans _
      ((square * kernel second target) * 1) _
      (Q'.mul_eqv_congr_left _ _ _
        (data.row_normalized first hfirst))
      (Q'.mul_one_eqv _)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv hright))

/-- Column stationarity averages the row comparison and bounds every entry
above by `spread^2`. -/
theorem pointwise_upper
    {State : Type}
    {states : List State} {weight : State → Q'}
    {kernel : State → State → Q'}
    (data :
      FiniteStationaryCrossRatioDensity
        states weight kernel)
    (source : State) (hsource : source ∈ states)
    (target : State) (htarget : target ∈ states) :
    kernel source target ≤
      data.certificate.spread *
        data.certificate.spread := by
  let square :=
    data.certificate.spread *
      data.certificate.spread
  have hterm :
      ∀ reference,
        reference ∈ states →
          weight reference * kernel source target ≤
            weight reference *
              (square * kernel reference target) := by
    intro reference hreference
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (data.row_domination
        source hsource reference hreference
        target htarget)
      (data.weight_nonnegative reference hreference)
  have hsum :=
    listQSum_mono
      (fun reference =>
        weight reference * kernel source target)
      (fun reference =>
        weight reference *
          (square * kernel reference target))
      states hterm
  have hleft :
      listQSum
          (fun reference =>
            weight reference * kernel source target)
          states ≈
        kernel source target := by
    refine Q'.eqv_trans _
      (listQSum weight states *
        kernel source target) _
      (listQSum_mul_right
        weight (kernel source target) states) ?_
    exact Q'.eqv_trans _
      (1 * kernel source target) _
      (Q'.mul_eqv_congr_right _ _ _
        data.weight_total)
      (Q'.one_mul_eqv _)
  have hright :
      listQSum
          (fun reference =>
            weight reference *
              (square * kernel reference target))
          states ≈
        square := by
    refine Q'.eqv_trans _
      (square *
        listQSum
          (fun reference =>
            weight reference *
              kernel reference target)
          states) _ ?_ ?_
    · refine Q'.eqv_trans _
        (listQSum
          (fun reference =>
            square *
              (weight reference *
                kernel reference target))
          states) _ ?_ ?_
      · apply listQSum_congr_on
        intro reference _
        ac_qeqv
      · exact listQSum_mul_left
          square
          (fun reference =>
            weight reference *
              kernel reference target)
          states
    exact Q'.eqv_trans _
      (square * 1) _
      (Q'.mul_eqv_congr_left square _ _
        (data.column_normalized target htarget))
      (Q'.mul_one_eqv _)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv hright))

/-- Reversing the two rows and averaging gives the reciprocal-free lower
bound `1 <= spread^2 * k(x,y)`. -/
theorem pointwise_lower_scaled
    {State : Type}
    {states : List State} {weight : State → Q'}
    {kernel : State → State → Q'}
    (data :
      FiniteStationaryCrossRatioDensity
        states weight kernel)
    (source : State) (hsource : source ∈ states)
    (target : State) (htarget : target ∈ states) :
    (1 : Q') ≤
      (data.certificate.spread *
          data.certificate.spread) *
        kernel source target := by
  let square :=
    data.certificate.spread *
      data.certificate.spread
  have hterm :
      ∀ reference,
        reference ∈ states →
          weight reference * kernel reference target ≤
            weight reference *
              (square * kernel source target) := by
    intro reference hreference
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (data.row_domination
        reference hreference source hsource
        target htarget)
      (data.weight_nonnegative reference hreference)
  have hsum :=
    listQSum_mono
      (fun reference =>
        weight reference * kernel reference target)
      (fun reference =>
        weight reference *
          (square * kernel source target))
      states hterm
  have hleft :=
    data.column_normalized target htarget
  have hright :
      listQSum
          (fun reference =>
            weight reference *
              (square * kernel source target))
          states ≈
        square * kernel source target := by
    refine Q'.eqv_trans _
      (listQSum weight states *
        (square * kernel source target)) _
      (listQSum_mul_right
        weight (square * kernel source target) states) ?_
    exact Q'.eqv_trans _
      (1 * (square * kernel source target)) _
      (Q'.mul_eqv_congr_right _ _ _
        data.weight_total)
      (Q'.one_mul_eqv _)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv hright))

/-- A stationary projective diameter is automatically an additive
positive-kernel convergence estimate:

    |k(x,y) - 1| <= spread^2 - 1.

The proof is division-free and constructive. -/
theorem pointwise_abs_sub_one_le_spreadSquare_sub_one
    {State : Type}
    {states : List State} {weight : State → Q'}
    {kernel : State → State → Q'}
    (data :
      FiniteStationaryCrossRatioDensity
        states weight kernel)
    (source : State) (hsource : source ∈ states)
    (target : State) (htarget : target ∈ states) :
    Q'.abs (kernel source target + (-1)) ≤
      data.certificate.spread *
          data.certificate.spread +
        (-1) := by
  let value := kernel source target
  let square :=
    data.certificate.spread *
      data.certificate.spread
  have hspreadNonnegative :
      (0 : Q') ≤ data.certificate.spread :=
    Q'.le_of_lt data.certificate.spread_pos
  have hsquareOne :
      (1 : Q') ≤ square := by
    have hmul :
        (1 : Q') * 1 ≤
          data.certificate.spread *
            data.certificate.spread :=
      Q'.mul_le_mul_of_nonneg
        data.certificate.one_le_spread
        data.certificate.one_le_spread
        hspreadNonnegative Q'.zero_le_one
    exact Q'.le_trans' _ _ _ (by decide) hmul
  have hupper : value ≤ square :=
    data.pointwise_upper source hsource target htarget
  have hlowerScaled : (1 : Q') ≤ square * value :=
    data.pointwise_lower_scaled source hsource target htarget
  by_cases hone : (1 : Q') ≤ value
  · have hdiffNonnegative :
        (0 : Q') ≤ value + (-1) :=
      Q'.sub_nonneg_of_le hone
    rw [abs_of_nonneg hdiffNonnegative]
    exact Q'.add_le_add_right _ _ (-1) hupper
  · have hvalueOne : value ≤ (1 : Q') :=
      Q'.le_of_not_le hone
    have hdiffNonpositive :
        value + (-1) ≤ (0 : Q') := by
      have h :=
        Q'.add_le_add_right value 1 (-1) hvalueOne
      exact Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (by decide))
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (q_abs_of_nonpos hdiffNonpositive)) ?_
    have hscaledDifferenceNonnegative :
        (0 : Q') ≤ square * value + (-1) :=
      Q'.sub_nonneg_of_le hlowerScaled
    have hfirst :
        -(value + (-1)) ≤
          (square * value + (-1)) +
            (-(value + (-1))) := by
      have h :=
        Q'.add_le_add_right
          0 (square * value + (-1))
          (-(value + (-1)))
          hscaledDifferenceNonnegative
      rw [Q'.zero_add'] at h
      exact h
    have hfirstEqv :
        (square * value + (-1)) +
            (-(value + (-1))) ≈
          (square + (-1)) * value := by
      refine Q'.eqv_trans _
        ((square * value + (-1)) +
          ((-value) + (-(-1)))) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.neg_add_eqv value (-1))
      refine Q'.eqv_trans _
        ((square * value + (-1)) +
          ((-value) + 1)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.add_eqv_congr_left
            (-value) _ _
            (Q'.neg_neg_eqv 1))
      refine Q'.eqv_trans _
        ((square * value + (-value)) +
          ((-1) + 1)) _ ?_ ?_
      · exact Q'.add_swap_inner
          (square * value) (-1) (-value) 1
      refine Q'.eqv_trans _
        ((square * value + (-value)) + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _
            (Q'.add_comm_eqv (-1) 1)
            (Q'.add_neg_self_eqv 1))
      refine Q'.eqv_trans _
        (square * value + (-value)) _ ?_ ?_
      · exact Q'.eqv_of_eq
          (Q'.add_zero'
            (square * value + (-value)))
      refine Q'.eqv_trans _
        (square * value + ((-1) * value)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm
            (Q'.eqv_trans _ _ _
              (Q'.neg_mul_eqv 1 value)
              (Q'.neg_eqv_congr _ _
                (Q'.one_mul_eqv value))))
      exact Q'.eqv_symm
        (Q'.add_mul_eqv square (-1) value)
    have hsquareDifferenceNonnegative :
        (0 : Q') ≤ square + (-1) :=
      Q'.sub_nonneg_of_le hsquareOne
    have hsecond :
        (square + (-1)) * value ≤
          (square + (-1)) * 1 :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        hvalueOne hsquareDifferenceNonnegative
    exact Q'.le_trans' _ _ _ hfirst
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv hfirstEqv)
        (Q'.le_trans' _ _ _ hsecond
          (Q'.le_of_eqv
            (Q'.mul_one_eqv
              (square + (-1))))))

/-- If the squared projective spread is at most `17/16`, the stationary
density lies pointwise within `1/16` of one. -/
theorem pointwise_sixteenth_of_spreadSquare
    {State : Type}
    {states : List State} {weight : State → Q'}
    {kernel : State → State → Q'}
    (data :
      FiniteStationaryCrossRatioDensity
        states weight kernel)
    (spreadSquare_le :
      data.certificate.spread *
          data.certificate.spread ≤
        Q'.mkPos 17 16 (by decide))
    (source : State) (hsource : source ∈ states)
    (target : State) (htarget : target ∈ states) :
    Q'.abs (kernel source target + (-1)) ≤
      Q'.mkPos 1 16 (by decide) := by
  refine Q'.le_trans' _ _ _
    (data.pointwise_abs_sub_one_le_spreadSquare_sub_one
      source hsource target htarget) ?_
  have h :=
    Q'.add_le_add_right
      (data.certificate.spread *
        data.certificate.spread)
      (Q'.mkPos 17 16 (by decide))
      (-1) spreadSquare_le
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (by decide))

end FiniteStationaryCrossRatioDensity

/-! ## 3. Pointwise Yang--Mills positive-kernel convergence -/

/-- A pointwise convergence window for one row of the genuine canonical
BF4 density.  This statement is support-safe: it is required only on the
positive physical carrier, where the density is actually normalized. -/
structure PhysicalConditionalDensityPointwiseWindow
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (source : EdgeLabelling)
    (tolerance : Q') : Type where
  source_mem :
    source ∈ centralPositiveHalfStates w hw K half
  tolerance_nonnegative :
    (0 : Q') ≤ tolerance
  pointwise :
    ∀ target,
      target ∈ centralPositiveHalfStates w hw K half →
        Q'.abs
            (centralPhysicalConditionalDensity
                w hw K half source target +
              (-1)) ≤
          tolerance

namespace PhysicalConditionalDensityPointwiseWindow

/-- The pointwise density window integrates with total stationary mass one;
there is no factor equal to the carrier size. -/
theorem density_centered_row_le
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    {tolerance : Q'}
    (window :
      PhysicalConditionalDensityPointwiseWindow
        w hw K half source tolerance) :
    finiteWeightedCenteredRowMass
        (centralPositiveHalfStates w hw K half)
        (centralPhysicalRowMarginal w hw K half)
        (centralPhysicalConditionalDensity w hw K half)
        source ≤
      tolerance := by
  let states := centralPositiveHalfStates w hw K half
  let pi := centralPhysicalRowMarginal w hw K half
  let density := centralPhysicalConditionalDensity w hw K half
  unfold finiteWeightedCenteredRowMass finiteL1Norm
    finiteWeightedCenteredTransition finiteCenteredDensity
  have hpoint :
      ∀ target,
        target ∈ states →
          Q'.abs
              (pi target *
                (density source target + (-1))) ≤
            pi target * tolerance := by
    intro target htarget
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (q_abs_mul_eqv
          (pi target)
          (density source target + (-1)))) ?_
    rw [abs_of_nonneg
      (centralPhysicalRowMarginal_nonnegative
        hw K half target)]
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (window.pointwise target htarget)
      (centralPhysicalRowMarginal_nonnegative
        hw K half target)
  refine Q'.le_trans' _ _ _
    (listQSum_mono _ _ states hpoint) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (listQSum_mul_right pi tolerance states)) ?_
  refine Q'.le_of_eqv
    (Q'.eqv_trans _ (1 * tolerance) _
      (Q'.mul_eqv_congr_right _ _ _
        (centralPositiveRowMarginal_total_one
          w hw K half))
      (Q'.one_mul_eqv tolerance))

/-- Hence a pointwise canonical-density window gives the exact
source-relative physical centered-row estimate. -/
theorem physical_centered_row_le
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    {tolerance : Q'}
    (window :
      PhysicalConditionalDensityPointwiseWindow
        w hw K half source tolerance) :
    physicalCenteredPhysicalRowMass
        w hw K half source ≤
      tolerance *
        centralPhysicalRowMarginal
          w hw K half source :=
  physicalCenteredPhysicalRowMass_le_of_densityCenteredRowMass
    window.source_mem
    window.density_centered_row_le

/-- The target `1/16` pointwise positive-kernel convergence window closes
the physical row needed by the common-rank-one triangle. -/
theorem physical_centered_row_sixteenth
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (window :
      PhysicalConditionalDensityPointwiseWindow
        w hw K half source
        (Q'.mkPos 1 16 (by decide))) :
    physicalCenteredPhysicalRowMass
        w hw K half source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          w hw K half source :=
  window.physical_centered_row_le

end PhysicalConditionalDensityPointwiseWindow

/-! ## 4. Support-safe core/tail positive-kernel convergence -/

/-- Pointwise convergence is needed only on a selected core.  Outside the
core, separate stationary and conditional row masses pay the absolute
difference. -/
structure FiniteWeightedDensityCoreTailWindow
    {State : Type}
    (states : List State) (weight : State → Q')
    (kernel : State → State → Q')
    (source : State) (inCore : State → Bool)
    (coreTolerance tailTolerance : Q') : Type where
  weight_nonnegative :
    ∀ state, state ∈ states →
      (0 : Q') ≤ weight state
  kernel_nonnegative :
    ∀ target, target ∈ states →
      (0 : Q') ≤ kernel source target
  weight_total :
    listQSum weight states ≈ 1
  coreTolerance_nonnegative :
    (0 : Q') ≤ coreTolerance
  core_pointwise :
    ∀ target,
      target ∈ states →
        inCore target = true →
          Q'.abs (kernel source target + (-1)) ≤
            coreTolerance
  tail_weight :
    listQSum
        (fun target =>
          if inCore target = true then 0
          else weight target)
        states ≤
      tailTolerance
  tail_kernel :
    listQSum
        (fun target =>
          if inCore target = true then 0
          else weight target * kernel source target)
        states ≤
      tailTolerance

namespace FiniteWeightedDensityCoreTailWindow

/-- **Core/tail density estimate.**

The core contributes `coreTolerance * sum pi`.  On the tail,
`|k-1| <= k+1`, so the conditional tail and stationary tail each contribute
once.  No cardinality or minimum weight occurs. -/
theorem density_centered_row_le
    {State : Type}
    {states : List State} {weight : State → Q'}
    {kernel : State → State → Q'}
    {source : State} {inCore : State → Bool}
    {coreTolerance tailTolerance : Q'}
    (window :
      FiniteWeightedDensityCoreTailWindow
        states weight kernel source inCore
        coreTolerance tailTolerance) :
    finiteWeightedCenteredRowMass
        states weight kernel source ≤
      (coreTolerance + tailTolerance) +
        tailTolerance := by
  let tailWeight : State → Q' := fun target =>
    if inCore target = true then 0
    else weight target
  let tailKernel : State → Q' := fun target =>
    if inCore target = true then 0
    else weight target * kernel source target
  let majorant : State → Q' := fun target =>
    (weight target * coreTolerance +
      tailKernel target) +
        tailWeight target
  have hpoint :
      ∀ target,
        target ∈ states →
          Q'.abs
              (weight target *
                (kernel source target + (-1))) ≤
            majorant target := by
    intro target htarget
    by_cases hcore : inCore target = true
    · have hscaled :
          weight target *
              Q'.abs
                (kernel source target + (-1)) ≤
            weight target * coreTolerance :=
        Q'.mul_le_mul_of_nonneg_left _ _ _
          (window.core_pointwise target htarget hcore)
          (window.weight_nonnegative target htarget)
      have habs :
          Q'.abs
              (weight target *
                (kernel source target + (-1))) ≈
            weight target *
              Q'.abs
                (kernel source target + (-1)) := by
        refine Q'.eqv_trans _ _ _
          (q_abs_mul_eqv
            (weight target)
            (kernel source target + (-1))) ?_
        exact Q'.mul_eqv_congr_right _ _ _
          (Q'.eqv_of_eq
            (abs_of_nonneg
              (window.weight_nonnegative
                target htarget)))
      unfold majorant tailKernel tailWeight
      rw [if_pos hcore, if_pos hcore]
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv habs)
        (Q'.le_trans' _ _ _ hscaled
          (Q'.le_of_eqv (by
            exact Q'.eqv_symm
              (Q'.eqv_trans _ _ _
                (Q'.eqv_of_eq
                  (Q'.add_zero'
                    (weight target *
                      coreTolerance + 0)))
                (Q'.eqv_of_eq
                  (Q'.add_zero'
                    (weight target *
                      coreTolerance)))))))
    · have hkernelNonnegative :=
        window.kernel_nonnegative target htarget
      have habsDifference :
          Q'.abs (kernel source target + (-1)) ≤
            kernel source target + 1 := by
        have htriangle :=
          Q'.abs_add_le'
            (kernel source target) (-1)
        refine Q'.le_trans' _ _ _ htriangle ?_
        exact Q'.add_le_add
          (Q'.le_of_eqv
            (Q'.eqv_of_eq
              (abs_of_nonneg hkernelNonnegative)))
          (Q'.le_of_eqv (by decide))
      have hscaled :
          weight target *
              Q'.abs
                (kernel source target + (-1)) ≤
            weight target *
              (kernel source target + 1) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _
          habsDifference
          (window.weight_nonnegative target htarget)
      have habs :
          Q'.abs
              (weight target *
                (kernel source target + (-1))) ≈
            weight target *
              Q'.abs
                (kernel source target + (-1)) := by
        refine Q'.eqv_trans _ _ _
          (q_abs_mul_eqv
            (weight target)
            (kernel source target + (-1))) ?_
        exact Q'.mul_eqv_congr_right _ _ _
          (Q'.eqv_of_eq
            (abs_of_nonneg
              (window.weight_nonnegative
                target htarget)))
      have hbase :
          Q'.abs
              (weight target *
                (kernel source target + (-1))) ≤
            weight target * kernel source target +
              weight target := by
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv habs)
          (Q'.le_trans' _ _ _ hscaled
            (Q'.le_of_eqv (by
              calc
                weight target *
                      (kernel source target + 1) ≈
                    weight target *
                        kernel source target +
                      weight target * 1 :=
                  Q'.mul_add_eqv _ _ _
                _ ≈
                    weight target *
                        kernel source target +
                      weight target :=
                  Q'.add_eqv_congr_left _ _ _
                    (Q'.mul_one_eqv _))))
      have hcoreContribution :
          (0 : Q') ≤
            weight target * coreTolerance :=
        Q'.mul_nonneg _ _
          (window.weight_nonnegative target htarget)
          window.coreTolerance_nonnegative
      have hinclusion :
          weight target * kernel source target +
              weight target ≤
            (weight target * coreTolerance +
                weight target * kernel source target) +
              weight target := by
        have hfirst :
            weight target * kernel source target ≤
              weight target * coreTolerance +
                weight target * kernel source target := by
          have h :=
            Q'.add_le_add_right
              0 (weight target * coreTolerance)
              (weight target * kernel source target)
              hcoreContribution
          rw [Q'.zero_add'] at h
          exact h
        exact
          Q'.add_le_add_right
            (weight target * kernel source target)
            (weight target * coreTolerance +
              weight target * kernel source target)
            (weight target)
            hfirst
      unfold majorant tailKernel tailWeight
      rw [if_neg hcore, if_neg hcore]
      exact Q'.le_trans' _ _ _ hbase hinclusion
  unfold finiteWeightedCenteredRowMass finiteL1Norm
    finiteWeightedCenteredTransition finiteCenteredDensity
  refine Q'.le_trans' _ _ _
    (listQSum_mono _ majorant states hpoint) ?_
  have hmajorant :
      listQSum majorant states ≈
        (listQSum
            (fun target =>
              weight target * coreTolerance)
            states +
          listQSum tailKernel states) +
            listQSum tailWeight states := by
    unfold majorant
    refine Q'.eqv_trans _
      (listQSum
          (fun target =>
            weight target * coreTolerance +
              tailKernel target)
          states +
        listQSum tailWeight states) _ ?_ ?_
    · exact listQSum_add _ _ states
    exact Q'.add_eqv_congr_right _ _ _
      (listQSum_add _ _ states)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv hmajorant) ?_
  have hcoreSum :
      listQSum
          (fun target =>
            weight target * coreTolerance)
          states ≈
        coreTolerance := by
    refine Q'.eqv_trans _
      (listQSum weight states * coreTolerance) _
      (listQSum_mul_right
        weight coreTolerance states) ?_
    exact Q'.eqv_trans _
      (1 * coreTolerance) _
      (Q'.mul_eqv_congr_right _ _ _
        window.weight_total)
      (Q'.one_mul_eqv _)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.add_eqv_congr_right _ _ _
        (Q'.add_eqv_congr_right _ _ _
          hcoreSum))) ?_
  exact Q'.add_le_add
    (Q'.add_le_add_left
      coreTolerance
      (listQSum tailKernel states)
      tailTolerance
      window.tail_kernel)
    window.tail_weight

/-- With a `1/32` core window and two `1/64` tails, the exact weighted
density row is at most `1/16`. -/
theorem density_centered_row_sixteenth
    {State : Type}
    {states : List State} {weight : State → Q'}
    {kernel : State → State → Q'}
    {source : State} {inCore : State → Bool}
    (window :
      FiniteWeightedDensityCoreTailWindow
        states weight kernel source inCore
        (Q'.mkPos 1 32 (by decide))
        (Q'.mkPos 1 64 (by decide))) :
    finiteWeightedCenteredRowMass
        states weight kernel source ≤
      Q'.mkPos 1 16 (by decide) :=
  Q'.le_trans' _ _ _
    window.density_centered_row_le
    (Q'.le_of_eqv (by decide))

end FiniteWeightedDensityCoreTailWindow

/-- A support-safe core/tail window for the genuine canonical BF4 density. -/
structure PhysicalConditionalDensityCoreTailWindow
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (source : EdgeLabelling)
    (inCore : EdgeLabelling → Bool) : Type where
  source_mem :
    source ∈ centralPositiveHalfStates w hw K half
  window :
    Nonempty
      (FiniteWeightedDensityCoreTailWindow
        (centralPositiveHalfStates w hw K half)
        (centralPhysicalRowMarginal w hw K half)
        (centralPhysicalConditionalDensity w hw K half)
        source inCore
        (Q'.mkPos 1 32 (by decide))
        (Q'.mkPos 1 64 (by decide)))

namespace PhysicalConditionalDensityCoreTailWindow

/-- The `1/32 + 1/64 + 1/64` core/tail split proves the physical
source-relative `1/16` row while permitting fusion zeros outside the core. -/
theorem physical_centered_row_sixteenth
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    {inCore : EdgeLabelling → Bool}
    (data :
      PhysicalConditionalDensityCoreTailWindow
        w hw K half source inCore) :
    physicalCenteredPhysicalRowMass
        w hw K half source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          w hw K half source :=
  by
    obtain ⟨window⟩ := data.window
    exact
      physicalCenteredPhysicalRowMass_le_of_densityCenteredRowMass
        data.source_mem window.density_centered_row_sixteenth

end PhysicalConditionalDensityCoreTailWindow

/-! ## 5. Canonical BF4 cross-ratio specialization -/

/-- The canonical physical BF4 density is stationary with respect to the
exact positive-row marginal.  Therefore any full-support cross-ratio
certificate for this density automatically supplies the generic stationary
projective package. -/
def centralPhysicalConditionalDensityStationaryCrossRatio
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (certificate :
      FiniteCrossRatioDiameterCertificate
        (centralPhysicalConditionalDensity w hw K half)
        (centralPositiveHalfStates w hw K half)
        (centralPositiveHalfStates w hw K half)) :
    FiniteStationaryCrossRatioDensity
      (centralPositiveHalfStates w hw K half)
      (centralPhysicalRowMarginal w hw K half)
      (centralPhysicalConditionalDensity w hw K half) where
  certificate := certificate
  weight_nonnegative := by
    intro state _
    exact centralPhysicalRowMarginal_nonnegative
      hw K half state
  weight_total :=
    centralPositiveRowMarginal_total_one
      w hw K half
  row_normalized := by
    intro source hsource
    exact
      centralPhysicalConditionalDensity_row_normalized
        hsource
  column_normalized := by
    intro target htarget
    exact
      centralPhysicalConditionalDensity_column_normalized
        htarget

/-- A squared projective diameter at most `17/16` for the genuine canonical
BF4 density gives its support-safe pointwise `1/16` convergence window. -/
def physicalConditionalDensityPointwiseWindow_of_crossRatio
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (certificate :
      FiniteCrossRatioDiameterCertificate
        (centralPhysicalConditionalDensity w hw K half)
        (centralPositiveHalfStates w hw K half)
        (centralPositiveHalfStates w hw K half))
    (spreadSquare_le :
      certificate.spread * certificate.spread ≤
        Q'.mkPos 17 16 (by decide))
    (source : EdgeLabelling)
    (hsource :
      source ∈ centralPositiveHalfStates w hw K half) :
    PhysicalConditionalDensityPointwiseWindow
      w hw K half source
      (Q'.mkPos 1 16 (by decide)) where
  source_mem := hsource
  tolerance_nonnegative := by decide
  pointwise := by
    intro target htarget
    exact
      (centralPhysicalConditionalDensityStationaryCrossRatio
        certificate).pointwise_sixteenth_of_spreadSquare
          spreadSquare_le source hsource target htarget

/-! ## 6. Spacing-uniform positive-kernel closure -/

/-- The all-scale Yang--Mills-specific positive-kernel target.

The first analytic field is the calibrated cross-zero profile Harnack
window.  The second is now the literal pointwise convergence of the
canonical physical BF4 density to its Perron density one.  No Mehler
surrogate, terminal strict-positivity assumption, or renamed joint-row
estimate appears in the second field. -/
structure MatchedPhysicalConditionalDensityWindows
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  calibrated_harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale) 0
  density_window :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        Nonempty
          (PhysicalConditionalDensityPointwiseWindow
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)
            source
            (Q'.mkPos 1 16 (by decide)))

namespace MatchedPhysicalConditionalDensityWindows

/-- The pointwise canonical-density windows give the physical centered
`1/16` row uniformly along the AF spacing family. -/
theorem physical_centered_row_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalConditionalDensityWindows
        family law spacing coupling
        halfExtent diagonalOrder)
    (scale : Nat) (source : EdgeLabelling)
    (source_mem :
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)) :
    physicalCenteredPhysicalRowMass
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale) source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale) source := by
  obtain ⟨window⟩ :=
    data.density_window scale source source_mem
  exact window.physical_centered_row_sixteenth

/-- The density formulation inhabits the common-rank-one physical
sixteenth consumer. -/
def toCrossZeroPhysicalSixteenthRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalConditionalDensityWindows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedCrossZeroPhysicalSixteenthRows
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  harnack := data.calibrated_harnack
  physical_centered_row_sixteenth :=
    data.physical_centered_row_sixteenth

/-- Therefore canonical positive-kernel convergence at tolerance `1/16`
proves both of the requested spacing-uniform rowwise `1/8` fields. -/
def toRowwiseEighthEstimates
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalConditionalDensityWindows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  data.toCrossZeroPhysicalSixteenthRows
    |>.toRowwiseEighthEstimates

end MatchedPhysicalConditionalDensityWindows

/-- Spacing-uniform support-safe convergence data.  The retained core may
change with the AF scale; fusion-zero channels may be placed in its tail,
provided both their stationary mass and their conditional row mass obey the
explicit `1/64` budgets. -/
structure MatchedPhysicalConditionalDensityCoreTailRows
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  calibrated_harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale) 0
  inCore :
    Nat → EdgeLabelling → Bool
  coreTail_exists :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        Nonempty
          (PhysicalConditionalDensityCoreTailWindow
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)
            source
            (inCore scale))

namespace MatchedPhysicalConditionalDensityCoreTailRows

/-- Every scale/source core-tail certificate gives the physical centered
`1/16` row. -/
theorem physical_centered_row_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalConditionalDensityCoreTailRows
        family law spacing coupling
        halfExtent diagonalOrder)
    (scale : Nat) (source : EdgeLabelling)
    (source_mem :
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)) :
    physicalCenteredPhysicalRowMass
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale) source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale) source := by
  obtain ⟨window⟩ :=
    data.coreTail_exists scale source source_mem
  exact window.physical_centered_row_sixteenth

/-- The support-safe core-tail family supplies the common physical
sixteenth consumer. -/
def toCrossZeroPhysicalSixteenthRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalConditionalDensityCoreTailRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedCrossZeroPhysicalSixteenthRows
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  harnack := data.calibrated_harnack
  physical_centered_row_sixteenth :=
    data.physical_centered_row_sixteenth

/-- Thus the spacing-dependent core/tail construction inhabits both
requested rowwise `1/8` estimates. -/
def toRowwiseEighthEstimates
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalConditionalDensityCoreTailRows
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  data.toCrossZeroPhysicalSixteenthRows
    |>.toRowwiseEighthEstimates

end MatchedPhysicalConditionalDensityCoreTailRows

/-- A spacing-uniform full-support projective certificate for the canonical
BF4 density.  Stationarity upgrades this single diameter estimate to the
pointwise windows above, so no rowwise convergence premise is retained. -/
structure MatchedPhysicalConditionalDensityCrossRatio
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  calibrated_harnack :
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
  one_le_spread :
    ∀ scale, (1 : Q') ≤ spread scale
  density_strictlyPositive :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        ∀ target,
          target ∈
              centralPositiveHalfStates
                (matchedAllSpinWeight family coupling scale)
                (matchedAllSpinWeight_nonnegative
                  family coupling scale)
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) →
            (0 : Q') <
              centralPhysicalConditionalDensity
                (matchedAllSpinWeight family coupling scale)
                (matchedAllSpinWeight_nonnegative
                  family coupling scale)
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale)
                source target
  density_crossRatioBound :
    ∀ scale first,
      first ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        ∀ second,
          second ∈
              centralPositiveHalfStates
                (matchedAllSpinWeight family coupling scale)
                (matchedAllSpinWeight_nonnegative
                  family coupling scale)
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) →
            ∀ left,
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
                    centralPhysicalConditionalDensity
                          (matchedAllSpinWeight family coupling scale)
                          (matchedAllSpinWeight_nonnegative
                            family coupling scale)
                          (matchedAllSpinCutoff family coupling scale)
                          (halfExtent scale)
                          first left *
                        centralPhysicalConditionalDensity
                          (matchedAllSpinWeight family coupling scale)
                          (matchedAllSpinWeight_nonnegative
                            family coupling scale)
                          (matchedAllSpinCutoff family coupling scale)
                          (halfExtent scale)
                          second right ≤
                      (spread scale * spread scale) *
                        (centralPhysicalConditionalDensity
                            (matchedAllSpinWeight family coupling scale)
                            (matchedAllSpinWeight_nonnegative
                              family coupling scale)
                            (matchedAllSpinCutoff family coupling scale)
                            (halfExtent scale)
                            first right *
                          centralPhysicalConditionalDensity
                            (matchedAllSpinWeight family coupling scale)
                            (matchedAllSpinWeight_nonnegative
                              family coupling scale)
                            (matchedAllSpinCutoff family coupling scale)
                            (halfExtent scale)
                            second left)
  spreadSquare_le :
    ∀ scale,
      spread scale * spread scale ≤
        Q'.mkPos 17 16 (by decide)

namespace MatchedPhysicalConditionalDensityCrossRatio

/-- Bundle the proposition-valued scale fields into the standard finite
cross-ratio certificate only when it is consumed. -/
def certificateAt
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalConditionalDensityCrossRatio
        family law spacing coupling
        halfExtent diagonalOrder)
    (scale : Nat) :
    FiniteCrossRatioDiameterCertificate
      (centralPhysicalConditionalDensity
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale))
      (centralPositiveHalfStates
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale))
      (centralPositiveHalfStates
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)) where
  spread := data.spread scale
  one_le_spread := data.one_le_spread scale
  strictlyPositive :=
    data.density_strictlyPositive scale
  crossRatioBound :=
    data.density_crossRatioBound scale

/-- Stationarity converts the scale-uniform cross-ratio diameter into the
pointwise canonical-density closure. -/
def toDensityWindows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalConditionalDensityCrossRatio
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicalConditionalDensityWindows
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  calibrated_harnack := data.calibrated_harnack
  density_window := by
    intro scale source hsource
    exact ⟨
      physicalConditionalDensityPointwiseWindow_of_crossRatio
        (data.certificateAt scale)
        (data.spreadSquare_le scale)
        source hsource⟩

/-- Hence a canonical-density projective diameter `s² <= 17/16` inhabits
both spacing-uniform `1/8` fields. -/
def toRowwiseEighthEstimates
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalConditionalDensityCrossRatio
        family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  data.toDensityWindows
    |>.toRowwiseEighthEstimates

end MatchedPhysicalConditionalDensityCrossRatio

end YMGap.Continuum.BF4PhysicalConditionalDensityContraction

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.centeredPhysicalEntry_eqv_source_mul_densityEntry
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.physicalCenteredPhysicalRowMass_eqv_densityCenteredRowMass
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.physicalCenteredPhysicalRowMass_le_of_densityCenteredRowMass
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.FiniteStationaryCrossRatioDensity.row_domination
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.FiniteStationaryCrossRatioDensity.pointwise_upper
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.FiniteStationaryCrossRatioDensity.pointwise_lower_scaled
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.FiniteStationaryCrossRatioDensity.pointwise_abs_sub_one_le_spreadSquare_sub_one
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.FiniteStationaryCrossRatioDensity.pointwise_sixteenth_of_spreadSquare
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.PhysicalConditionalDensityPointwiseWindow.density_centered_row_le
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.PhysicalConditionalDensityPointwiseWindow.physical_centered_row_sixteenth
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.FiniteWeightedDensityCoreTailWindow.density_centered_row_le
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.FiniteWeightedDensityCoreTailWindow.density_centered_row_sixteenth
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.PhysicalConditionalDensityCoreTailWindow.physical_centered_row_sixteenth
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.centralPhysicalConditionalDensityStationaryCrossRatio
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.physicalConditionalDensityPointwiseWindow_of_crossRatio
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.MatchedPhysicalConditionalDensityWindows.physical_centered_row_sixteenth
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.MatchedPhysicalConditionalDensityWindows.toCrossZeroPhysicalSixteenthRows
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.MatchedPhysicalConditionalDensityWindows.toRowwiseEighthEstimates
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.MatchedPhysicalConditionalDensityCoreTailRows.physical_centered_row_sixteenth
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.MatchedPhysicalConditionalDensityCoreTailRows.toCrossZeroPhysicalSixteenthRows
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.MatchedPhysicalConditionalDensityCoreTailRows.toRowwiseEighthEstimates
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.MatchedPhysicalConditionalDensityCrossRatio.toDensityWindows
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensityContraction.MatchedPhysicalConditionalDensityCrossRatio.toRowwiseEighthEstimates
