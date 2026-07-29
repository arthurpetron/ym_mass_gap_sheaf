/-
# Canonical finite centered spectral budget for the BF4 Mehler Gram

The positive BF4 feature-word Gram already supplies symmetry, strict
partition positivity, and positive semidefiniteness.  This module constructs
the remaining physical-mean-zero Rayleigh datum at every fixed finite BF4
scale.

The construction retains the cancellation which the order-one
Cauchy--Schwarz bound discarded.  It subtracts the exact physical marginal
vacuum joint

    V(x,y) = pi(x) pi(y),

whose quadratic form vanishes on `CentralPhysicalMeanZero`, and takes the
finite maximum of the exact row-relative masses of `M - V`.  Every retained
physical marginal is strictly positive, so each ratio is computed by
`Q'.divPos`; outside the retained carrier it is definitionally zero.

The resulting rate is an executable rational, not an analytic assumption.
Combining it with `BF4CanonicalFiniteNumeratorPartitionBudget` gives a
complete fixed-scale positive-Gram comparison certificate.  No claim of a
spacing-uniform quarter bound is made: the remaining theorem is to control
this exact sequence along the genuine physical AF trajectory.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
import YMGap.Continuum.BF4ReflectedAllSpinMehlerGramAFRow

namespace YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4AFUniformRowRelativeBudget
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramAFRow
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
open YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The normalized feature Gram and physical vacuum joint -/

/-- The literal normalized positive BF4 feature-word Gram entry. -/
def normalizedBF4MehlerGramJoint
    (diagonalOrder crossOrder : Nat)
    (left right : EdgeLabelling) : Q' :=
  Q'.divPos
    (bf4MehlerGramNumerator
      (diagonalOrder + 1) crossOrder left right)
    (bf4MehlerGramVacuumPartition
      (diagonalOrder + 1) crossOrder)
    (bf4MehlerGramVacuumPartition_pos
      (shiftedDiagonalVacuumCertificate diagonalOrder)
      crossOrder)

theorem normalizedBF4MehlerGramJoint_symmetric
    (diagonalOrder crossOrder : Nat)
    (left right : EdgeLabelling) :
    normalizedBF4MehlerGramJoint
        diagonalOrder crossOrder left right ≈
      normalizedBF4MehlerGramJoint
        diagonalOrder crossOrder right left := by
  unfold normalizedBF4MehlerGramJoint Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _
    (bf4MehlerGramNumerator_symmetric
      (diagonalOrder + 1) crossOrder left right)

/-- The rank-one joint selected by the exact physical stationary marginal. -/
def centralPhysicalVacuumJoint
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat)
    (left right : EdgeLabelling) : Q' :=
  centralPhysicalRowMarginal w hw K halfExtent left *
    centralPhysicalRowMarginal w hw K halfExtent right

theorem centralPhysicalVacuumJoint_symmetric
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat)
    (left right : EdgeLabelling) :
    centralPhysicalVacuumJoint
        w hw K halfExtent left right ≈
      centralPhysicalVacuumJoint
        w hw K halfExtent right left := by
  exact Q'.mul_comm_eqv _ _

/-! ## 2. Exact centered row ratios -/

/-- Absolute mass of one row after removing the exact physical vacuum joint
from the normalized positive feature Gram. -/
def exactCenteredMehlerGramRowMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (source : EdgeLabelling) : Q' :=
  finiteJointDifferenceAbsRowMass
    (centralPositiveHalfStates w hw K halfExtent)
    (normalizedBF4MehlerGramJoint
      diagonalOrder crossOrder)
    (centralPhysicalVacuumJoint
      w hw K halfExtent)
    source

theorem exactCenteredMehlerGramRowMass_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (source : EdgeLabelling) :
    (0 : Q') ≤
      exactCenteredMehlerGramRowMass
        w hw K halfExtent diagonalOrder crossOrder source := by
  unfold exactCenteredMehlerGramRowMass
    finiteJointDifferenceAbsRowMass
  exact listQSum_nonnegative_on _ _
    (fun target _ => Q'.abs_nonneg _)

/-- Exact centered row mass divided by the physical row marginal.  The
zero branch is used only outside the retained positive carrier. -/
def exactCenteredMehlerGramRowRatio
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (source : EdgeLabelling) : Q' :=
  if hpositive :
      (0 : Q') <
        centralPhysicalRowMarginal
          w hw K halfExtent source
  then
    Q'.divPos
      (exactCenteredMehlerGramRowMass
        w hw K halfExtent diagonalOrder crossOrder source)
      (centralPhysicalRowMarginal
        w hw K halfExtent source)
      hpositive
  else 0

theorem exactCenteredMehlerGramRowRatio_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (source : EdgeLabelling) :
    (0 : Q') ≤
      exactCenteredMehlerGramRowRatio
        w hw K halfExtent diagonalOrder crossOrder source := by
  unfold exactCenteredMehlerGramRowRatio
  split
  next hpositive =>
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (exactCenteredMehlerGramRowMass_nonnegative
        w hw K halfExtent diagonalOrder crossOrder source)
      (Q'.le_of_lt
        (Q'.recipPos_pos _ hpositive))
  next _ =>
    exact Q'.le_refl' 0

/-! ## 3. Constructive maximum over the retained carrier -/

/-- Maximum of a rational function over a finite list, seeded at zero.
The seed makes the construction total without selecting a head. -/
def listQMaxZero {State : Type}
    (value : State → Q') : List State → Q'
  | [] => 0
  | state :: rest =>
      Q'.max' (value state)
        (listQMaxZero value rest)

theorem le_listQMaxZero_of_mem
    {State : Type} (value : State → Q') :
    ∀ (states : List State) {state : State},
      state ∈ states →
        value state ≤ listQMaxZero value states
  | [], _, hmember =>
      False.elim (List.not_mem_nil hmember)
  | head :: tail, state, hmember => by
      rcases List.mem_cons.mp hmember with hhead | htail
      · subst state
        exact Q'.le_max'_left _ _
      · exact Q'.le_trans' _ _ _
          (le_listQMaxZero_of_mem value tail htail)
          (Q'.le_max'_right _ _)

theorem listQMaxZero_nonnegative
    {State : Type}
    (value : State → Q')
    (hvalue : ∀ state, (0 : Q') ≤ value state) :
    ∀ states : List State,
      (0 : Q') ≤ listQMaxZero value states
  | [] => Q'.le_refl' 0
  | head :: _tail =>
      Q'.le_trans' _ _ _
        (hvalue head)
        (Q'.le_max'_left _ _)

/-- The exact finite centered Schur rate of the positive BF4 Mehler Gram
against the physical stationary marginal. -/
def exactCenteredMehlerGramRate
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) : Q' :=
  listQMaxZero
    (exactCenteredMehlerGramRowRatio
      w hw K halfExtent diagonalOrder crossOrder)
    (centralPositiveHalfStates w hw K halfExtent)

theorem exactCenteredMehlerGramRate_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) :
    (0 : Q') ≤
      exactCenteredMehlerGramRate
        w hw K halfExtent diagonalOrder crossOrder := by
  unfold exactCenteredMehlerGramRate
  exact listQMaxZero_nonnegative _
    (exactCenteredMehlerGramRowRatio_nonnegative
      w hw K halfExtent diagonalOrder crossOrder)
    (centralPositiveHalfStates
      w hw K halfExtent)

theorem exactCenteredMehlerGramRowMass_le_rate_mul_marginal
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder crossOrder : Nat}
    {source : EdgeLabelling}
    (hsource :
      source ∈
        centralPositiveHalfStates
          w hw K halfExtent) :
    exactCenteredMehlerGramRowMass
        w hw K halfExtent diagonalOrder crossOrder source ≤
      exactCenteredMehlerGramRate
          w hw K halfExtent diagonalOrder crossOrder *
        centralPhysicalRowMarginal
          w hw K halfExtent source := by
  have hpositive :
      (0 : Q') <
        centralPhysicalRowMarginal
          w hw K halfExtent source :=
    (mem_centralPositiveHalfStates_iff.mp hsource).2
  have hratio :
      exactCenteredMehlerGramRowRatio
          w hw K halfExtent diagonalOrder crossOrder source ≤
        exactCenteredMehlerGramRate
          w hw K halfExtent diagonalOrder crossOrder := by
    exact le_listQMaxZero_of_mem
      (exactCenteredMehlerGramRowRatio
        w hw K halfExtent diagonalOrder crossOrder)
      (centralPositiveHalfStates
        w hw K halfExtent)
      hsource
  unfold exactCenteredMehlerGramRowRatio at hratio
  rw [dif_pos hpositive] at hratio
  have hscaled :
      Q'.divPos
          (exactCenteredMehlerGramRowMass
            w hw K halfExtent diagonalOrder crossOrder source)
          (centralPhysicalRowMarginal
            w hw K halfExtent source)
          hpositive *
          centralPhysicalRowMarginal
            w hw K halfExtent source ≤
        exactCenteredMehlerGramRate
            w hw K halfExtent diagonalOrder crossOrder *
          centralPhysicalRowMarginal
            w hw K halfExtent source :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hratio (Q'.le_of_lt hpositive)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (Q'.divPos_mul_eqv
        (exactCenteredMehlerGramRowMass
          w hw K halfExtent diagonalOrder crossOrder source)
        (centralPhysicalRowMarginal
          w hw K halfExtent source)
        hpositive))
    hscaled

/-! ## 4. Mean-zero cancellation and the exact spectral datum -/

/-- The physical marginal vacuum joint has zero quadratic form on the exact
physical mean-zero carrier. -/
theorem centralPhysicalVacuumJoint_quadratic_meanZero
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        w hw K halfExtent observable) :
    finiteJointQuadratic
        (centralPositiveHalfStates
          w hw K halfExtent)
        observable
        (centralPhysicalVacuumJoint
          w hw K halfExtent) ≈
      0 := by
  unfold centralPhysicalVacuumJoint
  let states :=
    centralPositiveHalfStates
      w hw K halfExtent
  let marginal :=
    centralPhysicalRowMarginal
      w hw K halfExtent
  let pairing :=
    listQSum
      (fun state =>
        observable state * marginal state)
      states
  have hrankOne :
      finiteJointQuadratic states observable
          (fun left right =>
            marginal left * marginal right) ≈
        pairing * pairing :=
    finiteJointQuadratic_rankOne_eq_square
      states observable marginal
  have hpairing :
      pairing ≈ 0 := by
    refine Q'.eqv_trans _
      (centralPhysicalStationaryMean
        w hw K halfExtent observable) _ ?_ hmean
    unfold pairing marginal states
      centralPhysicalStationaryMean
    apply listQSum_congr
    intro state
    exact Q'.mul_comm_eqv _ _
  refine Q'.eqv_trans _
    (pairing * pairing) _ hrankOne ?_
  exact Q'.eqv_trans _
    ((0 : Q') * pairing) _
    (Q'.mul_eqv_congr_right
      pairing 0 pairing hpairing)
    (Q'.zero_mul_eqv pairing)

/-- Exact finite physical-mean-zero Rayleigh estimate for the normalized
positive BF4 Mehler Gram. -/
theorem normalizedBF4MehlerGramJoint_meanZero_quadratic
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder crossOrder : Nat}
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        w hw K halfExtent observable) :
    Q'.abs
        (finiteJointQuadratic
          (centralPositiveHalfStates
            w hw K halfExtent)
          observable
          (normalizedBF4MehlerGramJoint
            diagonalOrder crossOrder)) ≤
      exactCenteredMehlerGramRate
          w hw K halfExtent diagonalOrder crossOrder *
        centralPhysicalWeightedInner
          w hw K halfExtent observable observable := by
  let states :=
    centralPositiveHalfStates
      w hw K halfExtent
  let gram :=
    normalizedBF4MehlerGramJoint
      diagonalOrder crossOrder
  let vacuum :=
    centralPhysicalVacuumJoint
      w hw K halfExtent
  let gramQuadratic :=
    finiteJointQuadratic states observable gram
  let vacuumQuadratic :=
    finiteJointQuadratic states observable vacuum
  have hvacuum :
      vacuumQuadratic ≈ 0 :=
    centralPhysicalVacuumJoint_quadratic_meanZero
      observable hmean
  have hdifference :
      gramQuadratic + (-vacuumQuadratic) ≈
        gramQuadratic := by
    exact Q'.eqv_trans _
      (gramQuadratic + 0) _
      (Q'.add_eqv_congr_left
        gramQuadratic (-vacuumQuadratic) 0
        (Q'.eqv_trans _ (-0) _
          (Q'.neg_eqv_congr _ _ hvacuum)
          (Q'.eqv_refl 0)))
      (Q'.eqv_of_eq
        (Q'.add_zero' gramQuadratic))
  have hperturbation :
      Q'.abs
          (gramQuadratic + (-vacuumQuadratic)) ≤
        exactCenteredMehlerGramRate
            w hw K halfExtent diagonalOrder crossOrder *
          finiteWeightedSquare
            states
            (centralPhysicalRowMarginal
              w hw K halfExtent)
            observable :=
    finiteJointQuadratic_abs_sub_le_weightedSquare
      states observable
      (centralPhysicalRowMarginal
        w hw K halfExtent)
      gram vacuum
      (exactCenteredMehlerGramRate
        w hw K halfExtent diagonalOrder crossOrder)
      (fun left right _ _ =>
        normalizedBF4MehlerGramJoint_symmetric
          diagonalOrder crossOrder left right)
      (fun left right _ _ =>
        centralPhysicalVacuumJoint_symmetric
          w hw K halfExtent left right)
      (fun state hstate =>
        exactCenteredMehlerGramRowMass_le_rate_mul_marginal
          hstate)
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (Q'.abs_eqv_congr hdifference))
    (Q'.le_trans' _ _ _ hperturbation ?_)
  exact Q'.le_of_eqv
    (Q'.mul_eqv_congr_left
      (exactCenteredMehlerGramRate
        w hw K halfExtent diagonalOrder crossOrder)
      (finiteWeightedSquare
        states
        (centralPhysicalRowMarginal
          w hw K halfExtent)
        observable)
      (centralPhysicalWeightedInner
        w hw K halfExtent observable observable)
      (finiteWeightedSquare_physical_eqv_inner
        w hw K halfExtent observable))

/-- Canonical, fully executable fixed-scale spectral datum for the positive
BF4 feature-word Gram. -/
def exactCenteredMehlerGramSpectralData
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) :
    MehlerGramEndpointSpectralData
      w hw K halfExtent diagonalOrder crossOrder where
  rate :=
    exactCenteredMehlerGramRate
      w hw K halfExtent diagonalOrder crossOrder
  rate_nonnegative :=
    exactCenteredMehlerGramRate_nonnegative
      w hw K halfExtent diagonalOrder crossOrder
  normalized_meanZero_quadratic :=
    normalizedBF4MehlerGramJoint_meanZero_quadratic

/-! ## 5. Exact fixed-scale physical comparison -/

/-- The canonical raw positive-Gram endpoint with the exact centered rate. -/
def exactCenteredMehlerGramRawEndpoint
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) :
    CentralPhysicalRawMehlerEndpoint
      w hw K halfExtent :=
  (exactCenteredMehlerGramSpectralData
    w hw K halfExtent diagonalOrder crossOrder).toRawEndpoint

/-- The complete exact numerator/partition/marginal budget for the centered
positive-Gram endpoint at one physical scale. -/
def exactCenteredMehlerGramFiniteBudgetData
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) :
    ExactFiniteBudgetData
      (exactCenteredMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder crossOrder) :=
  exactFiniteBudgetData
    (exactCenteredMehlerGramRawEndpoint
      w hw K halfExtent diagonalOrder crossOrder)

/-- Fixed-scale physical quarter theorem with no open finite-dimensional
data.  Its sole premise is the displayed exact rational quarter test. -/
theorem exactCenteredMehlerGram_physical_quadratic_abs_le_quarter
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder crossOrder : Nat}
    (hquarter :
      (exactCenteredMehlerGramRawEndpoint
          w hw K halfExtent diagonalOrder crossOrder).rate +
          exactFiniteEpsilon
            (exactCenteredMehlerGramRawEndpoint
              w hw K halfExtent diagonalOrder crossOrder) ≤
        Q'.mkPos 1 4 (by decide))
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        w hw K halfExtent observable) :
    Q'.abs
        (centralPhysicalWeightedInner
          w hw K halfExtent
          observable
          (centralPhysicalMarkovApply
            w hw K halfExtent observable)) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          w hw K halfExtent observable observable := by
  exact
    exactFinite_physical_markov_quadratic_abs_le_quarter
      (exactCenteredMehlerGramRawEndpoint
        w hw K halfExtent diagonalOrder crossOrder)
      hquarter observable hmean

/-! ## 6. Matched AF specialization -/

/-- The exact centered positive-Gram spectral datum on the literal matched
BF4 coordinates at one scale. -/
def matchedExactCenteredMehlerGramSpectralAt
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) :
    MehlerGramEndpointSpectralData
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale)
      (diagonalOrder scale)
      (crossOrder scale) :=
  exactCenteredMehlerGramSpectralData
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative
      family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)
    (diagonalOrder scale)
    (crossOrder scale)

/-- Named raw endpoint specialization.  Keeping the expanded dependent
physical carrier behind this definition prevents repeated elaboration of the
centered rate in AF-family record fields. -/
def matchedExactCenteredMehlerGramRawEndpointAt
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) :
    CentralPhysicalRawMehlerEndpoint
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale) :=
  (matchedExactCenteredMehlerGramSpectralAt
    family coupling halfExtent
    diagonalOrder crossOrder scale).toRawEndpoint

/-- The exact finite comparison data on the literal matched BF4 coordinates
at one scale.  Its epsilon is allowed to vary with scale; proving a common
small AF envelope is the remaining analytic theorem. -/
def matchedExactCenteredMehlerGramFiniteBudgetAt
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) :
    ExactFiniteBudgetData
      (matchedExactCenteredMehlerGramRawEndpointAt
        family coupling halfExtent
        diagonalOrder crossOrder scale) :=
  exactFiniteBudgetData
    (matchedExactCenteredMehlerGramRawEndpointAt
      family coupling halfExtent
      diagonalOrder crossOrder scale)

/-- The single exact rational whose spacing-uniform quarter bound remains to
be proved on the matched physical trajectory. -/
def matchedExactCenteredMehlerGramQuarterCostAt
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) : Q' :=
  let endpoint :=
    matchedExactCenteredMehlerGramRawEndpointAt
      family coupling halfExtent
      diagonalOrder crossOrder scale
  endpoint.rate + exactFiniteEpsilon endpoint

/-- Once the exact matched cost is below one quarter, the physical BF4
quadratic has the required quarter contraction at that scale. -/
theorem matchedExactCenteredMehlerGram_physical_quarter_at
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat)
    (hquarter :
      matchedExactCenteredMehlerGramQuarterCostAt
          family coupling halfExtent
          diagonalOrder crossOrder scale ≤
        Q'.mkPos 1 4 (by decide))
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        observable) :
    Q'.abs
        (centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)
            observable)) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable observable := by
  exact
    exactCenteredMehlerGram_physical_quadratic_abs_le_quarter
      hquarter observable hmean

end YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget

#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.normalizedBF4MehlerGramJoint_symmetric
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGramRowMass_nonnegative
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGramRowRatio_nonnegative
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.le_listQMaxZero_of_mem
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.listQMaxZero_nonnegative
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGramRate_nonnegative
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGramRowMass_le_rate_mul_marginal
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.centralPhysicalVacuumJoint_quadratic_meanZero
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.normalizedBF4MehlerGramJoint_meanZero_quadratic
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGramSpectralData
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGramRawEndpoint
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGramFiniteBudgetData
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGram_physical_quadratic_abs_le_quarter
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.matchedExactCenteredMehlerGramSpectralAt
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.matchedExactCenteredMehlerGramRawEndpointAt
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.matchedExactCenteredMehlerGramFiniteBudgetAt
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.matchedExactCenteredMehlerGram_physical_quarter_at
