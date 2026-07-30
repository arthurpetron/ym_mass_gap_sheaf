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

/-- Vacuum normalization of the displayed Gram is literal: its
vacuum--vacuum entry is one at every truncation order.  This is useful for
the positive-semidefinite normalization, but it also imposes a necessary
condition on any row-relative comparison with the probability-normalized
physical Choi joint; see `quarterCost_forces_vacuumMarginal_gt_half`
below. -/
theorem normalizedBF4MehlerGramJoint_vacuum
    (diagonalOrder crossOrder : Nat) :
    normalizedBF4MehlerGramJoint
        diagonalOrder crossOrder
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling ≈
      1 := by
  unfold normalizedBF4MehlerGramJoint
    bf4MehlerGramVacuumPartition
    SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
    Q'.divPos
  exact Q'.mul_recipPos_eqv _
    (bf4MehlerGramVacuumPartition_pos
      (shiftedDiagonalVacuumCertificate diagonalOrder)
      crossOrder)

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

private theorem listQSum_member_le_nonnegative_local
    {State : Type}
    (value : State → Q')
    (hvalue : ∀ state, (0 : Q') ≤ value state) :
    ∀ (states : List State) {state : State},
      state ∈ states →
        value state ≤ listQSum value states
  | [], _, hmember =>
      False.elim (List.not_mem_nil hmember)
  | head :: tail, state, hmember => by
      rcases List.mem_cons.mp hmember with hhead | htail
      · subst state
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun item _ => hvalue item))
      · have hinduction :=
          listQSum_member_le_nonnegative_local
            value hvalue tail htail
        have htailLe :
            listQSum value tail ≤
              value head + listQSum value tail := by
          exact Q'.le_trans' _
            (listQSum value tail + value head) _
            (Q'.add_le_self_of_nonneg
              (listQSum value tail)
              (value head) (hvalue head))
            (Q'.le_of_eqv
              (Q'.add_comm_eqv
                (listQSum value tail)
                (value head)))
        exact Q'.le_trans' _ _ _ hinduction htailLe

/-- Every retained physical row marginal is at most one. -/
theorem centralPhysicalRowMarginal_le_one_on_carrier
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K halfExtent) :
    centralPhysicalRowMarginal
        w hw K halfExtent source ≤
      1 := by
  have hmember :
      centralPhysicalRowMarginal
          w hw K halfExtent source ≤
        listQSum
          (centralPhysicalRowMarginal
            w hw K halfExtent)
          (centralPositiveHalfStates
            w hw K halfExtent) :=
    listQSum_member_le_nonnegative_local
      (centralPhysicalRowMarginal
        w hw K halfExtent)
      (fun state =>
        centralPhysicalRowMarginal_nonnegative
          hw K halfExtent state)
      (centralPositiveHalfStates
        w hw K halfExtent)
      hsource
  exact Q'.le_trans' _ _ _ hmember
    (Q'.le_of_eqv
      (centralPositiveRowMarginal_total_one
        w hw K halfExtent))

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

/-- The vacuum-normalized Gram forces a scale-independent lower constraint
on its centered rate.  Writing `pi0` for the physical vacuum row marginal,

`1 - pi0^2 <= r_cen * pi0`.

The inequality uses only the vacuum target term in the exact absolute row
mass. -/
theorem one_sub_vacuumMarginal_square_le_centeredRate_mul
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) :
    let pi0 :=
      centralPhysicalRowMarginal
        w hw K halfExtent
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
    1 + (-(pi0 * pi0)) ≤
      exactCenteredMehlerGramRate
          w hw K halfExtent diagonalOrder crossOrder *
        pi0 := by
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
  let states :=
    centralPositiveHalfStates
      w hw K halfExtent
  let gram :=
    normalizedBF4MehlerGramJoint
      diagonalOrder crossOrder
  let vacuum :=
    centralPhysicalVacuumJoint
      w hw K halfExtent
  have hvacuumMemberRaw :
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling ∈
        centralPositiveHalfStates
          w hw K halfExtent :=
    zeroEdgeLabelling_mem_centralPositiveHalfStates
      hw K halfExtent
  have hvacuumMember :
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling ∈
        states :=
    by simpa only [states] using hvacuumMemberRaw
  have hentryEqv :
      gram
          SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
          SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling +
          (-vacuum
            SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
            SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling) ≈
        1 + (-(pi0 * pi0)) := by
    exact Q'.add_eqv_congr'
      (normalizedBF4MehlerGramJoint_vacuum
        diagonalOrder crossOrder)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_refl _))
  have hentry :
      1 + (-(pi0 * pi0)) ≤
        Q'.abs
          (gram
              SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
              SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling +
            (-vacuum
              SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
              SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling)) := by
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hentryEqv)
      (Q'.le_abs_self _)
  have hrow :
      Q'.abs
          (gram
              SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
              SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling +
            (-vacuum
              SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
              SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling)) ≤
        exactCenteredMehlerGramRowMass
          w hw K halfExtent diagonalOrder crossOrder
          SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling := by
    unfold exactCenteredMehlerGramRowMass
      finiteJointDifferenceAbsRowMass
    exact listQSum_member_le_nonnegative_local
      (fun target =>
        Q'.abs
          (gram
              SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
              target +
            (-vacuum
              SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
              target)))
      (fun target => Q'.abs_nonneg _)
      states hvacuumMember
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ hentry hrow)
    (exactCenteredMehlerGramRowMass_le_rate_mul_marginal
      hvacuumMember)

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

/-- A quarter bound for the vacuum-normalized Gram is possible only if the
physical vacuum row carries more than half of the entire stationary mass.

This is a normalization fence, not a statement about the Yang--Mills gap.
It follows before using the finite comparison tolerance: the exact centered
Gram rate alone contains the vacuum mismatch
`1 - pi0^2`.  Thus no choice of diagonal or cross truncation order can prove
the displayed quarter estimate at a scale where `pi0 <= 1/2`. -/
theorem exactCenteredMehlerGramQuarterCost_forces_vacuumMarginal_gt_half
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (hquarter :
      (exactCenteredMehlerGramRawEndpoint
          w hw K halfExtent diagonalOrder crossOrder).rate +
          exactFiniteEpsilon
            (exactCenteredMehlerGramRawEndpoint
              w hw K halfExtent diagonalOrder crossOrder) ≤
        Q'.mkPos 1 4 (by decide)) :
    Q'.mkPos 1 2 (by decide) <
      centralPhysicalRowMarginal
        w hw K halfExtent
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling := by
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
  let rate :=
    exactCenteredMehlerGramRate
      w hw K halfExtent diagonalOrder crossOrder
  let endpoint :=
    exactCenteredMehlerGramRawEndpoint
      w hw K halfExtent diagonalOrder crossOrder
  have hpi0nonnegative : (0 : Q') ≤ pi0 :=
    centralPhysicalRowMarginal_nonnegative
      hw K halfExtent
      SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling
  have hepsilon :
      (0 : Q') ≤ exactFiniteEpsilon endpoint :=
    exactFiniteEpsilon_nonnegative endpoint
  have hrateLe :
      rate ≤ Q'.mkPos 1 4 (by decide) := by
    have hrateToSum :
        endpoint.rate ≤
          endpoint.rate + exactFiniteEpsilon endpoint :=
      Q'.add_le_self_of_nonneg
        endpoint.rate (exactFiniteEpsilon endpoint)
        hepsilon
    have hraw :
        endpoint.rate ≤ Q'.mkPos 1 4 (by decide) :=
      Q'.le_trans' _ _ _ hrateToSum hquarter
    exact hraw
  have hnecessary :
      1 + (-(pi0 * pi0)) ≤
        Q'.mkPos 1 4 (by decide) * pi0 := by
    exact Q'.le_trans' _ _ _
      (one_sub_vacuumMarginal_square_le_centeredRate_mul
        w hw K halfExtent diagonalOrder crossOrder)
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        hrateLe hpi0nonnegative)
  have hnot :
      ¬
        pi0 ≤ Q'.mkPos 1 2 (by decide) := by
    intro hpi0half
    have hhalfNonnegative :
        (0 : Q') ≤ Q'.mkPos 1 2 (by decide) := by
      decide
    have hquarterNonnegative :
        (0 : Q') ≤ Q'.mkPos 1 4 (by decide) := by
      decide
    have hsquare :
        pi0 * pi0 ≤
          Q'.mkPos 1 2 (by decide) *
            Q'.mkPos 1 2 (by decide) :=
      Q'.mul_le_mul_of_nonneg
        hpi0half hpi0half
        hhalfNonnegative hpi0nonnegative
    have hquarterPi :
        Q'.mkPos 1 4 (by decide) * pi0 ≤
          Q'.mkPos 1 4 (by decide) *
            Q'.mkPos 1 2 (by decide) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        hpi0half hquarterNonnegative
    have hadded :=
      Q'.add_le_add_right
        (1 + (-(pi0 * pi0)))
        (Q'.mkPos 1 4 (by decide) * pi0)
        (pi0 * pi0)
        hnecessary
    have hleft :
        (1 + (-(pi0 * pi0))) + pi0 * pi0 ≈
          1 := by
      exact Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv
          1 (-(pi0 * pi0)) (pi0 * pi0))
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left
            1 ((-(pi0 * pi0)) + pi0 * pi0) 0
            (Q'.neg_add_self_eqv (pi0 * pi0)))
          (Q'.eqv_of_eq (Q'.add_zero' 1)))
    have hone :
        (1 : Q') ≤
          Q'.mkPos 1 4 (by decide) * pi0 +
            pi0 * pi0 :=
      Q'.le_trans' _ _ _
        (Q'.ge_of_eqv hleft) hadded
    have hupper :
        Q'.mkPos 1 4 (by decide) * pi0 +
              pi0 * pi0 ≤
          Q'.mkPos 1 4 (by decide) *
              Q'.mkPos 1 2 (by decide) +
            Q'.mkPos 1 2 (by decide) *
              Q'.mkPos 1 2 (by decide) :=
      Q'.add_le_add hquarterPi hsquare
    have himpossible :
        (1 : Q') ≤ Q'.mkPos 3 8 (by decide) :=
      Q'.le_trans' _ _ _
        (Q'.le_trans' _ _ _ hone hupper)
        (Q'.le_of_eqv (by decide))
    exact
      (by decide :
        ¬ ((1 : Q') ≤ Q'.mkPos 3 8 (by decide)))
      himpossible
  show
    Q'.mkPos 1 2 (by decide) < pi0
  exact Int.lt_of_not_ge hnot

/-- Contrapositive normalization fence: at any fixed scale with physical
vacuum marginal at most one half, the present vacuum-normalized exact Gram
cost cannot satisfy the quarter premise, regardless of truncation orders. -/
theorem exactCenteredMehlerGramQuarterCost_impossible_of_vacuumMarginal_le_half
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (hvacuum :
      centralPhysicalRowMarginal
          w hw K halfExtent
          SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling ≤
        Q'.mkPos 1 2 (by decide)) :
    ¬
      ((exactCenteredMehlerGramRawEndpoint
          w hw K halfExtent diagonalOrder crossOrder).rate +
          exactFiniteEpsilon
            (exactCenteredMehlerGramRawEndpoint
              w hw K halfExtent diagonalOrder crossOrder) ≤
        Q'.mkPos 1 4 (by decide)) := by
  intro hquarter
  have hstrict :=
    exactCenteredMehlerGramQuarterCost_forces_vacuumMarginal_gt_half
      w hw K halfExtent diagonalOrder crossOrder hquarter
  exact (Int.not_lt_of_ge hvacuum) hstrict

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

/-- The requested matched quarter estimate has a concrete necessary
condition at every AF scale: the exact physical vacuum row marginal must
exceed one half.  Neither `CubicMarginLaw` nor `PhysicalSpacingEnvelope`
contains such a marginal statement. -/
theorem matchedExactCenteredMehlerGramQuarterCostAt_forces_vacuumMarginal_gt_half
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat)
    (hquarter :
      matchedExactCenteredMehlerGramQuarterCostAt
          family coupling halfExtent
          diagonalOrder crossOrder scale ≤
        Q'.mkPos 1 4 (by decide)) :
    Q'.mkPos 1 2 (by decide) <
      centralPhysicalRowMarginal
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling := by
  apply
    exactCenteredMehlerGramQuarterCost_forces_vacuumMarginal_gt_half
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale)
      (diagonalOrder scale)
      (crossOrder scale)
  exact hquarter

/-- A single matched scale with vacuum marginal at most one half refutes the
spacing-uniform quarter statement for the current vacuum-normalized cost. -/
theorem matchedExactCenteredMehlerGramQuarterCostAt_impossible_of_vacuumMarginal_le_half
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat)
    (hvacuum :
      centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling ≤
        Q'.mkPos 1 2 (by decide)) :
    ¬
      (matchedExactCenteredMehlerGramQuarterCostAt
          family coupling halfExtent
          diagonalOrder crossOrder scale ≤
        Q'.mkPos 1 4 (by decide)) := by
  intro hquarter
  have hstrict :=
    matchedExactCenteredMehlerGramQuarterCostAt_forces_vacuumMarginal_gt_half
      family coupling halfExtent diagonalOrder crossOrder scale hquarter
  exact (Int.not_lt_of_ge hvacuum) hstrict

/-- Uniform form of the normalization fence.  The requested all-scale
quarter estimate for the uncalibrated cost would force the physical vacuum
row to carry more than half of the stationary probability at every scale. -/
theorem matchedExactCenteredMehlerGramQuarterCostAt_uniform_forces_vacuumMarginal_gt_half
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (hquarter :
      ∀ scale,
        matchedExactCenteredMehlerGramQuarterCostAt
            family coupling halfExtent
            diagonalOrder crossOrder scale ≤
          Q'.mkPos 1 4 (by decide)) :
    ∀ scale,
      Q'.mkPos 1 2 (by decide) <
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          SU2FiniteTrivalentPacketGraphActualOperator.zeroEdgeLabelling := by
  intro scale
  exact
    matchedExactCenteredMehlerGramQuarterCostAt_forces_vacuumMarginal_gt_half
      family coupling halfExtent diagonalOrder crossOrder
      scale (hquarter scale)

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
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.normalizedBF4MehlerGramJoint_vacuum
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGramRowMass_nonnegative
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGramRowRatio_nonnegative
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.le_listQMaxZero_of_mem
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.listQMaxZero_nonnegative
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGramRate_nonnegative
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.centralPhysicalRowMarginal_le_one_on_carrier
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGramRowMass_le_rate_mul_marginal
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.one_sub_vacuumMarginal_square_le_centeredRate_mul
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.centralPhysicalVacuumJoint_quadratic_meanZero
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.normalizedBF4MehlerGramJoint_meanZero_quadratic
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGramSpectralData
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGramRawEndpoint
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGramFiniteBudgetData
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGramQuarterCost_forces_vacuumMarginal_gt_half
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGramQuarterCost_impossible_of_vacuumMarginal_le_half
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.exactCenteredMehlerGram_physical_quadratic_abs_le_quarter
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.matchedExactCenteredMehlerGramSpectralAt
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.matchedExactCenteredMehlerGramRawEndpointAt
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.matchedExactCenteredMehlerGramFiniteBudgetAt
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.matchedExactCenteredMehlerGramQuarterCostAt_forces_vacuumMarginal_gt_half
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.matchedExactCenteredMehlerGramQuarterCostAt_impossible_of_vacuumMarginal_le_half
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.matchedExactCenteredMehlerGramQuarterCostAt_uniform_forces_vacuumMarginal_gt_half
#print axioms YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget.matchedExactCenteredMehlerGram_physical_quarter_at
