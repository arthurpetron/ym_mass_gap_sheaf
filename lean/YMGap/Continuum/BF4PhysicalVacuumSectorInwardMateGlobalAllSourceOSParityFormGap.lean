/-
# The inward-mate parity demand gives a strict physical transfer form

The global inward-mate flow supplies an explicit positive Dirichlet-energy
floor for the Boolean central-face parity observable at every cutoff `K >= 1`.
This module centers that same observable by the genuine stationary marginal
and converts the floor into a strict Rayleigh bound for the literal reversible
BF4 conditional operator.

The proof has four exact steps.

* subtracting a constant leaves directed Dirichlet energy unchanged;
* deleting zero-marginal rows leaves that energy unchanged;
* the symmetric-joint identity identifies half the energy with
  `<f,f> - <f,Tf>` on the retained physical carrier; and
* Boolean parity has stationary square norm at most one.

Thus the absolute energy floor becomes a relative positive margin for this
one centered observable.  This is not an all-observable Poincare inequality,
a vacuum-complement operator norm, a thermodynamic/continuum limit, or a Clay
mass-gap theorem.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCoercivity

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFormGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalMarkovTransferLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCoercivity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityDemand
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFraction
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Two exact Dirichlet recodings -/

/-- A constant shift cancels on every directed edge. -/
theorem finiteJointDirichletEnergy_add_neg_constant_eqv
    {State : Type} (states : List State) (coefficient : State -> Q')
    (constant : Q') (joint : State -> State -> Q') :
    finiteJointDirichletEnergy states
        (fun state => coefficient state + (-constant)) joint ≈
      finiteJointDirichletEnergy states coefficient joint := by
  unfold finiteJointDirichletEnergy
  apply listQSum_congr_on
  intro left _hleft
  apply listQSum_congr_on
  intro right _hright
  let leftDifference :=
    (coefficient left + -constant) +
      -(coefficient right + -constant)
  let rightDifference := coefficient left + -coefficient right
  have hneg : -(coefficient right + -constant) ≈
      -coefficient right + -(-constant) :=
    Q'.neg_add_eqv _ _
  have hnegneg : -(-constant) ≈ constant := Q'.neg_neg_eqv constant
  have hdiff : leftDifference ≈ rightDifference := by
    refine Q'.eqv_trans _
      ((coefficient left + -constant) +
        (-coefficient right + -(-constant))) _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hneg) ?_
    refine Q'.eqv_trans _
      ((coefficient left + -constant) +
        (-coefficient right + constant)) _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) hnegneg)) ?_
    refine Q'.eqv_trans _
      (coefficient left + (-constant + (-coefficient right + constant))) _
      (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      (coefficient left + ((-coefficient right + -constant) + constant)) _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _
          ((-constant + -coefficient right) + constant) _
          (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
          (Q'.add_eqv_congr_right _ _ constant
            (Q'.add_comm_eqv (-constant) (-coefficient right))))) ?_
    refine Q'.eqv_trans _
      (coefficient left + (-coefficient right + 0)) _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ (-coefficient right + (-constant + constant)) _
          (Q'.add_assoc_eqv _ _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _)
            (Q'.neg_add_self_eqv constant)))) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_of_eq (Q'.add_zero' (-coefficient right)))
  have hsquare : leftDifference * leftDifference ≈
      rightDifference * rightDifference := by
    exact Q'.eqv_trans _ (rightDifference * leftDifference) _
      (Q'.mul_eqv_congr_right _ _ leftDifference hdiff)
      (Q'.mul_eqv_congr_left rightDifference _ _ hdiff)
  exact Q'.mul_eqv_congr_left (joint left right) _ _ hsquare

private theorem listQSum_filter_eq_of_zero_local
    {A : Type} (value : A -> Q') (predicate : A -> Bool) :
    forall items : List A,
      (forall item, item ∈ items -> predicate item = false ->
        value item ≈ 0) ->
      listQSum value (items.filter predicate) ≈ listQSum value items
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      cases hp : predicate head with
      | false =>
          simp only [List.filter_cons, hp, Bool.false_eq_true,
            if_false, listQSum]
          have hhead := hzero head List.mem_cons_self hp
          have htail := listQSum_filter_eq_of_zero_local value predicate tail
            (fun item hitem => hzero item (List.mem_cons_of_mem head hitem))
          exact Q'.eqv_trans _ (listQSum value tail) _ htail
            (Q'.eqv_trans _ (0 + listQSum value tail) _
              (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _)))
              (Q'.add_eqv_congr' (Q'.eqv_symm hhead) (Q'.eqv_refl _)))
      | true =>
          simp only [List.filter_cons, hp, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_filter_eq_of_zero_local value predicate tail
              (fun item hitem => hzero item
                (List.mem_cons_of_mem head hitem)))

private theorem listQSum_eqv_zero_of_all_local
    {A : Type} (value : A -> Q') : forall items : List A,
    (forall item, item ∈ items -> value item ≈ 0) ->
      listQSum value items ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (hzero head List.mem_cons_self)
          (listQSum_eqv_zero_of_all_local value tail
            (fun item hitem => hzero item
              (List.mem_cons_of_mem head hitem))))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

/-- Removing precisely the zero-marginal rows and columns preserves the
directed energy of every observable. -/
theorem centralPhysicalPositiveDirichlet_eqv_full
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling -> Q') :
    finiteJointDirichletEnergy
        (centralPositiveHalfStates w hw K half) observable
        (centralNormalizedPhysicalReflectedKernel w hw K half) ≈
      finiteJointDirichletEnergy
        (centralHalfStates K half) observable
        (centralNormalizedPhysicalReflectedKernel w hw K half) := by
  let states := centralHalfStates K half
  let positivePredicate : EdgeLabelling -> Bool := fun state =>
    decide ((0 : Q') < centralPhysicalRowMarginal w hw K half state)
  let term : EdgeLabelling -> EdgeLabelling -> Q' := fun left right =>
    centralNormalizedPhysicalReflectedKernel w hw K half left right *
      ((observable left + -observable right) *
        (observable left + -observable right))
  have hinner : forall left, left ∈ states ->
      listQSum (term left) (states.filter positivePredicate) ≈
        listQSum (term left) states := by
    intro left hleft
    apply listQSum_filter_eq_of_zero_local
    intro right hright hfalse
    have hnot : ¬ (0 : Q') <
        centralPhysicalRowMarginal w hw K half right := by
      simpa only [positivePredicate, decide_eq_false_iff_not] using hfalse
    have hentry :
        centralNormalizedPhysicalReflectedKernel w hw K half left right ≈
          0 :=
      centralNormalizedPhysicalReflectedKernel_eqv_zero_of_target_not_pos
        hleft hright hnot
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hentry)
      (Q'.zero_mul_eqv _)
  have hfiltered :
      listQSum
          (fun left => listQSum (term left)
            (states.filter positivePredicate))
          (states.filter positivePredicate) ≈
        listQSum (fun left => listQSum (term left) states) states := by
    refine Q'.eqv_trans _
      (listQSum (fun left => listQSum (term left) states)
        (states.filter positivePredicate)) _ ?_ ?_
    · apply listQSum_congr_on
      intro left hleft
      exact hinner left (List.mem_filter.mp hleft).1
    · apply listQSum_filter_eq_of_zero_local
      intro left hleft hfalse
      have hnot : ¬ (0 : Q') <
          centralPhysicalRowMarginal w hw K half left := by
        simpa only [positivePredicate, decide_eq_false_iff_not] using hfalse
      apply listQSum_eqv_zero_of_all_local
      intro right hright
      have hentry :
          centralNormalizedPhysicalReflectedKernel w hw K half left right ≈
            0 :=
        centralNormalizedPhysicalReflectedKernel_eqv_zero_of_row_not_pos
          hright hnot
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hentry)
        (Q'.zero_mul_eqv _)
  unfold finiteJointDirichletEnergy centralPositiveHalfStates
  change
    listQSum
        (fun left => listQSum (term left)
          (states.filter positivePredicate))
        (states.filter positivePredicate) ≈
      listQSum (fun left => listQSum (term left) states) states
  exact hfiltered

/-! ## 2. Center the Boolean parity observable -/

/-- The central-face parity after subtracting its genuine stationary mean. -/
def globalInwardMateCenteredParity (K : Nat) : EdgeLabelling -> Q' :=
  centralPhysicalCenteredObservable anchorCoupling (by decide) K 0
    centralFaceZeroParityCoefficient

theorem globalInwardMateCenteredParity_meanZero (K : Nat) :
    CentralPhysicalMeanZero anchorCoupling (by decide) K 0
      (globalInwardMateCenteredParity K) := by
  exact centralPhysicalCenteredObservable_meanZero
    anchorCoupling (by decide) K 0 centralFaceZeroParityCoefficient

/-- The global path lower bound survives both exact centering and removal of
zero-marginal rows. -/
theorem globalInwardMateParityDirichletFloor_le_positive_centered
    (K : Nat) (hK : 1 <= K) :
    globalInwardMateParityDirichletFloor ≤
      finiteJointDirichletEnergy
        (centralPositiveHalfStates anchorCoupling (by decide) K 0)
        (globalInwardMateCenteredParity K)
        (centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0) := by
  let mean := centralPhysicalStationaryMean
    anchorCoupling (by decide) K 0 centralFaceZeroParityCoefficient
  have hfloor := globalInwardMateParityDirichletFloor_le K hK
  have hshift :
      finiteJointDirichletEnergy (centralHalfStates K 0)
          (globalInwardMateCenteredParity K)
          (centralNormalizedPhysicalReflectedKernel
            anchorCoupling (by decide) K 0) ≈
        finiteJointDirichletEnergy (centralHalfStates K 0)
          centralFaceZeroParityCoefficient
          (centralNormalizedPhysicalReflectedKernel
            anchorCoupling (by decide) K 0) := by
    unfold globalInwardMateCenteredParity
      centralPhysicalCenteredObservable
    exact finiteJointDirichletEnergy_add_neg_constant_eqv
      (centralHalfStates K 0) centralFaceZeroParityCoefficient mean
      (centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0)
  have hfilter := centralPhysicalPositiveDirichlet_eqv_full
    anchorCoupling (by decide) K 0 (globalInwardMateCenteredParity K)
  exact Q'.le_trans' _ _ _ hfloor
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hshift) (Q'.ge_of_eqv hfilter))

/-- Half of that retained centered energy is exactly the deficit of the
literal physical conditional transfer form. -/
theorem half_mul_globalInwardMateCenteredParityDirichlet_eqv_deficit
    (K : Nat) :
    Q'.mkPos 1 2 (by decide) *
        finiteJointDirichletEnergy
          (centralPositiveHalfStates anchorCoupling (by decide) K 0)
          (globalInwardMateCenteredParity K)
          (centralNormalizedPhysicalReflectedKernel
            anchorCoupling (by decide) K 0) ≈
      centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          (globalInwardMateCenteredParity K)
          (globalInwardMateCenteredParity K) +
        -(centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          (globalInwardMateCenteredParity K)
          (centralPhysicalMarkovApply anchorCoupling (by decide) K 0
            (globalInwardMateCenteredParity K))) := by
  let states := centralPositiveHalfStates anchorCoupling (by decide) K 0
  let weight := centralPhysicalRowMarginal anchorCoupling (by decide) K 0
  let centered := globalInwardMateCenteredParity K
  let joint := centralNormalizedPhysicalReflectedKernel
    anchorCoupling (by decide) K 0
  have hgeneric := half_mul_finiteJointDirichletEnergy_eqv_deficit
    states weight centered joint
    (fun state hstate => centralPhysicalJoint_row_eq_marginal hstate)
    (fun left hleft right hright =>
      centralNormalizedPhysicalReflectedKernel_symm
        ((mem_centralPositiveHalfStates_iff.mp hleft).1)
        ((mem_centralPositiveHalfStates_iff.mp hright).1))
  have hdiag := finiteWeightedSquare_physical_eqv_inner
    anchorCoupling (by decide) K 0 centered
  have hmatrix := centralPhysicalWeightedMarkovQuadratic_eq_joint
    anchorCoupling (by decide) K 0 centered
  exact Q'.eqv_trans _ _ _ hgeneric
    (Q'.add_eqv_congr' hdiag
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hmatrix)))

/-! ## 3. Normalize the absolute floor into a relative strict margin -/

theorem centralFaceZeroParityCoefficient_square_le_one
    (state : EdgeLabelling) :
    centralFaceZeroParityCoefficient state *
        centralFaceZeroParityCoefficient state ≤ (1 : Q') := by
  by_cases hzero : state 0 % 2 = 0
  · unfold centralFaceZeroParityCoefficient
    rw [hzero]
    decide
  · have hlt : state 0 % 2 < 2 := Nat.mod_lt _ (by decide)
    have hone : state 0 % 2 = 1 := by omega
    unfold centralFaceZeroParityCoefficient
    rw [hone]
    decide

theorem centralFaceZeroParityWeightedSquare_le_one (K : Nat) :
    centralPhysicalWeightedInner anchorCoupling (by decide) K 0
        centralFaceZeroParityCoefficient
        centralFaceZeroParityCoefficient ≤ (1 : Q') := by
  let states := centralPositiveHalfStates anchorCoupling (by decide) K 0
  let weight := centralPhysicalRowMarginal anchorCoupling (by decide) K 0
  have hsum :
      listQSum
          (fun state => weight state *
            (centralFaceZeroParityCoefficient state *
              centralFaceZeroParityCoefficient state)) states ≤
        listQSum weight states := by
    apply listQSum_mono
    intro state _hstate
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (weight state)
        (centralFaceZeroParityCoefficient_square_le_one state)
        (centralPhysicalRowMarginal_nonnegative
          (by decide) K 0 state))
      (Q'.le_of_eqv (Q'.mul_one_eqv (weight state)))
  unfold centralPhysicalWeightedInner
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (centralPositiveRowMarginal_total_one
        anchorCoupling (by decide) K 0))

theorem globalInwardMateCenteredParityWeightedSquare_le_raw (K : Nat) :
    centralPhysicalWeightedInner anchorCoupling (by decide) K 0
        (globalInwardMateCenteredParity K)
        (globalInwardMateCenteredParity K) ≤
      centralPhysicalWeightedInner anchorCoupling (by decide) K 0
        centralFaceZeroParityCoefficient
        centralFaceZeroParityCoefficient := by
  let raw := centralPhysicalWeightedInner anchorCoupling (by decide) K 0
    centralFaceZeroParityCoefficient centralFaceZeroParityCoefficient
  let mean := centralPhysicalStationaryMean anchorCoupling (by decide) K 0
    centralFaceZeroParityCoefficient
  have hidentity := centralPhysicalCenteredObservable_norm_identity
    anchorCoupling (by decide) K 0 centralFaceZeroParityCoefficient
  have hsquare : (0 : Q') ≤ mean * mean :=
    YMGap.Constructive.SumOfSquares.q_mul_self_nonneg mean
  have hneg : - (mean * mean) ≤ (0 : Q') :=
    Q'.nonpos_neg_of_nonneg hsquare
  have hdrop : raw + -(mean * mean) ≤ raw := by
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left raw (-(mean * mean)) 0 hneg)
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' raw)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hidentity) hdrop

theorem globalInwardMateCenteredParityWeightedSquare_le_one (K : Nat) :
    centralPhysicalWeightedInner anchorCoupling (by decide) K 0
        (globalInwardMateCenteredParity K)
        (globalInwardMateCenteredParity K) ≤ (1 : Q') := by
  exact Q'.le_trans' _ _ _
    (globalInwardMateCenteredParityWeightedSquare_le_raw K)
    (centralFaceZeroParityWeightedSquare_le_one K)

/-- The relative form margin is half the directed-energy floor. -/
def globalInwardMateParityFormMargin : Q' :=
  Q'.mkPos 1 2 (by decide) * globalInwardMateParityDirichletFloor

theorem globalInwardMateParityFormMargin_positive :
    (0 : Q') < globalInwardMateParityFormMargin := by
  unfold globalInwardMateParityFormMargin
  exact Q'.mul_pos (by decide) globalInwardMateParityDirichletFloor_positive

theorem globalInwardMateParityDirichletFloor_le_one :
    globalInwardMateParityDirichletFloor ≤ (1 : Q') := by
  unfold globalInwardMateParityDirichletFloor
  apply Q'.divPos_le_of_le_mul
  have hcost : (1 : Q') ≤ globalInwardMateParityDirichletCost := by
    unfold globalInwardMateParityDirichletCost
    exact Q'.add_le_self_of_nonneg 1 globalInwardMateTransportCost
      (Q'.le_of_lt globalInwardMateTransportCost_positive)
  exact Q'.le_trans' _ (1 : Q') _ (by decide)
    (Q'.le_trans' _ globalInwardMateParityDirichletCost _ hcost
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.one_mul_eqv globalInwardMateParityDirichletCost))))

theorem globalInwardMateParityFormMargin_le_one :
    globalInwardMateParityFormMargin ≤ (1 : Q') := by
  unfold globalInwardMateParityFormMargin
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.mkPos 1 2 (by decide))
      globalInwardMateParityDirichletFloor_le_one (by decide))
    (Q'.le_trans' _ (Q'.mkPos 1 2 (by decide)) _
      (Q'.le_of_eqv (Q'.mul_one_eqv _)) (by decide))

/-- The explicit one-observable transfer rate. -/
def globalInwardMateParityFormRate : Q' :=
  1 + -globalInwardMateParityFormMargin

theorem globalInwardMateParityFormRate_nonnegative :
    (0 : Q') ≤ globalInwardMateParityFormRate := by
  unfold globalInwardMateParityFormRate
  exact Q'.sub_nonneg_of_le globalInwardMateParityFormMargin_le_one

private theorem one_add_neg_lt_one_of_pos {epsilon : Q'}
    (hpositive : (0 : Q') < epsilon) :
    (1 : Q') + (-epsilon) < (1 : Q') := by
  show ((1 : Q') + -epsilon).num * ((1 : Q').den : Int) <
    (1 : Q').num * (((1 : Q') + -epsilon).den : Int)
  have hnum : (0 : Int) < epsilon.num := Q'.num_pos_of_pos hpositive
  change
    (((1 : Int) * (epsilon.den : Int) + (-epsilon.num) * (1 : Int)) *
      (1 : Int)) <
      ((1 : Int) * (((1 : Nat) * epsilon.den : Nat) : Int))
  push_cast
  omega

theorem globalInwardMateParityFormRate_lt_one :
    globalInwardMateParityFormRate < (1 : Q') := by
  exact one_add_neg_lt_one_of_pos globalInwardMateParityFormMargin_positive

/-! ## 4. The strict physical transfer-form inequality -/

theorem globalInwardMateCenteredParity_margin_le_deficit
    (K : Nat) (hK : 1 <= K) :
    globalInwardMateParityFormMargin ≤
      centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          (globalInwardMateCenteredParity K)
          (globalInwardMateCenteredParity K) +
        -(centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          (globalInwardMateCenteredParity K)
          (centralPhysicalMarkovApply anchorCoupling (by decide) K 0
            (globalInwardMateCenteredParity K))) := by
  let energy := finiteJointDirichletEnergy
    (centralPositiveHalfStates anchorCoupling (by decide) K 0)
    (globalInwardMateCenteredParity K)
    (centralNormalizedPhysicalReflectedKernel
      anchorCoupling (by decide) K 0)
  have hscaledFloor : globalInwardMateParityFormMargin ≤
      Q'.mkPos 1 2 (by decide) * energy := by
    unfold globalInwardMateParityFormMargin
    exact Q'.mul_le_mul_of_nonneg_left _ _ (Q'.mkPos 1 2 (by decide))
      (globalInwardMateParityDirichletFloor_le_positive_centered K hK)
      (by decide)
  exact Q'.le_trans' _ _ _ hscaledFloor
    (Q'.le_of_eqv
      (half_mul_globalInwardMateCenteredParityDirichlet_eqv_deficit K))

theorem globalInwardMateCenteredParity_margin_mul_norm_le_deficit
    (K : Nat) (hK : 1 <= K) :
    globalInwardMateParityFormMargin *
        centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          (globalInwardMateCenteredParity K)
          (globalInwardMateCenteredParity K) ≤
      centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          (globalInwardMateCenteredParity K)
          (globalInwardMateCenteredParity K) +
        -(centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          (globalInwardMateCenteredParity K)
          (centralPhysicalMarkovApply anchorCoupling (by decide) K 0
            (globalInwardMateCenteredParity K))) := by
  let diagonal := centralPhysicalWeightedInner anchorCoupling (by decide) K 0
    (globalInwardMateCenteredParity K) (globalInwardMateCenteredParity K)
  let matrix := centralPhysicalWeightedInner anchorCoupling (by decide) K 0
    (globalInwardMateCenteredParity K)
    (centralPhysicalMarkovApply anchorCoupling (by decide) K 0
      (globalInwardMateCenteredParity K))
  have hmarginDeficit : globalInwardMateParityFormMargin ≤
      diagonal + -matrix :=
    globalInwardMateCenteredParity_margin_le_deficit K hK
  have hscaledNorm : globalInwardMateParityFormMargin * diagonal ≤
      globalInwardMateParityFormMargin := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ globalInwardMateParityFormMargin
        (globalInwardMateCenteredParityWeightedSquare_le_one K)
        (Q'.le_of_lt globalInwardMateParityFormMargin_positive))
      (Q'.le_of_eqv (Q'.mul_one_eqv globalInwardMateParityFormMargin))
  exact Q'.le_trans' _ _ _ hscaledNorm hmarginDeficit

/-- The detected centered parity is a genuinely nonzero physical vector: its
norm is bounded below by the same cutoff-independent form margin. -/
theorem globalInwardMateParityFormMargin_le_centeredNorm
    (K : Nat) (hK : 1 <= K) :
    globalInwardMateParityFormMargin ≤
      centralPhysicalWeightedInner anchorCoupling (by decide) K 0
        (globalInwardMateCenteredParity K)
        (globalInwardMateCenteredParity K) := by
  let diagonal := centralPhysicalWeightedInner anchorCoupling (by decide) K 0
    (globalInwardMateCenteredParity K) (globalInwardMateCenteredParity K)
  let matrix := centralPhysicalWeightedInner anchorCoupling (by decide) K 0
    (globalInwardMateCenteredParity K)
    (centralPhysicalMarkovApply anchorCoupling (by decide) K 0
      (globalInwardMateCenteredParity K))
  have hmarginDeficit : globalInwardMateParityFormMargin ≤
      diagonal + -matrix :=
    globalInwardMateCenteredParity_margin_le_deficit K hK
  have hmatrixNonnegative : (0 : Q') ≤ matrix :=
    centralPhysicalMarkovApply_positive
      anchorCoupling (by decide) K 0 (globalInwardMateCenteredParity K)
  have hdeficitLeDiagonal : diagonal + -matrix ≤ diagonal := by
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left diagonal (-matrix) 0
        (Q'.nonpos_neg_of_nonneg hmatrixNonnegative))
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' diagonal)))
  exact Q'.le_trans' _ _ _ hmarginDeficit hdeficitLeDiagonal

theorem globalInwardMateCenteredParityWeightedSquare_positive
    (K : Nat) (hK : 1 <= K) :
    (0 : Q') <
      centralPhysicalWeightedInner anchorCoupling (by decide) K 0
        (globalInwardMateCenteredParity K)
        (globalInwardMateCenteredParity K) := by
  exact Q'.pos_of_lt_of_le globalInwardMateParityFormMargin_positive
    (globalInwardMateParityFormMargin_le_centeredNorm K hK)

theorem globalInwardMateCenteredParity_strict_form
    (K : Nat) (hK : 1 <= K) :
    centralPhysicalWeightedInner anchorCoupling (by decide) K 0
        (globalInwardMateCenteredParity K)
        (centralPhysicalMarkovApply anchorCoupling (by decide) K 0
          (globalInwardMateCenteredParity K)) ≤
      globalInwardMateParityFormRate *
        centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          (globalInwardMateCenteredParity K)
          (globalInwardMateCenteredParity K) := by
  let diagonal := centralPhysicalWeightedInner anchorCoupling (by decide) K 0
    (globalInwardMateCenteredParity K) (globalInwardMateCenteredParity K)
  let matrix := centralPhysicalWeightedInner anchorCoupling (by decide) K 0
    (globalInwardMateCenteredParity K)
    (centralPhysicalMarkovApply anchorCoupling (by decide) K 0
      (globalInwardMateCenteredParity K))
  let margin := globalInwardMateParityFormMargin
  have hpoincare : margin * diagonal ≤ diagonal + -matrix :=
    globalInwardMateCenteredParity_margin_mul_norm_le_deficit K hK
  have hadd := Q'.add_le_add_right
    (margin * diagonal) (diagonal + -matrix) matrix hpoincare
  have hsum : margin * diagonal + matrix ≤ diagonal :=
    Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv
        (Q'.eqv_trans _ (diagonal + (-matrix + matrix)) _
          (Q'.add_assoc_eqv diagonal (-matrix) matrix)
          (Q'.eqv_trans _ (diagonal + 0) _
            (Q'.add_eqv_congr_left diagonal _ _
              (Q'.neg_add_self_eqv matrix))
            (Q'.eqv_of_eq (Q'.add_zero' diagonal)))))
  have htranslated := Q'.add_le_add_left
    (-(margin * diagonal)) (margin * diagonal + matrix) diagonal hsum
  have hleft : -(margin * diagonal) + (margin * diagonal + matrix) ≈
      matrix := by
    exact Q'.eqv_trans _ ((-(margin * diagonal) + margin * diagonal) + matrix) _
      (Q'.eqv_symm
        (Q'.add_assoc_eqv (-(margin * diagonal)) (margin * diagonal) matrix))
      (Q'.eqv_trans _ (0 + matrix) _
        (Q'.add_eqv_congr_right _ _ matrix
          (Q'.neg_add_self_eqv (margin * diagonal)))
        (Q'.eqv_of_eq (Q'.zero_add' matrix)))
  have hright : -(margin * diagonal) + diagonal ≈
      globalInwardMateParityFormRate * diagonal := by
    refine Q'.eqv_trans _ (diagonal + -(margin * diagonal)) _
      (Q'.add_comm_eqv _ _) ?_
    refine Q'.eqv_trans _ (diagonal + (-margin) * diagonal) _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_symm (Q'.neg_mul_eqv margin diagonal))) ?_
    refine Q'.eqv_trans _ ((1 : Q') * diagonal + (-margin) * diagonal) _
      (Q'.add_eqv_congr' (Q'.eqv_symm (Q'.one_mul_eqv diagonal))
        (Q'.eqv_refl _)) ?_
    unfold globalInwardMateParityFormRate margin
    exact Q'.eqv_symm (Q'.add_mul_eqv 1 (-globalInwardMateParityFormMargin)
      diagonal)
  exact le_of_eqv_le (Q'.eqv_symm hleft)
    (le_of_le_eqv htranslated hright)

theorem globalInwardMateCenteredParity_abs_strict_form
    (K : Nat) (hK : 1 <= K) :
    Q'.abs
        (centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          (globalInwardMateCenteredParity K)
          (centralPhysicalMarkovApply anchorCoupling (by decide) K 0
            (globalInwardMateCenteredParity K))) ≤
      globalInwardMateParityFormRate *
        centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          (globalInwardMateCenteredParity K)
          (globalInwardMateCenteredParity K) := by
  rw [abs_of_nonneg]
  · exact globalInwardMateCenteredParity_strict_form K hK
  · exact centralPhysicalMarkovApply_positive
      anchorCoupling (by decide) K 0 (globalInwardMateCenteredParity K)

structure GlobalInwardMateParityFormGapCertificate
    (K : Nat) (hK : 1 <= K) : Type where
  centeredCoefficient : EdgeLabelling -> Q'
  margin : Q'
  rate : Q'
  centeredCoefficient_eq : centeredCoefficient =
    globalInwardMateCenteredParity K
  meanZero : CentralPhysicalMeanZero anchorCoupling (by decide) K 0
    centeredCoefficient
  margin_eq : margin ≈ globalInwardMateParityFormMargin
  margin_positive : (0 : Q') < margin
  rate_eq : rate ≈ globalInwardMateParityFormRate
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  dirichlet_floor : globalInwardMateParityDirichletFloor ≤
    finiteJointDirichletEnergy
      (centralPositiveHalfStates anchorCoupling (by decide) K 0)
      centeredCoefficient
      (centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0)
  norm_floor : margin ≤
    centralPhysicalWeightedInner anchorCoupling (by decide) K 0
      centeredCoefficient centeredCoefficient
  norm_positive : (0 : Q') <
    centralPhysicalWeightedInner anchorCoupling (by decide) K 0
      centeredCoefficient centeredCoefficient
  strict_form : Q'.abs
      (centralPhysicalWeightedInner anchorCoupling (by decide) K 0
        centeredCoefficient
        (centralPhysicalMarkovApply anchorCoupling (by decide) K 0
          centeredCoefficient)) ≤
    rate * centralPhysicalWeightedInner anchorCoupling (by decide) K 0
      centeredCoefficient centeredCoefficient

def globalInwardMateParityFormGapCertificate
    (K : Nat) (hK : 1 <= K) :
    GlobalInwardMateParityFormGapCertificate K hK :=
  { centeredCoefficient := globalInwardMateCenteredParity K
    margin := globalInwardMateParityFormMargin
    rate := globalInwardMateParityFormRate
    centeredCoefficient_eq := rfl
    meanZero := globalInwardMateCenteredParity_meanZero K
    margin_eq := Q'.eqv_refl _
    margin_positive := globalInwardMateParityFormMargin_positive
    rate_eq := Q'.eqv_refl _
    rate_nonnegative := globalInwardMateParityFormRate_nonnegative
    rate_lt_one := globalInwardMateParityFormRate_lt_one
    dirichlet_floor :=
      globalInwardMateParityDirichletFloor_le_positive_centered K hK
    norm_floor := globalInwardMateParityFormMargin_le_centeredNorm K hK
    norm_positive := globalInwardMateCenteredParityWeightedSquare_positive K hK
    strict_form := globalInwardMateCenteredParity_abs_strict_form K hK }

#print axioms finiteJointDirichletEnergy_add_neg_constant_eqv
#print axioms centralPhysicalPositiveDirichlet_eqv_full
#print axioms globalInwardMateCenteredParity
#print axioms globalInwardMateCenteredParity_meanZero
#print axioms globalInwardMateParityDirichletFloor_le_positive_centered
#print axioms half_mul_globalInwardMateCenteredParityDirichlet_eqv_deficit
#print axioms centralFaceZeroParityWeightedSquare_le_one
#print axioms globalInwardMateCenteredParityWeightedSquare_le_one
#print axioms globalInwardMateParityFormMargin
#print axioms globalInwardMateParityFormMargin_positive
#print axioms globalInwardMateParityFormRate
#print axioms globalInwardMateParityFormRate_nonnegative
#print axioms globalInwardMateParityFormRate_lt_one
#print axioms globalInwardMateCenteredParity_margin_le_deficit
#print axioms globalInwardMateCenteredParity_margin_mul_norm_le_deficit
#print axioms globalInwardMateParityFormMargin_le_centeredNorm
#print axioms globalInwardMateCenteredParityWeightedSquare_positive
#print axioms globalInwardMateCenteredParity_strict_form
#print axioms globalInwardMateCenteredParity_abs_strict_form
#print axioms globalInwardMateParityFormGapCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFormGap
