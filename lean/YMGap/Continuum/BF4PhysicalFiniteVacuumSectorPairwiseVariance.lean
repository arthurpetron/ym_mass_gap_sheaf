/-
# Pairwise variance on finite BF4 vacuum sectors

The common endpoint estimate must be summed with the physical stationary
weights.  This module defines the weighted pairwise variance and proves its
exact algebraic identity

  pairVariance = 2 * (mass * diagonal - mean^2).

The proof reuses the generic Dirichlet identity with the stationary product
joint `weight_i * weight_j`; normalization of the selected component is not
needed.  Exact centering therefore gives

  pairVariance = 2 * mass * diagonal.

The all-endpoint floor/ceiling estimate is also summed constructively, giving
the two inequalities that the next Poincare module will combine.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Generic weighted pairwise variance -/

def finiteWeightedMass {State : Type}
    (states : List State) (weight : State → Q') : Q' :=
  listQSum weight states

def finiteListWeightedMean {State : Type}
    (states : List State) (weight coefficient : State → Q') : Q' :=
  listQSum (fun state => coefficient state * weight state) states

def finiteStationaryProductJoint {State : Type}
    (weight : State → Q') (left right : State) : Q' :=
  weight left * weight right

/-- The weighted squared difference summed over all ordered pairs. -/
def finiteWeightedPairwiseVariance {State : Type}
    (states : List State) (weight coefficient : State → Q') : Q' :=
  finiteJointDirichletEnergy states coefficient
    (finiteStationaryProductJoint weight)

theorem finiteStationaryProductJoint_quadratic_eqv_mean_square
    {State : Type} (states : List State)
    (weight coefficient : State → Q') :
    finiteJointQuadratic states coefficient
        (finiteStationaryProductJoint weight) ≈
      finiteListWeightedMean states weight coefficient *
        finiteListWeightedMean states weight coefficient := by
  let value : State → Q' := fun state =>
    coefficient state * weight state
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum (fun right => value left * value right) states)
      states) _ ?_ ?_
  · unfold finiteJointQuadratic finiteStationaryProductJoint value
    apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    q_ring
  · unfold finiteListWeightedMean value
    exact listQSum_product _ _ states states

/-- Exact pairwise-variance identity for an arbitrary finite weighted list.
No positivity or normalization assumption is needed for this equality. -/
theorem finiteWeightedPairwiseVariance_eqv_mass_diagonal_mean
    {State : Type} (states : List State)
    (weight coefficient : State → Q') :
    finiteWeightedPairwiseVariance states weight coefficient ≈
      (finiteWeightedMass states weight *
            finiteWeightedSquare states weight coefficient +
        finiteWeightedMass states weight *
            finiteWeightedSquare states weight coefficient) +
      -(finiteListWeightedMean states weight coefficient *
            finiteListWeightedMean states weight coefficient +
        finiteListWeightedMean states weight coefficient *
            finiteListWeightedMean states weight coefficient) := by
  let mass := finiteWeightedMass states weight
  let scaledWeight : State → Q' := fun state => mass * weight state
  have hrow : ∀ state, state ∈ states →
      listQSum (finiteStationaryProductJoint weight state) states ≈
        scaledWeight state := by
    intro state _hstate
    refine Q'.eqv_trans _ (weight state * mass) _ ?_ ?_
    · unfold finiteStationaryProductJoint mass finiteWeightedMass
      exact listQSum_mul_left (weight state) weight states
    · unfold scaledWeight
      exact Q'.mul_comm_eqv _ _
  have hsymmetric : ∀ left, left ∈ states →
      ∀ right, right ∈ states →
      finiteStationaryProductJoint weight left right ≈
        finiteStationaryProductJoint weight right left := by
    intro left _hleft right _hright
    unfold finiteStationaryProductJoint
    exact Q'.mul_comm_eqv _ _
  have hgeneric := finiteJointDirichletEnergy_eqv_twice_deficit
    states scaledWeight coefficient
    (finiteStationaryProductJoint weight) hrow hsymmetric
  have hdiagonal :
      finiteWeightedSquare states scaledWeight coefficient ≈
        mass * finiteWeightedSquare states weight coefficient := by
    unfold finiteWeightedSquare scaledWeight
    refine Q'.eqv_trans _
      (listQSum
        (fun state =>
          mass * (weight state *
            (coefficient state * coefficient state)))
        states) _ ?_ ?_
    · apply listQSum_congr
      intro state
      exact Q'.mul_assoc_eqv _ _ _
    · exact listQSum_mul_left mass
        (fun state =>
          weight state * (coefficient state * coefficient state))
        states
  have hmean :=
    finiteStationaryProductJoint_quadratic_eqv_mean_square
      states weight coefficient
  unfold finiteWeightedPairwiseVariance
  refine Q'.eqv_trans _ _ _ hgeneric ?_
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr' hdiagonal hdiagonal)
    (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr' hmean hmean))

/-- Exact centering removes the mean-square term from pairwise variance. -/
theorem finiteWeightedPairwiseVariance_centered_eqv_twice_mass_diagonal
    {State : Type} (states : List State)
    (weight coefficient : State → Q')
    (hcenter : finiteListWeightedMean states weight coefficient ≈ 0) :
    finiteWeightedPairwiseVariance states weight coefficient ≈
      finiteWeightedMass states weight *
          finiteWeightedSquare states weight coefficient +
        finiteWeightedMass states weight *
          finiteWeightedSquare states weight coefficient := by
  let massDiagonal := finiteWeightedMass states weight *
    finiteWeightedSquare states weight coefficient
  let mean := finiteListWeightedMean states weight coefficient
  have hmeanSquare : mean * mean ≈ 0 := by
    refine Q'.eqv_trans _ (0 * 0) _ ?_ ?_
    · exact Q'.eqv_trans _ (0 * mean) _
        (Q'.mul_eqv_congr_right mean 0 mean hcenter)
        (Q'.mul_eqv_congr_left 0 mean 0 hcenter)
    · exact Q'.zero_mul_eqv 0
  have hmeanTwice : mean * mean + mean * mean ≈ 0 := by
    refine Q'.eqv_trans _ (0 + 0) _
      (Q'.add_eqv_congr' hmeanSquare hmeanSquare) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' 0)
  refine Q'.eqv_trans _
    ((massDiagonal + massDiagonal) +
      -(mean * mean + mean * mean)) _ ?_ ?_
  · exact finiteWeightedPairwiseVariance_eqv_mass_diagonal_mean
      states weight coefficient
  refine Q'.eqv_trans _ ((massDiagonal + massDiagonal) + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ (-0) _
        (Q'.neg_eqv_congr _ _ hmeanTwice) (by decide))
  · exact Q'.eqv_of_eq (Q'.add_zero' _)

/-! ## 2. Summing a common endpoint estimate -/

/-- If every squared endpoint difference has a common floor/ceiling bound,
then the weighted pairwise variance obeys the corresponding mass-squared
global bound. -/
theorem floor_mul_finiteWeightedPairwiseVariance_le
    {State : Type} (states : List State)
    (weight coefficient : State → Q')
    (floor ceiling energy : Q')
    (hweight : ∀ state, state ∈ states → (0 : Q') ≤ weight state)
    (hendpoint : ∀ left, left ∈ states → ∀ right, right ∈ states →
      floor *
          ((coefficient left + -coefficient right) *
            (coefficient left + -coefficient right)) ≤
        ceiling * energy) :
    floor * finiteWeightedPairwiseVariance states weight coefficient ≤
      (finiteWeightedMass states weight *
          finiteWeightedMass states weight) *
        (ceiling * energy) := by
  let square : State → State → Q' := fun left right =>
    (coefficient left + -coefficient right) *
      (coefficient left + -coefficient right)
  let pairWeight : State → State → Q' := fun left right =>
    weight left * weight right
  let fixed := ceiling * energy
  let lowerSum := listQSum
    (fun left => listQSum
      (fun right => pairWeight left right * (floor * square left right))
      states)
    states
  let upperSum := listQSum
    (fun left => listQSum
      (fun right => pairWeight left right * fixed)
      states)
    states
  have hsums : lowerSum ≤ upperSum := by
    unfold lowerSum upperSum
    apply listQSum_mono
    intro left hleft
    apply listQSum_mono
    intro right hright
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (hendpoint left hleft right hright)
      (Q'.mul_nonneg _ _
        (hweight left hleft) (hweight right hright))
  have hlower : lowerSum ≈
      floor * finiteWeightedPairwiseVariance states weight coefficient := by
    unfold lowerSum finiteWeightedPairwiseVariance
      finiteJointDirichletEnergy pairWeight square
    refine Q'.eqv_trans _
      (listQSum
        (fun left => floor *
          listQSum
            (fun right =>
              (weight left * weight right) *
                ((coefficient left + -coefficient right) *
                  (coefficient left + -coefficient right)))
            states)
        states) _ ?_ ?_
    · apply listQSum_congr
      intro left
      refine Q'.eqv_trans _
        (listQSum
          (fun right => floor *
            ((weight left * weight right) *
              ((coefficient left + -coefficient right) *
                (coefficient left + -coefficient right))))
          states) _ ?_ ?_
      · apply listQSum_congr
        intro right
        q_ring
      · exact listQSum_mul_left floor _ states
    · exact listQSum_mul_left floor _ states
  have hupper : upperSum ≈
      (finiteWeightedMass states weight *
          finiteWeightedMass states weight) * fixed := by
    unfold upperSum
    refine Q'.eqv_trans _
      (listQSum
        (fun left =>
          (weight left * finiteWeightedMass states weight) * fixed)
        states) _ ?_ ?_
    · apply listQSum_congr
      intro left
      refine Q'.eqv_trans _
        (listQSum (fun right =>
          (weight left * weight right) * fixed) states) _
        (Q'.eqv_refl _) ?_
      refine Q'.eqv_trans _
        (listQSum (fun right => weight left * weight right) states * fixed)
        _ (listQSum_mul_right _ fixed states) ?_
      exact Q'.mul_eqv_congr_right _ _ fixed
        (Q'.eqv_trans _
          (weight left * listQSum weight states) _
          (listQSum_mul_left (weight left) weight states)
          (Q'.eqv_refl _))
    refine Q'.eqv_trans _
      (listQSum
          (fun left => weight left * finiteWeightedMass states weight)
          states * fixed) _
      (listQSum_mul_right _ fixed states) ?_
    exact Q'.mul_eqv_congr_right _ _ fixed
      (Q'.eqv_trans _
        (listQSum weight states * finiteWeightedMass states weight) _
        (listQSum_mul_right weight
          (finiteWeightedMass states weight) states)
        (Q'.eqv_refl _))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hlower))
    (Q'.le_trans' _ _ _ hsums (Q'.le_of_eqv hupper))

/-! ## 3. BF4 specializations -/

def centralPhysicalFiniteVacuumSectorMass
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  finiteWeightedMass
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteWeight w hw cutoff half)

def centralPhysicalFiniteVacuumSectorPairwiseVariance
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedPairwiseVariance
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteWeight w hw cutoff half)
    coefficient

theorem centralPhysicalFiniteVacuumSectorPairwiseVariance_centered_eqv
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q')
    (hcenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
        w hw cutoff half coefficient ≈ 0) :
    centralPhysicalFiniteVacuumSectorPairwiseVariance
        w hw cutoff half coefficient ≈
      centralPhysicalFiniteVacuumSectorMass w hw cutoff half *
          centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            w hw cutoff half coefficient +
        centralPhysicalFiniteVacuumSectorMass w hw cutoff half *
          centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            w hw cutoff half coefficient := by
  let states := centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let weight := centralPhysicalFiniteWeight w hw cutoff half
  have hgeneric :=
    finiteWeightedPairwiseVariance_centered_eqv_twice_mass_diagonal
      states weight coefficient hcenter
  have hdiagonal : finiteWeightedSquare states weight coefficient ≈
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half coefficient := by
    unfold finiteWeightedSquare
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic states weight
    apply listQSum_congr
    intro index
    exact Q'.mul_comm_eqv _ _
  unfold centralPhysicalFiniteVacuumSectorPairwiseVariance
    centralPhysicalFiniteVacuumSectorMass
  exact Q'.eqv_trans _ _ _ hgeneric
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ hdiagonal)
      (Q'.mul_eqv_congr_left _ _ _ hdiagonal))

theorem centralPhysicalFiniteVacuumSector_floor_mul_pairwiseVariance_le
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorEdgeFloor w hw cutoff half *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w hw cutoff half coefficient ≤
      (centralPhysicalFiniteVacuumSectorMass w hw cutoff half *
          centralPhysicalFiniteVacuumSectorMass w hw cutoff half) *
        (centralPhysicalFiniteVacuumSectorPathCeiling w hw cutoff half *
          finiteJointDirichletEnergy
            (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
            coefficient
            (centralPhysicalFiniteKernel w hw cutoff half)) := by
  exact floor_mul_finiteWeightedPairwiseVariance_le
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteWeight w hw cutoff half)
    coefficient
    (centralPhysicalFiniteVacuumSectorEdgeFloor w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorPathCeiling w hw cutoff half)
    (finiteJointDirichletEnergy
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      coefficient
      (centralPhysicalFiniteKernel w hw cutoff half))
    (fun state _hstate =>
      centralPhysicalRowMarginal_nonnegative hw cutoff half
        (centralPhysicalFiniteStateAt w hw cutoff half state))
    (fun left hleft right hright =>
      centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_ceiling_mul_Dirichlet
        w hw cutoff half coefficient left right hleft hright)

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance.finiteWeightedPairwiseVariance_eqv_mass_diagonal_mean
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance.finiteWeightedPairwiseVariance_centered_eqv_twice_mass_diagonal
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance.floor_mul_finiteWeightedPairwiseVariance_le
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance.centralPhysicalFiniteVacuumSectorPairwiseVariance_centered_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance.centralPhysicalFiniteVacuumSector_floor_mul_pairwiseVariance_le
