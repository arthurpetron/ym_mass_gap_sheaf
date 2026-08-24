/-
# Full pairwise variance contracts to one observable rooted at the vacuum

For a finite nonnegative law of mass at most one, the full ordered pairwise
variance of a coefficient is at most twice its weighted square distance from
any fixed root.  The proof shifts the *same* coefficient by its root value,
uses the exact finite pairwise-variance identity, and drops only the
nonnegative mean square.  No new observable or independently chosen moment is
introduced.

Specializing the root to the physical vacuum index `0` turns the quadratic
all-pairs endpoint problem into a one-body sum over physical states.  This is
the algebraic compiler needed by a rooted path traffic construction.  It does
not itself prove a uniform path-capacity estimate, transfer gap, continuum
limit, continuum QFT, or Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
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

private theorem q_neg_nonpos_of_nonnegative_local {value : Q'}
    (hvalue : (0 : Q') ≤ value) : -value ≤ (0 : Q') := by
  have hadded : (0 : Q') + -value ≤ value + -value :=
    Q'.add_le_add_right 0 value (-value) hvalue
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (-value))))
    (Q'.le_trans' _ _ _ hadded
      (Q'.le_of_eqv (Q'.add_neg_self_eqv value)))

/-! ## 1. Generic same-observable root contraction -/

/-- Weighted square distance of one coefficient from its value at `root`. -/
def finiteWeightedRootVariance {State : Type}
    (states : List State) (weight coefficient : State → Q')
    (root : State) : Q' :=
  listQSum
    (fun state =>
      weight state *
        ((coefficient state + -coefficient root) *
          (coefficient state + -coefficient root)))
    states

theorem finiteWeightedRootVariance_nonnegative
    {State : Type} (states : List State)
    (weight coefficient : State → Q') (root : State)
    (hweight : ∀ state, state ∈ states → (0 : Q') ≤ weight state) :
    (0 : Q') ≤
      finiteWeightedRootVariance states weight coefficient root := by
  unfold finiteWeightedRootVariance
  apply listQSum_nonnegative_on
  intro state hstate
  exact Q'.mul_nonneg _ _ (hweight state hstate)
    (SumOfSquares.q_mul_self_nonneg
      (coefficient state + -coefficient root))

/-- Subtracting the root value from the same coefficient leaves every
pairwise difference unchanged. -/
theorem finiteWeightedPairwiseVariance_shiftRoot_eqv
    {State : Type} (states : List State)
    (weight coefficient : State → Q') (root : State) :
    finiteWeightedPairwiseVariance states weight coefficient ≈
      finiteWeightedPairwiseVariance states weight
        (fun state => coefficient state + -coefficient root) := by
  unfold finiteWeightedPairwiseVariance finiteJointDirichletEnergy
  apply listQSum_congr
  intro left
  apply listQSum_congr
  intro right
  apply Q'.mul_eqv_congr_left
  let original := coefficient left + -coefficient right
  let shifted := (coefficient left + -coefficient root) +
    -(coefficient right + -coefficient root)
  have hneg : -(coefficient right + -coefficient root) ≈
      -coefficient right + coefficient root := by
    exact Q'.eqv_trans _
      (-coefficient right + -(-coefficient root)) _
      (Q'.neg_add_eqv _ _)
      (Q'.add_eqv_congr_left (-coefficient right) _ _
        (Q'.neg_neg_eqv _))
  have hshifted : shifted ≈ original := by
    unfold shifted original
    refine Q'.eqv_trans _
      ((coefficient left + -coefficient root) +
        (-coefficient right + coefficient root)) _
      (Q'.add_eqv_congr_left
        (coefficient left + -coefficient root) _ _ hneg) ?_
    refine Q'.eqv_trans _
      ((coefficient left + -coefficient right) +
        (-coefficient root + coefficient root)) _
      (Q'.add_swap_inner _ _ _ _) ?_
    refine Q'.eqv_trans _ ((coefficient left + -coefficient right) + 0) _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.neg_add_self_eqv (coefficient root))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' _)
  have hdifference : original ≈ shifted := Q'.eqv_symm hshifted
  exact Q'.eqv_trans _ (shifted * original) _
    (Q'.mul_eqv_congr_right original shifted original hdifference)
    (Q'.mul_eqv_congr_left shifted original shifted hdifference)

/-- Exact pairwise algebra bounds the ordered pairwise variance by twice the
mass times the weighted root variance.  The only discarded term is the
square of the shifted weighted mean. -/
theorem finiteWeightedPairwiseVariance_le_twice_mass_rootVariance
    {State : Type} (states : List State)
    (weight coefficient : State → Q') (root : State) :
    finiteWeightedPairwiseVariance states weight coefficient ≤
      finiteWeightedMass states weight *
          finiteWeightedRootVariance states weight coefficient root +
        finiteWeightedMass states weight *
          finiteWeightedRootVariance states weight coefficient root := by
  let shifted : State → Q' := fun state =>
    coefficient state + -coefficient root
  let massRoot := finiteWeightedMass states weight *
    finiteWeightedRootVariance states weight coefficient root
  let mean := finiteListWeightedMean states weight shifted
  have hshift := finiteWeightedPairwiseVariance_shiftRoot_eqv
    states weight coefficient root
  have hidentity := finiteWeightedPairwiseVariance_eqv_mass_diagonal_mean
    states weight shifted
  have hdiagonal : finiteWeightedSquare states weight shifted ≈
      finiteWeightedRootVariance states weight coefficient root := by
    unfold finiteWeightedSquare finiteWeightedRootVariance shifted
    exact Q'.eqv_refl _
  have hformula :
      finiteWeightedPairwiseVariance states weight coefficient ≈
        (massRoot + massRoot) + -(mean * mean + mean * mean) := by
    refine Q'.eqv_trans _ _ _ hshift ?_
    refine Q'.eqv_trans _ _ _ hidentity ?_
    unfold massRoot mean shifted
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ hdiagonal)
        (Q'.mul_eqv_congr_left _ _ _ hdiagonal))
      (Q'.eqv_refl _)
  have hmeanSquare : (0 : Q') ≤ mean * mean :=
    SumOfSquares.q_mul_self_nonneg mean
  have hmeanTwice : (0 : Q') ≤ mean * mean + mean * mean :=
    Q'.zero_le_add _ _ hmeanSquare hmeanSquare
  have hdrop :
      (massRoot + massRoot) + -(mean * mean + mean * mean) ≤
        (massRoot + massRoot) + 0 :=
    Q'.add_le_add_left (massRoot + massRoot) _ _
      (q_neg_nonpos_of_nonnegative_local hmeanTwice)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hformula)
    (Q'.le_trans' _ _ _ hdrop
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _))))

/-- If the finite law has mass at most one, the mass factor disappears. -/
theorem finiteWeightedPairwiseVariance_le_twice_rootVariance
    {State : Type} (states : List State)
    (weight coefficient : State → Q') (root : State)
    (hweight : ∀ state, state ∈ states → (0 : Q') ≤ weight state)
    (hmass : finiteWeightedMass states weight ≤ 1) :
    finiteWeightedPairwiseVariance states weight coefficient ≤
      finiteWeightedRootVariance states weight coefficient root +
        finiteWeightedRootVariance states weight coefficient root := by
  let rootVariance :=
    finiteWeightedRootVariance states weight coefficient root
  have hroot0 : (0 : Q') ≤ rootVariance :=
    finiteWeightedRootVariance_nonnegative
      states weight coefficient root hweight
  have hscaled : finiteWeightedMass states weight * rootVariance ≤
      rootVariance := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ rootVariance hmass hroot0)
      (Q'.le_of_eqv (Q'.one_mul_eqv rootVariance))
  exact Q'.le_trans' _ _ _
    (finiteWeightedPairwiseVariance_le_twice_mass_rootVariance
      states weight coefficient root)
    (Q'.add_le_add hscaled hscaled)

/-! ## 2. BF4 physical vacuum-root specialization -/

def centralPhysicalFiniteVacuumSectorRootVariance
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedRootVariance
    (centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (centralPhysicalFiniteWeight w hw K half)
    coefficient 0

/-- The complete finite physical pairwise variance of the same coefficient is
controlled by two copies of its one-body square distance from the vacuum. -/
theorem centralPhysicalFiniteVacuumSectorPairwiseVariance_le_twice_rootVariance
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorPairwiseVariance
        w hw K half coefficient ≤
      centralPhysicalFiniteVacuumSectorRootVariance
          w hw K half coefficient +
        centralPhysicalFiniteVacuumSectorRootVariance
          w hw K half coefficient := by
  exact finiteWeightedPairwiseVariance_le_twice_rootVariance
    (centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (centralPhysicalFiniteWeight w hw K half)
    coefficient 0
    (fun state _hstate =>
      centralPhysicalRowMarginal_nonnegative hw K half
        (centralPhysicalFiniteStateAt w hw K half state))
    (centralPhysicalFiniteVacuumSectorMass_le_one w hw K half)

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance.finiteWeightedRootVariance_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance.finiteWeightedPairwiseVariance_shiftRoot_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance.finiteWeightedPairwiseVariance_le_twice_mass_rootVariance
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance.finiteWeightedPairwiseVariance_le_twice_rootVariance
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance.centralPhysicalFiniteVacuumSectorPairwiseVariance_le_twice_rootVariance
