/-
# A completed BF4 vector from one moving rationally centered observable

The same finite cylinder coefficient can be centered legally at every
representation cutoff by changing only its rational root coordinate.  The
head-correction sequence now has a Type-level cutoff rate, so its rational
Cauchy control can be lifted to the actual cutoff-removed squared seminorm.

This module proves a global pointwise square bound between two moving
presentations, packages the presentations as an explicit-modulus Cauchy
representative, and constructs its sector and global completed vectors.  The
observable identity is fixed throughout; only the rational centering
coordinate moves.

This does not yet prove that the completed vector is nonzero or orthogonal to
the completed vacuum, identify its same-object transfer moments, inhabit a
dynamic observable pin, or make a continuum/Clay claim.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicUniformCauchy
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicUniformCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

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

/- Keep the quotient-rational algebra outside the large BF4 dependent
context below.  These two tiny compilers prevent normalization of all of the
observable and cutoff data when only an affine cancellation is required. -/
private theorem affineCorrectionDifference_eqv
    (raw firstCorrection secondCorrection rootValue : Q') :
    (raw + (-firstCorrection) * rootValue) +
        -(raw + (-secondCorrection) * rootValue) ≈
      (secondCorrection + -firstCorrection) * rootValue := by
  let firstTerm := (-firstCorrection) * rootValue
  let secondTerm := (-secondCorrection) * rootValue
  refine Q'.eqv_trans _
    ((raw + firstTerm) + ((-raw) + (-secondTerm))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left (raw + firstTerm)
      (-(raw + secondTerm)) ((-raw) + (-secondTerm))
      (Q'.neg_add_eqv raw secondTerm)
  refine Q'.eqv_trans _
    ((raw + -raw) + (firstTerm + -secondTerm)) _
    (Q'.add_swap_inner raw firstTerm (-raw) (-secondTerm)) ?_
  refine Q'.eqv_trans _
    ((0 : Q') + (firstTerm + -secondTerm)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right (raw + -raw) 0
      (firstTerm + -secondTerm) (Q'.add_neg_self_eqv raw)
  refine Q'.eqv_trans _ (firstTerm + -secondTerm) _ ?_ ?_
  · exact Q'.eqv_of_eq (Q'.zero_add' (firstTerm + -secondTerm))
  have hfirstTerm : firstTerm ≈ -(firstCorrection * rootValue) := by
    exact Q'.neg_mul_eqv firstCorrection rootValue
  have hsecondTerm : -secondTerm ≈ secondCorrection * rootValue := by
    refine Q'.eqv_trans _ (-(-(secondCorrection * rootValue))) _ ?_ ?_
    · exact Q'.neg_eqv_congr secondTerm
        (-(secondCorrection * rootValue))
        (Q'.neg_mul_eqv secondCorrection rootValue)
    · exact Q'.neg_neg_eqv (secondCorrection * rootValue)
  refine Q'.eqv_trans _
    (-(firstCorrection * rootValue) + secondCorrection * rootValue) _ ?_ ?_
  · exact Q'.add_eqv_congr' hfirstTerm hsecondTerm
  refine Q'.eqv_trans _
    (secondCorrection * rootValue + -(firstCorrection * rootValue)) _
    (Q'.add_comm_eqv _ _) ?_
  exact Q'.eqv_symm
    (Q'.sub_mul_eqv secondCorrection firstCorrection rootValue)

private theorem correctionReverse_eqv
    (firstCorrection secondCorrection : Q') :
    secondCorrection + -firstCorrection ≈
      -(firstCorrection + -secondCorrection) := by
  refine Q'.eqv_trans _ (-firstCorrection + secondCorrection) _
    (Q'.add_comm_eqv secondCorrection (-firstCorrection)) ?_
  refine Q'.eqv_trans _ (-firstCorrection + -(-secondCorrection)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left (-firstCorrection) secondCorrection
      (-(-secondCorrection))
      (Q'.eqv_symm (Q'.neg_neg_eqv secondCorrection))
  exact Q'.eqv_symm (Q'.neg_add_eqv firstCorrection (-secondCorrection))

private theorem negSquare_eqv (delta : Q') :
    (-delta) * (-delta) ≈ delta * delta := by
  refine Q'.eqv_trans _ (-(delta * (-delta))) _
    (Q'.neg_mul_eqv delta (-delta)) ?_
  refine Q'.eqv_trans _ (-(-(delta * delta))) _ ?_ ?_
  · exact Q'.neg_eqv_congr (delta * (-delta)) (-(delta * delta))
      (Q'.mul_neg_eqv delta delta)
  exact Q'.neg_neg_eqv (delta * delta)

private theorem productSquare_eqv (coefficient rootValue : Q') :
    (coefficient * rootValue) * (coefficient * rootValue) ≈
      (coefficient * coefficient) * (rootValue * rootValue) := by
  refine Q'.eqv_trans _
    (coefficient * (rootValue * (coefficient * rootValue))) _
    (Q'.mul_assoc_eqv coefficient rootValue
      (coefficient * rootValue)) ?_
  have hinner : rootValue * (coefficient * rootValue) ≈
      coefficient * (rootValue * rootValue) := by
    refine Q'.eqv_trans _ ((rootValue * coefficient) * rootValue) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv rootValue coefficient rootValue)) ?_
    refine Q'.eqv_trans _ ((coefficient * rootValue) * rootValue) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right
        (rootValue * coefficient) (coefficient * rootValue) rootValue
        (Q'.mul_comm_eqv rootValue coefficient)
    · exact Q'.mul_assoc_eqv coefficient rootValue rootValue
  refine Q'.eqv_trans _
    (coefficient * (coefficient * (rootValue * rootValue))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left coefficient
      (rootValue * (coefficient * rootValue))
      (coefficient * (rootValue * rootValue)) hinner
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv coefficient coefficient (rootValue * rootValue))

private theorem reversedCorrectionSquare_eqv
    (firstCorrection secondCorrection rootValue : Q') :
    ((secondCorrection + -firstCorrection) * rootValue) *
        ((secondCorrection + -firstCorrection) * rootValue) ≈
      ((firstCorrection + -secondCorrection) *
        (firstCorrection + -secondCorrection)) *
        (rootValue * rootValue) := by
  let positiveDelta := secondCorrection + -firstCorrection
  let delta := firstCorrection + -secondCorrection
  have hreverse : positiveDelta ≈ -delta :=
    correctionReverse_eqv firstCorrection secondCorrection
  have hcoefficientSquare : positiveDelta * positiveDelta ≈
      delta * delta := by
    refine Q'.eqv_trans _ ((-delta) * positiveDelta) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right positiveDelta (-delta)
        positiveDelta hreverse
    refine Q'.eqv_trans _ ((-delta) * (-delta)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left (-delta)
        positiveDelta (-delta) hreverse
    · exact negSquare_eqv delta
  refine Q'.eqv_trans _
    ((positiveDelta * positiveDelta) * (rootValue * rootValue)) _
    (productSquare_eqv positiveDelta rootValue) ?_
  exact Q'.mul_eqv_congr_right
    (positiveDelta * positiveDelta) (delta * delta)
    (rootValue * rootValue) hcoefficientSquare

/-! ## 1. Exact semantic expansion of the moving cylinder -/

private theorem stateCylinderLinearCombination_value_eqv_weighted
    (half : Nat) (stateAt : Nat → EdgeLabelling)
    (coefficient : Nat → Q') (state : EdgeLabelling)
    (indices : List Nat) :
    (centralPhysicalStateCylinderLinearCombination
        half stateAt coefficient indices).value state ≈
      listQSum
        (fun index => coefficient index *
          (centralPhysicalStateCylinderUnitObservable
            half (stateAt index)).value state)
        indices := by
  refine Q'.eqv_trans _
    (listQSum
      (fun index =>
        if labellingsAgreeOnB
            (centralLowerFaceIds half) state (stateAt index)
        then coefficient index else 0)
      indices) _
    (centralPhysicalStateCylinderLinearCombination_value
      half stateAt coefficient state indices) ?_
  apply listQSum_congr_on
  intro index _hindex
  cases hagree : labellingsAgreeOnB
      (centralLowerFaceIds half) state (stateAt index) with
  | false =>
      simp only [centralPhysicalStateCylinderUnitObservable,
        hagree, Bool.false_eq_true, if_false]
      exact Q'.eqv_symm (Q'.mul_zero_eqv (coefficient index))
  | true =>
      simp only [centralPhysicalStateCylinderUnitObservable,
        hagree, if_true]
      exact Q'.eqv_symm (Q'.mul_one_eqv (coefficient index))

/-- Evaluation of every moving presentation is the evaluation of one fixed
raw cylinder plus its rational root correction times one fixed root cylinder.
This is the same-observable identity used by the Cauchy proof below. -/
theorem centralPhysicalVacuumSectorMovingCentered_value_equiv_expansion
    {w : Q'} (hw0 : (0 : Q') < w)
    (base half : Nat) (coefficient : Nat → Q') (stage : Nat)
    (state : EdgeLabelling) :
    let raw := centralPhysicalFiniteVacuumSectorLinearObservable
      w (Q'.le_of_lt hw0) base half coefficient
    let root := CentralPhysicalLinearObservable.atom
      (centralPhysicalStateCylinderUnitObservable half
        (centralPhysicalFiniteStateAt
          w (Q'.le_of_lt hw0) base half 0))
    (centralPhysicalVacuumSectorMovingCenteredPresentation
        hw0 base half coefficient stage).toLinearObservable.value state ≈
      raw.value state +
        (-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
          hw0 base half coefficient stage) * root.value state := by
  dsimp only
  let states := centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw0) base half
  let stateAt := centralPhysicalFiniteStateAt
    w (Q'.le_of_lt hw0) base half
  let weight := fun index =>
    (centralPhysicalStateCylinderUnitObservable
      half (stateAt index)).value state
  have hmoving := stateCylinderLinearCombination_value_eqv_weighted
    half stateAt
    (centralPhysicalVacuumSectorMovingCenteredPresentation
      hw0 base half coefficient stage).coefficient
    state states
  have hraw := stateCylinderLinearCombination_value_eqv_weighted
    half stateAt coefficient state states
  have hshift :=
    BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing.finiteListRootShiftedWeightedMean
      states weight coefficient
      (centralPhysicalFiniteVacuumSectorIndices_nodup
        w (Q'.le_of_lt hw0) base half)
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) base half)
      (-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
        hw0 base half coefficient stage)
  refine Q'.eqv_trans _ _ _ hmoving ?_
  refine Q'.eqv_trans _
    (listQSum (fun index => coefficient index * weight index) states +
      (-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
        hw0 base half coefficient stage) * weight 0) _ ?_ ?_
  · simpa only [
      centralPhysicalVacuumSectorMovingCenteredPresentation,
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient,
      finiteListRootCenteredCoefficient,
      centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox,
      weight, states] using hshift
  · exact Q'.add_eqv_congr'
      (Q'.eqv_symm hraw) (Q'.eqv_refl _)

/-! ## 2. Type-level squared-distance modulus -/

/-- A positive correction tolerance whose square is at most the requested
squared-distance tolerance. -/
def centralPhysicalMovingCenteringTolerance (epsilon : Q') : Q' :=
  Q'.min' epsilon 1

theorem centralPhysicalMovingCenteringTolerance_pos
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < centralPhysicalMovingCenteringTolerance epsilon := by
  unfold centralPhysicalMovingCenteringTolerance Q'.min'
  split
  · exact hepsilon
  · decide

theorem centralPhysicalMovingCenteringTolerance_le_epsilon
    (epsilon : Q') :
    centralPhysicalMovingCenteringTolerance epsilon ≤ epsilon := by
  unfold centralPhysicalMovingCenteringTolerance Q'.min'
  split
  · exact Q'.le_refl' epsilon
  · rename_i h
    exact Q'.le_of_not_le h

theorem centralPhysicalMovingCenteringTolerance_le_one
    (epsilon : Q') :
    centralPhysicalMovingCenteringTolerance epsilon ≤ 1 := by
  unfold centralPhysicalMovingCenteringTolerance Q'.min'
  split
  · assumption
  · exact Q'.le_refl' 1

/-- The executable completion modulus is the explicit quotient rate at the
small positive tolerance above. -/
def centralPhysicalVacuumSectorMovingCenteredRate
    {w : Q'} (hw0 : (0 : Q') < w)
    (base half : Nat) (coefficient : Nat → Q')
    (epsilon : Q') : Nat :=
  centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffRate
    hw0 base half coefficient
    (centralPhysicalMovingCenteringTolerance epsilon)

private theorem correctionDifference_sq_le
    {firstCorrection secondCorrection epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon)
    (hforward : firstCorrection ≤ secondCorrection +
      centralPhysicalMovingCenteringTolerance epsilon)
    (hbackward : secondCorrection ≤ firstCorrection +
      centralPhysicalMovingCenteringTolerance epsilon) :
    (firstCorrection + -secondCorrection) *
        (firstCorrection + -secondCorrection) ≤ epsilon := by
  let delta := firstCorrection + -secondCorrection
  let tolerance := centralPhysicalMovingCenteringTolerance epsilon
  have htolerance0 : (0 : Q') ≤ tolerance :=
    Q'.le_of_lt (centralPhysicalMovingCenteringTolerance_pos hepsilon)
  have habs : Q'.abs delta ≤ tolerance :=
    CReal.abs_sub_le_of_bounds hforward hbackward
  have hsquareAbs : delta * delta ≤ Q'.abs delta * Q'.abs delta :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (ExpNeg.abs_mul_le delta delta)
  have hfirst : Q'.abs delta * Q'.abs delta ≤
      tolerance * Q'.abs delta :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ habs
      (Q'.abs_nonneg delta)
  have hsecond : tolerance * Q'.abs delta ≤ tolerance * tolerance :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ habs htolerance0
  have hthird : tolerance * tolerance ≤ tolerance * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (centralPhysicalMovingCenteringTolerance_le_one epsilon)
      htolerance0
  exact Q'.le_trans' _ _ _ hsquareAbs
    (Q'.le_trans' _ _ _ hfirst
        (Q'.le_trans' _ _ _ hsecond
          (Q'.le_trans' _ _ _ hthird
            (Q'.le_trans' _ tolerance _
              (Q'.le_of_eqv (Q'.mul_one_eqv tolerance))
              (centralPhysicalMovingCenteringTolerance_le_epsilon epsilon)))))

/-- Two sufficiently late moving cylinders are pointwise close at the
requested squared scale. -/
theorem centralPhysicalVacuumSectorMovingCentered_pointwiseSq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q')
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (first second : Nat)
    (hfirst : centralPhysicalVacuumSectorMovingCenteredRate
      hw0 base half coefficient epsilon ≤ first)
    (hsecond : centralPhysicalVacuumSectorMovingCenteredRate
      hw0 base half coefficient epsilon ≤ second)
    (state : EdgeLabelling) :
    let left := (centralPhysicalVacuumSectorMovingCenteredPresentation
      hw0 base half coefficient first).toLinearObservable
    let right := (centralPhysicalVacuumSectorMovingCenteredPresentation
      hw0 base half coefficient second).toLinearObservable
    let difference := left.value state + -(right.value state)
    difference * difference ≤ epsilon := by
  dsimp only
  let left := (centralPhysicalVacuumSectorMovingCenteredPresentation
    hw0 base half coefficient first).toLinearObservable
  let right := (centralPhysicalVacuumSectorMovingCenteredPresentation
    hw0 base half coefficient second).toLinearObservable
  let difference := left.value state + -(right.value state)
  change difference * difference ≤ epsilon
  let firstCorrection :=
    centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
      hw0 base half coefficient first
  let secondCorrection :=
    centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
      hw0 base half coefficient second
  let delta := firstCorrection + -secondCorrection
  have hregular :=
    centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoff_regular
      hw0 hw1 base half coefficient
      (centralPhysicalMovingCenteringTolerance epsilon)
      (centralPhysicalMovingCenteringTolerance_pos hepsilon)
      first second hfirst hsecond
  have hdeltaSq : delta * delta ≤ epsilon :=
    correctionDifference_sq_le hepsilon hregular.1 hregular.2
  let raw := centralPhysicalFiniteVacuumSectorLinearObservable
    w (Q'.le_of_lt hw0) base half coefficient
  let rootUnit := centralPhysicalStateCylinderUnitObservable half
    (centralPhysicalFiniteStateAt
      w (Q'.le_of_lt hw0) base half 0)
  let root := CentralPhysicalLinearObservable.atom rootUnit
  let rootValue := rootUnit.value state
  have hleft : left.value state ≈
      raw.value state + (-firstCorrection) * root.value state := by
    simpa only [left, raw, root, rootUnit, firstCorrection] using
      (centralPhysicalVacuumSectorMovingCentered_value_equiv_expansion
        hw0 base half coefficient first state)
  have hright : right.value state ≈
      raw.value state + (-secondCorrection) * root.value state := by
    simpa only [right, raw, root, rootUnit, secondCorrection] using
      (centralPhysicalVacuumSectorMovingCentered_value_equiv_expansion
        hw0 base half coefficient second state)
  have haffine : difference ≈
      (raw.value state + (-firstCorrection) * root.value state) +
        -(raw.value state + (-secondCorrection) * root.value state) := by
    unfold difference
    exact Q'.add_eqv_congr' hleft
      (Q'.neg_eqv_congr _ _ hright)
  have hfactor : difference ≈
      (secondCorrection + -firstCorrection) * rootValue := by
    refine Q'.eqv_trans _ _ _ haffine ?_
    dsimp only [root, rootValue, CentralPhysicalLinearObservable.value]
    exact affineCorrectionDifference_eqv
      (raw.value state) firstCorrection secondCorrection rootValue
  have hsquareEqv : difference * difference ≈
      (delta * delta) * (rootValue * rootValue) := by
    refine Q'.eqv_trans _
      (((secondCorrection + -firstCorrection) * rootValue) * difference)
      _ ?_ ?_
    · exact Q'.mul_eqv_congr_right difference
        ((secondCorrection + -firstCorrection) * rootValue)
        difference hfactor
    refine Q'.eqv_trans _
      (((secondCorrection + -firstCorrection) * rootValue) *
        ((secondCorrection + -firstCorrection) * rootValue))
      _ ?_ ?_
    · exact Q'.mul_eqv_congr_left
        ((secondCorrection + -firstCorrection) * rootValue)
        difference
        ((secondCorrection + -firstCorrection) * rootValue)
        hfactor
    · dsimp only [delta]
      exact reversedCorrectionSquare_eqv
        firstCorrection secondCorrection rootValue
  have hroot0 : (0 : Q') ≤ rootValue := rootUnit.nonnegative state
  have hroot1 : rootValue ≤ (1 : Q') := rootUnit.le_one state
  have hrootSquare : rootValue * rootValue ≤ (1 : Q') := by
    refine Q'.le_trans' _ ((1 : Q') * rootValue) _ ?_ ?_
    · exact Q'.mul_le_mul_of_nonneg_right _ _ _ hroot1 hroot0
    refine Q'.le_trans' _ ((1 : Q') * 1) _ ?_ ?_
    · exact Q'.mul_le_mul_of_nonneg_left _ _ _ hroot1 (by decide)
    · exact Q'.le_of_eqv (Q'.one_mul_eqv 1)
  have hscaled : (delta * delta) * (rootValue * rootValue) ≤
      delta * delta := by
    refine Q'.le_trans' _ ((delta * delta) * 1) _ ?_ ?_
    · exact Q'.mul_le_mul_of_nonneg_left _ _ _ hrootSquare
        (SumOfSquares.q_mul_self_nonneg delta)
    · exact Q'.le_of_eqv (Q'.mul_one_eqv (delta * delta))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsquareEqv)
    (Q'.le_trans' _ _ _ hscaled hdeltaSq)

/-- The moving rationally centered presentations form an explicit-modulus
Cauchy representative in the actual cutoff-removed sector seminorm. -/
def centralPhysicalVacuumSectorMovingCenteredCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') :
    (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy where
  seq stage := centralPhysicalVacuumSectorMovingCenteredPresentation
    hw0 base half coefficient stage
  modulus := centralPhysicalVacuumSectorMovingCenteredRate
    hw0 base half coefficient
  isCauchy := by
    intro epsilon hepsilon first second hfirst hsecond
    change CReal.leEv
      (physicalLinearDistSq hw0 hw1 half
        (centralPhysicalVacuumSectorMovingCenteredPresentation
          hw0 base half coefficient first).toLinearObservable
        (centralPhysicalVacuumSectorMovingCenteredPresentation
          hw0 base half coefficient second).toLinearObservable)
      (CReal.ofQ' epsilon)
    exact physicalLinearDistSq_le_of_pointwise_sq
      hw0 hw1 half _ _ epsilon
      (centralPhysicalVacuumSectorMovingCentered_pointwiseSq
        hw0 hw1 base half coefficient epsilon hepsilon
        first second hfirst hsecond)

/-! ## 3. The actual completed vector -/

/-- The completed sector vector selected by the same moving rationally
centered observable at every stage. -/
def centralPhysicalVacuumSectorMovingCenteredCompletion
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') :
    CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half :=
  Quotient.mk
    (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).completionSetoid
    (centralPhysicalVacuumSectorMovingCenteredCauchy
      hw0 hw1 base half coefficient)

/-- The same vector in the actual global cutoff-removed physical
completion. -/
def centralPhysicalVacuumSectorMovingCenteredGlobalVector
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') :=
  centralPhysicalVacuumSectorCylinderCompletionToGlobal
    (centralPhysicalVacuumSectorMovingCenteredCompletion
      hw0 hw1 base half coefficient)

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion.centralPhysicalVacuumSectorMovingCentered_value_equiv_expansion
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion.centralPhysicalVacuumSectorMovingCentered_pointwiseSq
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion.centralPhysicalVacuumSectorMovingCenteredCauchy
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion.centralPhysicalVacuumSectorMovingCenteredCompletion
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion.centralPhysicalVacuumSectorMovingCenteredGlobalVector
