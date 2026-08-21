/-
# Raw-square/raw-mean compiler for the physical BF4 slow diagonal

Exact finite-volume centering changes a raw quadratic form by the square of
its stationary mean.  This module exposes the two raw comparisons that
therefore suffice for the centered slow-diagonal bridge:

* the raw finite square versus the projective reflected-square evaluator;
* the raw finite mean versus the projective vacuum-pairing evaluator.

For a continuum vacuum-orthogonal representative, the explicit Type-level
vacuum-pairing modulus then makes the finite mean small.  The exact centering
identity compiles these inputs into the already constructed centered
comparison and hence the completed operator gap.  The moving-diagonal raw
comparisons are constructed from fixed-observable moduli; those pointwise
moduli and the continuum measure remain explicit inputs.
-/

import YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison

namespace YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalDenseStageAdaptiveProjectiveComparison
open YMGap.Continuum.BF4PhysicalDenseStageCenteredSlowComparison
open YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
open YMGap.Continuum.BF4PhysicalDenseStageRawMomentModulus
open YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalModulatedGapLimitStability
open YMGap.Continuum.BF4PhysicalSelectedVacuumMeanConvergence
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4PhysicalVacuumPairingModulus
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

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

/-- Exact finite-stage identity: centered square equals raw square minus the
square of the raw stationary mean. -/
theorem finiteStageCenteredSquare_identity
    {family : MatchedBlockFamily}
    {coupling : Nat -> Q'}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (rawStageObservable : forall scale : Nat,
      D.wilson.toGNSData.V ->
        (MatchedPhysicalStageGNSData family coupling scale).V)
    (scale : Nat) (observable : D.wilson.toGNSData.V) :
    (finiteStageSquareExpectation D
        (matchedCenteredStageObservable D rawStageObservable)
        scale observable).eqv
      (finiteStageSquareExpectation D rawStageObservable scale observable +
        -(finiteStageRawMean D rawStageObservable scale observable *
          finiteStageRawMean D rawStageObservable scale observable)) := by
  exact centralPhysicalCenteredObservable_norm_identity
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (rawStageObservable scale observable)

/-! ## Rational error bookkeeping -/

/-- Three successive symmetric errors of size `p`, followed by a size-`p`
zero bound, give a size-`delta` zero bound whenever `3p <= delta`. -/
private theorem three_step_small
    (x y z p delta : Q')
    (hxy : x <= y + p /\ y <= x + p)
    (hyz : y <= z + p /\ z <= y + p)
    (hz : -p <= z /\ z <= p)
    (hthree : (p + p) + p <= delta) :
    -delta <= x /\ x <= delta := by
  have hupper1 : x <= (z + p) + p :=
    Q'.le_trans' _ _ _ hxy.1
      (Q'.add_le_add_right y (z + p) p hyz.1)
  have hupper2 : (z + p) + p <= (p + p) + p :=
    Q'.add_le_add_right (z + p) (p + p) p
      (Q'.add_le_add_right z p p hz.2)
  have hupper : x <= delta :=
    Q'.le_trans' _ _ _ hupper1
      (Q'.le_trans' _ _ _ hupper2 hthree)
  have hlowerChain : -p <= (x + p) + p :=
    Q'.le_trans' _ _ _ hz.1
      (Q'.le_trans' _ _ _ hyz.2
        (Q'.add_le_add_right y (x + p) p hxy.2))
  have hshift1 := Q'.add_le_add_right (-p) ((x + p) + p) (-p)
    hlowerChain
  have hshift2 := Q'.add_le_add_right
    ((-p) + (-p)) (((x + p) + p) + (-p)) (-p) hshift1
  have hleft : (((-p) + (-p)) + (-p)) ≈ -((p + p) + p) := by
    q_ring
  have hright : ((((x + p) + p) + (-p)) + (-p)) ≈ x := by
    refine Q'.eqv_trans _ ((x + p) + (p + (-p)) + (-p)) _ ?_ ?_
    · exact Q'.add_eqv_congr_right
        (((x + p) + p) + (-p)) ((x + p) + (p + (-p))) (-p)
        (Q'.add_assoc_eqv (x + p) p (-p))
    refine Q'.eqv_trans _ ((x + p) + 0 + (-p)) _ ?_ ?_
    · exact Q'.add_eqv_congr_right ((x + p) + (p + (-p)))
        ((x + p) + 0) (-p)
        (Q'.add_eqv_congr_left (x + p) (p + (-p)) 0
          (Q'.add_neg_self_eqv p))
    refine Q'.eqv_trans _ ((x + p) + (-p)) _ ?_ ?_
    · exact Q'.add_eqv_congr_right ((x + p) + 0) (x + p) (-p)
        (Q'.eqv_of_eq (Q'.add_zero' (x + p)))
    refine Q'.eqv_trans _ (x + (p + (-p))) _
      (Q'.add_assoc_eqv x p (-p)) ?_
    refine Q'.eqv_trans _ (x + 0) _
      (Q'.add_eqv_congr_left x (p + (-p)) 0
        (Q'.add_neg_self_eqv p)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' x)
  have hnegThree : -delta <= -((p + p) + p) :=
    Q'.neg_le_neg hthree
  have hlower : -delta <= x :=
    Q'.le_trans' _ _ _ hnegThree
      (le_of_eqv_le (Q'.eqv_symm hleft)
        (le_of_le_eqv hshift2 hright))
  exact ⟨hlower, hupper⟩

/-- A symmetric bound by `delta`, with `delta <= 1` and
`delta <= budget`, bounds the square by `budget`. -/
private theorem square_le_budget
    (x delta budget : Q')
    (hdelta0 : (0 : Q') <= delta)
    (hdelta1 : delta <= 1)
    (hdeltabudget : delta <= budget)
    (hx : -delta <= x /\ x <= delta) :
    x * x <= budget := by
  have hxx : x * x <= delta * delta :=
    Q'.mul_le_of_bounds hdelta0 hdelta0 hx.1 hx.2 hx.1 hx.2
  have hdd : delta * delta <= delta * 1 :=
    Q'.mul_le_mul_of_nonneg_left delta 1 delta hdelta1 hdelta0
  exact Q'.le_trans' _ _ _ hxx
    (Q'.le_trans' _ _ _
      (le_of_le_eqv hdd (Q'.mul_one_eqv delta)) hdeltabudget)

/-- Raw-square closeness plus a small squared mean implies centered-square
closeness with the full tolerance. -/
private theorem centered_close_of_raw_close_and_mean_square
    (centered raw mean rational epsilon : Q')
    (hcentered : centered ≈ raw + -(mean * mean))
    (hraw : raw <= rational + HalfPow.half * epsilon /\
      rational <= raw + HalfPow.half * epsilon)
    (hmeanSquare : mean * mean <= HalfPow.half * epsilon) :
    centered <= rational + epsilon /\ rational <= centered + epsilon := by
  let halfEpsilon := HalfPow.half * epsilon
  have hmeanSquare0 : (0 : Q') <= mean * mean :=
    SumOfSquares.q_mul_self_nonneg mean
  have hcenteredRaw : centered <= raw := by
    refine le_of_eqv_le hcentered ?_
    refine le_of_le_eqv
      (Q'.add_le_add_left raw (-(mean * mean)) 0
        (Q'.neg_le_neg hmeanSquare0)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' raw)
  have hhalf0 : (0 : Q') <= halfEpsilon := by
    exact Q'.le_trans' (0 : Q') (mean * mean) halfEpsilon
      hmeanSquare0 hmeanSquare
  have hhalfLe : halfEpsilon <= epsilon :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg halfEpsilon halfEpsilon hhalf0)
      (Q'.le_of_eqv (ExpNeg.two_halves epsilon))
  have hupper : centered <= rational + epsilon :=
    Q'.le_trans' _ _ _ hcenteredRaw
      (Q'.le_trans' _ _ _ hraw.1
        (Q'.add_le_add_left rational halfEpsilon epsilon hhalfLe))
  have hsplit : (raw + halfEpsilon) ≈
      (raw + -(mean * mean)) + (mean * mean + halfEpsilon) := by
    apply Q'.eqv_symm
    refine Q'.eqv_trans _
      (raw + (-(mean * mean) + (mean * mean + halfEpsilon))) _
      (Q'.add_assoc_eqv raw (-(mean * mean))
        (mean * mean + halfEpsilon)) ?_
    refine Q'.eqv_trans _
      (raw + (((-(mean * mean)) + (mean * mean)) + halfEpsilon)) _ ?_ ?_
    · exact Q'.add_eqv_congr_left raw _ _
        (Q'.eqv_symm
          (Q'.add_assoc_eqv (-(mean * mean)) (mean * mean) halfEpsilon))
    refine Q'.eqv_trans _ (raw + (0 + halfEpsilon)) _ ?_ ?_
    · exact Q'.add_eqv_congr_left raw _ _
        (Q'.add_eqv_congr_right
          ((-(mean * mean)) + (mean * mean)) 0 halfEpsilon
          (Q'.neg_add_self_eqv (mean * mean)))
    exact Q'.add_eqv_congr_left raw _ halfEpsilon
      (Q'.eqv_of_eq (Q'.zero_add' halfEpsilon))
  have hbudget : mean * mean + halfEpsilon <= epsilon :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_right (mean * mean) halfEpsilon halfEpsilon
        hmeanSquare)
      (Q'.le_of_eqv (ExpNeg.two_halves epsilon))
  have hcenteredLeft : raw + -(mean * mean) <= centered :=
    Q'.ge_of_eqv hcentered
  have hlower : rational <= centered + epsilon :=
    Q'.le_trans' _ _ _
      (le_of_le_eqv hraw.2 hsplit)
      (Q'.add_le_add hcenteredLeft hbudget)
  exact ⟨hupper, hlower⟩

/-! ## Primitive raw comparison interface -/

/-- The two primitive finite/projective estimates from which exact centering
constructs the vacuum-complement comparison.  Neither estimate assumes
vacuum orthogonality; that condition enters only through the explicit
representative vacuum-pairing modulus carried by `base`. -/
structure BF4WilsonDenseStageRawMeanSlowComparison
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type 3 where
  base : BF4WilsonDenseStageCenteredVacuumProjectiveBase producer D
  rawSquareComparisonRate : SelectedWilsonCauchy D -> Q' -> Nat
  rawSquareComparison : forall (X : SelectedWilsonCauchy D)
    (epsilon : Q'), (0 : Q') < epsilon ->
      forall scale : Nat, rawSquareComparisonRate X epsilon <= scale ->
        let index := base.sampleIndex X scale
        let a := X.seq index
        let Ta := D.timeTranslation.tau a
        let finiteA := finiteStageSquareExpectation D
          base.rawStageObservable scale a
        let finiteTa := finiteStageSquareExpectation D
          base.rawStageObservable scale Ta
        let rationalA := base.regularizedFunctional.stageExpectationQ
          scale (mu.pick scale) (continuumSquareObservable D a)
        let rationalTa := base.regularizedFunctional.stageExpectationQ
          scale (mu.pick scale) (continuumSquareObservable D Ta)
        (finiteA <= rationalA + epsilon /\
            rationalA <= finiteA + epsilon) /\
          (finiteTa <= rationalTa + epsilon /\
            rationalTa <= finiteTa + epsilon)
  rawMeanComparisonRate : SelectedWilsonCauchy D -> Q' -> Nat
  rawMeanComparison : forall (X : SelectedWilsonCauchy D)
    (epsilon : Q'), (0 : Q') < epsilon ->
      forall scale : Nat, rawMeanComparisonRate X epsilon <= scale ->
        let index := base.sampleIndex X scale
        let a := X.seq index
        let Ta := D.timeTranslation.tau a
        let finiteA := finiteStageRawMean D base.rawStageObservable scale a
        let finiteTa := finiteStageRawMean D base.rawStageObservable scale Ta
        let rationalA := base.regularizedFunctional.stageExpectationQ
          scale (mu.pick scale) (continuumVacuumPairingObservable D a)
        let rationalTa := base.regularizedFunctional.stageExpectationQ
          scale (mu.pick scale) (continuumVacuumPairingObservable D Ta)
        (finiteA <= rationalA + epsilon /\
            rationalA <= finiteA + epsilon) /\
          (finiteTa <= rationalTa + epsilon /\
            rationalTa <= finiteTa + epsilon)

namespace BF4WilsonDenseStageRawMeanSlowComparison

variable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}
    {producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (data : BF4WilsonDenseStageRawMeanSlowComparison producer D)

/-- A projective base carrying fixed-observable raw moment moduli constructs
both moving-diagonal raw comparisons. -/
def ofProjectiveBase
    (base : BF4WilsonDenseStageCenteredVacuumProjectiveBase producer D) :
    BF4WilsonDenseStageRawMeanSlowComparison producer D where
  base := base
  rawSquareComparisonRate := base.projectiveDiagonalRate
  rawSquareComparison := base.raw_square_diagonal_comparison
  rawMeanComparisonRate := base.projectiveDiagonalRate
  rawMeanComparison := base.raw_mean_diagonal_comparison

/-- Radius whose square is bounded by the half-error budget. -/
def meanRadius (epsilon : Q') : Q' :=
  Q'.invSucc (HalfPow.half * epsilon).den

/-- One quarter of the mean radius, allocated to each of the three mean
comparison errors. -/
def meanStepTolerance (epsilon : Q') : Q' :=
  HalfPow.half * (HalfPow.half * meanRadius epsilon)

/-- One outer rate paying the raw-square comparison, raw-mean comparison,
projective square/pairing moduli, and representative vacuum-pairing modulus. -/
def centeredComparisonRate (X : SelectedWilsonCauchy D)
    (epsilon : Q') : Nat :=
  let halfEpsilon := HalfPow.half * epsilon
  let meanStep := meanStepTolerance epsilon
  max (data.rawSquareComparisonRate X halfEpsilon)
    (max (data.rawMeanComparisonRate X meanStep)
      (max (data.base.projectiveDiagonalRate X meanStep)
        (data.base.vacuumPairingDiagonalRate X meanStep)))

/-- The primitive raw estimates compile to the centered comparison on the
continuum vacuum complement. -/
def toCenteredVacuumSlowComparison :
    BF4WilsonDenseStageCenteredVacuumSlowComparison producer D where
  base := data.base
  centeredComparisonRate := data.centeredComparisonRate
  centeredComparison := by
    intro X horthogonal epsilon hepsilon scale hscale
    let halfEpsilon := HalfPow.half * epsilon
    let delta := meanRadius epsilon
    let p := meanStepTolerance epsilon
    let index := data.base.sampleIndex X scale
    let a := X.seq index
    let Ta := D.timeTranslation.tau a
    have hhalf : (0 : Q') < halfEpsilon :=
      ExpNeg.half_mul_pos epsilon hepsilon
    have hdelta : (0 : Q') < delta := Q'.invSucc_pos _
    have hp : (0 : Q') < p :=
      ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos delta hdelta)
    have hrawSquareRate :
        data.rawSquareComparisonRate X halfEpsilon <= scale :=
      Nat.le_trans (Nat.le_max_left _ _) hscale
    have hrawMeanRate : data.rawMeanComparisonRate X p <= scale :=
      Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_max_right _ _) hscale)
    have hprojectiveRate :
        data.base.projectiveDiagonalRate X p <= scale :=
      Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_max_right _ _)
          (Nat.le_trans (Nat.le_max_right _ _) hscale))
    have hvacuumRate :
        data.base.vacuumPairingDiagonalRate X p <= scale :=
      Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_right _ _)
          (Nat.le_trans (Nat.le_max_right _ _) hscale))
    have hraw := data.rawSquareComparison X halfEpsilon hhalf
      scale hrawSquareRate
    have hmean := data.rawMeanComparison X p hp scale hrawMeanRate
    have hadmissible :=
      data.base.projective_pairing_diagonal_admissible X p hp scale
        hprojectiveRate
    have hprojectiveA := data.base.regularizedFunctional.bound
      (continuumVacuumPairingObservable D a) p hp scale hadmissible.1
    have hprojectiveTa := data.base.regularizedFunctional.bound
      (continuumVacuumPairingObservable D Ta) p hp scale hadmissible.2
    have hvacuum := data.base.vacuum_pairing_diagonal_small
      X horthogonal p hp scale hvacuumRate
    rw [← WilsonDenseUnitVacuumPairingModulus.pairing_eq_continuumVacuumPairingExpectation
      (D := D) a] at hprojectiveA
    rw [← WilsonDenseUnitVacuumPairingModulus.pairing_eq_continuumVacuumPairingExpectation
      (D := D) Ta] at hprojectiveTa
    have hp0 : (0 : Q') <= p := Q'.le_of_lt hp
    have hthree : (p + p) + p <= delta := by
      refine Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg ((p + p) + p) p hp0) ?_
      exact CReal.fourQ_le delta hdelta
    have hmeanSmallA :
        -delta <= finiteStageRawMean D data.base.rawStageObservable scale a /\
          finiteStageRawMean D data.base.rawStageObservable scale a <= delta :=
      three_step_small _ _ _ p delta hmean.1 hprojectiveA hvacuum.1 hthree
    have hmeanSmallTa :
        -delta <= finiteStageRawMean D data.base.rawStageObservable scale Ta /\
          finiteStageRawMean D data.base.rawStageObservable scale Ta <= delta :=
      three_step_small _ _ _ p delta hmean.2 hprojectiveTa hvacuum.2 hthree
    have hdelta0 : (0 : Q') <= delta := Q'.le_of_lt hdelta
    have hdelta1 : delta <= 1 := CReal.invSucc_le_one _
    have hdeltahalf : delta <= halfEpsilon :=
      HalfPow.invSucc_den_le halfEpsilon hhalf
    have hmeanSquareA :
        finiteStageRawMean D data.base.rawStageObservable scale a *
            finiteStageRawMean D data.base.rawStageObservable scale a <=
          halfEpsilon :=
      square_le_budget _ delta halfEpsilon hdelta0 hdelta1
        hdeltahalf hmeanSmallA
    have hmeanSquareTa :
        finiteStageRawMean D data.base.rawStageObservable scale Ta *
            finiteStageRawMean D data.base.rawStageObservable scale Ta <=
          halfEpsilon :=
      square_le_budget _ delta halfEpsilon hdelta0 hdelta1
        hdeltahalf hmeanSmallTa
    have hcenteredA := finiteStageCenteredSquare_identity
      D data.base.rawStageObservable scale a
    have hcenteredTa := finiteStageCenteredSquare_identity
      D data.base.rawStageObservable scale Ta
    dsimp only
    exact
      ⟨centered_close_of_raw_close_and_mean_square _ _ _ _ epsilon
          hcenteredA hraw.1 hmeanSquareA,
        centered_close_of_raw_close_and_mean_square _ _ _ _ epsilon
          hcenteredTa hraw.2 hmeanSquareTa⟩

/-- The raw square/mean frontier is sufficient for the selected completed
physical BF4 operator gap. -/
def toWilsonOperatorNormGapPin : WilsonOperatorNormGapPin D :=
  data.toCenteredVacuumSlowComparison.toWilsonOperatorNormGapPin

/-- The fixed-observable projective base is sufficient for the selected
completed physical BF4 operator gap. -/
def projectiveBase_toWilsonOperatorNormGapPin
    (base : BF4WilsonDenseStageCenteredVacuumProjectiveBase producer D) :
    WilsonOperatorNormGapPin D :=
  (ofProjectiveBase base).toWilsonOperatorNormGapPin

end BF4WilsonDenseStageRawMeanSlowComparison

end YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison

#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.finiteStageCenteredSquare_identity
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageRawMeanSlowComparison.ofProjectiveBase
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageRawMeanSlowComparison.toCenteredVacuumSlowComparison
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageRawMeanSlowComparison.toWilsonOperatorNormGapPin
#print axioms YMGap.Continuum.BF4PhysicalDenseStageRawMeanComparison.BF4WilsonDenseStageRawMeanSlowComparison.projectiveBase_toWilsonOperatorNormGapPin
