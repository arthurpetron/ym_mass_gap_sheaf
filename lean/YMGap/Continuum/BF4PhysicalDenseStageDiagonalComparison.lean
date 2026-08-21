/-
# Cofinal diagonal comparison for dense physical BF4 stages

The summable-variation compiler constructs a limit of the finite norm stream,
but still asks that this constructed real be identified with the selected
continuum Wilson norm.  Here that final pin is replaced by a direct, vanishing
comparison with the continuum dense norm at the same sampled representative.

The continuum `CauchyGNS` machinery already proves that its dense diagonal
norms converge to `cinnerRep X X`.  An explicit cofinal sampling rate preserves
that convergence.  An eventual two-sided comparison modulus then transfers
the limit to the finite BF4 norm stream.  Thus the selected continuum norm is
reached without postulating equality with a separately constructed limit.

The comparison modulus and dense maps remain analytic inputs.  This module
does not construct the continuum measure or the comparison estimate.
-/

import YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler

namespace YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalModulatedGapLimitStability
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-! ## 1. Generic constructive convergence transport -/

/-- Type-level eventual two-sided closeness of two constructive-real
sequences.  Both the outer stage and inner approximation threshold are
explicit data. -/
structure CRealEventuallyClose (left right : Nat -> CReal) : Type 1 where
  stageRate : Q' -> Nat
  approxRate : Q' -> Nat -> Nat
  close : forall epsilon : Q', (0 : Q') < epsilon ->
    forall stage : Nat, stageRate epsilon <= stage ->
      forall k : Nat, approxRate epsilon stage <= k ->
        (left stage).approx k <= (right stage).approx k + epsilon /\
        (right stage).approx k <= (left stage).approx k + epsilon

/-- A uniformly cofinal reindexing preserves convergence. -/
theorem convergesTo_cofinalReindex
    {sequence : Nat -> CReal} {limit : CReal}
    (hconverges : CReal.ConvergesTo sequence limit)
    (index : Nat -> Nat) (cofinalRate : Nat -> Nat)
    (hcofinal : forall threshold stage : Nat,
      cofinalRate threshold <= stage -> threshold <= index stage) :
    CReal.ConvergesTo (fun stage => sequence (index stage)) limit := by
  intro epsilon hepsilon
  obtain ⟨threshold, hthreshold⟩ := hconverges epsilon hepsilon
  exact ⟨cofinalRate threshold, fun stage hstage =>
    hthreshold (index stage) (hcofinal threshold stage hstage)⟩

/-- Eventual two-sided closeness transfers a known limit from the right
sequence to the left sequence. -/
theorem convergesTo_of_eventuallyClose
    {left right : Nat -> CReal} {limit : CReal}
    (hclose : CRealEventuallyClose left right)
    (hright : CReal.ConvergesTo right limit) :
    CReal.ConvergesTo left limit := by
  intro epsilon hepsilon
  let halfEpsilon : Q' := HalfPow.half * epsilon
  have hhalf : (0 : Q') < halfEpsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨rightStage, hrightStage⟩ := hright halfEpsilon hhalf
  refine ⟨max rightStage (hclose.stageRate halfEpsilon),
    fun stage hstage => ?_⟩
  have hrightStage' : rightStage <= stage :=
    Nat.le_trans (Nat.le_max_left _ _) hstage
  have hcloseStage : hclose.stageRate halfEpsilon <= stage :=
    Nat.le_trans (Nat.le_max_right _ _) hstage
  obtain ⟨rightApprox, hrightApprox⟩ :=
    hrightStage stage hrightStage'
  refine ⟨max rightApprox (hclose.approxRate halfEpsilon stage),
    fun k hk => ?_⟩
  have hkRight : rightApprox <= k :=
    Nat.le_trans (Nat.le_max_left _ _) hk
  have hkClose : hclose.approxRate halfEpsilon stage <= k :=
    Nat.le_trans (Nat.le_max_right _ _) hk
  obtain ⟨hrl, hlr⟩ := hrightApprox k hkRight
  obtain ⟨hleftRight, hrightLeft⟩ :=
    hclose.close halfEpsilon hhalf stage hcloseStage k hkClose
  have htwice : (halfEpsilon + halfEpsilon).eqv epsilon := by
    exact ExpNeg.two_halves epsilon
  constructor
  · have hchain : (left stage).approx k <=
        (limit.approx k + halfEpsilon) + halfEpsilon :=
      Q'.le_trans' _ _ _ hleftRight
        (Q'.add_le_add_right _ _ halfEpsilon hrl)
    refine le_of_le_eqv hchain ?_
    exact Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (limit.approx k) halfEpsilon halfEpsilon)
      (Q'.add_eqv_congr_left (limit.approx k)
        (halfEpsilon + halfEpsilon) epsilon htwice)
  · have hchain : limit.approx k <=
        ((left stage).approx k + halfEpsilon) + halfEpsilon :=
      Q'.le_trans' _ _ _ hlr
        (Q'.add_le_add_right _ _ halfEpsilon hrightLeft)
    refine le_of_le_eqv hchain ?_
    exact Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv ((left stage).approx k) halfEpsilon halfEpsilon)
      (Q'.add_eqv_congr_left ((left stage).approx k)
        (halfEpsilon + halfEpsilon) epsilon htwice)

/-! ## 2. The continuum dense diagonal -/

/-- The continuum dense squared norm sampled along the same diagonal used by
the finite BF4 stage map. -/
def continuumDenseNormSequence
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (sampleIndex : Nat -> Nat) (X : SelectedWilsonCauchy D) : Nat -> CReal :=
  fun scale => CReal.ofQ'
    (D.wilson.toGNSData.cInnerSeq X X (sampleIndex scale))

/-- Cofinal sampling of a continuum Cauchy representative's dense norm
converges to its completed representative norm. -/
theorem continuumDenseNormSequence_converges
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (sampleIndex cofinalRate : Nat -> Nat)
    (hcofinal : forall threshold scale : Nat,
      cofinalRate threshold <= scale -> threshold <= sampleIndex scale)
    (X : SelectedWilsonCauchy D) :
    CReal.ConvergesTo (continuumDenseNormSequence D sampleIndex X)
      (D.wilson.toGNSData.cinnerRep X X) := by
  exact convergesTo_cofinalReindex
    (CReal.convergesTo_ofQ'CauchySeq
      (D.wilson.toGNSData.cInnerSeq X X)
      (D.wilson.toGNSData.cInnerQCauchy X X))
    sampleIndex cofinalRate hcofinal

/-! ## 3. Finite-to-continuum diagonal comparison -/

/-- Dense-stage approximation data with the residual norm identification
replaced by a vanishing comparison against the already-selected continuum
dense norm.

The cofinality law is uniform past the explicit `sampleRate threshold`, and
`normClose` supplies both outer and inner comparison moduli. -/
structure BF4WilsonDenseStageDiagonalComparison
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    extends BF4WilsonDenseStageMapData producer D where
  sampleRate : Nat -> Nat
  sampleIndex_cofinal : forall threshold scale : Nat,
    sampleRate threshold <= scale -> threshold <= sampleIndex scale
  normClose : forall X : SelectedWilsonCauchy D,
    CRealEventuallyClose
      (denseStageNormSequence D sampleIndex stageObservable X)
      (continuumDenseNormSequence D sampleIndex X)

namespace BF4WilsonDenseStageDiagonalComparison

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
    (data : BF4WilsonDenseStageDiagonalComparison producer D)

/-- The finite dense-stage norm converges to the selected continuum norm by
the two-leg diagonal comparison. -/
theorem norm_converges (X : SelectedWilsonCauchy D) :
    CReal.ConvergesTo
      (denseStageNormSequence D data.sampleIndex data.stageObservable X)
      (D.wilson.toGNSData.cinnerRep X X) :=
  convergesTo_of_eventuallyClose (data.normClose X)
    (continuumDenseNormSequence_converges D data.sampleIndex data.sampleRate
      data.sampleIndex_cofinal X)

/-- The finite transfer image is null-equivalent to the finite dense-stage
image of the selected pointwise continuum lift. -/
theorem transferredApproximant_null
    (X : SelectedWilsonCauchy D) (scale : Nat) :
    CauchyNull (MatchedPhysicalStageGNSData family coupling scale)
      (matchedPhysicalStageTransferCauchy family coupling scale
        (denseStageApproximant D data.sampleIndex data.stageObservable X scale))
      (denseStageApproximant D data.sampleIndex data.stageObservable
        (data.pointwiseTimeTranslation.linear.linearOperator.TCauchy X)
        scale) := by
  intro epsilon hepsilon
  refine ⟨0, fun n _ => ?_⟩
  apply le_of_eqv_le _ (Q'.le_of_lt hepsilon)
  apply rad_of_veq
  change (MatchedPhysicalStageGNSData family coupling scale).veq
    (centralPhysicalMarkovApply
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0
      (data.stageObservable scale (X.seq (data.sampleIndex scale))))
    (data.stageObservable scale
      ((data.pointwiseTimeTranslation.linear.linearOperator.TCauchy X).seq
        (data.sampleIndex scale)))
  exact (MatchedPhysicalStageGNSData family coupling scale).veq_trans
    (data.stageTransfer_intertwines scale
      (X.seq (data.sampleIndex scale)))
    ((MatchedPhysicalStageGNSData family coupling scale).veq_symm
      (data.stageObservable_congr scale
        (data.pointwiseTimeTranslation.pointwise X
          (data.sampleIndex scale))))

/-- Scale-by-scale equivalence of the transferred finite norm and the ordinary
finite norm of `TCauchy X`. -/
theorem transferredStageNorm_equiv
    (X : SelectedWilsonCauchy D) (scale : Nat) :
    CReal.Equiv
      (matchedPhysicalStageTransferredNorm family coupling scale
        (denseStageApproximant D data.sampleIndex data.stageObservable X scale))
      (denseStageNormSequence D data.sampleIndex data.stageObservable
        (data.pointwiseTimeTranslation.linear.linearOperator.TCauchy X) scale) :=
  (MatchedPhysicalStageGNSData family coupling scale).cinnerRep_welldef
    _ _ _ _ (data.transferredApproximant_null X scale)
      (data.transferredApproximant_null X scale)

/-- The same diagonal comparison applied to `TCauchy X`, together with exact
intertwining, proves transferred-norm convergence. -/
theorem transferredNorm_converges (X : SelectedWilsonCauchy D) :
    CReal.ConvergesTo
      (fun scale => matchedPhysicalStageTransferredNorm family coupling scale
        (denseStageApproximant D data.sampleIndex data.stageObservable X scale))
      (D.wilson.toGNSData.cinnerRep
        (data.pointwiseTimeTranslation.linear.linearOperator.TCauchy X)
        (data.pointwiseTimeTranslation.linear.linearOperator.TCauchy X)) := by
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (fun scale => CReal.Equiv.symm (data.transferredStageNorm_equiv X scale))
  exact data.norm_converges
    (data.pointwiseTimeTranslation.linear.linearOperator.TCauchy X)

/-- The diagonal comparison constructs the full linear graph-norm limit
record without a separate continuum norm-limit pin. -/
def toLinearGraphNormLimitApproximation :
    BF4WilsonLinearGraphNormLimitApproximation producer D where
  separatorPinned := data.separatorPinned
  linearTimeTranslation := data.pointwiseTimeTranslation.linear
  approximant := denseStageApproximant D data.sampleIndex data.stageObservable
  approximant_vacuumOrthogonal := data.stage_vacuumOrthogonal
  norm_converges := data.norm_converges
  transferredNorm_converges := data.transferredNorm_converges

/-- The cofinal diagonal comparison therefore constructs the selected
continuum Wilson operator norm gap. -/
def toWilsonOperatorNormGapPin : WilsonOperatorNormGapPin D :=
  data.toLinearGraphNormLimitApproximation.toWilsonOperatorNormGapPin

end BF4WilsonDenseStageDiagonalComparison

end YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison

#print axioms YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison.convergesTo_cofinalReindex
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison.convergesTo_of_eventuallyClose
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison.continuumDenseNormSequence_converges
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison.BF4WilsonDenseStageDiagonalComparison.norm_converges
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison.BF4WilsonDenseStageDiagonalComparison.transferredApproximant_null
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison.BF4WilsonDenseStageDiagonalComparison.transferredNorm_converges
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison.BF4WilsonDenseStageDiagonalComparison.toLinearGraphNormLimitApproximation
#print axioms YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison.BF4WilsonDenseStageDiagonalComparison.toWilsonOperatorNormGapPin
