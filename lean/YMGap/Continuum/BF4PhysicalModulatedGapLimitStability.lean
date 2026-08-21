/-
# Constructive limit stability of the physical BF4 operator gap

At every matched cutoff, a `BF4QuarterPhysicalSeparatorProducer` gives the
choice-free modulated completion a squared-norm contraction of rate
`(1/16)^2` on the vacuum complement.  This file isolates the exact data needed
to pass that inequality to a selected continuum Wilson transfer.

The bridge is deliberately graph-norm based.  For every selected continuum
vector it supplies explicit `CauchyGNS` representatives at every cutoff,
preserves vacuum orthogonality, and gives constructive convergence both of the
ordinary squared norms and of the transferred squared norms.  The continuum
real representatives are pinned to the actual Wilson inner products.  Thus
the continuum operator gap is derived from finite inequalities and two limit
proofs; it is not a field of the bridge.

No such approximation system, continuum measure, OS reconstruction, or
physical BF4 producer is constructed here.  In particular this is a
limit-stability compiler, not continuum Yang--Mills existence and not the Clay
mass-gap theorem.
-/

import YMGap.Continuum.BF4PhysicalModulatedOperatorNormGap
import YMGap.Continuum.BF4FarautPhysicalSeparatorProducer
import YMGap.Continuum.FCNormBoundLimit
import YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

namespace YMGap.Continuum.BF4PhysicalModulatedGapLimitStability

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4FarautPhysicalSeparatorProducer
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalMarkovModulusCompletion
open YMGap.Continuum.BF4PhysicalModulatedOperatorNormGap
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-! ## 1. Explicit representatives of the varying finite carriers -/

/-- The strict macro-transfer norm rate supplied by the BF4 four-cell
decomposition. -/
def bf4MacroNormRate : Q' := Q'.mkPos 1 16 (by decide)

/-- The corresponding squared-norm rate. -/
def bf4MacroSquaredNormRate : Q' := bf4MacroNormRate * bf4MacroNormRate

/-- The rational GNS datum at one member of the matched cutoff family. -/
abbrev MatchedPhysicalStageGNSData
    (family : MatchedBlockFamily) (coupling : Nat -> Q') (scale : Nat) :
    GNSData :=
  (centralPhysicalSmulGNS
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0).toGNSData

/-- A Type-level Cauchy representative of one vector at one matched cutoff. -/
abbrev MatchedPhysicalStageCauchy
    (family : MatchedBlockFamily) (coupling : Nat -> Q') (scale : Nat) : Type :=
  CauchyGNS (MatchedPhysicalStageGNSData family coupling scale)

/-- The modulated completion point represented by an explicit stage Cauchy
sequence.  No quotient representative is selected. -/
def matchedPhysicalStagePoint
    (family : MatchedBlockFamily) (coupling : Nat -> Q') (scale : Nat)
    (X : MatchedPhysicalStageCauchy family coupling scale) :
    CentralPhysicalModulatedGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 :=
  Quotient.mk
    (modulatedCauchySetoid
      (MatchedPhysicalStageGNSData family coupling scale)) X

/-- Apply the concrete physical macro transfer to an explicit stage
representative. -/
def matchedPhysicalStageTransferCauchy
    (family : MatchedBlockFamily) (coupling : Nat -> Q') (scale : Nat)
    (X : MatchedPhysicalStageCauchy family coupling scale) :
    MatchedPhysicalStageCauchy family coupling scale :=
  (centralPhysicalMarkovSymbol
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0).cDiagCauchy X

/-- A literal `CReal` representative of the stage squared norm. -/
def matchedPhysicalStageNorm
    (family : MatchedBlockFamily) (coupling : Nat -> Q') (scale : Nat)
    (X : MatchedPhysicalStageCauchy family coupling scale) : CReal :=
  (MatchedPhysicalStageGNSData family coupling scale).cinnerRep X X

/-- A literal `CReal` representative of the transferred stage squared norm. -/
def matchedPhysicalStageTransferredNorm
    (family : MatchedBlockFamily) (coupling : Nat -> Q') (scale : Nat)
    (X : MatchedPhysicalStageCauchy family coupling scale) : CReal :=
  (MatchedPhysicalStageGNSData family coupling scale).cinnerRep
    (matchedPhysicalStageTransferCauchy family coupling scale X)
    (matchedPhysicalStageTransferCauchy family coupling scale X)

/-- The completed modulated operator gap, specialized to an explicit
representative, is an inequality between its literal `CReal` norm streams. -/
theorem matchedPhysicalStage_operator_norm_gap_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat)
    (X : MatchedPhysicalStageCauchy family coupling scale)
    (horthogonal : CentralPhysicalModulatedVacuumOrthogonal
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0
      (matchedPhysicalStagePoint family coupling scale X)) :
    CReal.leEv
      (matchedPhysicalStageTransferredNorm family coupling scale X)
      (CReal.mul (CReal.ofQ' bf4MacroSquaredNormRate)
        (matchedPhysicalStageNorm family coupling scale X)) := by
  have hgap := producer_modulated_vacuum_operator_norm_gap_sixteenth
    producer scale (matchedPhysicalStagePoint family coupling scale X)
      horthogonal
  change CReal.RCle
    (Quotient.mk CReal.crealSetoid
      (matchedPhysicalStageTransferredNorm family coupling scale X))
    (CReal.RCscale bf4MacroSquaredNormRate
      (Quotient.mk CReal.crealSetoid
        (matchedPhysicalStageNorm family coupling scale X))) at hgap
  rw [CReal.RCscale_mk, CReal.RCle_mk] at hgap
  exact hgap

/-! ## 2. The graph-norm limit interface -/

/-- Explicit varying-cutoff approximation data sufficient to transport the
finite physical BF4 macro gap to the selected continuum Wilson transfer.

The two convergence fields are the graph-norm compatibility law: the same
stage representative controls both the vector norm and its image under the
actual finite macro transfer.  The two class pins identify the chosen limit
representatives with the actual continuum Wilson inner products. -/
structure BF4WilsonGraphNormLimitApproximation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type 3 where
  /-- The selected continuum Wilson separator is the finite macro rate.  A
  physical-time interpretation of that macro remains a separate obligation. -/
  separatorPinned : D.selectedSpectralData.gap.sep = bf4MacroNormRate
  /-- Explicit finite representative approximating each continuum vector. -/
  approximant : forall
    _x : D.wilson.toGNSData.gnsComplete.hilbert.carrier,
    (scale : Nat) -> MatchedPhysicalStageCauchy family coupling scale
  /-- Continuum vacuum-complement vectors are approximated within every
  finite vacuum complement, so the finite strict estimate applies. -/
  approximant_vacuumOrthogonal : forall
    (x : D.wilson.toGNSData.gnsComplete.hilbert.carrier),
    D.selectedSpectralData.vacPerp x -> forall scale : Nat,
      CentralPhysicalModulatedVacuumOrthogonal
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
        (matchedPhysicalStagePoint family coupling scale
          (approximant x scale))
  /-- A selected constructive-real representative of the continuum norm. -/
  normRepresentative :
    D.wilson.toGNSData.gnsComplete.hilbert.carrier -> CReal
  /-- A selected constructive-real representative of the transferred
  continuum norm. -/
  transferredNormRepresentative :
    D.wilson.toGNSData.gnsComplete.hilbert.carrier -> CReal
  /-- The selected representative denotes the actual continuum squared norm. -/
  normRepresentative_class : forall x,
    Quotient.mk CReal.crealSetoid (normRepresentative x) =
      D.wilson.toGNSData.gnsComplete.hilbert.cinner x x
  /-- The second representative denotes the squared norm of the actual
  selected continuum Wilson transfer. -/
  transferredNormRepresentative_class : forall x,
    Quotient.mk CReal.crealSetoid (transferredNormRepresentative x) =
      D.wilson.toGNSData.gnsComplete.hilbert.cinner
        (D.timeTranslation.op.T x) (D.timeTranslation.op.T x)
  /-- Effective convergence of finite squared norms. -/
  norm_converges : forall x,
    CReal.ConvergesTo
      (fun scale => matchedPhysicalStageNorm family coupling scale
        (approximant x scale))
      (normRepresentative x)
  /-- Effective convergence of the matching finite transferred norms to the
  norm of the actual continuum transfer. -/
  transferredNorm_converges : forall x,
    CReal.ConvergesTo
      (fun scale => matchedPhysicalStageTransferredNorm family coupling scale
        (approximant x scale))
      (transferredNormRepresentative x)

namespace BF4WilsonGraphNormLimitApproximation

/-- The uniform stage inequality survives in the two selected continuum norm
representatives. -/
theorem limit_operator_norm_gap_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}
    {producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (data : BF4WilsonGraphNormLimitApproximation producer D)
    (x : D.wilson.toGNSData.gnsComplete.hilbert.carrier)
    (horthogonal : D.selectedSpectralData.vacPerp x) :
    CReal.leEv (data.transferredNormRepresentative x)
      (CReal.mul (CReal.ofQ' bf4MacroSquaredNormRate)
        (data.normRepresentative x)) := by
  apply CReal.leEv_of_convergesTo_le
    (data.transferredNorm_converges x)
    (CReal.convergesTo_constMul bf4MacroSquaredNormRate
      (data.norm_converges x))
  intro scale
  exact matchedPhysicalStage_operator_norm_gap_sixteenth
    producer scale (data.approximant x scale)
      (data.approximant_vacuumOrthogonal x horthogonal scale)

/-- **Finite-to-continuum operator-gap compiler.**  The graph-norm
approximation data construct the existing minimal Wilson operator-gap pin;
the pin is not assumed. -/
def toWilsonOperatorNormGapPin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}
    {producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (data : BF4WilsonGraphNormLimitApproximation producer D) :
    WilsonOperatorNormGapPin D where
  normGap := by
    intro x horthogonal
    rw [<- data.transferredNormRepresentative_class x,
      <- data.normRepresentative_class x, data.separatorPinned]
    change CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (data.transferredNormRepresentative x))
      (CReal.RCscale bf4MacroSquaredNormRate
        (Quotient.mk CReal.crealSetoid (data.normRepresentative x)))
    rw [CReal.RCscale_mk, CReal.RCle_mk]
    exact data.limit_operator_norm_gap_sixteenth x horthogonal

end BF4WilsonGraphNormLimitApproximation

/-! ## 3. Choice-free representative-level graph-norm limits -/

/-- An explicit Cauchy representative of the selected continuum Wilson
completion. -/
abbrev SelectedWilsonCauchy
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type :=
  CauchyGNS D.wilson.toGNSData

/-- The continuum completion point denoted by an explicit representative. -/
def selectedWilsonPoint
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) (X : SelectedWilsonCauchy D) :
    D.wilson.toGNSData.gnsComplete.hilbert.carrier :=
  Quotient.mk (cauchySetoid D.wilson.toGNSData) X

/-- Choice-free graph-norm approximation data indexed by explicit continuum
Cauchy representatives.

Unlike `BF4WilsonGraphNormLimitApproximation`, this record never maps an
arbitrary quotient point into a Type-valued family of finite representatives.
It instead supplies finite approximants for each already-explicit continuum
representative.  The additional `transferredRepresentative` field is the
honest representative-level lift of the selected continuum transfer.  The
quotient-level norm gap is then proved by quotient induction into `Prop`. -/
structure BF4WilsonRepresentativeGraphNormLimitApproximation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type 3 where
  separatorPinned : D.selectedSpectralData.gap.sep = bf4MacroNormRate
  /-- A representative-level lift of the actual selected continuum
  time-translation operator. -/
  transferredRepresentative :
    SelectedWilsonCauchy D -> SelectedWilsonCauchy D
  /-- The lift represents exactly the quotient-level continuum transfer. -/
  transferredRepresentative_class : forall X,
    selectedWilsonPoint D (transferredRepresentative X) =
      D.timeTranslation.op.T (selectedWilsonPoint D X)
  /-- Explicit finite representatives approximating one explicit continuum
  representative at every cutoff. -/
  approximant : forall _X : SelectedWilsonCauchy D,
    (scale : Nat) -> MatchedPhysicalStageCauchy family coupling scale
  /-- Vacuum orthogonality descends to every finite approximant. -/
  approximant_vacuumOrthogonal : forall
    (X : SelectedWilsonCauchy D),
    D.selectedSpectralData.vacPerp (selectedWilsonPoint D X) ->
      forall scale : Nat,
        CentralPhysicalModulatedVacuumOrthogonal
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (matchedPhysicalStagePoint family coupling scale
            (approximant X scale))
  /-- Finite squared norms converge to the literal inner-product representative
  of the selected continuum Cauchy sequence. -/
  norm_converges : forall X,
    CReal.ConvergesTo
      (fun scale => matchedPhysicalStageNorm family coupling scale
        (approximant X scale))
      (D.wilson.toGNSData.cinnerRep X X)
  /-- The transferred finite squared norms converge to the literal inner
  representative of the supplied continuum transfer lift. -/
  transferredNorm_converges : forall X,
    CReal.ConvergesTo
      (fun scale => matchedPhysicalStageTransferredNorm family coupling scale
        (approximant X scale))
      (D.wilson.toGNSData.cinnerRep
        (transferredRepresentative X) (transferredRepresentative X))

namespace BF4WilsonRepresentativeGraphNormLimitApproximation

/-- Representative-level finite-to-limit preservation of the strict BF4
operator norm gap. -/
theorem representative_limit_operator_norm_gap_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}
    {producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (data : BF4WilsonRepresentativeGraphNormLimitApproximation producer D)
    (X : SelectedWilsonCauchy D)
    (horthogonal :
      D.selectedSpectralData.vacPerp (selectedWilsonPoint D X)) :
    CReal.leEv
      (D.wilson.toGNSData.cinnerRep
        (data.transferredRepresentative X)
        (data.transferredRepresentative X))
      (CReal.mul (CReal.ofQ' bf4MacroSquaredNormRate)
        (D.wilson.toGNSData.cinnerRep X X)) := by
  apply CReal.leEv_of_convergesTo_le
    (data.transferredNorm_converges X)
    (CReal.convergesTo_constMul bf4MacroSquaredNormRate
      (data.norm_converges X))
  intro scale
  exact matchedPhysicalStage_operator_norm_gap_sixteenth
    producer scale (data.approximant X scale)
      (data.approximant_vacuumOrthogonal X horthogonal scale)

/-- **Choice-free quotient compiler.**  Representative graph-norm limits
construct the Wilson operator-gap pin for every quotient vector by induction
into the proposition expressing the norm inequality. -/
def toWilsonOperatorNormGapPin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}
    {producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (data : BF4WilsonRepresentativeGraphNormLimitApproximation producer D) :
    WilsonOperatorNormGapPin D where
  normGap := by
    intro vector
    refine Quotient.inductionOn vector ?_
    intro X horthogonal
    change CReal.RCle
      (D.wilson.toGNSData.gnsComplete.hilbert.cinner
        (D.timeTranslation.op.T (selectedWilsonPoint D X))
        (D.timeTranslation.op.T (selectedWilsonPoint D X)))
      (CReal.RCscale
        (D.selectedSpectralData.gap.sep * D.selectedSpectralData.gap.sep)
        (D.wilson.toGNSData.gnsComplete.hilbert.cinner
          (selectedWilsonPoint D X) (selectedWilsonPoint D X)))
    rw [<- data.transferredRepresentative_class X]
    change CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (D.wilson.toGNSData.cinnerRep
          (data.transferredRepresentative X)
          (data.transferredRepresentative X)))
      (CReal.RCscale
        (D.selectedSpectralData.gap.sep * D.selectedSpectralData.gap.sep)
        (Quotient.mk CReal.crealSetoid
          (D.wilson.toGNSData.cinnerRep X X)))
    rw [data.separatorPinned]
    change CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (D.wilson.toGNSData.cinnerRep
          (data.transferredRepresentative X)
          (data.transferredRepresentative X)))
      (CReal.RCscale bf4MacroSquaredNormRate
        (Quotient.mk CReal.crealSetoid
          (D.wilson.toGNSData.cinnerRep X X)))
    rw [CReal.RCscale_mk, CReal.RCle_mk]
    exact data.representative_limit_operator_norm_gap_sixteenth X horthogonal

end BF4WilsonRepresentativeGraphNormLimitApproximation

/-! ## 4. AF/Faraut specialization -/

/-- The reduced AF/Faraut producer feeds the same limit compiler through its
already-constructed general physical producer. -/
def farautGraphNormLimit_toWilsonOperatorNormGapPin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (data : BF4WilsonGraphNormLimitApproximation
      producer.toBF4QuarterPhysicalSeparatorProducer D) :
    WilsonOperatorNormGapPin D :=
  data.toWilsonOperatorNormGapPin

/-- Choice-free AF/Faraut specialization using explicit continuum
representatives and quotient induction. -/
def farautRepresentativeGraphNormLimit_toWilsonOperatorNormGapPin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (data : BF4WilsonRepresentativeGraphNormLimitApproximation
      producer.toBF4QuarterPhysicalSeparatorProducer D) :
    WilsonOperatorNormGapPin D :=
  data.toWilsonOperatorNormGapPin

end YMGap.Continuum.BF4PhysicalModulatedGapLimitStability

#print axioms YMGap.Continuum.BF4PhysicalModulatedGapLimitStability.matchedPhysicalStage_operator_norm_gap_sixteenth
#print axioms YMGap.Continuum.BF4PhysicalModulatedGapLimitStability.BF4WilsonGraphNormLimitApproximation.limit_operator_norm_gap_sixteenth
#print axioms YMGap.Continuum.BF4PhysicalModulatedGapLimitStability.BF4WilsonGraphNormLimitApproximation.toWilsonOperatorNormGapPin
#print axioms YMGap.Continuum.BF4PhysicalModulatedGapLimitStability.farautGraphNormLimit_toWilsonOperatorNormGapPin
#print axioms YMGap.Continuum.BF4PhysicalModulatedGapLimitStability.BF4WilsonRepresentativeGraphNormLimitApproximation.representative_limit_operator_norm_gap_sixteenth
#print axioms YMGap.Continuum.BF4PhysicalModulatedGapLimitStability.BF4WilsonRepresentativeGraphNormLimitApproximation.toWilsonOperatorNormGapPin
#print axioms YMGap.Continuum.BF4PhysicalModulatedGapLimitStability.farautRepresentativeGraphNormLimit_toWilsonOperatorNormGapPin
