/-
# A scale-indexed same-observable path through embedded positive-time sectors

An exact finite positive-time calculation is useful downstream only if its
carrier, vacuum, transfer, and observable remain the same objects when the
calculation is embedded in the interacting Wilson completion.  Repeating such
a calculation at several cutoffs adds a second obligation: every stage must
realize one shared observable label, rather than choosing a new favorable
vector after seeing the cutoff.

This file factors those two obligations.  `EmbeddedPositiveTimeObservableSector`
transports a source transfer path through a Gram-preserving completion map and
derives the ambient vacuum-orthogonality and matrix-coefficient identities.
`CompletedPositiveTimeObservableTrajectory` then indexes such sectors by the
cutoff while pinning their ambient representatives to one shared observable.
The canonical quaternion two-mode calculation supplies a concrete constant
trajectory, showing that the interface is non-vacuous.

The constant canonical trajectory is not a shrinking-lattice or BF4/AF
trajectory.  Instantiating this interface with the physical cutoff family and
proving variation of its exact same-observable moments remain separate open
steps.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.SU2QuaternionCanonicalEightCompletedPositiveTimeSector
import YMGap.Continuum.SummableRationalStepVariation

namespace YMGap.Continuum.CompletedPositiveTimeObservableTrajectory

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BoundedTransferCalculus
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2QuaternionCanonicalEightCarrier
open YMGap.Continuum.SU2QuaternionCanonicalEightCompressedSpectralGap
open YMGap.Continuum.SU2QuaternionCanonicalEightCompletedPositiveTimeSector
open YMGap.Continuum.SU2QuaternionCanonicalEightPositiveTimeCompression

/-! ## 1. One observable-connected embedded sector -/

/-- A positive-time source sector embedded into an ambient interacting GNS
completion.

The source moment and vacuum-orthogonality fields are the finite analytic
inputs.  The two completion equalities are the semantic pins: they identify
the source vacuum and excitation with literal ambient Wilson observables.
All ambient conclusions below are derived from these fields and pairwise Gram
preservation; no unrelated ambient correlator is supplied. -/
structure EmbeddedPositiveTimeObservableSector (ambient : GNSData) : Type 1 where
  source : GNSData
  embedding : DenseGNSGramIsometry source ambient
  transfer : TransferOperator source.gnsComplete
  sourceVacuum : GNSCompletionSpace source
  sourceObservable : GNSCompletionSpace source
  ambientVacuum : ambient.V
  ambientObservable : ambient.V
  rate : Q'
  rate_nonnegative : (0 : Q') <= rate
  rate_lt_one : rate < (1 : Q')
  normSq : Q'
  normSq_pos : (0 : Q') < normSq
  transfer_vacuum_pin : transfer.vacuum = sourceVacuum
  transfer_vacuum_stationary : transfer.T sourceVacuum = sourceVacuum
  vacuum_pin : embedding.completed sourceVacuum = embedV ambient ambientVacuum
  observable_pin :
    embedding.completed sourceObservable = embedV ambient ambientObservable
  source_power_vacuum_orthogonal : forall time : Nat,
    source.cinnerCompl (Tpow transfer time sourceObservable) sourceVacuum =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' 0)
  source_moment_exact : forall time : Nat,
    source.cinnerCompl (Tpow transfer time sourceObservable) sourceObservable =
      Quotient.mk CReal.crealSetoid
        (CReal.ofQ' ((rate ^ time) * normSq))

namespace EmbeddedPositiveTimeObservableSector

variable {ambient : GNSData}
    (sector : EmbeddedPositiveTimeObservableSector ambient)

/-- The transferred source observable regarded as a vector in the ambient
interacting Wilson completion. -/
def ambientVectorAt (time : Nat) : GNSCompletionSpace ambient :=
  sector.embedding.completed
    (Tpow sector.transfer time sector.sourceObservable)

/-- At time zero the ambient path is the literal pinned Wilson observable. -/
theorem ambientVectorAt_zero :
    sector.ambientVectorAt 0 = embedV ambient sector.ambientObservable := by
  change sector.embedding.completed sector.sourceObservable = _
  exact sector.observable_pin

/-- Every transferred vector remains orthogonal to the literal pinned
ambient vacuum. -/
theorem ambientVectorAt_vacuum_orthogonal (time : Nat) :
    ambient.cinnerCompl
        (sector.ambientVectorAt time)
        (embedV ambient sector.ambientVacuum) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' 0) := by
  unfold ambientVectorAt
  rw [<- sector.vacuum_pin]
  rw [sector.embedding.completed_cinner]
  exact sector.source_power_vacuum_orthogonal time

/-- The literal same-object ambient matrix coefficient. -/
def ambientConnectedMoment (time : Nat) : CReal.RC :=
  ambient.cinnerCompl
    (sector.ambientVectorAt time)
    (embedV ambient sector.ambientObservable)

/-- Exact source moments pass through the completion embedding without a
change of carrier, vacuum, observable, or rate. -/
theorem ambientConnectedMoment_exact (time : Nat) :
    sector.ambientConnectedMoment time =
      Quotient.mk CReal.crealSetoid
        (CReal.ofQ' ((sector.rate ^ time) * sector.normSq)) := by
  unfold ambientConnectedMoment ambientVectorAt
  rw [<- sector.observable_pin]
  rw [sector.embedding.completed_cinner]
  exact sector.source_moment_exact time

end EmbeddedPositiveTimeObservableSector

/-! ## 2. One shared observable through every cutoff -/

/-- A scale-indexed family of embedded positive-time sectors with one shared
observable label.

`literal_observable` is deliberately an equality in the completed ambient
GNS carrier.  It permits different cutoff presentations while forbidding a
different completed observable from being substituted at a later scale. -/
structure CompletedPositiveTimeObservableTrajectory : Type 2 where
  Obs : Type
  GaugeInvariantLocal : Obs -> Prop
  observable : Obs
  observable_local : GaugeInvariantLocal observable
  ambient : Nat -> GNSData
  realize : (scale : Nat) -> Obs -> (ambient scale).V
  sector : (scale : Nat) ->
    EmbeddedPositiveTimeObservableSector (ambient scale)
  literal_observable : forall scale : Nat,
    embedV (ambient scale) (sector scale).ambientObservable =
      embedV (ambient scale) (realize scale observable)

namespace CompletedPositiveTimeObservableTrajectory

variable (trajectory : CompletedPositiveTimeObservableTrajectory)

/-- The literal transferred vector selected at one cutoff. -/
def vectorAt (scale time : Nat) :
    GNSCompletionSpace (trajectory.ambient scale) :=
  (trajectory.sector scale).ambientVectorAt time

/-- The shared observable label realized in the ambient GNS completion at one
cutoff. -/
def observableAt (scale : Nat) :
    GNSCompletionSpace (trajectory.ambient scale) :=
  embedV (trajectory.ambient scale)
    (trajectory.realize scale trajectory.observable)

/-- The literal connected matrix coefficient of the same observable at one
cutoff and one transfer time. -/
def connectedMoment (scale time : Nat) : CReal.RC :=
  (trajectory.ambient scale).cinnerCompl
    (trajectory.vectorAt scale time)
    (trajectory.observableAt scale)

/-- The trajectory's completed observable at time zero is exactly the shared
observable realization at that cutoff. -/
theorem vectorAt_zero (scale : Nat) :
    trajectory.vectorAt scale 0 = trajectory.observableAt scale := by
  unfold vectorAt observableAt
  rw [(trajectory.sector scale).ambientVectorAt_zero]
  exact trajectory.literal_observable scale

/-- The shared observable's literal connected moment is exactly the rational
stage moment supplied by the embedded sector. -/
theorem connectedMoment_exact (scale time : Nat) :
    trajectory.connectedMoment scale time =
      Quotient.mk CReal.crealSetoid
        (CReal.ofQ'
          ((((trajectory.sector scale).rate) ^ time) *
            (trajectory.sector scale).normSq)) := by
  unfold connectedMoment vectorAt observableAt
  rw [<- trajectory.literal_observable scale]
  exact (trajectory.sector scale).ambientConnectedMoment_exact time

/-- The rational number whose canonical `CReal` embedding is the literal
completed moment at one scale.  This is derived from the stage certificate,
not supplied as a parallel correlator. -/
def rationalMoment (time scale : Nat) : Q' :=
  (((trajectory.sector scale).rate) ^ time) *
    (trajectory.sector scale).normSq

/-- The literal completed moment is the quotient image of the trajectory's
derived rational moment. -/
theorem connectedMoment_eq_rationalMoment (scale time : Nat) :
    trajectory.connectedMoment scale time =
      Quotient.mk CReal.crealSetoid
        (CReal.ofQ' (trajectory.rationalMoment time scale)) :=
  trajectory.connectedMoment_exact scale time

/-- The transferred shared observable remains orthogonal to the literal
vacuum selected by the same stage certificate. -/
theorem vectorAt_vacuum_orthogonal (scale time : Nat) :
    (trajectory.ambient scale).cinnerCompl
        (trajectory.vectorAt scale time)
        (embedV (trajectory.ambient scale)
          (trajectory.sector scale).ambientVacuum) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' 0) :=
  (trajectory.sector scale).ambientVectorAt_vacuum_orthogonal time

end CompletedPositiveTimeObservableTrajectory

/-! ## 3. The explicit cross-scale comparison frontier -/

/-- Summable cutoff variation of the exact rational moments belonging to one
trajectory and one fixed transfer time.

This is the only additional datum needed to compare the already-pinned
same-observable moments across scales.  It cannot change the observable,
ambient stage, transfer path, or finite moment formula. -/
structure ConnectedMomentVariation
    (trajectory : CompletedPositiveTimeObservableTrajectory)
    (time : Nat) : Type 1 where
  rational : SummableRationalStepVariation
    (trajectory.rationalMoment time)

namespace ConnectedMomentVariation

variable {trajectory : CompletedPositiveTimeObservableTrajectory}
    {time : Nat} (variation : ConnectedMomentVariation trajectory time)

/-- The constructive-real cutoff limit selected by summable variation of the
exact same-observable stage moments. -/
def limit : CReal :=
  variation.rational.limit

/-- The exact rational stage moments converge to the selected constructive
real limit. -/
theorem converges :
    CReal.ConvergesTo
      (fun scale => CReal.ofQ'
        (trajectory.rationalMoment time scale))
      variation.limit :=
  variation.rational.converges

end ConnectedMomentVariation

/-! ## 4. The concrete canonical constant trajectory -/

/-- The canonical quaternion sector as one inhabitant of the generic embedded
positive-time interface. -/
def canonicalEmbeddedPositiveTimeObservableSector :
    EmbeddedPositiveTimeObservableSector canonicalWilsonGNS where
  source := wilsonModeGNS
  embedding := canonicalModeGramIsometry
  transfer := canonicalCompressedTransferOperator
  sourceVacuum := embedV wilsonModeGNS vacuumMode
  sourceObservable := embedV wilsonModeGNS fundamentalMode
  ambientVacuum := polyOne8
  ambientObservable := canonicalFundamentalBoundaryMode8
  rate := eighth
  rate_nonnegative := Q'.le_of_lt eighth_strict_window.1
  rate_lt_one := eighth_strict_window.2
  normSq := eighth
  normSq_pos := eighth_strict_window.1
  transfer_vacuum_pin := rfl
  transfer_vacuum_stationary := canonicalCompleted_vacuum_eigen
  vacuum_pin := canonicalCompletedModeEmbedding_vacuum
  observable_pin := canonicalCompletedModeEmbedding_fundamental
  source_power_vacuum_orthogonal := fun time => by
    have h := canonicalEmbeddedFundamentalAt_vacuum_orthogonal time
    unfold canonicalEmbeddedFundamentalAt at h
    rw [<- canonicalCompletedModeEmbedding_vacuum] at h
    rw [canonicalCompletedModeEmbedding_cinner] at h
    exact h
  source_moment_exact := fun time => by
    have h := canonicalEmbeddedFundamentalConnectedMoment_exact time
    unfold canonicalEmbeddedFundamentalConnectedMoment
      canonicalEmbeddedFundamentalAt at h
    rw [<- canonicalCompletedModeEmbedding_fundamental] at h
    rw [canonicalCompletedModeEmbedding_cinner] at h
    exact h

/-- A concrete constant trajectory.  It proves that the typed dynamic
same-observable interface itself is inhabited, while making no claim that a
constant finite stage is a physical continuum scaling trajectory. -/
def canonicalConstantCompletedPositiveTimeObservableTrajectory :
    CompletedPositiveTimeObservableTrajectory where
  Obs := Unit
  GaugeInvariantLocal := fun _ => True
  observable := ()
  observable_local := True.intro
  ambient := fun _ => canonicalWilsonGNS
  realize := fun _ _ => canonicalFundamentalBoundaryMode8
  sector := fun _ => canonicalEmbeddedPositiveTimeObservableSector
  literal_observable := fun _ => rfl

theorem canonicalConstant_connectedMoment_exact (scale time : Nat) :
    canonicalConstantCompletedPositiveTimeObservableTrajectory.connectedMoment
        scale time =
      Quotient.mk CReal.crealSetoid
        (CReal.ofQ' ((eighth ^ time) * eighth)) :=
  canonicalConstantCompletedPositiveTimeObservableTrajectory.connectedMoment_exact
    scale time

/-- The constant canonical trajectory has zero cross-scale variation at every
fixed transfer time.  This is a non-vacuous test of the comparison compiler,
not a physical continuum-limit theorem. -/
def canonicalConstantConnectedMomentVariation (time : Nat) :
    ConnectedMomentVariation
      canonicalConstantCompletedPositiveTimeObservableTrajectory time where
  rational := SummableRationalStepVariation.ofPointwiseEqvConstant
    (canonicalConstantCompletedPositiveTimeObservableTrajectory.rationalMoment
      time)
    ((eighth ^ time) * eighth)
    (fun _ => Q'.eqv_refl _)

end YMGap.Continuum.CompletedPositiveTimeObservableTrajectory

#print axioms YMGap.Continuum.CompletedPositiveTimeObservableTrajectory.EmbeddedPositiveTimeObservableSector.ambientVectorAt_vacuum_orthogonal
#print axioms YMGap.Continuum.CompletedPositiveTimeObservableTrajectory.EmbeddedPositiveTimeObservableSector.ambientConnectedMoment_exact
#print axioms YMGap.Continuum.CompletedPositiveTimeObservableTrajectory.CompletedPositiveTimeObservableTrajectory.vectorAt_zero
#print axioms YMGap.Continuum.CompletedPositiveTimeObservableTrajectory.CompletedPositiveTimeObservableTrajectory.connectedMoment_exact
#print axioms YMGap.Continuum.CompletedPositiveTimeObservableTrajectory.CompletedPositiveTimeObservableTrajectory.connectedMoment_eq_rationalMoment
#print axioms YMGap.Continuum.CompletedPositiveTimeObservableTrajectory.ConnectedMomentVariation.converges
#print axioms YMGap.Continuum.CompletedPositiveTimeObservableTrajectory.canonicalEmbeddedPositiveTimeObservableSector
#print axioms YMGap.Continuum.CompletedPositiveTimeObservableTrajectory.canonicalConstant_connectedMoment_exact
#print axioms YMGap.Continuum.CompletedPositiveTimeObservableTrajectory.canonicalConstantConnectedMomentVariation
