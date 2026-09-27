/-
# Conditional bridge from the current Wilson carrier to canonical OS/GNS data

The current spatial-union completion has a genuine `RC`-valued form, a
completed physical-time map, and the checked normalized-excitation resolvent
floor.  The canonical `WilsonTimeTranslationPin` instead lives on a
`GNSData` completion.  These carriers are not definitionally the same, so the
missing passage must be named rather than silently coerced.

This file supplies the smallest backward-facing bridge datum that consumes the
current result: a map preserving the completed form and zero, intertwining the
two-step current time map with the selected canonical transfer, and recording
vacuum orthogonality of the transported probe.  From it we construct a
canonical probe package whose squared norm has the same explicit `1/4` floor.
No bridge inhabitant is fabricated here. The target is the ordinary Wilson
completion `W.toGNSData`, not automatically the reflected positive-time
completion `CanonicalOSRoot.PositiveTimeOSRoot.positive`. An identification
with that physical OS form is a separate obligation; this conditional bridge
must not be treated as its construction. In particular, arbitrary supplied
Wilson data and time pins do not determine a compatible same-theory map.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse
import YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation
import YMGap.Continuum.WilsonGNSTransferUnderdetermination
import YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
import YMGap.Continuum.GNSDenseCompletionLaws
import YMGap.Continuum.GNSTransferMetric

namespace YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.CRealSeminormCompletion.SquaredSeminorm
open YMGap.Continuum.CRealSeminormPairingCompletion
  (representativeInner_eq_of_right_stage_pairings pairSequence_converges)
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnion (zeroStage unitStage)
open YMGap.Continuum.BF4WilsonSpatialUnion (Stage time)
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
  (completedInner_symm pairingData)
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
  (completedInner)
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef
  (completedZero fixed_orthogonal_eq_zero)
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection
open YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
open YMGap.Continuum.BF4WilsonSpatialUnionResolvent
open YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse
open YMGap.Continuum.BF4WilsonSpatialUnionRelaxation
  (mixed_correlator_sq_decay)
open YMGap.Continuum.BF4WilsonSpatialUnionResponseLower
  (unitExcitation_even_lower)
open YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation
  (evenOrbitResidual evenOrbitResidual_strict_form_bound)
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
  (completed_eq_of_pairings completedInner_sub_right)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap
  (completed_twoStep_form_gap)
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection
  (center_fixed_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate twoStepRate_positive twoStepRate_lt_one)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
  (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)
open YMGap.Continuum.WilsonGNSTransferUnderdetermination
open YMGap.Continuum.WilsonGNS
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDenseStageGraphNormCompiler
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalModulatedGapLimitStability
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.PhysicalSeparator

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate
local notation "V" => UnionCompletion nome_pos nome_lt_one hsmall hd hs
local notation "B" => completedInner nome_pos nome_lt_one hsmall hd hs
local notation "PD" => pairingData nome_pos nome_lt_one hsmall hd hs
local notation "U" => completedUnit nome_pos nome_lt_one hsmall hd hs
local notation "Z" => completedZero nome_pos nome_lt_one hsmall hd hs
local notation "T" => completedTime nome_pos nome_lt_one hsmall hd hs
local notation "R" => resolvent nome_pos nome_lt_one hsmall hd hs
local notation "S" => unionSeminorm nome_pos nome_lt_one hsmall hd hs

/-! ## The exact conditional carrier handoff -/

/-- The static part of the carrier handoff: a map from the completed current
carrier to the selected canonical completion, preserving zero and the full
completed pairing.  This certificate contains no dynamics. -/
structure CurrentCarrierFormCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W) : Type 2 where
  map : V → GNSCompletionSpace W.toGNSData
  map_zero : map Z = embedV W.toGNSData W.toGNSData.zero
  /-- The current vacuum is sent to the selected canonical vacuum. -/
  vacuum_preserving : map U = P.op.vacuum
  form_preserving : ∀ x y,
    W.toGNSData.cinnerCompl (map x) (map y) = B x y

/-! A producer-facing refinement of the static certificate. The current
completion is presented by explicit CReal-Cauchy streams, so a genuine source
must first map those streams into canonical GNS Cauchy streams and prove both
null descent and the completed Gram identity. -/

structure CurrentCarrierCauchyFormCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W) : Type 2 where
  mapCauchy : (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy →
    CauchyGNS W.toGNSData
  mapCauchy_null : ∀ {X Y : (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy},
    (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Close X Y →
    CauchyNull W.toGNSData (mapCauchy X) (mapCauchy Y)
  mapCauchy_pairing : ∀
    (X Y : (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy),
    W.toGNSData.cinnerCompl
      (Quotient.mk (cauchySetoid W.toGNSData) (mapCauchy X))
      (Quotient.mk (cauchySetoid W.toGNSData) (mapCauchy Y)) =
      B (Quotient.mk
        (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid X)
        (Quotient.mk
          (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid Y)
  mapCauchy_zero :
    Quotient.mk (cauchySetoid W.toGNSData)
        (mapCauchy ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant zeroStage)) =
      embedV W.toGNSData W.toGNSData.zero
  mapCauchy_unit :
    Quotient.mk (cauchySetoid W.toGNSData)
        (mapCauchy ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant unitStage)) =
      P.op.vacuum

/-! A finite-stage metric transport is a genuine forward-facing producer
compiler.  It is weaker than a completed carrier map: the producer supplies
one map on the original staged Wilson syntax and proves that every source
`CReal` tolerance transports to a rational `GNSData` tolerance.  The Cauchy
stream map and its null descent are then constructed below, without choosing
representatives of either quotient.  The completed Gram and distinguished
zero/unit pins remain separate fields of
`CurrentCarrierCauchyFormCertificate`; this compiler therefore does not hide
the OS/GNS identification in a larger wrapper. -/

structure CurrentStageCauchyTransportCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W) : Type 2 where
  mapStage : BF4WilsonSpatialUnion.Stage → W.toGNSData.V
  mapStage_distSq_le : ∀ (x y : BF4WilsonSpatialUnion.Stage) (ε : Q'),
    CReal.leEv
      ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).distSq x y)
      (CReal.ofQ' ε) →
    W.toGNSData.distSqQ (mapStage x) (mapStage y) ≤ ε

namespace CurrentStageCauchyTransportCertificate

variable
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}

local notation "D" => unionSeminorm nome_pos nome_lt_one hsmall hd hs

/-- Map a current CReal-Cauchy stream termwise into a canonical rational GNS
Cauchy stream, retaining the source modulus exactly. -/
def mapCauchy (K : CurrentStageCauchyTransportCertificate P)
    (X : (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy) :
    CauchyGNS W.toGNSData where
  seq := fun n => K.mapStage (X.seq n)
  modulus := X.modulus
  isCauchy := by
    intro ε hε p q hp hq
    exact K.mapStage_distSq_le (X.seq p) (X.seq q) ε
      (X.isCauchy ε hε p q hp hq)

/-- Source closeness transports constructively to canonical Cauchy-nullness;
the source closing modulus is reused verbatim. -/
theorem mapCauchy_null (K : CurrentStageCauchyTransportCertificate P)
    {X Y : (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy}
    (hXY : (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Close X Y) :
    CauchyNull W.toGNSData (K.mapCauchy X) (K.mapCauchy Y) := by
  intro ε hε
  refine ⟨hXY.modulus ε, ?_⟩
  intro n hn
  exact K.mapStage_distSq_le (X.seq n) (Y.seq n) ε
    (hXY.close ε hε n hn)

end CurrentStageCauchyTransportCertificate

/-! A finite-stage pairing compiler can now close the completed Gram field
constructively.  The canonical GNS representative pairing is the limit of
the termwise `Q'` pairings, while the current Wilson pairing is the limit of
the termwise `CReal` pairings.  A stage-level `CReal.Equiv` therefore suffices:
the existing limit-uniqueness theorem lifts it to arbitrary source Cauchy
streams.  The zero and unit pins remain explicit because they are observable
identifications, not consequences of metric transport alone. -/

structure CurrentStageCauchyStagePairingCertificate
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W) : Type 2 where
  transport : CurrentStageCauchyTransportCertificate P
  stagePairing : ∀ (x y : BF4WilsonSpatialUnion.Stage),
    CReal.Equiv
      (CReal.ofQ' (W.toGNSData.B (transport.mapStage x) (transport.mapStage y)))
      (BF4WilsonSpatialUnion.pairing nome_pos nome_lt_one hsmall hd hs x y)
  mapCauchy_zero :
    Quotient.mk (cauchySetoid W.toGNSData)
        (transport.mapCauchy
          ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant zeroStage)) =
      embedV W.toGNSData W.toGNSData.zero
  mapCauchy_unit :
    Quotient.mk (cauchySetoid W.toGNSData)
        (transport.mapCauchy
          ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant unitStage)) =
      P.op.vacuum

namespace CurrentStageCauchyStagePairingCertificate

variable
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}

local notation "D" => unionSeminorm nome_pos nome_lt_one hsmall hd hs

/-- Finite-stage pairing equivalence plus the explicit transport compiler
constructs the completed Gram identity for every pair of source Cauchy
streams.  The proof uses no representative extraction: both sides are the
canonical limits of their displayed termwise sequences. -/
theorem mapCauchy_pairing
    (K : CurrentStageCauchyStagePairingCertificate P)
    (X Y : (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy) :
    W.toGNSData.cinnerCompl
      (Quotient.mk (cauchySetoid W.toGNSData) (K.transport.mapCauchy X))
      (Quotient.mk (cauchySetoid W.toGNSData) (K.transport.mapCauchy Y)) =
      B (Quotient.mk
          (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid X)
        (Quotient.mk
          (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid Y) := by
  change Quotient.mk CReal.crealSetoid
      (W.toGNSData.cinnerRep (K.transport.mapCauchy X)
        (K.transport.mapCauchy Y)) =
    Quotient.mk CReal.crealSetoid
      (CRealSeminormPairingCompletion.representativeInner PD X Y)
  apply Quotient.sound
  apply CReal.Equiv_of_limit_of_close
    (CReal.convergesTo_ofQ'CauchySeq
      (W.toGNSData.cInnerSeq (K.transport.mapCauchy X)
        (K.transport.mapCauchy Y))
      (W.toGNSData.cInnerQCauchy (K.transport.mapCauchy X)
        (K.transport.mapCauchy Y)))
    (pairSequence_converges PD X Y)
  intro epsilon hepsilon
  refine ⟨0, fun N _ => ?_⟩
  obtain ⟨Npair, hNpair⟩ := K.stagePairing (X.seq N) (Y.seq N) epsilon hepsilon
  exact ⟨Npair, fun n hn => hNpair n hn⟩

end CurrentStageCauchyStagePairingCertificate

/-! The forward/backward meet with the physical matched-stage compiler.  The
current bridge supplies `Stage -> W.V`; the physical compiler supplies
`W.V -> (matched finite stage).V`.  Their composition is useful only after a
named two-step time law identifies the current stage advance with the selected
canonical observable shift.  The record below contains exactly that join; no
physical witness is inferred from either side alone. -/

structure CurrentStageMatchedPhysicalTransferJoin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {separator : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling separator)
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (K : CurrentStageCauchyStagePairingCertificate D.timeTranslation)
    (data : BF4WilsonDenseStageMapData producer D) : Type 2 where
  /-- The backward-facing current one-step shift agrees in the canonical
  carrier with the time shift consumed by the forward physical compiler. -/
  stage_time : ∀ x : Stage,
    D.wilson.toGNSData.veq
      (K.transport.mapStage (time 1 x))
      (D.timeTranslation.tau (K.transport.mapStage x))
  /-- The independently supplied two-step current shift agrees with the
  square of the canonical one-step shift.  This is kept explicit because the
  finite physical transfer is a one-macro-step operator. -/
  stage_two_time : ∀ x : Stage,
    D.wilson.toGNSData.veq
      (K.transport.mapStage (time 2 x))
      (D.timeTranslation.tau (D.timeTranslation.tau (K.transport.mapStage x)))

namespace CurrentStageMatchedPhysicalTransferJoin

variable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {separator : PhysicalSeparator}
    {producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling separator}
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : FourDExistence.ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    {K : CurrentStageCauchyStagePairingCertificate D.timeTranslation}
    {data : BF4WilsonDenseStageMapData producer D}

/-- The observable obtained by composing the current stage encoder with the
forward physical dense-stage map. -/
def stageObservable
    (J : CurrentStageMatchedPhysicalTransferJoin producer D K data)
    (scale : Nat) (x : Stage) :
    (MatchedPhysicalStageGNSData family coupling scale).V :=
  data.stageObservable scale (K.transport.mapStage x)

/-- The one-step current-stage advance is now an exact finite physical
transfer intertwining law.  This theorem is the constructive contraction of
the two independently typed directions; its only new premise is `stage_time`.
-/
theorem stageTransfer_intertwines
    (J : CurrentStageMatchedPhysicalTransferJoin producer D K data)
    (scale : Nat) (x : Stage) :
    (MatchedPhysicalStageGNSData family coupling scale).veq
      (centralPhysicalMarkovApply
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
        (J.stageObservable scale x))
      (J.stageObservable scale (time 1 x)) := by
  have hphysical := data.stageTransfer_intertwines scale
    (K.transport.mapStage x)
  have htime := data.stageObservable_congr scale (J.stage_time x)
  exact (MatchedPhysicalStageGNSData family coupling scale).veq_trans
    hphysical
    ((MatchedPhysicalStageGNSData family coupling scale).veq_symm htime)

/-! The square theorem is the honest two-step contraction used by the current
stage gap node.  It is not obtained by relabelling the one-step theorem: the
`stage_two_time` field records the separate two-step compatibility required by
the forward physical compiler. -/

theorem stageTransfer_square_intertwines
    (J : CurrentStageMatchedPhysicalTransferJoin producer D K data)
    (scale : Nat) (x : Stage) :
    (MatchedPhysicalStageGNSData family coupling scale).veq
      (centralPhysicalMarkovApply
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
        (centralPhysicalMarkovApply
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (J.stageObservable scale x)))
      (J.stageObservable scale (time 2 x)) := by
  have h₁ := data.stageTransfer_intertwines scale
    (K.transport.mapStage x)
  have h₁apply := centralPhysicalMarkovApply_congr
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0 h₁
  have h₂ := data.stageTransfer_intertwines scale
    (D.timeTranslation.tau (K.transport.mapStage x))
  have h₂time := data.stageObservable_congr scale (J.stage_two_time x)
  exact (MatchedPhysicalStageGNSData family coupling scale).veq_trans
    h₁apply
    ((MatchedPhysicalStageGNSData family coupling scale).veq_trans
      h₂
      ((MatchedPhysicalStageGNSData family coupling scale).veq_symm h₂time))

end CurrentStageMatchedPhysicalTransferJoin

/-! Once the finite-stage transport compiler is supplied, the only remaining
static pins are its completed Gram identity and the images of the literal
zero/unit streams.  Keeping these pins in a separate structure lets the
constructor below build the existing stream-level form certificate without
reintroducing a completed-stream map as an input. -/

structure CurrentStageCauchyFormCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W) : Type 2 where
  transport : CurrentStageCauchyTransportCertificate P
  mapCauchy_pairing : ∀
    (X Y : (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy),
    W.toGNSData.cinnerCompl
      (Quotient.mk (cauchySetoid W.toGNSData) (transport.mapCauchy X))
      (Quotient.mk (cauchySetoid W.toGNSData) (transport.mapCauchy Y)) =
      B (Quotient.mk
        (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid X)
        (Quotient.mk
          (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid Y)
  mapCauchy_zero :
    Quotient.mk (cauchySetoid W.toGNSData)
        (transport.mapCauchy
          ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant zeroStage)) =
      embedV W.toGNSData W.toGNSData.zero
  mapCauchy_unit :
    Quotient.mk (cauchySetoid W.toGNSData)
        (transport.mapCauchy
          ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant unitStage)) =
      P.op.vacuum

/-! Assemble the existing form compiler from the smaller finite-stage pairing
compiler and its two distinguished stream pins. -/
def CurrentStageCauchyStagePairingCertificate.toFormCertificate
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    (K : CurrentStageCauchyStagePairingCertificate P) :
    CurrentStageCauchyFormCertificate P where
  transport := K.transport
  mapCauchy_pairing := K.mapCauchy_pairing
  mapCauchy_zero := K.mapCauchy_zero
  mapCauchy_unit := K.mapCauchy_unit

def CurrentStageCauchyFormCertificate.toCauchyFormCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    (F : CurrentStageCauchyFormCertificate P) :
    CurrentCarrierCauchyFormCertificate P where
  mapCauchy := F.transport.mapCauchy
  mapCauchy_null := by
    intro X Y hXY
    exact F.transport.mapCauchy_null hXY
  mapCauchy_pairing := F.mapCauchy_pairing
  mapCauchy_zero := F.mapCauchy_zero
  mapCauchy_unit := F.mapCauchy_unit

namespace CurrentStageCauchyFormCertificate

variable
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}

local notation "D" => unionSeminorm nome_pos nome_lt_one hsmall hd hs

/-- The canonical class generated by one finite current stage.  This is kept
at the stream presentation so its Gram pin is available without choosing a
representative of the completed current carrier. -/
def stageClass (F : CurrentStageCauchyFormCertificate P)
    (x : BF4WilsonSpatialUnion.Stage) : GNSCompletionSpace W.toGNSData :=
  Quotient.mk (cauchySetoid W.toGNSData)
    (F.transport.mapCauchy
      ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant x))

theorem stageClass_pairing
    (F : CurrentStageCauchyFormCertificate P)
    (x y : BF4WilsonSpatialUnion.Stage) :
    W.toGNSData.cinnerCompl (F.stageClass x) (F.stageClass y) =
      B (Quotient.mk
          (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid
          ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant x))
        (Quotient.mk
          (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid
          ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant y)) :=
  F.mapCauchy_pairing
    ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant x)
    ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant y)

theorem stageClass_unit
    (F : CurrentStageCauchyFormCertificate P) :
    F.stageClass unitStage = P.op.vacuum :=
  by
    change Quotient.mk (cauchySetoid W.toGNSData)
        (F.transport.mapCauchy
          ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant unitStage)) =
      P.op.vacuum
    exact F.mapCauchy_unit

theorem stageClass_vacuum_orthogonal
    (F : CurrentStageCauchyFormCertificate P)
    (x : BF4WilsonSpatialUnion.Stage)
    (hx : B (BF4WilsonSpatialUnionSeminorm.embedStage
      nome_pos nome_lt_one hsmall hd hs x)
      (BF4WilsonSpatialUnionSeminorm.completedUnit
        nome_pos nome_lt_one hsmall hd hs) = RCzero) :
    W.toGNSData.cinnerCompl (F.stageClass x) P.op.vacuum = RCzero := by
  rw [← F.stageClass_unit, F.stageClass_pairing]
  exact hx

/-- The finite-stage transport respects equality already proved in the current
completion.  This is intentionally one-way: finite-stage Gram data alone does
not provide a density/separation theorem allowing canonical equality to be
pulled back from arbitrary completed vectors. -/
theorem stageClass_eq_of_current_eq
    (F : CurrentStageCauchyFormCertificate P)
    {x y : BF4WilsonSpatialUnion.Stage}
    (hxy : BF4WilsonSpatialUnionSeminorm.embedStage
      nome_pos nome_lt_one hsmall hd hs x =
      BF4WilsonSpatialUnionSeminorm.embedStage
        nome_pos nome_lt_one hsmall hd hs y) :
    F.stageClass x = F.stageClass y := by
  apply Quotient.sound
  have hrel :
      (unionSeminorm nome_pos nome_lt_one hsmall hd hs).CompletionRel
        ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant x)
        ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant y) := by
    change Quotient.mk
        (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid
        ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant x) =
      Quotient.mk
        (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid
        ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant y) at hxy
    exact Quotient.exact hxy
  rcases hrel with ⟨hclose⟩
  exact F.transport.mapCauchy_null hclose

end CurrentStageCauchyFormCertificate

/-! The finite-stage reverse edge is isolated as its own certificate.  The
forward edge (`stageClass_eq_of_current_eq`) is already discharged by source
quotient null descent.  The reverse edge is exactly the density/continuity
obligation: canonical equality of two transported stage classes must be
reflected by the original completed Wilson pairing when tested on every
finite stage.  Keeping this as a separate datum prevents a finite Gram pin
from being mistaken for completed-carrier separation. -/

structure CurrentStagePairingSeparationCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (F : CurrentStageCauchyFormCertificate P) : Type 2 where
  separates : ∀ {x y : BF4WilsonSpatialUnion.Stage},
    (∀ z : BF4WilsonSpatialUnion.Stage,
      B (BF4WilsonSpatialUnionSeminorm.embedStage
          nome_pos nome_lt_one hsmall hd hs x)
        (BF4WilsonSpatialUnionSeminorm.embedStage
          nome_pos nome_lt_one hsmall hd hs z) =
      B (BF4WilsonSpatialUnionSeminorm.embedStage
          nome_pos nome_lt_one hsmall hd hs y)
        (BF4WilsonSpatialUnionSeminorm.embedStage
          nome_pos nome_lt_one hsmall hd hs z)) →
    BF4WilsonSpatialUnionSeminorm.embedStage
        nome_pos nome_lt_one hsmall hd hs x =
      BF4WilsonSpatialUnionSeminorm.embedStage
        nome_pos nome_lt_one hsmall hd hs y

namespace CurrentStagePairingSeparationCertificate

variable
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    {F : CurrentStageCauchyFormCertificate P}

local notation "D" => unionSeminorm nome_pos nome_lt_one hsmall hd hs

/-- A supplied finite-stage separation certificate closes the reverse
compatibility edge for transported stage classes.  Together with the already
proved forward edge this is an equivalence, not an assertion that the
certificate is inhabited. -/
theorem stageClass_eq_iff_current_eq
    (sep : CurrentStagePairingSeparationCertificate P F)
    {x y : BF4WilsonSpatialUnion.Stage} :
    F.stageClass x = F.stageClass y ↔
      BF4WilsonSpatialUnionSeminorm.embedStage
          nome_pos nome_lt_one hsmall hd hs x =
        BF4WilsonSpatialUnionSeminorm.embedStage
          nome_pos nome_lt_one hsmall hd hs y := by
  constructor
  · intro hxy
    apply sep.separates
    intro z
    have hpair := congrArg
      (fun u => W.toGNSData.cinnerCompl u (F.stageClass z)) hxy
    change W.toGNSData.cinnerCompl (F.stageClass x) (F.stageClass z) =
      W.toGNSData.cinnerCompl (F.stageClass y) (F.stageClass z) at hpair
    rw [F.stageClass_pairing, F.stageClass_pairing] at hpair
    simpa only [BF4WilsonSpatialUnionSeminorm.embedStage] using hpair
  · intro hxy
    exact F.stageClass_eq_of_current_eq hxy

/-- The existing explicit Cauchy-stream pairing continuity constructs the
finite-stage separation certificate.  This is the forward/backward meet:
finite-stage equality is first extended along the supplied Cauchy modulus,
then the already-proved completed Wilson pairing separation returns source
carrier equality. -/
def ofExistingPairingContinuity
    (F : CurrentStageCauchyFormCertificate P) :
    CurrentStagePairingSeparationCertificate P F where
  separates := by
    intro x y hxy
    apply completed_eq_of_pairings nome_pos nome_lt_one hsmall hd hs
      (BF4WilsonSpatialUnionSeminorm.embedStage
        nome_pos nome_lt_one hsmall hd hs x)
      (BF4WilsonSpatialUnionSeminorm.embedStage
        nome_pos nome_lt_one hsmall hd hs y)
    intro z
    refine Quotient.inductionOn z ?_
    intro Y
    apply Quotient.sound
    apply representativeInner_eq_of_right_stage_pairings
      (pairingData nome_pos nome_lt_one hsmall hd hs)
      ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant x)
      ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant y) Y
    intro s
    have hstage := hxy s
    change B (BF4WilsonSpatialUnionSeminorm.embedStage
        nome_pos nome_lt_one hsmall hd hs x)
        (BF4WilsonSpatialUnionSeminorm.embedStage
          nome_pos nome_lt_one hsmall hd hs s) =
      B (BF4WilsonSpatialUnionSeminorm.embedStage
        nome_pos nome_lt_one hsmall hd hs y)
        (BF4WilsonSpatialUnionSeminorm.embedStage
          nome_pos nome_lt_one hsmall hd hs s) at hstage
    exact Quotient.exact hstage

end CurrentStagePairingSeparationCertificate

/-! A dense-stage dynamic pin asks only for exact transport of the original
finite stage time-two map. The Cauchy extension below derives the corresponding
completed-image equation from pairing continuity and self-adjointness. This
does not assert that the image exhausts the canonical completion. -/

structure CurrentStageDenseTwoStepCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (F : CurrentStageCauchyFormCertificate P) : Type 2 where
  twoStep_intertwines : ∀ x : BF4WilsonSpatialUnion.Stage,
    F.stageClass (BF4WilsonSpatialUnion.time 2 x) =
      P.op.T (P.op.T (F.stageClass x))

namespace CurrentStageDenseTwoStepCertificate

variable
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    {F : CurrentStageCauchyFormCertificate P}

local notation "D" => unionSeminorm nome_pos nome_lt_one hsmall hd hs

/-- The finite-stage dynamic pin identifies the canonical two-step coefficient
with the original current same-stage coefficient. -/
theorem twoStep_correlation_eq_current
    (C : CurrentStageDenseTwoStepCertificate P F)
    (x : BF4WilsonSpatialUnion.Stage) :
    W.toGNSData.cinnerCompl
        (P.op.T (P.op.T (F.stageClass x))) (F.stageClass x) =
      B (BF4WilsonSpatialUnionSeminorm.completedTime
        nome_pos nome_lt_one hsmall hd hs 2
        (BF4WilsonSpatialUnionSeminorm.embedStage
          nome_pos nome_lt_one hsmall hd hs x))
        (BF4WilsonSpatialUnionSeminorm.embedStage
          nome_pos nome_lt_one hsmall hd hs x) := by
  rw [← C.twoStep_intertwines x]
  rw [F.stageClass_pairing]
  rw [completedTime_embedStage]
  rfl

/-! The next theorem is the dense-stage form-gap consumer.  The current
orthogonality premise is explicit, and the result does not claim a completed
canonical range or a continuum gap. -/

theorem twoStep_form_bound
    (C : CurrentStageDenseTwoStepCertificate P F)
    (x : BF4WilsonSpatialUnion.Stage)
    (hx : B (BF4WilsonSpatialUnionSeminorm.embedStage
      nome_pos nome_lt_one hsmall hd hs x)
      (BF4WilsonSpatialUnionSeminorm.completedUnit
        nome_pos nome_lt_one hsmall hd hs) = RCzero) :
    RCle
      (W.toGNSData.cinnerCompl
        (P.op.T (P.op.T (F.stageClass x))) (F.stageClass x))
      (CReal.RCmul
        (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
        (W.toGNSData.cinnerCompl (F.stageClass x) (F.stageClass x))) := by
  have hcorr :
      W.toGNSData.cinnerCompl
          (P.op.T (P.op.T (F.stageClass x))) (F.stageClass x) =
        B (BF4WilsonSpatialUnionSeminorm.completedTime
          nome_pos nome_lt_one hsmall hd hs 2
          (BF4WilsonSpatialUnionSeminorm.embedStage
            nome_pos nome_lt_one hsmall hd hs x))
          (BF4WilsonSpatialUnionSeminorm.embedStage
            nome_pos nome_lt_one hsmall hd hs x) := by
    exact C.twoStep_correlation_eq_current x
  have hnorm :
      W.toGNSData.cinnerCompl (F.stageClass x) (F.stageClass x) =
        B (BF4WilsonSpatialUnionSeminorm.embedStage
          nome_pos nome_lt_one hsmall hd hs x)
          (BF4WilsonSpatialUnionSeminorm.embedStage
            nome_pos nome_lt_one hsmall hd hs x) := by
    rw [F.stageClass_pairing]
    rfl
  have hcurrent := completed_twoStep_form_gap
    nome_pos nome_lt_one hsmall hd hs
    (BF4WilsonSpatialUnionSeminorm.embedStage
      nome_pos nome_lt_one hsmall hd hs x) hx
  have hsym :
      B (BF4WilsonSpatialUnionSeminorm.completedTime
          nome_pos nome_lt_one hsmall hd hs 2
          (BF4WilsonSpatialUnionSeminorm.embedStage
            nome_pos nome_lt_one hsmall hd hs x))
          (BF4WilsonSpatialUnionSeminorm.embedStage
            nome_pos nome_lt_one hsmall hd hs x) =
        B (BF4WilsonSpatialUnionSeminorm.embedStage
            nome_pos nome_lt_one hsmall hd hs x)
          (BF4WilsonSpatialUnionSeminorm.completedTime
            nome_pos nome_lt_one hsmall hd hs 2
            (BF4WilsonSpatialUnionSeminorm.embedStage
              nome_pos nome_lt_one hsmall hd hs x)) :=
    completedInner_symm nome_pos nome_lt_one hsmall hd hs _ _
  have hcorr' :
      W.toGNSData.cinnerCompl
          (P.op.T (P.op.T (F.stageClass x))) (F.stageClass x) =
        B (BF4WilsonSpatialUnionSeminorm.embedStage
            nome_pos nome_lt_one hsmall hd hs x)
          (BF4WilsonSpatialUnionSeminorm.completedTime
            nome_pos nome_lt_one hsmall hd hs 2
            (BF4WilsonSpatialUnionSeminorm.embedStage
              nome_pos nome_lt_one hsmall hd hs x)) :=
    hcorr.trans hsym
  simpa only [hcorr', hnorm] using hcurrent

/-! If the finite-stage reverse separation edge is supplied, the current
fixed-point exclusion can already be consumed on canonical stage classes.
This is still a finite-stage statement: it does not extend the conclusion to
arbitrary canonical Cauchy classes. -/

theorem twoStep_fixed_stage_eq_zero
    (C : CurrentStageDenseTwoStepCertificate P F)
    (sep : CurrentStagePairingSeparationCertificate P F)
    (x : BF4WilsonSpatialUnion.Stage)
    (hx : B (BF4WilsonSpatialUnionSeminorm.embedStage
      nome_pos nome_lt_one hsmall hd hs x)
      (BF4WilsonSpatialUnionSeminorm.completedUnit
        nome_pos nome_lt_one hsmall hd hs) = RCzero)
    (hfixed : P.op.T (P.op.T (F.stageClass x)) = F.stageClass x) :
    F.stageClass x = embedV W.toGNSData W.toGNSData.zero := by
  have hclass : F.stageClass (BF4WilsonSpatialUnion.time 2 x) = F.stageClass x := by
    exact (C.twoStep_intertwines x).trans hfixed
  have hcurrent_stage :=
    (CurrentStagePairingSeparationCertificate.stageClass_eq_iff_current_eq sep).mp hclass
  have hsource :
      BF4WilsonSpatialUnionSeminorm.completedTime
          nome_pos nome_lt_one hsmall hd hs 2
          (BF4WilsonSpatialUnionSeminorm.embedStage
            nome_pos nome_lt_one hsmall hd hs x) =
        BF4WilsonSpatialUnionSeminorm.embedStage
          nome_pos nome_lt_one hsmall hd hs x := by
    simpa only [BF4WilsonSpatialUnionSeminorm.completedTime_embedStage] using hcurrent_stage
  have hzero := fixed_orthogonal_eq_zero
    nome_pos nome_lt_one hsmall hd hs
    (BF4WilsonSpatialUnionSeminorm.embedStage
      nome_pos nome_lt_one hsmall hd hs x) hx hsource
  have hstagezero :
      F.stageClass x = F.stageClass BF4WilsonSpatialUnion.zeroStage := by
    apply F.stageClass_eq_of_current_eq
    simpa only [completedZero] using hzero
  calc
    F.stageClass x = F.stageClass BF4WilsonSpatialUnion.zeroStage := hstagezero
    _ = embedV W.toGNSData W.toGNSData.zero := by
      change Quotient.mk (cauchySetoid W.toGNSData)
          (F.transport.mapCauchy
            ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant zeroStage)) = _
      exact F.mapCauchy_zero

theorem twoStep_fixed_stage_eq_zero_of_existing_pairing_continuity
    (C : CurrentStageDenseTwoStepCertificate P F)
    (x : BF4WilsonSpatialUnion.Stage)
    (hx : B (BF4WilsonSpatialUnionSeminorm.embedStage
      nome_pos nome_lt_one hsmall hd hs x)
      (BF4WilsonSpatialUnionSeminorm.completedUnit
        nome_pos nome_lt_one hsmall hd hs) = RCzero)
    (hfixed : P.op.T (P.op.T (F.stageClass x)) = F.stageClass x) :
    F.stageClass x = embedV W.toGNSData W.toGNSData.zero :=
  C.twoStep_fixed_stage_eq_zero
    (CurrentStagePairingSeparationCertificate.ofExistingPairingContinuity F)
    x hx hfixed

end CurrentStageDenseTwoStepCertificate

def CurrentCarrierCauchyFormCertificate.toFormCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    (C : CurrentCarrierCauchyFormCertificate P) :
    CurrentCarrierFormCertificate P where
  map := Quotient.lift
    (fun X => Quotient.mk (cauchySetoid W.toGNSData) (C.mapCauchy X))
    (fun X Y h => by
      rcases h with ⟨hclose⟩
      exact Quotient.sound (C.mapCauchy_null (X := X) (Y := Y) hclose))
  map_zero := by
    change Quotient.mk (cauchySetoid W.toGNSData)
        (C.mapCauchy
          ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant zeroStage)) =
      embedV W.toGNSData W.toGNSData.zero
    exact C.mapCauchy_zero
  vacuum_preserving := by
    change Quotient.mk (cauchySetoid W.toGNSData)
        (C.mapCauchy
          ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant unitStage)) =
      P.op.vacuum
    exact C.mapCauchy_unit
  form_preserving := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro X Y
    exact C.mapCauchy_pairing X Y

/-! The dynamic stream-level obligation is separated from the static Gram
identity. It asks only for transport of the explicit current two-step stream
through the already supplied canonical stream map. -/

structure CurrentCarrierCauchyTwoStepCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (C : CurrentCarrierCauchyFormCertificate P) : Type 2 where
  mapCauchy_twoStep : ∀ X : (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy,
    Quotient.mk (cauchySetoid W.toGNSData)
        (C.mapCauchy
          ((timeNonexpansive nome_pos nome_lt_one hsmall hd hs 2).mapCauchy X)) =
      P.op.T (P.op.T
        (Quotient.mk (cauchySetoid W.toGNSData) (C.mapCauchy X)))

/-! The probe stream certificate keeps quotient representative choice explicit.
The completed resolvent is not destructed to obtain a representative; a
producer must supply the Cauchy stream and its class equation. -/

structure CurrentCarrierCauchyProbeCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (C : CurrentCarrierCauchyFormCertificate P) : Type 2 where
  probeCauchy : (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy
  probeCauchy_class :
    Quotient.mk
        (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid
        probeCauchy = R unitExcitation
  probe_vacuum_orthogonal :
    W.toGNSData.cinnerCompl
      (Quotient.mk (cauchySetoid W.toGNSData) (C.mapCauchy probeCauchy))
      P.op.vacuum = RCzero

/-- The dynamic part of the carrier handoff.  It is deliberately separate from
the static form certificate so a producer can establish time intertwining
without silently supplying a form identification. -/
structure CurrentCarrierTwoStepCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (F : CurrentCarrierFormCertificate P) : Type 2 where
  twoStep_intertwines : ∀ x,
    F.map (T 2 x) = P.op.T (P.op.T (F.map x))

def CurrentCarrierCauchyTwoStepCertificate.toTwoStepCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    (C : CurrentCarrierCauchyFormCertificate P)
    (D : CurrentCarrierCauchyTwoStepCertificate P C) :
    CurrentCarrierTwoStepCertificate P C.toFormCertificate where
  twoStep_intertwines := by
    intro x
    refine Quotient.inductionOn x ?_
    intro X
    change Quotient.mk (cauchySetoid W.toGNSData)
        (C.mapCauchy
          ((timeNonexpansive nome_pos nome_lt_one hsmall hd hs 2).mapCauchy X)) =
      P.op.T (P.op.T
        (Quotient.mk (cauchySetoid W.toGNSData) (C.mapCauchy X)))
    exact D.mapCauchy_twoStep X

/-- The probe-specific vacuum-complement certificate. Its field follows from
the static form and vacuum pins via `ofFormCertificate` below; it is retained
as a compatibility interface rather than an independent analytic input. -/
structure CurrentCarrierProbeCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (F : CurrentCarrierFormCertificate P) : Type 2 where
  probe_vacuum_orthogonal :
    W.toGNSData.cinnerCompl (F.map (R unitExcitation)) P.op.vacuum = RCzero

/-- The existing resolvent is centered. Exact preservation of the form and
vacuum therefore supplies the probe certificate without a dynamics premise
or a choice of representative for the completed probe. -/
def CurrentCarrierProbeCertificate.ofFormCertificate
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    (F : CurrentCarrierFormCertificate P) :
    CurrentCarrierProbeCertificate P F where
  probe_vacuum_orthogonal := by
    rw [← F.vacuum_preserving, F.form_preserving (R unitExcitation) U]
    exact (center_fixed_iff nome_pos nome_lt_one hsmall hd hs _).mp
      unitExcitation_resolvent_centered

def CurrentCarrierCauchyProbeCertificate.toProbeCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    (C : CurrentCarrierCauchyFormCertificate P)
    (O : CurrentCarrierCauchyProbeCertificate P C) :
    CurrentCarrierProbeCertificate P C.toFormCertificate where
  probe_vacuum_orthogonal := by
    rw [← O.probeCauchy_class]
    exact O.probe_vacuum_orthogonal

/-- The named OS/GNS carrier bridge still required by the current Wilson route.

`map` is not assumed to be an identification: it is supplied together with
the form equation that makes the current `RC`-valued estimate usable on the
canonical completion.  `twoStep_intertwines` is the dynamic part needed before
the current same-object estimate can feed a canonical transfer argument. -/
structure CurrentCarrierBridge
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W) : Type 2 where
  /-- Map from the current spatial-union completion to the canonical completion. -/
  map : V → GNSCompletionSpace W.toGNSData
  /-- The current zero is sent to the canonical GNS zero. -/
  map_zero : map Z = embedV W.toGNSData W.toGNSData.zero
  /-- The current vacuum is sent to the selected canonical vacuum. -/
  vacuum_preserving : map U = P.op.vacuum
  /-- The completed pairings are preserved exactly in `RC`. -/
  form_preserving : ∀ x y,
    W.toGNSData.cinnerCompl (map x) (map y) = B x y
  /-- The current physical two-step map intertwines with the selected transfer. -/
  twoStep_intertwines : ∀ x,
    map (T 2 x) = P.op.T (P.op.T (map x))
  /-- The transported normalized resolvent probe is in the canonical vacuum complement. -/
  probe_vacuum_orthogonal :
    W.toGNSData.cinnerCompl (map (R unitExcitation)) P.op.vacuum = RCzero

/-- Reassemble the full bridge from its three independently producible
certificates.  This is a structural constructor only: it does not create any
of the certificates or weaken their carrier, form, or dynamics fields. -/
def CurrentCarrierBridge.ofCertificates
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (F : CurrentCarrierFormCertificate P)
    (D : CurrentCarrierTwoStepCertificate P F)
    (O : CurrentCarrierProbeCertificate P F) : CurrentCarrierBridge P where
  map := F.map
  map_zero := F.map_zero
  vacuum_preserving := F.vacuum_preserving
  form_preserving := F.form_preserving
  twoStep_intertwines := D.twoStep_intertwines
  probe_vacuum_orthogonal := O.probe_vacuum_orthogonal

/-- Contract the three stream-level producer certificates into the named
completed-space bridge. This is only composition of checked quotient descents;
it does not construct any producer certificate. -/
def CurrentCarrierCauchyFormCertificate.toBridge
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (C : CurrentCarrierCauchyFormCertificate P)
    (D : CurrentCarrierCauchyTwoStepCertificate P C)
    (O : CurrentCarrierCauchyProbeCertificate P C) :
    CurrentCarrierBridge P :=
  CurrentCarrierBridge.ofCertificates P C.toFormCertificate
    (CurrentCarrierCauchyTwoStepCertificate.toTwoStepCertificate C D)
    (CurrentCarrierCauchyProbeCertificate.toProbeCertificate C O)

namespace CurrentCarrierFormCertificate

variable
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}

open YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance
  (completedDist completedDist_time_contraction distanceData)
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
  (completedSub completedInner_sub_left)

/-- Exact form preservation already preserves squared distances, without a
separate linearity premise or rational representatives for the stage images. -/
theorem distance_preserving (F : CurrentCarrierFormCertificate P) (x y : V) :
    GNSTransferMetric.distanceSq W.toGNSData (F.map x) (F.map y) =
      completedDist nome_pos nome_lt_one hsmall hd hs x y := by
  unfold GNSTransferMetric.distanceSq completedDist
  rw [RCBilinearDifference.difference_diagonal W.toGNSData.cSub
    W.toGNSData.cinnerCompl W.toGNSData.cinnerCompl_cSub_left
    W.toGNSData.cinnerCompl_comm]
  rw [RCBilinearDifference.difference_diagonal
    (completedSub nome_pos nome_lt_one hsmall hd hs) B
    (completedInner_sub_left nome_pos nome_lt_one hsmall hd hs)
    (completedInner_symm nome_pos nome_lt_one hsmall hd hs)]
  simp only [F.form_preserving]

/-- A dense two-step equation extends through any completed form-preserving
map. The dense images may be arbitrary completed GNS vectors: this does not
require the stronger exact rational stage-map interface. -/
def toTwoStepCertificateOfDense (F : CurrentCarrierFormCertificate P)
    (dense : ∀ s : Stage,
      F.map (T 2 (embedStage nome_pos nome_lt_one hsmall hd hs s)) =
        P.op.T (P.op.T (F.map (embedStage nome_pos nome_lt_one hsmall hd hs s)))) :
    CurrentCarrierTwoStepCertificate P F where
  twoStep_intertwines := by
    intro x
    apply GNSTransferMetric.maps_eq_of_dense
      (distanceData nome_pos nome_lt_one hsmall hd hs) W.toGNSData
      (fun y => F.map (T 2 y)) (fun y => P.op.T (P.op.T (F.map y)))
      (dense := dense) (x := x)
    · intro a b
      rw [F.distance_preserving]
      exact completedDist_time_contraction nome_pos nome_lt_one hsmall hd hs 2 a b
    · intro a b
      apply RCle_trans (GNSTransferMetric.transfer_nonexpansive W.toGNSData P.op
        (P.op.T (F.map a)) (P.op.T (F.map b)))
      apply RCle_trans (GNSTransferMetric.transfer_nonexpansive W.toGNSData P.op
        (F.map a) (F.map b))
      rw [F.distance_preserving]
      exact RCle_refl _

/-- Static completed form/vacuum transport and its dense dynamics suffice.
Neither completed dynamics nor probe orthogonality is an independent input.
The supplied canonical datum and static transport are not constructed here. -/
def toBridgeOfDense (F : CurrentCarrierFormCertificate P)
    (dense : ∀ s : Stage,
      F.map (T 2 (embedStage nome_pos nome_lt_one hsmall hd hs s)) =
        P.op.T (P.op.T (F.map (embedStage nome_pos nome_lt_one hsmall hd hs s)))) :
    CurrentCarrierBridge P :=
  CurrentCarrierBridge.ofCertificates P F (F.toTwoStepCertificateOfDense dense)
    (CurrentCarrierProbeCertificate.ofFormCertificate F)

end CurrentCarrierFormCertificate

/-- The older termwise stage producer is a specialization of the same dense
extension argument. No second limit proof or canonical range section is
required. Its exact rational stage-image restriction remains unchanged. -/
def CurrentStageDenseTwoStepCertificate.toCauchyTwoStepCertificate
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    {F : CurrentStageCauchyFormCertificate P}
    (C : CurrentStageDenseTwoStepCertificate P F) :
    CurrentCarrierCauchyTwoStepCertificate P F.toCauchyFormCertificate where
  mapCauchy_twoStep := by
    intro X
    have dynamics : CurrentCarrierTwoStepCertificate P
        F.toCauchyFormCertificate.toFormCertificate :=
      F.toCauchyFormCertificate.toFormCertificate.toTwoStepCertificateOfDense (by
        intro s
        rw [completedTime_embedStage]
        exact C.twoStep_intertwines s)
    exact dynamics.twoStep_intertwines (Quotient.mk (S).completionSetoid X)

/-- Static stage transport and the dense two-step equation suffice for the
existing completed bridge. The completed dynamics and probe orthogonality
fields are derived, so neither remains a separate producer input here.
The static stage certificate and dense equation themselves remain inputs. -/
def CurrentStageDenseTwoStepCertificate.toBridge
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    {F : CurrentStageCauchyFormCertificate P}
    (C : CurrentStageDenseTwoStepCertificate P F) : CurrentCarrierBridge P :=
  CurrentCarrierBridge.ofCertificates P F.toCauchyFormCertificate.toFormCertificate
    (CurrentCarrierCauchyTwoStepCertificate.toTwoStepCertificate
      F.toCauchyFormCertificate C.toCauchyTwoStepCertificate)
    (CurrentCarrierProbeCertificate.ofFormCertificate
      F.toCauchyFormCertificate.toFormCertificate)

/-- Exact form preservation makes the bridge map injective.  The proof uses the
separating completed current pairing, so injectivity is not an extra field and
does not require a representative choice or classical quotient reasoning. -/
theorem CurrentCarrierBridge.map_injective
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    (J : CurrentCarrierBridge P) {x y : V}
    (h : J.map x = J.map y) : x = y := by
  apply completed_eq_of_pairings nome_pos nome_lt_one hsmall hd hs x y
  intro z
  rw [← J.form_preserving x z, ← J.form_preserving y z]
  exact congrArg (fun u => W.toGNSData.cinnerCompl u (J.map z)) h

/-- The canonical probe data produced by a supplied carrier bridge. -/
structure CanonicalProbeData
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (J : CurrentCarrierBridge P) : Type 2 where
  vector : GNSCompletionSpace W.toGNSData
  vacuum_orthogonal :
    W.toGNSData.cinnerCompl vector P.op.vacuum = RCzero
  norm_floor :
    RCle (Quotient.mk crealSetoid
      (ofQ' (Q'.mkPos 1 4 (by decide))))
      (W.toGNSData.cinnerCompl vector vector)
  twoStep_intertwines :
    J.map (T 2 (R unitExcitation)) = P.op.T (P.op.T vector)

/-! The normalized unit excitation has a sharper nontriviality payload than
    the resolvent probe: its current two-step response already carries the
    explicit positive `rayleighFloor`. -/

structure CanonicalUnitProbeData
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (J : CurrentCarrierBridge P) : Type 2 where
  vector : GNSCompletionSpace W.toGNSData
  current_preimage : V
  image_eq : J.map current_preimage = vector
  vacuum_orthogonal :
    W.toGNSData.cinnerCompl vector P.op.vacuum = RCzero
  nonzero : vector ≠ embedV W.toGNSData W.toGNSData.zero
  twoStep_response_floor :
    RCle (Quotient.mk crealSetoid (ofQ' rayleighFloor))
      (W.toGNSData.cinnerCompl
        (P.op.T (P.op.T vector)) vector)

namespace CurrentCarrierBridge

variable
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}

/-! ## The all-image vacuum-complement consumer -/

/-- A current vacuum-complement vector remains in the canonical vacuum
complement under a supplied bridge.  This is the first all-vector consequence
of the static vacuum identification; it is still restricted to the bridge
image and therefore does not assert canonical density. -/
theorem image_vacuum_orthogonal
    (J : CurrentCarrierBridge P) {x : V}
    (hx : B x U = RCzero) :
    W.toGNSData.cinnerCompl (J.map x) P.op.vacuum = RCzero := by
  rw [← J.vacuum_preserving, J.form_preserving x U]
  exact hx

/-- The canonical two-step same-object coefficient agrees exactly with the
current completed coefficient for every vector in the bridge image. -/
theorem image_twoStep_correlation_eq_current
    (J : CurrentCarrierBridge P) (x : V) :
    W.toGNSData.cinnerCompl
        (P.op.T (P.op.T (J.map x))) (J.map x) =
      B (T 2 x) x := by
  rw [← J.twoStep_intertwines x]
  exact J.form_preserving (T 2 x) x

/-- The current strict two-step form bound transports to every vector in the
image of a supplied bridge, once that vector is known to be orthogonal to the
current vacuum.  The remaining dense-range and completed-space steps are not
assumed here. -/
theorem image_twoStep_form_bound
    (J : CurrentCarrierBridge P) {x : V}
    (hx : B x U = RCzero) :
    RCle
      (W.toGNSData.cinnerCompl
        (P.op.T (P.op.T (J.map x))) (J.map x))
      (CReal.RCmul
        (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
        (W.toGNSData.cinnerCompl (J.map x) (J.map x))) := by
  have hgap := completed_twoStep_form_gap
    nome_pos nome_lt_one hsmall hd hs x hx
  have hsym :
      B (T 2 x) x = B x (T 2 x) :=
    completedInner_symm nome_pos nome_lt_one hsmall hd hs
      (T 2 x) x
  rw [← J.twoStep_intertwines x]
  rw [J.form_preserving (T 2 x) x]
  rw [J.form_preserving x x]
  rw [hsym]
  exact hgap

/-! The stronger same-carrier residual margin also transports through the
conditional bridge. This is still image-level: no density or canonical
completed-space coercivity is inferred. -/

theorem image_twoStep_defect_form_bound
    (J : CurrentCarrierBridge P) {x : V}
    (hx : B x U = RCzero) :
    RCle
      (CReal.RCscale (1 - twoStepRate nome hd)
        (W.toGNSData.cinnerCompl (J.map x) (J.map x)))
      (CReal.RCsub
        (W.toGNSData.cinnerCompl (J.map x) (J.map x))
        (W.toGNSData.cinnerCompl
          (P.op.T (P.op.T (J.map x))) (J.map x))) := by
  have hcurrent := evenOrbitResidual_strict_form_bound
    nome_pos nome_lt_one hsmall hd hs x hx
  unfold evenOrbitResidual at hcurrent
  rw [completedInner_sub_right] at hcurrent
  have hsym :
      B (T 2 x) x = B x (T 2 x) :=
    completedInner_symm nome_pos nome_lt_one hsmall hd hs (T 2 x) x
  rw [← J.twoStep_intertwines x]
  rw [J.form_preserving x x, J.form_preserving (T 2 x) x]
  rw [hsym]
  exact hcurrent

/-- A canonical two-step fixed vector cannot be a nonzero vector in the
bridge image.  Intertwining and the already-proved bridge injectivity pull the
fixed-point equation back to the current carrier, where the current strict
form gap kills every vacuum-complement fixed vector. -/
theorem image_twoStep_fixed_eq_zero
    (J : CurrentCarrierBridge P) {x : V}
    (hx : B x U = RCzero)
    (hfixed : P.op.T (P.op.T (J.map x)) = J.map x) :
    J.map x = embedV W.toGNSData W.toGNSData.zero := by
  have hmap : J.map (T 2 x) = J.map x := by
    rw [J.twoStep_intertwines x, hfixed]
  have hsource : T 2 x = x := J.map_injective hmap
  have hzero : x = Z :=
    fixed_orthogonal_eq_zero nome_pos nome_lt_one hsmall hd hs x hx hsource
  rw [hzero, J.map_zero]

/-- The checked current-carrier floor transported to the canonical completion. -/
theorem canonical_resolvent_norm_floor (J : CurrentCarrierBridge P) :
  RCle (Quotient.mk crealSetoid
      (ofQ' (Q'.mkPos 1 4 (by decide))))
      (W.toGNSData.cinnerCompl (J.map (R unitExcitation))
        (J.map (R unitExcitation))) := by
  rw [J.form_preserving]
  exact
    YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse.unitExcitation_resolvent_norm_floor

/-- The bridge exposes a canonical non-vacuum-complement probe package. -/
def canonicalProbe (J : CurrentCarrierBridge P) : CanonicalProbeData P J where
  vector := J.map (R unitExcitation)
  vacuum_orthogonal := J.probe_vacuum_orthogonal
  norm_floor := J.canonical_resolvent_norm_floor
  twoStep_intertwines := J.twoStep_intertwines (R unitExcitation)

theorem canonicalProbe_vector (J : CurrentCarrierBridge P) :
    (J.canonicalProbe).vector = J.map (R unitExcitation) := rfl

theorem canonicalProbe_vacuum_orthogonal (J : CurrentCarrierBridge P) :
    W.toGNSData.cinnerCompl (J.canonicalProbe).vector P.op.vacuum = RCzero :=
  J.canonicalProbe.vacuum_orthogonal

theorem canonicalProbe_norm_floor (J : CurrentCarrierBridge P) :
    RCle (Quotient.mk crealSetoid
      (ofQ' (Q'.mkPos 1 4 (by decide))))
      (W.toGNSData.cinnerCompl (J.canonicalProbe).vector
        (J.canonicalProbe).vector) :=
  J.canonicalProbe.norm_floor

private theorem positive_constant_not_le_zero_local (q : Q')
    (hq : (0 : Q') < q) :
    ¬ RCle (Quotient.mk crealSetoid (ofQ' q)) RCzero := by
  intro h
  obtain ⟨N, hN⟩ := h (HalfPow.half * q) (ExpNeg.half_mul_pos q hq)
  have hbad := hN N (Nat.le_refl N)
  change q ≤ 0 + HalfPow.half * q at hbad
  rw [Q'.zero_add'] at hbad
  have hprod : q * 1 ≤ q * HalfPow.half := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_one_eqv _))
    (Q'.le_trans' _ _ _ hbad (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
  exact (by decide : ¬ (1 : Q') ≤ HalfPow.half)
    (Q'.le_of_mul_le_mul_left hprod hq)

/-- The checked current-carrier floor makes the transported canonical probe
genuinely nonzero.  This is a consequence of the supplied bridge, not a new
OS/GNS identification or a replacement observable. -/
theorem canonicalProbe_ne_zero (J : CurrentCarrierBridge P) :
    (J.canonicalProbe).vector ≠
      embedV W.toGNSData W.toGNSData.zero := by
  intro hzero
  have hfloor := J.canonicalProbe_norm_floor
  rw [hzero, W.toGNSData.cinnerCompl_embedZero_left] at hfloor
  exact positive_constant_not_le_zero_local
    (Q'.mkPos 1 4 (by decide)) (by decide) hfloor

/-! ## The first canonical same-object moment consumer -/

/-- The canonical two-step matrix coefficient of the transported resolvent
probe is exactly the current-carrier coefficient.  The equality uses only
the bridge's form preservation and its explicit two-step intertwining field.
-/
theorem canonicalProbe_twoStepCorrelation_eq_current
    (J : CurrentCarrierBridge P) :
    W.toGNSData.cinnerCompl
        (P.op.T (P.op.T (J.canonicalProbe.vector)))
        (J.canonicalProbe.vector) =
      B (T 2 (R unitExcitation)) (R unitExcitation) := by
  change W.toGNSData.cinnerCompl
      (P.op.T (P.op.T (J.map (R unitExcitation))))
      (J.map (R unitExcitation)) =
    B (T 2 (R unitExcitation)) (R unitExcitation)
  rw [← J.twoStep_intertwines (R unitExcitation)]
  exact J.form_preserving (T 2 (R unitExcitation)) (R unitExcitation)

/-- The transported canonical probe inherits the fixed-spacing current
same-object squared decay at the two-step lag.  This is conditional only on
the named carrier bridge; it does not construct the OS/GNS bridge or change
the observable. -/
theorem canonicalProbe_twoStep_sq_decay
    (J : CurrentCarrierBridge P) :
    CReal.RCle
      (CReal.RCmul
        (W.toGNSData.cinnerCompl
          (P.op.T (P.op.T (J.canonicalProbe.vector)))
          (J.canonicalProbe.vector))
        (W.toGNSData.cinnerCompl
          (P.op.T (P.op.T (J.canonicalProbe.vector)))
          (J.canonicalProbe.vector)))
      (CReal.RCmul
        (W.toGNSData.cinnerCompl
          (J.canonicalProbe.vector) (J.canonicalProbe.vector))
        (CReal.RCscale
          (twoStepRate nome hd ^ 2)
          (W.toGNSData.cinnerCompl
            (J.canonicalProbe.vector) (J.canonicalProbe.vector)))) := by
  have hcurrent := mixed_correlator_sq_decay
    nome_pos nome_lt_one hsmall hd hs
    (R unitExcitation) (R unitExcitation)
    ((center_fixed_iff nome_pos nome_lt_one hsmall hd hs _).mp
      (unitExcitation_resolvent_centered)) 2
  rw [canonicalProbe_twoStepCorrelation_eq_current J]
  rw [canonicalProbe_vector J]
  rw [J.form_preserving (R unitExcitation) (R unitExcitation)]
  have hcorr :
      B (T 2 (R unitExcitation)) (R unitExcitation) =
        B (R unitExcitation) (T 2 (R unitExcitation)) :=
    completedInner_symm nome_pos nome_lt_one hsmall hd hs
      (T 2 (R unitExcitation)) (R unitExcitation)
  have hsq :
      CReal.RCmul
          (B (T 2 (R unitExcitation)) (R unitExcitation))
          (B (T 2 (R unitExcitation)) (R unitExcitation)) =
        CReal.RCmul
          (B (R unitExcitation) (T 2 (R unitExcitation)))
          (B (R unitExcitation) (T 2 (R unitExcitation))) :=
    congrArg (fun z : CReal.RC => CReal.RCmul z z) hcorr
  rw [hsq]
  exact hcurrent

/-! ## The strict form-gap consumer -/

/-- The transported canonical resolvent probe inherits the current carrier's
strict two-step form bound.  The orientation change is only the completed
pairing symmetry; the rate is still the literal fixed-spacing `twoStepRate`.
-/
theorem canonicalProbe_twoStep_form_bound
    (J : CurrentCarrierBridge P) :
    RCle
      (W.toGNSData.cinnerCompl
        (P.op.T (P.op.T (J.canonicalProbe.vector)))
        (J.canonicalProbe.vector))
      (CReal.RCmul
        (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
        (W.toGNSData.cinnerCompl
          (J.canonicalProbe.vector) (J.canonicalProbe.vector))) := by
  have horth : B (R unitExcitation) U = RCzero :=
    (center_fixed_iff nome_pos nome_lt_one hsmall hd hs _).mp
      unitExcitation_resolvent_centered
  have hgap := completed_twoStep_form_gap
    nome_pos nome_lt_one hsmall hd hs (R unitExcitation) horth
  have hsym :
      B (T 2 (R unitExcitation)) (R unitExcitation) =
        B (R unitExcitation) (T 2 (R unitExcitation)) :=
    completedInner_symm nome_pos nome_lt_one hsmall hd hs
      (T 2 (R unitExcitation)) (R unitExcitation)
  rw [canonicalProbe_twoStepCorrelation_eq_current J]
  rw [canonicalProbe_vector J]
  rw [J.form_preserving (R unitExcitation) (R unitExcitation)]
  rw [hsym]
  exact hgap

/-! ## The transported unit-excitation response -/

/-- The normalized current unit excitation remains in the canonical vacuum
complement under the named bridge. -/
theorem canonicalUnitProbe_vacuum_orthogonal
    (J : CurrentCarrierBridge P) :
    W.toGNSData.cinnerCompl (J.map unitExcitation) P.op.vacuum = RCzero :=
  J.image_vacuum_orthogonal unitExcitation_orthogonal

/-- Exact form preservation makes the transported normalized excitation
nonzero; no quotient representative is selected. -/
theorem canonicalUnitProbe_ne_zero
    (J : CurrentCarrierBridge P) :
    J.map unitExcitation ≠ embedV W.toGNSData W.toGNSData.zero := by
  intro hzero
  apply unitExcitation_ne_zero
  apply J.map_injective
  rw [hzero, J.map_zero]

/-- The canonical unit excitation retains the explicit positive current
two-step response floor on the same transferred carrier. -/
theorem canonicalUnitProbe_twoStep_response_floor
    (J : CurrentCarrierBridge P) :
    RCle (Quotient.mk crealSetoid (ofQ' rayleighFloor))
      (W.toGNSData.cinnerCompl
        (P.op.T (P.op.T (J.map unitExcitation)))
        (J.map unitExcitation)) := by
  have hsym :
      B (T 2 unitExcitation) unitExcitation =
        B unitExcitation (T 2 unitExcitation) :=
    completedInner_symm nome_pos nome_lt_one hsmall hd hs
      (T 2 unitExcitation) unitExcitation
  rw [← J.twoStep_intertwines unitExcitation]
  rw [J.form_preserving (T 2 unitExcitation) unitExcitation]
  rw [hsym]
  exact unitExcitation_even_lower 1

/-- Package the transported unit excitation as the minimal canonical
nontriviality witness: vacuum orthogonality, nonzero-ness, and a positive
same-object response floor all refer to one canonical vector. -/
def canonicalUnitProbe
    (J : CurrentCarrierBridge P) : CanonicalUnitProbeData P J where
  vector := J.map unitExcitation
  current_preimage := unitExcitation
  image_eq := rfl
  vacuum_orthogonal := J.canonicalUnitProbe_vacuum_orthogonal
  nonzero := J.canonicalUnitProbe_ne_zero
  twoStep_response_floor := J.canonicalUnitProbe_twoStep_response_floor

/-- The transported canonical unit probe has a genuinely strict positive
two-step response.  The strictness is derived from the rational floor and
does not introduce a second observable or a separate nonzero assumption. -/
theorem canonicalUnitProbe_twoStep_response_not_le_zero
    (J : CurrentCarrierBridge P) :
    ¬ RCle
      (W.toGNSData.cinnerCompl
        (P.op.T (P.op.T J.canonicalUnitProbe.vector))
        J.canonicalUnitProbe.vector)
      RCzero := by
  intro hzero
  apply positive_constant_not_le_zero_local rayleighFloor rayleighFloor_positive
  exact RCle_trans J.canonicalUnitProbe_twoStep_response_floor hzero

/-- The transported unit excitation also obeys the existing strict canonical
two-step form bound; its lower response floor and upper gap bound therefore
refer to one canonical vector. -/
theorem canonicalUnitProbe_twoStep_form_bound
    (J : CurrentCarrierBridge P) :
    RCle
      (W.toGNSData.cinnerCompl
        (P.op.T (P.op.T (J.canonicalUnitProbe.vector)))
        J.canonicalUnitProbe.vector)
      (CReal.RCmul
        (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
        (W.toGNSData.cinnerCompl
          J.canonicalUnitProbe.vector J.canonicalUnitProbe.vector)) := by
  change RCle
    (W.toGNSData.cinnerCompl
      (P.op.T (P.op.T (J.map unitExcitation)))
      (J.map unitExcitation))
    (CReal.RCmul
      (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
      (W.toGNSData.cinnerCompl (J.map unitExcitation) (J.map unitExcitation)))
  exact J.image_twoStep_form_bound unitExcitation_orthogonal

/-- The canonical unit probe also carries the strict residual margin for
`I - T²`, with the same fixed-spacing rate and the same canonical norm. -/
theorem canonicalUnitProbe_twoStep_defect_form_bound
    (J : CurrentCarrierBridge P) :
    RCle
      (CReal.RCscale (1 - twoStepRate nome hd)
        (W.toGNSData.cinnerCompl
          J.canonicalUnitProbe.vector J.canonicalUnitProbe.vector))
      (CReal.RCsub
        (W.toGNSData.cinnerCompl
          J.canonicalUnitProbe.vector J.canonicalUnitProbe.vector)
        (W.toGNSData.cinnerCompl
          (P.op.T (P.op.T J.canonicalUnitProbe.vector))
          J.canonicalUnitProbe.vector)) := by
  change RCle
    (CReal.RCscale (1 - twoStepRate nome hd)
      (W.toGNSData.cinnerCompl
        (J.map unitExcitation) (J.map unitExcitation)))
    (CReal.RCsub
      (W.toGNSData.cinnerCompl
        (J.map unitExcitation) (J.map unitExcitation))
      (W.toGNSData.cinnerCompl
        (P.op.T (P.op.T (J.map unitExcitation)))
        (J.map unitExcitation)))
  exact J.image_twoStep_defect_form_bound unitExcitation_orthogonal

/-- A supplied bridge transports the current fixed-point exclusion to the
canonical unit excitation. -/
theorem canonicalUnitProbe_twoStep_fixed_eq_zero
    (J : CurrentCarrierBridge P)
    (hfixed :
      P.op.T (P.op.T J.canonicalUnitProbe.vector) =
        J.canonicalUnitProbe.vector) :
    J.canonicalUnitProbe.vector = embedV W.toGNSData W.toGNSData.zero := by
  change J.map unitExcitation = embedV W.toGNSData W.toGNSData.zero
  apply J.image_twoStep_fixed_eq_zero unitExcitation_orthogonal
  change
    P.op.T (P.op.T (J.map unitExcitation)) =
      J.map unitExcitation
  exact hfixed

/-- The transported unit excitation is therefore not a two-step fixed vector. -/
theorem canonicalUnitProbe_twoStep_not_fixed
    (J : CurrentCarrierBridge P) :
    ¬ (P.op.T (P.op.T J.canonicalUnitProbe.vector) =
      J.canonicalUnitProbe.vector) := by
  intro hfixed
  apply J.canonicalUnitProbe_ne_zero
  exact J.canonicalUnitProbe_twoStep_fixed_eq_zero hfixed

/-- The canonical unit probe's two-step coefficient is exactly the existing
current-carrier same-object coefficient. -/
theorem canonicalUnitProbe_twoStep_correlation_eq_current
    (J : CurrentCarrierBridge P) :
    W.toGNSData.cinnerCompl
        (P.op.T (P.op.T J.canonicalUnitProbe.vector))
        J.canonicalUnitProbe.vector =
      B (T 2 unitExcitation) unitExcitation := by
  change
    W.toGNSData.cinnerCompl
        (P.op.T (P.op.T (J.map unitExcitation)))
        (J.map unitExcitation) =
      B (T 2 unitExcitation) unitExcitation
  exact J.image_twoStep_correlation_eq_current unitExcitation

/-- The canonical unit probe's norm is exactly the current normalized norm. -/
theorem canonicalUnitProbe_norm_eq_current
    (J : CurrentCarrierBridge P) :
    W.toGNSData.cinnerCompl
        J.canonicalUnitProbe.vector J.canonicalUnitProbe.vector =
      B unitExcitation unitExcitation := by
  change
    W.toGNSData.cinnerCompl
        (J.map unitExcitation) (J.map unitExcitation) =
      B unitExcitation unitExcitation
  exact J.form_preserving unitExcitation unitExcitation

/-! The exact norm identity now closes the selected-probe Rayleigh
    compatibility loop.  This remains an image-level statement: the bridge
    and the all-vector canonical range section are still explicit inputs. -/

/-- The canonical unit probe has the exact unit norm carried by the current
normalized excitation. -/
theorem canonicalUnitProbe_norm_one
    (J : CurrentCarrierBridge P) :
    W.toGNSData.cinnerCompl
        J.canonicalUnitProbe.vector J.canonicalUnitProbe.vector =
      Quotient.mk crealSetoid cone := by
  rw [J.canonicalUnitProbe_norm_eq_current]
  exact unitExcitation_norm

private theorem canonicalUnitProbe_rc_mul_one_local (a : CReal.RC) :
    CReal.RCmul a (Quotient.mk crealSetoid cone) = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (CRealAlg.cmul_cone A)

/-- The canonical unit probe's positive response floor is bounded by the
strict two-step rate after transport through its exact same-object norm. -/
theorem canonicalUnitProbe_response_floor_le_rate_scaled_norm
    (J : CurrentCarrierBridge P) :
    RCle (Quotient.mk crealSetoid (ofQ' rayleighFloor))
      (CReal.RCmul
        (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
        (W.toGNSData.cinnerCompl
          J.canonicalUnitProbe.vector J.canonicalUnitProbe.vector)) := by
  exact RCle_trans J.canonicalUnitProbe.twoStep_response_floor
    J.canonicalUnitProbe_twoStep_form_bound

/-- The selected canonical unit probe therefore forces the literal current
fixed-spacing rate to dominate the positive response floor. -/
theorem canonicalUnitProbe_response_floor_le_rate
    (J : CurrentCarrierBridge P) :
    (rayleighFloor : Q') ≤ twoStepRate nome hd := by
  have h := J.canonicalUnitProbe_response_floor_le_rate_scaled_norm
  rw [J.canonicalUnitProbe_norm_one, canonicalUnitProbe_rc_mul_one_local] at h
  exact YMGap.Continuum.GNSQuotient.GNSData.RCofQ'_le_reflect h

end CurrentCarrierBridge

/-! ## The completed canonical-range consumer

The image estimates above are conditional on a vector already known to come
from the current carrier. The next backward-facing obligation is therefore a
constructive section of the canonical completion through the current carrier.
The section is stated at the supplied Cauchy-stream level, so a future
producer must return representatives and a kernel-checked class equation
rather than invoking choice. When supplied, that class equation is itself an
exact surjectivity witness for the bridge map; no section inhabitant is
constructed here.
-/

/-- A constructive section of the canonical completion through a supplied
current-carrier bridge. This is an explicit producer interface, not an
inhabited assertion: no canonical preimage is selected here. -/
structure CanonicalRangeSectionCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (J : CurrentCarrierBridge P) : Type 2 where
  preimage : CauchyGNS W.toGNSData ->
    (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy
  class_eq : ∀ X : CauchyGNS W.toGNSData,
    Quotient.mk (cauchySetoid W.toGNSData) X =
      J.map (Quotient.mk
        (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid
        (preimage X))

namespace CanonicalRangeSectionCertificate

variable
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    {J : CurrentCarrierBridge P}

def canonicalClass (X : CauchyGNS W.toGNSData) :
    GNSCompletionSpace W.toGNSData :=
  Quotient.mk (cauchySetoid W.toGNSData) X

def currentClass
    (Y : (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy) : V :=
  Quotient.mk
    (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid Y

/-! A supplied section is stronger than a dense-range statement: because every
canonical completion point is represented by a `CauchyGNS`, its class equation
is an exact surjectivity witness for the bridge map.  We expose this only as a
conditional consumer; no section inhabitant is constructed here. -/

theorem map_surjective
    (D : CanonicalRangeSectionCertificate P J) :
    Function.Surjective J.map := by
  intro z
  refine Quotient.inductionOn z ?_
  intro X
  exact ⟨currentClass (D.preimage X), (D.class_eq X).symm⟩

theorem preimage_class_unique
    (D : CanonicalRangeSectionCertificate P J)
    {X Y : CauchyGNS W.toGNSData}
    (hXY : canonicalClass X = canonicalClass Y) :
    currentClass (D.preimage X) = currentClass (D.preimage Y) := by
  apply J.map_injective
  exact (D.class_eq X).symm.trans (hXY.trans (D.class_eq Y))

/-- Descend the supplied canonical preimage map through the canonical Cauchy
quotient.  The well-definedness proof uses `preimage_class_unique`, so no
representative is extracted from a quotient and no choice principle is used. -/
def currentOfCanonical
    (D : CanonicalRangeSectionCertificate P J) :
    GNSCompletionSpace W.toGNSData → V :=
  Quotient.lift
    (fun X => currentClass (D.preimage X))
    (fun _ _ h => D.preimage_class_unique (Quotient.sound h))

/-- The explicit inverse maps every canonical completion class back to its
bridge image. -/
theorem map_currentOfCanonical
    (D : CanonicalRangeSectionCertificate P J)
    (z : GNSCompletionSpace W.toGNSData) :
    J.map (D.currentOfCanonical z) = z := by
  refine Quotient.inductionOn z ?_
  intro X
  exact (D.class_eq X).symm

/-- On the transported unit probe, a supplied canonical range section
round-trips to the exact stored current-carrier preimage. This is the
pointwise naturality statement needed before attempting an all-vector section;
it does not construct that section. -/
theorem currentOfCanonical_unitProbe
    (D : CanonicalRangeSectionCertificate P J) :
    D.currentOfCanonical J.canonicalUnitProbe.vector =
      J.canonicalUnitProbe.current_preimage := by
  apply J.map_injective
  rw [D.map_currentOfCanonical]
  exact J.canonicalUnitProbe.image_eq.symm

/-- The supplied range section therefore identifies the current and canonical
completed carriers in both directions. -/
theorem currentOfCanonical_map
    (D : CanonicalRangeSectionCertificate P J)
    (x : V) :
    D.currentOfCanonical (J.map x) = x := by
  apply J.map_injective
  exact D.map_currentOfCanonical (J.map x)

theorem map_bijective
    (D : CanonicalRangeSectionCertificate P J) :
    (∀ x y, J.map x = J.map y → x = y) ∧
      (∀ z, ∃ x, J.map x = z) :=
  ⟨fun x y h => J.map_injective h, fun z => D.map_surjective z⟩

/-- Every canonical vector orthogonal to the selected vacuum inherits the
strict two-step form bound once the explicit range section is supplied. The
proof is an image rewrite: the section supplies the current preimage, while
`CurrentCarrierBridge.image_twoStep_form_bound` supplies the estimate. No
density, limit interchange, or spectral theorem is hidden in this consumer. -/
theorem twoStep_form_bound
    (D : CanonicalRangeSectionCertificate P J)
    (X : CauchyGNS W.toGNSData)
    (hx : W.toGNSData.cinnerCompl (canonicalClass X) P.op.vacuum = RCzero) :
    RCle
      (W.toGNSData.cinnerCompl
        (P.op.T (P.op.T (canonicalClass X))) (canonicalClass X))
      (CReal.RCmul
        (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
        (W.toGNSData.cinnerCompl (canonicalClass X) (canonicalClass X))) := by
  let Y := D.preimage X
  let y := currentClass Y
  have hyclass : canonicalClass X = J.map y := by
    simpa only [canonicalClass, y, currentClass, Y] using (D.class_eq X)
  have hyorth : B y U = RCzero := by
    calc
      B y U = W.toGNSData.cinnerCompl (J.map y) (J.map U) :=
        (J.form_preserving y U).symm
      _ = W.toGNSData.cinnerCompl (J.map y) P.op.vacuum := by
        rw [J.vacuum_preserving]
      _ = W.toGNSData.cinnerCompl (canonicalClass X) P.op.vacuum := by
        rw [hyclass]
      _ = RCzero := hx
  have himage := J.image_twoStep_form_bound hyorth
  rw [← hyclass] at himage
  exact himage

/-! The residual version is kept alongside the strict form version because it
is the form used by the current resolvent and by later inverse/range consumers.
-/

/-- The same explicit range section transports the `(1-q)` residual margin to
every canonical vacuum-complement vector. -/
theorem twoStep_defect_form_bound
    (D : CanonicalRangeSectionCertificate P J)
    (X : CauchyGNS W.toGNSData)
    (hx : W.toGNSData.cinnerCompl (canonicalClass X) P.op.vacuum = RCzero) :
    RCle
      (CReal.RCscale (1 - twoStepRate nome hd)
        (W.toGNSData.cinnerCompl (canonicalClass X) (canonicalClass X)))
      (CReal.RCsub
        (W.toGNSData.cinnerCompl (canonicalClass X) (canonicalClass X))
        (W.toGNSData.cinnerCompl
          (P.op.T (P.op.T (canonicalClass X))) (canonicalClass X))) := by
  let Y := D.preimage X
  let y := currentClass Y
  have hyclass : canonicalClass X = J.map y := by
    simpa only [canonicalClass, y, currentClass, Y] using (D.class_eq X)
  have hyorth : B y U = RCzero := by
    calc
      B y U = W.toGNSData.cinnerCompl (J.map y) (J.map U) :=
        (J.form_preserving y U).symm
      _ = W.toGNSData.cinnerCompl (J.map y) P.op.vacuum := by
        rw [J.vacuum_preserving]
      _ = W.toGNSData.cinnerCompl (canonicalClass X) P.op.vacuum := by
        rw [hyclass]
      _ = RCzero := hx
  have himage := J.image_twoStep_defect_form_bound hyorth
  rw [← hyclass] at himage
  exact himage

/-- A supplied canonical range section upgrades the image-level fixed-point
exclusion to the whole canonical completion: a vacuum-orthogonal canonical
two-step fixed vector is the canonical zero. -/
theorem twoStep_fixed_eq_zero
    (D : CanonicalRangeSectionCertificate P J)
    (X : CauchyGNS W.toGNSData)
    (hx : W.toGNSData.cinnerCompl (canonicalClass X) P.op.vacuum = RCzero)
    (hfixed : P.op.T (P.op.T (canonicalClass X)) = canonicalClass X) :
    canonicalClass X = embedV W.toGNSData W.toGNSData.zero := by
  let Y := D.preimage X
  let y := currentClass Y
  have hyclass : canonicalClass X = J.map y := by
    simpa only [canonicalClass, y, currentClass, Y] using (D.class_eq X)
  have hyorth : B y U = RCzero := by
    calc
      B y U = W.toGNSData.cinnerCompl (J.map y) (J.map U) :=
        (J.form_preserving y U).symm
      _ = W.toGNSData.cinnerCompl (J.map y) P.op.vacuum := by
        rw [J.vacuum_preserving]
      _ = W.toGNSData.cinnerCompl (canonicalClass X) P.op.vacuum := by
        rw [hyclass]
      _ = RCzero := hx
  have hfixed_image : P.op.T (P.op.T (J.map y)) = J.map y := by
    rw [← hyclass]
    exact hfixed
  have hzero := J.image_twoStep_fixed_eq_zero hyorth hfixed_image
  rw [hyclass]
  exact hzero

end CanonicalRangeSectionCertificate

/-! ## Contracted conditional canonical gap datum -/

/-- The exact canonical completed-gap package produced by a supplied range
section. Its rate and all three operator consequences remain fixed-spacing
SU(2) data; the structure is a downstream interface, not an assertion that a
range section or a continuum limit has been constructed. -/
structure CanonicalCompletedGapCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W) : Type 2 where
  rate_pos : (0 : Q') < twoStepRate nome hd
  rate_lt_one : twoStepRate nome hd < (1 : Q')
  form_bound : ∀ (X : CauchyGNS W.toGNSData),
    W.toGNSData.cinnerCompl
        (CanonicalRangeSectionCertificate.canonicalClass X) P.op.vacuum = RCzero →
    RCle
        (W.toGNSData.cinnerCompl
          (P.op.T (P.op.T (CanonicalRangeSectionCertificate.canonicalClass X)))
          (CanonicalRangeSectionCertificate.canonicalClass X))
        (CReal.RCmul
        (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
        (W.toGNSData.cinnerCompl
          (CanonicalRangeSectionCertificate.canonicalClass X)
          (CanonicalRangeSectionCertificate.canonicalClass X)))
  defect_form_bound : ∀ (X : CauchyGNS W.toGNSData),
    W.toGNSData.cinnerCompl
        (CanonicalRangeSectionCertificate.canonicalClass X) P.op.vacuum = RCzero →
    RCle
      (CReal.RCscale (1 - twoStepRate nome hd)
        (W.toGNSData.cinnerCompl
          (CanonicalRangeSectionCertificate.canonicalClass X)
          (CanonicalRangeSectionCertificate.canonicalClass X)))
      (CReal.RCsub
        (W.toGNSData.cinnerCompl
          (CanonicalRangeSectionCertificate.canonicalClass X)
          (CanonicalRangeSectionCertificate.canonicalClass X))
        (W.toGNSData.cinnerCompl
          (P.op.T (P.op.T (CanonicalRangeSectionCertificate.canonicalClass X)))
          (CanonicalRangeSectionCertificate.canonicalClass X)))
  fixed_eq_zero : ∀ (X : CauchyGNS W.toGNSData),
    W.toGNSData.cinnerCompl
        (CanonicalRangeSectionCertificate.canonicalClass X) P.op.vacuum = RCzero →
    P.op.T (P.op.T (CanonicalRangeSectionCertificate.canonicalClass X)) =
      CanonicalRangeSectionCertificate.canonicalClass X →
    CanonicalRangeSectionCertificate.canonicalClass X =
      embedV W.toGNSData W.toGNSData.zero

namespace CanonicalCompletedGapCertificate

variable
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    {J : CurrentCarrierBridge P}

/-- Contract a supplied canonical range section into the complete conditional
gap datum. Every field is obtained from a previously checked consumer. -/
def ofRangeSection
    (D : CanonicalRangeSectionCertificate P J) :
    CanonicalCompletedGapCertificate P where
  rate_pos := twoStepRate_positive nome_pos hd
  rate_lt_one := twoStepRate_lt_one nome_pos hd hs
  form_bound := fun X hx => D.twoStep_form_bound X hx
  defect_form_bound := fun X hx => D.twoStep_defect_form_bound X hx
  fixed_eq_zero := fun X hx hfixed => D.twoStep_fixed_eq_zero X hx hfixed

end CanonicalCompletedGapCertificate

end YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalRangeSectionCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalRangeSectionCertificate.map_surjective
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalRangeSectionCertificate.preimage_class_unique
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalRangeSectionCertificate.currentOfCanonical
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalRangeSectionCertificate.map_currentOfCanonical
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalRangeSectionCertificate.currentOfCanonical_map
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalRangeSectionCertificate.map_bijective
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalRangeSectionCertificate.twoStep_form_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalRangeSectionCertificate.twoStep_defect_form_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalRangeSectionCertificate.twoStep_fixed_eq_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalCompletedGapCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalCompletedGapCertificate.ofRangeSection
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierCauchyFormCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierCauchyFormCertificate.toFormCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageCauchyTransportCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageCauchyTransportCertificate.mapCauchy
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageCauchyTransportCertificate.mapCauchy_null
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageCauchyStagePairingCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageCauchyStagePairingCertificate.mapCauchy_pairing
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageCauchyStagePairingCertificate.toFormCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageMatchedPhysicalTransferJoin
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageMatchedPhysicalTransferJoin.stageObservable
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageMatchedPhysicalTransferJoin.stageTransfer_intertwines
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageMatchedPhysicalTransferJoin.stageTransfer_square_intertwines
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageCauchyFormCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageCauchyFormCertificate.toCauchyFormCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageCauchyFormCertificate.stageClass
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageCauchyFormCertificate.stageClass_pairing
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageCauchyFormCertificate.stageClass_unit
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageCauchyFormCertificate.stageClass_vacuum_orthogonal
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageCauchyFormCertificate.stageClass_eq_of_current_eq
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStagePairingSeparationCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStagePairingSeparationCertificate.stageClass_eq_iff_current_eq
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStagePairingSeparationCertificate.ofExistingPairingContinuity
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageDenseTwoStepCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageDenseTwoStepCertificate.twoStep_correlation_eq_current
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageDenseTwoStepCertificate.twoStep_form_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageDenseTwoStepCertificate.twoStep_fixed_stage_eq_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageDenseTwoStepCertificate.twoStep_fixed_stage_eq_zero_of_existing_pairing_continuity
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageDenseTwoStepCertificate.toCauchyTwoStepCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentStageDenseTwoStepCertificate.toBridge
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierProbeCertificate.ofFormCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierFormCertificate.distance_preserving
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierFormCertificate.toTwoStepCertificateOfDense
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierFormCertificate.toBridgeOfDense
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierCauchyTwoStepCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierCauchyTwoStepCertificate.toTwoStepCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierCauchyProbeCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierCauchyProbeCertificate.toProbeCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.ofCertificates
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierCauchyFormCertificate.toBridge
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.map_injective
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.image_vacuum_orthogonal
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.image_twoStep_correlation_eq_current
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.image_twoStep_form_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.image_twoStep_defect_form_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.image_twoStep_fixed_eq_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonical_resolvent_norm_floor
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe_norm_floor
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe_ne_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe_twoStepCorrelation_eq_current
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe_twoStep_sq_decay
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe_twoStep_form_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalUnitProbe_vacuum_orthogonal
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalUnitProbe_ne_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalUnitProbe_twoStep_response_floor
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalUnitProbe_twoStep_response_not_le_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalUnitProbe
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalUnitProbe_twoStep_form_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalUnitProbe_twoStep_defect_form_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalUnitProbe_twoStep_fixed_eq_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalUnitProbe_twoStep_not_fixed
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalUnitProbe_twoStep_correlation_eq_current
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalUnitProbe_norm_eq_current
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalUnitProbe_norm_one
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalUnitProbe_response_floor_le_rate_scaled_norm
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalUnitProbe_response_floor_le_rate
