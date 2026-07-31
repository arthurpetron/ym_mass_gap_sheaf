/-
# Grouped BF4 common-kernel Perron/action producer

This module replaces the raw physical-action field in
`BF4CalibratedProfileFarautAt` by the exact BF4 construction.

At one scale the genuine half-amplitude is grouped as

  A(x,b) = sum_m prefix(x,m) terminal(m,b).

The complete physical boundary activity `W(b) B(b) / Z` is pushed through
`terminal`.  Finite Fubini then identifies the action of the common kernel
`prefix(x,m)`, transposed to `m -> x`, with the exact physical marginal.
Strict terminal positivity makes the pushed activity a constructive nonzero
positive activity.  Consequently the only action identity retained as
analytic input is the candidate/Peter--Weyl identity.

The scale-family wrapper uses the identical `bits`, `depth`, and nonlinear
rate for this grouped profile certificate and for the literal physical
buffered rows.  It therefore produces the existing threshold-core/Faraut
package without duplicating either physical activity positivity or the
physical action identification.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction
import YMGap.Continuum.BF4PhysicalDensityThresholdCoreAF

namespace YMGap.Continuum.BF4GroupedCommonKernelPerronAction

set_option maxRecDepth 100000
set_option maxHeartbeats 200000

open YMGap.Constructive
open YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
open YMGap.Continuum.BF4BufferedPerronRowConvergence
open YMGap.Continuum.BF4CalibratedAnchoredProjectiveHarnack
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4FarautAnchoredProfileHarnack
open YMGap.Continuum.BF4FarautJointCarrierAFBudget
open YMGap.Continuum.BF4LocalContractionGluing
open YMGap.Continuum.BF4MatchedBufferedPerronEighthClosure
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction
open YMGap.Continuum.BF4PhysicalConditionalDensityContraction
open YMGap.Continuum.BF4PhysicalDensityThresholdCore
open YMGap.Continuum.BF4PhysicalDensityThresholdCoreAF
open YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.BF4TerminalSmoothingProjective
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One exact grouped physical scale -/

/-- Named type of the strictly positive grouped prefix rows.  Keeping this
large carrier expression behind a definition avoids duplicating it in every
generated projection of `BF4GroupedProfileFarautAt`. -/
def BF4GroupedPositivePrefixRowsAt
    {Middle : Type}
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat)
    (middles : List Middle)
    (prefixWeight : EdgeLabelling → Middle → Q') : Type :=
  PositivePrefixRows
    prefixWeight
    (BF4RetainedProfileStates
      w hw K halfExtent)
    middles

/-- Named terminal cross-ratio certificate type. -/
def BF4GroupedTerminalCertificateAt
    {Middle : Type}
    (K halfExtent : Nat)
    (middles : List Middle)
    (terminal : Middle → EdgeLabelling → Q') : Type :=
  FiniteCrossRatioDiameterCertificate
    terminal middles
    (centralBoundaryChannels K halfExtent)

/-- Named exact BF4 half-amplitude factorization proposition. -/
def BF4GroupedPhysicalGluingAt
    {Middle : Type}
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat)
    (middles : List Middle)
    (prefixWeight : EdgeLabelling → Middle → Q')
    (terminal : Middle → EdgeLabelling → Q') : Prop :=
  ∀ state,
    state ∈
        BF4RetainedProfileStates
          w hw K halfExtent →
      ∀ boundary,
        boundary ∈
            centralBoundaryChannels K halfExtent →
          centralHalfAmplitude
              w K halfExtent state boundary ≈
            FiniteCrossRatioDiameterCertificate.finiteKernelAction
              terminal middles
              (prefixWeight state) boundary

/-- Named common-kernel cross-ratio certificate type. -/
def BF4GroupedCommonCertificateAt
    {Middle : Type}
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat)
    (middles : List Middle)
    (prefixWeight : EdgeLabelling → Middle → Q') : Type :=
  FiniteCrossRatioDiameterCertificate
    (centralGroupedPhysicalCommonKernel prefixWeight)
    middles
    (BF4RetainedProfileStates
      w hw K halfExtent)

/-- Named candidate activity certificate type on the grouped carrier. -/
def BF4GroupedCandidateActivityAt
    {Middle : Type}
    (middles : List Middle)
    (candidate : Middle → Q') : Type :=
  FiniteCrossRatioDiameterCertificate.NonzeroNonnegativeActivity
    middles candidate

/-- Named candidate/Peter--Weyl action-identification proposition. -/
def BF4GroupedCandidateIdentificationAt
    {Middle : Type}
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder : Nat)
    (middles : List Middle)
    (prefixWeight : EdgeLabelling → Middle → Q')
    (candidate : Middle → Q') : Prop :=
  ∀ state,
    state ∈
        BF4RetainedProfileStates
          w hw K halfExtent →
      BF4CalibratedRightProfile
          w hw K halfExtent diagonalOrder state ≈
        FiniteCrossRatioDiameterCertificate.finiteKernelAction
          (centralGroupedPhysicalCommonKernel prefixWeight)
          middles candidate state

/-- Named projective Perron remainder proposition. -/
def BF4GroupedProjectivePerronAt
    {Middle : Type}
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {middles : List Middle}
    {prefixWeight : EdgeLabelling → Middle → Q'}
    (certificate :
      BF4GroupedCommonCertificateAt
        w hw K halfExtent middles prefixWeight)
    (bits depth : Nat) (qS : Q') : Prop :=
  certificate.spread *
      certificate.spread ≤
    (1 : Q') +
      farautPerronSquare bits *
        qS ^ (depth - 2)

/-- A grouped common-kernel certificate at one physical BF4 scale.

The candidate activity and its Peter--Weyl action identity remain explicit
because they concern the calibrated Mehler endpoint.  In contrast, the
physical activity, its nonzero positivity, and its action identity are
constructed by `toProfileFarautAt`. -/
structure BF4GroupedProfileFarautAt
    {Middle : Type}
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder bits depth : Nat)
    (qS : Q') : Type where
  middles : List Middle
  prefixWeight : EdgeLabelling → Middle → Q'
  terminal : Middle → EdgeLabelling → Q'
  prefixRows :
    BF4GroupedPositivePrefixRowsAt
      w hw K halfExtent middles prefixWeight
  terminalCertificate :
    BF4GroupedTerminalCertificateAt
      K halfExtent middles terminal
  physical_gluing :
    BF4GroupedPhysicalGluingAt
      w hw K halfExtent middles
      prefixWeight terminal
  commonCertificate :
    BF4GroupedCommonCertificateAt
      w hw K halfExtent middles prefixWeight
  candidate : Middle → Q'
  candidateActivity :
    BF4GroupedCandidateActivityAt
      middles candidate
  candidate_identification :
    BF4GroupedCandidateIdentificationAt
      w hw K halfExtent diagonalOrder
      middles prefixWeight candidate
  qS_nonnegative :
    (0 : Q') ≤ qS
  qS_le_quarter :
    qS ≤ quarter
  depth_available :
    farautCoreTailRequiredDepth bits ≤ depth
  projectivePerron :
    BF4GroupedProjectivePerronAt
      commonCertificate bits depth qS

namespace BF4GroupedProfileFarautAt

/-- The pushed exact physical activity on the grouped middle carrier. -/
abbrev physicalActivity
    {Middle : Type}
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder bits depth : Nat}
    {qS : Q'}
    (data :
      BF4GroupedProfileFarautAt
        (Middle := Middle)
        w hw K halfExtent diagonalOrder
        bits depth qS) :
    Middle → Q' :=
  centralGroupedPhysicalMiddleActivity
    w hw K halfExtent data.terminal

/-- Construct the existing common-kernel/Faraut interface.  In particular,
`physicalActivity` and `physical_identification` are theorem outputs, not
fields of the grouped input. -/
def toProfileFarautAt
    {Middle : Type}
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder bits depth : Nat}
    {qS : Q'}
    (data :
      BF4GroupedProfileFarautAt
        (Middle := Middle)
        w hw K halfExtent diagonalOrder
        bits depth qS) :
    BF4CalibratedProfileFarautAt
      (Source := Middle)
      w hw K halfExtent diagonalOrder
      bits depth qS where
  kernel :=
    centralGroupedPhysicalCommonKernel
      data.prefixWeight
  sources := data.middles
  candidate := data.candidate
  physical := data.physicalActivity
  certificate := data.commonCertificate
  candidateActivity := data.candidateActivity
  physicalActivity :=
    centralGroupedPhysicalMiddleActivityCertificate
      data.prefixRows data.terminalCertificate
  qS_nonnegative := data.qS_nonnegative
  qS_le_quarter := data.qS_le_quarter
  depth_available := data.depth_available
  projectivePerron := data.projectivePerron
  candidate_identification :=
    data.candidate_identification
  physical_identification := by
    intro state state_mem
    exact Q'.eqv_symm
      (centralGroupedPhysicalCommonKernelAction_eqv_marginal
        data.middles data.prefixWeight data.terminal
        data.physical_gluing state_mem)

end BF4GroupedProfileFarautAt

/-! ## 2. Same-trajectory scale family and threshold-core consumer -/

/-- The exact per-scale stationary gluing type, kept behind a named
definition so the matched-family structure does not repeatedly normalize
the full weight/cutoff expression while elaborating its projections. -/
def MatchedBF4OneStepGluingRowAt
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent bits depth : Nat → Nat)
    (nonlinearRate : Nat → Q')
    (oneStep :
      ∀ (_scale : Nat), EdgeLabelling → EdgeLabelling → Q')
    (scale : Nat) (source : EdgeLabelling) : Type :=
  PhysicalBF4OneStepContractionGluingRow
    (matchedAllSpinWeight_nonnegative
      family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)
    source
    (depth scale)
    (oneStep scale)
    (farautRetainedSpread (bits scale))
    (nonlinearRate scale)

/-- The scale-uniform grouped common-kernel profile construction.

The bit, depth, and nonlinear-rate schedules are parameters rather than
fields.  This lets the stationary gluing family below share them
definitionally without forcing Lean to normalize projections through a
large dependent record. -/
structure MatchedBF4GroupedProfileFarautRows
    (Middle : Nat → Type)
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder bits depth : Nat → Nat)
    (nonlinearRate : Nat → Q') : Type where
  coupling_pos :
    ∀ (scale : Nat), (0 : Q') < coupling scale
  coupling_le_window :
    ∀ (scale : Nat), coupling scale ≤ law.g₁
  groupedProfileAt :
    ∀ (scale : Nat),
      BF4GroupedProfileFarautAt
        (Middle := Middle scale)
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale)
        (bits scale)
        (depth scale)
        (nonlinearRate scale)

/-- Genuine one-step stationary density gluing rows on a fixed matched-AF
schedule.  This is deliberately a constructive dependent function rather
than a structure: no choice is needed, and Lean need not generate enormous
recursors for the proof-dependent physical row type.

Every returned row lives on the literal positive BF4 carrier.  Its
`PhysicalBF4FarautBufferedRow` is computed by
`PhysicalBF4OneStepContractionGluingRow.toFarautBufferedRow`; it is not an
independent assumption. -/
def MatchedBF4OneStepGluingRows
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent bits depth : Nat → Nat)
    (nonlinearRate : Nat → Q')
    (oneStep :
      ∀ (_scale : Nat), EdgeLabelling → EdgeLabelling → Q') : Type :=
  ∀ (scale : Nat) (source : EdgeLabelling),
    source ∈
        centralPositiveHalfStates
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale) →
      MatchedBF4OneStepGluingRowAt
        family coupling halfExtent bits depth
        nonlinearRate oneStep scale source

namespace MatchedBF4GroupedProfileFarautRows

/-- Combine the grouped common-kernel profile with a genuine stationary
one-step gluing family on the definitionally identical AF schedule.

This constructs both formerly abstract layers:

* exact physical common-kernel action is supplied by
  `BF4GroupedProfileFarautAt.toProfileFarautAt`; and
* the witness-bearing physical Faraut buffer is supplied by
  `PhysicalBF4OneStepContractionGluingRow.toFarautBufferedRow`.

Only the candidate/Peter--Weyl and projective-Perron estimates remain inside
the grouped profile input, while the one-step Yang--Mills estimates remain
inside the gluing input. -/
def toThresholdCoreFarautRows
    {Middle : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    (profile :
      MatchedBF4GroupedProfileFarautRows
        Middle family law spacing coupling
        halfExtent diagonalOrder bits depth
        nonlinearRate)
    (oneStep :
      ∀ (_scale : Nat), EdgeLabelling → EdgeLabelling → Q')
    (gluingRows :
      MatchedBF4OneStepGluingRows
        family coupling halfExtent bits depth
        nonlinearRate oneStep) :
    MatchedBF4ThresholdCoreFarautRows
      Middle family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := profile.coupling_pos
  coupling_le_window := profile.coupling_le_window
  bits := bits
  depth := depth
  nonlinearRate := nonlinearRate
  profileAt := fun scale =>
    (profile.groupedProfileAt scale).toProfileFarautAt
  bufferedRow_exists := by
    intro scale source source_mem
    have row :=
      gluingRows scale source source_mem
    change
      PhysicalBF4OneStepContractionGluingRow
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        source
        (depth scale)
        (oneStep scale)
        (farautRetainedSpread (bits scale))
        (nonlinearRate scale) at row
    exact ⟨
      row.toFarautBufferedRow⟩

/-- The grouped exact action construction and the same-schedule physical
buffered rows produce the already proved source-dependent core, both
`1/64` tails, and the two rowwise eighths. -/
def toRowwiseEighthEstimates
    {Middle : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    (profile :
      MatchedBF4GroupedProfileFarautRows
        Middle family law spacing coupling
        halfExtent diagonalOrder bits depth
        nonlinearRate)
    (oneStep :
      ∀ (_scale : Nat), EdgeLabelling → EdgeLabelling → Q')
    (gluingRows :
      MatchedBF4OneStepGluingRows
        family coupling halfExtent bits depth
        nonlinearRate oneStep) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  (profile.toThresholdCoreFarautRows
      oneStep gluingRows)
    |>.toRowwiseEighthEstimates

end MatchedBF4GroupedProfileFarautRows

/-! ## 3. Preferred boundary-carrier terminal-smoothed producer -/

/-- The strict common-kernel certificate obtained by terminal smoothing and
then transposition.  Its sources are complete fixed-interface channels and
its targets are retained physical rows.  Its spread is definitionally the
primitive terminal spread, so no positivity or Harnack certificate for the
generally zero-containing prefix is needed. -/
def centralGroupedBoundaryCertificate
    {Middle : Type}
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {middles : List Middle}
    {prefixWeight : EdgeLabelling → Middle → Q'}
    {terminal : Middle → EdgeLabelling → Q'}
    (terminalCertificate :
      BF4GroupedTerminalCertificateAt
        K halfExtent middles terminal)
    (prefixRows :
      BF4GroupedPositivePrefixRowsAt
        w hw K halfExtent middles prefixWeight) :
    FiniteCrossRatioDiameterCertificate
      (centralGroupedBoundaryCommonKernel
        middles prefixWeight terminal)
      (centralBoundaryChannels K halfExtent)
      (BF4RetainedProfileStates
        w hw K halfExtent) := by
  exact transposeCertificate
    (terminalSmoothedCertificate
      terminalCertificate prefixRows)

/-- The boundary-carrier certificate preserves the primitive terminal
spread exactly. -/
theorem centralGroupedBoundaryCertificate_spread
    {Middle : Type}
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {middles : List Middle}
    {prefixWeight : EdgeLabelling → Middle → Q'}
    {terminal : Middle → EdgeLabelling → Q'}
    (terminalCertificate :
      BF4GroupedTerminalCertificateAt
        K halfExtent middles terminal)
    (prefixRows :
      BF4GroupedPositivePrefixRowsAt
        w hw K halfExtent middles prefixWeight) :
    (centralGroupedBoundaryCertificate
      terminalCertificate prefixRows).spread =
        terminalCertificate.spread :=
  rfl

/-- Candidate activity certificate on the complete boundary carrier. -/
def BF4BoundaryGroupedCandidateActivityAt
    (K halfExtent : Nat)
    (candidate : EdgeLabelling → Q') : Type :=
  FiniteCrossRatioDiameterCertificate.NonzeroNonnegativeActivity
    (centralBoundaryChannels K halfExtent)
    candidate

/-- Candidate/Peter--Weyl action identification for the preferred
terminal-smoothed boundary common kernel. -/
def BF4BoundaryGroupedCandidateIdentificationAt
    {Middle : Type}
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder : Nat)
    (middles : List Middle)
    (prefixWeight : EdgeLabelling → Middle → Q')
    (terminal : Middle → EdgeLabelling → Q')
    (candidate : EdgeLabelling → Q') : Prop :=
  ∀ state,
    state ∈
        BF4RetainedProfileStates
          w hw K halfExtent →
      BF4CalibratedRightProfile
          w hw K halfExtent diagonalOrder state ≈
        FiniteCrossRatioDiameterCertificate.finiteKernelAction
          (centralGroupedBoundaryCommonKernel
            middles prefixWeight terminal)
          (centralBoundaryChannels K halfExtent)
          candidate state

/-- Projective-Perron remainder stated only for the primitive terminal
certificate.  The common boundary certificate has the same spread by
definition. -/
def BF4BoundaryGroupedProjectivePerronAt
    {Middle : Type}
    {K halfExtent : Nat}
    {middles : List Middle}
    {terminal : Middle → EdgeLabelling → Q'}
    (terminalCertificate :
      BF4GroupedTerminalCertificateAt
        K halfExtent middles terminal)
    (bits depth : Nat) (qS : Q') : Prop :=
  terminalCertificate.spread *
      terminalCertificate.spread ≤
    (1 : Q') +
      farautPerronSquare bits *
        qS ^ (depth - 2)

/-- Preferred one-scale grouped profile data.

Compared with `BF4GroupedProfileFarautAt`, this structure has no common
prefix-kernel certificate field.  Terminal smoothing constructs the common
boundary kernel and its certificate, while the exact physical boundary
activity and action are supplied by theorem.  The remaining profile inputs
are precisely the candidate/Peter--Weyl boundary activity and the primitive
terminal Perron estimate. -/
structure BF4BoundaryGroupedProfileFarautAt
    {Middle : Type}
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder bits depth : Nat)
    (qS : Q') : Type where
  middles : List Middle
  prefixWeight : EdgeLabelling → Middle → Q'
  terminal : Middle → EdgeLabelling → Q'
  prefixRows :
    BF4GroupedPositivePrefixRowsAt
      w hw K halfExtent middles prefixWeight
  terminalCertificate :
    BF4GroupedTerminalCertificateAt
      K halfExtent middles terminal
  physical_gluing :
    BF4GroupedPhysicalGluingAt
      w hw K halfExtent middles
      prefixWeight terminal
  candidate : EdgeLabelling → Q'
  candidateActivity :
    BF4BoundaryGroupedCandidateActivityAt
      K halfExtent candidate
  candidate_identification :
    BF4BoundaryGroupedCandidateIdentificationAt
      w hw K halfExtent diagonalOrder
      middles prefixWeight terminal candidate
  qS_nonnegative :
    (0 : Q') ≤ qS
  qS_le_quarter :
    qS ≤ quarter
  depth_available :
    farautCoreTailRequiredDepth bits ≤ depth
  projectivePerron :
    BF4BoundaryGroupedProjectivePerronAt
      terminalCertificate bits depth qS

namespace BF4BoundaryGroupedProfileFarautAt

/-- Construct the calibrated profile/Faraut interface on the preferred
boundary carrier.  Both the common certificate and the entire physical
activity/action side are computed. -/
def toProfileFarautAt
    {Middle : Type}
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder bits depth : Nat}
    {qS : Q'}
    (data :
      BF4BoundaryGroupedProfileFarautAt
        (Middle := Middle)
        w hw K halfExtent diagonalOrder
        bits depth qS) :
    BF4CalibratedProfileFarautAt
      (Source := EdgeLabelling)
      w hw K halfExtent diagonalOrder
      bits depth qS where
  kernel :=
    centralGroupedBoundaryCommonKernel
      data.middles data.prefixWeight data.terminal
  sources :=
    centralBoundaryChannels K halfExtent
  candidate := data.candidate
  physical :=
    centralPhysicalBoundaryActivity
      w hw K halfExtent
  certificate :=
    centralGroupedBoundaryCertificate
      data.terminalCertificate data.prefixRows
  candidateActivity := data.candidateActivity
  physicalActivity :=
    centralPhysicalBoundaryActivityCertificate
      w hw K halfExtent
  qS_nonnegative := data.qS_nonnegative
  qS_le_quarter := data.qS_le_quarter
  depth_available := data.depth_available
  projectivePerron := data.projectivePerron
  candidate_identification :=
    data.candidate_identification
  physical_identification := by
    intro state state_mem
    exact Q'.eqv_symm
      (centralGroupedBoundaryCommonKernelAction_eqv_marginal
        data.middles data.prefixWeight data.terminal
        data.physical_gluing state_mem)

end BF4BoundaryGroupedProfileFarautAt

/-- Scale-uniform preferred boundary-carrier profiles on explicit shared
bit/depth/nonlinear-rate schedules. -/
structure MatchedBF4BoundaryGroupedProfileFarautRows
    (Middle : Nat → Type)
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder bits depth : Nat → Nat)
    (nonlinearRate : Nat → Q') : Type where
  coupling_pos :
    ∀ (scale : Nat), (0 : Q') < coupling scale
  coupling_le_window :
    ∀ (scale : Nat), coupling scale ≤ law.g₁
  profileAt :
    ∀ (scale : Nat),
      BF4BoundaryGroupedProfileFarautAt
        (Middle := Middle scale)
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale)
        (bits scale)
        (depth scale)
        (nonlinearRate scale)

namespace MatchedBF4BoundaryGroupedProfileFarautRows

/-- Combine the preferred boundary-carrier profiles with genuine one-step
stationary gluing rows on the identical AF schedule. -/
def toThresholdCoreFarautRows
    {Middle : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    (profile :
      MatchedBF4BoundaryGroupedProfileFarautRows
        Middle family law spacing coupling
        halfExtent diagonalOrder bits depth
        nonlinearRate)
    (oneStep :
      ∀ (_scale : Nat), EdgeLabelling → EdgeLabelling → Q')
    (gluingRows :
      MatchedBF4OneStepGluingRows
        family coupling halfExtent bits depth
        nonlinearRate oneStep) :
    MatchedBF4ThresholdCoreFarautRows
      (fun _ => EdgeLabelling)
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := profile.coupling_pos
  coupling_le_window := profile.coupling_le_window
  bits := bits
  depth := depth
  nonlinearRate := nonlinearRate
  profileAt := fun scale =>
    (profile.profileAt scale).toProfileFarautAt
  bufferedRow_exists := by
    intro scale source source_mem
    have row :=
      gluingRows scale source source_mem
    change
      PhysicalBF4OneStepContractionGluingRow
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        source
        (depth scale)
        (oneStep scale)
        (farautRetainedSpread (bits scale))
        (nonlinearRate scale) at row
    exact ⟨row.toFarautBufferedRow⟩

/-- The preferred boundary common kernel plus one-step stationary gluing
constructs both rowwise eighth estimates. -/
def toRowwiseEighthEstimates
    {Middle : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    (profile :
      MatchedBF4BoundaryGroupedProfileFarautRows
        Middle family law spacing coupling
        halfExtent diagonalOrder bits depth
        nonlinearRate)
    (oneStep :
      ∀ (_scale : Nat), EdgeLabelling → EdgeLabelling → Q')
    (gluingRows :
      MatchedBF4OneStepGluingRows
        family coupling halfExtent bits depth
        nonlinearRate oneStep) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  (profile.toThresholdCoreFarautRows
      oneStep gluingRows)
    |>.toRowwiseEighthEstimates

end MatchedBF4BoundaryGroupedProfileFarautRows

/-! ## 4. Direct terminal-Harnack route without a Perron-form field -/

/-- Preferred one-scale boundary profile with the analytically minimal
terminal Harnack input.  The terminal squared-spread cap is stated directly;
no representation as `1 + C_b² q^(m-2)` is required merely to construct the
two calibrated profile windows.

The `qS` and depth fields remain because the independent stationary buffer
uses them to pay the physical density core and tails. -/
structure BF4BoundaryGroupedProfileHarnackAt
    {Middle : Type}
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder bits depth : Nat)
    (qS : Q') : Type where
  middles : List Middle
  prefixWeight : EdgeLabelling → Middle → Q'
  terminal : Middle → EdgeLabelling → Q'
  prefixRows :
    BF4GroupedPositivePrefixRowsAt
      w hw K halfExtent middles prefixWeight
  terminalCertificate :
    BF4GroupedTerminalCertificateAt
      K halfExtent middles terminal
  terminal_spread_square_le :
    terminalCertificate.spread *
        terminalCertificate.spread ≤
      anchoredProjectiveCeiling
  physical_gluing :
    BF4GroupedPhysicalGluingAt
      w hw K halfExtent middles
      prefixWeight terminal
  candidate : EdgeLabelling → Q'
  candidateActivity :
    BF4BoundaryGroupedCandidateActivityAt
      K halfExtent candidate
  candidate_identification :
    BF4BoundaryGroupedCandidateIdentificationAt
      w hw K halfExtent diagonalOrder
      middles prefixWeight terminal candidate
  qS_nonnegative :
    (0 : Q') ≤ qS
  qS_le_quarter :
    qS ≤ quarter
  depth_available :
    farautCoreTailRequiredDepth bits ≤ depth

namespace BF4BoundaryGroupedProfileHarnackAt

/-- Construct both calibrated cross-zero profile windows directly from the
terminal spread cap and the exact boundary-carrier actions. -/
def toCalibratedHarnack
    {Middle : Type}
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder bits depth : Nat}
    {qS : Q'}
    (data :
      BF4BoundaryGroupedProfileHarnackAt
        (Middle := Middle)
        w hw K halfExtent diagonalOrder
        bits depth qS) :
    CalibratedEmptyProfileHarnackData
      w hw K halfExtent diagonalOrder 0 :=
  calibratedEmptyCrossZeroProfileHarnackData_of_kernelActions
    w hw K halfExtent diagonalOrder
    (centralGroupedBoundaryCommonKernel
      data.middles data.prefixWeight data.terminal)
    (centralBoundaryChannels K halfExtent)
    data.candidate
    (centralPhysicalBoundaryActivity
      w hw K halfExtent)
    (centralGroupedBoundaryCertificate
      data.terminalCertificate data.prefixRows)
    data.candidateActivity
    (centralPhysicalBoundaryActivityCertificate
      w hw K halfExtent)
    data.terminal_spread_square_le
    data.candidate_identification
    (fun _state state_mem =>
      Q'.eqv_symm
        (centralGroupedBoundaryCommonKernelAction_eqv_marginal
          data.middles data.prefixWeight data.terminal
          data.physical_gluing state_mem))

end BF4BoundaryGroupedProfileHarnackAt

/-- A quantitative terminal Perron profile canonically yields the direct
terminal-Harnack profile.  This records that the Perron-form estimate is a
sufficient construction route, not part of the minimal final interface. -/
def BF4BoundaryGroupedProfileFarautAt.toProfileHarnackAt
    {Middle : Type}
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder bits depth : Nat}
    {qS : Q'}
    (data :
      BF4BoundaryGroupedProfileFarautAt
        (Middle := Middle)
        w hw K halfExtent diagonalOrder
        bits depth qS) :
    BF4BoundaryGroupedProfileHarnackAt
      (Middle := Middle)
      w hw K halfExtent diagonalOrder
      bits depth qS where
  middles := data.middles
  prefixWeight := data.prefixWeight
  terminal := data.terminal
  prefixRows := data.prefixRows
  terminalCertificate := data.terminalCertificate
  terminal_spread_square_le := by
    apply
      spreadSquare_le_anchoredProjectiveCeiling_of_farautPerron
        data.terminalCertificate
        bits qS depth
        data.qS_nonnegative
        data.qS_le_quarter
    · have hdepth := data.depth_available
      unfold farautCoreTailRequiredDepth at hdepth
      unfold farautHarnackRequiredDepth
      omega
    · exact data.projectivePerron
  physical_gluing := data.physical_gluing
  candidate := data.candidate
  candidateActivity := data.candidateActivity
  candidate_identification :=
    data.candidate_identification
  qS_nonnegative := data.qS_nonnegative
  qS_le_quarter := data.qS_le_quarter
  depth_available := data.depth_available

/-- Scale-uniform direct terminal-Harnack profiles sharing the literal
bit/depth/nonlinear-rate schedule used by the stationary buffer. -/
structure MatchedBF4BoundaryGroupedCoreHarnackRows
    (Middle : Nat → Type)
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder bits depth : Nat → Nat)
    (nonlinearRate : Nat → Q') : Type where
  coupling_pos :
    ∀ (scale : Nat), (0 : Q') < coupling scale
  coupling_le_window :
    ∀ (scale : Nat), coupling scale ≤ law.g₁
  profileAt :
    ∀ (scale : Nat),
      BF4BoundaryGroupedProfileHarnackAt
        (Middle := Middle scale)
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale)
        (bits scale)
        (depth scale)
        (nonlinearRate scale)

/-- Scale-uniform Perron profiles forget canonically to the minimal direct
terminal-Harnack family on the identical schedule. -/
def MatchedBF4BoundaryGroupedProfileFarautRows.toCoreHarnackRows
    {Middle : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    (profile :
      MatchedBF4BoundaryGroupedProfileFarautRows
        Middle family law spacing coupling
        halfExtent diagonalOrder bits depth
        nonlinearRate) :
    MatchedBF4BoundaryGroupedCoreHarnackRows
      Middle family law spacing coupling
      halfExtent diagonalOrder bits depth
      nonlinearRate where
  coupling_pos := profile.coupling_pos
  coupling_le_window := profile.coupling_le_window
  profileAt := fun scale =>
    (profile.profileAt scale).toProfileHarnackAt

namespace MatchedBF4BoundaryGroupedCoreHarnackRows

/-- Direct terminal Harnack plus genuine one-step stationary gluing
constructs the executable physical core and both tails without retaining a
Perron-form profile field. -/
def toMatchedCoreTailRows
    {Middle : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    (profile :
      MatchedBF4BoundaryGroupedCoreHarnackRows
        Middle family law spacing coupling
        halfExtent diagonalOrder bits depth
        nonlinearRate)
    (oneStep :
      ∀ (_scale : Nat), EdgeLabelling → EdgeLabelling → Q')
    (gluingRows :
      MatchedBF4OneStepGluingRows
        family coupling halfExtent bits depth
        nonlinearRate oneStep) :
    MatchedPhysicalConditionalDensityCoreTailRows
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := profile.coupling_pos
  coupling_le_window := profile.coupling_le_window
  calibrated_harnack := fun scale =>
    (profile.profileAt scale).toCalibratedHarnack
  inCore := fun scale source =>
    centralPhysicalThirtySecondCore
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale)
      source
  coreTail_exists := by
    intro scale source source_mem
    have oneStepRow :=
      gluingRows scale source source_mem
    change
      PhysicalBF4OneStepContractionGluingRow
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        source
        (depth scale)
        (oneStep scale)
        (farautRetainedSpread (bits scale))
        (nonlinearRate scale) at oneStepRow
    let row := oneStepRow.toFarautBufferedRow
    let scaleProfile := profile.profileAt scale
    exact ⟨
      PhysicalBF4FarautBufferedRow.toThirtySecondCoreTailWindow
        row source_mem
        scaleProfile.qS_nonnegative
        scaleProfile.qS_le_quarter
        scaleProfile.depth_available⟩

/-- The direct terminal-Harnack route therefore constructs both requested
rowwise eighth estimates. -/
def toRowwiseEighthEstimates
    {Middle : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    (profile :
      MatchedBF4BoundaryGroupedCoreHarnackRows
        Middle family law spacing coupling
        halfExtent diagonalOrder bits depth
        nonlinearRate)
    (oneStep :
      ∀ (_scale : Nat), EdgeLabelling → EdgeLabelling → Q')
    (gluingRows :
      MatchedBF4OneStepGluingRows
        family coupling halfExtent bits depth
        nonlinearRate oneStep) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  (profile.toMatchedCoreTailRows
      oneStep gluingRows)
    |>.toRowwiseEighthEstimates

/-- Genuine local one-step BF4 contraction rows on the identical physical
schedule.  This dependent function retains the kernel as data and needs no
choice when a scale/source row is consumed. -/
def MatchedBF4LocalContractionGluingRows
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent depth : Nat → Nat)
    (localRate : Nat → Q')
    (oneStep :
      ∀ (_scale : Nat), EdgeLabelling → EdgeLabelling → Q') : Type :=
  ∀ (scale : Nat) (source : EdgeLabelling),
    source ∈
        centralPositiveHalfStates
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale) →
      PhysicalBF4LocalContractionGluingRow
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        source
        (depth scale)
        (oneStep scale)
        (localRate scale)

/-- The direct terminal Harnack and the actual local slice contraction
construct the existing endpoint-free physical contraction family. -/
def toMatchedLocalContractionRows
    {Middle : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    (profile :
      MatchedBF4BoundaryGroupedCoreHarnackRows
        Middle family law spacing coupling
        halfExtent diagonalOrder bits depth
        nonlinearRate)
    (oneStep :
      ∀ (_scale : Nat), EdgeLabelling → EdgeLabelling → Q')
    (localRows :
      MatchedBF4LocalContractionGluingRows
        family coupling halfExtent depth
        nonlinearRate oneStep) :
    MatchedPhysicalBF4LocalContractionRows
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := profile.coupling_pos
  coupling_le_window := profile.coupling_le_window
  calibrated_harnack := fun scale =>
    (profile.profileAt scale).toCalibratedHarnack
  depth := depth
  localRate := nonlinearRate
  localRate_le_quarter := fun scale =>
    (profile.profileAt scale).qS_le_quarter
  localRow_exists := by
    intro scale source source_mem
    exact ⟨⟨
      oneStep scale,
      localRows scale source source_mem⟩⟩

/-- Preferred endpoint-free route to both rowwise eighths. -/
def toRowwiseEighthEstimatesOfLocalContraction
    {Middle : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    (profile :
      MatchedBF4BoundaryGroupedCoreHarnackRows
        Middle family law spacing coupling
        halfExtent diagonalOrder bits depth
        nonlinearRate)
    (oneStep :
      ∀ (_scale : Nat), EdgeLabelling → EdgeLabelling → Q')
    (localRows :
      MatchedBF4LocalContractionGluingRows
        family coupling halfExtent depth
        nonlinearRate oneStep) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  (profile.toMatchedLocalContractionRows
      oneStep localRows)
    |>.toRowwiseEighthEstimates

end MatchedBF4BoundaryGroupedCoreHarnackRows

end YMGap.Continuum.BF4GroupedCommonKernelPerronAction

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4GroupedCommonKernelPerronAction.BF4GroupedProfileFarautAt.toProfileFarautAt
#print axioms YMGap.Continuum.BF4GroupedCommonKernelPerronAction.MatchedBF4GroupedProfileFarautRows.toThresholdCoreFarautRows
#print axioms YMGap.Continuum.BF4GroupedCommonKernelPerronAction.MatchedBF4GroupedProfileFarautRows.toRowwiseEighthEstimates
#print axioms YMGap.Continuum.BF4GroupedCommonKernelPerronAction.centralGroupedBoundaryCertificate
#print axioms YMGap.Continuum.BF4GroupedCommonKernelPerronAction.BF4BoundaryGroupedProfileFarautAt.toProfileFarautAt
#print axioms YMGap.Continuum.BF4GroupedCommonKernelPerronAction.MatchedBF4BoundaryGroupedProfileFarautRows.toThresholdCoreFarautRows
#print axioms YMGap.Continuum.BF4GroupedCommonKernelPerronAction.MatchedBF4BoundaryGroupedProfileFarautRows.toRowwiseEighthEstimates
#print axioms YMGap.Continuum.BF4GroupedCommonKernelPerronAction.BF4BoundaryGroupedProfileHarnackAt.toCalibratedHarnack
#print axioms YMGap.Continuum.BF4GroupedCommonKernelPerronAction.BF4BoundaryGroupedProfileFarautAt.toProfileHarnackAt
#print axioms YMGap.Continuum.BF4GroupedCommonKernelPerronAction.MatchedBF4BoundaryGroupedProfileFarautRows.toCoreHarnackRows
#print axioms YMGap.Continuum.BF4GroupedCommonKernelPerronAction.MatchedBF4BoundaryGroupedCoreHarnackRows.toMatchedCoreTailRows
#print axioms YMGap.Continuum.BF4GroupedCommonKernelPerronAction.MatchedBF4BoundaryGroupedCoreHarnackRows.toRowwiseEighthEstimates
#print axioms YMGap.Continuum.BF4GroupedCommonKernelPerronAction.MatchedBF4BoundaryGroupedCoreHarnackRows.toMatchedLocalContractionRows
#print axioms YMGap.Continuum.BF4GroupedCommonKernelPerronAction.MatchedBF4BoundaryGroupedCoreHarnackRows.toRowwiseEighthEstimatesOfLocalContraction
