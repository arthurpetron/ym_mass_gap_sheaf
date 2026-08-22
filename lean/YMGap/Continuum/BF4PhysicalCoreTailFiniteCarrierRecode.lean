/-
# Exact finite-carrier recoding for the physical core/tail checker

The literal cutoff-one lower carrier enumerates `2^24` bounded face
labellings before positivity filtering.  Directly reducing the all-source
core/tail checker is therefore not a viable proof architecture.

This file proves the exact compression seam.  If a finite code list maps
onto the literal positive physical carrier with a checked list equality,
then every weight, kernel, core, and tail sum can be checked on the code list
and transported back to the physical carrier.  An encoder/retraction lets an
all-code Boolean check cover every literal physical source.

The matched-AF package exposes the remaining all-scale target as one exact
carrier presentation and one true compressed Boolean scan per scale.  No
such nontrivial presentation or checked family is asserted here.  In
particular, the existing 128-surface signed-Haar moment evaluation is not
silently identified with the separately normalized positive physical
carrier.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCoreTailFiniteChecker

namespace YMGap.Continuum.BF4PhysicalCoreTailFiniteCarrierRecode

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalConditionalDensity
open YMGap.Continuum.BF4PhysicalConditionalDensityContraction
open YMGap.Continuum.BF4PhysicalCoreTailCompletedGap
open YMGap.Continuum.BF4PhysicalCoreTailFiniteChecker
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic transport of a checked mapped carrier -/

private theorem listQSum_map_local
    {A B : Type} (value : B → Q') (decode : A → B) :
    ∀ codes : List A,
      listQSum value (codes.map decode) =
        listQSum (fun code => value (decode code)) codes
  | [] => rfl
  | _ :: tail => by
      simp only [List.map, listQSum]
      rw [listQSum_map_local value decode tail]

/-- A core/tail window checked on a finite code list transports exactly to
the mapped state list.  No injectivity premise is needed: the theorem
preserves the list, including multiplicity and order, literally. -/
def finiteWeightedDensityCoreTailWindow_of_mappedCarrier
    {State Code : Type}
    {states : List State} {codes : List Code}
    {decode : Code → State}
    {weight : State → Q'}
    {kernel : State → State → Q'}
    {sourceCode : Code} {inCore : State → Bool}
    {coreTolerance tailTolerance : Q'}
    (carrier_eq : states = codes.map decode)
    (window :
      FiniteWeightedDensityCoreTailWindow
        codes
        (fun code => weight (decode code))
        (fun left right => kernel (decode left) (decode right))
        sourceCode (fun code => inCore (decode code))
        coreTolerance tailTolerance) :
    FiniteWeightedDensityCoreTailWindow
      states weight kernel (decode sourceCode) inCore
      coreTolerance tailTolerance := by
  refine
    { weight_nonnegative := ?_
      kernel_nonnegative := ?_
      weight_total := ?_
      coreTolerance_nonnegative :=
        window.coreTolerance_nonnegative
      core_pointwise := ?_
      tail_weight := ?_
      tail_kernel := ?_ }
  · intro state hstate
    rw [carrier_eq] at hstate
    obtain ⟨code, hcode, rfl⟩ := List.mem_map.mp hstate
    exact window.weight_nonnegative code hcode
  · intro state hstate
    rw [carrier_eq] at hstate
    obtain ⟨code, hcode, rfl⟩ := List.mem_map.mp hstate
    exact window.kernel_nonnegative code hcode
  · rw [carrier_eq, listQSum_map_local]
    exact window.weight_total
  · intro state hstate hcore
    rw [carrier_eq] at hstate
    obtain ⟨code, hcode, rfl⟩ := List.mem_map.mp hstate
    exact window.core_pointwise code hcode hcore
  · rw [carrier_eq, listQSum_map_local]
    exact window.tail_weight
  · rw [carrier_eq, listQSum_map_local]
    exact window.tail_kernel

/-! ## 2. Exact presentation of one positive physical carrier -/

/-- A finite presentation of the literal positive physical carrier.  The
list equality is the load-bearing compression theorem.  The encoder and its
on-carrier retraction let a code-level all-source scan cover every literal
physical source. -/
structure PhysicalPositiveCarrierPresentation
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) : Type 1 where
  Code : Type
  codes : List Code
  decode : Code → EdgeLabelling
  encode : EdgeLabelling → Code
  carrier_eq :
    centralPositiveHalfStates w hw K half =
      codes.map decode
  encode_mem :
    ∀ source,
      source ∈ centralPositiveHalfStates w hw K half →
        encode source ∈ codes
  decode_encode :
    ∀ source,
      source ∈ centralPositiveHalfStates w hw K half →
        decode (encode source) = source

namespace PhysicalPositiveCarrierPresentation

/-- Every listed code decodes to a literal retained physical source. -/
theorem decode_mem
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (presentation : PhysicalPositiveCarrierPresentation w hw K half)
    (code : presentation.Code)
    (code_mem : code ∈ presentation.codes) :
    presentation.decode code ∈
      centralPositiveHalfStates w hw K half := by
  rw [presentation.carrier_eq]
  exact List.mem_map.mpr ⟨code, code_mem, rfl⟩

/-- Run the exact support-safe row checker on the compressed presentation. -/
def coreTailRowCheck
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (presentation : PhysicalPositiveCarrierPresentation w hw K half)
    (sourceCode : presentation.Code)
    (inCore : EdgeLabelling → Bool) : Bool :=
  finiteWeightedDensityCoreTailCheck
    presentation.codes
    (fun code =>
      centralPhysicalRowMarginal
        w hw K half (presentation.decode code))
    (fun left right =>
      centralPhysicalConditionalDensity
        w hw K half
        (presentation.decode left) (presentation.decode right))
    sourceCode
    (fun code => inCore (presentation.decode code))
    (Q'.mkPos 1 32 (by decide))
    (Q'.mkPos 1 64 (by decide))

/-- A true compressed row check constructs the literal physical core/tail
window for its decoded source. -/
def physicalCoreTailWindow_of_rowCheck
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (presentation : PhysicalPositiveCarrierPresentation w hw K half)
    (sourceCode : presentation.Code)
    (source_mem : sourceCode ∈ presentation.codes)
    (inCore : EdgeLabelling → Bool)
    (checked :
      presentation.coreTailRowCheck sourceCode inCore = true) :
    PhysicalConditionalDensityCoreTailWindow
      w hw K half (presentation.decode sourceCode) inCore where
  source_mem := presentation.decode_mem sourceCode source_mem
  window := ⟨
    finiteWeightedDensityCoreTailWindow_of_mappedCarrier
      presentation.carrier_eq
      (finiteWeightedDensityCoreTailWindow_of_check checked)⟩

/-- Scan every compressed source code.  Target sums are also evaluated on
the compressed carrier, so the literal `2^24` ambient enumeration is absent
once a small exact presentation has been proved. -/
def coreTailAllRowsCheck
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (presentation : PhysicalPositiveCarrierPresentation w hw K half)
    (inCore : presentation.Code → EdgeLabelling → Bool) : Bool :=
  presentation.codes.all fun sourceCode =>
    presentation.coreTailRowCheck
      sourceCode (inCore sourceCode)

/-- Soundness of the compressed all-source scan on the literal physical
carrier. -/
theorem physicalCoreTailWindow_of_allRowsCheck
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    (presentation : PhysicalPositiveCarrierPresentation w hw K half)
    (inCore : presentation.Code → EdgeLabelling → Bool)
    (checked : presentation.coreTailAllRowsCheck inCore = true)
    (source : EdgeLabelling)
    (source_mem :
      source ∈ centralPositiveHalfStates w hw K half) :
    Nonempty
      (PhysicalConditionalDensityCoreTailWindow
        w hw K half source
        (inCore (presentation.encode source))) := by
  let sourceCode := presentation.encode source
  have sourceCode_mem : sourceCode ∈ presentation.codes :=
    presentation.encode_mem source source_mem
  have rowChecked :
      presentation.coreTailRowCheck
          sourceCode (inCore sourceCode) = true :=
    List.all_eq_true.mp checked sourceCode sourceCode_mem
  let window := presentation.physicalCoreTailWindow_of_rowCheck
    sourceCode sourceCode_mem (inCore sourceCode) rowChecked
  have hdecode : presentation.decode sourceCode = source :=
    presentation.decode_encode source source_mem
  rw [hdecode] at window
  exact ⟨window⟩

end PhysicalPositiveCarrierPresentation

/-! ## 3. Matched compressed checks to completed decay -/

/-- The compressed, executable form of the remaining all-scale analytic
frontier.  It asks for an exact finite presentation and a true compressed
all-source check at each matched scale. -/
structure PhysicalCoreTailAFRecodeCheckedCertificate
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q') : Type 1 where
  coupling_pos : ∀ scale, (0 : Q') < coupling scale
  coupling_le_window : ∀ scale, coupling scale ≤ law.g₁
  presentation :
    ∀ scale,
      PhysicalPositiveCarrierPresentation
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
  inCore :
    ∀ scale,
      (presentation scale).Code → EdgeLabelling → Bool
  allRows_checked :
    ∀ scale,
      (presentation scale).coreTailAllRowsCheck
        (inCore scale) = true

namespace PhysicalCoreTailAFRecodeCheckedCertificate

/-- Compile exact carrier recodings and true compressed checks into the
minimal support-safe matched certificate. -/
def toCoreTailCertificate
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (checked : PhysicalCoreTailAFRecodeCheckedCertificate
      family law spacing coupling) :
    PhysicalConditionalDensityCoreTailAFCertificate
      family law spacing coupling where
  coupling_pos := checked.coupling_pos
  coupling_le_window := checked.coupling_le_window
  inCore := fun scale source =>
    checked.inCore scale
      ((checked.presentation scale).encode source)
  coreTail_exists := by
    intro scale source source_mem
    exact
      (checked.presentation scale).physicalCoreTailWindow_of_allRowsCheck
        (checked.inCore scale)
        (checked.allRows_checked scale)
        source source_mem

/-- The compressed checked family gives the completed vacuum form gap. -/
def completed_vacuum_form_gap_data
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (checked : PhysicalCoreTailAFRecodeCheckedCertificate
      family law spacing coupling)
    (scale : Nat) :=
  checked.toCoreTailCertificate
    |>.completed_vacuum_form_gap_data scale

/-- The same compressed checked family gives geometric squared same-vector
completed matrix-coefficient decay. -/
def completed_power_autocorrelationSq_decay_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (checked : PhysicalCoreTailAFRecodeCheckedCertificate
      family law spacing coupling)
    (scale n : Nat)
    (vector : CentralPhysicalGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 vector) :=
  checked.toCoreTailCertificate
    |>.completed_power_autocorrelationSq_decay_sixteenth
      scale n vector horthogonal

end PhysicalCoreTailAFRecodeCheckedCertificate

/-! ## Axiom audit -/

#print axioms finiteWeightedDensityCoreTailWindow_of_mappedCarrier
#print axioms PhysicalPositiveCarrierPresentation.decode_mem
#print axioms PhysicalPositiveCarrierPresentation.physicalCoreTailWindow_of_rowCheck
#print axioms PhysicalPositiveCarrierPresentation.physicalCoreTailWindow_of_allRowsCheck
#print axioms PhysicalCoreTailAFRecodeCheckedCertificate.toCoreTailCertificate
#print axioms PhysicalCoreTailAFRecodeCheckedCertificate.completed_vacuum_form_gap_data
#print axioms PhysicalCoreTailAFRecodeCheckedCertificate.completed_power_autocorrelationSq_decay_sixteenth

end YMGap.Continuum.BF4PhysicalCoreTailFiniteCarrierRecode
