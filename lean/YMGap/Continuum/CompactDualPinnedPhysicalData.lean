/-
# One physical data object for the finite spin foam, reflection form, and RG state

This module supplies the structural CD-0 interface requested in `work_plan.md`.
One `CompactDualPhysicalData` value fixes the rational coupling, physical
representation cutoff, finite box, and observable packet.  Its projections
are definitionally the already existing finite-volume objects:

* the physical plaquette and link enumerations;
* the coupling-parametric heat-kernel face packet;
* the fusion-complete compensated packet graph;
* the physical spin-foam term and partition;
* the Schur-normalized algebraic reflection weights `w^(4 C₂(s))`;
* the observable coefficients used in the diagonal reflection form.

The `Pinned` carrier is a singleton indexed by an existing value.  It lets the
generic `RGInterface`/`RGState` types retain these exact values at the type
level: constructing a state for this interface cannot silently substitute a
different coupling, cutoff, box, packet graph, link term, or observable.
It is structural plumbing, not an analytic RG or contraction witness.

## Honest remaining interface

`ReflectionPositivity.reflSchwinger` is parameterized by rational heat time
`t` and the constructive-real weight `exp (-t C₂(s))`.  The finite spin-foam
packet is parameterized by rational `w` and the exact coefficient
`(s+1) w^(4 C₂(s))`.  This module pins the exact algebraic Schur form obtained
from that same rational packet.  It does **not** identify it with
`reflSchwinger`: doing so requires a proved coordinate bridge
`w = exp (-t/4)`, which is not presently available in the repository's exact
rational/constructive-real interfaces.

No analytic contraction, stable-manifold, landing, thermodynamic-limit, or
mass-gap claim is made here.

## Axiom gate

Definitions, reduction, and previously audited finite-volume/reflection
lemmas only.  No `Classical.*`, `sorry`, `native_decide`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.Z4ParametricArbitraryCutoffSpinFoamIdentity
import YMGap.Continuum.ReflectionPositivity
import YMGap.RG.PolynomialTree

namespace YMGap.Continuum.CompactDualPinnedPhysicalData

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricArbitraryCutoffSpinFoamIdentity
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.RG.PolynomialTree

local infix:50 " ≈ " => Q'.eqv

/-! ## The common physical datum and its existing finite-volume views -/

/-- The physical choices shared by every consumer in this module.

The observable is an existing `CharacterPacket` at the very same physical
cutoff; it cannot be supplied at a different cutoff. -/
structure CompactDualPhysicalData : Type where
  coupling : Q'
  coupling_nonnegative : (0 : Q') ≤ coupling
  cutoff : Nat
  boxExtent : Nat
  observable : CharacterPacket cutoff

namespace CompactDualPhysicalData

/-- The existing physical plaquette enumeration for the selected box. -/
def faceEdges (D : CompactDualPhysicalData) : List Nat :=
  physicalFaceEdges D.boxExtent

/-- The existing deduplicated physical-link enumeration for the selected box. -/
def enumeratedLinks (D : CompactDualPhysicalData) : List (Nat × Z4Link) :=
  enumerate (distinctBoxLinks D.boxExtent)

/-- The exact heat-kernel packet at the selected coupling and physical cutoff. -/
def facePacket (D : CompactDualPhysicalData) : CharacterPacket D.cutoff :=
  heatKernelPacket D.cutoff D.coupling

/-- The existing fusion-complete packet graph at the same coupling/cutoff/box. -/
def packetGraphState (D : CompactDualPhysicalData) :
    CompensatedGraphState (linkAuxiliaryCutoff D.cutoff) :=
  parametricFusionCompleteBoxState D.coupling D.cutoff D.boxExtent

/-- The existing physical face factor, with no reparameterization. -/
def faceFactor (D : CompactDualPhysicalData) (physical : EdgeLabelling) : Q' :=
  parametricKPhysicalFaceFactor
    D.coupling D.cutoff D.boxExtent physical

/-- The existing physical spin-foam summand.  Its link factor consumes
`D.enumeratedLinks` by definitional equality. -/
def physicalTerm (D : CompactDualPhysicalData) (physical : EdgeLabelling) : Q' :=
  parametricKPhysicalTerm D.coupling D.cutoff D.boxExtent physical

/-- The existing finite-volume physical partition. -/
def physicalPartition (D : CompactDualPhysicalData) : Q' :=
  parametricKPhysicalPartition D.coupling D.cutoff D.boxExtent

/-- The shared-link expansion is literally the existing physical term. -/
theorem physicalTerm_eq_faceFactor_mul_enumeratedLinks
    (D : CompactDualPhysicalData) (physical : EdgeLabelling) :
    D.physicalTerm physical =
      D.faceFactor physical *
        explicitLinkMultiplicityProduct D.cutoff D.boxExtent physical
          D.enumeratedLinks :=
  rfl

/-- The literal packet-graph Cartesian sum is the physical partition selected
by the same `CompactDualPhysicalData` value. -/
theorem packetGraphSum_eq_physicalPartition (D : CompactDualPhysicalData) :
    parametricFusionCompleteBoxVertexCartesianSum
        D.coupling D.cutoff D.boxExtent ≈
      D.physicalPartition :=
  parametricFusionCompleteBoxVertexCartesianSum_eq_physicalPartition
    D.coupling D.cutoff D.boxExtent

/-! ## The exact algebraic Schur form carried by the same face packet -/

/-- The Schur-normalized rational weight `w^(4 C₂(s))` of the selected
heat-kernel packet. -/
def reflectionWeightQ (D : CompactDualPhysicalData) (s : Nat) : Q' :=
  qpow D.coupling (c4 s)

/-- The same rational reflection weight embedded in constructive reals. -/
def reflectionWeight (D : CompactDualPhysicalData) (s : Nat) : CReal :=
  CReal.ofQ' (D.reflectionWeightQ s)

/-- Boundary coefficients from the exact observable packet selected in `D`. -/
def reflectedCoefficients (D : CompactDualPhysicalData) (s : Nat) : Q' :=
  coeffAt D.observable s

/-- The finite Schur-diagonal reflection form attached to this physical datum. -/
def reflectionForm (D : CompactDualPhysicalData) : CReal :=
  ReflectionPositivity.diagReflForm
    D.reflectionWeight D.reflectedCoefficients (D.cutoff + 1)

/-- Below the physical cutoff, the exact face-packet coefficient is dimension
times the Schur-normalized reflection weight selected above. -/
theorem facePacket_coeff_eq_dim_mul_reflectionWeightQ
    (D : CompactDualPhysicalData) {s : Nat} (hs : s < D.cutoff + 1) :
    coeffAt D.facePacket s = dimQ s * D.reflectionWeightQ s := by
  unfold facePacket reflectionWeightQ
  rw [coeffAt_heatKernelPacket hs]
  rfl

/-- Every algebraic reflection weight is nonnegative at nonnegative coupling. -/
theorem reflectionWeight_nonneg (D : CompactDualPhysicalData) (s : Nat) :
    ExpPos.geRat (D.reflectionWeight s) 0 :=
  SumOfSquares.geRat_ofQ'_nonneg
    (qpow_nonneg D.coupling D.coupling_nonnegative (c4 s))

/-- The Schur form from the shared packet data is nonnegative for the exact
observable carried by `D`. -/
theorem reflectionForm_nonneg (D : CompactDualPhysicalData) :
    ExpPos.geRat D.reflectionForm 0 :=
  ReflectionPositivity.diagReflForm_nonneg
    D.reflectionWeight D.reflectionWeight_nonneg
    D.reflectedCoefficients (D.cutoff + 1)

/-! ## Pinning the same values into the generic RG interface -/

/-- A singleton carrier indexed by an already constructed value.

Unlike an unindexed `Unit` placeholder, the value is present in the type, so
two physical data sets produce incompatible carriers unless their indices are
definitionally the same. -/
inductive Pinned {α : Type} (value : α) : Type where
  | here : Pinned value

/-- Recover the value used as the singleton's type index. -/
def Pinned.get {α : Type} {value : α} : Pinned value → α
  | .here => value

@[simp] theorem Pinned.get_here {α : Type} {value : α} :
    Pinned.get (Pinned.here : Pinned value) = value :=
  rfl

/-- The physical cutoff carrier placed into the RG interface. -/
structure FiniteBoxCutoff : Type where
  physicalCutoff : Nat
  boxExtent : Nat

def finiteBoxCutoff (D : CompactDualPhysicalData) : FiniteBoxCutoff where
  physicalCutoff := D.cutoff
  boxExtent := D.boxExtent

/-- An actual `RGInterface` whose physical carriers are pinned to `D`.

Only the action/response vocabulary and the genuinely future analytic norm,
certificate, and error carriers remain parameters. -/
def rgInterface
    (D : CompactDualPhysicalData)
    (Action : Type) (Response : Action → Type)
    (NormData CertificateData ErrorData : Type) : RGInterface.{0} where
  action := Action
  response := Response
  cutoffData := Pinned D.finiteBoxCutoff
  retainedField := Pinned D.packetGraphState
  polymerActivity := Pinned D.physicalTerm
  relevantCoordinate := Pinned D.coupling
  normData := NormData
  observableData := Pinned D.observable
  certificateData := CertificateData
  errorData := ErrorData

/-- Construct an `RGState` at the pinned physical interface.

All scoped physical fields have their unique indexed inhabitant.  The caller
must still provide the norm, certificate ledger, and distortion data; this
constructor does not manufacture any analytic witness. -/
def rgState
    (D : CompactDualPhysicalData)
    (Action : Type) (Response : Action → Type)
    (NormData CertificateData ErrorData : Type)
    (norm : NormData)
    (bounds : CertificateData)
    (certificateLedger : List CertificateData)
    (dynamicDistortion interfaceDistortion : ErrorData) :
    RGState (D.rgInterface Action Response NormData CertificateData ErrorData) where
  cutoff := Pinned.here
  effectiveField := Pinned.here
  relevantPotential := Pinned.here
  irrelevantActivity := Pinned.here
  norm := norm
  bounds := bounds
  observables := Pinned.here
  certificateLedger := certificateLedger
  dynamicDistortion := dynamicDistortion
  interfaceDistortion := interfaceDistortion

/-- The RG state's relevant coordinate recovers the same rational coupling. -/
@[simp] theorem rgState_coupling
    (D : CompactDualPhysicalData)
    (Action : Type) (Response : Action → Type)
    (NormData CertificateData ErrorData : Type)
    (norm : NormData) (bounds : CertificateData)
    (ledger : List CertificateData) (dynamic interface : ErrorData) :
    Pinned.get
        (D.rgState Action Response NormData CertificateData ErrorData
          norm bounds ledger dynamic interface).relevantPotential =
      D.coupling :=
  rfl

/-- The RG state's cutoff datum recovers the same physical cutoff and box. -/
@[simp] theorem rgState_finiteBoxCutoff
    (D : CompactDualPhysicalData)
    (Action : Type) (Response : Action → Type)
    (NormData CertificateData ErrorData : Type)
    (norm : NormData) (bounds : CertificateData)
    (ledger : List CertificateData) (dynamic interface : ErrorData) :
    Pinned.get
        (D.rgState Action Response NormData CertificateData ErrorData
          norm bounds ledger dynamic interface).cutoff =
      D.finiteBoxCutoff :=
  rfl

/-- The RG state's observable recovers the exact packet carried by `D`. -/
@[simp] theorem rgState_observable
    (D : CompactDualPhysicalData)
    (Action : Type) (Response : Action → Type)
    (NormData CertificateData ErrorData : Type)
    (norm : NormData) (bounds : CertificateData)
    (ledger : List CertificateData) (dynamic interface : ErrorData) :
    Pinned.get
        (D.rgState Action Response NormData CertificateData ErrorData
          norm bounds ledger dynamic interface).observables =
      D.observable :=
  rfl

/-- The RG state's polymer activity recovers the exact physical summand,
including the existing enumerated shared-link factor. -/
@[simp] theorem rgState_physicalTerm
    (D : CompactDualPhysicalData)
    (Action : Type) (Response : Action → Type)
    (NormData CertificateData ErrorData : Type)
    (norm : NormData) (bounds : CertificateData)
    (ledger : List CertificateData) (dynamic interface : ErrorData) :
    Pinned.get
        (D.rgState Action Response NormData CertificateData ErrorData
          norm bounds ledger dynamic interface).irrelevantActivity =
      D.physicalTerm :=
  rfl

/-- The RG state's retained field recovers the exact fusion-complete graph. -/
@[simp] theorem rgState_packetGraph
    (D : CompactDualPhysicalData)
    (Action : Type) (Response : Action → Type)
    (NormData CertificateData ErrorData : Type)
    (norm : NormData) (bounds : CertificateData)
    (ledger : List CertificateData) (dynamic interface : ErrorData) :
    Pinned.get
        (D.rgState Action Response NormData CertificateData ErrorData
          norm bounds ledger dynamic interface).effectiveField =
      D.packetGraphState :=
  rfl

end CompactDualPhysicalData

#print axioms CompactDualPhysicalData.physicalTerm_eq_faceFactor_mul_enumeratedLinks
#print axioms CompactDualPhysicalData.packetGraphSum_eq_physicalPartition
#print axioms CompactDualPhysicalData.facePacket_coeff_eq_dim_mul_reflectionWeightQ
#print axioms CompactDualPhysicalData.reflectionWeight_nonneg
#print axioms CompactDualPhysicalData.reflectionForm_nonneg
#print axioms CompactDualPhysicalData.rgState_coupling
#print axioms CompactDualPhysicalData.rgState_finiteBoxCutoff
#print axioms CompactDualPhysicalData.rgState_observable
#print axioms CompactDualPhysicalData.rgState_physicalTerm
#print axioms CompactDualPhysicalData.rgState_packetGraph

end YMGap.Continuum.CompactDualPinnedPhysicalData
