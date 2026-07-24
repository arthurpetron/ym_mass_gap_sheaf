/-
Production-facing bridge from the legacy Q'-valued induction package to the
scale-dependent polynomial-tree interface.

This module connects three layers that previously coexisted without a checked
adapter:

* `InductiveState Q' P PolyAtlas`, which carries the actual scale index,
  renormalized string tension, running coupling, three KP certificates, and
  polymer atlas used by the block-spin budget;
* `StepTypeWithBudget`, which carries the genuine S1--S4 per-step inequalities;
* `PolynomialTree.RGState`, which adds typed retained fields, observables,
  certificate ledgers, and separate dynamic/interface distortions.

The bridge is deliberately conservative.  Retained-field and observable data
are explicit inputs because the legacy state does not contain them.  Adjacent
carrier transport requires explicit constructive equivalences; no physical
block-spin equivalence or Yang--Mills estimate is asserted.  In particular,
this module does not claim that coarse and fine field spaces are equivalent.

Axiom gate (AGENTS.md Rules 1 and 8): definitions, structure projections, and
constructor proofs only.  No classical reasoning, sorry, native_decide,
quotient, or noncomputable declaration.
-/

import YMGap.RG.BlockSpin
import YMGap.RG.InterfaceStability

namespace YMGap.RG.InductiveInterfaceBridge

open YMGap.Constructive
open YMGap.Sheaf
open YMGap.RG
open YMGap.RG.InductiveState
open YMGap.RG.PolynomialTree
open YMGap.RG.InterfaceStability

/-! ## Concrete Q'-valued carriers already present in `InductiveState` -/

/-- The two relevant scalar coordinates already carried by the legacy
induction package.  They are kept together so neither is misidentified as a
norm or an error term. -/
structure RelevantCoordinates where
  sigmaHat : Q'
  coupling : Q'

/-- The six KP norm parameters already carried by the three regime
certificates.  This is a lossless numerical summary, not a new analytic norm
estimate. -/
structure KPNormSummary where
  rhoSf : Q'
  KSf : Q'
  rhoLf : Q'
  KLf : Q'
  rhoCap : Q'
  KCap : Q'

/-- The small-field, large-field, and overlap certificates as one ledger
entry.  Each constituent retains its original proof of `P rho K`. -/
structure KPCertificateBundle (P : Q' → Q' → Prop) where
  sf : KPCertificate Q' P
  lf : KPCertificate Q' P
  cap : KPCertificate Q' P

namespace KPCertificateBundle

/-- Extract the exact six-number norm summary of a certificate bundle. -/
def normSummary {P : Q' → Q' → Prop}
    (c : KPCertificateBundle P) : KPNormSummary where
  rhoSf := c.sf.rho
  KSf := c.sf.K
  rhoLf := c.lf.rho
  KLf := c.lf.K
  rhoCap := c.cap.rho
  KCap := c.cap.K

end KPCertificateBundle

/-! ## A production-facing specialization of `RGInterface` -/

/-- Carrier types not present in the legacy `InductiveState`.

The polymer atlas is included here because it can genuinely change type across
interfaces.  Retained fields and observables remain abstract carrier types;
constructing their physical Yang--Mills values is an analytic task, not a
type-level default. -/
structure ProductionCarriers where
  retainedField : Type
  polymerAtlas : Type
  observableData : Type
  verificationDiagnostic : Type
  counterexample : Type

/-- Standard response carriers specialized to the actual Q' coordinate, KP,
and error data used by the induction package. -/
def productionResponses
    (P : Q' → Q' → Prop) (C : ProductionCarriers) :
    StandardResponseTypes where
  integrated := C.retainedField
  relevantExtracted := RelevantCoordinates
  polymerLocalized := C.polymerAtlas
  fieldsRescaled := C.retainedField
  observableTransported := C.observableData
  verificationCertificate := KPCertificateBundle P
  verificationDiagnostic := C.verificationDiagnostic
  counterexample := C.counterexample

/-- Standard RG carrier slots specialized to the legacy induction's genuine
Q' data and to explicit missing field/observable carriers. -/
def productionCarrierTypes
    (P : Q' → Q' → Prop) (C : ProductionCarriers) :
    RGCarrierTypes where
  cutoffData := Nat
  retainedField := C.retainedField
  polymerActivity := C.polymerAtlas
  relevantCoordinate := RelevantCoordinates
  normData := KPNormSummary
  observableData := C.observableData
  certificateData := KPCertificateBundle P
  errorData := Q'

/-- The production-facing polynomial-tree interface induced by the existing
Q' block-spin state.  Its cutoff datum is exactly the legacy scale index; no
unavailable lattice-spacing or volume datum is invented. -/
def productionInterface
    (P : Q' → Q' → Prop) (C : ProductionCarriers) : RGInterface :=
  standardInterface (productionCarrierTypes P C) (productionResponses P C)

/-! ## Lossless embedding of the legacy induction state -/

/-- Bundle the three certificates of a legacy induction state. -/
def certificatesOf
    {P : Q' → Q' → Prop} {A : Type}
    (s : InductiveState Q' P A) : KPCertificateBundle P :=
  ⟨s.c_sf, s.c_lf, s.c_cap⟩

/-- Embed a legacy Q' induction state into the new typed RG state.

Every datum already present in `InductiveState` is copied exactly.  The four
new data absent from it -- retained field, observable, dynamic distortion, and
interface distortion -- must be supplied explicitly. -/
def ofInductiveState
    {P : Q' → Q' → Prop} {C : ProductionCarriers}
    (s : InductiveState Q' P C.polymerAtlas)
    (field : C.retainedField) (observable : C.observableData)
    (dynamicError interfaceError : Q') :
    RGState (productionInterface P C) where
  cutoff := s.k
  effectiveField := field
  relevantPotential := ⟨s.sigmaHat, s.g⟩
  irrelevantActivity := s.poly_atlas
  norm := (certificatesOf s).normSummary
  bounds := certificatesOf s
  observables := observable
  certificateLedger := [certificatesOf s]
  dynamicDistortion := dynamicError
  interfaceDistortion := interfaceError

/-- Project the exact legacy induction package out of a production RG state.
The extra retained-field, observable, and split-error components are outside
the legacy type and are therefore intentionally not part of this projection. -/
def toInductiveState
    {P : Q' → Q' → Prop} {C : ProductionCarriers}
    (s : RGState (productionInterface P C)) :
    InductiveState Q' P C.polymerAtlas where
  k := s.cutoff
  sigmaHat := s.relevantPotential.sigmaHat
  g := s.relevantPotential.coupling
  c_sf := s.bounds.sf
  c_lf := s.bounds.lf
  c_cap := s.bounds.cap
  poly_atlas := s.irrelevantActivity

/-- The bridge is a retraction: every datum in the legacy induction state is
recovered exactly after embedding. -/
@[simp] theorem toInductiveState_ofInductiveState
    {P : Q' → Q' → Prop} {C : ProductionCarriers}
    (s : InductiveState Q' P C.polymerAtlas)
    (field : C.retainedField) (observable : C.observableData)
    (dynamicError interfaceError : Q') :
    toInductiveState
      (ofInductiveState s field observable dynamicError interfaceError) = s := by
  cases s
  rfl

/-- Validity of a legacy state is preserved by embedding and exact
re-projection; no new analytic claim is needed. -/
def valid_after_bridge
    {P : Q' → Q' → Prop} {C : ProductionCarriers}
    {s : InductiveState Q' P C.polymerAtlas}
    (h : Valid s)
    (field : C.retainedField) (observable : C.observableData)
    (dynamicError interfaceError : Q') :
    Valid (toInductiveState
      (ofInductiveState s field observable dynamicError interfaceError)) := by
  simpa using h

/-! ## Lifting a genuine S1--S4 budgeted step -/

/-- A `StepTypeWithBudget` output together with the state components absent
from the legacy induction package.

All content-bearing outputs are fields in `Type`: the next induction state,
retained field, observable, and both distortion ledgers.  The six propositions
are exactly the legacy `Valid` and S1--S4 obligations. -/
structure BudgetedTransition
    (P : Q' → Q' → Prop) (C : ProductionCarriers)
    (b : Q')
    (epsSf epsLf deltaCap eta : Q' → Q' → Q')
    (source : InductiveState Q' P C.polymerAtlas) where
  next : InductiveState Q' P C.polymerAtlas
  nextValid : Valid next
  scaleAdvance : next.k = source.k + 1
  sfBudget : source.c_sf.rho - epsSf b source.g ≤ next.c_sf.rho
  lfBudget : source.c_lf.rho - epsLf b source.g ≤ next.c_lf.rho
  capBudget : next.c_cap.K ≤ source.c_cap.K + deltaCap b source.g
  sigmaBudget : source.sigmaHat - eta b source.g ≤ next.sigmaHat
  nextField : C.retainedField
  nextObservable : C.observableData
  dynamicDistortion : Q'
  interfaceDistortion : Q'

namespace BudgetedTransition

/-- Apply an existing genuine `StepTypeWithBudget` term and add the four
explicit components that its legacy codomain does not carry. -/
def fromStep
    {P : Q' → Q' → Prop} {C : ProductionCarriers}
    {b : Q'} {epsSf epsLf deltaCap eta : Q' → Q' → Q'}
    (step : StepTypeWithBudget Q' P C.polymerAtlas b
      epsSf epsLf deltaCap eta)
    (source : InductiveState Q' P C.polymerAtlas) (hsource : Valid source)
    (field : C.retainedField) (observable : C.observableData)
    (dynamicError interfaceError : Q') :
    BudgetedTransition P C b epsSf epsLf deltaCap eta source := by
  let out := step source hsource
  exact
    { next := out.1
      nextValid := out.2.1
      scaleAdvance := out.2.2.1
      sfBudget := out.2.2.2.1
      lfBudget := out.2.2.2.2.1
      capBudget := out.2.2.2.2.2.1
      sigmaBudget := out.2.2.2.2.2.2
      nextField := field
      nextObservable := observable
      dynamicDistortion := dynamicError
      interfaceDistortion := interfaceError }

/-- The complete next polynomial-tree state of a budgeted transition. -/
def nextRGState
    {P : Q' → Q' → Prop} {C : ProductionCarriers}
    {b : Q'} {epsSf epsLf deltaCap eta : Q' → Q' → Q'}
    {source : InductiveState Q' P C.polymerAtlas}
    (t : BudgetedTransition P C b epsSf epsLf deltaCap eta source) :
    RGState (productionInterface P C) :=
  ofInductiveState t.next t.nextField t.nextObservable
    t.dynamicDistortion t.interfaceDistortion

/-- Projecting a lifted next RG state recovers the exact S1--S4 successor. -/
@[simp] theorem toInductiveState_nextRGState
    {P : Q' → Q' → Prop} {C : ProductionCarriers}
    {b : Q'} {epsSf epsLf deltaCap eta : Q' → Q' → Q'}
    {source : InductiveState Q' P C.polymerAtlas}
    (t : BudgetedTransition P C b epsSf epsLf deltaCap eta source) :
    toInductiveState t.nextRGState = t.next :=
  toInductiveState_ofInductiveState _ _ _ _ _

end BudgetedTransition

/-! ## Exact carrier equivalences and interface transport -/

/-- Explicit constructive equivalences for the carrier types absent from the
legacy Q' state.  Requiring these as arguments prevents a non-invertible
physical block-spin map from being silently presented as an equivalence. -/
structure ProductionCarrierEquiv
    (C D : ProductionCarriers) where
  retainedField : TypeEquiv C.retainedField D.retainedField
  polymerAtlas : TypeEquiv C.polymerAtlas D.polymerAtlas
  observableData : TypeEquiv C.observableData D.observableData
  verificationDiagnostic :
    TypeEquiv C.verificationDiagnostic D.verificationDiagnostic
  counterexample : TypeEquiv C.counterexample D.counterexample

/-- Map only the atlas carrier of a legacy induction state.  All Q' and KP
data remain exactly unchanged. -/
def mapAtlas
    {P : Q' → Q' → Prop} {A B : Type}
    (e : TypeEquiv A B) (s : InductiveState Q' P A) :
    InductiveState Q' P B where
  k := s.k
  sigmaHat := s.sigmaHat
  g := s.g
  c_sf := s.c_sf
  c_lf := s.c_lf
  c_cap := s.c_cap
  poly_atlas := e s.poly_atlas

/-- Atlas equivalence preserves every clause of legacy validity because those
clauses depend only on the unchanged Q' and KP data. -/
def mapAtlas_valid
    {P : Q' → Q' → Prop} {A B : Type}
    (e : TypeEquiv A B) {s : InductiveState Q' P A}
    (h : Valid s) : Valid (mapAtlas e s) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- Constructive equivalence of verification responses. -/
def verificationResultEquiv
    {CertificateA CertificateB DiagnosticA DiagnosticB : Type}
    (certificate : TypeEquiv CertificateA CertificateB)
    (diagnostic : TypeEquiv DiagnosticA DiagnosticB) :
    TypeEquiv
      (VerificationResult CertificateA DiagnosticA)
      (VerificationResult CertificateB DiagnosticB) where
  toFun
    | .success c => .success (certificate c)
    | .failure d => .failure (diagnostic d)
  invFun
    | .success c => .success (certificate.invFun c)
    | .failure d => .failure (diagnostic.invFun d)
  leftInv
    | .success c => by
        change VerificationResult.success
          (certificate.invFun (certificate.toFun c)) = .success c
        rw [certificate.leftInv]
    | .failure d => by
        change VerificationResult.failure
          (diagnostic.invFun (diagnostic.toFun d)) = .failure d
        rw [diagnostic.leftInv]
  rightInv
    | .success c => by
        change VerificationResult.success
          (certificate.toFun (certificate.invFun c)) = .success c
        rw [certificate.rightInv]
    | .failure d => by
        change VerificationResult.failure
          (diagnostic.toFun (diagnostic.invFun d)) = .failure d
        rw [diagnostic.rightInv]

namespace ProductionCarrierEquiv

/-- Dependent response transport for every standard RG action. -/
def responseEquiv
    {P : Q' → Q' → Prop} {C D : ProductionCarriers}
    (e : ProductionCarrierEquiv C D)
    (a : ULift RGAction) :
    TypeEquiv
      ((productionInterface P C).response a)
      ((productionInterface P D).response a) := by
  cases a with
  | up action =>
      cases action with
      | integrateFluctuation => exact e.retainedField
      | extractRelevantPart => exact TypeEquiv.refl _
      | localizePolymer => exact e.polymerAtlas
      | rescaleFields => exact e.retainedField
      | transportObservable => exact e.observableData
      | verifyBounds =>
          exact verificationResultEquiv (TypeEquiv.refl _)
            e.verificationDiagnostic
      | abortWithCounterexample => exact e.counterexample

/-- Lift explicit carrier equivalences to the full coherent interface
transport.  The Q' coordinate, KP norm/certificate, cutoff-index, and split
error carriers transport by identity. -/
def toInterfaceTransport
    {P : Q' → Q' → Prop} {C D : ProductionCarriers}
    (e : ProductionCarrierEquiv C D) :
    InterfaceTransport (productionInterface P C) (productionInterface P D) where
  actionEquiv := TypeEquiv.refl _
  responseEquiv := e.responseEquiv
  cutoffEquiv := TypeEquiv.refl _
  retainedFieldEquiv := e.retainedField
  polymerActivityEquiv := e.polymerAtlas
  relevantCoordinateEquiv := TypeEquiv.refl _
  normEquiv := TypeEquiv.refl _
  observableEquiv := e.observableData
  certificateEquiv := TypeEquiv.refl _
  errorEquiv := TypeEquiv.refl _

/-- Interpret source carriers in the target carrier vocabulary. -/
def sourceSemantics
    {P : Q' → Q' → Prop} {C D : ProductionCarriers}
    (e : ProductionCarrierEquiv C D) :
    InterfaceSemantics (productionInterface P C)
      RelevantCoordinates KPNormSummary D.polymerAtlas D.observableData
      (KPCertificateBundle P) where
  coordinate := fun x => x
  norm := fun x => x
  localization := e.polymerAtlas
  observable := e.observableData
  certificate := fun x => x

/-- Target carriers interpreted in their own vocabulary. -/
def targetSemantics
    {P : Q' → Q' → Prop} (D : ProductionCarriers) :
    InterfaceSemantics (productionInterface P D)
      RelevantCoordinates KPNormSummary D.polymerAtlas D.observableData
      (KPCertificateBundle P) where
  coordinate := fun x => x
  norm := fun x => x
  localization := fun x => x
  observable := fun x => x
  certificate := fun x => x

/-- The lifted carrier transport preserves the exact coordinate, norm,
polymer, observable, and certificate interpretations. -/
def transportPreserves
    {P : Q' → Q' → Prop} {C D : ProductionCarriers}
    (e : ProductionCarrierEquiv C D) :
    InterfaceTransportPreserves (e.toInterfaceTransport (P := P))
      (e.sourceSemantics (P := P)) (targetSemantics (P := P) D) where
  coordinate := fun _ => rfl
  norm := fun _ => rfl
  localization := fun _ => rfl
  observable := fun _ => rfl
  certificate := fun _ => rfl

/-- State-level naturality of the bridge.  Transporting the embedded RG state
is exactly the same as mapping the legacy atlas and the explicit field and
observable carriers first.  Both error ledgers remain separate and unchanged. -/
theorem stateForward_ofInductiveState
    {P : Q' → Q' → Prop} {C D : ProductionCarriers}
    (e : ProductionCarrierEquiv C D)
    (s : InductiveState Q' P C.polymerAtlas)
    (field : C.retainedField) (observable : C.observableData)
    (dynamicError interfaceError : Q') :
    (e.toInterfaceTransport (P := P)).stateForward
        (ofInductiveState s field observable dynamicError interfaceError) =
      ofInductiveState (mapAtlas e.polymerAtlas s)
        (e.retainedField field) (e.observableData observable)
        dynamicError interfaceError := by
  cases s
  rfl

end ProductionCarrierEquiv

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms RelevantCoordinates
#print axioms KPCertificateBundle.normSummary
#print axioms productionInterface
#print axioms ofInductiveState
#print axioms toInductiveState_ofInductiveState
#print axioms valid_after_bridge
#print axioms BudgetedTransition
#print axioms BudgetedTransition.fromStep
#print axioms BudgetedTransition.toInductiveState_nextRGState
#print axioms mapAtlas_valid
#print axioms verificationResultEquiv
#print axioms ProductionCarrierEquiv.toInterfaceTransport
#print axioms ProductionCarrierEquiv.transportPreserves
#print axioms ProductionCarrierEquiv.stateForward_ofInductiveState

end YMGap.RG.InductiveInterfaceBridge
