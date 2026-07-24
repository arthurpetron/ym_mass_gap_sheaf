/-
Scale-dependent RG interfaces, organized as polynomial trees.

This module implements the structural correction recorded in
`docs/rg-polynomial-tree-2026-07-22.md`: an RG history changes both its
state and the interface in which the next state is legal.

The implementation is deliberately constructive and Mathlib-free.

* `Polynomial` is the position/direction container `Σ i, y^(D i)`.
* `PolyTreeApprox n` is the executable depth-`n` approximation.
* `PolyTreeHomApprox` is Spivak's finite morphism tower

    Π i, Σ j, Π e, Σ d, HomApprox(child i d, child j e).

* `PolyTree` is a coalgebraic presentation of a possibly infinite tree.  Its
  internal `State`, current state, node polynomial, and transition function
  give guarded observations at every finite depth without postulating a
  native coinductive record.
* `RGProgram` specializes the coalgebra to evolving RG interfaces.
* `RGStep` indexes the successor state by the selected child interface, so an
  ill-typed cross-scale state transition cannot be constructed.

No analytic contraction, landing, interface-stabilization, or mass-gap claim
is made here.  Those remain named obligations in `work_plan.md`.

Axiom gate (AGENTS.md Rules 1 and 8): all declarations below are definitions
or proofs by reduction/constructor disjointness.  No `Classical.*`, `sorry`,
`native_decide`, quotient, or noncomputable declaration is used.
-/

namespace YMGap.RG.PolynomialTree

universe u v

/-! ## Polynomial containers and finite tree approximants -/

/-- A polynomial interface `Σ i : Pos, y^(Dir i)`. -/
structure Polynomial where
  /-- Positions, interpreted in the RG specialization as admissible actions. -/
  Pos : Type u
  /-- Directions returned after a position is selected. -/
  Dir : Pos → Type u

/-- Executable polynomial trees of exactly the requested observation depth.

Depth zero exposes no node.  A successor depth exposes a polynomial root and
a depth-`n` child for every position/direction interaction. -/
def PolyTreeApprox : Nat → Type (u + 1)
  | 0 => PUnit.{u + 2}
  | n + 1 =>
      Σ p : Polynomial.{u},
        (i : p.Pos) → p.Dir i → PolyTreeApprox n

/-- The finite polynomial-tree morphism tower.

At depth zero there is one observation.  At successor depth a source position
chooses a target position; every target direction is answered by a source
direction and a morphism between the selected child approximants. -/
def PolyTreeHomApprox :
    (n : Nat) → PolyTreeApprox.{u} n → PolyTreeApprox.{u} n → Type (u + 1)
  | 0, _, _ => PUnit.{u + 2}
  | n + 1, p, q =>
      (i : p.1.Pos) →
        Σ j : q.1.Pos,
          (e : q.1.Dir j) →
            Σ d : p.1.Dir i,
              PolyTreeHomApprox n (p.2 i d) (q.2 j e)

/-! ## A coalgebraic presentation of possibly infinite polynomial trees -/

/-- A possibly infinite polynomial tree, presented by a transition coalgebra.

`State` is an internal node code.  Observing a state returns its current
polynomial, and a position/direction pair computes the next state.  This
supports productive finite observation at every depth and is the executable
replacement for a literal unsupported coinductive record. -/
structure PolyTree where
  /-- Internal node codes for this presentation. -/
  State : Type u
  /-- The currently selected node. -/
  current : State
  /-- Polynomial interface exposed by each node code. -/
  root : State → Polynomial.{u}
  /-- Child-node selection after a position/direction interaction. -/
  rest : (s : State) → (i : (root s).Pos) → (root s).Dir i → State

namespace PolyTree

/-- The polynomial currently exposed by a tree. -/
def currentPolynomial (t : PolyTree.{u}) : Polynomial.{u} :=
  t.root t.current

/-- Select the child tree after one position/direction interaction. -/
def child (t : PolyTree.{u})
    (i : t.currentPolynomial.Pos)
    (d : t.currentPolynomial.Dir i) : PolyTree.{u} where
  State := t.State
  current := t.rest t.current i d
  root := t.root
  rest := t.rest

/-- Observe a possibly infinite tree to a finite executable depth. -/
def approx (t : PolyTree.{u}) : (n : Nat) → PolyTreeApprox.{u} n
  | 0 => PUnit.unit
  | n + 1 =>
      ⟨t.currentPolynomial, fun i d => (t.child i d).approx n⟩

/-- Embed a fixed polynomial interface as a constant tree. -/
def constant (p : Polynomial.{u}) : PolyTree.{u} where
  State := PUnit.{u + 1}
  current := PUnit.unit
  root := fun _ => p
  rest := fun _ _ _ => PUnit.unit

/-- A constant tree exposes its fixed interface at the root. -/
@[simp] theorem constant_currentPolynomial (p : Polynomial.{u}) :
    (constant p).currentPolynomial = p := rfl

/-- Every child of a constant tree is definitionally the same presentation. -/
@[simp] theorem constant_child (p : Polynomial.{u})
    (i : p.Pos) (d : p.Dir i) :
    (constant p).child i d = constant p := rfl

end PolyTree

/-! ## RG interfaces and their polynomial-tree specialization -/

/-- The complete type-level interface visible at one RG scale.

The first two fields are the polynomial action/response interface.  The
remaining fields record the scale-dependent types whose silent identification
was the structural bug: cutoff data, retained fields, polymer activities,
relevant coordinates, norms, observables, certificates, and error budgets. -/
structure RGInterface where
  action : Type u
  response : action → Type u
  cutoffData : Type u
  retainedField : Type u
  polymerActivity : Type u
  relevantCoordinate : Type u
  normData : Type u
  observableData : Type u
  certificateData : Type u
  errorData : Type u

/-- Forget the RG-specific carriers and retain the polynomial action/response
interface at the current scale. -/
def RGInterface.toPolynomial (I : RGInterface.{u}) : Polynomial.{u} where
  Pos := I.action
  Dir := I.response

/-- A scale-indexed RG interface tree.

`Node` is a constructive code for the current interface.  Crucially, `next`
returns the node selected by the actual action and response, including failure
responses that enter a diagnostic branch. -/
structure RGProgram where
  Node : Type u
  interface : Node → RGInterface.{u}
  next : (n : Node) →
    (a : (interface n).action) →
    (interface n).response a → Node

namespace RGProgram

/-- Regard an RG program as a possibly infinite polynomial tree. -/
def toPolyTree (p : RGProgram.{u}) (start : p.Node) : PolyTree.{u} where
  State := p.Node
  current := start
  root := fun n => (p.interface n).toPolynomial
  rest := p.next

/-- The executable depth-`n` approximation of an RG history tree. -/
def approx (p : RGProgram.{u}) (start : p.Node) (n : Nat) :
    PolyTreeApprox.{u} n :=
  (p.toPolyTree start).approx n

end RGProgram

/-! ## The standard RG operation vocabulary -/

/-- The first implementation-independent vocabulary of RG actions. -/
inductive RGAction where
  | integrateFluctuation
  | extractRelevantPart
  | localizePolymer
  | rescaleFields
  | transportObservable
  | verifyBounds
  | abortWithCounterexample

/-- Verification returns either its proof-carrying certificate or explicit
diagnostic evidence.  Failure is data and therefore can select a different
child interface; it is never silently discarded. -/
inductive VerificationResult (Certificate Diagnostic : Type u) where
  | success : Certificate → VerificationResult Certificate Diagnostic
  | failure : Diagnostic → VerificationResult Certificate Diagnostic

/-- Proof-carrying contraction data, abstract over the constructive scalar and
the two witness families.  In an analytic instance, `Scalar` is `CReal`,
`DerivativeBound q` certifies `‖DR‖ ≤ q`, and `BelowOne q` certifies `q < 1`.
Both witnesses live in `Type`, so later computation cannot lose them through
proof erasure. -/
structure ContractionCertificate
    (Scalar : Type u)
    (DerivativeBound BelowOne : Scalar → Type v) where
  q : Scalar
  derivativeBound : DerivativeBound q
  belowOne : BelowOne q

/-- Response types for the implementation-independent action vocabulary. -/
structure StandardResponseTypes where
  integrated : Type u
  relevantExtracted : Type u
  polymerLocalized : Type u
  fieldsRescaled : Type u
  observableTransported : Type u
  verificationCertificate : Type u
  verificationDiagnostic : Type u
  counterexample : Type u

/-- Response family associated to the standard RG actions. -/
def StandardResponseTypes.response
    (R : StandardResponseTypes.{u}) : RGAction → Type u
  | .integrateFluctuation => R.integrated
  | .extractRelevantPart => R.relevantExtracted
  | .localizePolymer => R.polymerLocalized
  | .rescaleFields => R.fieldsRescaled
  | .transportObservable => R.observableTransported
  | .verifyBounds =>
      VerificationResult R.verificationCertificate R.verificationDiagnostic
  | .abortWithCounterexample => R.counterexample

/-- Scale-dependent carrier types accompanying the action/response
polynomial. -/
structure RGCarrierTypes where
  cutoffData : Type u
  retainedField : Type u
  polymerActivity : Type u
  relevantCoordinate : Type u
  normData : Type u
  observableData : Type u
  certificateData : Type u
  errorData : Type u

/-- Build the standard RG interface independently of any analytic
implementation. -/
def standardInterface
    (C : RGCarrierTypes.{u})
    (R : StandardResponseTypes.{u}) : RGInterface.{u} where
  action := ULift.{u} RGAction
  response := fun a => R.response a.down
  cutoffData := C.cutoffData
  retainedField := C.retainedField
  polymerActivity := C.polymerActivity
  relevantCoordinate := C.relevantCoordinate
  normData := C.normData
  observableData := C.observableData
  certificateData := C.certificateData
  errorData := C.errorData

/-! ## State/interface separation and typed transitions -/

/-- The effective state valid at one particular interface.

Changing the interface changes the type of this structure.  A value cannot be
reused at the next scale without an explicit typed transition that constructs
all of the new fields. -/
structure RGState (I : RGInterface.{u}) where
  cutoff : I.cutoffData
  effectiveField : I.retainedField
  relevantPotential : I.relevantCoordinate
  irrelevantActivity : I.polymerActivity
  norm : I.normData
  bounds : I.certificateData
  observables : I.observableData
  certificateLedger : List I.certificateData
  dynamicDistortion : I.errorData
  interfaceDistortion : I.errorData

/-- One typed RG transition.

The successor state is indexed directly by the child selected by `action` and
`response`.  `AnalyticWitness` is abstract because this module supplies the
structural type, not the hard analytic estimate. -/
structure RGStep
    (p : RGProgram.{u})
    (AnalyticWitness :
      {n : p.Node} →
      (s : RGState (p.interface n)) →
      (a : (p.interface n).action) →
      (d : (p.interface n).response a) →
      RGState (p.interface (p.next n a d)) → Type v)
    {n : p.Node}
    (s : RGState (p.interface n)) where
  action : (p.interface n).action
  response : (p.interface n).response action
  next : RGState (p.interface (p.next n action response))
  analyticWitness : AnalyticWitness s action response next

/-- A finite, fully typed RG trace.  Each successor layer carries both the
analytic witness and, through the successor index, the interface-transition
witness.  It is defined by structural recursion on the requested trace length,
which avoids a positivity restriction on the dependent child index. -/
def RGTrace
    (p : RGProgram.{u})
    (AnalyticWitness :
      {n : p.Node} →
      (s : RGState (p.interface n)) →
      (a : (p.interface n).action) →
      (d : (p.interface n).response a) →
      RGState (p.interface (p.next n a d)) → Type v) :
    (n : p.Node) → RGState (p.interface n) → Nat → Type (max (u + 1) v)
  | _, _, 0 => PUnit.{(max (u + 1) v) + 1}
  | n, s, k + 1 =>
      Σ step : RGStep p AnalyticWitness s,
        RGTrace p AnalyticWitness
          (p.next n step.action step.response) step.next k

/-! ## Checked three-transition example, including a diagnostic branch -/

/-- Nodes of a small executable RG history used as a kernel-checked type test. -/
inductive DemoNode where
  | scale0
  | scale1
  | scale2
  | stable
  | diagnostic
  deriving DecidableEq

/-- Node-indexed carrier data.  Values from distinct nodes have incompatible
types even though each constructor stores a natural-number payload. -/
inductive DemoDatum : DemoNode → Type
  | atScale0 (value : Nat) : DemoDatum .scale0
  | atScale1 (value : Nat) : DemoDatum .scale1
  | atScale2 (value : Nat) : DemoDatum .scale2
  | atStable (value : Nat) : DemoDatum .stable
  | atDiagnostic (value : Nat) : DemoDatum .diagnostic

/-- Extract the numerical payload used only by the example's certificates. -/
def DemoDatum.value : {n : DemoNode} → DemoDatum n → Nat
  | _, .atScale0 value => value
  | _, .atScale1 value => value
  | _, .atScale2 value => value
  | _, .atStable value => value
  | _, .atDiagnostic value => value

/-- Construct node-indexed demo data. -/
def demoDatum (n : DemoNode) (value : Nat) : DemoDatum n :=
  match n with
  | .scale0 => .atScale0 value
  | .scale1 => .atScale1 value
  | .scale2 => .atScale2 value
  | .stable => .atStable value
  | .diagnostic => .atDiagnostic value

@[simp] theorem demoDatum_value (n : DemoNode) (value : Nat) :
    (demoDatum n value).value = value := by
  cases n <;> rfl

/-- The legal action type changes with the current node. -/
inductive DemoAction : DemoNode → Type
  | integrate : DemoAction .scale0
  | verify : DemoAction .scale1
  | transport : DemoAction .scale2
  | continueStable : DemoAction .stable
  | inspectFailure : DemoAction .diagnostic

/-- Responses are indexed by the chosen node/action pair. -/
inductive DemoResponse : {n : DemoNode} → DemoAction n → Type
  | integrated (blockWitness : Nat) : DemoResponse .integrate
  | verified (contractionWitness : Nat) : DemoResponse .verify
  | failed (counterexample : Nat) : DemoResponse .verify
  | transported (observableWitness : Nat) : DemoResponse .transport
  | continued (closureWitness : Nat) : DemoResponse .continueStable
  | inspected (diagnosticWitness : Nat) : DemoResponse .inspectFailure

/-- The response selects the next interface.  In particular, failed
verification enters `diagnostic` instead of fabricating the intended branch. -/
def demoNext : (n : DemoNode) → (a : DemoAction n) → DemoResponse a → DemoNode
  | .scale0, .integrate, .integrated _ => .scale1
  | .scale1, .verify, .verified _ => .scale2
  | .scale1, .verify, .failed _ => .diagnostic
  | .scale2, .transport, .transported _ => .stable
  | .stable, .continueStable, .continued _ => .stable
  | .diagnostic, .inspectFailure, .inspected _ => .diagnostic

/-- The demo interface changes all node-indexed carrier types. -/
def demoInterface (n : DemoNode) : RGInterface where
  action := DemoAction n
  response := DemoResponse
  cutoffData := DemoDatum n
  retainedField := DemoDatum n
  polymerActivity := DemoDatum n
  relevantCoordinate := DemoDatum n
  normData := DemoDatum n
  observableData := DemoDatum n
  certificateData := DemoDatum n
  errorData := DemoDatum n

/-- The demo polynomial-tree program. -/
def demoProgram : RGProgram where
  Node := DemoNode
  interface := demoInterface
  next := demoNext

/-- Construct an example state at any demo node. -/
def demoState (n : DemoNode)
    (scale observable certificates dynamicError interfaceError : Nat) :
    RGState (demoInterface n) where
  cutoff := demoDatum n scale
  effectiveField := demoDatum n scale
  relevantPotential := demoDatum n scale
  irrelevantActivity := demoDatum n scale
  norm := demoDatum n scale
  bounds := demoDatum n certificates
  observables := demoDatum n observable
  certificateLedger := [demoDatum n certificates]
  dynamicDistortion := demoDatum n dynamicError
  interfaceDistortion := demoDatum n interfaceError

/-- The four checks carried by every transition in the demo trace: analytic
progress, observable transport, certificate-ledger update, and cumulative
interface-error update.  The successor's type separately certifies the
interface transition itself. -/
structure DemoStepWitness
    {n : DemoNode}
    (s : RGState (demoInterface n))
    (a : DemoAction n)
    (d : DemoResponse a)
    (s' : RGState (demoInterface (demoNext n a d))) : Type where
  analyticStep : s'.cutoff.value = s.cutoff.value + 1
  observableTransport : s'.observables.value = s.observables.value + 1
  certificateUpdate : s'.bounds.value = s.bounds.value + 1
  cumulativeInterfaceError :
    s'.interfaceDistortion.value = s.interfaceDistortion.value + 1

def demoState0 : RGState (demoInterface .scale0) :=
  demoState .scale0 0 10 0 0 0

def demoState1 : RGState (demoInterface .scale1) :=
  demoState .scale1 1 11 1 1 1

def demoState2 : RGState (demoInterface .scale2) :=
  demoState .scale2 2 12 2 2 2

def demoState3 : RGState (demoInterface .stable) :=
  demoState .stable 3 13 3 3 3

/-- Scale 0 → 1: integrate fluctuations and change interface. -/
def demoStep01 : RGStep demoProgram DemoStepWitness demoState0 where
  action := .integrate
  response := .integrated 1
  next := demoState1
  analyticWitness := ⟨rfl, rfl, rfl, rfl⟩

/-- Scale 1 → 2: a successful bound certificate selects the analytic branch. -/
def demoStep12 : RGStep demoProgram DemoStepWitness demoState1 where
  action := .verify
  response := .verified 95
  next := demoState2
  analyticWitness := ⟨rfl, rfl, rfl, rfl⟩

/-- Scale 2 → stable tail: transport the observable into the stable interface. -/
def demoStep23 : RGStep demoProgram DemoStepWitness demoState2 where
  action := .transport
  response := .transported 13
  next := demoState3
  analyticWitness := ⟨rfl, rfl, rfl, rfl⟩

/-- The requested checked three-scale trace, covering scales 0, 1, and 2. -/
def demoThreeScaleTrace :
    RGTrace demoProgram DemoStepWitness .scale0 demoState0 2 :=
  ⟨demoStep01, ⟨demoStep12, PUnit.unit⟩⟩

/-- A checked three-transition trace.  Every transition carries the analytic
witness, child-interface index, transported observable, updated certificate,
and updated cumulative interface error. -/
def demoThreeTransitionTrace :
    RGTrace demoProgram DemoStepWitness .scale0 demoState0 3 :=
  ⟨demoStep01, ⟨demoStep12, ⟨demoStep23, PUnit.unit⟩⟩⟩

/-- Finite executable approximants requested before using the full coalgebra. -/
def demoApprox1 : PolyTreeApprox 1 := demoProgram.approx .scale0 1
def demoApprox2 : PolyTreeApprox 2 := demoProgram.approx .scale0 2
def demoApprox3 : PolyTreeApprox 3 := demoProgram.approx .scale0 3

/-- Failed verification selects the diagnostic interface. -/
theorem demo_failure_selects_diagnostic :
    demoNext .scale1 .verify (.failed 7) = .diagnostic := rfl

/-- Success and failure genuinely select different child interfaces. -/
theorem demo_verification_branch_sensitive :
    demoNext .scale1 .verify (.verified 95) ≠
      demoNext .scale1 .verify (.failed 7) := by
  decide

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms Polynomial
#print axioms PolyTreeApprox
#print axioms PolyTreeHomApprox
#print axioms PolyTree.constant_child
#print axioms RGInterface
#print axioms RGProgram.approx
#print axioms RGState
#print axioms RGStep
#print axioms RGTrace
#print axioms demoThreeScaleTrace
#print axioms demoThreeTransitionTrace
#print axioms demo_failure_selects_diagnostic
#print axioms demo_verification_branch_sensitive

end YMGap.RG.PolynomialTree
