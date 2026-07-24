/-
Coherent interface transport and constructive stabilization certificates.

This module closes the STRUCTURAL portions of work-plan items RG-I4 and RG-I5:

* `InterfaceTransport I J` carries equivalences for the polynomial action /
  response interface and every scale-dependent RG carrier.
* `InterfaceTransport.stateForward` transports a complete `RGState I` into
  `RGState J`; `stateBackward_forward` proves exact round-trip coherence.
* `InterfaceSemantics` and `InterfaceTransportPreserves` make preservation of
  relevant coordinates, norms, localization, observables, and certificate
  interpretation explicit rather than inferred from type equivalence.
* `StableTailCertificate` returns `kStar`, the selected tail branch, transports
  into a common stable interface, a four-component discrepancy, and a
  computable stabilization modulus as Type-level data.
* `demoStableTail` is an exact-rational checked instance for the executable
  interface tree from `PolynomialTree.lean`.

The demo is a type-system/certificate test.  It does NOT provide the physical
Yang--Mills transports or analytic discrepancy estimates.  Those production
instances remain explicitly open in `work_plan.md`.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, quotient, or noncomputable declaration.
-/

import YMGap.RG.PolynomialTree
import YMGap.Constructive.Rationals

namespace YMGap.RG.InterfaceStability

open YMGap.Constructive
open YMGap.RG.PolynomialTree

universe u v w

/-! ## Exact interface transports -/

/-- A constructive equivalence of types.  Kept local and minimal so this
module remains independent of any classical or Mathlib equivalence layer. -/
structure TypeEquiv (A : Type u) (B : Type v) where
  toFun : A → B
  invFun : B → A
  leftInv : ∀ x, invFun (toFun x) = x
  rightInv : ∀ y, toFun (invFun y) = y

namespace TypeEquiv

instance {A : Type u} {B : Type v} : CoeFun (TypeEquiv A B) (fun _ => A → B) :=
  ⟨TypeEquiv.toFun⟩

def refl (A : Type u) : TypeEquiv A A where
  toFun := fun x => x
  invFun := fun x => x
  leftInv := fun _ => rfl
  rightInv := fun _ => rfl

def symm {A : Type u} {B : Type v} (e : TypeEquiv A B) : TypeEquiv B A where
  toFun := e.invFun
  invFun := e.toFun
  leftInv := e.rightInv
  rightInv := e.leftInv

def trans {A : Type u} {B : Type v} {C : Type w}
    (e : TypeEquiv A B) (f : TypeEquiv B C) : TypeEquiv A C where
  toFun := fun x => f (e x)
  invFun := fun z => e.invFun (f.invFun z)
  leftInv := by intro x; rw [f.leftInv, e.leftInv]
  rightInv := by intro z; rw [e.rightInv, f.rightInv]

@[simp] theorem invFun_apply {A : Type u} {B : Type v}
    (e : TypeEquiv A B) (x : A) : e.invFun (e x) = x :=
  e.leftInv x

@[simp] theorem apply_invFun {A : Type u} {B : Type v}
    (e : TypeEquiv A B) (y : B) : e (e.invFun y) = y :=
  e.rightInv y

@[simp] theorem list_map_invFun_toFun {A : Type u} {B : Type v}
    (e : TypeEquiv A B) : ∀ xs : List A,
    (xs.map e).map e.invFun = xs
  | [] => rfl
  | x :: xs => by
      simp [list_map_invFun_toFun e xs]

@[simp] theorem list_map_toFun_invFun {A : Type u} {B : Type v}
    (e : TypeEquiv A B) : ∀ ys : List B,
    (ys.map e.invFun).map e = ys
  | [] => rfl
  | y :: ys => by
      simp [list_map_toFun_invFun e ys]

end TypeEquiv

/-- A coherent equivalence between two RG interfaces.

The response equivalence is dependent on the transported action.  Every other
carrier is an ordinary constructive `Equiv`. -/
structure InterfaceTransport (I J : RGInterface.{u}) where
  actionEquiv : TypeEquiv I.action J.action
  responseEquiv : (a : I.action) →
    TypeEquiv (I.response a) (J.response (actionEquiv a))
  cutoffEquiv : TypeEquiv I.cutoffData J.cutoffData
  retainedFieldEquiv : TypeEquiv I.retainedField J.retainedField
  polymerActivityEquiv : TypeEquiv I.polymerActivity J.polymerActivity
  relevantCoordinateEquiv : TypeEquiv I.relevantCoordinate J.relevantCoordinate
  normEquiv : TypeEquiv I.normData J.normData
  observableEquiv : TypeEquiv I.observableData J.observableData
  certificateEquiv : TypeEquiv I.certificateData J.certificateData
  errorEquiv : TypeEquiv I.errorData J.errorData

namespace InterfaceTransport

/-- Identity transport on a fixed interface. -/
def refl (I : RGInterface.{u}) : InterfaceTransport I I where
  actionEquiv := TypeEquiv.refl _
  responseEquiv := fun _ => TypeEquiv.refl _
  cutoffEquiv := TypeEquiv.refl _
  retainedFieldEquiv := TypeEquiv.refl _
  polymerActivityEquiv := TypeEquiv.refl _
  relevantCoordinateEquiv := TypeEquiv.refl _
  normEquiv := TypeEquiv.refl _
  observableEquiv := TypeEquiv.refl _
  certificateEquiv := TypeEquiv.refl _
  errorEquiv := TypeEquiv.refl _

/-- Composition of coherent interface transports. -/
def trans {I J K : RGInterface.{u}}
    (f : InterfaceTransport I J)
    (g : InterfaceTransport J K) : InterfaceTransport I K where
  actionEquiv := f.actionEquiv.trans g.actionEquiv
  responseEquiv := fun a =>
    (f.responseEquiv a).trans (g.responseEquiv (f.actionEquiv a))
  cutoffEquiv := f.cutoffEquiv.trans g.cutoffEquiv
  retainedFieldEquiv := f.retainedFieldEquiv.trans g.retainedFieldEquiv
  polymerActivityEquiv := f.polymerActivityEquiv.trans g.polymerActivityEquiv
  relevantCoordinateEquiv :=
    f.relevantCoordinateEquiv.trans g.relevantCoordinateEquiv
  normEquiv := f.normEquiv.trans g.normEquiv
  observableEquiv := f.observableEquiv.trans g.observableEquiv
  certificateEquiv := f.certificateEquiv.trans g.certificateEquiv
  errorEquiv := f.errorEquiv.trans g.errorEquiv

/-- Transport a complete RG state into the target interface. -/
def stateForward {I J : RGInterface.{u}}
    (t : InterfaceTransport I J) (s : RGState I) : RGState J where
  cutoff := t.cutoffEquiv s.cutoff
  effectiveField := t.retainedFieldEquiv s.effectiveField
  relevantPotential := t.relevantCoordinateEquiv s.relevantPotential
  irrelevantActivity := t.polymerActivityEquiv s.irrelevantActivity
  norm := t.normEquiv s.norm
  bounds := t.certificateEquiv s.bounds
  observables := t.observableEquiv s.observables
  certificateLedger := s.certificateLedger.map t.certificateEquiv
  dynamicDistortion := t.errorEquiv s.dynamicDistortion
  interfaceDistortion := t.errorEquiv s.interfaceDistortion

/-- Pull a target-interface state back through the carrier equivalences. -/
def stateBackward {I J : RGInterface.{u}}
    (t : InterfaceTransport I J) (s : RGState J) : RGState I where
  cutoff := t.cutoffEquiv.invFun s.cutoff
  effectiveField := t.retainedFieldEquiv.invFun s.effectiveField
  relevantPotential := t.relevantCoordinateEquiv.invFun s.relevantPotential
  irrelevantActivity := t.polymerActivityEquiv.invFun s.irrelevantActivity
  norm := t.normEquiv.invFun s.norm
  bounds := t.certificateEquiv.invFun s.bounds
  observables := t.observableEquiv.invFun s.observables
  certificateLedger := s.certificateLedger.map t.certificateEquiv.invFun
  dynamicDistortion := t.errorEquiv.invFun s.dynamicDistortion
  interfaceDistortion := t.errorEquiv.invFun s.interfaceDistortion

/-- Forward state transport followed by backward transport is exact. -/
theorem stateBackward_forward {I J : RGInterface.{u}}
    (t : InterfaceTransport I J) (s : RGState I) :
    t.stateBackward (t.stateForward s) = s := by
  cases s
  simp only [stateBackward, stateForward, TypeEquiv.invFun_apply]
  congr 1
  exact TypeEquiv.list_map_invFun_toFun _ _

/-- Backward state transport followed by forward transport is exact. -/
theorem stateForward_backward {I J : RGInterface.{u}}
    (t : InterfaceTransport I J) (s : RGState J) :
    t.stateForward (t.stateBackward s) = s := by
  cases s
  simp only [stateBackward, stateForward, TypeEquiv.apply_invFun]
  congr 1
  exact TypeEquiv.list_map_toFun_invFun _ _

end InterfaceTransport

/-! ## Semantic preservation witnesses -/

/-- Interpret the five interface components whose meaning must survive scale
transport.  The common meaning types let source and target interpretations be
compared without identifying their carrier types. -/
structure InterfaceSemantics
    (I : RGInterface.{u})
    (CoordinateMeaning NormMeaning PolymerMeaning
      ObservableMeaning CertificateMeaning : Type v) where
  coordinate : I.relevantCoordinate → CoordinateMeaning
  norm : I.normData → NormMeaning
  localization : I.polymerActivity → PolymerMeaning
  observable : I.observableData → ObservableMeaning
  certificate : I.certificateData → CertificateMeaning

/-- A transport preserves the declared interpretation of relevant
coordinates, norms, localization, observables, and certificates. -/
structure InterfaceTransportPreserves
    {I J : RGInterface.{u}}
    {CoordinateMeaning NormMeaning PolymerMeaning
      ObservableMeaning CertificateMeaning : Type v}
    (t : InterfaceTransport I J)
    (source : InterfaceSemantics I CoordinateMeaning NormMeaning
      PolymerMeaning ObservableMeaning CertificateMeaning)
    (target : InterfaceSemantics J CoordinateMeaning NormMeaning
      PolymerMeaning ObservableMeaning CertificateMeaning) : Type (max u v) where
  coordinate : ∀ x, target.coordinate (t.relevantCoordinateEquiv x) = source.coordinate x
  norm : ∀ x, target.norm (t.normEquiv x) = source.norm x
  localization : ∀ x,
    target.localization (t.polymerActivityEquiv x) = source.localization x
  observable : ∀ x, target.observable (t.observableEquiv x) = source.observable x
  certificate : ∀ x,
    target.certificate (t.certificateEquiv x) = source.certificate x

namespace InterfaceTransportPreserves

/-- Identity transport preserves any fixed interpretation. -/
def refl
    {I : RGInterface.{u}}
    {CoordinateMeaning NormMeaning PolymerMeaning
      ObservableMeaning CertificateMeaning : Type v}
    (semantics : InterfaceSemantics I CoordinateMeaning NormMeaning
      PolymerMeaning ObservableMeaning CertificateMeaning) :
    InterfaceTransportPreserves (InterfaceTransport.refl I) semantics semantics where
  coordinate := fun _ => rfl
  norm := fun _ => rfl
  localization := fun _ => rfl
  observable := fun _ => rfl
  certificate := fun _ => rfl

end InterfaceTransportPreserves

/-! ## Four-component discrepancy and stable tails -/

/-- The interface discrepancy components.  Exact `Q'` values are constructive
upper bounds suitable for later embedding into `CReal`. -/
structure InterfaceDiscrepancy where
  coordinate : Q'
  norm : Q'
  observable : Q'
  certificate : Q'

/-- The maximum discrepancy: every component must fit the common budget. -/
def InterfaceDiscrepancy.maximum (d : InterfaceDiscrepancy) : Q' :=
  max (max d.coordinate d.norm) (max d.observable d.certificate)

/-- Componentwise nonnegativity of a discrepancy certificate. -/
structure InterfaceDiscrepancy.Nonnegative (d : InterfaceDiscrepancy) : Prop where
  coordinate : (0 : Q') ≤ d.coordinate
  norm : (0 : Q') ≤ d.norm
  observable : (0 : Q') ≤ d.observable
  certificate : (0 : Q') ≤ d.certificate

/-- A constructive certificate that a selected RG branch stabilizes to a
common effective interface.

Offset `n` represents physical scale `kStar + n`.  `modulus ε` is returned as
data, and `eventuallyWithin` proves every later interface is within resolution
`ε`. -/
structure StableTailCertificate (p : RGProgram.{u}) where
  kStar : Nat
  stableInterface : RGInterface.{u}
  nodeAt : Nat → p.Node
  actionAt : (n : Nat) → (p.interface (nodeAt n)).action
  responseAt : (n : Nat) →
    (p.interface (nodeAt n)).response (actionAt n)
  followsBranch : ∀ n,
    p.next (nodeAt n) (actionAt n) (responseAt n) = nodeAt (n + 1)
  transport : (n : Nat) →
    InterfaceTransport (p.interface (nodeAt n)) stableInterface
  CoordinateMeaning : Type v
  NormMeaning : Type v
  PolymerMeaning : Type v
  ObservableMeaning : Type v
  CertificateMeaning : Type v
  sourceSemantics : (n : Nat) →
    InterfaceSemantics (p.interface (nodeAt n)) CoordinateMeaning NormMeaning
      PolymerMeaning ObservableMeaning CertificateMeaning
  stableSemantics :
    InterfaceSemantics stableInterface CoordinateMeaning NormMeaning
      PolymerMeaning ObservableMeaning CertificateMeaning
  transportPreserves : (n : Nat) →
    InterfaceTransportPreserves (transport n) (sourceSemantics n) stableSemantics
  discrepancy : Nat → InterfaceDiscrepancy
  discrepancyNonnegative : ∀ n, (discrepancy n).Nonnegative
  tolerance : Nat → Q'
  withinTolerance : ∀ n, (discrepancy n).maximum ≤ tolerance n
  modulus : Q' → Nat
  eventuallyWithin : ∀ ε : Q', (0 : Q') < ε →
    ∀ n, modulus ε ≤ n → tolerance n ≤ ε

namespace StableTailCertificate

/-- Extract the stabilization scale as Type-level data at any positive
resolution.  No proposition-level existential hides the witness. -/
def scaleFor
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p)
    (ε : Q') (hε : (0 : Q') < ε) :
    Σ' N : Nat, ∀ n, N ≤ n → (c.discrepancy n).maximum ≤ ε :=
  ⟨c.modulus ε, fun n hn =>
    Q'.le_trans' _ _ _ (c.withinTolerance n) (c.eventuallyWithin ε hε n hn)⟩

end StableTailCertificate

/-! ## Checked exact-rational demo instance -/

/-- Any two demo carrier types are equivalent by preserving their numerical
payload. -/
def demoDatumEquiv (m n : DemoNode) : TypeEquiv (DemoDatum m) (DemoDatum n) where
  toFun := fun x => demoDatum n x.value
  invFun := fun x => demoDatum m x.value
  leftInv := by
    intro x
    rw [demoDatum_value]
    cases x <;> rfl
  rightInv := by
    intro x
    rw [demoDatum_value]
    cases x <;> rfl

/-- The scale-2 action is identified with the stable-tail action. -/
def demoScale2StableActionEquiv :
    TypeEquiv (DemoAction .scale2) (DemoAction .stable) where
  toFun := fun | .transport => .continueStable
  invFun := fun | .continueStable => .transport
  leftInv := fun | .transport => rfl
  rightInv := fun | .continueStable => rfl

/-- Response evidence is transported without discarding its payload. -/
def demoScale2StableResponseEquiv
    (a : DemoAction .scale2) :
    TypeEquiv (DemoResponse a)
      (DemoResponse (demoScale2StableActionEquiv a)) := by
  cases a with
  | transport =>
      exact
        { toFun := fun | .transported witness => .continued witness
          invFun := fun | .continued witness => .transported witness
          leftInv := fun | .transported _ => rfl
          rightInv := fun | .continued _ => rfl }

/-- Exact interface transport from scale 2 into the stable demo interface. -/
def demoScale2ToStableTransport :
    InterfaceTransport (demoInterface .scale2) (demoInterface .stable) where
  actionEquiv := demoScale2StableActionEquiv
  responseEquiv := demoScale2StableResponseEquiv
  cutoffEquiv := demoDatumEquiv .scale2 .stable
  retainedFieldEquiv := demoDatumEquiv .scale2 .stable
  polymerActivityEquiv := demoDatumEquiv .scale2 .stable
  relevantCoordinateEquiv := demoDatumEquiv .scale2 .stable
  normEquiv := demoDatumEquiv .scale2 .stable
  observableEquiv := demoDatumEquiv .scale2 .stable
  certificateEquiv := demoDatumEquiv .scale2 .stable
  errorEquiv := demoDatumEquiv .scale2 .stable

/-- Every demo carrier is interpreted by its stored natural-number payload. -/
def demoSemantics (n : DemoNode) :
    InterfaceSemantics (demoInterface n) Nat Nat Nat Nat Nat where
  coordinate := DemoDatum.value
  norm := DemoDatum.value
  localization := DemoDatum.value
  observable := DemoDatum.value
  certificate := DemoDatum.value

/-- The scale-2 transport preserves every declared interpretation. -/
def demoScale2TransportPreserves :
    InterfaceTransportPreserves demoScale2ToStableTransport
      (demoSemantics .scale2) (demoSemantics .stable) where
  coordinate := by intro x; cases x <;> rfl
  norm := by intro x; cases x <;> rfl
  localization := by intro x; cases x <;> rfl
  observable := by intro x; cases x <;> rfl
  certificate := by intro x; cases x <;> rfl

/-- The certified tail starts at physical scale 2 and then stays at the stable
node. -/
def demoTailNode : Nat → DemoNode
  | 0 => .scale2
  | _ + 1 => .stable

def demoTailAction : (n : Nat) → DemoAction (demoTailNode n)
  | 0 => .transport
  | _ + 1 => .continueStable

def demoTailResponse : (n : Nat) → DemoResponse (demoTailAction n)
  | 0 => .transported 13
  | _ + 1 => .continued 13

theorem demoTail_followsBranch : ∀ n,
    demoNext (demoTailNode n) (demoTailAction n) (demoTailResponse n) =
      demoTailNode (n + 1)
  | 0 => rfl
  | _ + 1 => rfl

def demoTailTransport : (n : Nat) →
    InterfaceTransport (demoInterface (demoTailNode n)) (demoInterface .stable)
  | 0 => demoScale2ToStableTransport
  | _ + 1 => InterfaceTransport.refl _

def demoTailTransportPreserves : (n : Nat) →
    InterfaceTransportPreserves (demoTailTransport n)
      (demoSemantics (demoTailNode n)) (demoSemantics .stable)
  | 0 => demoScale2TransportPreserves
  | _ + 1 => InterfaceTransportPreserves.refl _

/-- At entry the demo tail has discrepancy `1/4`; after one certified
transport it is exactly the stable interface. -/
def demoTailDiscrepancy : Nat → InterfaceDiscrepancy
  | 0 =>
      { coordinate := Q'.mkPos 1 4 (by decide)
        norm := Q'.mkPos 1 4 (by decide)
        observable := Q'.mkPos 1 4 (by decide)
        certificate := Q'.mkPos 1 4 (by decide) }
  | _ + 1 =>
      { coordinate := 0
        norm := 0
        observable := 0
        certificate := 0 }

def demoTailTolerance : Nat → Q'
  | 0 => Q'.mkPos 1 4 (by decide)
  | _ + 1 => 0

theorem demoTailDiscrepancy_nonnegative : ∀ n,
    (demoTailDiscrepancy n).Nonnegative
  | 0 => ⟨by decide, by decide, by decide, by decide⟩
  | n + 1 => by
      exact ⟨Q'.le_refl' 0, Q'.le_refl' 0, Q'.le_refl' 0, Q'.le_refl' 0⟩

theorem demoTailDiscrepancy_within : ∀ n,
    (demoTailDiscrepancy n).maximum ≤ demoTailTolerance n
  | 0 => by decide
  | n + 1 => Q'.le_refl' 0

/-- A positive rational is nonnegative, constructively. -/
private theorem q_nonnegative_of_positive {q : Q'}
    (h : (0 : Q') < q) : (0 : Q') ≤ q := by
  show (0 : Int) * (q.den : Int) ≤ q.num * (((0 : Q').den) : Int)
  exact Int.le_of_lt h

/-- The constant modulus `1` is valid because the demo discrepancy becomes
zero after the first tail transport. -/
theorem demoTail_eventuallyWithin (ε : Q') (hε : (0 : Q') < ε) :
    ∀ n, 1 ≤ n → demoTailTolerance n ≤ ε := by
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
      show (0 : Q') ≤ ε
      exact q_nonnegative_of_positive hε

/-- Checked constructive stabilization certificate for the demo RG branch. -/
def demoStableTail : StableTailCertificate demoProgram where
  kStar := 2
  stableInterface := demoInterface .stable
  nodeAt := demoTailNode
  actionAt := demoTailAction
  responseAt := demoTailResponse
  followsBranch := demoTail_followsBranch
  transport := demoTailTransport
  CoordinateMeaning := Nat
  NormMeaning := Nat
  PolymerMeaning := Nat
  ObservableMeaning := Nat
  CertificateMeaning := Nat
  sourceSemantics := fun n => demoSemantics (demoTailNode n)
  stableSemantics := demoSemantics .stable
  transportPreserves := demoTailTransportPreserves
  discrepancy := demoTailDiscrepancy
  discrepancyNonnegative := demoTailDiscrepancy_nonnegative
  tolerance := demoTailTolerance
  withinTolerance := demoTailDiscrepancy_within
  modulus := fun _ => 1
  eventuallyWithin := demoTail_eventuallyWithin

/-- The stabilization scale is constructively extractable at every positive
rational resolution. -/
def demoScaleFor (ε : Q') (hε : (0 : Q') < ε) :
    Σ' N : Nat, ∀ n, N ≤ n → (demoStableTail.discrepancy n).maximum ≤ ε :=
  demoStableTail.scaleFor ε hε

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms InterfaceTransport
#print axioms InterfaceTransport.trans
#print axioms InterfaceTransport.stateForward
#print axioms InterfaceTransport.stateBackward_forward
#print axioms InterfaceTransport.stateForward_backward
#print axioms InterfaceTransportPreserves
#print axioms InterfaceDiscrepancy.maximum
#print axioms StableTailCertificate
#print axioms StableTailCertificate.scaleFor
#print axioms demoScale2ToStableTransport
#print axioms demoScale2TransportPreserves
#print axioms demoTail_followsBranch
#print axioms demoStableTail
#print axioms demoScaleFor

end YMGap.RG.InterfaceStability
