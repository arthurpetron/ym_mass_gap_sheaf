/-
Directed constructive transport for non-invertible RG coarse graining.

`InterfaceStability.InterfaceTransport` is intentionally an equivalence: it is
the right object for exact coordinate changes and proves round trips.  A genuine
block-spin step, however, integrates out degrees of freedom and is generally
not invertible.  Requiring an equivalence there would turn a useful structural
interface into a false physical assertion.

This module supplies the weaker forward notion:

* `DirectedInterfaceTransport I J` maps actions, dependent responses, and every
  carrier of `RGState I` into the corresponding carrier of `RGState J`;
* `stateForward` transports a complete state while keeping dynamic and
  interface distortions as separate fields;
* `DirectedTransportPreserves` and `DirectedErrorPreserves` carry explicit
  semantic and two-ledger error witnesses;
* every exact `InterfaceTransport` has a canonical directed image;
* `ProductionCarrierMap` instantiates the directed interface for the genuine
  Q'/KP bridge without demanding inverse field, polymer, or observable maps.

No contraction, stability estimate, or physical block-spin map is constructed
here.  Those remain analytic inputs; this module makes their correct directed
type available without overstating invertibility.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, quotient, or noncomputable declaration.
-/

import YMGap.RG.InductiveInterfaceBridge

namespace YMGap.RG.DirectedInterfaceTransport

open YMGap.Constructive
open YMGap.RG
open YMGap.RG.PolynomialTree
open YMGap.RG.InterfaceStability
open YMGap.RG.InductiveInterfaceBridge

universe u v

/-! ## Directed transports and state pushforward -/

/-- A forward transport between RG interfaces.

Unlike `InterfaceTransport`, none of these maps is required to have an inverse.
The response map remains dependent on the transported action, so illegal
action/response combinations still cannot be formed. -/
structure DirectedTransport (I J : RGInterface.{u}) where
  actionMap : I.action → J.action
  responseMap : (a : I.action) → I.response a → J.response (actionMap a)
  cutoffMap : I.cutoffData → J.cutoffData
  retainedFieldMap : I.retainedField → J.retainedField
  polymerActivityMap : I.polymerActivity → J.polymerActivity
  relevantCoordinateMap : I.relevantCoordinate → J.relevantCoordinate
  normMap : I.normData → J.normData
  observableMap : I.observableData → J.observableData
  certificateMap : I.certificateData → J.certificateData
  errorMap : I.errorData → J.errorData

namespace DirectedTransport

/-- Identity directed transport. -/
def refl (I : RGInterface.{u}) : DirectedTransport I I where
  actionMap := fun x => x
  responseMap := fun _ x => x
  cutoffMap := fun x => x
  retainedFieldMap := fun x => x
  polymerActivityMap := fun x => x
  relevantCoordinateMap := fun x => x
  normMap := fun x => x
  observableMap := fun x => x
  certificateMap := fun x => x
  errorMap := fun x => x

/-- Composition of forward transports. -/
def trans {I J K : RGInterface.{u}}
    (f : DirectedTransport I J) (g : DirectedTransport J K) :
    DirectedTransport I K where
  actionMap := fun a => g.actionMap (f.actionMap a)
  responseMap := fun a d => g.responseMap (f.actionMap a) (f.responseMap a d)
  cutoffMap := fun x => g.cutoffMap (f.cutoffMap x)
  retainedFieldMap := fun x => g.retainedFieldMap (f.retainedFieldMap x)
  polymerActivityMap := fun x => g.polymerActivityMap (f.polymerActivityMap x)
  relevantCoordinateMap := fun x =>
    g.relevantCoordinateMap (f.relevantCoordinateMap x)
  normMap := fun x => g.normMap (f.normMap x)
  observableMap := fun x => g.observableMap (f.observableMap x)
  certificateMap := fun x => g.certificateMap (f.certificateMap x)
  errorMap := fun x => g.errorMap (f.errorMap x)

/-- Forward-transport every carrier of a complete RG state.  The two error
ledgers are mapped independently and remain separate fields. -/
def stateForward {I J : RGInterface.{u}}
    (t : DirectedTransport I J) (s : RGState I) : RGState J where
  cutoff := t.cutoffMap s.cutoff
  effectiveField := t.retainedFieldMap s.effectiveField
  relevantPotential := t.relevantCoordinateMap s.relevantPotential
  irrelevantActivity := t.polymerActivityMap s.irrelevantActivity
  norm := t.normMap s.norm
  bounds := t.certificateMap s.bounds
  observables := t.observableMap s.observables
  certificateLedger := s.certificateLedger.map t.certificateMap
  dynamicDistortion := t.errorMap s.dynamicDistortion
  interfaceDistortion := t.errorMap s.interfaceDistortion

/-- Every exact equivalence transport has a canonical forward image. -/
def ofInterfaceTransport {I J : RGInterface.{u}}
    (t : InterfaceTransport I J) : DirectedTransport I J where
  actionMap := t.actionEquiv.toFun
  responseMap := fun a => (t.responseEquiv a).toFun
  cutoffMap := t.cutoffEquiv.toFun
  retainedFieldMap := t.retainedFieldEquiv.toFun
  polymerActivityMap := t.polymerActivityEquiv.toFun
  relevantCoordinateMap := t.relevantCoordinateEquiv.toFun
  normMap := t.normEquiv.toFun
  observableMap := t.observableEquiv.toFun
  certificateMap := t.certificateEquiv.toFun
  errorMap := t.errorEquiv.toFun

/-- Directed pushforward agrees definitionally with exact-equivalence
pushforward.  Thus the old exact API remains a strict special case. -/
theorem stateForward_ofInterfaceTransport {I J : RGInterface.{u}}
    (t : InterfaceTransport I J) (s : RGState I) :
    (ofInterfaceTransport t).stateForward s = t.stateForward s := rfl

end DirectedTransport

/-! ## Explicit semantic and error witnesses -/

/-- Preservation of the five shared interface interpretations under a
directed transport.  Equality is a witness to commutation of interpretation
with the forward map; no inverse is involved. -/
structure DirectedTransportPreserves
    {I J : RGInterface.{u}}
    {CoordinateMeaning NormMeaning PolymerMeaning
      ObservableMeaning CertificateMeaning : Type v}
    (t : DirectedTransport I J)
    (source : InterfaceSemantics I CoordinateMeaning NormMeaning
      PolymerMeaning ObservableMeaning CertificateMeaning)
    (target : InterfaceSemantics J CoordinateMeaning NormMeaning
      PolymerMeaning ObservableMeaning CertificateMeaning) : Type (max u v) where
  coordinate : ∀ x,
    target.coordinate (t.relevantCoordinateMap x) = source.coordinate x
  norm : ∀ x, target.norm (t.normMap x) = source.norm x
  localization : ∀ x,
    target.localization (t.polymerActivityMap x) = source.localization x
  observable : ∀ x, target.observable (t.observableMap x) = source.observable x
  certificate : ∀ x,
    target.certificate (t.certificateMap x) = source.certificate x

/-- Separate interpretations of dynamic and interface distortion carriers.
They share a carrier type in `RGInterface` but have different meanings and are
therefore never collapsed into one witness. -/
structure ErrorSemantics
    (I : RGInterface.{u}) (DynamicMeaning InterfaceMeaning : Type v) where
  dynamic : I.errorData → DynamicMeaning
  interface : I.errorData → InterfaceMeaning

/-- Preservation witnesses for the two error ledgers under directed
transport.  A physical implementation may replace equality with a bounded
comparison in a further analytic layer; it must still provide both fields. -/
structure DirectedErrorPreserves
    {I J : RGInterface.{u}}
    {DynamicMeaning InterfaceMeaning : Type v}
    (t : DirectedTransport I J)
    (source : ErrorSemantics I DynamicMeaning InterfaceMeaning)
    (target : ErrorSemantics J DynamicMeaning InterfaceMeaning) : Type (max u v) where
  dynamic : ∀ x, target.dynamic (t.errorMap x) = source.dynamic x
  interface : ∀ x, target.interface (t.errorMap x) = source.interface x

namespace DirectedTransportPreserves

/-- Identity forward transport preserves any declared semantics. -/
def refl
    {I : RGInterface.{u}}
    {CoordinateMeaning NormMeaning PolymerMeaning
      ObservableMeaning CertificateMeaning : Type v}
    (semantics : InterfaceSemantics I CoordinateMeaning NormMeaning
      PolymerMeaning ObservableMeaning CertificateMeaning) :
    DirectedTransportPreserves (DirectedTransport.refl I) semantics semantics where
  coordinate := fun _ => rfl
  norm := fun _ => rfl
  localization := fun _ => rfl
  observable := fun _ => rfl
  certificate := fun _ => rfl

/-- Exact semantic preservation specializes to directed preservation. -/
def ofInterfaceTransportPreserves
    {I J : RGInterface.{u}}
    {CoordinateMeaning NormMeaning PolymerMeaning
      ObservableMeaning CertificateMeaning : Type v}
    {t : InterfaceTransport I J}
    {source : InterfaceSemantics I CoordinateMeaning NormMeaning
      PolymerMeaning ObservableMeaning CertificateMeaning}
    {target : InterfaceSemantics J CoordinateMeaning NormMeaning
      PolymerMeaning ObservableMeaning CertificateMeaning}
    (h : InterfaceTransportPreserves t source target) :
    DirectedTransportPreserves (DirectedTransport.ofInterfaceTransport t)
      source target :=
  ⟨h.coordinate, h.norm, h.localization, h.observable, h.certificate⟩

end DirectedTransportPreserves

namespace DirectedErrorPreserves

/-- Identity forward transport preserves both error interpretations. -/
def refl
    {I : RGInterface.{u}} {DynamicMeaning InterfaceMeaning : Type v}
    (semantics : ErrorSemantics I DynamicMeaning InterfaceMeaning) :
    DirectedErrorPreserves (DirectedTransport.refl I) semantics semantics where
  dynamic := fun _ => rfl
  interface := fun _ => rfl

end DirectedErrorPreserves

/-! ## Production carrier maps without inverse assumptions -/

/-- The carrier maps a physical coarse-graining implementation must supply.
These are ordinary forward functions: integration/localization may lose data.
The Q'/KP carriers of `productionInterface` remain unchanged and therefore use
identity maps below. -/
structure ProductionCarrierMap
    (C D : ProductionCarriers) where
  retainedField : C.retainedField → D.retainedField
  polymerAtlas : C.polymerAtlas → D.polymerAtlas
  observableData : C.observableData → D.observableData
  verificationDiagnostic : C.verificationDiagnostic → D.verificationDiagnostic
  counterexample : C.counterexample → D.counterexample

/-- Forward map of success/failure verification results. -/
def verificationResultMap
    {CertificateA CertificateB DiagnosticA DiagnosticB : Type}
    (certificate : CertificateA → CertificateB)
    (diagnostic : DiagnosticA → DiagnosticB) :
    VerificationResult CertificateA DiagnosticA →
      VerificationResult CertificateB DiagnosticB
  | .success c => .success (certificate c)
  | .failure d => .failure (diagnostic d)

/-- Map a legacy induction atlas forward without changing its Q'/KP data. -/
def mapAtlasForward
    {P : Q' → Q' → Prop} {A B : Type}
    (f : A → B) (s : InductiveState Q' P A) : InductiveState Q' P B where
  k := s.k
  sigmaHat := s.sigmaHat
  g := s.g
  c_sf := s.c_sf
  c_lf := s.c_lf
  c_cap := s.c_cap
  poly_atlas := f s.poly_atlas

/-- Forward atlas maps preserve every legacy validity clause because those
clauses depend only on the unchanged Q'/KP data. -/
def mapAtlasForward_valid
    {P : Q' → Q' → Prop} {A B : Type}
    (f : A → B) {s : InductiveState Q' P A}
    (h : InductiveState.Valid s) :
    InductiveState.Valid (mapAtlasForward f s) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

namespace ProductionCarrierMap

/-- Dependent response map for all standard actions. -/
def responseMap
    {P : Q' → Q' → Prop} {C D : ProductionCarriers}
    (f : ProductionCarrierMap C D)
    (a : ULift RGAction) :
    (productionInterface P C).response a →
      (productionInterface P D).response a := by
  cases a with
  | up action =>
      cases action with
      | integrateFluctuation => exact f.retainedField
      | extractRelevantPart => exact fun x => x
      | localizePolymer => exact f.polymerAtlas
      | rescaleFields => exact f.retainedField
      | transportObservable => exact f.observableData
      | verifyBounds =>
          exact verificationResultMap (fun x => x) f.verificationDiagnostic
      | abortWithCounterexample => exact f.counterexample

/-- A production carrier map induces a directed transport of the complete
Q'/KP interface, with no inverse hypotheses. -/
def toDirectedTransport
    {P : Q' → Q' → Prop} {C D : ProductionCarriers}
    (f : ProductionCarrierMap C D) :
    DirectedTransport (productionInterface P C) (productionInterface P D) where
  actionMap := fun a => a
  responseMap := f.responseMap
  cutoffMap := fun x => x
  retainedFieldMap := f.retainedField
  polymerActivityMap := f.polymerAtlas
  relevantCoordinateMap := fun x => x
  normMap := fun x => x
  observableMap := f.observableData
  certificateMap := fun x => x
  errorMap := fun x => x

/-- Canonical source semantics expressed in the target carrier vocabulary.
This is structural commutation only; a physical interpretation can instead
supply its own `InterfaceSemantics` and preservation proof. -/
def sourceSemantics
    {P : Q' → Q' → Prop} {C D : ProductionCarriers}
    (f : ProductionCarrierMap C D) :
    InterfaceSemantics (productionInterface P C)
      RelevantCoordinates KPNormSummary D.polymerAtlas D.observableData
      (KPCertificateBundle P) where
  coordinate := fun x => x
  norm := fun x => x
  localization := f.polymerAtlas
  observable := f.observableData
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

/-- Canonical structural semantics commute with production carrier maps. -/
def transportPreserves
    {P : Q' → Q' → Prop} {C D : ProductionCarriers}
    (f : ProductionCarrierMap C D) :
    DirectedTransportPreserves (f.toDirectedTransport (P := P))
      (f.sourceSemantics (P := P)) (targetSemantics (P := P) D) where
  coordinate := fun _ => rfl
  norm := fun _ => rfl
  localization := fun _ => rfl
  observable := fun _ => rfl
  certificate := fun _ => rfl

/-- The production Q' error carrier, with dynamic and interface ledgers
interpreted separately even though both currently use exact rational values. -/
def qErrorSemantics
    {P : Q' → Q' → Prop} (C : ProductionCarriers) :
    ErrorSemantics (productionInterface P C) Q' Q' where
  dynamic := fun x => x
  interface := fun x => x

/-- Production carrier transport preserves both Q' error ledgers separately. -/
def errorPreserves
    {P : Q' → Q' → Prop} {C D : ProductionCarriers}
    (f : ProductionCarrierMap C D) :
    DirectedErrorPreserves (f.toDirectedTransport (P := P))
      (qErrorSemantics (P := P) C) (qErrorSemantics (P := P) D) where
  dynamic := fun _ => rfl
  interface := fun _ => rfl

/-- Naturality of the production bridge under arbitrary forward carrier maps.
No inverse is used. -/
theorem stateForward_ofInductiveState
    {P : Q' → Q' → Prop} {C D : ProductionCarriers}
    (f : ProductionCarrierMap C D)
    (s : InductiveState Q' P C.polymerAtlas)
    (field : C.retainedField) (observable : C.observableData)
    (dynamicError interfaceError : Q') :
    (f.toDirectedTransport (P := P)).stateForward
        (ofInductiveState s field observable dynamicError interfaceError) =
      ofInductiveState (mapAtlasForward f.polymerAtlas s)
        (f.retainedField field) (f.observableData observable)
        dynamicError interfaceError := by
  cases s
  rfl

end ProductionCarrierMap

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms DirectedTransport
#print axioms DirectedTransport.trans
#print axioms DirectedTransport.stateForward
#print axioms DirectedTransport.ofInterfaceTransport
#print axioms DirectedTransport.stateForward_ofInterfaceTransport
#print axioms DirectedTransportPreserves
#print axioms DirectedErrorPreserves
#print axioms DirectedTransportPreserves.ofInterfaceTransportPreserves
#print axioms ProductionCarrierMap
#print axioms mapAtlasForward_valid
#print axioms ProductionCarrierMap.toDirectedTransport
#print axioms ProductionCarrierMap.transportPreserves
#print axioms ProductionCarrierMap.errorPreserves
#print axioms ProductionCarrierMap.stateForward_ofInductiveState

end YMGap.RG.DirectedInterfaceTransport
