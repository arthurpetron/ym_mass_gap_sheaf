/-
Forward-only stable-tail presentation for non-invertible RG coarse graining.

Physical block-spin maps generally discard fine degrees of freedom.  The
canonical `DirectedTransport` therefore maps every interface carrier forward
without asserting an inverse.  This module derives the strongest RG-I5/I6
consequence supported by that data:

* the selected source ray retains its exact dependent action/response typing;
* every selected action, response, and complete state maps forward into one
  stable interface;
* the forward images form a ray in a genuinely constant polynomial tree;
* declared coordinate, norm, localization, observable, certificate, dynamic
  error, and interface-error meanings commute with forward transport; and
* every positive rational resolution returns a tail offset and physical scale
  whose entire suffix satisfies the interface-discrepancy bound.

No state recovery, injectivity, interface isomorphism, or equivalence of the
source branching tree with the constant tree is claimed.  Exact equivalence
certificates embed as a strict special case, but physical instances need only
provide directed maps.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, quotient, or noncomputable declaration.
-/

import YMGap.RG.DirectedInterfaceTransport

namespace YMGap.RG.DirectedStableTailPresentation

open YMGap.Constructive
open YMGap.RG.PolynomialTree
open YMGap.RG.InterfaceStability
open YMGap.RG.DirectedInterfaceTransport

universe u v

/-! ## Forward-composition coherence -/

@[simp] private theorem list_map_identity {A : Type u} : ∀ xs : List A,
    xs.map (fun x => x) = xs
  | [] => rfl
  | _ :: xs => by simp [list_map_identity xs]

@[simp] private theorem list_map_composition
    {A B C : Type u} (f : A → B) (g : B → C) : ∀ xs : List A,
    (xs.map f).map g = xs.map (fun x => g (f x))
  | [] => rfl
  | _ :: xs => by simp [list_map_composition f g xs]

/-- Identity directed transport acts identically on complete states. -/
theorem directedStateForward_refl
    (I : RGInterface.{u}) (s : RGState I) :
    (DirectedTransport.refl I).stateForward s = s := by
  cases s
  simp only [DirectedTransport.stateForward, DirectedTransport.refl]
  congr 1
  exact list_map_identity _

/-- Complete-state pushforward respects composition of directed transports. -/
theorem directedStateForward_trans
    {I J K : RGInterface.{u}}
    (f : DirectedTransport I J) (g : DirectedTransport J K)
    (s : RGState I) :
    (f.trans g).stateForward s = g.stateForward (f.stateForward s) := by
  cases s
  simp only [DirectedTransport.stateForward, DirectedTransport.trans]
  congr 1
  exact (list_map_composition f.certificateMap g.certificateMap _).symm

/-! ## Selected rays and forward stable-tail certificates -/

/-- A selected infinite ray of an RG polynomial tree. -/
structure SelectedRay (p : RGProgram.{u}) where
  nodeAt : Nat → p.Node
  actionAt : (n : Nat) → (p.interface (nodeAt n)).action
  responseAt : (n : Nat) →
    (p.interface (nodeAt n)).response (actionAt n)
  follows : ∀ n,
    p.next (nodeAt n) (actionAt n) (responseAt n) = nodeAt (n + 1)

/-- Forward-only stabilization data for a selected physical RG ray.

Offsets are measured from `kStar`.  Each source interface maps into the common
stable interface, but the map need not be reversible.  Dynamic and interface
errors have separate interpretation types and preservation witnesses. -/
structure DirectedStableTailCertificate (p : RGProgram.{u}) where
  kStar : Nat
  stableInterface : RGInterface.{u}
  nodeAt : Nat → p.Node
  actionAt : (n : Nat) → (p.interface (nodeAt n)).action
  responseAt : (n : Nat) →
    (p.interface (nodeAt n)).response (actionAt n)
  followsRay : ∀ n,
    p.next (nodeAt n) (actionAt n) (responseAt n) = nodeAt (n + 1)
  transport : (n : Nat) →
    DirectedTransport (p.interface (nodeAt n)) stableInterface
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
    DirectedTransportPreserves (transport n) (sourceSemantics n) stableSemantics
  DynamicErrorMeaning : Type u
  InterfaceErrorMeaning : Type u
  sourceErrorSemantics : (n : Nat) →
    ErrorSemantics (p.interface (nodeAt n))
      DynamicErrorMeaning InterfaceErrorMeaning
  stableErrorSemantics :
    ErrorSemantics stableInterface DynamicErrorMeaning InterfaceErrorMeaning
  errorPreserves : (n : Nat) →
    DirectedErrorPreserves (transport n) (sourceErrorSemantics n)
      stableErrorSemantics
  discrepancy : Nat → InterfaceDiscrepancy
  discrepancyNonnegative : ∀ n, (discrepancy n).Nonnegative
  tolerance : Nat → Q'
  withinTolerance : ∀ n, (discrepancy n).maximum ≤ tolerance n
  modulus : Q' → Nat
  eventuallyWithin : ∀ ε : Q', (0 : Q') < ε →
    ∀ n, modulus ε ≤ n → tolerance n ≤ ε

namespace DirectedStableTailCertificate

/-- The typed source ray carried by the certificate. -/
def sourceRay {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p) : SelectedRay p where
  nodeAt := c.nodeAt
  actionAt := c.actionAt
  responseAt := c.responseAt
  follows := c.followsRay

/-- Physical scale corresponding to offset `n`. -/
def physicalScale {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p) (n : Nat) : Nat :=
  c.kStar + n

theorem kStar_le_physicalScale {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p) (n : Nat) :
    c.kStar ≤ c.physicalScale n :=
  Nat.le_add_right _ _

/-- Extract an all-later stabilization offset as Type-level data. -/
def scaleFor {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p)
    (ε : Q') (hε : (0 : Q') < ε) :
    Σ' N : Nat, ∀ n, N ≤ n → (c.discrepancy n).maximum ≤ ε :=
  ⟨c.modulus ε, fun n hn =>
    Q'.le_trans' _ _ _ (c.withinTolerance n)
      (c.eventuallyWithin ε hε n hn)⟩

/-- An exact-equivalence stable tail has a canonical directed presentation.

The two error interpretations remain separate fields, even though this exact
special case interprets both in the common stable error carrier. -/
def ofStableTailCertificate {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p) :
    DirectedStableTailCertificate.{u, v} p where
  kStar := c.kStar
  stableInterface := c.stableInterface
  nodeAt := c.nodeAt
  actionAt := c.actionAt
  responseAt := c.responseAt
  followsRay := c.followsBranch
  transport := fun n => DirectedTransport.ofInterfaceTransport (c.transport n)
  CoordinateMeaning := c.CoordinateMeaning
  NormMeaning := c.NormMeaning
  PolymerMeaning := c.PolymerMeaning
  ObservableMeaning := c.ObservableMeaning
  CertificateMeaning := c.CertificateMeaning
  sourceSemantics := c.sourceSemantics
  stableSemantics := c.stableSemantics
  transportPreserves := fun n =>
    DirectedTransportPreserves.ofInterfaceTransportPreserves
      (c.transportPreserves n)
  DynamicErrorMeaning := c.stableInterface.errorData
  InterfaceErrorMeaning := c.stableInterface.errorData
  sourceErrorSemantics := fun n =>
    { dynamic := (c.transport n).errorEquiv.toFun
      interface := (c.transport n).errorEquiv.toFun }
  stableErrorSemantics :=
    { dynamic := fun x => x
      interface := fun x => x }
  errorPreserves := fun _ =>
    { dynamic := fun _ => rfl
      interface := fun _ => rfl }
  discrepancy := c.discrepancy
  discrepancyNonnegative := c.discrepancyNonnegative
  tolerance := c.tolerance
  withinTolerance := c.withinTolerance
  modulus := c.modulus
  eventuallyWithin := c.eventuallyWithin

end DirectedStableTailCertificate

/-! ## Constant target program and ray -/

/-- A genuinely constant-interface target program. -/
def constantTargetProgram (I : RGInterface.{u}) : RGProgram.{u} where
  Node := PUnit
  interface := fun _ => I
  next := fun _ _ _ => PUnit.unit

/-- Its polynomial tree is definitionally the standard constant-tree
embedding. -/
theorem constantTargetProgram_toPolyTree (I : RGInterface.{u}) :
    (constantTargetProgram I).toPolyTree PUnit.unit =
      PolyTree.constant I.toPolynomial := rfl

namespace DirectedStableTailCertificate

/-- Forward image of the selected source action. -/
def stableActionAt {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p) (n : Nat) :
    c.stableInterface.action :=
  (c.transport n).actionMap (c.actionAt n)

/-- Forward image of the selected response, indexed by the forward action. -/
def stableResponseAt {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p) (n : Nat) :
    c.stableInterface.response (c.stableActionAt n) :=
  (c.transport n).responseMap (c.actionAt n) (c.responseAt n)

/-- The forward images form a ray in the constant target program. -/
def constantRay {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p) :
    SelectedRay (constantTargetProgram c.stableInterface) where
  nodeAt := fun _ => PUnit.unit
  actionAt := c.stableActionAt
  responseAt := c.stableResponseAt
  follows := fun _ => rfl

/-- A source-state family along the selected changing-interface ray. -/
abbrev SourceStateFamily {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p) :=
  (n : Nat) → RGState (p.interface (c.nodeAt n))

/-- Forward-normalize a complete source state into the stable interface. -/
def stableStateAt {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p)
    (states : SourceStateFamily c) (n : Nat) :
    RGState c.stableInterface :=
  (c.transport n).stateForward (states n)

/-- Relevant-coordinate meaning commutes with forward normalization. -/
theorem coordinateMeaning_stableStateAt {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p)
    (states : SourceStateFamily c) (n : Nat) :
    c.stableSemantics.coordinate (c.stableStateAt states n).relevantPotential =
      (c.sourceSemantics n).coordinate (states n).relevantPotential :=
  (c.transportPreserves n).coordinate _

/-- Norm meaning commutes with forward normalization. -/
theorem normMeaning_stableStateAt {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p)
    (states : SourceStateFamily c) (n : Nat) :
    c.stableSemantics.norm (c.stableStateAt states n).norm =
      (c.sourceSemantics n).norm (states n).norm :=
  (c.transportPreserves n).norm _

/-- Polymer/localization meaning commutes with forward normalization. -/
theorem localizationMeaning_stableStateAt {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p)
    (states : SourceStateFamily c) (n : Nat) :
    c.stableSemantics.localization
        (c.stableStateAt states n).irrelevantActivity =
      (c.sourceSemantics n).localization (states n).irrelevantActivity :=
  (c.transportPreserves n).localization _

/-- Observable meaning commutes with forward normalization. -/
theorem observableMeaning_stableStateAt {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p)
    (states : SourceStateFamily c) (n : Nat) :
    c.stableSemantics.observable (c.stableStateAt states n).observables =
      (c.sourceSemantics n).observable (states n).observables :=
  (c.transportPreserves n).observable _

/-- Certificate meaning commutes with forward normalization. -/
theorem certificateMeaning_stableStateAt {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p)
    (states : SourceStateFamily c) (n : Nat) :
    c.stableSemantics.certificate (c.stableStateAt states n).bounds =
      (c.sourceSemantics n).certificate (states n).bounds :=
  (c.transportPreserves n).certificate _

/-- Dynamic-error meaning remains separate and commutes with pushforward. -/
theorem dynamicErrorMeaning_stableStateAt {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p)
    (states : SourceStateFamily c) (n : Nat) :
    c.stableErrorSemantics.dynamic
        (c.stableStateAt states n).dynamicDistortion =
      (c.sourceErrorSemantics n).dynamic (states n).dynamicDistortion :=
  (c.errorPreserves n).dynamic _

/-- Interface-error meaning remains separate and commutes with pushforward. -/
theorem interfaceErrorMeaning_stableStateAt {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p)
    (states : SourceStateFamily c) (n : Nat) :
    c.stableErrorSemantics.interface
        (c.stableStateAt states n).interfaceDistortion =
      (c.sourceErrorSemantics n).interface (states n).interfaceDistortion :=
  (c.errorPreserves n).interface _

end DirectedStableTailCertificate

/-! ## Resolution-indexed directed presentation -/

/-- Constructive forward-only landing data at a requested interface
resolution.  The action/response equalities tie the returned constant ray to
the forward image of the selected physical ray. -/
structure DirectedConstantTailAtResolution
    {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p) (ε : Q') where
  offset : Nat
  physicalScale : Nat
  physicalScale_eq : physicalScale = c.kStar + offset
  kStar_le_physicalScale : c.kStar ≤ physicalScale
  stableRay : SelectedRay (constantTargetProgram c.stableInterface)
  stableAction_eq : ∀ n, stableRay.actionAt n = c.stableActionAt n
  stableResponse_eq : ∀ n,
    HEq (stableRay.responseAt n) (c.stableResponseAt n)
  discrepancyWithin : ∀ n, offset ≤ n → (c.discrepancy n).maximum ≤ ε

namespace DirectedStableTailCertificate

/-- Compute the directed constant-ray presentation and all-later discrepancy
bound at any positive rational resolution. -/
def constantTailAtResolution {p : RGProgram.{u}}
    (c : DirectedStableTailCertificate.{u, v} p)
    (ε : Q') (hε : (0 : Q') < ε) :
    DirectedConstantTailAtResolution c ε :=
  let landing := c.scaleFor ε hε
  { offset := landing.1
    physicalScale := c.kStar + landing.1
    physicalScale_eq := rfl
    kStar_le_physicalScale := Nat.le_add_right _ _
    stableRay := c.constantRay
    stableAction_eq := fun _ => rfl
    stableResponse_eq := fun _ => HEq.rfl
    discrepancyWithin := landing.2 }

end DirectedStableTailCertificate

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms directedStateForward_refl
#print axioms directedStateForward_trans
#print axioms SelectedRay
#print axioms DirectedStableTailCertificate
#print axioms DirectedStableTailCertificate.scaleFor
#print axioms DirectedStableTailCertificate.ofStableTailCertificate
#print axioms constantTargetProgram_toPolyTree
#print axioms DirectedStableTailCertificate.constantRay
#print axioms DirectedStableTailCertificate.stableStateAt
#print axioms DirectedStableTailCertificate.coordinateMeaning_stableStateAt
#print axioms DirectedStableTailCertificate.normMeaning_stableStateAt
#print axioms DirectedStableTailCertificate.localizationMeaning_stableStateAt
#print axioms DirectedStableTailCertificate.observableMeaning_stableStateAt
#print axioms DirectedStableTailCertificate.certificateMeaning_stableStateAt
#print axioms DirectedStableTailCertificate.dynamicErrorMeaning_stableStateAt
#print axioms DirectedStableTailCertificate.interfaceErrorMeaning_stableStateAt
#print axioms DirectedConstantTailAtResolution
#print axioms DirectedStableTailCertificate.constantTailAtResolution

end YMGap.RG.DirectedStableTailPresentation
