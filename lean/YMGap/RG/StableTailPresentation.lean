/-
Constant-interface presentation of a certified RG tail.

`InterfaceStability.StableTailCertificate` already supplies a selected typed
branch, coherent transports from every interface on that branch into one
stable interface, and a computable discrepancy modulus.  This module extracts
the exact structural consequence needed by RG-I6:

* the selected source branch remains typed in the original changing-interface
  program;
* its actions, responses, and states are transported into a single constant
  interface with exact round trips;
* the transported action/response sequence is a branch of a genuinely
  constant polynomial tree; and
* at every positive rational resolution, the landing offset and physical
  scale are returned as Type-level data together with the tail bound.

This identifies only the selected branch.  A `StableTailCertificate` contains
no transports for off-branch children, so this file deliberately makes no
claim that the entire branching source tree is equivalent to a constant tree.
It also does not construct the physical Yang--Mills stabilization certificate:
the physical transports and discrepancy estimate remain analytic inputs.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, quotient, or noncomputable declaration.
-/

import YMGap.RG.InterfaceStability

namespace YMGap.RG.StableTailPresentation

open YMGap.Constructive
open YMGap.RG.PolynomialTree
open YMGap.RG.InterfaceStability

universe u v

/-! ## Typed selected branches -/

/-- An infinite selected branch of an RG polynomial tree.

Every response is indexed by the action chosen at the same node, and
`followsBranch` records the exact source-program successor. -/
structure SelectedBranch (p : RGProgram.{u}) where
  nodeAt : Nat → p.Node
  actionAt : (n : Nat) → (p.interface (nodeAt n)).action
  responseAt : (n : Nat) →
    (p.interface (nodeAt n)).response (actionAt n)
  followsBranch : ∀ n,
    p.next (nodeAt n) (actionAt n) (responseAt n) = nodeAt (n + 1)

/-- Forget the analytic fields of a stabilization certificate while retaining
its fully typed selected source branch. -/
def StableTailCertificate.sourceBranch
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p) : SelectedBranch p where
  nodeAt := c.nodeAt
  actionAt := c.actionAt
  responseAt := c.responseAt
  followsBranch := c.followsBranch

/-- Physical scale corresponding to offset `n` along the certified tail. -/
def StableTailCertificate.physicalScale
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p) (n : Nat) : Nat :=
  c.kStar + n

@[simp] theorem StableTailCertificate.physicalScale_zero
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p) :
    physicalScale c 0 = c.kStar := rfl

theorem StableTailCertificate.kStar_le_physicalScale
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p) (n : Nat) :
    c.kStar ≤ physicalScale c n :=
  Nat.le_add_right _ _

/-! ## The constant-interface target program -/

/-- The RG program whose interface is definitionally constant and whose
polynomial tree has a single internal node code. -/
def constantInterfaceProgram (I : RGInterface.{u}) : RGProgram.{u} where
  Node := PUnit
  interface := fun _ => I
  next := fun _ _ _ => PUnit.unit

@[simp] theorem constantInterfaceProgram_interface
    (I : RGInterface.{u}) (n : (constantInterfaceProgram I).Node) :
    (constantInterfaceProgram I).interface n = I := rfl

@[simp] theorem constantInterfaceProgram_next
    (I : RGInterface.{u})
    (n : (constantInterfaceProgram I).Node)
    (a : ((constantInterfaceProgram I).interface n).action)
    (d : ((constantInterfaceProgram I).interface n).response a) :
    (constantInterfaceProgram I).next n a d = PUnit.unit := rfl

/-- The polynomial tree underlying `constantInterfaceProgram` is exactly the
standard constant-tree embedding. -/
theorem constantInterfaceProgram_toPolyTree
    (I : RGInterface.{u}) :
    (constantInterfaceProgram I).toPolyTree PUnit.unit =
      PolyTree.constant I.toPolynomial := rfl

/-- The constant-interface target tree attached to a stable-tail
certificate. -/
def StableTailCertificate.constantTree
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p) : PolyTree.{u} :=
  PolyTree.constant c.stableInterface.toPolynomial

@[simp] theorem StableTailCertificate.constantTree_child
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p)
    (a : c.stableInterface.action)
    (d : c.stableInterface.response a) :
    ((constantTree c).child a d) = constantTree c := rfl

/-! ## Exact action/response transport onto the constant tree -/

/-- Selected source action expressed in the common stable interface. -/
def StableTailCertificate.stableActionAt
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p) (n : Nat) :
    c.stableInterface.action :=
  (c.transport n).actionEquiv (c.actionAt n)

/-- Selected source response expressed in the common stable interface. -/
def StableTailCertificate.stableResponseAt
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p) (n : Nat) :
    c.stableInterface.response (stableActionAt c n) :=
  (c.transport n).responseEquiv (c.actionAt n) (c.responseAt n)

/-- Transporting the stable action back recovers the exact source action. -/
theorem StableTailCertificate.stableActionAt_roundTrip
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p) (n : Nat) :
    (c.transport n).actionEquiv.invFun (stableActionAt c n) = c.actionAt n :=
  TypeEquiv.invFun_apply _ _

/-- Transporting the stable response back recovers the exact source response.
The response equivalence remains indexed by the original selected action. -/
theorem StableTailCertificate.stableResponseAt_roundTrip
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p) (n : Nat) :
    ((c.transport n).responseEquiv (c.actionAt n)).invFun
        (stableResponseAt c n) = c.responseAt n :=
  TypeEquiv.invFun_apply _ _

/-- The transported action/response sequence is an infinite branch of the
genuinely constant-interface target program. -/
def StableTailCertificate.constantBranch
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p) :
    SelectedBranch (constantInterfaceProgram c.stableInterface) where
  nodeAt := fun _ => PUnit.unit
  actionAt := stableActionAt c
  responseAt := stableResponseAt c
  followsBranch := fun _ => rfl

/-- Every successor on the target branch stays at the same constant tree
node, independently of the transported action and response. -/
theorem StableTailCertificate.constantBranch_follows
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p) (n : Nat) :
    (constantInterfaceProgram c.stableInterface).next
        ((constantBranch c).nodeAt n)
        ((constantBranch c).actionAt n)
        ((constantBranch c).responseAt n) =
      (constantBranch c).nodeAt (n + 1) := rfl

/-! ## State-family transport and semantic coherence -/

/-- A changing-interface family of states along the selected source branch. -/
abbrev SourceStateFamily
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p) :=
  (n : Nat) → RGState (p.interface (c.nodeAt n))

/-- Transport one complete source state into the common stable interface. -/
def StableTailCertificate.stableStateAt
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p)
    (states : SourceStateFamily c) (n : Nat) :
    RGState c.stableInterface :=
  (c.transport n).stateForward (states n)

/-- Stable-interface state transport is exactly reversible at every offset. -/
theorem StableTailCertificate.stableStateAt_roundTrip
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p)
    (states : SourceStateFamily c) (n : Nat) :
    (c.transport n).stateBackward (stableStateAt c states n) = states n :=
  InterfaceTransport.stateBackward_forward _ _

/-- Relevant-coordinate meaning is unchanged by stable-interface transport. -/
theorem StableTailCertificate.coordinateMeaning_stableStateAt
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p)
    (states : SourceStateFamily c) (n : Nat) :
    c.stableSemantics.coordinate (stableStateAt c states n).relevantPotential =
      (c.sourceSemantics n).coordinate (states n).relevantPotential :=
  (c.transportPreserves n).coordinate _

/-- Gaussian-norm meaning is unchanged by stable-interface transport. -/
theorem StableTailCertificate.normMeaning_stableStateAt
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p)
    (states : SourceStateFamily c) (n : Nat) :
    c.stableSemantics.norm (stableStateAt c states n).norm =
      (c.sourceSemantics n).norm (states n).norm :=
  (c.transportPreserves n).norm _

/-- Polymer/localization meaning is unchanged by stable-interface transport. -/
theorem StableTailCertificate.localizationMeaning_stableStateAt
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p)
    (states : SourceStateFamily c) (n : Nat) :
    c.stableSemantics.localization
        (stableStateAt c states n).irrelevantActivity =
      (c.sourceSemantics n).localization (states n).irrelevantActivity :=
  (c.transportPreserves n).localization _

/-- Observable meaning is unchanged by stable-interface transport. -/
theorem StableTailCertificate.observableMeaning_stableStateAt
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p)
    (states : SourceStateFamily c) (n : Nat) :
    c.stableSemantics.observable (stableStateAt c states n).observables =
      (c.sourceSemantics n).observable (states n).observables :=
  (c.transportPreserves n).observable _

/-- Bound-certificate meaning is unchanged by stable-interface transport. -/
theorem StableTailCertificate.certificateMeaning_stableStateAt
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p)
    (states : SourceStateFamily c) (n : Nat) :
    c.stableSemantics.certificate (stableStateAt c states n).bounds =
      (c.sourceSemantics n).certificate (states n).bounds :=
  (c.transportPreserves n).certificate _

/-! ## Constructive landing at a requested resolution -/

/-- Type-level landing data for a positive rational interface resolution.

`offset` is the computable tail offset, `physicalScale` is the corresponding
actual scale, `stableBranch` is the constant-interface presentation, and
`discrepancyWithin` controls every later source interface. -/
structure ConstantTailAtResolution
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p) (ε : Q') where
  offset : Nat
  physicalScale : Nat
  physicalScale_eq : physicalScale = c.kStar + offset
  kStar_le_physicalScale : c.kStar ≤ physicalScale
  stableBranch : SelectedBranch (constantInterfaceProgram c.stableInterface)
  stableAction_eq : ∀ n,
    stableBranch.actionAt n = StableTailCertificate.stableActionAt c n
  stableResponse_eq : ∀ n,
    HEq (stableBranch.responseAt n)
      (StableTailCertificate.stableResponseAt c n)
  discrepancyWithin : ∀ n, offset ≤ n → (c.discrepancy n).maximum ≤ ε

/-- Compute the constant-interface landing data at any positive resolution. -/
def StableTailCertificate.constantTailAtResolution
    {p : RGProgram.{u}}
    (c : StableTailCertificate.{u, v} p)
    (ε : Q') (hε : (0 : Q') < ε) :
    ConstantTailAtResolution c ε :=
  let landing := c.scaleFor ε hε
  { offset := landing.1
    physicalScale := c.kStar + landing.1
    physicalScale_eq := rfl
    kStar_le_physicalScale := Nat.le_add_right _ _
    stableBranch := constantBranch c
    stableAction_eq := fun _ => rfl
    stableResponse_eq := fun _ => HEq.rfl
    discrepancyWithin := landing.2 }

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms SelectedBranch
#print axioms StableTailCertificate.sourceBranch
#print axioms StableTailCertificate.kStar_le_physicalScale
#print axioms constantInterfaceProgram_toPolyTree
#print axioms StableTailCertificate.constantTree_child
#print axioms StableTailCertificate.stableActionAt_roundTrip
#print axioms StableTailCertificate.stableResponseAt_roundTrip
#print axioms StableTailCertificate.constantBranch
#print axioms StableTailCertificate.constantBranch_follows
#print axioms StableTailCertificate.stableStateAt_roundTrip
#print axioms StableTailCertificate.coordinateMeaning_stableStateAt
#print axioms StableTailCertificate.normMeaning_stableStateAt
#print axioms StableTailCertificate.localizationMeaning_stableStateAt
#print axioms StableTailCertificate.observableMeaning_stableStateAt
#print axioms StableTailCertificate.certificateMeaning_stableStateAt
#print axioms ConstantTailAtResolution
#print axioms StableTailCertificate.constantTailAtResolution

end YMGap.RG.StableTailPresentation
