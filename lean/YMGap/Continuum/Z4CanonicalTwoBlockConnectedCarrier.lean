/-
# A connected carrier for the two-block disagreement branch

When the two-block classifier is connected, it supplies two canonical polymer
roots joined in the two-replica disagreement graph.  This file turns a
constructively loop-erased disagreement path between those roots into one
literal connected plaquette support.  For the strict doubled-time OS blocks,
the support inherits the previously proved linear `2 * shift + 6` size floor.

The construction is geometric.  It does not yet sum carrier weights or prove
a Poincare inequality.
-/

import YMGap.Continuum.Z4CanonicalTwoBlockComponentSwitch
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeCarrierFloor

namespace YMGap.Continuum.Z4CanonicalTwoBlockConnectedCarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteDisagreementReverseRecovery
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalMarkedRootSwitch
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeCarrierFloor
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedEventRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4PhysicalSurfaceComponents

/-! ## 1. A literal path support between two reached atoms -/

def twoBlockDisagreementEdge
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n) :
    CanonicalAtom n → CanonicalAtom n → Bool :=
  disagreementEdge (canonicalAmbientAtoms n)
    (canonicalAtomCompatibleB n)
    (memberB (canonicalFamilyAtoms hleft))
    (memberB (canonicalFamilyAtoms hright))

def twoBlockConnectedPath
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (first second : CanonicalAtom n)
    (hreach : canonicalDisagreementCut hleft hright first second = true) :
    CWalk.Simple (twoBlockDisagreementEdge hleft hright) first second :=
  simpleWalkOfWarshall (twoBlockDisagreementEdge hleft hright)
    (canonicalAmbientAtoms n) first second (by
      simpa [twoBlockDisagreementEdge, canonicalDisagreementCut] using hreach)

def twoBlockConnectedPathAtoms
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (first second : CanonicalAtom n)
    (hreach : canonicalDisagreementCut hleft hright first second = true) :
    List (CanonicalAtom n) :=
  (twoBlockConnectedPath hleft hright first second hreach).walk.vertices

def twoBlockConnectedCarrierSupport
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (first second : CanonicalAtom n)
    (hreach : canonicalDisagreementCut hleft hright first second = true) :
    List Nat :=
  familyUnionSupport n
    ((twoBlockConnectedPathAtoms
      hleft hright first second hreach).map Subtype.val)

theorem twoBlockConnectedPathAtom_face_mem_support
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (first second : CanonicalAtom n)
    (hreach : canonicalDisagreementCut hleft hright first second = true)
    {atom : CanonicalAtom n}
    (hatom : atom ∈ twoBlockConnectedPathAtoms
      hleft hright first second hreach)
    {face : Nat} (hface : face ∈ atom.val) :
    face ∈ twoBlockConnectedCarrierSupport
      hleft hright first second hreach := by
  unfold twoBlockConnectedCarrierSupport
  rw [mem_familyUnionSupport_iff]
  constructor
  · exact mem_of_mem_sublists (physicalFaceEdges n) atom.val
      (canonicalSurfacePolymer_mem_faceSupports atom.property) face hface
  · exact ⟨atom.val, List.mem_map.mpr ⟨atom, hatom, rfl⟩, hface⟩

def twoBlockConnectedCarrierSupport_face_witness
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (first second : CanonicalAtom n)
    (hreach : canonicalDisagreementCut hleft hright first second = true)
    {face : Nat}
    (hface : face ∈ twoBlockConnectedCarrierSupport
      hleft hright first second hreach) :
    Σ' atom : CanonicalAtom n,
      (atom ∈ twoBlockConnectedPathAtoms
        hleft hright first second hreach) ×' (face ∈ atom.val) := by
  have hcontains : familyContainsFaceB face
      ((twoBlockConnectedPathAtoms
        hleft hright first second hreach).map Subtype.val) = true := by
    unfold twoBlockConnectedCarrierSupport familyUnionSupport at hface
    exact (List.mem_filter.mp hface).2
  obtain ⟨polymer, hpolymer, hfacePolymer⟩ :=
    familyContainsFaceWitness face _ hcontains
  obtain ⟨atom, hatom, hatomValue⟩ :=
    decodeMapMember Subtype.val
      (twoBlockConnectedPathAtoms hleft hright first second hreach)
      polymer hpolymer
  refine ⟨atom, hatom, ?_⟩
  rw [hatomValue]
  exact hfacePolymer

theorem twoBlockConnectedCarrierSupport_mem_faceSupports
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (first second : CanonicalAtom n)
    (hreach : canonicalDisagreementCut hleft hright first second = true) :
    twoBlockConnectedCarrierSupport hleft hright first second hreach ∈
      cutoffOneFaceSupports n :=
  familyUnionSupport_mem_cutoffOneFaceSupports n _

/-! ## 2. The path union is internally face-connected -/

def twoBlockDisagreementCWalk_faceChainFromStart
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n) :
    ∀ {first last : CanonicalAtom n}
      (walk : CWalk (twoBlockDisagreementEdge hleft hright) first last)
      (support : List Nat),
      (∀ atom, atom ∈ walk.vertices →
        ∀ face, face ∈ atom.val → face ∈ support) →
      ∀ {target : CanonicalAtom n}, target ∈ walk.vertices →
        ∀ {start finish : Nat}, start ∈ first.val →
          finish ∈ target.val →
          ChainIn (faceLinkAdjacentB n) support start finish
  | _, _, .single atom, support, hcover, target, htarget,
      start, finish, hstart, hfinish => by
      have htargetEq : target = atom := List.mem_singleton.mp htarget
      subst target
      exact ChainIn.mono
        (fun face hface => hcover atom List.mem_cons_self face hface)
        ((canonicalSurfacePolymers_allConnected n) atom atom.property
          start finish hstart hfinish)
  | first, last, .cons (middle := middle) hedge rest, support, hcover,
      target, htarget, start, finish, hstart, hfinish => by
      cases heqTarget : decide (target = first) with
      | true =>
          have htargetFirst : target = first := of_decide_eq_true heqTarget
          subst target
          exact ChainIn.mono
            (fun face hface => hcover first List.mem_cons_self face hface)
            ((canonicalSurfacePolymers_allConnected n) first first.property
              start finish hstart hfinish)
      | false =>
          have htargetFirst : target ≠ first := of_decide_eq_false heqTarget
          have htargetRest : target ∈ rest.vertices :=
            (List.mem_cons.mp htarget).resolve_left htargetFirst
          have hincompatible : canonicalPolymerCompatibleB n
              first.val middle.val = false :=
            canonicalDisagreementEdge_incompatible hleft hright
              (by simpa [twoBlockDisagreementEdge] using hedge)
          obtain ⟨leftContact, hleftContact, rightContact,
              hrightContact, hcontact⟩ :=
            canonicalPolymerIncompatibleContact hincompatible
          have hhead : ChainIn (faceLinkAdjacentB n) support
              start leftContact :=
            ChainIn.mono
              (fun face hface =>
                hcover first List.mem_cons_self face hface)
              ((canonicalSurfacePolymers_allConnected n) first first.property
                start leftContact hstart hleftContact)
          have htail : ChainIn (faceLinkAdjacentB n) support
              rightContact finish :=
            twoBlockDisagreementCWalk_faceChainFromStart
              hleft hright rest support
              (fun atom hatom face hface =>
                hcover atom (List.mem_cons_of_mem first hatom) face hface)
              htargetRest hrightContact hfinish
          cases hcontact with
          | same heq =>
              subst rightContact
              exact ChainIn.trans hhead htail
          | adjacent hadj =>
              exact ChainIn.trans hhead
                (.step hadj
                  (hcover middle
                    (List.mem_cons_of_mem first
                      (CWalk.start_mem_vertices rest))
                    rightContact hrightContact)
                  htail)

def twoBlockConnectedCarrierSupport_chain_from_first
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (first second : CanonicalAtom n)
    (hreach : canonicalDisagreementCut hleft hright first second = true)
    {firstFace face : Nat} (hfirstFace : firstFace ∈ first.val)
    (hface : face ∈ twoBlockConnectedCarrierSupport
      hleft hright first second hreach) :
    ChainIn (faceLinkAdjacentB n)
      (twoBlockConnectedCarrierSupport hleft hright first second hreach)
      firstFace face := by
  obtain ⟨target, htarget, hfaceTarget⟩ :=
    twoBlockConnectedCarrierSupport_face_witness
      hleft hright first second hreach hface
  exact twoBlockDisagreementCWalk_faceChainFromStart hleft hright
    (twoBlockConnectedPath hleft hright first second hreach).walk
    (twoBlockConnectedCarrierSupport hleft hright first second hreach)
    (fun atom hatom found hfound =>
      twoBlockConnectedPathAtom_face_mem_support
        hleft hright first second hreach hatom hfound)
    htarget hfirstFace hfaceTarget

def twoBlockConnectedCarrierSupport_internallyConnected
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (first second : CanonicalAtom n)
    (hreach : canonicalDisagreementCut hleft hright first second = true)
    {firstFace : Nat} (hfirstFace : firstFace ∈ first.val) :
    InternallyConnected (faceLinkAdjacentB n)
      (twoBlockConnectedCarrierSupport
        hleft hright first second hreach) := by
  intro leftFace rightFace hleftFace hrightFace
  have hfirstLeft := twoBlockConnectedCarrierSupport_chain_from_first
    hleft hright first second hreach hfirstFace hleftFace
  have hfirstRight := twoBlockConnectedCarrierSupport_chain_from_first
    hleft hright first second hreach hfirstFace hrightFace
  exact ChainIn.trans
    (chainInReverse (faceLinkAdjacentB_symmetric n) hfirstLeft
      (twoBlockConnectedPathAtom_face_mem_support
        hleft hright first second hreach
        (by simpa [twoBlockConnectedPathAtoms] using
          (CWalk.start_mem_vertices
            (twoBlockConnectedPath hleft hright first second hreach).walk))
        hfirstFace))
    hfirstRight

theorem twoBlockConnectedCarrierSupport_first_mem
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (first second : CanonicalAtom n)
    (hreach : canonicalDisagreementCut hleft hright first second = true)
    {face : Nat} (hface : face ∈ first.val) :
    face ∈ twoBlockConnectedCarrierSupport
      hleft hright first second hreach :=
  twoBlockConnectedPathAtom_face_mem_support
    hleft hright first second hreach
    (by simpa [twoBlockConnectedPathAtoms] using
      (CWalk.start_mem_vertices
        (twoBlockConnectedPath hleft hright first second hreach).walk))
    hface

theorem twoBlockConnectedCarrierSupport_second_mem
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (first second : CanonicalAtom n)
    (hreach : canonicalDisagreementCut hleft hright first second = true)
    {face : Nat} (hface : face ∈ second.val) :
    face ∈ twoBlockConnectedCarrierSupport
      hleft hright first second hreach :=
  twoBlockConnectedPathAtom_face_mem_support
    hleft hright first second hreach
    (by simpa [twoBlockConnectedPathAtoms] using
      (CWalk.end_mem_vertices
        (twoBlockConnectedPath hleft hright first second hreach).walk))
    hface

/-! ## 3. Strict doubled-time specialization -/

/-- A connected disagreement branch between the literal strict lower and
doubled-time upper root blocks constructs a connected support satisfying the
linear temporal size floor. -/
def strictJointDoubledTimeConnectedBranch_size_floor
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    {left right : List (List Nat)}
    (hleft : left ∈
      canonicalCompatibleAmbientFamilies (centralAmbient radius))
    (hright : right ∈
      canonicalCompatibleAmbientFamilies (centralAmbient radius))
    (first second : CanonicalAtom (centralAmbient radius))
    (hfirst : first.val ∈ roots.map
      (strictJointDoubledTimeMixedLowerRoot radius base shift))
    (hsecond : second.val ∈ roots.map
      (strictJointDoubledTimeMixedUpperRoot radius base shift))
    (hreach : canonicalDisagreementCut hleft hright first second = true) :
    Σ' support : List Nat,
      (support ∈ cutoffOneFaceSupports (centralAmbient radius)) ×'
      InternallyConnected
        (faceLinkAdjacentB (centralAmbient radius)) support ×'
      (shift + shift + 6 ≤ support.length) := by
  obtain ⟨lowerRoot, hlowerRoot, hfirstEq⟩ :=
    decodeMapMember
      (strictJointDoubledTimeMixedLowerRoot radius base shift)
      roots first.val hfirst
  obtain ⟨upperRoot, hupperRoot, hsecondEq⟩ :=
    decodeMapMember
      (strictJointDoubledTimeMixedUpperRoot radius base shift)
      roots second.val hsecond
  let firstWitness := canonicalSurfacePolymers_allNonempty
    (centralAmbient radius) first.val first.property
  let secondWitness := canonicalSurfacePolymers_allNonempty
    (centralAmbient radius) second.val second.property
  let support := twoBlockConnectedCarrierSupport
    hleft hright first second hreach
  have hfirstFace : firstWitness.1 ∈
      strictJointDoubledTimeMixedLowerRoot
        radius base shift lowerRoot := by
    rw [hfirstEq]
    exact firstWitness.2
  have hsecondFace : secondWitness.1 ∈
      strictJointDoubledTimeMixedUpperRoot
        radius base shift upperRoot := by
    rw [hsecondEq]
    exact secondWitness.2
  have hfirstMem : firstWitness.1 ∈ support :=
    twoBlockConnectedCarrierSupport_first_mem
      hleft hright first second hreach firstWitness.2
  have hsecondMem : secondWitness.1 ∈ support :=
    twoBlockConnectedCarrierSupport_second_mem
      hleft hright first second hreach secondWitness.2
  have hsupport := twoBlockConnectedCarrierSupport_mem_faceSupports
    hleft hright first second hreach
  have hconnected := twoBlockConnectedCarrierSupport_internallyConnected
    hleft hright first second hreach firstWitness.2
  refine ⟨support, hsupport, hconnected, ?_⟩
  exact strictJointDoubledTimeConnectedSupport_size_floor
    hadmissible (hroots lowerRoot hlowerRoot)
    (hroots upperRoot hupperRoot)
    hfirstFace hsecondFace hsupport hconnected hfirstMem hsecondMem

#print axioms twoBlockConnectedCarrierSupport_internallyConnected
#print axioms twoBlockConnectedCarrierSupport_second_mem
#print axioms strictJointDoubledTimeConnectedBranch_size_floor

end YMGap.Continuum.Z4CanonicalTwoBlockConnectedCarrier
