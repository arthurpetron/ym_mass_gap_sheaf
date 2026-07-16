/-
# The slab connected carrier is a rooted face animal

The two colored path families have a literal union support.  This file proves
that support internally connected, contains every face of the deterministically
selected marked root, and reaches a plaquette omitted by the corrected slab.
It therefore supplies a reusable L-infinity size floor for the carrier.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedPathCarrier
import YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierAnimal

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedPathCarrier
open YMGap.Continuum.Z4HalfTimeReflectionTopBoundaryTail
open YMGap.Continuum.Z4PhysicalSurfaceComponents

/-! ## 1. Literal union support and path coverage -/

def slabConnectedCarrierSupport
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) : List Nat :=
  familyUnionSupport (extent + 1)
    (slabConnectedPathLeftFamily defaultRoot entry ++
      slabConnectedPathRightFamily defaultRoot entry)

theorem slabConnectedPathAtom_mem_coloredFamily
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (entry : SlabConnectedSourceEntry extent roots predicate)
    {atom : CanonicalAtom (extent + 1)}
    (hatom : atom ∈ slabConnectedPathAtoms defaultRoot entry) :
    atom.val ∈ slabConnectedPathLeftFamily defaultRoot entry ∨
      atom.val ∈ slabConnectedPathRightFamily defaultRoot entry := by
  have htest : slabConnectedPathTest defaultRoot entry atom.val = true := by
    unfold slabConnectedPathTest slabConnectedPathValues
    apply (memberB_eq_true_iff _ _).2
    exact List.mem_map.mpr ⟨atom, hatom, rfl⟩
  rcases slabConnectedPathAtoms_exclusive defaultRoot hrootsSupported
      entry atom hatom with hleft | hright
  · apply Or.inl
    unfold slabConnectedPathLeftFamily
    apply List.mem_filter.mpr
    exact ⟨(canonicalFamilyAtom_mem_iff
      (slabCylinderSourceLeftCompatible entry.val) atom).1
        ((memberB_eq_true_iff _ _).1 hleft.1), htest⟩
  · apply Or.inr
    unfold slabConnectedPathRightFamily
    apply List.mem_filter.mpr
    exact ⟨(canonicalFamilyAtom_mem_iff
      (slabCylinderSourceRightCompatible entry.val) atom).1
        ((memberB_eq_true_iff _ _).1 hright.2), htest⟩

theorem slabConnectedPathAtom_face_mem_support
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (entry : SlabConnectedSourceEntry extent roots predicate)
    {atom : CanonicalAtom (extent + 1)}
    (hatom : atom ∈ slabConnectedPathAtoms defaultRoot entry)
    {face : Nat} (hface : face ∈ atom.val) :
    face ∈ slabConnectedCarrierSupport defaultRoot entry := by
  unfold slabConnectedCarrierSupport
  rw [mem_familyUnionSupport_iff]
  constructor
  · exact mem_of_mem_sublists (physicalFaceEdges (extent + 1)) atom.val
      (canonicalSurfacePolymer_mem_faceSupports atom.property) face hface
  · refine ⟨atom.val, ?_, hface⟩
    rcases slabConnectedPathAtom_mem_coloredFamily
      defaultRoot hrootsSupported entry hatom with hleft | hright
    · exact List.mem_append_left _ hleft
    · exact List.mem_append_right _ hright

theorem slabConnectedColoredFamily_pathTest
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate)
    {polymer : List Nat}
    (hpolymer : polymer ∈ slabConnectedPathLeftFamily defaultRoot entry ++
      slabConnectedPathRightFamily defaultRoot entry) :
    slabConnectedPathTest defaultRoot entry polymer = true := by
  rcases List.mem_append.mp hpolymer with hleft | hright
  · exact (List.mem_filter.mp hleft).2
  · exact (List.mem_filter.mp hright).2

def slabConnectedCarrierSupport_face_witness
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate)
    {face : Nat} (hface : face ∈
      slabConnectedCarrierSupport defaultRoot entry) :
    Σ' atom : CanonicalAtom (extent + 1),
      (atom ∈ slabConnectedPathAtoms defaultRoot entry) ×'
        (face ∈ atom.val) := by
  have hcontains : familyContainsFaceB face
      (slabConnectedPathLeftFamily defaultRoot entry ++
        slabConnectedPathRightFamily defaultRoot entry) = true :=
    (List.mem_filter.mp hface).2
  obtain ⟨polymer, hpolymer, hfacePolymer⟩ :=
    familyContainsFaceWitness face _ hcontains
  have hpathTest : slabConnectedPathTest defaultRoot entry polymer = true :=
    slabConnectedColoredFamily_pathTest defaultRoot entry hpolymer
  have hpathValue : polymer ∈ slabConnectedPathValues defaultRoot entry :=
    (memberB_eq_true_iff _ _).1 hpathTest
  obtain ⟨atom, hatom, hatomValue⟩ :=
    decodeMapMember Subtype.val (slabConnectedPathAtoms defaultRoot entry)
      polymer hpathValue
  refine ⟨atom, ?_, ?_⟩
  · simpa [slabConnectedPathValues] using hatom
  · rw [hatomValue]
    exact hfacePolymer

theorem slabConnectedCarrierSupport_mem_faceSupports
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    slabConnectedCarrierSupport defaultRoot entry ∈
      cutoffOneFaceSupports (extent + 1) :=
  familyUnionSupport_mem_cutoffOneFaceSupports (extent + 1) _

/-! ## 2. Splicing polymer chains along the disagreement walk -/

def slabDisagreementCWalk_faceChainFromStart
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (pair : SlabCylinderSourcePair extent roots predicate) :
    ∀ {first last : CanonicalAtom (extent + 1)}
      (walk : CWalk (slabSourceDisagreementEdge pair) first last)
      (support : List Nat),
      (∀ atom, atom ∈ walk.vertices →
        ∀ face, face ∈ atom.val → face ∈ support) →
      ∀ {target : CanonicalAtom (extent + 1)}, target ∈ walk.vertices →
        ∀ {start finish : Nat}, start ∈ first.val →
          finish ∈ target.val →
          ChainIn (faceLinkAdjacentB (extent + 1)) support start finish
  | _, _, .single atom, support, hcover, target, htarget,
      start, finish, hstart, hfinish => by
      have htargetEq : target = atom := List.mem_singleton.mp htarget
      subst target
      exact ChainIn.mono
        (fun face hface => hcover atom List.mem_cons_self face hface)
        ((canonicalSurfacePolymers_allConnected (extent + 1))
          atom atom.property start finish hstart hfinish)
  | first, last, .cons (middle := middle) hedge rest, support, hcover,
      target, htarget, start, finish, hstart, hfinish => by
      cases heqTarget : decide (target = first) with
      | true =>
        have htargetFirst : target = first := of_decide_eq_true heqTarget
        subst target
        exact ChainIn.mono
          (fun face hface => hcover first List.mem_cons_self face hface)
          ((canonicalSurfacePolymers_allConnected (extent + 1))
            first first.property start finish hstart hfinish)
      | false =>
        have htargetFirst : target ≠ first := of_decide_eq_false heqTarget
        have htargetRest : target ∈ rest.vertices :=
          (List.mem_cons.mp htarget).resolve_left htargetFirst
        have hincompatible : canonicalPolymerCompatibleB (extent + 1)
            first.val middle.val = false :=
          canonicalDisagreementEdge_incompatible
            (slabCylinderSourceLeftCompatible pair)
            (slabCylinderSourceRightCompatible pair)
            (by simpa [slabSourceDisagreementEdge] using hedge)
        obtain ⟨leftContact, hleftContact, rightContact,
            hrightContact, hcontact⟩ :=
          canonicalPolymerIncompatibleContact hincompatible
        have hhead : ChainIn (faceLinkAdjacentB (extent + 1)) support
            start leftContact :=
          ChainIn.mono
            (fun face hface => hcover first List.mem_cons_self face hface)
            ((canonicalSurfacePolymers_allConnected (extent + 1))
              first first.property start leftContact hstart hleftContact)
        have htail : ChainIn (faceLinkAdjacentB (extent + 1)) support
            rightContact finish :=
          slabDisagreementCWalk_faceChainFromStart pair rest support
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

def slabConnectedCarrierSupport_chain_from_root
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (entry : SlabConnectedSourceEntry extent roots predicate)
    {rootFace face : Nat}
    (hrootFace : rootFace ∈ (slabSourceRootAtom defaultRoot entry.val).val)
    (hface : face ∈ slabConnectedCarrierSupport defaultRoot entry) :
    ChainIn (faceLinkAdjacentB (extent + 1))
      (slabConnectedCarrierSupport defaultRoot entry) rootFace face := by
  obtain ⟨target, htarget, hfaceTarget⟩ :=
    slabConnectedCarrierSupport_face_witness defaultRoot entry hface
  exact slabDisagreementCWalk_faceChainFromStart entry.val
    (slabConnectedSourcePath defaultRoot entry).walk
    (slabConnectedCarrierSupport defaultRoot entry)
    (fun atom hatom found hfound =>
      slabConnectedPathAtom_face_mem_support
        defaultRoot hrootsSupported entry hatom hfound)
    htarget hrootFace hfaceTarget

def slabConnectedCarrierSupport_internallyConnected
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (entry : SlabConnectedSourceEntry extent roots predicate)
    {rootFace : Nat}
    (hrootFace : rootFace ∈ (slabSourceRootAtom defaultRoot entry.val).val) :
    InternallyConnected (faceLinkAdjacentB (extent + 1))
      (slabConnectedCarrierSupport defaultRoot entry) := by
  intro first last hfirst hlast
  have hrootFirst := slabConnectedCarrierSupport_chain_from_root
    defaultRoot hrootsSupported entry hrootFace hfirst
  have hrootLast := slabConnectedCarrierSupport_chain_from_root
    defaultRoot hrootsSupported entry hrootFace hlast
  have hstartAtom : slabSourceRootAtom defaultRoot entry.val ∈
      slabConnectedPathAtoms defaultRoot entry := by
    unfold slabConnectedPathAtoms
    exact CWalk.start_mem_vertices
      (slabConnectedSourcePath defaultRoot entry).walk
  exact ChainIn.trans
    (chainInReverse (faceLinkAdjacentB_symmetric (extent + 1)) hrootFirst
      (slabConnectedPathAtom_face_mem_support
        defaultRoot hrootsSupported entry hstartAtom hrootFace))
    hrootLast

theorem slabConnectedCarrierSupport_root_mem
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (entry : SlabConnectedSourceEntry extent roots predicate)
    {rootFace : Nat}
    (hrootFace : rootFace ∈ (slabSourceRootAtom defaultRoot entry.val).val) :
    rootFace ∈ slabConnectedCarrierSupport defaultRoot entry := by
  have hstartAtom : slabSourceRootAtom defaultRoot entry.val ∈
      slabConnectedPathAtoms defaultRoot entry := by
    unfold slabConnectedPathAtoms
    exact CWalk.start_mem_vertices
      (slabConnectedSourcePath defaultRoot entry).walk
  exact slabConnectedPathAtom_face_mem_support
    defaultRoot hrootsSupported entry hstartAtom hrootFace

/-! ## 3. The support reaches the literal omitted slab face set -/

theorem slabConnectedCarrierSupport_hits_complement
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    ∃ q : Z4Plaq,
      q ∈ geometricPolymer (extent + 1)
          (slabConnectedCarrierSupport defaultRoot entry) ∧
        q ∉ boundaryCompleteSlabPlaquettes extent := by
  have hhit := slabSourceOutsideAtom_hits_complement
    defaultRoot entry.val entry.property
  unfold canonicalPolymerHitsSlabComplementB at hhit
  obtain ⟨q, hq, hqOutside⟩ := List.any_eq_true.mp hhit
  obtain ⟨face, hface, hqEq⟩ := List.mem_map.mp hq
  subst q
  have hendAtom : slabSourceOutsideAtom defaultRoot entry.val ∈
      slabConnectedPathAtoms defaultRoot entry := by
    unfold slabConnectedPathAtoms
    exact CWalk.end_mem_vertices
      (slabConnectedSourcePath defaultRoot entry).walk
  have hfaceSupport : face ∈
      slabConnectedCarrierSupport defaultRoot entry :=
    slabConnectedPathAtom_face_mem_support
      defaultRoot hrootsSupported entry hendAtom hface
  refine ⟨boxPlaquetteAt (extent + 1) face, ?_, ?_⟩
  · unfold geometricPolymer
    exact List.mem_map.mpr ⟨face, hfaceSupport, rfl⟩
  · exact of_decide_eq_true hqOutside

theorem slabConnectedCarrierSupport_linf_size_floor
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (entry : SlabConnectedSourceEntry extent roots predicate)
    {rootFace distance : Nat}
    (hrootFace : rootFace ∈ (slabSourceRootAtom defaultRoot entry.val).val)
    (hseparation : ∀ q : Z4Plaq,
      q ∈ boxPlaquettes (extent + 1) →
      q ∉ boundaryCompleteSlabPlaquettes extent →
      distance ≤ linfDist (boxPlaquetteAt (extent + 1) rootFace) q) :
    distance + 1 ≤
      (slabConnectedCarrierSupport defaultRoot entry).length := by
  obtain ⟨q, hqSupport, hqOutside⟩ :=
    slabConnectedCarrierSupport_hits_complement
      defaultRoot hrootsSupported entry
  have hqBox := geometricPolymer_subset_box
    (familyUnionSupport_mem_cutoffOneFaceSupports (extent + 1) _) q
    hqSupport
  exact connectedFaceSupport_linf_size_floor
    (slabConnectedCarrierSupport_mem_faceSupports defaultRoot entry)
    (slabConnectedCarrierSupport_internallyConnected
      defaultRoot hrootsSupported entry hrootFace)
    (slabConnectedCarrierSupport_root_mem
      defaultRoot hrootsSupported entry hrootFace)
    hqSupport (hseparation q hqBox hqOutside)

theorem slabConnectedCarrierSupport_mem_canonicalSurfacePolymers
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (entry : SlabConnectedSourceEntry extent roots predicate)
    {rootFace : Nat}
    (hrootFace : rootFace ∈ (slabSourceRootAtom defaultRoot entry.val).val) :
    slabConnectedCarrierSupport defaultRoot entry ∈
      canonicalSurfacePolymers (extent + 1) :=
  connectedFaceSupport_mem_canonicalSurfacePolymers
    (slabConnectedCarrierSupport_mem_faceSupports defaultRoot entry)
    ⟨rootFace, slabConnectedCarrierSupport_root_mem
      defaultRoot hrootsSupported entry hrootFace⟩
    (slabConnectedCarrierSupport_internallyConnected
      defaultRoot hrootsSupported entry hrootFace)

#print axioms slabConnectedPathAtom_face_mem_support
#print axioms slabDisagreementCWalk_faceChainFromStart
#print axioms slabConnectedCarrierSupport_internallyConnected
#print axioms slabConnectedCarrierSupport_hits_complement
#print axioms slabConnectedCarrierSupport_linf_size_floor
#print axioms slabConnectedCarrierSupport_mem_canonicalSurfacePolymers

end YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierAnimal
