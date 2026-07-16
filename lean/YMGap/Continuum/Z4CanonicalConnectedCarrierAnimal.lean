/-
# The colored carrier union is a genuine boundary-reaching animal

The carrier code stores two color supports, but their union is the physical
support visited by the loop-erased disagreement path.  Consecutive polymers
have an actual common face or shared-link contact.  Internal polymer chains
therefore splice into one chain on the union support.  This module makes that
connectivity constructive and packages the union as an ordinary Z4 lattice
animal, without assuming it is already a member of the canonical polymer
list.
-/

import YMGap.Continuum.Z4CanonicalConnectedPathCarrier
import YMGap.Continuum.Z4CanonicalPolymerAnimalBridge

namespace YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteDisagreementReverseRecovery
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalBoundarySwitchSummation
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalConnectedResiduePath
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalIncompatibilityWalk
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4PhysicalSurfaceComponents

/-! ## 1. Symmetry of finite internal chains -/

def chainInReverse {A : Type} {adj : A → A → Bool}
    {support : List A} (hsymm : SymmetricAdj adj) :
    {first last : A} → ChainIn adj support first last →
      first ∈ support → ChainIn adj support last first
  | _, _, .refl first, _ => .refl first
  | first, _, .step (b := middle) hedge hmiddle rest, hfirst =>
      ChainIn.trans (chainInReverse hsymm rest hmiddle)
        (.step (by simpa [hsymm first middle] using hedge)
          hfirst (.refl first))

/-! ## 2. The literal union support of the two path colors -/

def connectedCarrierSupport
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) : List Nat :=
  familyUnionSupport n
    (connectedPathLeftFamily hsmall entry ++
      connectedPathRightFamily hsmall entry)

def familyContainsFaceWitness (face : Nat) :
    ∀ family : List (List Nat), familyContainsFaceB face family = true →
      Σ' polymer : List Nat, (polymer ∈ family) ×' (face ∈ polymer)
  | [], h => by cases h
  | polymer :: rest, h => by
      by_cases hface : face ∈ polymer
      · exact ⟨polymer, List.mem_cons_self, hface⟩
      · have hrest : familyContainsFaceB face rest = true := by
          simpa [familyContainsFaceB, hface] using h
        obtain ⟨found, hfound, hfoundFace⟩ :=
          familyContainsFaceWitness face rest hrest
        exact ⟨found, List.mem_cons_of_mem polymer hfound, hfoundFace⟩

theorem connectedPathAtom_mem_coloredFamily
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall)
    {atom : CanonicalAtom n} (hatom : atom ∈ connectedPathAtoms hsmall entry) :
    atom.val ∈ connectedPathLeftFamily hsmall entry ∨
      atom.val ∈ connectedPathRightFamily hsmall entry := by
  have htest : connectedPathTest hsmall entry atom.val = true := by
    unfold connectedPathTest connectedPathValues
    apply (memberB_eq_true_iff _ _).2
    exact List.mem_map.mpr ⟨atom, hatom, rfl⟩
  rcases connectedPathAtoms_exclusive hsmall entry atom hatom with
      hleft | hright
  · apply Or.inl
    unfold connectedPathLeftFamily
    apply List.mem_filter.mpr
    exact ⟨(canonicalFamilyAtom_mem_iff
      (sourceLeftCompatible entry.val) atom).1
        ((memberB_eq_true_iff _ _).1 hleft.1), htest⟩
  · apply Or.inr
    unfold connectedPathRightFamily
    apply List.mem_filter.mpr
    exact ⟨(canonicalFamilyAtom_mem_iff
      (sourceRightCompatible hsmall entry.val) atom).1
        ((memberB_eq_true_iff _ _).1 hright.2), htest⟩

theorem connectedPathAtom_face_mem_support
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall)
    {atom : CanonicalAtom n} (hatom : atom ∈ connectedPathAtoms hsmall entry)
    {face : Nat} (hface : face ∈ atom.val) :
    face ∈ connectedCarrierSupport hsmall entry := by
  unfold connectedCarrierSupport
  rw [mem_familyUnionSupport_iff]
  constructor
  · exact mem_of_mem_sublists (physicalFaceEdges n) atom.val
      (canonicalSurfacePolymer_mem_faceSupports atom.property) face hface
  · refine ⟨atom.val, ?_, hface⟩
    rcases connectedPathAtom_mem_coloredFamily hsmall entry hatom with
      hleft | hright
    · exact List.mem_append_left _ hleft
    · exact List.mem_append_right _ hright

theorem connectedColoredFamily_pathTest
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) {polymer : List Nat}
    (hpolymer : polymer ∈ connectedPathLeftFamily hsmall entry ++
      connectedPathRightFamily hsmall entry) :
    connectedPathTest hsmall entry polymer = true := by
  rcases List.mem_append.mp hpolymer with hleft | hright
  · exact (List.mem_filter.mp hleft).2
  · exact (List.mem_filter.mp hright).2

def connectedCarrierSupport_face_witness
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall)
    {face : Nat} (hface : face ∈ connectedCarrierSupport hsmall entry) :
    Σ' atom : CanonicalAtom n,
      (atom ∈ connectedPathAtoms hsmall entry) ×' (face ∈ atom.val) := by
  have hcontains : familyContainsFaceB face
      (connectedPathLeftFamily hsmall entry ++
        connectedPathRightFamily hsmall entry) = true := by
    exact (List.mem_filter.mp hface).2
  obtain ⟨polymer, hpolymer, hfacePolymer⟩ :=
    familyContainsFaceWitness face _ hcontains
  have hpathTest : connectedPathTest hsmall entry polymer = true :=
    connectedColoredFamily_pathTest hsmall entry hpolymer
  have hpathValue : polymer ∈ connectedPathValues hsmall entry :=
    (memberB_eq_true_iff _ _).1 hpathTest
  obtain ⟨atom, hatom, hatomValue⟩ :=
    decodeMapMember Subtype.val (connectedPathAtoms hsmall entry)
      polymer hpathValue
  refine ⟨atom, ?_, ?_⟩
  · simpa [connectedPathValues] using hatom
  · rw [hatomValue]
    exact hfacePolymer

theorem connectedCarrierSupport_mem_faceSupports
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) :
    connectedCarrierSupport hsmall entry ∈ cutoffOneFaceSupports n :=
  familyUnionSupport_mem_cutoffOneFaceSupports n _

/-! ## 3. Splicing the polymer chains along a disagreement walk -/

def allFalseWitness {A : Type} (test : A → Bool) :
    ∀ xs : List A, xs.all test = false →
      Σ' item : A, (item ∈ xs) ×' (test item = false)
  | [], h => by cases h
  | head :: tail, h => by
      cases hhead : test head with
      | false => exact ⟨head, List.mem_cons_self, hhead⟩
      | true =>
          have htail : tail.all test = false := by
            change (test head && tail.all test) = false at h
            rw [hhead] at h
            exact h
          let witness := allFalseWitness test tail htail
          exact ⟨witness.1,
            List.mem_cons_of_mem head witness.2.1, witness.2.2⟩

inductive FaceContact (n left right : Nat) : Type
  | same : left = right → FaceContact n left right
  | adjacent : faceLinkAdjacentB n left right = true →
      FaceContact n left right

def canonicalPolymerIncompatibleContact
    {n : Nat} {left right : List Nat}
    (hincompatible : canonicalPolymerCompatibleB n left right = false) :
    Σ' leftFace : Nat, (leftFace ∈ left) ×'
      Σ' rightFace : Nat, (rightFace ∈ right) ×'
        FaceContact n leftFace rightFace := by
  unfold canonicalPolymerCompatibleB at hincompatible
  obtain ⟨leftFace, hleftFace, hrightAll⟩ :=
    allFalseWitness
      (fun leftFace => right.all (fun rightFace =>
        !(decide (leftFace = rightFace)) &&
          !(faceLinkAdjacentB n leftFace rightFace)))
      left hincompatible
  obtain ⟨rightFace, hrightFace, hpair⟩ :=
    allFalseWitness
      (fun rightFace =>
        !(decide (leftFace = rightFace)) &&
          !(faceLinkAdjacentB n leftFace rightFace))
      right hrightAll
  refine ⟨leftFace, hleftFace, rightFace, hrightFace, ?_⟩
  cases heq : decide (leftFace = rightFace) with
  | true => exact .same (of_decide_eq_true heq)
  | false =>
      cases hadj : faceLinkAdjacentB n leftFace rightFace with
      | true => exact .adjacent hadj
      | false =>
          simp only [heq, Bool.not_false, hadj, Bool.true_and] at hpair
          cases hpair

def disagreementCWalk_faceChainFromStart
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root) :
    ∀ {first last : CanonicalAtom n}
      (walk : CWalk (sourceDisagreementEdge hsmall pair) first last)
      (support : List Nat),
      (∀ atom, atom ∈ walk.vertices →
        ∀ face, face ∈ atom.val → face ∈ support) →
      ∀ {target : CanonicalAtom n}, target ∈ walk.vertices →
        ∀ {start finish : Nat}, start ∈ first.val → finish ∈ target.val →
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
          canonicalDisagreementEdge_incompatible
            (sourceLeftCompatible pair)
            (sourceRightCompatible hsmall pair)
            (by simpa [sourceDisagreementEdge] using hedge)
        obtain ⟨leftContact, hleftContact, rightContact,
            hrightContact, hcontact⟩ :=
          canonicalPolymerIncompatibleContact hincompatible
        have hhead : ChainIn (faceLinkAdjacentB n) support
            start leftContact :=
          ChainIn.mono
            (fun face hface => hcover first List.mem_cons_self face hface)
            ((canonicalSurfacePolymers_allConnected n) first first.property
              start leftContact hstart hleftContact)
        have htail : ChainIn (faceLinkAdjacentB n) support
            rightContact finish :=
          disagreementCWalk_faceChainFromStart hsmall pair rest support
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
                (List.mem_cons_of_mem first (CWalk.start_mem_vertices rest))
                rightContact hrightContact)
              htail)

def connectedCarrierSupport_chain_from_root
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall)
    {rootFace face : Nat} (hrootFace : rootFace ∈ root)
    (hface : face ∈ connectedCarrierSupport hsmall entry) :
    ChainIn (faceLinkAdjacentB n) (connectedCarrierSupport hsmall entry)
      rootFace face := by
  obtain ⟨target, htarget, hfaceTarget⟩ :=
    connectedCarrierSupport_face_witness hsmall entry hface
  exact disagreementCWalk_faceChainFromStart hsmall entry.val
    (connectedSourcePath hsmall entry).walk
    (connectedCarrierSupport hsmall entry)
    (fun atom hatom found hfound =>
      connectedPathAtom_face_mem_support hsmall entry hatom hfound)
    htarget hrootFace hfaceTarget

def connectedCarrierSupport_internallyConnected
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall)
    {rootFace : Nat} (hrootFace : rootFace ∈ root) :
    InternallyConnected (faceLinkAdjacentB n)
      (connectedCarrierSupport hsmall entry) := by
  intro first last hfirst hlast
  have hrootFirst := connectedCarrierSupport_chain_from_root
    hsmall entry hrootFace hfirst
  have hrootLast := connectedCarrierSupport_chain_from_root
    hsmall entry hrootFace hlast
  exact ChainIn.trans
    (chainInReverse (faceLinkAdjacentB_symmetric n) hrootFirst
      (connectedPathAtom_face_mem_support hsmall entry
        (by simpa [connectedPathAtoms] using
          CWalk.start_mem_vertices (connectedSourcePath hsmall entry).walk)
        hrootFace))
    hrootLast

/-! ## 4. A uniform animal certificate and the boundary size floor -/

theorem connectedCarrierSupport_root_mem
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall)
    {rootFace : Nat} (hrootFace : rootFace ∈ root) :
    rootFace ∈ connectedCarrierSupport hsmall entry :=
  connectedPathAtom_face_mem_support hsmall entry
    (by simpa [connectedPathAtoms] using
      CWalk.start_mem_vertices (connectedSourcePath hsmall entry).walk)
    hrootFace

def connectedFaceSupportAnimalAt
    {n rootFace : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hconnected : InternallyConnected (faceLinkAdjacentB n) support)
    (hroot : rootFace ∈ support) :
    IsClusterThroughIn z4Chain (boxPlaquetteAt n rootFace)
      support.length (geometricPolymer n support) := by
  unfold IsClusterThroughIn IsClusterThrough
  refine ⟨?_, ?_, geometricPolymer_nodup hsupport, ?_⟩
  · unfold Polymer.size geometricPolymer
    simp only [List.length_map]
  · unfold geometricPolymer
    exact List.mem_map.mpr ⟨rootFace, hroot, rfl⟩
  · exact ⟨numericalConnectedToGeometric hconnected⟩

theorem connectedFaceSupport_overcountedAt
    {n rootFace : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hconnected : InternallyConnected (faceLinkAdjacentB n) support)
    (hroot : rootFace ∈ support) :
    ∃ animal,
      animal ∈ enumPolys z4Chain (boxPlaquetteAt n rootFace)
          support.length ∧
        sameSupport (geometricPolymer n support) animal := by
  exact (z4ClusterCountBound_animal (boxPlaquetteAt n rootFace)).2
    support.length (geometricPolymer n support)
    (connectedFaceSupportAnimalAt hsupport hconnected hroot)

theorem connectedFaceSupport_linf_size_floor
    {n rootFace distance : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n)
    (hconnected : InternallyConnected (faceLinkAdjacentB n) support)
    (hroot : rootFace ∈ support)
    {q : Z4Plaq} (hq : q ∈ geometricPolymer n support)
    (hsep : distance ≤ linfDist (boxPlaquetteAt n rootFace) q) :
    distance + 1 ≤ support.length := by
  obtain ⟨animal, hanimal, hsame⟩ :=
    connectedFaceSupport_overcountedAt hsupport hconnected hroot
  have hqAnimal : q ∈ animal := hsame.1 q hq
  have hfloor := enum_linf_reach_floor
    (boxPlaquetteAt n rootFace) support.length animal hanimal
    q hqAnimal distance hsep
  have hgeomNodup : (geometricPolymer n support).Nodup :=
    geometricPolymer_nodup hsupport
  have hanimalNodup : animal.Nodup :=
    enumPoly_nodup z4Chain (boxPlaquetteAt n rootFace)
      support.length hanimal
  have hlength : animal.length = support.length := by
    have hsameLength := sameSupport_length_eq_of_nodup
      hsame hgeomNodup hanimalNodup
    simpa only [geometricPolymer, List.length_map] using hsameLength.symm
  rw [hlength] at hfloor
  exact hfloor

theorem connectedCarrierSupport_boundary_floor
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall)
    {start inner distance : Nat}
    (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    distance + 2 ≤ (connectedCarrierSupport hsmall entry).length := by
  have houtside := sourceOutsideAtom_outside
    hsmall entry.val entry.property
  obtain ⟨outsidePlaquette, houtsidePlaquette, houtsideSmall⟩ :=
    polymerInsideBoxB_false_witness houtside
  obtain ⟨finish, hfinish, hfinishEq⟩ :=
    List.mem_map.mp houtsidePlaquette
  have hfinishSupport : finish ∈ connectedCarrierSupport hsmall entry :=
    connectedPathAtom_face_mem_support hsmall entry
      (by simpa [connectedPathAtoms] using
        CWalk.end_mem_vertices (connectedSourcePath hsmall entry).walk)
      hfinish
  have hfinishOutside :
      boxPlaquetteAt n finish ∉ boxPlaquettes small := by
    rw [hfinishEq]
    exact houtsideSmall
  have houtSmall : outsideBoxB small (boxPlaquetteAt n finish) = true :=
    (outsideBoxB_true_iff_not_mem small (boxPlaquetteAt n finish)).2
      hfinishOutside
  have houtExpanded :
      outsideBoxB (inner + distance) (boxPlaquetteAt n finish) = true := by
    rw [hbox]
    exact houtSmall
  have hsep := outside_expanded_box_linf_floor hstartInner houtExpanded
  have hfloor := connectedFaceSupport_linf_size_floor
    (connectedCarrierSupport_mem_faceSupports hsmall entry)
    (connectedCarrierSupport_internallyConnected hsmall entry hstart)
    (connectedCarrierSupport_root_mem hsmall entry hstart)
    (List.mem_map.mpr ⟨finish, hfinishSupport, rfl⟩)
    hsep
  omega

theorem connectedCarrierSupport_mem_canonicalSurfacePolymers
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall)
    {rootFace : Nat} (hrootFace : rootFace ∈ root) :
    connectedCarrierSupport hsmall entry ∈ canonicalSurfacePolymers n :=
  connectedFaceSupport_mem_canonicalSurfacePolymers
    (connectedCarrierSupport_mem_faceSupports hsmall entry)
    ⟨rootFace, connectedCarrierSupport_root_mem hsmall entry hrootFace⟩
    (connectedCarrierSupport_internallyConnected hsmall entry hrootFace)

end YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal.chainInReverse
#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal.allFalseWitness
#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal.canonicalPolymerIncompatibleContact
#print axioms YMGap.Continuum.Z4CanonicalPolymerUniverse.canonicalSurfacePolymers_allConnected
#print axioms YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery.canonicalDisagreementEdge_incompatible
#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal.connectedCarrierSupport_face_witness
#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal.disagreementCWalk_faceChainFromStart
#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal.connectedCarrierSupport_internallyConnected
#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal.connectedFaceSupportAnimalAt
#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal.connectedCarrierSupport_boundary_floor
#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal.connectedCarrierSupport_mem_canonicalSurfacePolymers
