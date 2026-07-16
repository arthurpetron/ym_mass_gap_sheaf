/-
# Connected-versus-switchable dichotomy for a canonical boundary pair

A boundary family contains a literal polymer leaving the smaller box.  Given a
second compatible family, this module forms the finite side-tagged
incompatibility graph of the pair and decides whether a chosen local polymer
reaches that exiting polymer.

The true branch carries an extracted canonical path and therefore the geometric
path-cost floor.  The false branch is retained as explicit Boolean evidence;
it is the domain on which the next disagreement-component switch acts.
-/

import YMGap.Continuum.Z4CanonicalBipartitePath
import YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance

namespace YMGap.Continuum.Z4CanonicalBoundaryPairDichotomy

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteBoxExhaustion

/-! ## 1. Side-tagged vertices of a pair of compatible families -/

def familyCanonicalAtoms (n : Nat) :
    ∀ (family : List (List Nat)),
      (∀ polymer, polymer ∈ family →
        polymer ∈ canonicalSurfacePolymers n) →
      List (CanonicalAtom n)
  | [], _ => []
  | polymer :: rest, hmembers =>
      (⟨polymer, hmembers polymer List.mem_cons_self⟩ : CanonicalAtom n) ::
        familyCanonicalAtoms n rest
          (fun item hitem =>
            hmembers item (List.mem_cons_of_mem polymer hitem))

def pairBipartiteVertices (n : Nat)
    (left right : List (List Nat))
    (hleft : ∀ polymer, polymer ∈ left →
      polymer ∈ canonicalSurfacePolymers n)
    (hright : ∀ polymer, polymer ∈ right →
      polymer ∈ canonicalSurfacePolymers n) :
    List (BipartiteVertex n) :=
  (familyCanonicalAtoms n left hleft).map BipartiteVertex.left ++
    (familyCanonicalAtoms n right hright).map BipartiteVertex.right

def compatiblePairVertices {n : Nat}
    {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n) :
    List (BipartiteVertex n) :=
  pairBipartiteVertices n left right
    (fun _polymer hpolymer =>
      compatibleAmbientFamily_member_ambient hleft hpolymer)
    (fun _polymer hpolymer =>
      compatibleAmbientFamily_member_ambient hright hpolymer)

def leftCanonicalAtomOfMember {n : Nat}
    {left : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    {polymer : List Nat} (hpolymer : polymer ∈ left) :
    CanonicalAtom n :=
  ⟨polymer, compatibleAmbientFamily_member_ambient hleft hpolymer⟩

theorem familyCanonicalAtoms_values (n : Nat) :
    ∀ (family : List (List Nat))
      (hmembers : ∀ polymer, polymer ∈ family →
        polymer ∈ canonicalSurfacePolymers n),
      (familyCanonicalAtoms n family hmembers).map Subtype.val = family
  | [], _ => rfl
  | polymer :: rest, hmembers => by
      simp only [familyCanonicalAtoms, List.map_cons]
      rw [familyCanonicalAtoms_values n rest]

theorem familyCanonicalAtom_mem_iff
    {n : Nat} {family : List (List Nat)}
    (hmembers : ∀ polymer, polymer ∈ family →
      polymer ∈ canonicalSurfacePolymers n)
    (atom : CanonicalAtom n) :
    atom ∈ familyCanonicalAtoms n family hmembers ↔
      atom.val ∈ family := by
  constructor
  · intro hatom
    have hvalue : atom.val ∈
        (familyCanonicalAtoms n family hmembers).map Subtype.val :=
      List.mem_map.mpr ⟨atom, hatom, rfl⟩
    rw [familyCanonicalAtoms_values n family hmembers] at hvalue
    exact hvalue
  · intro hvalue
    have hmapped : atom.val ∈
        (familyCanonicalAtoms n family hmembers).map Subtype.val := by
      rw [familyCanonicalAtoms_values n family hmembers]
      exact hvalue
    obtain ⟨found, hfound, hfoundValue⟩ := List.mem_map.mp hmapped
    have hsame : found = atom := Subtype.ext hfoundValue
    simpa [hsame] using hfound

/-! ## 2. A boundary pair and its constructive reachability split -/

/-- The finite Boolean test for whether the root component reaches *any*
polymer of the boundary replica that leaves the smaller box.  Testing all
outside polymers is essential: avoiding only one chosen witness would not
ensure that the switched opposite replica remains embedded. -/
def boundaryOutsideReachB {target : Nat} (small : Nat)
    (vertices : List (BipartiteVertex target))
    (root : CanonicalAtom target)
    (boundaryAtoms : List (CanonicalAtom target)) : Bool :=
  boundaryAtoms.any (fun outside =>
    (!(polymerInsideBoxB small target outside.val)) &&
      warshall (bipartiteIncompatibilityB target) vertices
        (.left root) (.left outside))

/-- Constructive exhaustive dichotomy: either the local root reaches a
literal outside polymer, or it reaches no outside polymer in the boundary
replica.  This is proved by evaluating the finite Boolean test, not by an
excluded-middle or choice principle. -/
theorem boundaryPairReachDichotomy
    {small target : Nat}
    {boundaryFamily otherFamily : List (List Nat)}
    (hboundary : boundaryFamily ∈
      boundaryTargetFamilies small target)
    (hother : otherFamily ∈ canonicalCompatibleAmbientFamilies target)
    {root : List Nat} (hroot : root ∈ boundaryFamily) :
    (∃ outside : CanonicalAtom target,
      outside.val ∈ boundaryFamily ∧
        polymerInsideBoxB small target outside.val = false ∧
          warshall (bipartiteIncompatibilityB target)
            (compatiblePairVertices
              (List.mem_filter.mp hboundary).1 hother)
            (.left (leftCanonicalAtomOfMember
              (List.mem_filter.mp hboundary).1 hroot))
            (.left outside) = true) ∨
      (∀ outside : CanonicalAtom target,
        outside.val ∈ boundaryFamily →
          polymerInsideBoxB small target outside.val = false →
            warshall (bipartiteIncompatibilityB target)
              (compatiblePairVertices
                (List.mem_filter.mp hboundary).1 hother)
              (.left (leftCanonicalAtomOfMember
                (List.mem_filter.mp hboundary).1 hroot))
              (.left outside) = false) := by
  let hboundaryCompatible := (List.mem_filter.mp hboundary).1
  let hmembers : ∀ polymer : List Nat, polymer ∈ boundaryFamily →
      polymer ∈ canonicalSurfacePolymers target :=
    fun polymer hpolymer =>
      compatibleAmbientFamily_member_ambient
        hboundaryCompatible hpolymer
  let atoms := familyCanonicalAtoms target boundaryFamily hmembers
  let vertices := compatiblePairVertices hboundaryCompatible hother
  let rootAtom := leftCanonicalAtomOfMember hboundaryCompatible hroot
  cases hdecision : boundaryOutsideReachB small vertices rootAtom atoms with
  | true =>
      left
      obtain ⟨outside, houtsideAtoms, hterm⟩ :=
        List.any_eq_true.mp hdecision
      have hparts := (Bool.and_eq_true _ _).mp hterm
      have houtside : polymerInsideBoxB small target outside.val = false := by
        cases hinside : polymerInsideBoxB small target outside.val <;>
          simp_all
      exact ⟨outside,
        (familyCanonicalAtom_mem_iff hmembers outside).1 houtsideAtoms,
        houtside, hparts.2⟩
  | false =>
      right
      intro outside houtsideFamily houtside
      cases hreach : warshall (bipartiteIncompatibilityB target)
          vertices (.left rootAtom) (.left outside) with
      | false => rfl
      | true =>
          have houtsideAtoms : outside ∈ atoms :=
            (familyCanonicalAtom_mem_iff hmembers outside).2
              houtsideFamily
          have hany : boundaryOutsideReachB small vertices rootAtom atoms =
              true := by
            apply List.any_eq_true.mpr
            exact ⟨outside, houtsideAtoms, by simp [houtside, hreach]⟩
          rw [hdecision] at hany
          exact False.elim (Bool.false_ne_true hany)

/-! ## 3. The connected branch pays the boundary distance -/

theorem connectedBoundaryPair_path_cost_floor
    {small target : Nat}
    {boundaryFamily otherFamily : List (List Nat)}
    (hboundaryCompatible : boundaryFamily ∈
      canonicalCompatibleAmbientFamilies target)
    (hother : otherFamily ∈ canonicalCompatibleAmbientFamilies target)
    {root : List Nat} (hroot : root ∈ boundaryFamily)
    {outside : CanonicalAtom target}
    {start inner distance : Nat}
    (houtside :
      polymerInsideBoxB small target outside.val = false)
    (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt target start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small)
    (hconnected : warshall (bipartiteIncompatibilityB target)
      (compatiblePairVertices hboundaryCompatible hother)
      (.left (leftCanonicalAtomOfMember hboundaryCompatible hroot))
      (.left outside) = true) :
    distance + 2 ≤
      (warshallCanonicalPath
        (compatiblePairVertices hboundaryCompatible hother)
        (.left (leftCanonicalAtomOfMember hboundaryCompatible hroot))
        (.left outside) hconnected).cost := by
  obtain ⟨outsidePlaquette, houtsidePlaquette, houtsideSmall⟩ :=
    polymerInsideBoxB_false_witness houtside
  obtain ⟨finish, hfinish, hfinishEq⟩ :=
    List.mem_map.mp houtsidePlaquette
  have hfinishOutside :
      boxPlaquetteAt target finish ∉ boxPlaquettes small := by
    rw [hfinishEq]
    exact houtsideSmall
  have houtSmall : outsideBoxB small
      (boxPlaquetteAt target finish) = true :=
    (outsideBoxB_true_iff_not_mem small
      (boxPlaquetteAt target finish)).2 hfinishOutside
  have houtExpanded : outsideBoxB (inner + distance)
      (boxPlaquetteAt target finish) = true := by
    rw [hbox]
    exact houtSmall
  exact warshallCanonicalPath_outside_box_cost_floor
    (compatiblePairVertices hboundaryCompatible hother)
    (.left (leftCanonicalAtomOfMember hboundaryCompatible hroot))
    (.left outside) hconnected hstart hfinish hstartInner houtExpanded

end YMGap.Continuum.Z4CanonicalBoundaryPairDichotomy

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalBoundaryPairDichotomy.boundaryPairReachDichotomy
#print axioms YMGap.Continuum.Z4CanonicalBoundaryPairDichotomy.connectedBoundaryPair_path_cost_floor
