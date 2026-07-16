/-
# Canonical boundary disagreement-component switch

This module instantiates the generic ambient-order switch with the corrected
canonical surface-polymer compatibility relation.  The cut is the finite
Warshall component reached from a chosen left root in the side-tagged pair
graph.  On atoms present on the left it uses left-occurrence reachability; on
right-only atoms it uses right-occurrence reachability.  This convention makes
the single ambient occupation-bit cut exact even when the same polymer occurs
in both replicas.

The main results below prove that the reachability cut is constant across every
occupied cross-replica incompatibility edge and hence that switching preserves
both corrected hard-core compatibility and the exact product activity.
-/

import YMGap.Continuum.FiniteCompatibilitySwitching
import YMGap.Continuum.Z4CanonicalBoundaryPairDichotomy

namespace YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryPairDichotomy
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalIncompatibilityWalk
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Canonical atoms in literal ambient order -/

def canonicalAtomCompatibleB (n : Nat) :
    CanonicalAtom n → CanonicalAtom n → Bool :=
  fun left right =>
    canonicalPolymerCompatibleB n left.val right.val

def canonicalAmbientAtoms (n : Nat) : List (CanonicalAtom n) :=
  familyCanonicalAtoms n (canonicalSurfacePolymers n)
    (fun _ hpolymer => hpolymer)

def canonicalFamilyAtoms {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    List (CanonicalAtom n) :=
  familyCanonicalAtoms n family
    (fun _ hpolymer =>
      compatibleAmbientFamily_member_ambient hfamily hpolymer)

theorem familyCanonicalAtoms_filter_values (n : Nat)
    (test : List Nat → Bool) :
    ∀ (family : List (List Nat))
      (hmembers : ∀ polymer, polymer ∈ family →
        polymer ∈ canonicalSurfacePolymers n),
      ((familyCanonicalAtoms n family hmembers).filter
          (fun atom => test atom.val)).map Subtype.val =
        family.filter test
  | [], _ => rfl
  | polymer :: rest, hmembers => by
      cases htest : test polymer with
      | false =>
          simp only [familyCanonicalAtoms, List.filter_cons, htest,
            Bool.false_eq_true, ↓reduceIte]
          exact familyCanonicalAtoms_filter_values n test rest _
      | true =>
          simp only [familyCanonicalAtoms, List.filter_cons, htest,
            ↓reduceIte, List.map]
          rw [familyCanonicalAtoms_filter_values n test rest]

private theorem canonicalAtomList_eq_of_values_eq {n : Nat} :
    ∀ {left right : List (CanonicalAtom n)},
      left.map Subtype.val = right.map Subtype.val → left = right
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | leftHead :: leftTail, rightHead :: rightTail, h => by
      have hhead : leftHead.val = rightHead.val :=
        List.cons.inj h |>.1
      have htail : leftTail.map Subtype.val =
          rightTail.map Subtype.val := List.cons.inj h |>.2
      have hatom : leftHead = rightHead := Subtype.ext hhead
      subst rightHead
      rw [canonicalAtomList_eq_of_values_eq htail]

private theorem nodup_of_map_nodup {X Y : Type} (value : X → Y) :
    ∀ {xs : List X}, (xs.map value).Nodup → xs.Nodup
  | [], _ => List.nodup_nil
  | head :: tail, h => by
      have hparts := List.nodup_cons.mp h
      apply List.nodup_cons.mpr
      constructor
      · intro hhead
        exact hparts.1 (List.mem_map.mpr ⟨head, hhead, rfl⟩)
      · exact nodup_of_map_nodup value hparts.2

theorem canonicalAmbientAtoms_values (n : Nat) :
    (canonicalAmbientAtoms n).map Subtype.val =
      canonicalSurfacePolymers n :=
  familyCanonicalAtoms_values n _ _

theorem canonicalAmbientAtoms_nodup (n : Nat) :
    (canonicalAmbientAtoms n).Nodup := by
  apply nodup_of_map_nodup Subtype.val
  rw [canonicalAmbientAtoms_values]
  exact canonicalSurfacePolymers_nodup n

theorem canonicalFamilyAtoms_values
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    (canonicalFamilyAtoms hfamily).map Subtype.val = family :=
  familyCanonicalAtoms_values n _ _

/-- The proof-carrying atom list of every compatible family is a literal
subsequence of the proof-carrying canonical ambient list. -/
theorem canonicalFamilyAtoms_mem_sublists
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    canonicalFamilyAtoms hfamily ∈ sublists (canonicalAmbientAtoms n) := by
  let normalized := (canonicalAmbientAtoms n).filter
    (fun atom => memberB family atom.val)
  have hnormalized : normalized ∈ sublists (canonicalAmbientAtoms n) :=
    filter_mem_sublists _ _
  have hnormalizedValues : normalized.map Subtype.val = family := by
    unfold normalized canonicalAmbientAtoms
    rw [familyCanonicalAtoms_filter_values n (memberB family)]
    exact filter_memberB_eq_of_mem_sublists
      (canonicalSurfacePolymers_nodup n)
      (compatibleAmbientFamily_sublist hfamily)
  have hsame : normalized = canonicalFamilyAtoms hfamily :=
    canonicalAtomList_eq_of_values_eq
      (hnormalizedValues.trans (canonicalFamilyAtoms_values hfamily).symm)
  rw [← hsame]
  exact hnormalized

/-! ## 2. Reachability cut and closure across every cross edge -/

def pairReachLeft
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left)
    (atom : CanonicalAtom n) : Bool :=
  warshall (bipartiteIncompatibilityB n)
    (compatiblePairVertices hleft hright)
    (.left (leftCanonicalAtomOfMember hleft hroot)) (.left atom)

def pairReachRight
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left)
    (atom : CanonicalAtom n) : Bool :=
  warshall (bipartiteIncompatibilityB n)
    (compatiblePairVertices hleft hright)
    (.left (leftCanonicalAtomOfMember hleft hroot)) (.right atom)

/-- A single atom cut suitable for pointwise occupation-bit swapping.  A
left-present atom uses its left occurrence; a right-only atom uses its right
occurrence. -/
def pairReachCut
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left)
    (atom : CanonicalAtom n) : Bool :=
  if memberB (canonicalFamilyAtoms hleft) atom then
    pairReachLeft hleft hright hroot atom
  else pairReachRight hleft hright hroot atom

theorem leftAtom_mem_pairVertices
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {atom : CanonicalAtom n}
    (hatom : atom ∈ canonicalFamilyAtoms hleft) :
    BipartiteVertex.left atom ∈ compatiblePairVertices hleft hright := by
  unfold compatiblePairVertices pairBipartiteVertices
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨atom, by simpa [canonicalFamilyAtoms] using hatom, rfl⟩

theorem rightAtom_mem_pairVertices
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {atom : CanonicalAtom n}
    (hatom : atom ∈ canonicalFamilyAtoms hright) :
    BipartiteVertex.right atom ∈ compatiblePairVertices hleft hright := by
  unfold compatiblePairVertices pairBipartiteVertices
  apply List.mem_append_right
  apply List.mem_map.mpr
  exact ⟨atom, by simpa [canonicalFamilyAtoms] using hatom, rfl⟩

theorem canonicalAtomCompatibleB_self_false
    {n : Nat} (atom : CanonicalAtom n) :
    canonicalAtomCompatibleB n atom atom = false := by
  obtain ⟨face, hface⟩ :=
    canonicalSurfacePolymers_allNonempty n atom.val atom.property
  exact canonicalPolymerCompatibleB_false_of_contact
    hface hface (Or.inl rfl)

theorem pairReachRight_of_left_edge
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left)
    {leftAtom rightAtom : CanonicalAtom n}
    (hleftAtom : leftAtom ∈ canonicalFamilyAtoms hleft)
    (hreach : pairReachLeft hleft hright hroot leftAtom = true)
    (hincompatible :
      canonicalAtomCompatibleB n leftAtom rightAtom = false) :
    pairReachRight hleft hright hroot rightAtom = true := by
  unfold pairReachLeft at hreach
  unfold pairReachRight
  apply warshall_trans_of_mem (bipartiteIncompatibilityB n)
    (compatiblePairVertices hleft hright)
    (.left (leftCanonicalAtomOfMember hleft hroot))
    (.left leftAtom) (.right rightAtom)
    (leftAtom_mem_pairVertices hleft hright hleftAtom) hreach
  apply warshall_edge
  change (!(canonicalPolymerCompatibleB n
    leftAtom.val rightAtom.val)) = true
  have hraw : canonicalPolymerCompatibleB n
      leftAtom.val rightAtom.val = false := hincompatible
  rw [hraw]
  rfl

theorem pairReachLeft_of_right_edge
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left)
    {rightAtom leftAtom : CanonicalAtom n}
    (hrightAtom : rightAtom ∈ canonicalFamilyAtoms hright)
    (hreach : pairReachRight hleft hright hroot rightAtom = true)
    (hincompatible :
      canonicalAtomCompatibleB n leftAtom rightAtom = false) :
    pairReachLeft hleft hright hroot leftAtom = true := by
  unfold pairReachRight at hreach
  unfold pairReachLeft
  apply warshall_trans_of_mem (bipartiteIncompatibilityB n)
    (compatiblePairVertices hleft hright)
    (.left (leftCanonicalAtomOfMember hleft hroot))
    (.right rightAtom) (.left leftAtom)
    (rightAtom_mem_pairVertices hleft hright hrightAtom) hreach
  apply warshall_edge
  have hreverse : canonicalAtomCompatibleB n rightAtom leftAtom = false := by
    unfold canonicalAtomCompatibleB
    rw [← canonicalPolymerCompatibleB_symm]
    exact hincompatible
  change (!(canonicalPolymerCompatibleB n
    rightAtom.val leftAtom.val)) = true
  have hraw : canonicalPolymerCompatibleB n
      rightAtom.val leftAtom.val = false := hreverse
  rw [hraw]
  rfl

/-- The reachability cut is constant across every occupied left/right
incompatibility edge. -/
theorem pairReachCut_closed
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left)
    {leftAtom rightAtom : CanonicalAtom n}
    (hleftAtom : leftAtom ∈ canonicalFamilyAtoms hleft)
    (hrightAtom : rightAtom ∈ canonicalFamilyAtoms hright)
    (hincompatible :
      canonicalAtomCompatibleB n leftAtom rightAtom = false) :
    pairReachCut hleft hright hroot leftAtom =
      pairReachCut hleft hright hroot rightAtom := by
  have hleftMemberB : memberB (canonicalFamilyAtoms hleft) leftAtom = true :=
    (memberB_eq_true_iff _ _).2 hleftAtom
  cases hrightLeftMember : memberB (canonicalFamilyAtoms hleft) rightAtom with
  | false =>
      simp only [pairReachCut, hleftMemberB, hrightLeftMember,
        ↓reduceIte]
      apply Bool.eq_iff_iff.mpr
      constructor
      · exact fun hreach => pairReachRight_of_left_edge
          hleft hright hroot hleftAtom hreach hincompatible
      · exact fun hreach => pairReachLeft_of_right_edge
          hleft hright hroot hrightAtom hreach hincompatible
  | true =>
      have hrightLeft : rightAtom ∈ canonicalFamilyAtoms hleft :=
        (memberB_eq_true_iff _ _).1 hrightLeftMember
      simp only [pairReachCut, hleftMemberB, hrightLeftMember, ↓reduceIte]
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hleftReach
        have hrightSideReach := pairReachRight_of_left_edge
          hleft hright hroot hleftAtom hleftReach hincompatible
        exact pairReachLeft_of_right_edge hleft hright hroot hrightAtom
          hrightSideReach (canonicalAtomCompatibleB_self_false rightAtom)
      · intro hrightReach
        have hrightSideReach := pairReachRight_of_left_edge
          hleft hright hroot hrightLeft hrightReach
            (canonicalAtomCompatibleB_self_false rightAtom)
        exact pairReachLeft_of_right_edge hleft hright hroot hrightAtom
          hrightSideReach hincompatible

/-! ## 3. The exact canonical atom switch -/

def switchedLeftAtoms
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left) :
    List (CanonicalAtom n) :=
  switchedLeft (canonicalAmbientAtoms n)
    (pairReachCut hleft hright hroot)
    (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright)

def switchedRightAtoms
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left) :
    List (CanonicalAtom n) :=
  switchedRight (canonicalAmbientAtoms n)
    (pairReachCut hleft hright hroot)
    (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright)

private theorem familyCanonicalAtoms_all_values (n : Nat)
    (test : List Nat → Bool) :
    ∀ (family : List (List Nat))
      (hmembers : ∀ polymer, polymer ∈ family →
        polymer ∈ canonicalSurfacePolymers n),
      (familyCanonicalAtoms n family hmembers).all
          (fun atom => test atom.val) = family.all test
  | [], _ => rfl
  | _ :: rest, _ => by
      simp only [familyCanonicalAtoms, List.all_cons]
      rw [familyCanonicalAtoms_all_values n test rest]

private theorem familyCanonicalAtoms_compatible_eq (n : Nat) :
    ∀ (family : List (List Nat))
      (hmembers : ∀ polymer, polymer ∈ family →
        polymer ∈ canonicalSurfacePolymers n),
      familyCompatibleB (canonicalAtomCompatibleB n)
          (familyCanonicalAtoms n family hmembers) =
        canonicalFamilyCompatibleB n family
  | [], _ => rfl
  | head :: tail, hmembers => by
      change
        ((familyCanonicalAtoms n tail _).all
            (fun atom => canonicalPolymerCompatibleB n head atom.val) &&
          familyCompatibleB (canonicalAtomCompatibleB n)
            (familyCanonicalAtoms n tail _)) =
          (tail.all (canonicalPolymerCompatibleB n head) &&
            canonicalFamilyCompatibleB n tail)
      rw [familyCanonicalAtoms_all_values n
        (canonicalPolymerCompatibleB n head) tail]
      rw [familyCanonicalAtoms_compatible_eq n tail]

theorem canonicalFamilyAtoms_compatible
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    familyCompatibleB (canonicalAtomCompatibleB n)
      (canonicalFamilyAtoms hfamily) = true := by
  have hcanonical := (List.mem_filter.mp hfamily).2
  have heq : familyCompatibleB (canonicalAtomCompatibleB n)
      (canonicalFamilyAtoms hfamily) =
      canonicalFamilyCompatibleB n family :=
    familyCanonicalAtoms_compatible_eq n family _
  rw [heq]
  exact hcanonical

theorem switchedAtoms_compatible
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left) :
    familyCompatibleB (canonicalAtomCompatibleB n)
        (switchedLeftAtoms hleft hright hroot) = true ∧
      familyCompatibleB (canonicalAtomCompatibleB n)
        (switchedRightAtoms hleft hright hroot) = true := by
  exact switched_pair_compatible (canonicalAtomCompatibleB n)
    (fun first second => canonicalPolymerCompatibleB_symm
      n first.val second.val)
    (pairReachCut hleft hright hroot)
    (canonicalAmbientAtoms_nodup n)
    (canonicalFamilyAtoms_compatible hleft)
    (canonicalFamilyAtoms_compatible hright)
    (fun leftAtom hleftAtom rightAtom hrightAtom hincompatible =>
      pairReachCut_closed hleft hright hroot
        hleftAtom hrightAtom hincompatible)

theorem switchedAtoms_weight_preserved
    (w : Q') {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left) :
    familyWeight (fun atom : CanonicalAtom n =>
        canonicalSurfaceActivity w n atom.val)
        (switchedLeftAtoms hleft hright hroot) *
      familyWeight (fun atom : CanonicalAtom n =>
        canonicalSurfaceActivity w n atom.val)
        (switchedRightAtoms hleft hright hroot) ≈
    familyWeight (fun atom : CanonicalAtom n =>
        canonicalSurfaceActivity w n atom.val)
        (canonicalFamilyAtoms hleft) *
      familyWeight (fun atom : CanonicalAtom n =>
        canonicalSurfaceActivity w n atom.val)
        (canonicalFamilyAtoms hright) := by
  exact switched_pair_weight_preserved
    (fun atom : CanonicalAtom n => canonicalSurfaceActivity w n atom.val)
    (pairReachCut hleft hright hroot)
    (canonicalAmbientAtoms_nodup n)
    (canonicalFamilyAtoms_mem_sublists hleft)
    (canonicalFamilyAtoms_mem_sublists hright)

/-! ## 4. Return to literal canonical families -/

def switchedLeftFamily
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left) :
    List (List Nat) :=
  (switchedLeftAtoms hleft hright hroot).map Subtype.val

def switchedRightFamily
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left) :
    List (List Nat) :=
  (switchedRightAtoms hleft hright hroot).map Subtype.val

private theorem atomList_all_values {n : Nat}
    (test : List Nat → Bool) :
    ∀ atoms : List (CanonicalAtom n),
      atoms.all (fun atom => test atom.val) =
        (atoms.map Subtype.val).all test
  | [] => rfl
  | _ :: rest => by
      simp only [List.all_cons, List.map]
      rw [atomList_all_values test rest]

private theorem atomList_compatible_eq {n : Nat} :
    ∀ atoms : List (CanonicalAtom n),
      familyCompatibleB (canonicalAtomCompatibleB n) atoms =
        familyCompatibleB (canonicalPolymerCompatibleB n)
          (atoms.map Subtype.val)
  | [] => rfl
  | head :: rest => by
      change
        (rest.all (fun atom =>
            canonicalPolymerCompatibleB n head.val atom.val) &&
          familyCompatibleB (canonicalAtomCompatibleB n) rest) =
        ((rest.map Subtype.val).all
            (canonicalPolymerCompatibleB n head.val) &&
          familyCompatibleB (canonicalPolymerCompatibleB n)
            (rest.map Subtype.val))
      rw [atomList_all_values
        (canonicalPolymerCompatibleB n head.val) rest]
      rw [atomList_compatible_eq rest]

theorem switchedFamilies_mem_compatible
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left) :
    switchedLeftFamily hleft hright hroot ∈
        canonicalCompatibleAmbientFamilies n ∧
      switchedRightFamily hleft hright hroot ∈
        canonicalCompatibleAmbientFamilies n := by
  have hatomCompat := switchedAtoms_compatible hleft hright hroot
  constructor
  · unfold canonicalCompatibleAmbientFamilies
    apply List.mem_filter.mpr
    constructor
    · have hsub := map_mem_sublists Subtype.val
          (canonicalAmbientAtoms n)
          (switchedLeftAtoms hleft hright hroot)
          (switchedLeft_mem_sublists (canonicalAmbientAtoms n)
            (pairReachCut hleft hright hroot)
            (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright))
      rw [canonicalAmbientAtoms_values] at hsub
      exact hsub
    · have hgeneric : familyCompatibleB
          (canonicalPolymerCompatibleB n)
          (switchedLeftFamily hleft hright hroot) = true := by
        unfold switchedLeftFamily
        rw [← atomList_compatible_eq]
        exact hatomCompat.1
      rw [genericFamilyCompatibleB_eq_canonical n] at hgeneric
      exact hgeneric
  · unfold canonicalCompatibleAmbientFamilies
    apply List.mem_filter.mpr
    constructor
    · have hsub := map_mem_sublists Subtype.val
          (canonicalAmbientAtoms n)
          (switchedRightAtoms hleft hright hroot)
          (switchedRight_mem_sublists (canonicalAmbientAtoms n)
            (pairReachCut hleft hright hroot)
            (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright))
      rw [canonicalAmbientAtoms_values] at hsub
      exact hsub
    · have hgeneric : familyCompatibleB
          (canonicalPolymerCompatibleB n)
          (switchedRightFamily hleft hright hroot) = true := by
        unfold switchedRightFamily
        rw [← atomList_compatible_eq]
        exact hatomCompat.2
      rw [genericFamilyCompatibleB_eq_canonical n] at hgeneric
      exact hgeneric

private theorem atomList_weight_eq (w : Q') (n : Nat) :
    ∀ atoms : List (CanonicalAtom n),
      familyWeight (fun atom : CanonicalAtom n =>
          canonicalSurfaceActivity w n atom.val) atoms =
        canonicalSurfaceFamilyActivity w n
          (atoms.map Subtype.val)
  | [] => rfl
  | _ :: rest => by
      simp only [familyWeight_cons, List.map,
        canonicalSurfaceFamilyActivity]
      rw [atomList_weight_eq w n rest]

theorem switchedFamilies_weight_preserved
    (w : Q') {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left) :
    canonicalSurfaceFamilyActivity w n
        (switchedLeftFamily hleft hright hroot) *
      canonicalSurfaceFamilyActivity w n
        (switchedRightFamily hleft hright hroot) ≈
    canonicalSurfaceFamilyActivity w n left *
      canonicalSurfaceFamilyActivity w n right := by
  have hweight := switchedAtoms_weight_preserved
    w hleft hright hroot
  rw [atomList_weight_eq w n] at hweight
  rw [atomList_weight_eq w n] at hweight
  rw [atomList_weight_eq w n] at hweight
  rw [atomList_weight_eq w n] at hweight
  rw [canonicalFamilyAtoms_values hleft] at hweight
  rw [canonicalFamilyAtoms_values hright] at hweight
  exact hweight

/-! ## 5. Membership and the local event under switching -/

theorem canonicalFamilyAtom_mem_iff
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n)
    (atom : CanonicalAtom n) :
    atom ∈ canonicalFamilyAtoms hfamily ↔ atom.val ∈ family := by
  unfold canonicalFamilyAtoms
  exact familyCanonicalAtom_mem_iff _ atom

theorem canonicalAtom_mem_ambientAtoms
    {n : Nat} (atom : CanonicalAtom n) :
    atom ∈ canonicalAmbientAtoms n := by
  unfold canonicalAmbientAtoms
  exact (familyCanonicalAtom_mem_iff _ atom).2 atom.property

theorem canonicalAtom_value_mem_values_iff
    {n : Nat} (atoms : List (CanonicalAtom n))
    (atom : CanonicalAtom n) :
    atom.val ∈ atoms.map Subtype.val ↔ atom ∈ atoms := by
  constructor
  · intro hvalue
    obtain ⟨found, hfound, hfoundValue⟩ := List.mem_map.mp hvalue
    have hsame : found = atom := Subtype.ext hfoundValue
    simpa [hsame] using hfound
  · intro hatom
    exact List.mem_map.mpr ⟨atom, hatom, rfl⟩

theorem mem_switchedLeftAtoms_iff
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left)
    (atom : CanonicalAtom n) :
    atom ∈ switchedLeftAtoms hleft hright hroot ↔
      switchedLeftB (pairReachCut hleft hright hroot)
        (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright)
        atom = true := by
  unfold switchedLeftAtoms switchedLeft
  constructor
  · exact fun hatom => (List.mem_filter.mp hatom).2
  · intro htest
    exact List.mem_filter.mpr
      ⟨canonicalAtom_mem_ambientAtoms atom, htest⟩

theorem mem_switchedRightAtoms_iff
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left)
    (atom : CanonicalAtom n) :
    atom ∈ switchedRightAtoms hleft hright hroot ↔
      switchedRightB (pairReachCut hleft hright hroot)
        (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright)
        atom = true := by
  unfold switchedRightAtoms switchedRight
  constructor
  · exact fun hatom => (List.mem_filter.mp hatom).2
  · intro htest
    exact List.mem_filter.mpr
      ⟨canonicalAtom_mem_ambientAtoms atom, htest⟩

theorem pairReachCut_root_true
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left) :
    pairReachCut hleft hright hroot
      (leftCanonicalAtomOfMember hleft hroot) = true := by
  have hrootAtom : leftCanonicalAtomOfMember hleft hroot ∈
      canonicalFamilyAtoms hleft :=
    (canonicalFamilyAtom_mem_iff hleft _).2 hroot
  have hrootMemberB : memberB (canonicalFamilyAtoms hleft)
      (leftCanonicalAtomOfMember hleft hroot) = true :=
    (memberB_eq_true_iff _ _).2 hrootAtom
  simp only [pairReachCut, hrootMemberB, ↓reduceIte]
  unfold pairReachLeft
  exact warshall_refl (bipartiteIncompatibilityB n)
    (compatiblePairVertices hleft hright)
    (.left (leftCanonicalAtomOfMember hleft hroot))

theorem switchedFamilies_root_cells
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left)
    (hrootRight : root ∉ right) :
    familyContainsPolymerB root
        (switchedLeftFamily hleft hright hroot) = false ∧
      familyContainsPolymerB root
        (switchedRightFamily hleft hright hroot) = true := by
  let rootAtom := leftCanonicalAtomOfMember hleft hroot
  have hrootLeftAtom : rootAtom ∈ canonicalFamilyAtoms hleft :=
    (canonicalFamilyAtom_mem_iff hleft rootAtom).2 hroot
  have hrootRightAtom : rootAtom ∉ canonicalFamilyAtoms hright := by
    intro hmem
    exact hrootRight ((canonicalFamilyAtom_mem_iff hright rootAtom).1 hmem)
  have hcut : pairReachCut hleft hright hroot rootAtom = true :=
    pairReachCut_root_true hleft hright hroot
  have hleftOut : rootAtom ∉ switchedLeftAtoms hleft hright hroot := by
    intro hmem
    have htest := (mem_switchedLeftAtoms_iff
      hleft hright hroot rootAtom).1 hmem
    have hrightB : memberB (canonicalFamilyAtoms hright) rootAtom = false :=
      (memberB_eq_false_iff _ _).2 hrootRightAtom
    simp [switchedLeftB, hcut, hrightB] at htest
  have hrightOut : rootAtom ∈ switchedRightAtoms hleft hright hroot := by
    apply (mem_switchedRightAtoms_iff hleft hright hroot rootAtom).2
    have hleftB : memberB (canonicalFamilyAtoms hleft) rootAtom = true :=
      (memberB_eq_true_iff _ _).2 hrootLeftAtom
    simp [switchedRightB, hcut, hleftB]
  constructor
  · unfold familyContainsPolymerB switchedLeftFamily
    have hnot : root ∉
        (switchedLeftAtoms hleft hright hroot).map Subtype.val := by
      intro hvalue
      exact hleftOut
        ((canonicalAtom_value_mem_values_iff _ rootAtom).1 hvalue)
    simpa using hnot
  · unfold familyContainsPolymerB switchedRightFamily
    have hvalue : root ∈
        (switchedRightAtoms hleft hright hroot).map Subtype.val :=
      (canonicalAtom_value_mem_values_iff _ rootAtom).2 hrightOut
    simpa using hvalue

/-! ## 6. The separated branch lands in the opposite four-cell product -/

theorem switchedRightFamily_inside_of_separated
    {small n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left)
    (hrightInside : FamilyInsideBox small n right)
    (hseparated : ∀ outside : CanonicalAtom n,
      outside.val ∈ left →
        polymerInsideBoxB small n outside.val = false →
          pairReachLeft hleft hright hroot outside = false) :
    FamilyInsideBox small n
      (switchedRightFamily hleft hright hroot) := by
  intro support hsupport
  unfold switchedRightFamily at hsupport
  obtain ⟨atom, hatom, hatomValue⟩ := List.mem_map.mp hsupport
  subst support
  have htest := (mem_switchedRightAtoms_iff
    hleft hright hroot atom).1 hatom
  cases hcut : pairReachCut hleft hright hroot atom with
  | false =>
      have hrightAtom : atom ∈ canonicalFamilyAtoms hright := by
        have hmemberB : memberB (canonicalFamilyAtoms hright) atom = true := by
          simpa [switchedRightB, hcut] using htest
        exact (memberB_eq_true_iff _ _).1 hmemberB
      exact hrightInside atom.val
        ((canonicalFamilyAtom_mem_iff hright atom).1 hrightAtom)
  | true =>
      have hleftAtom : atom ∈ canonicalFamilyAtoms hleft := by
        have hmemberB : memberB (canonicalFamilyAtoms hleft) atom = true := by
          simpa [switchedRightB, hcut] using htest
        exact (memberB_eq_true_iff _ _).1 hmemberB
      have hleftRaw : atom.val ∈ left :=
        (canonicalFamilyAtom_mem_iff hleft atom).1 hleftAtom
      have hleftMemberB : memberB (canonicalFamilyAtoms hleft) atom = true :=
        (memberB_eq_true_iff _ _).2 hleftAtom
      have hreach : pairReachLeft hleft hright hroot atom = true := by
        unfold pairReachCut at hcut
        simpa [hleftMemberB] using hcut
      cases hinside : polymerInsideBoxB small n atom.val with
      | true =>
          exact (polymerInsideBoxB_true_iff small n atom.val).1 hinside
      | false =>
          have hnotReach := hseparated atom hleftRaw hinside
          rw [hnotReach] at hreach
          exact False.elim (Bool.false_ne_true hreach)

theorem outside_support_mem_switchedLeft_of_separated
    {small n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left)
    {outside : List Nat} (houtside : outside ∈ left)
    (houtsideBox : polymerInsideBoxB small n outside = false)
    (hseparated : ∀ atom : CanonicalAtom n,
      atom.val ∈ left →
        polymerInsideBoxB small n atom.val = false →
          pairReachLeft hleft hright hroot atom = false) :
    outside ∈ switchedLeftFamily hleft hright hroot := by
  let outsideAtom : CanonicalAtom n :=
    ⟨outside, compatibleAmbientFamily_member_ambient hleft houtside⟩
  have houtsideAtom : outsideAtom ∈ canonicalFamilyAtoms hleft :=
    (canonicalFamilyAtom_mem_iff hleft outsideAtom).2 houtside
  have hreach : pairReachLeft hleft hright hroot outsideAtom = false :=
    hseparated outsideAtom houtside houtsideBox
  have hleftMemberB : memberB (canonicalFamilyAtoms hleft) outsideAtom = true :=
    (memberB_eq_true_iff _ _).2 houtsideAtom
  have hcut : pairReachCut hleft hright hroot outsideAtom = false := by
    unfold pairReachCut
    simpa [hleftMemberB] using hreach
  have houtAtoms : outsideAtom ∈
      switchedLeftAtoms hleft hright hroot := by
    apply (mem_switchedLeftAtoms_iff
      hleft hright hroot outsideAtom).2
    simp [switchedLeftB, hcut, hleftMemberB]
  unfold switchedLeftFamily
  exact (canonicalAtom_value_mem_values_iff _ outsideAtom).2 houtAtoms

theorem switchedLeftFamily_mem_boundary_of_separated
    {small n : Nat} (hsmall : small ≤ n)
    {left right : List (List Nat)}
    (hleftBoundary : left ∈ boundaryTargetFamilies small n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {root : List Nat} (hroot : root ∈ left)
    (hseparated : ∀ atom : CanonicalAtom n,
      atom.val ∈ left →
        polymerInsideBoxB small n atom.val = false →
          pairReachLeft (List.mem_filter.mp hleftBoundary).1
            hright hroot atom = false) :
    switchedLeftFamily (List.mem_filter.mp hleftBoundary).1
        hright hroot ∈ boundaryTargetFamilies small n := by
  let hleft := (List.mem_filter.mp hleftBoundary).1
  obtain ⟨outside, houtside, plaquette, hplaquette,
      hplaquetteOutside⟩ :=
    boundaryTargetFamily_has_outside_witness hsmall hleftBoundary
  have houtsideBox : polymerInsideBoxB small n outside = false := by
    cases hinside : polymerInsideBoxB small n outside with
    | false => rfl
    | true =>
        have hin := (polymerInsideBoxB_true_iff small n outside).1
          hinside plaquette hplaquette
        exact False.elim (hplaquetteOutside hin)
  have houtsideOutput : outside ∈
      switchedLeftFamily hleft hright hroot :=
    outside_support_mem_switchedLeft_of_separated
      hleft hright hroot houtside houtsideBox hseparated
  have houtCompat :=
    (switchedFamilies_mem_compatible hleft hright hroot).1
  have hnotEmbedded : switchedLeftFamily hleft hright hroot ∉
      embeddedCompatibleFamilies small n := by
    intro hembedded
    have hinside := familyInsideBox_of_mem_embeddedCompatibleFamilies
      hsmall hembedded
    exact hplaquetteOutside
      (hinside outside houtsideOutput plaquette hplaquette)
  unfold boundaryTargetFamilies
  apply List.mem_filter.mpr
  constructor
  · exact houtCompat
  · unfold embeddedFamilyB
    simp [hnotEmbedded]

theorem switchedRightFamily_mem_embedded_of_separated
    {small n : Nat} (hsmall : small ≤ n)
    {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hrightEmbedded : right ∈ embeddedCompatibleFamilies small n)
    {root : List Nat} (hroot : root ∈ left)
    (hseparated : ∀ atom : CanonicalAtom n,
      atom.val ∈ left →
        polymerInsideBoxB small n atom.val = false →
          pairReachLeft hleft
            (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
            hroot atom = false) :
    switchedRightFamily hleft
        (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
        hroot ∈ embeddedCompatibleFamilies small n := by
  let hright := embeddedCompatibleFamilies_member_target
    hsmall hrightEmbedded
  have hrightInside := familyInsideBox_of_mem_embeddedCompatibleFamilies
    hsmall hrightEmbedded
  have houtInside := switchedRightFamily_inside_of_separated
    hleft hright hroot hrightInside hseparated
  have houtCompat :=
    (switchedFamilies_mem_compatible hleft hright hroot).2
  exact family_mem_embeddedCompatibleFamilies_of_inside
    hsmall houtCompat houtInside

/-- Complete per-pair separated-branch switch.  A boundary family containing
the root and an embedded family avoiding it are sent to a boundary family
avoiding the root and an embedded family containing it, with the exact pair
activity unchanged.  This is the local cancellation mechanism required by the
four-cell covariance identity; global injectivity/recovery is the next layer. -/
theorem separated_boundary_event_pair_switch
    (w : Q') {small n : Nat} (hsmall : small ≤ n)
    {left right : List (List Nat)}
    (hleftBoundary : left ∈ boundaryTargetFamilies small n)
    (hrightEmbedded : right ∈ embeddedCompatibleFamilies small n)
    {root : List Nat} (hroot : root ∈ left)
    (hrootRight : root ∉ right)
    (hseparated : ∀ atom : CanonicalAtom n,
      atom.val ∈ left →
        polymerInsideBoxB small n atom.val = false →
          pairReachLeft (List.mem_filter.mp hleftBoundary).1
            (embeddedCompatibleFamilies_member_target
              hsmall hrightEmbedded)
            hroot atom = false) :
    switchedLeftFamily (List.mem_filter.mp hleftBoundary).1
        (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
        hroot ∈ boundaryTargetFamilies small n ∧
      familyContainsPolymerB root
        (switchedLeftFamily (List.mem_filter.mp hleftBoundary).1
          (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
          hroot) = false ∧
      switchedRightFamily (List.mem_filter.mp hleftBoundary).1
        (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
        hroot ∈ embeddedCompatibleFamilies small n ∧
      familyContainsPolymerB root
        (switchedRightFamily (List.mem_filter.mp hleftBoundary).1
          (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
          hroot) = true ∧
      canonicalSurfaceFamilyActivity w n
          (switchedLeftFamily (List.mem_filter.mp hleftBoundary).1
            (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
            hroot) *
        canonicalSurfaceFamilyActivity w n
          (switchedRightFamily (List.mem_filter.mp hleftBoundary).1
            (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
            hroot) ≈
      canonicalSurfaceFamilyActivity w n left *
        canonicalSurfaceFamilyActivity w n right := by
  let hleft := (List.mem_filter.mp hleftBoundary).1
  let hright := embeddedCompatibleFamilies_member_target
    hsmall hrightEmbedded
  have hboundary := switchedLeftFamily_mem_boundary_of_separated
    hsmall hleftBoundary hright hroot hseparated
  have hembedded := switchedRightFamily_mem_embedded_of_separated
    hsmall hleft hrightEmbedded hroot hseparated
  have hrootCells := switchedFamilies_root_cells
    hleft hright hroot hrootRight
  have hweight := switchedFamilies_weight_preserved
    w hleft hright hroot
  exact ⟨hboundary, hrootCells.1, hembedded,
    hrootCells.2, hweight⟩

end YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch.canonicalFamilyAtoms_mem_sublists
#print axioms YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch.pairReachCut_closed
#print axioms YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch.switchedAtoms_compatible
#print axioms YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch.switchedAtoms_weight_preserved
#print axioms YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch.switchedFamilies_mem_compatible
#print axioms YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch.switchedFamilies_weight_preserved
#print axioms YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch.switchedFamilies_root_cells
#print axioms YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch.switchedRightFamily_inside_of_separated
#print axioms YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch.switchedLeftFamily_mem_boundary_of_separated
#print axioms YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch.switchedRightFamily_mem_embedded_of_separated
#print axioms YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch.separated_boundary_event_pair_switch
