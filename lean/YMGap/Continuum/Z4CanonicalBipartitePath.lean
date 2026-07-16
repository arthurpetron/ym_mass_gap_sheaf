/-
# Bipartite incompatibility paths for the canonical gas

Pairs of compatible families have no incompatibility edges within either
replica; every disagreement edge runs between replicas.  This module builds a
finite Warshall reachability test on side-tagged canonical polymers, extracts
an actual directed incompatibility path, and proves that the path's repeated
surface cost pays the L-infinity separation of arbitrary endpoint faces.

Repeated middle polymers are intentionally counted twice under path
composition.  This is the correct safe majorant for the subsequent positive
walk sum and avoids any unproved simple-path erasure.
-/

import YMGap.Continuum.Z4CanonicalIncompatibilityWalk

namespace YMGap.Continuum.Z4CanonicalBipartitePath

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4CanonicalIncompatibilityWalk
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4FiniteBoxExhaustion

/-! ## 1. Canonical atoms and the bipartite incompatibility graph -/

abbrev CanonicalAtom (n : Nat) : Type :=
  {polymer : List Nat // polymer ∈ canonicalSurfacePolymers n}

inductive BipartiteVertex (n : Nat) : Type
  | left : CanonicalAtom n → BipartiteVertex n
  | right : CanonicalAtom n → BipartiteVertex n
deriving DecidableEq

def BipartiteVertex.atom {n : Nat} :
    BipartiteVertex n → CanonicalAtom n
  | .left atom => atom
  | .right atom => atom

def bipartiteIncompatibilityB (n : Nat) :
    BipartiteVertex n → BipartiteVertex n → Bool
  | .left left, .right right =>
      !(canonicalPolymerCompatibleB n left.val right.val)
  | .right left, .left right =>
      !(canonicalPolymerCompatibleB n left.val right.val)
  | _, _ => false

theorem bipartiteIncompatibilityB_symm (n : Nat)
    (left right : BipartiteVertex n) :
    bipartiteIncompatibilityB n left right =
      bipartiteIncompatibilityB n right left := by
  cases left <;> cases right <;>
    simp only [bipartiteIncompatibilityB]
  · rw [canonicalPolymerCompatibleB_symm]
  · rw [canonicalPolymerCompatibleB_symm]

/-! ## 2. Finite Warshall reachability -/

inductive DWalk {A : Type} (edge : A → A → Bool) : A → A → Type
  | refl (vertex : A) : DWalk edge vertex vertex
  | edge {left right : A} : edge left right = true →
      DWalk edge left right
  | trans {left middle right : A} :
      DWalk edge left middle → DWalk edge middle right →
        DWalk edge left right

def warshall [DecidableEq A] (edge : A → A → Bool) :
    List A → A → A → Bool
  | [], left, right => decide (left = right) || edge left right
  | middle :: rest, left, right =>
      warshall edge rest left right ||
        (warshall edge rest left middle &&
          warshall edge rest middle right)

theorem warshall_refl [DecidableEq A] (edge : A → A → Bool) :
    ∀ vertices : List A, ∀ vertex : A,
      warshall edge vertices vertex vertex = true
  | [], vertex => by simp [warshall]
  | _ :: rest, vertex => by
      unfold warshall
      rw [warshall_refl edge rest vertex]
      rfl

theorem warshall_edge [DecidableEq A] (edge : A → A → Bool)
    {left right : A} (hedge : edge left right = true) :
    ∀ vertices : List A,
      warshall edge vertices left right = true
  | [] => by simp [warshall, hedge]
  | _ :: rest => by
      unfold warshall
      rw [warshall_edge edge hedge rest]
      rfl

/-- Warshall reachability is transitive through every intermediate vertex
that occurs in the explicit finite universe. -/
theorem warshall_trans_of_mem [DecidableEq A] (edge : A → A → Bool) :
    ∀ (vertices : List A) (left middle right : A), middle ∈ vertices →
      warshall edge vertices left middle = true →
      warshall edge vertices middle right = true →
      warshall edge vertices left right = true
  | [], _, middle, _, hmiddle, _, _ => by cases hmiddle
  | pivot :: rest, left, middle, right, hmiddle, hleft, hright => by
      unfold warshall at hleft hright ⊢
      rcases List.mem_cons.mp hmiddle with hmiddlePivot | hmiddleRest
      · subst middle
        rcases (Bool.or_eq_true _ _).mp hleft with hleftPivot | hleftVia
        · have hleftPivot' := hleftPivot
          rcases (Bool.or_eq_true _ _).mp hright with hpivotRight | hrightVia
          · exact (Bool.or_eq_true _ _).mpr (Or.inr
              ((Bool.and_eq_true _ _).mpr
                ⟨hleftPivot', hpivotRight⟩))
          · exact (Bool.or_eq_true _ _).mpr (Or.inr
              ((Bool.and_eq_true _ _).mpr
                ⟨hleftPivot',
                  ((Bool.and_eq_true _ _).mp hrightVia).2⟩))
        · have hleftPivot' := ((Bool.and_eq_true _ _).mp hleftVia).1
          rcases (Bool.or_eq_true _ _).mp hright with hpivotRight | hrightVia
          · exact (Bool.or_eq_true _ _).mpr (Or.inr
              ((Bool.and_eq_true _ _).mpr
                ⟨hleftPivot', hpivotRight⟩))
          · exact (Bool.or_eq_true _ _).mpr (Or.inr
              ((Bool.and_eq_true _ _).mpr
                ⟨hleftPivot',
                  ((Bool.and_eq_true _ _).mp hrightVia).2⟩))
      · rcases (Bool.or_eq_true _ _).mp hleft with hleftDirect | hleftVia
        · rcases (Bool.or_eq_true _ _).mp hright with
            hrightDirect | hrightVia
          · exact (Bool.or_eq_true _ _).mpr (Or.inl
              (warshall_trans_of_mem edge rest left middle right
                hmiddleRest hleftDirect hrightDirect))
          · rcases (Bool.and_eq_true _ _).mp hrightVia with
              ⟨hmiddlePivot, hpivotRight⟩
            have hleftPivot := warshall_trans_of_mem edge rest
              left middle pivot hmiddleRest hleftDirect hmiddlePivot
            exact (Bool.or_eq_true _ _).mpr (Or.inr
              ((Bool.and_eq_true _ _).mpr
                ⟨hleftPivot, hpivotRight⟩))
        · rcases (Bool.and_eq_true _ _).mp hleftVia with
            ⟨hleftPivot, hpivotMiddle⟩
          rcases (Bool.or_eq_true _ _).mp hright with
              hrightDirect | hrightVia
          · have hpivotRight := warshall_trans_of_mem edge rest
              pivot middle right hmiddleRest hpivotMiddle hrightDirect
            exact (Bool.or_eq_true _ _).mpr (Or.inr
              ((Bool.and_eq_true _ _).mpr
                ⟨hleftPivot, hpivotRight⟩))
          · exact (Bool.or_eq_true _ _).mpr (Or.inr
              ((Bool.and_eq_true _ _).mpr
                ⟨hleftPivot,
                  ((Bool.and_eq_true _ _).mp hrightVia).2⟩))

/-- Finite Warshall closure is equivariant under an injective relabelling of
vertices that preserves every directed edge.  Keeping the mapped universe
literal avoids any hidden appeal to permutation invariance in the later
reverse-component argument. -/
theorem warshall_map_equiv
    {A B : Type} [DecidableEq A] [DecidableEq B]
    (edgeA : A → A → Bool) (edgeB : B → B → Bool)
    (rename : A → B) (hinjective : Function.Injective rename)
    (hedge : ∀ left right,
      edgeB (rename left) (rename right) = edgeA left right) :
    ∀ (vertices : List A) (left right : A),
      warshall edgeB (vertices.map rename)
          (rename left) (rename right) =
        warshall edgeA vertices left right
  | [], left, right => by
      have heq : (rename left = rename right) ↔ left = right := by
        constructor
        · exact fun h => hinjective h
        · exact fun h => congrArg rename h
      have hdecide : decide (rename left = rename right) =
          decide (left = right) := by
        apply Bool.eq_iff_iff.mpr
        simpa only [decide_eq_true_eq] using heq
      simp only [List.map, warshall, hdecide, hedge]
  | middle :: rest, left, right => by
      simp only [List.map, warshall]
      rw [warshall_map_equiv edgeA edgeB rename hinjective hedge
        rest left right]
      rw [warshall_map_equiv edgeA edgeB rename hinjective hedge
        rest left middle]
      rw [warshall_map_equiv edgeA edgeB rename hinjective hedge
        rest middle right]

/-- Warshall truth carries an actual finite directed walk. -/
def warshallSound [DecidableEq A] (edge : A → A → Bool) :
    ∀ (vertices : List A) (left right : A),
      warshall edge vertices left right = true →
        DWalk edge left right
  | [], left, right, h => by
      cases heq : decide (left = right) with
      | true =>
          have hsame : left = right := of_decide_eq_true heq
          subst right
          exact DWalk.refl left
      | false =>
          have hedge : edge left right = true := by
            simpa [warshall, heq] using h
          exact DWalk.edge hedge
  | middle :: rest, left, right, h => by
      cases hdirect : warshall edge rest left right with
      | true => exact warshallSound edge rest left right hdirect
      | false =>
          have hboth : (warshall edge rest left middle &&
              warshall edge rest middle right) = true := by
            simpa [warshall, hdirect] using h
          have hparts := (Bool.and_eq_true _ _).mp hboth
          exact DWalk.trans
            (warshallSound edge rest left middle hparts.1)
            (warshallSound edge rest middle right hparts.2)

/-! ## 3. Extracted canonical paths and their repeated cost -/

inductive CanonicalIncompatibilityPath (n : Nat) :
    CanonicalAtom n → CanonicalAtom n → Type
  | refl (atom : CanonicalAtom n) :
      CanonicalIncompatibilityPath n atom atom
  | edge {left right : CanonicalAtom n}
      (hincompatible :
        canonicalPolymerCompatibleB n left.val right.val = false) :
      CanonicalIncompatibilityPath n left right
  | trans {left middle right : CanonicalAtom n}
      (first : CanonicalIncompatibilityPath n left middle)
      (second : CanonicalIncompatibilityPath n middle right) :
      CanonicalIncompatibilityPath n left right

def CanonicalIncompatibilityPath.cost {n : Nat} :
    {left right : CanonicalAtom n} →
      CanonicalIncompatibilityPath n left right → Nat
  | _, _, .refl atom => atom.val.length
  | _, _, .edge (left := left) (right := right) _ =>
      left.val.length + right.val.length
  | _, _, .trans first second => first.cost + second.cost

private theorem bool_not_true_implies_false {value : Bool}
    (h : (!value) = true) : value = false := by
  cases value <;> simp_all

/-- Every side-tagged graph walk forgets to a genuine canonical
incompatibility path. -/
def dWalkToCanonicalPath {n : Nat} :
    {left right : BipartiteVertex n} →
      DWalk (bipartiteIncompatibilityB n) left right →
        CanonicalIncompatibilityPath n left.atom right.atom
  | _, _, .refl vertex => .refl vertex.atom
  | .left left, .right right, .edge hedge =>
      .edge (bool_not_true_implies_false hedge)
  | .right left, .left right, .edge hedge =>
      .edge (bool_not_true_implies_false hedge)
  | .left _, .left _, .edge hedge => by cases hedge
  | .right _, .right _, .edge hedge => by cases hedge
  | _, _, .trans first second =>
      .trans (dWalkToCanonicalPath first)
        (dWalkToCanonicalPath second)

def warshallCanonicalPath {n : Nat}
    (vertices : List (BipartiteVertex n))
    (left right : BipartiteVertex n)
    (hreaches : warshall (bipartiteIncompatibilityB n)
      vertices left right = true) :
    CanonicalIncompatibilityPath n left.atom right.atom :=
  dWalkToCanonicalPath
    (warshallSound (bipartiteIncompatibilityB n)
      vertices left right hreaches)

/-! ## 4. Endpoint separation is paid by repeated path cost -/

theorem canonicalIncompatibilityPath_cost_floor
    {n : Nat} {left right : CanonicalAtom n}
    (path : CanonicalIncompatibilityPath n left right) :
    ∀ {start finish : Nat}, start ∈ left.val → finish ∈ right.val →
      linfDist (boxPlaquetteAt n start)
          (boxPlaquetteAt n finish) + 1 ≤ path.cost := by
  induction path with
  | refl atom =>
      intro start finish hstart hfinish
      exact canonicalSurfacePolymer_linf_size_floor
        atom.property hstart
        (List.mem_map.mpr ⟨finish, hfinish, rfl⟩)
        (Nat.le_refl _)
  | @edge left right hincompatible =>
      intro start finish hstart hfinish
      obtain ⟨leftFace, hleftFace, rightFace, hrightFace, hcontact⟩ :=
        canonicalPolymer_incompatible_contact hincompatible
      have hleft :
          linfDist (boxPlaquetteAt n start)
              (boxPlaquetteAt n leftFace) + 1 ≤ left.val.length :=
        canonicalSurfacePolymer_linf_size_floor
          left.property hstart
          (List.mem_map.mpr ⟨leftFace, hleftFace, rfl⟩)
          (Nat.le_refl _)
      have hright :
          linfDist (boxPlaquetteAt n rightFace)
              (boxPlaquetteAt n finish) + 1 ≤ right.val.length :=
        canonicalSurfacePolymer_linf_size_floor
          right.property hrightFace
          (List.mem_map.mpr ⟨finish, hfinish, rfl⟩)
          (Nat.le_refl _)
      have hedge := incompatible_contact_linfDist_le_one hcontact
      have htriFirst :
          linfDist (boxPlaquetteAt n start)
              (boxPlaquetteAt n rightFace) ≤
            linfDist (boxPlaquetteAt n start)
                (boxPlaquetteAt n leftFace) +
              linfDist (boxPlaquetteAt n leftFace)
                (boxPlaquetteAt n rightFace) := by
        exact z4SepLinf.dist_triangle _ _ _
      have htriSecond :
          linfDist (boxPlaquetteAt n start)
              (boxPlaquetteAt n finish) ≤
            linfDist (boxPlaquetteAt n start)
                (boxPlaquetteAt n rightFace) +
              linfDist (boxPlaquetteAt n rightFace)
                (boxPlaquetteAt n finish) := by
        exact z4SepLinf.dist_triangle _ _ _
      change linfDist (boxPlaquetteAt n start)
          (boxPlaquetteAt n finish) + 1 ≤
        left.val.length + right.val.length
      omega
  | @trans left middle right first second ihFirst ihSecond =>
      intro start finish hstart hfinish
      obtain ⟨middleFace, hmiddleFace⟩ :=
        canonicalSurfacePolymers_allNonempty n middle.val middle.property
      have hfirst := ihFirst hstart hmiddleFace
      have hsecond := ihSecond hmiddleFace hfinish
      have htri :
          linfDist (boxPlaquetteAt n start)
              (boxPlaquetteAt n finish) ≤
            linfDist (boxPlaquetteAt n start)
                (boxPlaquetteAt n middleFace) +
              linfDist (boxPlaquetteAt n middleFace)
                (boxPlaquetteAt n finish) := by
        exact z4SepLinf.dist_triangle _ _ _
      change linfDist (boxPlaquetteAt n start)
          (boxPlaquetteAt n finish) + 1 ≤
        first.cost + second.cost
      omega

theorem warshallCanonicalPath_cost_floor
    {n : Nat} (vertices : List (BipartiteVertex n))
    (left right : BipartiteVertex n)
    (hreaches : warshall (bipartiteIncompatibilityB n)
      vertices left right = true)
    {start finish : Nat}
    (hstart : start ∈ left.atom.val)
    (hfinish : finish ∈ right.atom.val) :
    linfDist (boxPlaquetteAt n start)
        (boxPlaquetteAt n finish) + 1 ≤
      (warshallCanonicalPath vertices left right hreaches).cost :=
  canonicalIncompatibilityPath_cost_floor _ hstart hfinish

/-- A Warshall-connected endpoint outside an expanded box forces the repeated
path cost to begin at grade `distance + 2`. -/
theorem warshallCanonicalPath_outside_box_cost_floor
    {n : Nat} (vertices : List (BipartiteVertex n))
    (left right : BipartiteVertex n)
    (hreaches : warshall (bipartiteIncompatibilityB n)
      vertices left right = true)
    {start finish inner distance : Nat}
    (hstart : start ∈ left.atom.val)
    (hfinish : finish ∈ right.atom.val)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hout : outsideBoxB (inner + distance)
      (boxPlaquetteAt n finish) = true) :
    distance + 2 ≤
      (warshallCanonicalPath vertices left right hreaches).cost := by
  have hsep := outside_expanded_box_linf_floor hstartInner hout
  have hcost := warshallCanonicalPath_cost_floor
    vertices left right hreaches hstart hfinish
  omega

end YMGap.Continuum.Z4CanonicalBipartitePath

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalBipartitePath.bipartiteIncompatibilityB_symm
#print axioms YMGap.Continuum.Z4CanonicalBipartitePath.warshallSound
#print axioms YMGap.Continuum.Z4CanonicalBipartitePath.warshall_trans_of_mem
#print axioms YMGap.Continuum.Z4CanonicalBipartitePath.warshall_map_equiv
#print axioms YMGap.Continuum.Z4CanonicalBipartitePath.dWalkToCanonicalPath
#print axioms YMGap.Continuum.Z4CanonicalBipartitePath.canonicalIncompatibilityPath_cost_floor
#print axioms YMGap.Continuum.Z4CanonicalBipartitePath.warshallCanonicalPath_cost_floor
#print axioms YMGap.Continuum.Z4CanonicalBipartitePath.warshallCanonicalPath_outside_box_cost_floor
