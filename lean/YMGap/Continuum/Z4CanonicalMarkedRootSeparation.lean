/-
# Separated and connected branches for a finite marked cylinder

The simultaneous marked-component switch has the same geometric dichotomy as
the singleton switch.  If none of the marked components reaches an outside
left-family polymer, the switched left family stays in the boundary cell and
the switched right family stays embedded.  Otherwise a concrete marked root
and an outside endpoint are retained, with exact disagreement reachability.
-/

import YMGap.Continuum.Z4CanonicalMarkedRootSwitch

namespace YMGap.Continuum.Z4CanonicalMarkedRootSeparation

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteDisagreementReverseRecovery
open YMGap.Continuum.FiniteMarkedRootSwitch
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalMarkedRootSwitch
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteBoxExhaustion

local infix:50 " ≈ " => Q'.eqv

/-- Does some marked disagreement component meet an outside polymer in the
left boundary family? -/
def boundaryOutsideMarkedReachB
    {n : Nat} (small : Nat) {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) : Bool :=
  (canonicalFamilyAtoms hleft).any (fun atom =>
    (!(polymerInsideBoxB small n atom.val)) &&
      canonicalMarkedCut hleft hright roots atom)

theorem boundaryOutsideMarkedReachB_false_separated
    {small n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n))
    (hreach : boundaryOutsideMarkedReachB small hleft hright roots = false) :
    ∀ atom : CanonicalAtom n, atom.val ∈ left →
      polymerInsideBoxB small n atom.val = false →
        canonicalMarkedCut hleft hright roots atom = false := by
  intro atom hatom houtside
  cases hcut : canonicalMarkedCut hleft hright roots atom with
  | false => rfl
  | true =>
      have hatomList : atom ∈ canonicalFamilyAtoms hleft :=
        (canonicalFamilyAtom_mem_iff hleft atom).2 hatom
      have hterm :
          ((!(polymerInsideBoxB small n atom.val)) &&
            canonicalMarkedCut hleft hright roots atom) = true := by
        simp [houtside, hcut]
      have hany : (canonicalFamilyAtoms hleft).any (fun found =>
          (!(polymerInsideBoxB small n found.val)) &&
            canonicalMarkedCut hleft hright roots found) = true :=
        List.any_eq_true.mpr ⟨atom, hatomList, hterm⟩
      unfold boundaryOutsideMarkedReachB at hreach
      rw [hreach] at hany
      exact False.elim (Bool.false_ne_true hany)

theorem boundaryOutsideMarkedReachB_true_witness
    {small n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n))
    (hreach : boundaryOutsideMarkedReachB small hleft hright roots = true) :
    ∃ outside : CanonicalAtom n,
      outside.val ∈ left ∧
        polymerInsideBoxB small n outside.val = false ∧
          canonicalMarkedCut hleft hright roots outside = true := by
  unfold boundaryOutsideMarkedReachB at hreach
  obtain ⟨outside, houtsideAtoms, hterm⟩ := List.any_eq_true.mp hreach
  have hparts := (Bool.and_eq_true _ _).mp hterm
  have houtside : polymerInsideBoxB small n outside.val = false := by
    cases hinside : polymerInsideBoxB small n outside.val <;> simp_all
  exact ⟨outside,
    (canonicalFamilyAtom_mem_iff hleft outside).1 houtsideAtoms,
    houtside, hparts.2⟩

/-- A reached point in the union cut supplies one concrete marked root. -/
theorem canonicalMarkedCut_true_has_root
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) (atom : CanonicalAtom n)
    (hcut : canonicalMarkedCut hleft hright roots atom = true) :
    ∃ root : CanonicalAtom n, root ∈ roots ∧
      canonicalDisagreementCut hleft hright root atom = true := by
  unfold canonicalMarkedCut markedRootCut at hcut
  obtain ⟨root, hroot, hreach⟩ := List.any_eq_true.mp hcut
  exact ⟨root, hroot, hreach⟩

/-- The connected branch contains a marked root-to-outside endpoint pair. -/
theorem boundaryOutsideMarkedReachB_true_root_witness
    {small n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n))
    (hreach : boundaryOutsideMarkedReachB small hleft hright roots = true) :
    ∃ root outside : CanonicalAtom n,
      root ∈ roots ∧ outside.val ∈ left ∧
        polymerInsideBoxB small n outside.val = false ∧
          canonicalDisagreementCut hleft hright root outside = true := by
  obtain ⟨outside, houtside, houtsideBox, hcut⟩ :=
    boundaryOutsideMarkedReachB_true_witness hleft hright roots hreach
  obtain ⟨root, hroot, hrootReach⟩ :=
    canonicalMarkedCut_true_has_root hleft hright roots outside hcut
  exact ⟨root, outside, hroot, houtside, houtsideBox, hrootReach⟩

/-- A nontrivial dependent walk has an edge leaving its start vertex. -/
theorem dWalk_start_edge_of_ne {A : Type} [DecidableEq A]
    (edge : A → A → Bool)
    {start finish : A} (walk : DWalk edge start finish)
    (hne : start ≠ finish) :
    ∃ next : A, edge start next = true := by
  induction walk with
  | refl vertex => exact False.elim (hne rfl)
  | edge hedge => exact ⟨_, hedge⟩
  | @trans left middle right first second ihFirst ihSecond =>
      cases hmiddle : decide (left = middle) with
      | false =>
          exact ihFirst (of_decide_eq_false hmiddle)
      | true =>
          have heq : left = middle := of_decide_eq_true hmiddle
          subst middle
          exact ihSecond hne

theorem disagreementEdge_source_exclusive
    {A : Type} [DecidableEq A] (ambient : List A)
    (compat : A → A → Bool) (left right : A → Bool)
    {first second : A}
    (hedge : disagreementEdge ambient compat left right first second = true) :
    (left first = true ∧ right first = false) ∨
      (left first = false ∧ right first = true) := by
  have hdisagreement := (Bool.and_eq_true _ _).mp hedge |>.2
  have hcross := (Bool.and_eq_true _ _).mp hdisagreement |>.1
  cases hleft : left first with
  | false =>
      cases hright : right first with
      | false =>
          simp [disagreementBits, leftOnly, rightOnly,
            hleft, hright] at hcross
      | true => exact Or.inr ⟨rfl, rfl⟩
  | true =>
      cases hright : right first with
      | false => exact Or.inl ⟨rfl, rfl⟩
      | true =>
          simp [disagreementBits, leftOnly, rightOnly,
            hleft, hright] at hcross

/-- If an inside marked root reaches an outside endpoint, it is an exclusive
occurrence in one of the two source families. -/
theorem canonicalRoot_exclusive_of_reaches_outside
    {small n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root outside : CanonicalAtom n)
    (hrootInside : polymerInsideBoxB small n root.val = true)
    (houtside : polymerInsideBoxB small n outside.val = false)
    (hreaches : canonicalDisagreementCut hleft hright root outside = true) :
    (root.val ∈ left ∧ root.val ∉ right) ∨
      (root.val ∉ left ∧ root.val ∈ right) := by
  have hne : root ≠ outside := by
    intro heq
    subst outside
    rw [hrootInside] at houtside
    exact Bool.false_ne_true houtside.symm
  have hwalk := warshallSound
    (disagreementEdge (canonicalAmbientAtoms n)
      (canonicalAtomCompatibleB n)
      (memberB (canonicalFamilyAtoms hleft))
      (memberB (canonicalFamilyAtoms hright)))
    (canonicalAmbientAtoms n) root outside hreaches
  obtain ⟨next, hedge⟩ := dWalk_start_edge_of_ne _ hwalk hne
  rcases disagreementEdge_source_exclusive _ _ _ _ hedge with
    hleftOnly | hrightOnly
  · exact Or.inl ⟨
      (canonicalFamilyAtom_mem_iff hleft root).1
        ((memberB_eq_true_iff _ _).1 hleftOnly.1),
      fun hmem => (memberB_eq_false_iff _ _).1 hleftOnly.2
        ((canonicalFamilyAtom_mem_iff hright root).2 hmem)⟩
  · exact Or.inr ⟨
      fun hmem => (memberB_eq_false_iff _ _).1 hrightOnly.1
        ((canonicalFamilyAtom_mem_iff hleft root).2 hmem),
      (canonicalFamilyAtom_mem_iff hright root).1
        ((memberB_eq_true_iff _ _).1 hrightOnly.2)⟩

theorem mem_recoverableMarkedSwitchedLeftAtoms_iff
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) (atom : CanonicalAtom n) :
    atom ∈ recoverableMarkedSwitchedLeftAtoms hleft hright roots ↔
      switchedLeftB (canonicalMarkedCut hleft hright roots)
        (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright)
        atom = true := by
  unfold recoverableMarkedSwitchedLeftAtoms
    markedRootComponentSwitchedLeft canonicalMarkedCut
    FiniteCompatibilitySwitching.switchedLeft
  constructor
  · exact fun hatom => (List.mem_filter.mp hatom).2
  · intro htest
    exact List.mem_filter.mpr
      ⟨canonicalAtom_mem_ambientAtoms atom, htest⟩

theorem mem_recoverableMarkedSwitchedRightAtoms_iff
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) (atom : CanonicalAtom n) :
    atom ∈ recoverableMarkedSwitchedRightAtoms hleft hright roots ↔
      switchedRightB (canonicalMarkedCut hleft hright roots)
        (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright)
        atom = true := by
  unfold recoverableMarkedSwitchedRightAtoms
    markedRootComponentSwitchedRight canonicalMarkedCut
    FiniteCompatibilitySwitching.switchedRight
  constructor
  · exact fun hatom => (List.mem_filter.mp hatom).2
  · intro htest
    exact List.mem_filter.mpr
      ⟨canonicalAtom_mem_ambientAtoms atom, htest⟩

theorem recoverableMarkedSwitchedRightFamily_inside_of_separated
    {small n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n))
    (hrightInside : FamilyInsideBox small n right)
    (hseparated : ∀ outside : CanonicalAtom n,
      outside.val ∈ left →
        polymerInsideBoxB small n outside.val = false →
          canonicalMarkedCut hleft hright roots outside = false) :
    FamilyInsideBox small n
      (recoverableMarkedSwitchedRightFamily hleft hright roots) := by
  intro support hsupport
  unfold recoverableMarkedSwitchedRightFamily at hsupport
  obtain ⟨atom, hatom, hatomValue⟩ := List.mem_map.mp hsupport
  subst support
  have htest := (mem_recoverableMarkedSwitchedRightAtoms_iff
    hleft hright roots atom).1 hatom
  cases hcut : canonicalMarkedCut hleft hright roots atom with
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
      cases hinside : polymerInsideBoxB small n atom.val with
      | true =>
          exact (polymerInsideBoxB_true_iff small n atom.val).1 hinside
      | false =>
          have hnotReach := hseparated atom hleftRaw hinside
          rw [hnotReach] at hcut
          exact False.elim (Bool.false_ne_true hcut)

theorem outside_support_mem_recoverableMarkedSwitchedLeft_of_separated
    {small n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n))
    {outside : List Nat} (houtside : outside ∈ left)
    (houtsideBox : polymerInsideBoxB small n outside = false)
    (hseparated : ∀ atom : CanonicalAtom n,
      atom.val ∈ left →
        polymerInsideBoxB small n atom.val = false →
          canonicalMarkedCut hleft hright roots atom = false) :
    outside ∈ recoverableMarkedSwitchedLeftFamily hleft hright roots := by
  let outsideAtom : CanonicalAtom n :=
    ⟨outside, compatibleAmbientFamily_member_ambient hleft houtside⟩
  have houtsideAtom : outsideAtom ∈ canonicalFamilyAtoms hleft :=
    (canonicalFamilyAtom_mem_iff hleft outsideAtom).2 houtside
  have hcut : canonicalMarkedCut hleft hright roots outsideAtom = false :=
    hseparated outsideAtom houtside houtsideBox
  have hleftB : memberB (canonicalFamilyAtoms hleft) outsideAtom = true :=
    (memberB_eq_true_iff _ _).2 houtsideAtom
  have houtAtoms : outsideAtom ∈
      recoverableMarkedSwitchedLeftAtoms hleft hright roots := by
    apply (mem_recoverableMarkedSwitchedLeftAtoms_iff
      hleft hright roots outsideAtom).2
    simp [switchedLeftB, hcut, hleftB]
  unfold recoverableMarkedSwitchedLeftFamily
  exact (canonicalAtom_value_mem_values_iff _ outsideAtom).2 houtAtoms

theorem recoverableMarkedSwitchedLeftFamily_mem_boundary_of_separated
    {small n : Nat} (hsmall : small ≤ n)
    {left right : List (List Nat)}
    (hleftBoundary : left ∈ boundaryTargetFamilies small n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n))
    (hseparated : ∀ atom : CanonicalAtom n,
      atom.val ∈ left →
        polymerInsideBoxB small n atom.val = false →
          canonicalMarkedCut (List.mem_filter.mp hleftBoundary).1
            hright roots atom = false) :
    recoverableMarkedSwitchedLeftFamily
        (List.mem_filter.mp hleftBoundary).1 hright roots ∈
      boundaryTargetFamilies small n := by
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
      recoverableMarkedSwitchedLeftFamily hleft hright roots :=
    outside_support_mem_recoverableMarkedSwitchedLeft_of_separated
      hleft hright roots houtside houtsideBox hseparated
  have houtCompat :=
    (recoverableMarkedSwitchedFamilies_mem_compatible
      hleft hright roots).1
  have hnotEmbedded : recoverableMarkedSwitchedLeftFamily
      hleft hright roots ∉ embeddedCompatibleFamilies small n := by
    intro hembedded
    have hinside := familyInsideBox_of_mem_embeddedCompatibleFamilies
      hsmall hembedded
    exact hplaquetteOutside
      (hinside outside houtsideOutput plaquette hplaquette)
  unfold boundaryTargetFamilies
  apply List.mem_filter.mpr
  exact ⟨houtCompat, by
    unfold embeddedFamilyB
    simp [hnotEmbedded]⟩

theorem recoverableMarkedSwitchedRightFamily_mem_embedded_of_separated
    {small n : Nat} (hsmall : small ≤ n)
    {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hrightEmbedded : right ∈ embeddedCompatibleFamilies small n)
    (roots : List (CanonicalAtom n))
    (hseparated : ∀ atom : CanonicalAtom n,
      atom.val ∈ left →
        polymerInsideBoxB small n atom.val = false →
          canonicalMarkedCut hleft
            (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
            roots atom = false) :
    recoverableMarkedSwitchedRightFamily hleft
        (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
        roots ∈ embeddedCompatibleFamilies small n := by
  let hright := embeddedCompatibleFamilies_member_target
    hsmall hrightEmbedded
  have hrightInside := familyInsideBox_of_mem_embeddedCompatibleFamilies
    hsmall hrightEmbedded
  have houtInside := recoverableMarkedSwitchedRightFamily_inside_of_separated
    hleft hright roots hrightInside hseparated
  have houtCompat :=
    (recoverableMarkedSwitchedFamilies_mem_compatible
      hleft hright roots).2
  exact family_mem_embeddedCompatibleFamilies_of_inside
    hsmall houtCompat houtInside

/-- Complete separated-branch switch for an arbitrary finite cylinder. -/
theorem separated_marked_boundary_cylinder_pair_switch
    (w : Q') {small n : Nat} (hsmall : small ≤ n)
    {left right : List (List Nat)}
    (hleftBoundary : left ∈ boundaryTargetFamilies small n)
    (hrightEmbedded : right ∈ embeddedCompatibleFamilies small n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool)
    (hseparated : ∀ atom : CanonicalAtom n,
      atom.val ∈ left →
        polymerInsideBoxB small n atom.val = false →
          canonicalMarkedCut
            (List.mem_filter.mp hleftBoundary).1
            (embeddedCompatibleFamilies_member_target
              hsmall hrightEmbedded) roots atom = false) :
    let hleft := (List.mem_filter.mp hleftBoundary).1
    let hright := embeddedCompatibleFamilies_member_target
      hsmall hrightEmbedded
    recoverableMarkedSwitchedLeftFamily hleft hright roots ∈
        boundaryTargetFamilies small n ∧
      recoverableMarkedSwitchedRightFamily hleft hright roots ∈
        embeddedCompatibleFamilies small n ∧
      cylinderEvent (roots.map Subtype.val) predicate
          (recoverableMarkedSwitchedLeftFamily hleft hright roots) =
        cylinderEvent (roots.map Subtype.val) predicate right ∧
      cylinderEvent (roots.map Subtype.val) predicate
          (recoverableMarkedSwitchedRightFamily hleft hright roots) =
        cylinderEvent (roots.map Subtype.val) predicate left ∧
      canonicalSurfaceFamilyActivity w n
          (recoverableMarkedSwitchedLeftFamily hleft hright roots) *
        canonicalSurfaceFamilyActivity w n
          (recoverableMarkedSwitchedRightFamily hleft hright roots) ≈
        canonicalSurfaceFamilyActivity w n left *
          canonicalSurfaceFamilyActivity w n right := by
  intro hleft hright
  have hboundary :=
    recoverableMarkedSwitchedLeftFamily_mem_boundary_of_separated
      hsmall hleftBoundary hright roots hseparated
  have hembedded :=
    recoverableMarkedSwitchedRightFamily_mem_embedded_of_separated
      hsmall hleft hrightEmbedded roots hseparated
  have hevents := recoverableMarkedSwitchedFamilies_cylinderEvent_swap
    hleft hright roots predicate
  have hweight := recoverableMarkedSwitchedFamilies_weight_preserved
    w hleft hright roots
  exact ⟨hboundary, hembedded, hevents.1, hevents.2, hweight⟩

end YMGap.Continuum.Z4CanonicalMarkedRootSeparation

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalMarkedRootSeparation.boundaryOutsideMarkedReachB_false_separated
#print axioms YMGap.Continuum.Z4CanonicalMarkedRootSeparation.boundaryOutsideMarkedReachB_true_root_witness
#print axioms YMGap.Continuum.Z4CanonicalMarkedRootSeparation.canonicalRoot_exclusive_of_reaches_outside
#print axioms YMGap.Continuum.Z4CanonicalMarkedRootSeparation.recoverableMarkedSwitchedLeftFamily_mem_boundary_of_separated
#print axioms YMGap.Continuum.Z4CanonicalMarkedRootSeparation.recoverableMarkedSwitchedRightFamily_mem_embedded_of_separated
#print axioms YMGap.Continuum.Z4CanonicalMarkedRootSeparation.separated_marked_boundary_cylinder_pair_switch
