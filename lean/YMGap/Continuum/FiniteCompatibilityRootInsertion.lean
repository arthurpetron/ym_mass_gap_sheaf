/-
# Weighted insertion of one root into a finite compatibility gas

Let `deleted` be a duplicate-free sub-ambient all of whose atoms are
compatible with a distinguished root.  Every compatible family in `deleted`
can be augmented by the root and then reordered by filtering the original
ambient enumeration.  This gives a weight-preserving injection into the
root-occurrence event and hence

  weight(root) * Z(deleted) <= occurrenceNumerator(root).

The argument is entirely finite and constructive.  Ambient ordering is used
to make the encoding literally injective on lists rather than only up to
permutation.
-/

import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.Z4CanonicalPolymerUniverse

namespace YMGap.Continuum.FiniteCompatibilityRootInsertion

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4CanonicalPolymerUniverse

local infix:50 " ≈ " => Q'.eqv

variable {A : Type} [DecidableEq A]

/-- Add the root set-theoretically and restore the unique ambient order. -/
def orderedRootInsertion (ambient : List A) (root : A)
    (family : List A) : List A :=
  ambient.filter (memberB (root :: family))

theorem mem_orderedRootInsertion_iff
    (ambient : List A) (root : A) (family : List A) (atom : A) :
    atom ∈ orderedRootInsertion ambient root family ↔
      atom ∈ ambient ∧ (atom = root ∨ atom ∈ family) := by
  unfold orderedRootInsertion
  rw [List.mem_filter]
  simp only [memberB_eq_true_iff, List.mem_cons]

/-- A product of single-atom weights depends only on the permutation class of
the family list. -/
theorem familyWeight_perm (weight : A → Q') :
    ∀ {left right : List A}, left.Perm right →
      familyWeight weight left ≈ familyWeight weight right
  | _, _, List.Perm.nil => Q'.eqv_refl 1
  | _, _, List.Perm.cons _ hperm =>
      Q'.mul_eqv_congr_left _ _ _ (familyWeight_perm weight hperm)
  | _, _, List.Perm.swap first second rest => by
      change weight second * (weight first * familyWeight weight rest) ≈
        weight first * (weight second * familyWeight weight rest)
      refine Q'.eqv_trans _
        ((weight second * weight first) * familyWeight weight rest) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((weight first * weight second) * familyWeight weight rest) _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_comm_eqv (weight second) (weight first))) ?_
      exact Q'.mul_assoc_eqv _ _ _
  | _, _, List.Perm.trans first second =>
      Q'.eqv_trans _ _ _
        (familyWeight_perm weight first)
        (familyWeight_perm weight second)

private theorem listQSum_mul_left (factor : Q') (value : B → Q') :
    ∀ xs : List B,
      listQSum (fun item => factor * value item) xs ≈
        factor * listQSum value xs
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv factor)
  | head :: tail => by
      change factor * value head +
          listQSum (fun item => factor * value item) tail ≈
        factor * (value head + listQSum value tail)
      exact Q'.eqv_trans _
        (factor * value head + factor * listQSum value tail) _
        (Q'.add_eqv_congr_left _ _ _
          (listQSum_mul_left factor value tail))
        (Q'.eqv_symm (Q'.mul_add_eqv factor _ _))

/-- Weighted root insertion.  The hypotheses state exactly that `deleted` is
a duplicate-free sub-ambient, excludes the root, and consists only of atoms
compatible with the root. -/
theorem root_weight_mul_partition_le_occurrenceNumerator
    (compat : A → A → Bool)
    (hsymm : ∀ left right, compat left right = compat right left)
    (weight : A → Q') (hweight : ∀ atom, (0 : Q') ≤ weight atom)
    (ambient deleted : List A) (root : A)
    (hambient : ambient.Nodup) (hdeleted : deleted.Nodup)
    (hrootAmbient : root ∈ ambient) (hrootDeleted : root ∉ deleted)
    (hdeletedSource : ∀ atom, atom ∈ deleted → atom ∈ ambient)
    (hrootCompat : ∀ atom, atom ∈ deleted → compat root atom = true) :
    weight root * partition compat weight deleted ≤
      eventNumerator compat weight ambient
        (fun family => memberB family root) := by
  let source := compatibleFamilies compat deleted
  let target := (compatibleFamilies compat ambient).filter
    (fun family => memberB family root)
  let encode := orderedRootInsertion ambient root
  have hsourceNodup : source.Nodup := by
    unfold source compatibleFamilies
    exact List.filter_sublist.nodup (sublists_nodup deleted hdeleted)
  have hinjection :
      listQSum (fun family => weight root * familyWeight weight family) source ≤
        listQSum (familyWeight weight) target := by
    apply listQSum_le_of_injective source target
      (fun family => weight root * familyWeight weight family)
      (familyWeight weight) encode hsourceNodup
    · intro family hfamily
      have hparts : family ∈ sublists deleted ∧
          familyCompatibleB compat family = true := by
        exact List.mem_filter.mp hfamily
      have hencodedCompat :
          familyCompatibleB compat (encode family) = true := by
        apply familyCompatibleB_of_pairwise compat
          (List.filter_sublist.nodup hambient)
        intro left hleft right hright hne
        have hleftRaw :=
          (mem_orderedRootInsertion_iff ambient root family left).mp hleft
        have hrightRaw :=
          (mem_orderedRootInsertion_iff ambient root family right).mp hright
        rcases hleftRaw.2 with hleftRoot | hleftFamily
        · subst left
          rcases hrightRaw.2 with hrightRoot | hrightFamily
          · subst right
            exact False.elim (hne rfl)
          · exact hrootCompat right
              (mem_of_mem_sublists deleted family hparts.1
                right hrightFamily)
        · rcases hrightRaw.2 with hrightRoot | hrightFamily
          · subst right
            rw [hsymm]
            exact hrootCompat left
              (mem_of_mem_sublists deleted family hparts.1
                left hleftFamily)
          · exact familyCompatibleB_pairwise compat hsymm hparts.2
              hleftFamily hrightFamily hne
      have htargetFamily : encode family ∈
          compatibleFamilies compat ambient := by
        unfold compatibleFamilies
        apply List.mem_filter.mpr
        exact ⟨filter_mem_sublists _ _, hencodedCompat⟩
      have hrootEncoded : root ∈ encode family :=
        (mem_orderedRootInsertion_iff ambient root family root).2
          ⟨hrootAmbient, Or.inl rfl⟩
      unfold target
      apply List.mem_filter.mpr
      exact ⟨htargetFamily,
        (memberB_eq_true_iff (encode family) root).2 hrootEncoded⟩
    · intro left hleft right hright heq
      have hleftParts : left ∈ sublists deleted ∧
          familyCompatibleB compat left = true :=
        List.mem_filter.mp hleft
      have hrightParts : right ∈ sublists deleted ∧
          familyCompatibleB compat right = true :=
        List.mem_filter.mp hright
      apply sublists_eq_of_mem_iff deleted left right hdeleted
        hleftParts.1 hrightParts.1
      intro atom
      constructor
      · intro hatomLeft
        have hatomDeleted := mem_of_mem_sublists deleted left
          hleftParts.1 atom hatomLeft
        have hatomEncoded : atom ∈ encode left :=
          (mem_orderedRootInsertion_iff ambient root left atom).2
            ⟨hdeletedSource atom hatomDeleted, Or.inr hatomLeft⟩
        rw [heq] at hatomEncoded
        have hraw :=
          (mem_orderedRootInsertion_iff ambient root right atom).1
            hatomEncoded
        rcases hraw.2 with hroot | hatomRight
        · subst atom
          exact False.elim (hrootDeleted hatomDeleted)
        · exact hatomRight
      · intro hatomRight
        have hatomDeleted := mem_of_mem_sublists deleted right
          hrightParts.1 atom hatomRight
        have hatomEncoded : atom ∈ encode right :=
          (mem_orderedRootInsertion_iff ambient root right atom).2
            ⟨hdeletedSource atom hatomDeleted, Or.inr hatomRight⟩
        rw [← heq] at hatomEncoded
        have hraw :=
          (mem_orderedRootInsertion_iff ambient root left atom).1
            hatomEncoded
        rcases hraw.2 with hroot | hatomLeft
        · subst atom
          exact False.elim (hrootDeleted hatomDeleted)
        · exact hatomLeft
    · intro family hfamily
      have hparts : family ∈ sublists deleted ∧
          familyCompatibleB compat family = true :=
        List.mem_filter.mp hfamily
      have hfamilyNodup : family.Nodup := by
        have hfiltered : (deleted.filter (memberB family)).Nodup :=
          List.filter_sublist.nodup hdeleted
        rw [filter_memberB_eq_of_mem_sublists hdeleted hparts.1]
          at hfiltered
        exact hfiltered
      have hrootNotFamily : root ∉ family := by
        intro hrootFamily
        exact hrootDeleted
          (mem_of_mem_sublists deleted family hparts.1 root hrootFamily)
      have hrawNodup : (root :: family).Nodup :=
        List.nodup_cons.mpr ⟨hrootNotFamily, hfamilyNodup⟩
      have hperm : (root :: family).Perm (encode family) := by
        apply perm_of_nodup_mem_iff (root :: family) (encode family)
          hrawNodup (List.filter_sublist.nodup hambient)
        intro atom
        constructor
        · intro hraw
          apply (mem_orderedRootInsertion_iff
            ambient root family atom).2
          refine ⟨?_, List.mem_cons.mp hraw⟩
          rcases List.mem_cons.mp hraw with hroot | hfamilyAtom
          · subst atom
            exact hrootAmbient
          · exact hdeletedSource atom
              (mem_of_mem_sublists deleted family hparts.1
                atom hfamilyAtom)
        · intro hencoded
          exact List.mem_cons.mpr
            ((mem_orderedRootInsertion_iff
              ambient root family atom).1 hencoded |>.2)
      exact Q'.le_of_eqv (familyWeight_perm weight hperm)
    · intro family _
      exact familyWeight_nonnegative weight hweight family
  unfold source at hinjection
  unfold target at hinjection
  unfold partition eventNumerator
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (listQSum_mul_left (weight root) (familyWeight weight)
        (compatibleFamilies compat deleted)))
    hinjection

end YMGap.Continuum.FiniteCompatibilityRootInsertion

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.FiniteCompatibilityRootInsertion.orderedRootInsertion
#print axioms YMGap.Continuum.FiniteCompatibilityRootInsertion.mem_orderedRootInsertion_iff
#print axioms YMGap.Continuum.FiniteCompatibilityRootInsertion.familyWeight_perm
#print axioms YMGap.Continuum.FiniteCompatibilityRootInsertion.root_weight_mul_partition_le_occurrenceNumerator
