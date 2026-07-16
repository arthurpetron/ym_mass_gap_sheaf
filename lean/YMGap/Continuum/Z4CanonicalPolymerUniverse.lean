/-
# A finite universe for the canonical Z4 surface polymers

The exact connected-surface gas is flattened and duplicate-erased to produce a
finite ambient list of polymers.  A corrected Boolean compatibility test checks
both face disjointness and actual shared-link separation.  Every exact gas
family embeds into the filtered power set of this ambient list after putting
its members in ambient order, and that reordering preserves its exact rational
activity.

The converse range theorem (every corrected-compatible ambient subfamily comes
from one support) is deliberately left as the next theorem, not assumed here.
-/

import YMGap.Continuum.Z4CanonicalConnectedSurfaceGas

namespace YMGap.Continuum.Z4CanonicalPolymerUniverse

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4PhysicalSurfaceComponents

local infix:50 " ≈ " => Q'.eqv

def decodeFlatMapMember {A B : Type} [DecidableEq B]
    (f : A → List B) :
    ∀ (xs : List A) (value : B), value ∈ xs.flatMap f →
      Σ' source : A, (source ∈ xs) ×' (value ∈ f source)
  | [], value, hmem => absurd hmem List.not_mem_nil
  | head :: tail, value, hmem => by
      by_cases hhead : value ∈ f head
      · exact ⟨head, List.mem_cons_self, hhead⟩
      · have hsplit : value ∈ f head ++ tail.flatMap f := hmem
        have htail : value ∈ tail.flatMap f :=
          (List.mem_append.mp hsplit).resolve_left hhead
        obtain ⟨source, hsource, hvalue⟩ :=
          decodeFlatMapMember f tail value htail
        exact ⟨source, List.mem_cons_of_mem head hsource, hvalue⟩

private theorem filtered_eraseDups_nodup {A : Type}
    [BEq A] [LawfulBEq A] (xs : List A) :
    ∀ predicate : A → Bool, (xs.filter predicate).eraseDups.Nodup := by
  induction xs with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons head tail ih =>
      intro predicate
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr
          ⟨?_, ih (fun item => (!(item == head)) && predicate item)⟩
        intro hmem
        have hmem' : head ∈ tail.filter
            (fun item => (!(item == head)) && predicate item) :=
          List.mem_eraseDups.mp hmem
        have hfalse := (List.mem_filter.mp hmem').2
        have hself : (head == head) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact ih predicate

private theorem filter_true_local {A : Type} :
    ∀ xs : List A, xs.filter (fun _ => true) = xs
  | [] => rfl
  | head :: tail =>
      congrArg (List.cons head) (filter_true_local tail)

private theorem eraseDups_nodup_local {A : Type}
    [BEq A] [LawfulBEq A] (xs : List A) : xs.eraseDups.Nodup := by
  have h := filtered_eraseDups_nodup xs (fun _ => true)
  rw [filter_true_local] at h
  exact h

/-! ## 1. The finite ambient polymer list -/

def rawCanonicalSurfacePolymers (n : Nat) : List (List Nat) :=
  (canonicalConnectedSurfaceGas n).flatMap (fun family => family)

def canonicalSurfacePolymers (n : Nat) : List (List Nat) :=
  (rawCanonicalSurfacePolymers n).eraseDups

theorem canonicalSurfacePolymers_nodup (n : Nat) :
    (canonicalSurfacePolymers n).Nodup := by
  unfold canonicalSurfacePolymers
  exact eraseDups_nodup_local _

theorem mem_canonicalSurfacePolymers_iff
    {n : Nat} {polymer : List Nat} :
    polymer ∈ canonicalSurfacePolymers n ↔
      ∃ family, family ∈ canonicalConnectedSurfaceGas n ∧
        polymer ∈ family := by
  unfold canonicalSurfacePolymers rawCanonicalSurfacePolymers
  simp only [List.mem_eraseDups, List.mem_flatMap]

def decodeCanonicalSurfacePolymerMember
    {n : Nat} (polymer : List Nat)
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    Σ' family : List (List Nat),
      (family ∈ canonicalConnectedSurfaceGas n) ×'
        (polymer ∈ family) := by
  have hraw : polymer ∈ rawCanonicalSurfacePolymers n :=
    List.mem_eraseDups.mp hpolymer
  unfold rawCanonicalSurfacePolymers at hraw
  exact decodeFlatMapMember (fun family : List (List Nat) => family)
    (canonicalConnectedSurfaceGas n) polymer hraw

def canonicalSurfacePolymers_allNonempty (n : Nat) :
    AllNonempty (canonicalSurfacePolymers n) := by
  intro polymer hpolymer
  obtain ⟨family, hfamily, hmember⟩ :=
    decodeCanonicalSurfacePolymerMember polymer hpolymer
  exact (canonicalConnectedSurfaceGas_correctedCompatibility hfamily).1
    polymer hmember

def canonicalSurfacePolymers_allConnected (n : Nat) :
    AllConnected (faceLinkAdjacentB n) (canonicalSurfacePolymers n) := by
  intro polymer hpolymer
  obtain ⟨family, hfamily, hmember⟩ :=
    decodeCanonicalSurfacePolymerMember polymer hpolymer
  exact (canonicalConnectedSurfaceGas_correctedCompatibility hfamily).2.1
    polymer hmember

theorem canonicalSurfacePolymer_mem_faceSupports
    {n : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    polymer ∈ cutoffOneFaceSupports n := by
  obtain ⟨family, hfamily, hmember⟩ :=
    (mem_canonicalSurfacePolymers_iff.mp hpolymer)
  obtain ⟨support, _, hfamilyEq⟩ := List.mem_map.mp hfamily
  rw [← hfamilyEq] at hmember
  exact canonicalSurfaceFamily_members_are_faceSupports n support
    polymer hmember

theorem gasFamily_member_mem_canonicalSurfacePolymers
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalConnectedSurfaceGas n)
    {polymer : List Nat} (hpolymer : polymer ∈ family) :
    polymer ∈ canonicalSurfacePolymers n := by
  apply mem_canonicalSurfacePolymers_iff.mpr
  exact ⟨family, hfamily, hpolymer⟩

/-! ## 2. Corrected Boolean compatibility -/

def canonicalPolymerCompatibleB (n : Nat)
    (left right : List Nat) : Bool :=
  left.all (fun leftFace =>
    right.all (fun rightFace =>
      !(decide (leftFace = rightFace)) &&
        !(faceLinkAdjacentB n leftFace rightFace)))

def canonicalFamilyCompatibleB (n : Nat) : List (List Nat) → Bool
  | [] => true
  | head :: tail =>
      tail.all (canonicalPolymerCompatibleB n head) &&
        canonicalFamilyCompatibleB n tail

theorem canonicalPolymerCompatibleB_true_of
    {n : Nat} {left right : List Nat}
    (hdisjoint : SupportsDisjoint left right)
    (hseparated : SupportsSeparated (faceLinkAdjacentB n) left right) :
    canonicalPolymerCompatibleB n left right = true := by
  unfold canonicalPolymerCompatibleB
  apply List.all_eq_true.mpr
  intro leftFace hleftFace
  apply List.all_eq_true.mpr
  intro rightFace hrightFace
  have hne : leftFace ≠ rightFace := by
    intro heq
    subst rightFace
    exact hdisjoint leftFace hleftFace hrightFace
  have hadj := hseparated leftFace hleftFace rightFace hrightFace
  simp [hne, hadj]

theorem canonicalFamilyCompatibleB_true
    (n : Nat) : ∀ family : List (List Nat),
    family.Nodup → DistinctDisjoint family →
      DistinctSeparated (faceLinkAdjacentB n) family →
        canonicalFamilyCompatibleB n family = true
  | [], _, _, _ => rfl
  | head :: tail, hnodup, hdisjoint, hseparated => by
      have hparts := List.nodup_cons.mp hnodup
      have hheadAll : tail.all (canonicalPolymerCompatibleB n head) = true := by
        apply List.all_eq_true.mpr
        intro component hcomponent
        have hne : head ≠ component := by
          intro heq
          subst component
          exact hparts.1 hcomponent
        exact canonicalPolymerCompatibleB_true_of
          (hdisjoint head List.mem_cons_self component
            (List.mem_cons_of_mem head hcomponent) hne)
          (hseparated head List.mem_cons_self component
            (List.mem_cons_of_mem head hcomponent) hne)
      have htailDisjoint : DistinctDisjoint tail := by
        intro left hleft right hright hne
        exact hdisjoint left (List.mem_cons_of_mem head hleft)
          right (List.mem_cons_of_mem head hright) hne
      have htailSeparated :
          DistinctSeparated (faceLinkAdjacentB n) tail := by
        intro left hleft right hright hne
        exact hseparated left (List.mem_cons_of_mem head hleft)
          right (List.mem_cons_of_mem head hright) hne
      simp only [canonicalFamilyCompatibleB, hheadAll, Bool.true_and]
      exact canonicalFamilyCompatibleB_true n tail hparts.2
        htailDisjoint htailSeparated

/-! ## 3. Ambient-order embeddings of every exact gas family -/

def ambientOrderedFamily (n : Nat) (family : List (List Nat)) :
    List (List Nat) :=
  (canonicalSurfacePolymers n).filter
    (fun polymer => decide (polymer ∈ family))

theorem mem_ambientOrderedFamily_iff
    (n : Nat) (family : List (List Nat)) (polymer : List Nat) :
    polymer ∈ ambientOrderedFamily n family ↔
      polymer ∈ canonicalSurfacePolymers n ∧ polymer ∈ family := by
  unfold ambientOrderedFamily
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]

theorem gasFamily_mem_ambientOrderedFamily_iff
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalConnectedSurfaceGas n)
    (polymer : List Nat) :
    polymer ∈ ambientOrderedFamily n family ↔ polymer ∈ family := by
  rw [mem_ambientOrderedFamily_iff]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨gasFamily_member_mem_canonicalSurfacePolymers hfamily h, h⟩

theorem ambientOrderedFamily_nodup (n : Nat)
    (family : List (List Nat)) :
    (ambientOrderedFamily n family).Nodup := by
  unfold ambientOrderedFamily
  exact List.filter_sublist.nodup (canonicalSurfacePolymers_nodup n)

theorem gasFamily_ambientOrdered_compatible
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalConnectedSurfaceGas n) :
    canonicalFamilyCompatibleB n (ambientOrderedFamily n family) = true := by
  let facts := canonicalConnectedSurfaceGas_correctedCompatibility hfamily
  have horderedDisjoint : DistinctDisjoint (ambientOrderedFamily n family) := by
    intro left hleft right hright hne
    exact facts.2.2.1 left
      ((gasFamily_mem_ambientOrderedFamily_iff hfamily left).1 hleft)
      right ((gasFamily_mem_ambientOrderedFamily_iff hfamily right).1 hright)
      hne
  have horderedSeparated :
      DistinctSeparated (faceLinkAdjacentB n)
        (ambientOrderedFamily n family) := by
    intro left hleft right hright hne
    exact facts.2.2.2 left
      ((gasFamily_mem_ambientOrderedFamily_iff hfamily left).1 hleft)
      right ((gasFamily_mem_ambientOrderedFamily_iff hfamily right).1 hright)
      hne
  exact canonicalFamilyCompatibleB_true n (ambientOrderedFamily n family)
    (ambientOrderedFamily_nodup n family)
    horderedDisjoint horderedSeparated

def canonicalCompatibleAmbientFamilies (n : Nat) :
    List (List (List Nat)) :=
  (sublists (canonicalSurfacePolymers n)).filter
    (canonicalFamilyCompatibleB n)

theorem gasFamily_ambientOrdered_mem_compatibleFamilies
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalConnectedSurfaceGas n) :
    ambientOrderedFamily n family ∈
      canonicalCompatibleAmbientFamilies n := by
  unfold canonicalCompatibleAmbientFamilies
  apply List.mem_filter.mpr
  exact ⟨filter_mem_sublists _ _,
    gasFamily_ambientOrdered_compatible hfamily⟩

/-! ## 4. Reordering preserves the exact family activity -/

theorem perm_of_nodup_mem_iff {A : Type} [DecidableEq A] :
    ∀ (xs ys : List A), xs.Nodup → ys.Nodup →
      (∀ item, item ∈ xs ↔ item ∈ ys) → xs.Perm ys
  | [], [], _, _, _ => List.Perm.nil
  | [], head :: tail, _, _, hmem => by
      have hfalse : head ∈ ([] : List A) :=
        (hmem head).2 List.mem_cons_self
      cases hfalse
  | head :: tail, ys, hxs, hys, hmem => by
      have hparts := List.nodup_cons.mp hxs
      have hheadYs : head ∈ ys := (hmem head).1 List.mem_cons_self
      obtain ⟨before, after, hsplit⟩ := List.append_of_mem hheadYs
      subst ys
      have hmiddle : (head :: (before ++ after)).Perm
          (before ++ head :: after) := List.perm_middle.symm
      have hmiddleNodup : (head :: (before ++ after)).Nodup :=
        hmiddle.symm.nodup hys
      have hmiddleParts := List.nodup_cons.mp hmiddleNodup
      have htailMem : ∀ item, item ∈ tail ↔ item ∈ before ++ after := by
        intro item
        constructor
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hparts.1 hitem
          have hy := (hmem item).1 (List.mem_cons_of_mem head hitem)
          rcases List.mem_append.mp hy with hbefore | hrest
          · exact List.mem_append_left after hbefore
          · exact List.mem_append_right before
              ((List.mem_cons.mp hrest).resolve_left hne)
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hmiddleParts.1 hitem
          have hy : item ∈ before ++ head :: after := by
            rcases List.mem_append.mp hitem with hbefore | hafter
            · exact List.mem_append_left (head :: after) hbefore
            · exact List.mem_append_right before
                (List.mem_cons_of_mem head hafter)
          exact (List.mem_cons.mp ((hmem item).2 hy)).resolve_left hne
      have htailPerm := perm_of_nodup_mem_iff tail (before ++ after)
        hparts.2 hmiddleParts.2 htailMem
      exact (List.Perm.cons head htailPerm).trans hmiddle

theorem gasFamily_perm_ambientOrdered
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalConnectedSurfaceGas n) :
    family.Perm (ambientOrderedFamily n family) := by
  obtain ⟨support, _, hfamilyEq⟩ := List.mem_map.mp hfamily
  have hfamilyNodup : family.Nodup := by
    rw [← hfamilyEq]
    exact canonicalSurfaceFamily_nodup n support
  apply perm_of_nodup_mem_iff family (ambientOrderedFamily n family)
    hfamilyNodup (ambientOrderedFamily_nodup n family)
  intro polymer
  exact (gasFamily_mem_ambientOrderedFamily_iff hfamily polymer).symm

theorem canonicalSurfaceFamilyActivity_perm (w : Q') (n : Nat) :
    ∀ {left right : List (List Nat)}, left.Perm right →
      canonicalSurfaceFamilyActivity w n left ≈
        canonicalSurfaceFamilyActivity w n right
  | _, _, List.Perm.nil => Q'.eqv_refl 1
  | _, _, List.Perm.cons _ hperm =>
      Q'.mul_eqv_congr_left _ _ _
        (canonicalSurfaceFamilyActivity_perm w n hperm)
  | _, _, List.Perm.swap first second rest => by
      change canonicalSurfaceActivity w n second *
          (canonicalSurfaceActivity w n first *
            canonicalSurfaceFamilyActivity w n rest) ≈
        canonicalSurfaceActivity w n first *
          (canonicalSurfaceActivity w n second *
            canonicalSurfaceFamilyActivity w n rest)
      refine Q'.eqv_trans _
        ((canonicalSurfaceActivity w n second *
            canonicalSurfaceActivity w n first) *
          canonicalSurfaceFamilyActivity w n rest) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((canonicalSurfaceActivity w n first *
            canonicalSurfaceActivity w n second) *
          canonicalSurfaceFamilyActivity w n rest) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
  | _, _, List.Perm.trans first second =>
      Q'.eqv_trans _ _ _
        (canonicalSurfaceFamilyActivity_perm w n first)
        (canonicalSurfaceFamilyActivity_perm w n second)

theorem gasFamilyActivity_eqv_ambientOrdered
    (w : Q') {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalConnectedSurfaceGas n) :
    canonicalSurfaceFamilyActivity w n family ≈
      canonicalSurfaceFamilyActivity w n
        (ambientOrderedFamily n family) :=
  canonicalSurfaceFamilyActivity_perm w n
    (gasFamily_perm_ambientOrdered hfamily)

end YMGap.Continuum.Z4CanonicalPolymerUniverse

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalPolymerUniverse.canonicalSurfacePolymers_nodup
#print axioms YMGap.Continuum.Z4CanonicalPolymerUniverse.canonicalSurfacePolymers_allNonempty
#print axioms YMGap.Continuum.Z4CanonicalPolymerUniverse.canonicalSurfacePolymers_allConnected
#print axioms YMGap.Continuum.Z4CanonicalPolymerUniverse.canonicalFamilyCompatibleB_true
#print axioms YMGap.Continuum.Z4CanonicalPolymerUniverse.gasFamily_ambientOrdered_mem_compatibleFamilies
#print axioms YMGap.Continuum.Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff
#print axioms YMGap.Continuum.Z4CanonicalPolymerUniverse.gasFamily_perm_ambientOrdered
#print axioms YMGap.Continuum.Z4CanonicalPolymerUniverse.gasFamilyActivity_eqv_ambientOrdered
