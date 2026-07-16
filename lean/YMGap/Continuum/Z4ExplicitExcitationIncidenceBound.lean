/-
# A geometric incidence bound for the localized excitation product

The exact localization theorem retains only links touching an excited
plaquette.  Here those retained links are injected into the flattened four
edge boundaries of the excited plaquette entries.  Consequently their number
is at most four times the number of excited plaquettes, independently of the
ambient box volume.

This controls the number of local multiplicity factors.  It does not yet
bound the face activities or sum connected supports.
-/

import YMGap.Continuum.Z4ExplicitExcitationLocalization
import YMGap.Continuum.Z4UnitCubeEnumerationParity

namespace YMGap.Continuum.Z4ExplicitExcitationIncidenceBound

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4UnitCubeEnumerationParity

/-! ## 1. Explicit support and incidence lists -/

def excitedPlaquetteEntries (n : Nat) (physical : EdgeLabelling) :
    List (Nat × Z4Plaq) :=
  (enumerate (boxPlaquettes n)).filter
    (fun indexed => decide (1 ≤ physical indexed.1))

def excitedBoundaryLinks (n : Nat) (physical : EdgeLabelling) :
    List Z4Link :=
  (excitedPlaquetteEntries n physical).flatMap
    (fun indexed => edgesOf indexed.2)

def touchedPhysicalLinks (n : Nat) (physical : EdgeLabelling) :
    List Z4Link :=
  (distinctBoxLinks n).filter
    (fun ell => hasExcitedB physical (incidentPlaqIds n ell))

def touchedIndexedLinks (n : Nat) (physical : EdgeLabelling) :
    List (Nat × Z4Link) :=
  (enumerate (distinctBoxLinks n)).filter
    (linkTouchesExcitationB n physical)

private theorem hasExcitedB_exists_local (label : EdgeLabelling) :
    ∀ edges, hasExcitedB label edges = true →
      ∃ edge, edge ∈ edges ∧ 1 ≤ label edge
  | [], h => by cases h
  | edge :: rest, h => by
      by_cases he : 1 ≤ label edge
      · exact ⟨edge, List.mem_cons_self, he⟩
      · have hr : hasExcitedB label rest = true := by
          simpa [hasExcitedB, he] using h
        obtain ⟨found, hmem, hexcited⟩ :=
          hasExcitedB_exists_local label rest hr
        exact ⟨found, List.mem_cons_of_mem edge hmem, hexcited⟩

/-! ## 2. Every touched link occurs on an excited plaquette boundary -/

theorem touchedPhysicalLink_mem_excitedBoundary
    {n : Nat} {physical : EdgeLabelling} {ell : Z4Link}
    (htouched : ell ∈ touchedPhysicalLinks n physical) :
    ell ∈ excitedBoundaryLinks n physical := by
  have htouch : hasExcitedB physical (incidentPlaqIds n ell) = true := by
    exact (List.mem_filter.mp htouched).2
  obtain ⟨plaquetteId, hid, hexcited⟩ :=
    hasExcitedB_exists_local physical (incidentPlaqIds n ell) htouch
  obtain ⟨p, hindexed, hedge⟩ :=
    (mem_incidentPlaqIds.mp hid)
  unfold excitedBoundaryLinks excitedPlaquetteEntries
  rw [List.mem_flatMap]
  refine ⟨(plaquetteId, p), ?_, hedge⟩
  exact List.mem_filter.mpr ⟨hindexed, by
    simpa only [decide_eq_true_eq] using hexcited⟩

theorem excitedBoundaryLinks_length (n : Nat)
    (physical : EdgeLabelling) :
    (excitedBoundaryLinks n physical).length =
      (excitedPlaquetteEntries n physical).length * 4 := by
  unfold excitedBoundaryLinks
  apply length_flatMap_fixed
  intro indexed
  rfl

/-! ## 3. Constructive duplicate-freeness of erased link lists -/

private theorem filtered_eraseDups_nodup {A : Type}
    [BEq A] [LawfulBEq A] (xs : List A) :
    ∀ p : A → Bool, (xs.filter p).eraseDups.Nodup := by
  induction xs with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons a rest ih =>
      intro p
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr
          ⟨?_, ih (fun b => (!(b == a)) && p b)⟩
        intro ha
        have ha' : a ∈ rest.filter (fun b => (!(b == a)) && p b) :=
          List.mem_eraseDups.mp ha
        have hfalse := (List.mem_filter.mp ha').2
        have hself : (a == a) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact ih p

private theorem filter_true {A : Type} :
    ∀ xs : List A, xs.filter (fun _ => true) = xs
  | [] => rfl
  | a :: rest => congrArg (List.cons a) (filter_true rest)

private theorem eraseDups_nodup_local {A : Type}
    [BEq A] [LawfulBEq A] (xs : List A) : xs.eraseDups.Nodup := by
  have h := filtered_eraseDups_nodup xs (fun _ => true)
  rw [filter_true] at h
  exact h

theorem touchedPhysicalLinks_nodup (n : Nat)
    (physical : EdgeLabelling) :
    (touchedPhysicalLinks n physical).Nodup := by
  unfold touchedPhysicalLinks distinctBoxLinks
  exact List.filter_sublist.nodup (eraseDups_nodup_local (boxLinks n))

/-! ## 4. Uniform incidence-count bound -/

theorem touchedPhysicalLinks_length_le (n : Nat)
    (physical : EdgeLabelling) :
    (touchedPhysicalLinks n physical).length ≤
      (excitedPlaquetteEntries n physical).length * 4 := by
  have hsubset : ∀ ell, ell ∈ touchedPhysicalLinks n physical →
      ell ∈ excitedBoundaryLinks n physical := by
    intro ell hell
    exact touchedPhysicalLink_mem_excitedBoundary hell
  have hle := nodup_subset_length_le
    (touchedPhysicalLinks n physical)
    (excitedBoundaryLinks n physical)
    (touchedPhysicalLinks_nodup n physical) hsubset
  rw [excitedBoundaryLinks_length] at hle
  exact hle

theorem map_touchedIndexedLinks_snd (n : Nat)
    (physical : EdgeLabelling) :
    (touchedIndexedLinks n physical).map Prod.snd =
      touchedPhysicalLinks n physical := by
  let pred : Z4Link → Bool := fun ell =>
    hasExcitedB physical (incidentPlaqIds n ell)
  change (((enumerate (distinctBoxLinks n)).filter
      (pred ∘ Prod.snd)).map Prod.snd) =
    (distinctBoxLinks n).filter pred
  rw [← List.filter_map]
  exact congrArg (List.filter pred)
    (Z4UnitCubeEnumerationParity.enumerate_map_snd (distinctBoxLinks n))

theorem touchedIndexedLinks_length_le (n : Nat)
    (physical : EdgeLabelling) :
    (touchedIndexedLinks n physical).length ≤
      (excitedPlaquetteEntries n physical).length * 4 := by
  have hmap := congrArg List.length
    (map_touchedIndexedLinks_snd n physical)
  simp only [List.length_map] at hmap
  rw [hmap]
  exact touchedPhysicalLinks_length_le n physical

end YMGap.Continuum.Z4ExplicitExcitationIncidenceBound

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ExplicitExcitationIncidenceBound.touchedPhysicalLink_mem_excitedBoundary
#print axioms YMGap.Continuum.Z4ExplicitExcitationIncidenceBound.touchedPhysicalLinks_nodup
#print axioms YMGap.Continuum.Z4ExplicitExcitationIncidenceBound.touchedPhysicalLinks_length_le
#print axioms YMGap.Continuum.Z4ExplicitExcitationIncidenceBound.touchedIndexedLinks_length_le
