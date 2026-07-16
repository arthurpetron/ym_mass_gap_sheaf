/-
# Adjacent-swap and full-permutation lift at the physical `6*K` cutoff

The four-leg recoupling bijection gives equality of the two-step transition
counts.  This file lifts that equality through an arbitrary suffix weight,
then through an arbitrary prefix, and finally through a `List.Perm` proof for
lists of at most six cutoff-`K` external spins.
-/

import YMGap.Continuum.Z4FusionMultiplicityPermutation

namespace YMGap.Continuum.Z4FusionMultiplicityPermutationLift

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionMultiplicityPermutation
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Finite natural-sum algebra -/

theorem natListSum_map_add {A : Type}
    (left right : A → Nat) : ∀ xs : List A,
    natListSum (xs.map fun x => left x + right x) =
      natListSum (xs.map left) + natListSum (xs.map right)
  | [] => rfl
  | head :: tail => by
      simp only [List.map_cons, natListSum]
      rw [natListSum_map_add left right tail]
      omega

theorem natListSum_map_zero_local {A : Type} : ∀ xs : List A,
    natListSum (xs.map fun _ => 0) = 0
  | [] => rfl
  | _ :: tail => by
      simp only [List.map_cons, natListSum, Nat.zero_add]
      exact natListSum_map_zero_local tail

theorem natListSum_map_swap {A B : Type}
    (term : A → B → Nat) : ∀ (xs : List A) (ys : List B),
    natListSum (xs.map fun x =>
        natListSum (ys.map fun y => term x y)) =
      natListSum (ys.map fun y =>
        natListSum (xs.map fun x => term x y))
  | [], ys => by
      simp only [List.map_nil, natListSum]
      exact (natListSum_map_zero_local ys).symm
  | head :: tail, ys => by
      simp only [List.map_cons, natListSum]
      rw [natListSum_map_swap term tail ys]
      rw [← natListSum_map_add
        (fun y => term head y)
        (fun y => natListSum (tail.map fun x => term x y)) ys]

theorem natListSum_if_const_eq_filter_length {A : Type}
    (allowed : A → Bool) (weight : Nat) : ∀ xs : List A,
    natListSum (xs.map fun x => if allowed x then weight else 0) =
      (xs.filter allowed).length * weight := by
  intro xs
  induction xs with
  | nil => simp [natListSum]
  | cons head tail ih =>
      cases hallowed : allowed head
      · simp [hallowed, natListSum, ih]
      · simp [hallowed, natListSum, ih, Nat.succ_mul, Nat.add_comm]

/-! ## 2. The two-step weighted recoupling identity -/

def twoStepWeighted (cutoff p a b : Nat)
    (weight : Nat → Nat) : Nat :=
  natListSum ((List.range (cutoff + 1)).map fun first =>
    natListSum ((List.range (cutoff + 1)).map fun output =>
      if fusionOK p a first then
        if fusionOK first b output then weight output else 0
      else 0))

theorem weightedOneChannel_eq
    (cutoff a b c d weight : Nat) :
    natListSum ((List.range (cutoff + 1)).map fun channel =>
      if fusionOK a b channel then
        if fusionOK channel c d then weight else 0
      else 0) =
      oneChannelMultiplicity cutoff a b c d * weight := by
  calc
    natListSum ((List.range (cutoff + 1)).map fun channel =>
        if fusionOK a b channel then
          if fusionOK channel c d then weight else 0
        else 0) =
        natListSum ((List.range (cutoff + 1)).map fun channel =>
          if fusionOK a b channel && fusionOK channel c d
            then weight else 0) := by
              apply natListSum_map_congr
              intro channel _
              cases fusionOK a b channel <;>
                cases fusionOK channel c d <;> rfl
    _ = ((List.range (cutoff + 1)).filter fun channel =>
          fusionOK a b channel && fusionOK channel c d).length *
          weight :=
      natListSum_if_const_eq_filter_length _ weight _
    _ = oneChannelMultiplicity cutoff a b c d * weight := rfl

theorem oneChannelMultiplicity_symm_first
    (cutoff a b c d : Nat) :
    oneChannelMultiplicity cutoff a b c d =
      oneChannelMultiplicity cutoff b a c d := by
  unfold oneChannelMultiplicity
  apply congrArg List.length
  apply List.filter_congr
  intro channel _
  rw [fusionOK_symm_ab a b channel]

theorem oneChannelMultiplicity_swap_middle
    {cutoff p a b d : Nat}
    (hpa : p + a ≤ cutoff)
    (hab : a + b ≤ cutoff)
    (hpb : p + b ≤ cutoff) :
    oneChannelMultiplicity cutoff p a b d =
      oneChannelMultiplicity cutoff p b a d := by
  calc
    oneChannelMultiplicity cutoff p a b d =
        oneChannelMultiplicity cutoff a b p d :=
      oneChannelMultiplicity_assoc hpa hab
    _ = oneChannelMultiplicity cutoff b a p d :=
      oneChannelMultiplicity_symm_first cutoff a b p d
    _ = oneChannelMultiplicity cutoff p b a d :=
      (oneChannelMultiplicity_assoc hpb (by omega)).symm

theorem twoStepWeighted_swap
    {cutoff p a b : Nat} (weight : Nat → Nat)
    (hpa : p + a ≤ cutoff)
    (hab : a + b ≤ cutoff)
    (hpb : p + b ≤ cutoff) :
    twoStepWeighted cutoff p a b weight =
      twoStepWeighted cutoff p b a weight := by
  unfold twoStepWeighted
  let channels := List.range (cutoff + 1)
  calc
    natListSum (channels.map fun first =>
        natListSum (channels.map fun output =>
          if fusionOK p a first then
            if fusionOK first b output then weight output else 0
          else 0)) =
        natListSum (channels.map fun output =>
          natListSum (channels.map fun first =>
            if fusionOK p a first then
              if fusionOK first b output then weight output else 0
            else 0)) := by
              exact natListSum_map_swap
                (fun first output =>
                  if fusionOK p a first then
                    if fusionOK first b output
                      then weight output else 0
                  else 0) channels channels
    _ = natListSum (channels.map fun output =>
          oneChannelMultiplicity cutoff p a b output *
            weight output) := by
              apply natListSum_map_congr
              intro output _
              exact weightedOneChannel_eq cutoff p a b output
                (weight output)
    _ = natListSum (channels.map fun output =>
          oneChannelMultiplicity cutoff p b a output *
            weight output) := by
              apply natListSum_map_congr
              intro output _
              rw [oneChannelMultiplicity_swap_middle hpa hab hpb]
    _ = natListSum (channels.map fun output =>
          natListSum (channels.map fun first =>
            if fusionOK p b first then
              if fusionOK first a output then weight output else 0
            else 0)) := by
              apply natListSum_map_congr
              intro output _
              exact (weightedOneChannel_eq cutoff p b a output
                (weight output)).symm
    _ = natListSum (channels.map fun first =>
        natListSum (channels.map fun output =>
          if fusionOK p b first then
            if fusionOK first a output then weight output else 0
          else 0)) := by
              exact (natListSum_map_swap
                (fun first output =>
                  if fusionOK p b first then
                    if fusionOK first a output
                      then weight output else 0
                  else 0) channels channels).symm

/-! ## 3. Adjacent swaps at an arbitrary prefix -/

theorem fusionPathMultiplicity_threePrefix_eq_twoStepWeighted
    (cutoff p a b : Nat) (after : List Nat) :
    fusionPathMultiplicity cutoff (p :: a :: b :: after) =
      twoStepWeighted cutoff p a b
        (fun output => fusionPathMultiplicity cutoff (output :: after)) := by
  rw [fusionPathMultiplicity_cons_cons]
  unfold twoStepWeighted
  apply natListSum_map_congr
  intro first _
  cases hfirst : fusionOK p a first with
  | false =>
      simp only [hfirst, if_false]
      exact (natListSum_map_zero_local
        (List.range (cutoff + 1))).symm
  | true =>
      simp only [hfirst, if_true]
      exact fusionPathMultiplicity_cons_cons cutoff first b after

theorem fusionPathMultiplicity_swap_first
    (cutoff a b : Nat) (after : List Nat) :
    fusionPathMultiplicity cutoff (a :: b :: after) =
      fusionPathMultiplicity cutoff (b :: a :: after) := by
  rw [fusionPathMultiplicity_cons_cons,
    fusionPathMultiplicity_cons_cons]
  apply natListSum_map_congr
  intro channel _
  rw [fusionOK_symm_ab a b channel]

theorem fusionPathMultiplicity_swap_after_one
    {cutoff p a b : Nat} (after : List Nat)
    (hpa : p + a ≤ cutoff)
    (hab : a + b ≤ cutoff)
    (hpb : p + b ≤ cutoff) :
    fusionPathMultiplicity cutoff (p :: a :: b :: after) =
      fusionPathMultiplicity cutoff (p :: b :: a :: after) := by
  rw [fusionPathMultiplicity_threePrefix_eq_twoStepWeighted,
    fusionPathMultiplicity_threePrefix_eq_twoStepWeighted]
  exact twoStepWeighted_swap _ hpa hab hpb

private theorem fusionPathMultiplicity_swap_adjacent_fuel
    {cutoff a b : Nat} : ∀ fuel before after,
    before.length ≤ fuel →
    natListSum before + a + b ≤ cutoff →
    fusionPathMultiplicity cutoff (before ++ a :: b :: after) =
      fusionPathMultiplicity cutoff (before ++ b :: a :: after)
  | 0, before, after, hlength, hbudget => by
      have hnil : before = [] := by
        cases before with
        | nil => rfl
        | cons _ _ => simp at hlength
      subst before
      exact fusionPathMultiplicity_swap_first cutoff a b after
  | fuel + 1, before, after, hlength, hbudget => by
      cases before with
      | nil => exact fusionPathMultiplicity_swap_first cutoff a b after
      | cons p tail =>
          cases tail with
          | nil =>
              exact fusionPathMultiplicity_swap_after_one after
                (by simp only [natListSum] at hbudget; omega)
                (by simp only [natListSum] at hbudget; omega)
                (by simp only [natListSum] at hbudget; omega)
          | cons q rest =>
              simp only [List.cons_append]
              rw [fusionPathMultiplicity_cons_cons,
                fusionPathMultiplicity_cons_cons]
              apply natListSum_map_congr
              intro channel _
              cases hfusion : fusionOK p q channel with
              | false => rfl
              | true =>
                  simp only [hfusion, if_true]
                  apply fusionPathMultiplicity_swap_adjacent_fuel
                    fuel (channel :: rest) after
                  · simp only [List.length_cons] at hlength ⊢
                    omega
                  · have hchannel := fusionOK_output_le_add hfusion
                    simp only [natListSum] at hbudget ⊢
                    omega

/-- Swapping two neighboring external spins behind any prefix preserves the
left-fusion path count whenever the prefix plus the swapped pair fits in the
auxiliary channel window. -/
theorem fusionPathMultiplicity_swap_adjacent
    {cutoff a b : Nat} (before after : List Nat)
    (hbudget : natListSum before + a + b ≤ cutoff) :
    fusionPathMultiplicity cutoff (before ++ a :: b :: after) =
      fusionPathMultiplicity cutoff (before ++ b :: a :: after) :=
  fusionPathMultiplicity_swap_adjacent_fuel before.length before after
    (Nat.le_refl _) hbudget

/-! ## 4. The physical `6*K` budget and arbitrary permutations -/

theorem natListSum_le_length_mul
    {K : Nat} : ∀ (spins : List Nat),
    SpinsBounded K spins →
      natListSum spins ≤ spins.length * K
  | [], _ => by simp [natListSum]
  | spin :: rest, hbounded => by
      have hspin : spin ≤ K := hbounded spin List.mem_cons_self
      have hrest : SpinsBounded K rest := by
        intro value hvalue
        exact hbounded value (List.mem_cons_of_mem spin hvalue)
      have ih := natListSum_le_length_mul rest hrest
      simpa [natListSum, Nat.succ_mul, Nat.add_comm] using
        Nat.add_le_add hspin ih

theorem spinsBounded_of_perm
    {K : Nat} {left right : List Nat}
    (hperm : left.Perm right)
    (hbounded : SpinsBounded K left) :
    SpinsBounded K right := by
  intro spin hspin
  exact hbounded spin ((hperm.mem_iff).mpr hspin)

theorem physicalAdjacentBudget
    {K a b : Nat} {before after : List Nat}
    (hlength : (before ++ a :: b :: after).length ≤ 6)
    (hbounded : SpinsBounded K (before ++ a :: b :: after)) :
    natListSum before + a + b ≤ linkAuxiliaryCutoff K := by
  have hparts := spinsBounded_append hbounded
  have hbefore := natListSum_le_length_mul before hparts.1
  have ha : a ≤ K := hparts.2 a List.mem_cons_self
  have hb : b ≤ K := hparts.2 b
    (List.mem_cons_of_mem a List.mem_cons_self)
  have hprefixLength : before.length + 2 ≤ 6 := by
    simp only [List.length_append, List.length_cons] at hlength
    omega
  have hscaled := Nat.mul_le_mul_right K hprefixLength
  unfold linkAuxiliaryCutoff
  calc
    natListSum before + a + b ≤
        before.length * K + K + K := by omega
    _ = (before.length + 2) * K := by
      simp [Nat.add_mul, Nat.succ_mul, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
    _ ≤ 6 * K := hscaled

/-- Prefix-stable permutation invariance.  Keeping the prefix explicit makes
the `cons` constructor of `List.Perm` a direct recursive call and the `swap`
constructor exactly the adjacent-swap theorem above. -/
theorem fusionPathMultiplicity_perm_prefix
    {K : Nat} {left right : List Nat}
    (hperm : left.Perm right) : ∀ before : List Nat,
    (before ++ left).length ≤ 6 →
    SpinsBounded K (before ++ left) →
    fusionPathMultiplicity (linkAuxiliaryCutoff K) (before ++ left) =
      fusionPathMultiplicity (linkAuxiliaryCutoff K) (before ++ right) := by
  induction hperm with
  | nil =>
      intro before _ _
      rfl
  | @cons spin left right hperm ih =>
      intro before hlength hbounded
      have hlength' : ((before ++ [spin]) ++ left).length ≤ 6 := by
        simpa only [List.append_assoc, List.singleton_append] using hlength
      have hbounded' : SpinsBounded K ((before ++ [spin]) ++ left) := by
        simpa only [List.append_assoc, List.singleton_append] using hbounded
      simpa only [List.append_assoc, List.singleton_append] using
        ih (before ++ [spin]) hlength' hbounded'
  | swap first second rest =>
      intro before hlength hbounded
      exact fusionPathMultiplicity_swap_adjacent before rest
        (physicalAdjacentBudget hlength hbounded)
  | @trans first middle last hleft hright ihleft ihrigh =>
      intro before hlength hbounded
      have hmiddleLength : (before ++ middle).length ≤ 6 := by
        have hsizes := hleft.length_eq
        simp only [List.length_append] at hlength ⊢
        omega
      have hmiddleBounded : SpinsBounded K (before ++ middle) := by
        intro spin hspin
        rcases List.mem_append.mp hspin with hbefore | hmiddle
        · exact hbounded spin (List.mem_append_left _ hbefore)
        · exact hbounded spin (List.mem_append_right _
            ((hleft.mem_iff).mpr hmiddle))
      exact (ihleft before hlength hbounded).trans
        (ihrigh before hmiddleLength hmiddleBounded)

/-- **Physical fusion-path permutation theorem.**  Any two permutations of a
list of at most six cutoff-`K` external spins have exactly the same
vacuum-ending path cardinality in the production `6*K` auxiliary window. -/
theorem fusionPathMultiplicity_physical_perm
    {K : Nat} {left right : List Nat}
    (hperm : left.Perm right)
    (hlength : left.length ≤ 6)
    (hbounded : SpinsBounded K left) :
    fusionPathMultiplicity (linkAuxiliaryCutoff K) left =
      fusionPathMultiplicity (linkAuxiliaryCutoff K) right := by
  simpa using fusionPathMultiplicity_perm_prefix hperm [] hlength hbounded

/-- The explicit valence-zero-through-six formula inherits the same complete
permutation invariance.  This is the form consumed by the finite-slab link
factor. -/
theorem explicitValenceMultiplicity_physical_perm
    {K : Nat} {left right : List Nat}
    (hperm : left.Perm right)
    (hlength : left.length ≤ 6)
    (hbounded : SpinsBounded K left) :
    explicitValenceMultiplicity (linkAuxiliaryCutoff K) left.length
        (externalSpinsOfList left) =
      explicitValenceMultiplicity (linkAuxiliaryCutoff K) right.length
        (externalSpinsOfList right) := by
  have hrightLength : right.length ≤ 6 := by
    rw [← hperm.length_eq]
    exact hlength
  have hrightBounded : SpinsBounded K right :=
    spinsBounded_of_perm hperm hbounded
  have hleftAux : SpinsBounded (linkAuxiliaryCutoff K) left := by
    intro spin hspin
    exact Nat.le_trans (hbounded spin hspin)
      (externalCutoff_le_linkAuxiliaryCutoff K)
  have hrightAux : SpinsBounded (linkAuxiliaryCutoff K) right := by
    intro spin hspin
    exact Nat.le_trans (hrightBounded spin hspin)
      (externalCutoff_le_linkAuxiliaryCutoff K)
  rw [← fusionPathMultiplicity_eq_explicit_of_length_le_six
      left hlength hleftAux,
    ← fusionPathMultiplicity_eq_explicit_of_length_le_six
      right hrightLength hrightAux]
  exact fusionPathMultiplicity_physical_perm hperm hlength hbounded

end YMGap.Continuum.Z4FusionMultiplicityPermutationLift

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4FusionMultiplicityPermutationLift.natListSum_map_swap
#print axioms YMGap.Continuum.Z4FusionMultiplicityPermutationLift.weightedOneChannel_eq
#print axioms YMGap.Continuum.Z4FusionMultiplicityPermutationLift.oneChannelMultiplicity_swap_middle
#print axioms YMGap.Continuum.Z4FusionMultiplicityPermutationLift.twoStepWeighted_swap
#print axioms YMGap.Continuum.Z4FusionMultiplicityPermutationLift.fusionPathMultiplicity_swap_adjacent
#print axioms YMGap.Continuum.Z4FusionMultiplicityPermutationLift.physicalAdjacentBudget
#print axioms YMGap.Continuum.Z4FusionMultiplicityPermutationLift.fusionPathMultiplicity_physical_perm
#print axioms YMGap.Continuum.Z4FusionMultiplicityPermutationLift.explicitValenceMultiplicity_physical_perm
