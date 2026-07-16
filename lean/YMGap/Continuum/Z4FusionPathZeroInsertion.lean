/-
# Vacuum insertion invariance for bounded left-fusion paths

The explicit finite-box link resolver uses a left-associated fusion chain.
When a box is enlarged, an old spin decoration extends by spin zero on every
new plaquette.  This file isolates the exact local algebra needed for that
transport: inserting a zero external spin at any position does not change
the number of vacuum-ending fusion paths.

The proof is a literal finite-sum argument.  Fusion with spin zero forces the
adjacent channel to be unchanged, and the forced channel lies in the finite
enumeration because all external spins are assumed bounded by the cutoff.
-/

import YMGap.Continuum.Z4NestedBoxEnumeration
import YMGap.Continuum.Z4ValenceFusionCutoffIndependence

namespace YMGap.Continuum.Z4FusionPathZeroInsertion

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4NestedBoxEnumeration
open YMGap.Continuum.Z4UnitCubeEnumerationParity
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. A list presentation of the canonical left-fusion count -/

/-- Structurally fuelled implementation of the left-fusion recursion.  The
public wrapper below supplies exactly the list length as fuel. -/
def fusionPathMultiplicityAux (cutoff : Nat) : Nat → List Nat → Nat
  | _, [] => 1
  | _, [a] => boolMultiplicity (decide (a = 0))
  | 0, _ :: _ :: _ => 0
  | fuel + 1, a :: b :: rest =>
      natListSum ((List.range (cutoff + 1)).map fun channel =>
        if fusionOK a b channel then
          fusionPathMultiplicityAux cutoff fuel (channel :: rest)
        else 0)

/-- Number of left-associated fusion paths ending in the vacuum.  The
one-spin case is the vacuum indicator; every longer list sums over the first
intermediate channel and recurses. -/
def fusionPathMultiplicity (cutoff : Nat) (spins : List Nat) : Nat :=
  fusionPathMultiplicityAux cutoff spins.length spins

@[simp] theorem fusionPathMultiplicity_nil (cutoff : Nat) :
    fusionPathMultiplicity cutoff [] = 1 := rfl

@[simp] theorem fusionPathMultiplicity_singleton (cutoff a : Nat) :
    fusionPathMultiplicity cutoff [a] =
      boolMultiplicity (decide (a = 0)) := rfl

theorem fusionPathMultiplicity_cons_cons (cutoff a b : Nat)
    (rest : List Nat) :
    fusionPathMultiplicity cutoff (a :: b :: rest) =
      natListSum ((List.range (cutoff + 1)).map fun channel =>
        if fusionOK a b channel then
          fusionPathMultiplicity cutoff (channel :: rest)
        else 0) := by
  simp only [fusionPathMultiplicity, List.length_cons]
  change fusionPathMultiplicityAux cutoff (Nat.succ (rest.length + 1))
      (a :: b :: rest) = _
  rw [fusionPathMultiplicityAux]

def SpinsBounded (cutoff : Nat) (spins : List Nat) : Prop :=
  ∀ spin, spin ∈ spins → spin ≤ cutoff

theorem spinsBounded_append {cutoff : Nat} {left right : List Nat}
    (h : SpinsBounded cutoff (left ++ right)) :
    SpinsBounded cutoff left ∧ SpinsBounded cutoff right := by
  constructor
  · intro spin hspin
    exact h spin (List.mem_append_left right hspin)
  · intro spin hspin
    exact h spin (List.mem_append_right left hspin)

/-! ## 2. Collapse of a finite natural sum to its unique supported term -/

private theorem natListSum_map_zero {A : Type} (term : A → Nat) :
    ∀ xs : List A, (∀ x, x ∈ xs → term x = 0) →
      natListSum (xs.map term) = 0
  | [], _ => rfl
  | x :: xs, hzero => by
      simp only [List.map_cons, natListSum]
      rw [hzero x List.mem_cons_self,
        natListSum_map_zero term xs
          (fun y hy => hzero y (List.mem_cons_of_mem x hy))]

private theorem natListSum_range_unique {cutoff chosen : Nat}
    (term : Nat → Nat) (hchosen : chosen ≤ cutoff)
    (hzero : ∀ x, x ≤ cutoff → x ≠ chosen → term x = 0) :
    natListSum ((List.range (cutoff + 1)).map term) = term chosen := by
  induction cutoff with
  | zero =>
      have hc : chosen = 0 := by omega
      subst chosen
      rfl
  | succ cutoff ih =>
      rw [List.range_succ, List.map_append, natListSum_append]
      simp only [List.map_singleton, natListSum, Nat.add_zero]
      by_cases hc : chosen ≤ cutoff
      · rw [ih hc (fun x hx hne => hzero x (by omega) hne),
          hzero (cutoff + 1) (by omega) (by omega), Nat.add_zero]
      · have hchosenTop : chosen = cutoff + 1 := by omega
        subst chosen
        have hprefix :
            natListSum ((List.range (cutoff + 1)).map term) = 0 :=
          natListSum_map_zero term (List.range (cutoff + 1))
            (fun x hx => hzero x (by
              have hlt := List.mem_range.mp hx
              omega) (by
              have hlt := List.mem_range.mp hx
              omega))
        rw [hprefix, Nat.zero_add]

/-! ## 3. Spin zero forces the neighboring channel -/

theorem fusionOK_zero_left_eq_decide (a channel : Nat) :
    fusionOK 0 a channel = decide (channel = a) := by
  by_cases h : channel = a
  · subst channel
    rw [YMGap.Continuum.FusionQuotientCollapse.fusionOK_zero_left_self]
    simp
  · rw [YMGap.Continuum.FusionQuotientCollapse.fusionOK_zero_left_ne a channel]
    · simp [h]
    · exact fun ha => h ha.symm

theorem fusionOK_zero_right_eq_decide (a channel : Nat) :
    fusionOK a 0 channel = decide (channel = a) := by
  rw [YMGap.Continuum.FusionCoreStepRoundD.fusionOK_symm_ab]
  exact fusionOK_zero_left_eq_decide a channel

theorem fusionOK_zero_output_eq_decide (a b : Nat) :
    fusionOK a b 0 = decide (a = b) := by
  by_cases h : a = b
  · subst b
    rw [YMGap.Continuum.FusionQuotientCollapse.fusionOK_zero_diag_self]
    simp
  · rw [YMGap.Continuum.FusionQuotientCollapse.fusionOK_zero_diag_ne a b h]
    simp [h]

/-! ## 4. Vacuum insertion at the first two positions -/

theorem fusionPathMultiplicity_zero_cons {cutoff : Nat}
    (spins : List Nat) (hspins : SpinsBounded cutoff spins) :
    fusionPathMultiplicity cutoff (0 :: spins) =
      fusionPathMultiplicity cutoff spins := by
  cases spins with
  | nil => rfl
  | cons a rest =>
      have ha : a ≤ cutoff := hspins a List.mem_cons_self
      rw [fusionPathMultiplicity_cons_cons]
      change natListSum ((List.range (cutoff + 1)).map fun channel =>
          if fusionOK 0 a channel then
            fusionPathMultiplicity cutoff (channel :: rest)
          else 0) = fusionPathMultiplicity cutoff (a :: rest)
      rw [natListSum_range_unique
        (fun channel => if fusionOK 0 a channel then
          fusionPathMultiplicity cutoff (channel :: rest) else 0) ha]
      · rw [fusionOK_zero_left_eq_decide]
        simp
      · intro channel _ hne
        rw [fusionOK_zero_left_eq_decide]
        simp [hne]

theorem fusionPathMultiplicity_zero_second {cutoff a : Nat}
    (rest : List Nat) (ha : a ≤ cutoff) :
      fusionPathMultiplicity cutoff (a :: 0 :: rest) =
      fusionPathMultiplicity cutoff (a :: rest) := by
  rw [fusionPathMultiplicity_cons_cons]
  change natListSum ((List.range (cutoff + 1)).map fun channel =>
      if fusionOK a 0 channel then
        fusionPathMultiplicity cutoff (channel :: rest)
      else 0) = fusionPathMultiplicity cutoff (a :: rest)
  rw [natListSum_range_unique
    (fun channel => if fusionOK a 0 channel then
      fusionPathMultiplicity cutoff (channel :: rest) else 0) ha]
  · rw [fusionOK_zero_right_eq_decide]
    simp
  · intro channel _ hne
    rw [fusionOK_zero_right_eq_decide]
    simp [hne]

/-! ## 5. Vacuum insertion at an arbitrary position -/

private theorem fusionPathMultiplicity_insert_zero_fuel {cutoff : Nat} :
    ∀ fuel before after,
    before.length ≤ fuel →
    SpinsBounded cutoff (before ++ after) →
    fusionPathMultiplicity cutoff (before ++ after) =
      fusionPathMultiplicity cutoff (before ++ 0 :: after)
  | 0, before, after, hlength, hbounded => by
      have hnil : before = [] := by
        cases before with
        | nil => rfl
        | cons _ _ => simp at hlength
      subst before
      exact (fusionPathMultiplicity_zero_cons after hbounded).symm
  | fuel + 1, before, after, hlength, hbounded => by
      cases before with
      | nil =>
          exact (fusionPathMultiplicity_zero_cons after hbounded).symm
      | cons a tail =>
          cases tail with
          | nil =>
              have ha : a ≤ cutoff := hbounded a (by simp)
              exact (fusionPathMultiplicity_zero_second after ha).symm
          | cons b rest =>
              simp only [List.cons_append]
              rw [fusionPathMultiplicity_cons_cons,
                fusionPathMultiplicity_cons_cons]
              apply natListSum_map_congr
              intro channel hchannel
              by_cases hfusion : fusionOK a b channel = true
              · simp only [hfusion, if_true]
                exact fusionPathMultiplicity_insert_zero_fuel
                  (cutoff := cutoff) fuel (channel :: rest) after
                  (by
                    simp only [List.length_cons] at hlength ⊢
                    omega)
                  (by
                    intro spin hspin
                    simp only [List.cons_append, List.mem_append,
                      List.mem_cons] at hspin ⊢
                    rcases hspin with rfl | hrest | hafter
                    · have hlt := List.mem_range.mp hchannel
                      omega
                    · exact hbounded spin (by simp [hrest])
                    · exact hbounded spin (by simp [hafter]))
              · have hfalse : fusionOK a b channel = false := by
                  cases h : fusionOK a b channel
                  · rfl
                  · exact False.elim (hfusion h)
                simp [hfalse]

/-- Inserting one spin-zero face anywhere in a bounded external list leaves
the exact left-fusion path cardinality unchanged. -/
theorem fusionPathMultiplicity_insert_zero {cutoff : Nat}
    (before after : List Nat)
    (hbounded : SpinsBounded cutoff (before ++ after)) :
    fusionPathMultiplicity cutoff (before ++ after) =
      fusionPathMultiplicity cutoff (before ++ 0 :: after) :=
  fusionPathMultiplicity_insert_zero_fuel before.length before after
    (Nat.le_refl _) hbounded

/-! ## 6. Identification with the explicit valence-zero-through-six formulas -/

private theorem natListSum_boolMultiplicity_eq_filter_length
    (allowed : Nat → Bool) : ∀ xs : List Nat,
    natListSum (xs.map fun x => boolMultiplicity (allowed x)) =
      (xs.filter allowed).length
  | [] => rfl
  | x :: xs => by
      simp only [List.map_cons, natListSum]
      rw [natListSum_boolMultiplicity_eq_filter_length allowed xs]
      cases h : allowed x with
      | false =>
          simp [List.filter_cons, h, boolMultiplicity]
      | true =>
          simp [List.filter_cons, h, boolMultiplicity, Nat.add_comm]

theorem oneValentMultiplicity_eq_bool_zero (cutoff a : Nat) :
    oneValentMultiplicity cutoff a =
      boolMultiplicity (decide (a = 0)) := by
  unfold oneValentMultiplicity
  rw [← natListSum_boolMultiplicity_eq_filter_length]
  rw [natListSum_range_unique
    (fun vacuum => boolMultiplicity
      (fusionOK a vacuum vacuum && decide (vacuum = 0)))
    (chosen := 0) (Nat.zero_le cutoff)]
  · rw [fusionOK_zero_right_eq_decide]
    simp [boolMultiplicity, eq_comm]
  · intro vacuum _ hne
    simp [boolMultiplicity, hne]

theorem twoValentMultiplicity_eq_bool_zero_output
    (cutoff a b : Nat) :
    twoValentMultiplicity cutoff a b =
      boolMultiplicity (fusionOK a b 0) := by
  unfold twoValentMultiplicity
  rw [← natListSum_boolMultiplicity_eq_filter_length]
  rw [natListSum_range_unique
    (fun vacuum => boolMultiplicity
      (fusionOK a b vacuum && decide (vacuum = 0)))
    (chosen := 0) (Nat.zero_le cutoff)]
  · cases h : fusionOK a b 0 <;> simp [boolMultiplicity, h]
  · intro vacuum _ hne
    simp [boolMultiplicity, hne]

theorem fusionPathMultiplicity_two (cutoff a b : Nat) :
    fusionPathMultiplicity cutoff [a, b] =
      boolMultiplicity (fusionOK a b 0) := by
  rw [fusionPathMultiplicity_cons_cons]
  rw [natListSum_range_unique
    (fun channel => if fusionOK a b channel then
      fusionPathMultiplicity cutoff [channel] else 0)
    (chosen := 0) (Nat.zero_le cutoff)]
  · cases h : fusionOK a b 0 <;>
      simp [h, boolMultiplicity]
  · intro channel _ hne
    simp [fusionPathMultiplicity_singleton, boolMultiplicity, hne]

theorem fusionPathMultiplicity_three
    (cutoff a b c : Nat) (hc : c ≤ cutoff) :
    fusionPathMultiplicity cutoff [a, b, c] =
      boolMultiplicity (fusionOK a b c) := by
  rw [fusionPathMultiplicity_cons_cons]
  rw [natListSum_range_unique
    (fun channel => if fusionOK a b channel then
      fusionPathMultiplicity cutoff [channel, c] else 0)
    (chosen := c) hc]
  · rw [fusionPathMultiplicity_two,
      YMGap.Continuum.FusionQuotientCollapse.fusionOK_zero_diag_self]
    cases h : fusionOK a b c <;> simp [h, boolMultiplicity]
  · intro channel _ hne
    rw [fusionPathMultiplicity_two,
      YMGap.Continuum.FusionQuotientCollapse.fusionOK_zero_diag_ne
        channel c hne]
    simp [boolMultiplicity]

theorem fusionPathMultiplicity_four
    (cutoff a b c d : Nat) (hd : d ≤ cutoff) :
    fusionPathMultiplicity cutoff [a, b, c, d] =
      oneChannelMultiplicity cutoff a b c d := by
  rw [fusionPathMultiplicity_cons_cons]
  calc
    natListSum ((List.range (cutoff + 1)).map fun channel =>
        if fusionOK a b channel then
          fusionPathMultiplicity cutoff [channel, c, d]
        else 0) =
        natListSum ((List.range (cutoff + 1)).map fun channel =>
          boolMultiplicity
            (fusionOK a b channel && fusionOK channel c d)) := by
              apply natListSum_map_congr
              intro channel _
              rw [fusionPathMultiplicity_three cutoff channel c d hd]
              cases hleft : fusionOK a b channel <;>
                cases hright : fusionOK channel c d <;> rfl
    _ = ((List.range (cutoff + 1)).filter fun channel =>
          fusionOK a b channel && fusionOK channel c d).length :=
      natListSum_boolMultiplicity_eq_filter_length _ _
    _ = oneChannelMultiplicity cutoff a b c d := rfl

theorem fusionPathMultiplicity_five
    (cutoff a b c d e : Nat) (he : e ≤ cutoff) :
    fusionPathMultiplicity cutoff [a, b, c, d, e] =
      twoChannelMultiplicity cutoff a b c d e := by
  rw [fusionPathMultiplicity_cons_cons,
    twoChannelMultiplicity_eq_pairPathCount]
  unfold pairPathCount
  apply natListSum_map_congr
  intro channel _
  rw [fusionPathMultiplicity_four cutoff channel c d e he]
  by_cases hleft : fusionOK a b channel = true
  · simp only [hleft, if_true]
    unfold oneChannelMultiplicity filterRangeCount
    simp only [hleft, Bool.true_and]
  · have hfalse : fusionOK a b channel = false := by
      cases h : fusionOK a b channel
      · rfl
      · exact False.elim (hleft h)
    simp only [hfalse, if_false]
    symm
    apply filterRangeCount_zero
    intro inner
    simp [hfalse]

theorem fusionPathMultiplicity_six
    (cutoff a b c d e f : Nat) (hf : f ≤ cutoff) :
    fusionPathMultiplicity cutoff [a, b, c, d, e, f] =
      threeChannelMultiplicity cutoff a b c d e f := by
  rw [fusionPathMultiplicity_cons_cons,
    threeChannelMultiplicity_eq_triplePathCount]
  unfold triplePathCount
  apply natListSum_map_congr
  intro channel _
  rw [fusionPathMultiplicity_five cutoff channel c d e f hf]
  by_cases hleft : fusionOK a b channel = true
  · simp only [hleft, if_true]
    rw [twoChannelMultiplicity_eq_pairPathCount]
    unfold pairPathCount filterRangeCount
    simp only [hleft, Bool.true_and]
  · have hfalse : fusionOK a b channel = false := by
      cases h : fusionOK a b channel
      · rfl
      · exact False.elim (hleft h)
    simp only [hfalse, if_false]
    symm
    apply pairPathCount_zero
    intro middle inner
    simp [hfalse]

def externalSpinsOfList (spins : List Nat) : Nat → Nat :=
  fun position => spins.getD position 0

/-- Through the maximum geometric degree six, the structurally recursive
list count is exactly the pre-existing explicit finite-box multiplicity. -/
theorem fusionPathMultiplicity_eq_explicit_of_length_le_six
    {cutoff : Nat} (spins : List Nat)
    (hlength : spins.length ≤ 6)
    (hbounded : SpinsBounded cutoff spins) :
    fusionPathMultiplicity cutoff spins =
      explicitValenceMultiplicity cutoff spins.length
        (externalSpinsOfList spins) := by
  cases spins with
  | nil => rfl
  | cons a tail =>
      cases tail with
      | nil =>
          rw [fusionPathMultiplicity_singleton]
          change boolMultiplicity (decide (a = 0)) =
            oneValentMultiplicity cutoff a
          exact (oneValentMultiplicity_eq_bool_zero cutoff a).symm
      | cons b tail =>
          cases tail with
          | nil =>
              rw [fusionPathMultiplicity_two]
              change boolMultiplicity (fusionOK a b 0) =
                twoValentMultiplicity cutoff a b
              exact (twoValentMultiplicity_eq_bool_zero_output
                cutoff a b).symm
          | cons c tail =>
              have hc : c ≤ cutoff := hbounded c (by simp)
              cases tail with
              | nil =>
                  rw [fusionPathMultiplicity_three cutoff a b c hc]
                  rfl
              | cons d tail =>
                  have hd : d ≤ cutoff := hbounded d (by simp)
                  cases tail with
                  | nil =>
                      rw [fusionPathMultiplicity_four cutoff a b c d hd]
                      rfl
                  | cons e tail =>
                      have he : e ≤ cutoff := hbounded e (by simp)
                      cases tail with
                      | nil =>
                          rw [fusionPathMultiplicity_five
                            cutoff a b c d e he]
                          rfl
                      | cons f tail =>
                          have hf : f ≤ cutoff := hbounded f (by simp)
                          cases tail with
                          | nil =>
                              rw [fusionPathMultiplicity_six
                                cutoff a b c d e f hf]
                              rfl
                          | cons beyond rest =>
                              simp at hlength

/-! ## 7. Repeated zero extensions -/

/-- `target` is obtained from `source` by preserving every old spin in order
and inserting only vacuum spins. -/
inductive ZeroExtension : List Nat → List Nat → Prop
  | nil : ZeroExtension [] []
  | keep {source target : List Nat} (spin : Nat) :
      ZeroExtension source target →
        ZeroExtension (spin :: source) (spin :: target)
  | insertZero {source target : List Nat} :
      ZeroExtension source target →
        ZeroExtension source (0 :: target)

theorem ZeroExtension.bounded {cutoff : Nat} {source target : List Nat}
    (h : ZeroExtension source target)
    (hsource : SpinsBounded cutoff source) :
    SpinsBounded cutoff target := by
  induction h with
  | nil => exact hsource
  | keep s h ih =>
      intro value hvalue
      rcases List.mem_cons.mp hvalue with rfl | htail
      · exact hsource _ List.mem_cons_self
      · exact ih (fun item hitem =>
          hsource item (List.mem_cons_of_mem _ hitem)) value htail
  | insertZero h ih =>
      intro value hvalue
      rcases List.mem_cons.mp hvalue with rfl | htail
      · exact Nat.zero_le cutoff
      · exact ih hsource value htail

private theorem spinsBounded_append_of
    {cutoff : Nat} {left right : List Nat}
    (hleft : SpinsBounded cutoff left)
    (hright : SpinsBounded cutoff right) :
    SpinsBounded cutoff (left ++ right) := by
  intro spin hspin
  rcases List.mem_append.mp hspin with hmem | hmem
  · exact hleft spin hmem
  · exact hright spin hmem

private theorem fusionPathMultiplicity_zeroExtension_prefix
    {cutoff : Nat} {source target : List Nat}
    (h : ZeroExtension source target) :
    ∀ before,
    SpinsBounded cutoff (before ++ source) →
    fusionPathMultiplicity cutoff (before ++ source) =
      fusionPathMultiplicity cutoff (before ++ target) := by
  induction h with
  | nil =>
      intro before _
      rfl
  | @keep source target spin h ih =>
      intro before hbounded
      have hbounded' : SpinsBounded cutoff ((before ++ [spin]) ++ source) := by
        simpa only [List.append_assoc, List.singleton_append] using hbounded
      simpa only [List.append_assoc, List.singleton_append] using
        ih (before ++ [spin]) hbounded'
  | @insertZero source target h ih =>
      intro before hbounded
      have hparts := spinsBounded_append hbounded
      have htarget : SpinsBounded cutoff target :=
        h.bounded hparts.2
      have hbeforeTarget : SpinsBounded cutoff (before ++ target) :=
        spinsBounded_append_of hparts.1 htarget
      exact Eq.trans (ih before hbounded)
        (fusionPathMultiplicity_insert_zero before target hbeforeTarget)

theorem fusionPathMultiplicity_zeroExtension
    {cutoff : Nat} {source target : List Nat}
    (h : ZeroExtension source target)
    (hsource : SpinsBounded cutoff source) :
    fusionPathMultiplicity cutoff source =
      fusionPathMultiplicity cutoff target := by
  simpa using fusionPathMultiplicity_zeroExtension_prefix
    (cutoff := cutoff) h [] hsource

/-- The production explicit link multiplicity is invariant under any ordered
extension that inserts only bounded vacuum spins. -/
theorem explicitValenceMultiplicity_zeroExtension
    {cutoff : Nat} {source target : List Nat}
    (h : ZeroExtension source target)
    (hsourceLength : source.length ≤ 6)
    (htargetLength : target.length ≤ 6)
    (hsourceBounded : SpinsBounded cutoff source) :
    explicitValenceMultiplicity cutoff source.length
        (externalSpinsOfList source) =
      explicitValenceMultiplicity cutoff target.length
        (externalSpinsOfList target) := by
  rw [← fusionPathMultiplicity_eq_explicit_of_length_le_six
      source hsourceLength hsourceBounded,
    ← fusionPathMultiplicity_eq_explicit_of_length_le_six
      target htargetLength (h.bounded hsourceBounded)]
  exact fusionPathMultiplicity_zeroExtension h hsourceBounded

/-! ## 8. Producing zero extensions from ordered geometric sublists -/

open scoped List

theorem ZeroExtension.map_of_sublist {A : Type} (value : A → Nat)
    {source target : List A} (hsub : source <+ target)
    (htargetNodup : target.Nodup)
    (hzero : ∀ item, item ∈ target → item ∉ source → value item = 0) :
    ZeroExtension (source.map value) (target.map value) := by
  induction hsub with
  | slnil => exact ZeroExtension.nil
  | @cons source target item hsub ih =>
      have hparts := List.nodup_cons.mp htargetNodup
      have hitemNotSource : item ∉ source := by
        intro hitem
        exact hparts.1 (hsub.mem hitem)
      have htailZero : ∀ x, x ∈ target → x ∉ source → value x = 0 := by
        intro x hx hnot
        exact hzero x (List.mem_cons_of_mem item hx) hnot
      have htail := ih hparts.2 htailZero
      have hhead : value item = 0 :=
        hzero item List.mem_cons_self hitemNotSource
      simpa only [List.map_cons, hhead] using ZeroExtension.insertZero htail
  | @cons₂ source target item hsub ih =>
      have hparts := List.nodup_cons.mp htargetNodup
      have htailZero : ∀ x, x ∈ target → x ∉ source → value x = 0 := by
        intro x hx hnot
        apply hzero x (List.mem_cons_of_mem item hx)
        intro hsource
        rcases List.mem_cons.mp hsource with heq | hmem
        · subst x
          exact hparts.1 hx
        · exact hnot hmem
      simpa only [List.map_cons] using
        ZeroExtension.keep (value item) (ih hparts.2 htailZero)

def geometricIncidentSpins (n : Nat) (ell : Z4Link)
    (spin : Z4Plaq → Nat) : List Nat :=
  ((boxPlaquettes n).filter fun p => decide (ell ∈ edgesOf p)).map spin

/-- A geometric spin decoration extended by zero outside the smaller box
gives an ordered zero extension on every fixed link's incident face list. -/
theorem geometricIncidentSpins_zeroExtension
    {small large : Nat} (hsmall : small ≤ large)
    (ell : Z4Link) (spin : Z4Plaq → Nat)
    (hzeroOutside : ∀ p, p ∈ boxPlaquettes large →
      p ∉ boxPlaquettes small → spin p = 0) :
    ZeroExtension
      (geometricIncidentSpins small ell spin)
      (geometricIncidentSpins large ell spin) := by
  unfold geometricIncidentSpins
  apply ZeroExtension.map_of_sublist spin
    (incidentBoxPlaquettes_sublist hsmall ell)
  · exact List.filter_sublist.nodup (boxPlaquettes_nodup large)
  · intro p hpLarge hpNotSmallIncident
    have hlargeParts := List.mem_filter.mp hpLarge
    apply hzeroOutside p hlargeParts.1
    intro hpSmall
    apply hpNotSmallIncident
    exact List.mem_filter.mpr ⟨hpSmall, hlargeParts.2⟩

/-- The explicit formula only reads positions strictly below its degree. -/
theorem explicitValenceMultiplicity_congr_prefix
    {cutoff degree : Nat} {left right : Nat → Nat}
    (hdegree : degree ≤ 6)
    (hagree : ∀ position, position < degree →
      left position = right position) :
    explicitValenceMultiplicity cutoff degree left =
      explicitValenceMultiplicity cutoff degree right := by
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · change oneValentMultiplicity cutoff (left 0) =
      oneValentMultiplicity cutoff (right 0)
    rw [hagree 0 (by omega)]
  · change twoValentMultiplicity cutoff (left 0) (left 1) =
      twoValentMultiplicity cutoff (right 0) (right 1)
    rw [hagree 0 (by omega), hagree 1 (by omega)]
  · change boolMultiplicity (fusionOK (left 0) (left 1) (left 2)) =
      boolMultiplicity (fusionOK (right 0) (right 1) (right 2))
    rw [hagree 0 (by omega), hagree 1 (by omega),
      hagree 2 (by omega)]
  · change oneChannelMultiplicity cutoff
      (left 0) (left 1) (left 2) (left 3) =
      oneChannelMultiplicity cutoff
        (right 0) (right 1) (right 2) (right 3)
    rw [hagree 0 (by omega), hagree 1 (by omega),
      hagree 2 (by omega), hagree 3 (by omega)]
  · change twoChannelMultiplicity cutoff
      (left 0) (left 1) (left 2) (left 3) (left 4) =
      twoChannelMultiplicity cutoff
        (right 0) (right 1) (right 2) (right 3) (right 4)
    rw [hagree 0 (by omega), hagree 1 (by omega),
      hagree 2 (by omega), hagree 3 (by omega),
      hagree 4 (by omega)]
  · change threeChannelMultiplicity cutoff
      (left 0) (left 1) (left 2) (left 3) (left 4) (left 5) =
      threeChannelMultiplicity cutoff
        (right 0) (right 1) (right 2) (right 3) (right 4) (right 5)
    rw [hagree 0 (by omega), hagree 1 (by omega),
      hagree 2 (by omega), hagree 3 (by omega),
      hagree 4 (by omega), hagree 5 (by omega)]

#print axioms fusionOK_zero_left_eq_decide
#print axioms fusionOK_zero_right_eq_decide
#print axioms fusionOK_zero_output_eq_decide
#print axioms fusionPathMultiplicityAux
#print axioms fusionPathMultiplicity_cons_cons
#print axioms natListSum_map_zero
#print axioms natListSum_range_unique
#print axioms fusionPathMultiplicity_zero_cons
#print axioms fusionPathMultiplicity_zero_second
#print axioms fusionPathMultiplicity_insert_zero
#print axioms fusionPathMultiplicity_eq_explicit_of_length_le_six
#print axioms ZeroExtension.bounded
#print axioms fusionPathMultiplicity_zeroExtension
#print axioms explicitValenceMultiplicity_zeroExtension
#print axioms ZeroExtension.map_of_sublist
#print axioms geometricIncidentSpins_zeroExtension
#print axioms explicitValenceMultiplicity_congr_prefix

end YMGap.Continuum.Z4FusionPathZeroInsertion
