/-
# Three-state counting of two colored canonical supports

Two ambient-ordered face supports are encoded by their physical union and,
at each union face, one of the three nonempty color states: left only, right
only, or both.  The code is injective and has exactly `3^size` possible words
at union size `size`.  This is the finite combinatorial origin of the existing
`eSurrogate = 3` factor.
-/

import YMGap.Continuum.Z4CanonicalConnectedCarrierWeight

namespace YMGap.Continuum.Z4CanonicalColoredSupportCount

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition

abbrev ColoredSupportPair := List Nat × List Nat

def coloredSupportUnion (n : Nat) (pair : ColoredSupportPair) : List Nat :=
  (physicalFaceEdges n).filter (fun face =>
    memberB pair.1 face || memberB pair.2 face)

def colorState (left right : Bool) : Nat :=
  if left then (if right then 2 else 0) else 1

def coloredSupportCode (n : Nat) (pair : ColoredSupportPair) : List Nat :=
  (coloredSupportUnion n pair).map (fun face =>
    colorState (memberB pair.1 face) (memberB pair.2 face))

theorem coloredSupportUnion_mem_faceSupports
    (n : Nat) (pair : ColoredSupportPair) :
    coloredSupportUnion n pair ∈ cutoffOneFaceSupports n := by
  unfold coloredSupportUnion cutoffOneFaceSupports
  exact filter_mem_sublists _ _

theorem mem_coloredSupportUnion_iff
    {n : Nat} {pair : ColoredSupportPair}
    (hleft : pair.1 ∈ cutoffOneFaceSupports n)
    (hright : pair.2 ∈ cutoffOneFaceSupports n)
    (face : Nat) :
    face ∈ coloredSupportUnion n pair ↔
      face ∈ pair.1 ∨ face ∈ pair.2 := by
  unfold coloredSupportUnion
  rw [List.mem_filter]
  constructor
  · intro h
    rcases (Bool.or_eq_true _ _).mp h.2 with hleftB | hrightB
    · exact Or.inl ((memberB_eq_true_iff _ _).1 hleftB)
    · exact Or.inr ((memberB_eq_true_iff _ _).1 hrightB)
  · intro h
    constructor
    · rcases h with hface | hface
      · exact mem_of_mem_sublists (physicalFaceEdges n) pair.1 hleft
          face hface
      · exact mem_of_mem_sublists (physicalFaceEdges n) pair.2 hright
          face hface
    · rcases h with hface | hface
      · rw [Bool.or_eq_true]
        exact Or.inl ((memberB_eq_true_iff _ _).2 hface)
      · rw [Bool.or_eq_true]
        exact Or.inr ((memberB_eq_true_iff _ _).2 hface)

theorem coloredSupportUnion_memberB
    {n : Nat} {pair : ColoredSupportPair}
    (hleft : pair.1 ∈ cutoffOneFaceSupports n)
    (hright : pair.2 ∈ cutoffOneFaceSupports n)
    (face : Nat) :
    memberB (coloredSupportUnion n pair) face =
      (memberB pair.1 face || memberB pair.2 face) := by
  apply Bool.eq_iff_iff.mpr
  simp only [memberB_eq_true_iff, Bool.or_eq_true]
  exact mem_coloredSupportUnion_iff hleft hright face

theorem colorState_lt_three (left right : Bool) :
    colorState left right < 3 := by
  cases left <;> cases right <;> decide

theorem coloredSupportCode_length (n : Nat) (pair : ColoredSupportPair) :
    (coloredSupportCode n pair).length =
      (coloredSupportUnion n pair).length := by
  unfold coloredSupportCode
  exact List.length_map _

theorem coloredSupportCode_all_lt_three (n : Nat)
    (pair : ColoredSupportPair) :
    ∀ code, code ∈ coloredSupportCode n pair → code < 3 := by
  intro code hcode
  obtain ⟨face, _, hvalue⟩ := List.mem_map.mp hcode
  rw [← hvalue]
  exact colorState_lt_three _ _

theorem taggedMap_eq_of_valueMap_eq {A B : Type} :
    ∀ (xs : List A) (left right : A → B),
      xs.map left = xs.map right →
        xs.map (fun item => (item, left item)) =
          xs.map (fun item => (item, right item))
  | [], _, _, _ => rfl
  | head :: tail, left, right, heq => by
      have hhead : left head = right head := List.cons.inj heq |>.1
      have htail : tail.map left = tail.map right := List.cons.inj heq |>.2
      simp only [List.map]
      rw [hhead, taggedMap_eq_of_valueMap_eq tail left right htail]

theorem colorState_eq_of_union_code_eq
    {n : Nat} {first second : ColoredSupportPair}
    (hunion : coloredSupportUnion n first = coloredSupportUnion n second)
    (hcode : coloredSupportCode n first = coloredSupportCode n second)
    {face : Nat} (hface : face ∈ coloredSupportUnion n first) :
    colorState (memberB first.1 face) (memberB first.2 face) =
      colorState (memberB second.1 face) (memberB second.2 face) := by
  unfold coloredSupportCode at hcode
  rw [← hunion] at hcode
  have htagged := taggedMap_eq_of_valueMap_eq
    (coloredSupportUnion n first)
    (fun found => colorState (memberB first.1 found) (memberB first.2 found))
    (fun found => colorState (memberB second.1 found) (memberB second.2 found))
    hcode
  have hleftMem :
      (face, colorState (memberB first.1 face) (memberB first.2 face)) ∈
        (coloredSupportUnion n first).map (fun found =>
          (found, colorState (memberB first.1 found)
            (memberB first.2 found))) :=
    List.mem_map.mpr ⟨face, hface, rfl⟩
  have hrightMem := htagged ▸ hleftMem
  obtain ⟨found, _hfound, hfoundEq⟩ := List.mem_map.mp hrightMem
  have hfaceEq : found = face := congrArg Prod.fst hfoundEq
  have hcolorEq := congrArg Prod.snd hfoundEq
  subst found
  exact hcolorEq.symm

theorem colorBits_injective
    (left right left' right' : Bool)
    (hunion : (left || right) = (left' || right'))
    (hcolor : colorState left right = colorState left' right') :
    left = left' ∧ right = right' := by
  cases left <;> cases right <;> cases left' <;> cases right' <;>
    simp_all [colorState]

theorem coloredSupportPair_injective
    {n : Nat} {first second : ColoredSupportPair}
    (hfirstLeft : first.1 ∈ cutoffOneFaceSupports n)
    (hfirstRight : first.2 ∈ cutoffOneFaceSupports n)
    (hsecondLeft : second.1 ∈ cutoffOneFaceSupports n)
    (hsecondRight : second.2 ∈ cutoffOneFaceSupports n)
    (hunion : coloredSupportUnion n first = coloredSupportUnion n second)
    (hcode : coloredSupportCode n first = coloredSupportCode n second) :
    first = second := by
  have hbits : ∀ face,
      memberB first.1 face = memberB second.1 face ∧
        memberB first.2 face = memberB second.2 face := by
    intro face
    have hor : (memberB first.1 face || memberB first.2 face) =
        (memberB second.1 face || memberB second.2 face) := by
      rw [← coloredSupportUnion_memberB hfirstLeft hfirstRight,
        ← coloredSupportUnion_memberB hsecondLeft hsecondRight, hunion]
    by_cases hface : face ∈ coloredSupportUnion n first
    · exact colorBits_injective _ _ _ _ hor
        (colorState_eq_of_union_code_eq hunion hcode hface)
    · have hfirstUnion :
          memberB (coloredSupportUnion n first) face = false :=
        (memberB_eq_false_iff _ _).2 hface
      have hsecondNot : face ∉ coloredSupportUnion n second := by
        rw [← hunion]
        exact hface
      have hsecondUnion :
          memberB (coloredSupportUnion n second) face = false :=
        (memberB_eq_false_iff _ _).2 hsecondNot
      rw [coloredSupportUnion_memberB hfirstLeft hfirstRight] at hfirstUnion
      rw [coloredSupportUnion_memberB hsecondLeft hsecondRight] at hsecondUnion
      cases hfl : memberB first.1 face <;>
        cases hfr : memberB first.2 face <;>
        cases hsl : memberB second.1 face <;>
        cases hsr : memberB second.2 face <;> simp_all
  apply Prod.ext
  · apply sublists_eq_of_mem_iff (physicalFaceEdges n)
      first.1 second.1 (physicalFaceEdges_nodup n)
      hfirstLeft hsecondLeft
    intro face
    constructor
    · intro hface
      exact (memberB_eq_true_iff _ _).1
        ((hbits face).1 ▸ (memberB_eq_true_iff _ _).2 hface)
    · intro hface
      exact (memberB_eq_true_iff _ _).1
        ((hbits face).1.symm ▸ (memberB_eq_true_iff _ _).2 hface)
  · apply sublists_eq_of_mem_iff (physicalFaceEdges n)
      first.2 second.2 (physicalFaceEdges_nodup n)
      hfirstRight hsecondRight
    intro face
    constructor
    · intro hface
      exact (memberB_eq_true_iff _ _).1
        ((hbits face).2 ▸ (memberB_eq_true_iff _ _).2 hface)
    · intro hface
      exact (memberB_eq_true_iff _ _).1
        ((hbits face).2.symm ▸ (memberB_eq_true_iff _ _).2 hface)

/-! ## Fixed-size canonical colored pairs -/

def canonicalColoredPinnedSizePairs (n rootFace size : Nat) :
    List ColoredSupportPair :=
  (cartesian (cutoffOneFaceSupports n) (cutoffOneFaceSupports n)).filter
    (fun pair => memberB (canonicalPinnedSizePolymers n rootFace size)
      (coloredSupportUnion n pair))

theorem canonicalColoredPinnedSizePairs_nodup (n rootFace size : Nat) :
    (canonicalColoredPinnedSizePairs n rootFace size).Nodup := by
  unfold canonicalColoredPinnedSizePairs
  exact List.filter_sublist.nodup
    (cartesian_nodup _ _ (cutoffOneFaceSupports_nodup n)
      (cutoffOneFaceSupports_nodup n))

def coloredRepresentation (n : Nat)
    (pair : ColoredSupportPair) (target : List Nat × List Nat) : Prop :=
  coloredSupportUnion n pair = target.1 ∧
    coloredSupportCode n pair = target.2

theorem cartesian_length (xs : List A) (ys : List B) :
    (cartesian xs ys).length = xs.length * ys.length := by
  unfold cartesian
  exact length_flatMap_const
    (fun x : A => ys.map (fun y => (x, y))) ys.length xs
    (fun _ _ => List.length_map _)

theorem canonicalColoredPinnedSizePairs_length_le
    (n rootFace size : Nat) :
    (canonicalColoredPinnedSizePairs n rootFace size).length ≤
      (canonicalPinnedSizePolymers n rootFace size).length * 3 ^ size := by
  have hbound := length_le_of_unique_representation (coloredRepresentation n)
    (canonicalColoredPinnedSizePairs n rootFace size)
    (cartesian (canonicalPinnedSizePolymers n rootFace size)
      (allSeqs 3 size))
    (canonicalColoredPinnedSizePairs_nodup n rootFace size)
    (fun pair hpair => by
      have hraw := (List.mem_filter.mp hpair).1
      have hpinned : coloredSupportUnion n pair ∈
          canonicalPinnedSizePolymers n rootFace size :=
        (memberB_eq_true_iff _ _).1 (List.mem_filter.mp hpair).2
      have hsize := (mem_canonicalPinnedSizePolymers_iff.mp hpinned).2.2
      have hcode : coloredSupportCode n pair ∈ allSeqs 3 size :=
        mem_allSeqs 3 size _
          (by rw [coloredSupportCode_length, hsize])
          (coloredSupportCode_all_lt_three n pair)
      exact ⟨(coloredSupportUnion n pair, coloredSupportCode n pair),
        (mem_cartesian_iff _ _ _).2 ⟨hpinned, hcode⟩, rfl, rfl⟩)
    (fun first hfirst second hsecond target hfirstRel hsecondRel => by
      have hfirstRaw := (mem_cartesian_iff _ _ first).1
        (List.mem_filter.mp hfirst).1
      have hsecondRaw := (mem_cartesian_iff _ _ second).1
        (List.mem_filter.mp hsecond).1
      exact coloredSupportPair_injective
        hfirstRaw.1 hfirstRaw.2 hsecondRaw.1 hsecondRaw.2
        (hfirstRel.1.trans hsecondRel.1.symm)
        (hfirstRel.2.trans hsecondRel.2.symm))
  rw [cartesian_length, length_allSeqs] at hbound
  exact hbound

end YMGap.Continuum.Z4CanonicalColoredSupportCount

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalColoredSupportCount.coloredSupportPair_injective
#print axioms YMGap.Continuum.Z4CanonicalColoredSupportCount.canonicalColoredPinnedSizePairs_length_le
