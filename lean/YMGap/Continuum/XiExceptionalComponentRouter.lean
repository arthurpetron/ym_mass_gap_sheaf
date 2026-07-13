/-
# Residual-component routing

Path-local routing can put the two endpoints of an off-path disagreement edge
into the same external family.  The corrected router switches the *entire*
residual disagreement component rooted at an unsafe left occurrence.  On the
right-safe branch this has four constructive properties needed by the frozen
carrier target: both output families are compatible, every background
occurrence is path-safe, the full activity product is preserved exactly, and
reverse-component recovery makes the map injective.
-/

import YMGap.Continuum.XiPathSafeFactsClosure

namespace YMGap.Continuum.XiExceptionalComponentRouter

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalSwitchedCompatibility
open YMGap.Continuum.XiNonexceptionalTargetValidity

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

def unsafeMask (safe : Nat → Bool) : Nat → Bool :=
  fun i => !safe i

def residualComponentCut (Gamma : List (Polymer L))
    (safe : Nat → Bool) (left right : OccBitVec Gamma.length) : Nat → Bool :=
  forwardComponent Gamma.length (incAtDistinct Gamma)
    (bitMask left) (bitMask right) (unsafeMask safe)

def componentBackground (Gamma : List (Polymer L))
    (safe : Nat → Bool) (left right : OccBitVec Gamma.length) :
    OccBitVec Gamma.length :=
  bitsFromMask Gamma.length
    (switchedLeft Gamma.length (incAtDistinct Gamma)
      (bitMask left) (bitMask right) (unsafeMask safe)) 0

def componentExternal (Gamma : List (Polymer L))
    (safe : Nat → Bool) (left right : OccBitVec Gamma.length) :
    OccBitVec Gamma.length :=
  bitsFromMask Gamma.length
    (switchedRight Gamma.length (incAtDistinct Gamma)
      (bitMask left) (bitMask right) (unsafeMask safe)) 0

theorem componentBackground_at
    (Gamma : List (Polymer L)) (safe : Nat → Bool)
    (left right : OccBitVec Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (componentBackground Gamma safe left right).at i =
      switchedLeft Gamma.length (incAtDistinct Gamma)
        (bitMask left) (bitMask right) (unsafeMask safe) i := by
  unfold componentBackground
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

theorem componentExternal_at
    (Gamma : List (Polymer L)) (safe : Nat → Bool)
    (left right : OccBitVec Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (componentExternal Gamma safe left right).at i =
      switchedRight Gamma.length (incAtDistinct Gamma)
        (bitMask left) (bitMask right) (unsafeMask safe) i := by
  unfold componentExternal
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

private theorem bitVec_pairwise_guard
    (Gamma : List (Polymer L)) (bits : OccBitVec Gamma.length)
    (hcompat : familyCompatibleB (selectByBits Gamma bits) = true) :
    ∀ i j, bitMask bits i = true → bitMask bits j = true →
      symConflict (incAtDistinct Gamma) i j = false := by
  apply sameSide_guard_incAtDistinct Gamma (bitMask bits)
  intro i j hij hi hj
  have hiN : i < Gamma.length := by
    cases hlt : decide (i < Gamma.length) with
    | true => exact of_decide_eq_true hlt
    | false =>
        have hout := bitVec_at_false_of_ge bits i (by
          have := of_decide_eq_false hlt
          omega)
        have hiAt : bits.at i = true := hi
        rw [hiAt] at hout
        cases hout
  have hjN : j < Gamma.length := by
    cases hlt : decide (j < Gamma.length) with
    | true => exact of_decide_eq_true hlt
    | false =>
        have hout := bitVec_at_false_of_ge bits j (by
          have := of_decide_eq_false hlt
          omega)
        have hjAt : bits.at j = true := hj
        rw [hjAt] at hout
        cases hout
  exact selectByBits_pairwise_compatible Gamma bits i j hiN hjN hij
    hi hj hcompat

/-- Component switching preserves internal compatibility on both target
sides.  Unlike the path-local router, a residual conflict edge can never be
cut between the two output orientations. -/
theorem component_families_compatible
    (Gamma : List (Polymer L)) (safe : Nat → Bool)
    (left right : OccBitVec Gamma.length)
    (hleft : familyCompatibleB (selectByBits Gamma left) = true)
    (hright : familyCompatibleB (selectByBits Gamma right) = true) :
    familyCompatibleB
        (selectByBits Gamma (componentBackground Gamma safe left right)) = true ∧
      familyCompatibleB
        (selectByBits Gamma (componentExternal Gamma safe left right)) = true := by
  have hleftGuard := bitVec_pairwise_guard Gamma left hleft
  have hrightGuard := bitVec_pairwise_guard Gamma right hright
  constructor
  · apply selectByBits_familyCompatible_of_pairwise
    intro i j hi hj hij hbi hbj
    rw [componentBackground_at Gamma safe left right i hi] at hbi
    rw [componentBackground_at Gamma safe left right j hj] at hbj
    exact compatibleB_of_incAtDistinct_symConflict_false Gamma hij
      (switchedLeft_sameSide_guard Gamma.length (incAtDistinct Gamma)
        (bitMask left) (bitMask right) (unsafeMask safe)
        hleftGuard hrightGuard i j hi hj hbi hbj)
  · apply selectByBits_familyCompatible_of_pairwise
    intro i j hi hj hij hei hej
    rw [componentExternal_at Gamma safe left right i hi] at hei
    rw [componentExternal_at Gamma safe left right j hj] at hej
    exact compatibleB_of_incAtDistinct_symConflict_false Gamma hij
      (switchedRight_sameSide_guard Gamma.length (incAtDistinct Gamma)
        (bitMask left) (bitMask right) (unsafeMask safe)
        hleftGuard hrightGuard i j hi hj hei hej)

/-- If the residual right side is path-safe, every unsafe residual left
occurrence roots a switched component, while every right occurrence moved
into the background is safe. -/
theorem component_background_safe_of_right_safe
    (Gamma : List (Polymer L)) (safe : Nat → Bool)
    (left right : OccBitVec Gamma.length)
    (hexclusive : ∀ i, i < Gamma.length → safe i = false →
      left.at i = true → right.at i = false)
    (hrightSafe : ∀ i, i < Gamma.length → right.at i = true →
      safe i = true) :
    ∀ i, i < Gamma.length →
      (componentBackground Gamma safe left right).at i = true →
      safe i = true := by
  intro i hi hbackground
  rw [componentBackground_at Gamma safe left right i hi] at hbackground
  unfold switchedLeft swapLeftMask at hbackground
  cases hcut : residualComponentCut Gamma safe left right i with
  | false =>
      have hleft : left.at i = true := by
        unfold residualComponentCut at hcut
        simpa [hcut, bitMask] using hbackground
      cases hsafe : safe i with
      | true => rfl
      | false =>
          have hseed : forwardSeed Gamma.length (bitMask left) (bitMask right)
              (unsafeMask safe) i = true := by
            unfold forwardSeed leftOnly bitMask unsafeMask
            simp [decide_eq_true hi, hleft,
              hexclusive i hi hsafe hleft, hsafe]
          have hreached := forwardSeed_reached Gamma.length
            (incAtDistinct Gamma) (bitMask left) (bitMask right)
            (unsafeMask safe) hseed
          change residualComponentCut Gamma safe left right i = true at hreached
          rw [hcut] at hreached
          cases hreached
  | true =>
      have hright : right.at i = true := by
        unfold residualComponentCut at hcut
        simpa [hcut, bitMask] using hbackground
      exact hrightSafe i hi hright

/-- The component router is an exact occurrence swap, hence preserves the
complete residual activity product without a numerical estimate. -/
theorem component_familyActivity_preserved
    (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep) (safe : Nat → Bool)
    (left right : OccBitVec Gamma.length) :
    familyActivity w
        (selectByBits Gamma (componentBackground Gamma safe left right)) label *
      familyActivity w
        (selectByBits Gamma (componentExternal Gamma safe left right)) label ≈
      familyActivity w (selectByBits Gamma left) label *
        familyActivity w (selectByBits Gamma right) label := by
  let cut := residualComponentCut Gamma safe left right
  have hweight := maskWeight_swap_preserved w Gamma label cut
    (bitMask left) (bitMask right)
  have hbgMask : ∀ i, i < Gamma.length →
      bitMask (componentBackground Gamma safe left right) i =
        swapLeftMask cut (bitMask left) (bitMask right) i := by
    intro i hi
    change (componentBackground Gamma safe left right).at i = _
    rw [componentBackground_at Gamma safe left right i hi]
    rfl
  have hextMask : ∀ i, i < Gamma.length →
      bitMask (componentExternal Gamma safe left right) i =
        swapRightMask cut (bitMask left) (bitMask right) i := by
    intro i hi
    change (componentExternal Gamma safe left right).at i = _
    rw [componentExternal_at Gamma safe left right i hi]
    rfl
  rw [← maskWeight_congr_on w Gamma label
      (bitMask (componentBackground Gamma safe left right))
      (swapLeftMask cut (bitMask left) (bitMask right)) hbgMask,
    ← maskWeight_congr_on w Gamma label
      (bitMask (componentExternal Gamma safe left right))
      (swapRightMask cut (bitMask left) (bitMask right)) hextMask] at hweight
  have hbg := maskWeight_eqv_familyActivity w Gamma label
    (bitMask (componentBackground Gamma safe left right))
  have hext := maskWeight_eqv_familyActivity w Gamma label
    (bitMask (componentExternal Gamma safe left right))
  have hleft := maskWeight_eqv_familyActivity w Gamma label (bitMask left)
  have hright := maskWeight_eqv_familyActivity w Gamma label (bitMask right)
  rw [maskFamily_toMask_eq_selectByBits] at hbg hext hleft hright
  exact Q'.eqv_trans _ _ _
    (mul_eqv_congr_both (Q'.eqv_symm hbg) (Q'.eqv_symm hext))
    (Q'.eqv_trans _ _ _ hweight (mul_eqv_congr_both hleft hright))

private theorem switched_pair_injective_of_right_good
    (N : Nat) (inc : Nat → Nat → Bool) (bad : Nat → Bool)
    (left1 right1 left2 right2 : Nat → Bool)
    (hleft1 : ∀ i j, left1 i = true → left1 j = true →
      symConflict inc i j = false)
    (hright1 : ∀ i j, right1 i = true → right1 j = true →
      symConflict inc i j = false)
    (hgood1 : ∀ i, right1 i = true → bad i = false)
    (hleft2 : ∀ i j, left2 i = true → left2 j = true →
      symConflict inc i j = false)
    (hright2 : ∀ i j, right2 i = true → right2 j = true →
      symConflict inc i j = false)
    (hgood2 : ∀ i, right2 i = true → bad i = false)
    (houtLeft : ∀ i,
      switchedLeft N inc left1 right1 bad i =
        switchedLeft N inc left2 right2 bad i)
    (houtRight : ∀ i,
      switchedRight N inc left1 right1 bad i =
        switchedRight N inc left2 right2 bad i) :
    (∀ i, left1 i = left2 i) ∧ (∀ i, right1 i = right2 i) := by
  let cut1 := forwardComponent N inc left1 right1 bad
  let cut2 := forwardComponent N inc left2 right2 bad
  have hsl : switchedLeft N inc left1 right1 bad =
      switchedLeft N inc left2 right2 bad := funext houtLeft
  have hsr : switchedRight N inc left1 right1 bad =
      switchedRight N inc left2 right2 bad := funext houtRight
  have hcut : ∀ i, cut1 i = cut2 i := by
    intro i
    have hr1 := reverse_component_recovers N inc left1 right1 bad
      hleft1 hright1 hgood1 i
    have hr2 := reverse_component_recovers N inc left2 right2 bad
      hleft2 hright2 hgood2 i
    dsimp only [cut1, cut2]
    rw [← hr1, ← hr2, hsl, hsr]
  have hcutFun : cut1 = cut2 := funext hcut
  apply swapMasks_pair_injective cut1 left1 right1 left2 right2
  · intro i
    have h := houtLeft i
    unfold switchedLeft at h
    change swapLeftMask cut1 left1 right1 i =
      swapLeftMask cut2 left2 right2 i at h
    rw [← hcutFun] at h
    exact h
  · intro i
    have h := houtRight i
    unfold switchedRight at h
    change swapRightMask cut1 left1 right1 i =
      swapRightMask cut2 left2 right2 i at h
    rw [← hcutFun] at h
    exact h

/-- Equality of component-routed finite masks recovers both residual input
masks on the right-safe branch. -/
theorem component_pair_injective_of_right_safe
    (Gamma : List (Polymer L)) (safe : Nat → Bool)
    (left1 right1 left2 right2 : OccBitVec Gamma.length)
    (hleft1 : familyCompatibleB (selectByBits Gamma left1) = true)
    (hright1 : familyCompatibleB (selectByBits Gamma right1) = true)
    (hgood1 : ∀ i, i < Gamma.length → right1.at i = true → safe i = true)
    (hleft2 : familyCompatibleB (selectByBits Gamma left2) = true)
    (hright2 : familyCompatibleB (selectByBits Gamma right2) = true)
    (hgood2 : ∀ i, i < Gamma.length → right2.at i = true → safe i = true)
    (hroute :
      (componentBackground Gamma safe left1 right1,
          componentExternal Gamma safe left1 right1) =
        (componentBackground Gamma safe left2 right2,
          componentExternal Gamma safe left2 right2)) :
    (left1, right1) = (left2, right2) := by
  have hbg := congrArg Prod.fst hroute
  have hext := congrArg Prod.snd hroute
  change componentBackground Gamma safe left1 right1 =
    componentBackground Gamma safe left2 right2 at hbg
  change componentExternal Gamma safe left1 right1 =
    componentExternal Gamma safe left2 right2 at hext
  have houtLeft : ∀ i,
      switchedLeft Gamma.length (incAtDistinct Gamma)
          (bitMask left1) (bitMask right1) (unsafeMask safe) i =
        switchedLeft Gamma.length (incAtDistinct Gamma)
          (bitMask left2) (bitMask right2) (unsafeMask safe) i := by
    intro i
    by_cases hi : i < Gamma.length
    · have h := congrArg (fun bits => bits.at i) hbg
      change (componentBackground Gamma safe left1 right1).at i =
        (componentBackground Gamma safe left2 right2).at i at h
      rw [componentBackground_at Gamma safe left1 right1 i hi,
        componentBackground_at Gamma safe left2 right2 i hi] at h
      exact h
    · have hge : Gamma.length ≤ i := by omega
      unfold switchedLeft swapLeftMask bitMask
      rw [bitVec_at_false_of_ge left1 i hge,
        bitVec_at_false_of_ge right1 i hge,
        bitVec_at_false_of_ge left2 i hge,
        bitVec_at_false_of_ge right2 i hge]
      cases forwardComponent Gamma.length (incAtDistinct Gamma)
        (fun j => left1.at j) (fun j => right1.at j) (unsafeMask safe) i <;>
        cases forwardComponent Gamma.length (incAtDistinct Gamma)
          (fun j => left2.at j) (fun j => right2.at j) (unsafeMask safe) i <;>
        rfl
  have houtRight : ∀ i,
      switchedRight Gamma.length (incAtDistinct Gamma)
          (bitMask left1) (bitMask right1) (unsafeMask safe) i =
        switchedRight Gamma.length (incAtDistinct Gamma)
          (bitMask left2) (bitMask right2) (unsafeMask safe) i := by
    intro i
    by_cases hi : i < Gamma.length
    · have h := congrArg (fun bits => bits.at i) hext
      change (componentExternal Gamma safe left1 right1).at i =
        (componentExternal Gamma safe left2 right2).at i at h
      rw [componentExternal_at Gamma safe left1 right1 i hi,
        componentExternal_at Gamma safe left2 right2 i hi] at h
      exact h
    · have hge : Gamma.length ≤ i := by omega
      unfold switchedRight swapRightMask bitMask
      rw [bitVec_at_false_of_ge right1 i hge,
        bitVec_at_false_of_ge left1 i hge,
        bitVec_at_false_of_ge right2 i hge,
        bitVec_at_false_of_ge left2 i hge]
      cases forwardComponent Gamma.length (incAtDistinct Gamma)
        (fun j => left1.at j) (fun j => right1.at j) (unsafeMask safe) i <;>
        cases forwardComponent Gamma.length (incAtDistinct Gamma)
          (fun j => left2.at j) (fun j => right2.at j) (unsafeMask safe) i <;>
        rfl
  have hdecoded := switched_pair_injective_of_right_good Gamma.length
    (incAtDistinct Gamma) (unsafeMask safe)
    (bitMask left1) (bitMask right1) (bitMask left2) (bitMask right2)
    (bitVec_pairwise_guard Gamma left1 hleft1)
    (bitVec_pairwise_guard Gamma right1 hright1)
    (fun i hi => by
      by_cases hiN : i < Gamma.length
      · unfold unsafeMask
        rw [hgood1 i hiN hi]
        rfl
      · have hge : Gamma.length ≤ i := by omega
        have hout := bitVec_at_false_of_ge right1 i hge
        have hiAt : right1.at i = true := hi
        rw [hiAt] at hout
        cases hout)
    (bitVec_pairwise_guard Gamma left2 hleft2)
    (bitVec_pairwise_guard Gamma right2 hright2)
    (fun i hi => by
      by_cases hiN : i < Gamma.length
      · unfold unsafeMask
        rw [hgood2 i hiN hi]
        rfl
      · have hge : Gamma.length ≤ i := by omega
        have hout := bitVec_at_false_of_ge right2 i hge
        have hiAt : right2.at i = true := hi
        rw [hiAt] at hout
        cases hout)
    houtLeft houtRight
  apply Prod.ext
  · apply BitVec.ext
    exact hdecoded.1
  · apply BitVec.ext
    exact hdecoded.2

#print axioms componentBackground_at
#print axioms componentExternal_at
#print axioms component_families_compatible
#print axioms component_background_safe_of_right_safe
#print axioms component_familyActivity_preserved
#print axioms component_pair_injective_of_right_safe

end YMGap.Continuum.XiExceptionalComponentRouter
