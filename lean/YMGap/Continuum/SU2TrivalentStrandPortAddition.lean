/-
# Colored strand-port embeddings under SU(2) resolution addition

Additivity of the three canonical trivalent bundle counts says more than
Boolean support union.  Every strand of either summand has a canonical,
color-preserving address inside the summed resolution.  The address uses the
same bundle coordinate and places the left block before the right block in
each of `ab`, `bc`, and `ca`.

This module constructs the two typed port embeddings and proves that both
commute with the exact trivalent mate.  Thus the local resolved graph of a
sum contains two invariant colored copies of the summand graphs; no source
color is lost by canonical re-resolution.

The construction is the stronger local datum needed by a component-switch
decoder.  It is not yet lifted across internal-edge continuation, a complete
canonical link path, or a slab assignment.

Constructive contract: explicit `Fin` maps and natural arithmetic only; no
`Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.SU2TrivalentStrandResolutionAddition

namespace YMGap.Continuum.SU2TrivalentStrandPortAddition

set_option autoImplicit false

open YMGap.Continuum.SU2TrivalentStrandPeeling
open YMGap.Continuum.SU2TrivalentStrandPortPairing
open YMGap.Continuum.SU2TrivalentStrandResolutionAddition

/-! ## 1. Embed the left bundle blocks -/

/-- Embed a port of the left resolution into the summed resolution.  Within
each bundle, the left summand occupies the first block. -/
def trivalentStrandPortInSumLeft
    {a b c a' b' c' : Nat}
    (left : TrivalentStrandResolution a b c)
    (right : TrivalentStrandResolution a' b' c') :
    TrivalentStrandPort a b c →
      TrivalentStrandPort (a + a') (b + b') (c + c')
  | .onA slot =>
      if hca : slot.val < left.ca then
        .onA ⟨slot.val, by
          have ha := left.a_balance
          omega⟩
      else
        .onA ⟨left.ca + right.ca + (slot.val - left.ca), by
          have ha := left.a_balance
          have ha' := right.a_balance
          omega⟩
  | .onB slot =>
      if hbc : slot.val < left.bc then
        .onB ⟨slot.val, by
          have hb := left.b_balance
          omega⟩
      else
        .onB ⟨left.bc + right.bc + (slot.val - left.bc), by
          have hb := left.b_balance
          have hb' := right.b_balance
          omega⟩
  | .onC slot =>
      if hbc : slot.val < left.bc then
        .onC ⟨slot.val, by
          have hc := left.c_balance
          omega⟩
      else
        .onC ⟨left.bc + right.bc + (slot.val - left.bc), by
          have hc := left.c_balance
          have hc' := right.c_balance
          omega⟩

/-! ## 2. Embed the right bundle blocks -/

/-- Embed a port of the right resolution into the summed resolution.  Within
each bundle, the right summand follows the corresponding left block. -/
def trivalentStrandPortInSumRight
    {a b c a' b' c' : Nat}
    (left : TrivalentStrandResolution a b c)
    (right : TrivalentStrandResolution a' b' c') :
    TrivalentStrandPort a' b' c' →
      TrivalentStrandPort (a + a') (b + b') (c + c')
  | .onA slot =>
      if hca : slot.val < right.ca then
        .onA ⟨left.ca + slot.val, by
          have ha := left.a_balance
          have ha' := right.a_balance
          omega⟩
      else
        .onA ⟨left.ca + right.ca + left.ab +
            (slot.val - right.ca), by
          have ha := left.a_balance
          have ha' := right.a_balance
          omega⟩
  | .onB slot =>
      if hbc : slot.val < right.bc then
        .onB ⟨left.bc + slot.val, by
          have hb := left.b_balance
          have hb' := right.b_balance
          omega⟩
      else
        .onB ⟨left.bc + right.bc + left.ab +
            (slot.val - right.bc), by
          have hb := left.b_balance
          have hb' := right.b_balance
          omega⟩
  | .onC slot =>
      if hbc : slot.val < right.bc then
        .onC ⟨left.bc + slot.val, by
          have hc := left.c_balance
          have hc' := right.c_balance
          omega⟩
      else
        .onC ⟨left.bc + right.bc + left.ca +
            (slot.val - right.bc), by
          have hc := left.c_balance
          have hc' := right.c_balance
          omega⟩

/-! ## 3. Both colors commute with the local mate -/

/-- The left colored copy is closed under the exact local mate of the summed
resolution. -/
theorem trivalentStrandPortInSumLeft_mate
    {a b c a' b' c' : Nat}
    (left : TrivalentStrandResolution a b c)
    (right : TrivalentStrandResolution a' b' c')
    (port : TrivalentStrandPort a b c) :
    trivalentStrandPortInSumLeft left right (strandMate left port) =
      strandMate (addTrivalentStrandResolutions left right)
        (trivalentStrandPortInSumLeft left right port) := by
  cases port with
  | onA slot =>
      by_cases hca : slot.val < left.ca
      · have hsumCa : slot.val < left.ca + right.ca := by omega
        have hleftC : ¬ left.bc + slot.val < left.bc := by omega
        simp [strandMate, hca,
          trivalentStrandPortInSumLeft, hsumCa, hleftC,
          TrivalentStrandResolution.add_bc,
          TrivalentStrandResolution.add_ca]
      · have hsumNotCa :
            ¬ left.ca + right.ca + (slot.val - left.ca) <
              left.ca + right.ca := by omega
        have hleftB :
            ¬ left.bc + (slot.val - left.ca) < left.bc := by omega
        simp [strandMate, hca,
          trivalentStrandPortInSumLeft, hsumNotCa, hleftB,
          TrivalentStrandResolution.add_bc,
          TrivalentStrandResolution.add_ca]
  | onB slot =>
      by_cases hbc : slot.val < left.bc
      · have hsumBc : slot.val < left.bc + right.bc := by omega
        simp [strandMate, hbc,
          trivalentStrandPortInSumLeft, hsumBc,
          TrivalentStrandResolution.add_bc]
      · have hsumNotBc :
            ¬ left.bc + right.bc + (slot.val - left.bc) <
              left.bc + right.bc := by omega
        have hleftA :
            ¬ left.ca + (slot.val - left.bc) < left.ca := by omega
        simp [strandMate, hbc,
          trivalentStrandPortInSumLeft, hsumNotBc, hleftA,
          TrivalentStrandResolution.add_bc,
          TrivalentStrandResolution.add_ca]
  | onC slot =>
      by_cases hbc : slot.val < left.bc
      · have hsumBc : slot.val < left.bc + right.bc := by omega
        simp [strandMate, hbc,
          trivalentStrandPortInSumLeft, hsumBc,
          TrivalentStrandResolution.add_bc]
      · have hsumNotBc :
            ¬ left.bc + right.bc + (slot.val - left.bc) <
              left.bc + right.bc := by omega
        have hleftA : slot.val - left.bc < left.ca := by
          have hc := left.c_balance
          omega
        simp [strandMate, hbc,
          trivalentStrandPortInSumLeft, hsumNotBc, hleftA,
          TrivalentStrandResolution.add_bc]

/-- The right colored copy is also closed under the summed local mate. -/
theorem trivalentStrandPortInSumRight_mate
    {a b c a' b' c' : Nat}
    (left : TrivalentStrandResolution a b c)
    (right : TrivalentStrandResolution a' b' c')
    (port : TrivalentStrandPort a' b' c') :
    trivalentStrandPortInSumRight left right (strandMate right port) =
      strandMate (addTrivalentStrandResolutions left right)
        (trivalentStrandPortInSumRight left right port) := by
  cases port with
  | onA slot =>
      by_cases hca : slot.val < right.ca
      · have hsumCa : left.ca + slot.val < left.ca + right.ca := by omega
        have hrightC : ¬ right.bc + slot.val < right.bc := by omega
        simp [strandMate, hca,
          trivalentStrandPortInSumRight, hsumCa, hrightC,
          TrivalentStrandResolution.add_bc,
          TrivalentStrandResolution.add_ca]
        omega
      · have hsumNotCa :
            ¬ left.ca + right.ca + left.ab +
                (slot.val - right.ca) < left.ca + right.ca := by omega
        have hrightB :
            ¬ right.bc + (slot.val - right.ca) < right.bc := by omega
        simp [strandMate, hca,
          trivalentStrandPortInSumRight, hsumNotCa, hrightB,
          TrivalentStrandResolution.add_bc,
          TrivalentStrandResolution.add_ca]
        omega
  | onB slot =>
      by_cases hbc : slot.val < right.bc
      · have hsumBc : left.bc + slot.val < left.bc + right.bc := by omega
        simp [strandMate, hbc,
          trivalentStrandPortInSumRight, hsumBc,
          TrivalentStrandResolution.add_bc]
      · have hsumNotBc :
            ¬ left.bc + right.bc + left.ab +
                (slot.val - right.bc) < left.bc + right.bc := by omega
        have hrightA :
            ¬ right.ca + (slot.val - right.bc) < right.ca := by omega
        simp [strandMate, hbc,
          trivalentStrandPortInSumRight, hsumNotBc, hrightA,
          TrivalentStrandResolution.add_bc,
          TrivalentStrandResolution.add_ca]
        omega
  | onC slot =>
      by_cases hbc : slot.val < right.bc
      · have hsumBc : left.bc + slot.val < left.bc + right.bc := by omega
        simp [strandMate, hbc,
          trivalentStrandPortInSumRight, hsumBc,
          TrivalentStrandResolution.add_bc]
      · have hsumNotBc :
            ¬ left.bc + right.bc + left.ca +
                (slot.val - right.bc) < left.bc + right.bc := by omega
        have hrightA : slot.val - right.bc < right.ca := by
          have hc := right.c_balance
          omega
        have hsumA : left.ca + (slot.val - right.bc) <
            left.ca + right.ca := by omega
        simp [strandMate, hbc,
          trivalentStrandPortInSumRight, hsumNotBc, hrightA,
          TrivalentStrandResolution.add_bc]
        omega

end YMGap.Continuum.SU2TrivalentStrandPortAddition

#print axioms YMGap.Continuum.SU2TrivalentStrandPortAddition.trivalentStrandPortInSumLeft
#print axioms YMGap.Continuum.SU2TrivalentStrandPortAddition.trivalentStrandPortInSumRight
#print axioms YMGap.Continuum.SU2TrivalentStrandPortAddition.trivalentStrandPortInSumLeft_mate
#print axioms YMGap.Continuum.SU2TrivalentStrandPortAddition.trivalentStrandPortInSumRight_mate
