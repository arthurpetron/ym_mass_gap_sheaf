/-
# Recoverable routing of exceptional branches

A terminal background has to be compatible with the extracted path.  This
file gives a finite occurrence router which can move selected left-mask bits
to the external slot without losing their side information.  At an occurrence
declared safe, the two target bits store left and right separately.  At an
unsafe occurrence, the background bit is forced to zero and the external bit
stores the left bit; recoverability therefore has the exact side condition
that the right bit is absent there.

The resulting routed carrier is an actual target code and is injective on any
exceptional source region satisfying that side condition.  A closed one-bit
counterexample records that the condition is information-theoretically sharp:
without it, an unsafe left bit and an unsafe right bit have the same routed
code.
-/

import YMGap.Continuum.XiExceptionalCustomCarrier

namespace YMGap.Continuum.XiExceptionalBranchRouter

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalCustomCarrier

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

/-! ## 1. A two-slot occurrence router -/

def routedBackground (safe : Nat → Bool) (left : OccBitVec n) :
    OccBitVec n :=
  bitsFromMask n (fun i => safe i && left.at i) 0

def routedExternal (safe : Nat → Bool)
    (left right : OccBitVec n) : OccBitVec n :=
  bitsFromMask n (fun i => ((!safe i) && left.at i) || right.at i) 0

def routedMaskPair (safe : Nat → Bool)
    (left right : OccBitVec n) : MaskPair n :=
  (routedBackground safe left, routedExternal safe left right)

theorem routedBackground_at (safe : Nat → Bool) (left : OccBitVec n)
    (i : Nat) (hi : i < n) :
    (routedBackground safe left).at i = (safe i && left.at i) := by
  unfold routedBackground
  simpa using bitsFromMask_at n (fun j => safe j && left.at j) 0 i hi

theorem routedExternal_at (safe : Nat → Bool)
    (left right : OccBitVec n) (i : Nat) (hi : i < n) :
    (routedExternal safe left right).at i =
      (((!safe i) && left.at i) || right.at i) := by
  unfold routedExternal
  simpa using bitsFromMask_at n
    (fun j => ((!safe j) && left.at j) || right.at j) 0 i hi

private theorem right_false_at_unsafe
    (safe : Nat → Bool) (right : OccBitVec n)
    (hrightSafe : ∀ i, i < n → right.at i = true → safe i = true)
    (i : Nat) (hi : i < n) (hunsafe : safe i = false) :
    right.at i = false := by
  cases hright : right.at i with
  | false => rfl
  | true =>
      have hs := hrightSafe i hi hright
      rw [hunsafe] at hs
      cases hs

/-- The routed pair retains both input masks whenever right bits occur only
at safe indices. -/
theorem routedMaskPair_injective_of_right_safe
    (safe : Nat → Bool)
    (left1 right1 left2 right2 : OccBitVec n)
    (hrightSafe1 : ∀ i, i < n → right1.at i = true → safe i = true)
    (hrightSafe2 : ∀ i, i < n → right2.at i = true → safe i = true)
    (hroute : routedMaskPair safe left1 right1 =
      routedMaskPair safe left2 right2) :
    (left1, right1) = (left2, right2) := by
  have hbackground : routedBackground safe left1 =
      routedBackground safe left2 := congrArg Prod.fst hroute
  have hexternal : routedExternal safe left1 right1 =
      routedExternal safe left2 right2 := congrArg Prod.snd hroute
  apply Prod.ext
  · change left1 = left2
    apply BitVec.ext
    intro i
    by_cases hi : i < n
    · have hbg := congrArg (fun bits => bits.at i) hbackground
      have hext := congrArg (fun bits => bits.at i) hexternal
      change (routedBackground safe left1).at i =
        (routedBackground safe left2).at i at hbg
      change (routedExternal safe left1 right1).at i =
        (routedExternal safe left2 right2).at i at hext
      rw [routedBackground_at safe left1 i hi,
        routedBackground_at safe left2 i hi] at hbg
      rw [routedExternal_at safe left1 right1 i hi,
        routedExternal_at safe left2 right2 i hi] at hext
      cases hsafe : safe i with
      | true => simpa [hsafe] using hbg
      | false =>
          have hr1 := right_false_at_unsafe safe right1 hrightSafe1
            i hi hsafe
          have hr2 := right_false_at_unsafe safe right2 hrightSafe2
            i hi hsafe
          simpa [hsafe, hr1, hr2] using hext
    · have hge : n ≤ i := by omega
      exact (bitVec_at_false_of_ge left1 i hge).trans
        (bitVec_at_false_of_ge left2 i hge).symm
  · change right1 = right2
    apply BitVec.ext
    intro i
    by_cases hi : i < n
    · have hext := congrArg (fun bits => bits.at i) hexternal
      change (routedExternal safe left1 right1).at i =
        (routedExternal safe left2 right2).at i at hext
      rw [routedExternal_at safe left1 right1 i hi,
        routedExternal_at safe left2 right2 i hi] at hext
      cases hsafe : safe i with
      | true => simpa [hsafe] using hext
      | false =>
          have hr1 := right_false_at_unsafe safe right1 hrightSafe1
            i hi hsafe
          have hr2 := right_false_at_unsafe safe right2 hrightSafe2
            i hi hsafe
          exact hr1.trans hr2.symm
    · have hge : n ≤ i := by omega
      exact (bitVec_at_false_of_ge right1 i hge).trans
        (bitVec_at_false_of_ge right2 i hge).symm

/-! ## 2. Routed exceptional carrier codes -/

def exceptionalRoutedCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (safe : Nat → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccCarrierXiCodeAt Gamma :=
  let switched := switchedBranchCode Gamma b2 entry.1
  exceptionalCustomCarrierCode Gamma qP b1 b2 entry
    (routedBackground safe switched.1)
    (routedExternal safe switched.1 switched.2)

theorem exceptionalRoutedCarrierCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (safe : Nat → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    exceptionalRoutedCarrierCode Gamma qP b1 b2 safe entry ∈
      occurrenceCarrierXiCodes Gamma := by
  unfold exceptionalRoutedCarrierCode
  exact exceptionalCustomCarrierCode_mem Gamma qP b1 b2 entry _ _

/-- Equality of routed carrier codes recovers the entire exceptional source
entry on a region where the routed-right mask is safe. -/
theorem exceptionalRoutedCarrierCode_injective
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (safe : Nat → Bool)
    (entry1 entry2 : ExceptionalSourceEntry Gamma qP b1 b2)
    (hrightSafe1 : ∀ i, i < Gamma.length →
      (switchedBranchCode Gamma b2 entry1.1).2.at i = true →
        safe i = true)
    (hrightSafe2 : ∀ i, i < Gamma.length →
      (switchedBranchCode Gamma b2 entry2.1).2.at i = true →
        safe i = true)
    (hcode : exceptionalRoutedCarrierCode Gamma qP b1 b2 safe entry1 =
      exceptionalRoutedCarrierCode Gamma qP b1 b2 safe entry2) :
    entry1 = entry2 := by
  have hbackgroundRaw := congrArg
    (fun code => terminalBackground code.carrier.chain) hcode
  have hbackground :
      routedBackground safe (switchedBranchCode Gamma b2 entry1.1).1 =
        routedBackground safe (switchedBranchCode Gamma b2 entry2.1).1 := by
    simpa [exceptionalRoutedCarrierCode, exceptionalCustomCarrierCode,
      terminalBackground_occurrenceChainCodeOfWalk] using hbackgroundRaw
  have hexternal :
      routedExternal safe (switchedBranchCode Gamma b2 entry1.1).1
          (switchedBranchCode Gamma b2 entry1.1).2 =
        routedExternal safe (switchedBranchCode Gamma b2 entry2.1).1
          (switchedBranchCode Gamma b2 entry2.1).2 := by
    simpa [exceptionalRoutedCarrierCode, exceptionalCustomCarrierCode] using
      congrArg (fun code => code.external) hcode
  have hroute :
      routedMaskPair safe (switchedBranchCode Gamma b2 entry1.1).1
          (switchedBranchCode Gamma b2 entry1.1).2 =
        routedMaskPair safe (switchedBranchCode Gamma b2 entry2.1).1
          (switchedBranchCode Gamma b2 entry2.1).2 := by
    apply Prod.ext
    · exact hbackground
    · exact hexternal
  have hswitch := routedMaskPair_injective_of_right_safe safe
    (switchedBranchCode Gamma b2 entry1.1).1
    (switchedBranchCode Gamma b2 entry1.1).2
    (switchedBranchCode Gamma b2 entry2.1).1
    (switchedBranchCode Gamma b2 entry2.1).2
    hrightSafe1 hrightSafe2 hroute
  have hpairs := switchedBranchCode_injective_on_source Gamma qP b1 b2
    entry1.1 entry2.1 entry1.2 entry2.2 hswitch
  exact Subtype.ext hpairs

/-! ## 3. The exact one-bit capacity fence -/

private def oneTrue : OccBitVec 1 := .cons true .nil
private def oneFalse : OccBitVec 1 := .cons false .nil
private def unsafeLeftPair : MaskPair 1 := (oneTrue, oneFalse)
private def unsafeRightPair : MaskPair 1 := (oneFalse, oneTrue)
private def noSafeIndex : Nat → Bool := fun _ => false

theorem unsafe_side_pairs_ne : unsafeLeftPair ≠ unsafeRightPair := by
  intro hpairs
  have hleft := congrArg (fun pair => pair.1.at 0) hpairs
  cases hleft

/-- If right bits are admitted at unsafe indices, the two available target
bits cannot distinguish the left and right one-bit states once background is
forced to zero. -/
theorem unsafe_side_route_collision :
    routedMaskPair noSafeIndex unsafeLeftPair.1 unsafeLeftPair.2 =
      routedMaskPair noSafeIndex unsafeRightPair.1 unsafeRightPair.2 := by
  rfl

#print axioms routedMaskPair_injective_of_right_safe
#print axioms exceptionalRoutedCarrierCode_mem
#print axioms exceptionalRoutedCarrierCode_injective
#print axioms unsafe_side_pairs_ne
#print axioms unsafe_side_route_collision

end YMGap.Continuum.XiExceptionalBranchRouter
