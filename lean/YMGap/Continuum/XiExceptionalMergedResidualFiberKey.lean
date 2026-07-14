/-
# Fixed-right fibres of the merged residual carrier

The merged external mask forgets only the left/right colouring.  Once the
right residual is fixed, disjoint union cancellation recovers the left
residual.  Replacing the empty terminal background in the merged carrier by
that recovered left mask reconstructs the old two-sided carrier, hence the
source entry.  Thus all merged-carrier collisions necessarily cross distinct
right-residual keys.

The final theorem lifts any fixed-right exact-payment region globally through
the existing finite fibrewise summation theorem.  This does not assume that
different right keys are disjoint; those cross-key fibres remain the next
allocation problem.
-/

import YMGap.Continuum.XiExceptionalMergedResidualCarrier
import YMGap.Continuum.XiExceptionalFiberwiseInjection
import YMGap.Continuum.XiExceptionalTargetNodup

namespace YMGap.Continuum.XiExceptionalMergedResidualFiberKey

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalFiberwiseInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalCustomCarrier
open YMGap.Continuum.XiExceptionalParallelExternalFamily
open YMGap.Continuum.XiExceptionalParallelResidualBlock
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
open YMGap.Continuum.XiExceptionalTwoSidedOriginalCarrier
open YMGap.Continuum.XiExceptionalMergedResidualCarrier
open YMGap.Continuum.XiExceptionalTargetNodup

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## Disjoint-union cancellation -/

private theorem bool_or_left_cancel_of_right_eq
    (a₁ r₁ a₂ r₂ : Bool)
    (hu : (a₁ || r₁) = (a₂ || r₂))
    (hr : r₁ = r₂)
    (hd₁ : a₁ = true → r₁ = false)
    (hd₂ : a₂ = true → r₂ = false) : a₁ = a₂ := by
  subst r₂
  cases hr₁ : r₁ with
  | false => simpa [hr₁] using hu
  | true =>
      have ha₁ : a₁ = false := by
        cases ha : a₁ with
        | false => rfl
        | true =>
            have hbad := hd₁ ha
            rw [hr₁] at hbad
            cases hbad
      have ha₂ : a₂ = false := by
        cases ha : a₂ with
        | false => rfl
        | true =>
            have hbad := hd₂ ha
            rw [hr₁] at hbad
            cases hbad
      exact ha₁.trans ha₂.symm

theorem unionBits_left_cancel {n : Nat}
    (left₁ right₁ left₂ right₂ : OccBitVec n)
    (hu : unionBits left₁ right₁ = unionBits left₂ right₂)
    (hr : right₁ = right₂)
    (hd₁ : DisjointBits left₁ right₁)
    (hd₂ : DisjointBits left₂ right₂) : left₁ = left₂ := by
  apply BitVec.ext
  intro i
  have hui := congrArg (fun bits => bits.at i) hu
  change (unionBits left₁ right₁).at i =
    (unionBits left₂ right₂).at i at hui
  rw [unionBits_at, unionBits_at] at hui
  have hri := congrArg (fun bits => bits.at i) hr
  exact bool_or_left_cancel_of_right_eq
    (left₁.at i) (right₁.at i) (left₂.at i) (right₂.at i)
    hui hri (hd₁ i) (hd₂ i)

/-! ## Replacing the terminal background in an occurrence chain -/

def setTerminalBackground {n : Nat} :
    OccChainCode n → OccBitVec n → OccChainCode n
  | .terminal _, background => .terminal background
  | .step next rest, background =>
      .step next (setTerminalBackground rest background)

theorem setTerminalBackground_ofWalk
    {edge : Nat → Nat → Bool} {start finish : Nat}
    (walk : CWalk edge start finish)
    (oldBackground newBackground : OccBitVec n) :
    setTerminalBackground
        (occurrenceChainCodeOfWalk walk oldBackground) newBackground =
      occurrenceChainCodeOfWalk walk newBackground := by
  induction walk with
  | single _ => rfl
  | cons _ rest ih =>
      simp only [occurrenceChainCodeOfWalk, setTerminalBackground]
      rw [ih]

private theorem occCarrierXiCode_eq_of_fields
    {Gamma : List (Polymer L)} (code₁ code₂ : OccCarrierXiCodeAt Gamma)
    (hstart : code₁.carrier.start = code₂.carrier.start)
    (hchain : code₁.carrier.chain = code₂.carrier.chain)
    (hexternal : code₁.external = code₂.external) : code₁ = code₂ := by
  cases code₁ with
  | mk carrier₁ external₁ =>
      cases code₂ with
      | mk carrier₂ external₂ =>
          cases carrier₁ with
          | mk start₁ chain₁ =>
              cases carrier₂ with
              | mk start₂ chain₂ =>
                  cases hstart
                  cases hchain
                  cases hexternal
                  rfl

/-! ## The fixed-right key restores injectivity -/

theorem mergedResidualCarrierCode_injective_of_right_eq
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry₁ entry₂ : ExceptionalSourceEntry Gamma qP b1 b2)
    (hd₁ : DisjointBits
      (leftPathResidual Gamma qP b1 b2 entry₁)
      (rightPathResidual Gamma qP b1 b2 entry₁))
    (hd₂ : DisjointBits
      (leftPathResidual Gamma qP b1 b2 entry₂)
      (rightPathResidual Gamma qP b1 b2 entry₂))
    (hright : rightPathResidual Gamma qP b1 b2 entry₁ =
      rightPathResidual Gamma qP b1 b2 entry₂)
    (hcode : mergedResidualCarrierCode Gamma qP b1 b2 entry₁ =
      mergedResidualCarrierCode Gamma qP b1 b2 entry₂) :
    entry₁ = entry₂ := by
  let left₁ := leftPathResidual Gamma qP b1 b2 entry₁
  let right₁ := rightPathResidual Gamma qP b1 b2 entry₁
  let left₂ := leftPathResidual Gamma qP b1 b2 entry₂
  let right₂ := rightPathResidual Gamma qP b1 b2 entry₂
  let facts₁ := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry₁.1 entry₁.2
  let facts₂ := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry₂.1 entry₂.2
  let path₁ := sourceExceptionalPath Gamma qP b1 b2 entry₁.1 facts₁
  let path₂ := sourceExceptionalPath Gamma qP b1 b2 entry₂.1 facts₂
  have hunion : unionBits left₁ right₁ = unionBits left₂ right₂ := by
    have h := congrArg (fun code => code.external) hcode
    simpa [mergedResidualCarrierCode, mergedResidualBits,
      exceptionalCustomCarrierCode, left₁, right₁, left₂, right₂]
      using h
  have hleft : left₁ = left₂ :=
    unionBits_left_cancel left₁ right₁ left₂ right₂ hunion
      (by simpa [right₁, right₂] using hright)
      (by simpa [left₁, right₁] using hd₁)
      (by simpa [left₂, right₂] using hd₂)
  have hstart : exceptionalMarkedIndex Gamma b1 b2 entry₁.1 =
      exceptionalMarkedIndex Gamma b1 b2 entry₂.1 := by
    have h := congrArg (fun code => code.carrier.start) hcode
    simpa [mergedResidualCarrierCode, exceptionalCustomCarrierCode] using h
  have hchainEmpty :
      occurrenceChainCodeOfWalk path₁.indexWalk (emptyOccurrenceBits Gamma) =
        occurrenceChainCodeOfWalk path₂.indexWalk
          (emptyOccurrenceBits Gamma) := by
    have h := congrArg (fun code => code.carrier.chain) hcode
    simpa [mergedResidualCarrierCode, exceptionalCustomCarrierCode,
      path₁, path₂, facts₁, facts₂] using h
  have hchain : occurrenceChainCodeOfWalk path₁.indexWalk left₁ =
      occurrenceChainCodeOfWalk path₂.indexWalk left₂ := by
    refine Eq.trans (Eq.symm
      (setTerminalBackground_ofWalk path₁.indexWalk
        (emptyOccurrenceBits Gamma) left₁)) ?_
    refine Eq.trans ?_
      (setTerminalBackground_ofWalk path₂.indexWalk
        (emptyOccurrenceBits Gamma) left₂)
    rw [hchainEmpty, hleft]
  apply originalTwoSidedCarrierCode_injective Gamma qP b1 b2 entry₁ entry₂
  apply occCarrierXiCode_eq_of_fields
  · simpa [originalTwoSidedCarrierCode, exceptionalCustomCarrierCode]
      using hstart
  · simpa [originalTwoSidedCarrierCode, exceptionalCustomCarrierCode,
      path₁, path₂, facts₁, facts₂, left₁, left₂] using hchain
  · simpa [originalTwoSidedCarrierCode, exceptionalCustomCarrierCode,
      right₁, right₂] using hright

/-! ## Fibrewise lift of a fixed-right region -/

private theorem qListSum_le_of_fibers_of_injective [DecidableEq β]
    (source : List α) (target : List β)
    (sourceWeight : α → Q') (targetWeight : β → Q')
    (encode : α → β)
    (hsource : source.Nodup)
    (htarget : target.Nodup)
    (hmem : ∀ x, x ∈ source → encode x ∈ target)
    (hinjective : ∀ x, x ∈ source → ∀ y, y ∈ source →
      encode x = encode y → x = y)
    (hterm : ∀ x, x ∈ source →
      sourceWeight x ≤ targetWeight (encode x))
    (hsourceNonneg : ∀ x, x ∈ source → (0 : Q') ≤ sourceWeight x)
    (htargetNonneg : ∀ y, y ∈ target → (0 : Q') ≤ targetWeight y) :
    qListSum sourceWeight source ≤ qListSum targetWeight target := by
  apply qListSum_le_of_fibers source target sourceWeight targetWeight encode
    htarget hmem hsourceNonneg
  intro y hy
  let fiber := source.filter (fun x => decide (encode x = y))
  have hfiberNodup : fiber.Nodup :=
    nodup_filter_bool _ source hsource
  have hlocal := qListSum_le_of_injective fiber [y]
    sourceWeight targetWeight encode hfiberNodup
  have hbound : qListSum sourceWeight fiber ≤ qListSum targetWeight [y] := by
    apply hlocal
    · intro x hx
      have hp := List.mem_filter.mp hx
      exact List.mem_singleton.mpr (of_decide_eq_true hp.2)
    · intro x hx z hz heq
      exact hinjective x (List.mem_filter.mp hx).1
        z (List.mem_filter.mp hz).1 heq
    · intro x hx
      exact hterm x (List.mem_filter.mp hx).1
    · intro z hz
      rw [List.mem_singleton.mp hz]
      exact htargetNonneg y hy
  exact Q'.le_trans' _ _ _ hbound
    (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' (targetWeight y))))

theorem mergedResidual_fixedRight_region_global_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (source : List (ExceptionalSourceEntry Gamma qP b1 b2))
    (hsource : source.Nodup)
    (rightKey : OccBitVec Gamma.length)
    (hright : ∀ entry, entry ∈ source →
      rightPathResidual Gamma qP b1 b2 entry = rightKey)
    (hdisjoint : ∀ entry, entry ∈ source → DisjointBits
      (leftPathResidual Gamma qP b1 b2 entry)
      (rightPathResidual Gamma qP b1 b2 entry))
    (hcompatible : ∀ entry, entry ∈ source → familyCompatibleB
      (selectByBits Gamma
        (mergedResidualBits Gamma qP b1 b2 entry)) = true)
    (hq : ∀ entry, entry ∈ source →
      (selectByBits Gamma
        (mergedResidualBits Gamma qP b1 b2 entry)).all qP = true) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) source ≤
      qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  apply qListSum_le_of_fibers_of_injective source
    (occurrenceCarrierXiCodes Gamma)
    (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
    (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
    (mergedResidualCarrierCode Gamma qP b1 b2)
    hsource (occurrenceCarrierXiCodes_nodup Gamma)
  · intro entry _
    exact mergedResidualCarrierCode_mem Gamma qP b1 b2 entry
  · intro entry₁ h₁ entry₂ h₂ hcode
    exact mergedResidualCarrierCode_injective_of_right_eq
      Gamma qP b1 b2 entry₁ entry₂
      (hdisjoint entry₁ h₁) (hdisjoint entry₂ h₂)
      ((hright entry₁ h₁).trans (hright entry₂ h₂).symm) hcode
  · intro entry hentry
    exact Q'.le_of_eqv (Q'.eqv_symm
      (mergedResidualCarrierCode_weight_eqv_source
        w qP b1 b2 Gamma label entry (hdisjoint entry hentry)
        (hcompatible entry hentry) (hq entry hentry)))
  · intro entry hentry
    unfold occurrencePairWeight
    exact Q'.mul_nonneg _ _
      (admissibleFamilyWeight_nonnegative hw _ label _)
      (admissibleFamilyWeight_nonnegative hw _ label _)
  · intro code _
    exact occurrenceCarrierXiCodeWeight_nonnegative hw
      qP b1 b2 Gamma label code

#print axioms unionBits_left_cancel
#print axioms setTerminalBackground_ofWalk
#print axioms mergedResidualCarrierCode_injective_of_right_eq
#print axioms mergedResidual_fixedRight_region_global_bound

end YMGap.Continuum.XiExceptionalMergedResidualFiberKey
