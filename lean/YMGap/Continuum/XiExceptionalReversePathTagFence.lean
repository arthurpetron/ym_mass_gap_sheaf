/-
# Reversed canonical paths cannot tag a positive target term

The exceptional canonical path starts at the marked polymer and ends at a
`b2` polymer.  Reversing it would provide an attractive orientation tag, but
the reversed chain ends at the marked polymer.  That polymer belongs to the
original right source family, which is pointwise `!b2`; hence its terminal
chain weight is zero.  This holds for every background and external family.
-/

import YMGap.Continuum.XiExceptionalTwoSidedOriginalCarrier

namespace YMGap.Continuum.XiExceptionalReversePathTagFence

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalSafeCarrierWeight
open YMGap.Continuum.XiExceptionalBranchPacking

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

private theorem polymerIncompatSymm (X Y : Polymer L)
    (h : (!(compatibleB X Y)) = true) :
    (!(compatibleB Y X)) = true := by
  rw [compatibleB_symm Y X]
  exact h

/-- A chain whose terminal polymer fails `b2` has zero weight, independently
of all earlier steps and of the terminal background. -/
theorem chainCodeOfWalk_weight_zero_of_terminal_b2_false
    (w : Q') (qP b2 : Polymer L → Bool)
    (Gamma background : List (Polymer L))
    (label : L.Plaquette → Rep) :
    ∀ {X Y : Polymer L}
      (walk : CWalk (fun A B : Polymer L => !(compatibleB A B)) X Y)
      (bg : Polymer L → Bool),
      b2 Y = false →
      chainCodeWeight w qP b2 Gamma label X bg
          (chainCodeOfWalk walk background) ≈ 0
  | _, _, .single _, bg, hb2 => by
      simp only [chainCodeOfWalk, chainCodeWeight, hb2, Bool.and_false]
      exact Q'.eqv_refl _
  | _, _, .cons hedge rest, bg, hb2 => by
      unfold chainCodeOfWalk chainCodeWeight
      split
      · exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (chainCodeOfWalk_weight_zero_of_terminal_b2_false
              w qP b2 Gamma background label rest
              (fun T => bg T && compatibleB _ T) hb2))
          (Q'.mul_zero_eqv _)
      · exact Q'.mul_zero_eqv _

theorem exceptional_marked_b2_false
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    b2 (polyAt Gamma
      (exceptionalMarkedIndex Gamma b1 b2 entry.1)) = false := by
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  have hgood := facts.right_good
    (exceptionalMarkedIndex Gamma b1 b2 entry.1)
    facts.marked_right_true
  exact hgood

def reversedPathCarrierXiCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (background external : List (Polymer L)) : CarrierXiCode L :=
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  (((polyAt Gamma path.seed,
      chainCodeOfWalk (path.polymerWalk.reverse polymerIncompatSymm)
        background)), external)

/-- The proposed reversed-path tag is an actual zero-weight carrier term for
every choice of background and external payload. -/
theorem reversedPathCarrierXiCode_weight_zero
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (background external : List (Polymer L)) :
    carrierXiCodeWeight w qP b1 b2 Gamma label
      (reversedPathCarrierXiCode Gamma qP b1 b2 entry
        background external) ≈ 0 := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  have hterminal : b2 (polyAt Gamma
      (exceptionalMarkedIndex Gamma b1 b2 pair)) = false :=
    exceptional_marked_b2_false Gamma qP b1 b2 entry
  have hchain := chainCodeOfWalk_weight_zero_of_terminal_b2_false
    w qP b2 Gamma background label
    (path.polymerWalk.reverse polymerIncompatSymm) (fun _ => true) hterminal
  unfold reversedPathCarrierXiCode carrierXiCodeWeight carrierCodeWeight
  dsimp only
  split
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hchain)
      (Q'.zero_mul_eqv _)
  · exact Q'.zero_mul_eqv _

#print axioms chainCodeOfWalk_weight_zero_of_terminal_b2_false
#print axioms exceptional_marked_b2_false
#print axioms reversedPathCarrierXiCode_weight_zero

end YMGap.Continuum.XiExceptionalReversePathTagFence
