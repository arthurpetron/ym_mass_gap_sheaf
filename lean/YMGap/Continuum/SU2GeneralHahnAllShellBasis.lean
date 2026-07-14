/-
# Leakage-free direct-sum bases on every physical Hahn shell

The all-shell recursive solver is realized as an actual finite sum of
monomial tensors whose source indices are `shellLo n t + a`.  The generic
shell-prefix transvectant theorem then identifies the complete output form in
every active contraction order.  Unit channel data yield a direct-sum basis
with literal zero leakage into all other active orders.
-/

import YMGap.Continuum.SU2GeneralHahnAllShellRecursiveSolver
import YMGap.Continuum.SU2GeneralHahnCentralShellBasis

namespace YMGap.Continuum.SU2GeneralHahnAllShellBasis

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2GeneralHahnCentralShellBasis
open YMGap.Continuum.SU2GeneralHahnAllShellColumnElimination
open YMGap.Continuum.SU2GeneralHahnAllShellRecursiveSolver

local infix:50 " ≈ " => Q'.eqv

/-- Actual tensor synthesis of arbitrary simultaneous channel data on any
nonempty physical shell. -/
def allShellSynth (m n t : Nat) (ht : t ≤ m + n)
    (y : Nat → Q') : YMGap.Continuum.TransvectantCG.BForm2 :=
  shellSourcePrefix t (shellWidth m n t + 1)
    (fun a => shellLo n t + a) (allShellHahnSolve m n t ht y)

/-- **All-shell transvectant/Hahn bridge.**  Every active requested channel
is reproduced as its complete one-monomial output form. -/
theorem allShellSynth_channels (m n t : Nat) (ht : t ≤ m + n)
    (y : Nat → Q') (r : Nat) (hr : r < shellWidth m n t + 1) :
    BFormEqv (YMGap.Continuum.TransvectantCG.transvect m n r
      (allShellSynth m n t ht y))
      (fun s => y r * mono (t - r) s) := by
  intro s
  let x := allShellHahnSolve m n t ht y
  have hcols : ∀ a, a < shellWidth m n t + 1 →
      shellLo n t + a ≤ t := by
    intro a ha
    exact (sourceActive_of_index m n t a ht
      (Nat.lt_succ_iff.mp ha)).1
  have hrow := channelActive_of_index m n t r ht
    (Nat.lt_succ_iff.mp hr)
  have hshell := shellSourcePrefix_transvect_form m n t r
    (shellWidth m n t + 1) (fun a => shellLo n t + a) x
    hcols hrow.2.2.1 s
  have hsolve := allShellHahnSolve_rightInverse m n t ht y r hr
  refine Q'.eqv_trans _
    (physicalHahnAction m n t x r * mono (t - r) s) _ ?_ ?_
  · simpa only [allShellSynth, x, physicalHahnAction,
      physicalHahnMatrix] using hshell
  · exact Q'.mul_eqv_congr_right _ _ _ hsolve

/-- Unit row data for one physical channel. -/
def physicalChannelUnit (q r : Nat) : Q' := if r = q then 1 else 0

/-- Actual source tensor selecting exactly channel `q`. -/
def allShellBasis (m n t : Nat) (ht : t ≤ m + n) (q : Nat) :
    YMGap.Continuum.TransvectantCG.BForm2 :=
  allShellSynth m n t ht (physicalChannelUnit q)

/-- One statement contains the target coefficient and all cross-channel
zeros for the all-shell direct-sum basis. -/
theorem allShellBasis_channels (m n t : Nat) (ht : t ≤ m + n)
    (q r : Nat) (hr : r < shellWidth m n t + 1) :
    BFormEqv (YMGap.Continuum.TransvectantCG.transvect m n r
      (allShellBasis m n t ht q))
      (fun s => physicalChannelUnit q r * mono (t - r) s) :=
  allShellSynth_channels m n t ht (physicalChannelUnit q) r hr

/-- The selected active channel is exactly its output monomial. -/
theorem allShellBasis_target (m n t : Nat) (ht : t ≤ m + n)
    (q : Nat) (hq : q < shellWidth m n t + 1) :
    BFormEqv (YMGap.Continuum.TransvectantCG.transvect m n q
      (allShellBasis m n t ht q)) (mono (t - q)) := by
  intro s
  have h := allShellBasis_channels m n t ht q q hq s
  refine Q'.eqv_trans _ (1 * mono (t - q) s) _ ?_ ?_
  · simpa only [physicalChannelUnit, if_pos] using h
  · exact Q'.one_mul_eqv _

/-- Every other active contraction order vanishes as a complete output form. -/
theorem allShellBasis_noLeak (m n t : Nat) (ht : t ≤ m + n)
    (q r : Nat) (hr : r < shellWidth m n t + 1) (hrq : ¬ r = q) :
    BFormEqv (YMGap.Continuum.TransvectantCG.transvect m n r
      (allShellBasis m n t ht q)) zeroF := by
  intro s
  have h := allShellBasis_channels m n t ht q r hr s
  refine Q'.eqv_trans _ (0 * mono (t - r) s) _ ?_ ?_
  · simpa only [physicalChannelUnit, if_neg hrq] using h
  · exact Q'.zero_mul_eqv _

end YMGap.Continuum.SU2GeneralHahnAllShellBasis

#print axioms YMGap.Continuum.SU2GeneralHahnAllShellBasis.allShellSynth_channels
#print axioms YMGap.Continuum.SU2GeneralHahnAllShellBasis.allShellBasis_target
#print axioms YMGap.Continuum.SU2GeneralHahnAllShellBasis.allShellBasis_noLeak
