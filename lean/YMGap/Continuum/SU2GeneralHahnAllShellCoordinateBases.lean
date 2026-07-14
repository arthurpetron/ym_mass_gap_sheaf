/-
# Every physical Hahn shell as a constructive coordinate basis

The exact physical source-coordinate window is equipped with the all-shell
Hahn action and its explicit recursive inverse.  Constructive injectivity
gives semantic reconstruction, while the simultaneous right inverse gives
coordinate reconstruction.  Actual shell-prefix realization identifies the
package with the leakage-free binary-form synthesis on every shell.
-/

import YMGap.Continuum.SU2GeneralHahnAllShellCoordinateEquivalence
import YMGap.Continuum.PentagonFromCoordinateBases

namespace YMGap.Continuum.SU2GeneralHahnAllShellCoordinateBases

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2GeneralHahnCumulativeTransform
open YMGap.Continuum.SU2GeneralHahnCentralShellBasis
open YMGap.Continuum.SU2GeneralHahnAllShellColumnElimination
open YMGap.Continuum.SU2GeneralHahnAllShellRecursiveSolver
open YMGap.Continuum.SU2GeneralHahnAllShellBasis
open YMGap.Continuum.SU2GeneralHahnAllShellCoordinateEquivalence
open YMGap.Continuum.PentagonFromCoordinateBases

local infix:50 " ≈ " => Q'.eqv

/-- Extend an exact finite physical-channel vector by zero without choice. -/
def boundedAllShellChannels {m n t : Nat}
    (c : Fin (shellWidth m n t + 1) → Q') : Nat → Q' :=
  fun r => if hr : r < shellWidth m n t + 1 then c ⟨r, hr⟩ else 0

theorem boundedAllShellChannels_apply {m n t : Nat}
    (c : Fin (shellWidth m n t + 1) → Q')
    (r : Fin (shellWidth m n t + 1)) :
    boundedAllShellChannels c r.val ≈ c r := by
  unfold boundedAllShellChannels
  rw [dif_pos r.isLt]
  exact Q'.eqv_refl _

private theorem finiteDot_fixed_row_congr (N : Nat)
    (row x z : Nat → Q')
    (hxz : ∀ i, i < N → x i ≈ z i) :
    finiteDot N row x ≈ finiteDot N row z := by
  induction N generalizing row x z with
  | zero => exact Q'.eqv_refl _
  | succ N ih =>
      simp only [finiteDot]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ (hxz 0 (by omega)))
        (ih _ _ _ (fun i hi => hxz (i + 1) (by omega)))

/-- The physical Hahn row map observes exactly the active source window. -/
theorem physicalHahnAction_congr (m n t : Nat) (x z : Nat → Q')
    (hxz : ∀ i, i < shellWidth m n t + 1 → x i ≈ z i) :
    ∀ r, physicalHahnAction m n t x r ≈
      physicalHahnAction m n t z r := by
  intro r
  exact finiteDot_fixed_row_congr (shellWidth m n t + 1) _ _ _ hxz

/-- **All-shell direct-sum coordinate basis.**  The semantic carrier is the
active physical source-coordinate window and the coordinates are all active
contraction channels simultaneously. -/
def allShellCoordinateBases (m n t : Nat) (ht : t ≤ m + n) :
    CoordinateBases Unit (Nat → Q') where
  Index := fun _ => Fin (shellWidth m n t + 1)
  Rel := fun x z => ∀ i, i < shellWidth m n t + 1 → x i ≈ z i
  rel_refl := fun x i hi => Q'.eqv_refl _
  rel_symm := fun h i hi => Q'.eqv_symm (h i hi)
  rel_trans := fun h₁ h₂ i hi => Q'.eqv_trans _ _ _ (h₁ i hi) (h₂ i hi)
  synth := fun _ c =>
    allShellHahnSolve m n t ht (boundedAllShellChannels c)
  coords := fun _ x r => physicalHahnAction m n t x r.val
  coords_congr := by
    intro T x z hxz r
    exact physicalHahnAction_congr m n t x z hxz r.val
  synth_coords := by
    intro T x
    apply physicalHahnAction_injective m n t ht
    intro r hr
    let c : Fin (shellWidth m n t + 1) → Q' :=
      fun q => physicalHahnAction m n t x q.val
    have hright := allShellHahnSolve_rightInverse m n t ht
      (boundedAllShellChannels c) r hr
    refine Q'.eqv_trans _ (boundedAllShellChannels c r) _ hright ?_
    unfold boundedAllShellChannels
    rw [dif_pos hr]
    exact Q'.eqv_refl _
  coords_synth := by
    intro T c r
    have hright := allShellHahnSolve_rightInverse m n t ht
      (boundedAllShellChannels c) r.val r.isLt
    exact Q'.eqv_trans _ _ _ hright (boundedAllShellChannels_apply c r)

/-- Realize the active physical source vector as an actual shell tensor sum. -/
def allShellRealize (m n t : Nat) (x : Nat → Q') :
    YMGap.Continuum.TransvectantCG.BForm2 :=
  shellSourcePrefix t (shellWidth m n t + 1)
    (fun a => shellLo n t + a) x

/-- Packaged coordinate synthesis followed by actual realization is
definitionally the all-shell tensor synthesis. -/
theorem allShellRealize_synth (m n t : Nat) (ht : t ≤ m + n)
    (c : Fin (shellWidth m n t + 1) → Q') :
    allShellRealize m n t
        ((allShellCoordinateBases m n t ht).synth () c) =
      allShellSynth m n t ht (boundedAllShellChannels c) := by
  rfl

/-- **Physical realization of the all-shell coordinate package.**  Every
finite coordinate is realized as exactly its prescribed complete output
monomial under the corresponding transvectant. -/
theorem allShellCoordinateBases_realizes (m n t : Nat)
    (ht : t ≤ m + n)
    (c : Fin (shellWidth m n t + 1) → Q')
    (r : Fin (shellWidth m n t + 1)) :
    BFormEqv
      (YMGap.Continuum.TransvectantCG.transvect m n r.val
        (allShellRealize m n t
          ((allShellCoordinateBases m n t ht).synth () c)))
      (fun s => c r * mono (t - r.val) s) := by
  rw [allShellRealize_synth]
  intro s
  have h := allShellSynth_channels m n t ht
    (boundedAllShellChannels c) r.val r.isLt s
  refine Q'.eqv_trans _
    (boundedAllShellChannels c r.val * mono (t - r.val) s) _ h ?_
  exact Q'.mul_eqv_congr_right _ _ _ (boundedAllShellChannels_apply c r)

end YMGap.Continuum.SU2GeneralHahnAllShellCoordinateBases

#print axioms YMGap.Continuum.SU2GeneralHahnAllShellCoordinateBases.physicalHahnAction_congr
#print axioms YMGap.Continuum.SU2GeneralHahnAllShellCoordinateBases.allShellCoordinateBases
#print axioms YMGap.Continuum.SU2GeneralHahnAllShellCoordinateBases.allShellRealize_synth
#print axioms YMGap.Continuum.SU2GeneralHahnAllShellCoordinateBases.allShellCoordinateBases_realizes
