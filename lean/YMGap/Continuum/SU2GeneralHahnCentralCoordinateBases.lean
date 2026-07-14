/-
# Central Hahn shells as constructive direct-sum coordinate bases

The active source-coordinate window is equipped with the exact channel row
map and the recursive inverse.  Kernel triviality gives semantic
reconstruction, while the right inverse gives coordinate reconstruction.
The resulting object is an actual `PentagonFromCoordinateBases.CoordinateBases`
datum; a separate realization theorem identifies its synthesis with the
leakage-free binary-form vectors from the central shell basis.
-/

import YMGap.Continuum.SU2GeneralHahnCentralShellBasis
import YMGap.Continuum.PentagonFromCoordinateBases

namespace YMGap.Continuum.SU2GeneralHahnCentralCoordinateBases

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2GeneralHahnCumulativeTransform
open YMGap.Continuum.SU2GeneralHahnKernelTrivial
open YMGap.Continuum.SU2GeneralHahnRecursiveSolver
open YMGap.Continuum.SU2GeneralHahnCoordinateEquivalence
open YMGap.Continuum.SU2GeneralHahnCentralShellBasis
open YMGap.Continuum.PentagonFromCoordinateBases

local infix:50 " ≈ " => Q'.eqv

/-- Extend a finite channel vector by zero without choice. -/
def boundedCentralChannels {m : Nat} (c : Fin (m + 1) → Q') : Nat → Q' :=
  fun r => if hr : r < m + 1 then c ⟨r, hr⟩ else 0

theorem boundedCentralChannels_apply {m : Nat}
    (c : Fin (m + 1) → Q') (r : Fin (m + 1)) :
    boundedCentralChannels c r.val ≈ c r := by
  unfold boundedCentralChannels
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

/-- The central Hahn row map respects equality on exactly the active source
window; no values beyond that finite window are observed. -/
theorem centralHahnAction_congr (m n t : Nat) (x z : Nat → Q')
    (hxz : ∀ i, i < m + 1 → x i ≈ z i) :
    ∀ r, centralHahnAction m n t x r ≈ centralHahnAction m n t z r := by
  intro r
  exact finiteDot_fixed_row_congr (m + 1) _ _ _ hxz

/-- **Central-shell direct-sum coordinate basis.**  The semantic carrier is
the finite active source-coordinate window, represented as a total function.
Its coordinates are all active contraction rows simultaneously. -/
def centralShellCoordinateBases (m n t : Nat)
    (hmt : m ≤ t) (htn : t ≤ n) :
    CoordinateBases Unit (Nat → Q') where
  Index := fun _ => Fin (m + 1)
  Rel := fun x z => ∀ i, i < m + 1 → x i ≈ z i
  rel_refl := fun x i hi => Q'.eqv_refl _
  rel_symm := fun h i hi => Q'.eqv_symm (h i hi)
  rel_trans := fun h₁ h₂ i hi => Q'.eqv_trans _ _ _ (h₁ i hi) (h₂ i hi)
  synth := fun _ c =>
    centralHahnSolve m n t hmt htn (boundedCentralChannels c)
  coords := fun _ x r => centralHahnAction m n t x r.val
  coords_congr := by
    intro T x z hxz r
    exact centralHahnAction_congr m n t x z hxz r.val
  synth_coords := by
    intro T x
    apply centralHahnAction_injective m n t hmt htn
    intro r hr
    let c : Fin (m + 1) → Q' := fun q => centralHahnAction m n t x q.val
    have hright := centralHahnSolve_rightInverse m n t hmt htn
      (boundedCentralChannels c) r hr
    refine Q'.eqv_trans _ (boundedCentralChannels c r) _ hright ?_
    unfold boundedCentralChannels
    rw [dif_pos hr]
    exact Q'.eqv_refl _
  coords_synth := by
    intro T c r
    have hright := centralHahnSolve_rightInverse m n t hmt htn
      (boundedCentralChannels c) r.val r.isLt
    exact Q'.eqv_trans _ _ _ hright (boundedCentralChannels_apply c r)

/-- Realize a finite active source vector as its actual shell tensor sum. -/
def centralShellRealize (m t : Nat) (x : Nat → Q') :
    YMGap.Continuum.TransvectantCG.BForm2 :=
  shellSourcePrefix t (m + 1) (fun q => q) x

/-- Coordinate synthesis followed by actual shell realization is definitionally
the leakage-free central-shell synthesis already proved. -/
theorem centralShellRealize_synth (m n t : Nat)
    (hmt : m ≤ t) (htn : t ≤ n) (c : Fin (m + 1) → Q') :
    centralShellRealize m t
        ((centralShellCoordinateBases m n t hmt htn).synth () c) =
      centralShellSynth m n t hmt htn (boundedCentralChannels c) := by
  rfl

/-- The packaged coordinate basis has the promised physical meaning: each
coordinate is realized as exactly one transvectant output monomial. -/
theorem centralShellCoordinateBases_realizes (m n t : Nat)
    (hmt : m ≤ t) (htn : t ≤ n) (c : Fin (m + 1) → Q')
    (r : Fin (m + 1)) :
    BFormEqv
      (YMGap.Continuum.TransvectantCG.transvect m n r.val
        (centralShellRealize m t
          ((centralShellCoordinateBases m n t hmt htn).synth () c)))
      (fun s => c r * mono (t - r.val) s) := by
  rw [centralShellRealize_synth]
  intro s
  have h := centralShellSynth_channels m n t hmt htn
    (boundedCentralChannels c) r.val r.isLt s
  refine Q'.eqv_trans _ (boundedCentralChannels c r.val * mono (t - r.val) s) _
    h ?_
  exact Q'.mul_eqv_congr_right _ _ _ (boundedCentralChannels_apply c r)

end YMGap.Continuum.SU2GeneralHahnCentralCoordinateBases

#print axioms YMGap.Continuum.SU2GeneralHahnCentralCoordinateBases.centralHahnAction_congr
#print axioms YMGap.Continuum.SU2GeneralHahnCentralCoordinateBases.centralShellCoordinateBases
#print axioms YMGap.Continuum.SU2GeneralHahnCentralCoordinateBases.centralShellCoordinateBases_realizes
