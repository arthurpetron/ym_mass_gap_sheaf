/-
# Constructive coordinate bases for admissible trivalent channels

The explicit transvectant section is packaged as genuine finite coordinates:
synthesis followed by coordinate extraction is the identity, while synthesis
after extraction is equal modulo the kernel of the admissible transvectant.
This is the local round-trip datum needed before composing fusion trees.
-/

import YMGap.Continuum.SU2TransvectantAdmissibleSynthesis

namespace YMGap.Continuum.SU2TransvectantTrivalentCoordinateBasis

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantAdmissibleSynthesis
open YMGap.Continuum.BondMovingStep

def boundedCoeffForm {c : Nat} (v : Fin (c + 1) → Q') : BForm :=
  fun s => if hs : s < c + 1 then v ⟨s, hs⟩ else 0

theorem boundedCoeffForm_apply {c : Nat} (v : Fin (c + 1) → Q')
    (s : Fin (c + 1)) : (boundedCoeffForm v s.val).eqv (v s) := by
  unfold boundedCoeffForm
  rw [dif_pos s.isLt]
  exact Q'.eqv_refl _

/-- Local constructive coordinate-basis data for one guarded trivalent
Clebsch--Gordan channel.  The semantic relation on inputs is equality after
the channel transvectant. -/
structure TrivalentCoordinateBasis (a b c : Nat) where
  synth : (Fin (c + 1) → Q') → BForm2
  coords : BForm2 → Fin (c + 1) → Q'
  coords_synth : ∀ v s, (coords (synth v) s).eqv (v s)
  synth_coords : ∀ input s, s < c + 1 →
    (transvect a b (couplingOrder a b c) (synth (coords input)) s).eqv
      (transvect a b (couplingOrder a b c) input s)

/-- Every admissible trivalent channel has explicit synthesis and coordinate
round trips; no basis choice or quotient representative choice is used. -/
def admissibleTrivalentCoordinateBasis (a b c : Nat)
    (h : fusionOK a b c = true) : TrivalentCoordinateBasis a b c where
  synth := fun v => admissibleSynth a b c h (boundedCoeffForm v)
  coords := fun input s =>
    transvect a b (couplingOrder a b c) input s.val
  coords_synth := by
    intro v s
    have hr := admissibleSynth_rightInverse a b c h (boundedCoeffForm v)
      s.val s.isLt
    exact Q'.eqv_trans _ _ _ hr (boundedCoeffForm_apply v s)
  synth_coords := by
    intro input s hs
    have hr := admissibleSynth_rightInverse a b c h
      (boundedCoeffForm (c := c) (fun u : Fin (c + 1) =>
        transvect a b (couplingOrder a b c) input u.val)) s hs
    refine Q'.eqv_trans _ _ _ hr ?_
    unfold boundedCoeffForm
    rw [dif_pos hs]
    exact Q'.eqv_refl _

theorem admissibleTrivalent_coords_synth (a b c : Nat)
    (h : fusionOK a b c = true) (v : Fin (c + 1) → Q')
    (s : Fin (c + 1)) :
    ((admissibleTrivalentCoordinateBasis a b c h).coords
      ((admissibleTrivalentCoordinateBasis a b c h).synth v) s).eqv (v s) :=
  (admissibleTrivalentCoordinateBasis a b c h).coords_synth v s

theorem admissibleTrivalent_synth_coords (a b c : Nat)
    (h : fusionOK a b c = true) (input : BForm2) (s : Nat)
    (hs : s < c + 1) :
    (transvect a b (couplingOrder a b c)
      ((admissibleTrivalentCoordinateBasis a b c h).synth
        ((admissibleTrivalentCoordinateBasis a b c h).coords input)) s).eqv
      (transvect a b (couplingOrder a b c) input s) :=
  (admissibleTrivalentCoordinateBasis a b c h).synth_coords input s hs

end YMGap.Continuum.SU2TransvectantTrivalentCoordinateBasis

#print axioms YMGap.Continuum.SU2TransvectantTrivalentCoordinateBasis.boundedCoeffForm_apply
#print axioms YMGap.Continuum.SU2TransvectantTrivalentCoordinateBasis.admissibleTrivalentCoordinateBasis
#print axioms YMGap.Continuum.SU2TransvectantTrivalentCoordinateBasis.admissibleTrivalent_coords_synth
#print axioms YMGap.Continuum.SU2TransvectantTrivalentCoordinateBasis.admissibleTrivalent_synth_coords
