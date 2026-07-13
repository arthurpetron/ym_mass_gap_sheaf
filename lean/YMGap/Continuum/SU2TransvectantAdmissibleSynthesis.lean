/-
# A choice-free synthesis section for every admissible transvectant

The coordinate pivots are assembled by primitive recursion into one explicit
two-form input for an arbitrary finite output form.  This produces a literal
right inverse on the full degree-`c` coefficient window, without choice.
-/

import YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity

namespace YMGap.Continuum.SU2TransvectantAdmissibleSynthesis

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantAdmissibleSurjectivity
open YMGap.Continuum.BondMovingStep

def zeroForm2 : BForm2 := fun _ _ => 0

def truncateForm (f : BForm) (N : Nat) : BForm :=
  fun s => if s < N then f s else 0

theorem truncateForm_succ (f : BForm) (N t : Nat) :
    (truncateForm f N t + f N * mono N t).eqv
      (truncateForm f (N + 1) t) := by
  by_cases ht : t < N
  · have hne : ¬ t = N := by omega
    unfold truncateForm mono
    rw [if_pos ht, if_pos (by omega : t < N + 1), if_neg hne]
    refine Q'.eqv_trans _ (f t + 0) _
      (Q'.add_eqv_congr_left (f t) _ 0 (Q'.mul_zero_eqv (f N))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' _)
  · by_cases heq : t = N
    · subst t
      unfold truncateForm mono
      rw [if_neg (Nat.lt_irrefl N), if_pos (Nat.lt_succ_self N), if_pos rfl]
      refine Q'.eqv_trans _ (0 + f N) _
        (Q'.add_eqv_congr_left 0 _ _ (Q'.mul_one_eqv (f N))) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' _)
    · have hsucc : ¬ t < N + 1 := by omega
      unfold truncateForm mono
      rw [if_neg ht, if_neg hsucc, if_neg heq]
      refine Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr_left 0 _ 0 (Q'.mul_zero_eqv (f N))) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' 0)

theorem transvect_zeroForm2 (m n k : Nat) :
    BFormEqv (transvect m n k zeroForm2) zeroF := by
  let carrier := tprod (mono 0) (mono 0)
  have hcarrier : BForm2Eqv zeroForm2 (bscale 0 carrier) := by
    intro i j
    exact Q'.eqv_symm (Q'.zero_mul_eqv (carrier i j))
  have hcongr := transvect_congr m n k hcarrier
  have hscale := transvect_scale m n k 0 carrier
  intro s
  refine Q'.eqv_trans _ _ _ (hcongr s) ?_
  refine Q'.eqv_trans _ _ _ (hscale s) ?_
  exact Q'.zero_mul_eqv _

/-- Explicit finite sum of the coordinate preimages.  The guard makes the
definition total; it is always true on the prefix used below. -/
def synthPrefix (a b c : Nat) (h : fusionOK a b c = true)
    (f : BForm) : Nat → BForm2
  | 0 => zeroForm2
  | N + 1 =>
      if hN : N < c + 1 then
        badd (synthPrefix a b c h f N)
          (bscale (f N) (admissibleCoordinateInput a b c h ⟨N, hN⟩))
      else
        synthPrefix a b c h f N

theorem synthPrefix_maps (a b c : Nat) (h : fusionOK a b c = true)
    (f : BForm) : ∀ N, N ≤ c + 1 →
    BFormEqv
      (transvect a b (couplingOrder a b c) (synthPrefix a b c h f N))
      (truncateForm f N) := by
  intro N
  induction N with
  | zero =>
      intro _ s
      have hz := transvect_zeroForm2 a b (couplingOrder a b c) s
      refine Q'.eqv_trans _ 0 _ hz ?_
      exact Q'.eqv_refl 0
  | succ N ih =>
      intro hN
      have hlt : N < c + 1 := by omega
      have hbase := ih (by omega)
      have hpivot := admissibleCoordinateInput_maps a b c h ⟨N, hlt⟩
      intro s
      have hadd := transvect_add a b (couplingOrder a b c)
        (synthPrefix a b c h f N)
        (bscale (f N) (admissibleCoordinateInput a b c h ⟨N, hlt⟩)) s
      have hscale := transvect_scale a b (couplingOrder a b c) (f N)
        (admissibleCoordinateInput a b c h ⟨N, hlt⟩) s
      have hscaled :
          (transvect a b (couplingOrder a b c)
            (bscale (f N) (admissibleCoordinateInput a b c h ⟨N, hlt⟩)) s).eqv
            (f N * mono N s) :=
        Q'.eqv_trans _ _ _ hscale
          (Q'.mul_eqv_congr_left (f N) _ _ (hpivot s))
      change (transvect a b (couplingOrder a b c)
        (if hN' : N < c + 1 then
          badd (synthPrefix a b c h f N)
            (bscale (f N) (admissibleCoordinateInput a b c h ⟨N, hN'⟩))
        else synthPrefix a b c h f N) s).eqv _
      rw [dif_pos hlt]
      refine Q'.eqv_trans _ _ _ hadd ?_
      refine Q'.eqv_trans _
        (truncateForm f N s + f N * mono N s) _
        (Q'.add_eqv_congr' (hbase s) hscaled) ?_
      exact truncateForm_succ f N s

/-- The explicit section for the complete degree-`c` output window. -/
def admissibleSynth (a b c : Nat) (h : fusionOK a b c = true)
    (f : BForm) : BForm2 :=
  synthPrefix a b c h f (c + 1)

/-- **Choice-free right inverse.**  Transvecting the synthesized input recovers
every coefficient of the requested degree-`c` form. -/
theorem admissibleSynth_rightInverse (a b c : Nat)
    (h : fusionOK a b c = true) (f : BForm) :
    FormEqv (c + 1)
      (transvect a b (couplingOrder a b c) (admissibleSynth a b c h f)) f := by
  have hall := synthPrefix_maps a b c h f (c + 1) (Nat.le_refl _)
  intro s hs
  refine Q'.eqv_trans _ _ _ (hall s) ?_
  unfold truncateForm
  rw [if_pos hs]
  exact Q'.eqv_refl _

end YMGap.Continuum.SU2TransvectantAdmissibleSynthesis

#print axioms YMGap.Continuum.SU2TransvectantAdmissibleSynthesis.truncateForm_succ
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleSynthesis.transvect_zeroForm2
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleSynthesis.synthPrefix_maps
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleSynthesis.admissibleSynth_rightInverse
