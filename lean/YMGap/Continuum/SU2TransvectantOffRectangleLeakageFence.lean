/-
# Checked fence: raw total tensors leak outside the physical rectangle

`BForm2` is represented by a total function.  Consequently its raw
order-zero diagonal restriction can read coefficients outside a declared
bidegree rectangle.  The explicit `(m,n)=(1,1)` witness below prevents a
future coordinate package from treating `transvect` as congruent modulo only
`FormEqv2 2 2` without first projecting to physical support.
-/

import YMGap.Continuum.SU2TransvectantAllOrder

namespace YMGap.Continuum.SU2TransvectantOffRectangleLeakageFence

open YMGap.Constructive
open YMGap.Continuum.TransvectantCG

local infix:50 " ≈ " => Q'.eqv

/-- A single coefficient just above the second-factor degree-one window. -/
def offRectangleProbe : BForm2 := mono2 0 2

/-- The probe is indistinguishable from zero on the full physical
`(1+1) x (1+1)` rectangle. -/
theorem offRectangleProbe_rectangle_zero :
    FormEqv2 2 2 offRectangleProbe (fun _ _ => 0) := by
  decide

/-- Nevertheless raw order-zero diagonal restriction reads that coefficient
at output slot two. -/
theorem offRectangleProbe_transvect_two :
    transvect 1 1 0 offRectangleProbe 2 ≈ 1 := by
  decide

theorem zeroTensor_transvect_two :
    transvect 1 1 0 (fun _ _ => 0) 2 ≈ 0 := by
  decide

/-- **Off-rectangle leakage fence.**  Rectangle equality alone does not make
the raw transvectant coordinate well-defined. -/
theorem raw_transvect_not_congruent_mod_rectangle :
    ∃ x z : BForm2,
      FormEqv2 2 2 x z ∧
      ¬ (transvect 1 1 0 x 2 ≈ transvect 1 1 0 z 2) := by
  refine ⟨offRectangleProbe, (fun _ _ => 0),
    offRectangleProbe_rectangle_zero, ?_⟩
  intro h
  have hfalse : (1 : Q') ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm offRectangleProbe_transvect_two)
      (Q'.eqv_trans _ _ _ h zeroTensor_transvect_two)
  have hne : ¬ ((1 : Q') ≈ 0) := by decide
  exact hne hfalse

end YMGap.Continuum.SU2TransvectantOffRectangleLeakageFence

#print axioms YMGap.Continuum.SU2TransvectantOffRectangleLeakageFence.offRectangleProbe_rectangle_zero
#print axioms YMGap.Continuum.SU2TransvectantOffRectangleLeakageFence.offRectangleProbe_transvect_two
#print axioms YMGap.Continuum.SU2TransvectantOffRectangleLeakageFence.raw_transvect_not_congruent_mod_rectangle
