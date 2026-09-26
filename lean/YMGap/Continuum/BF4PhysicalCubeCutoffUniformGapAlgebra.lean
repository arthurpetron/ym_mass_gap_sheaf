/-
# Algebraic margin identity for a positive rational rate

For arbitrary positive rationals `p,q`, this module proves that the strict
margin of `p/q` is the quotient `(q-p)/q`.  The result is the scale-free
algebra needed when a later certificate identifies `q-p` with a fixed positive
constant and compares the denominator with a changing physical spacing.

No scale uniformity, physical-rate band, continuum limit, OS/GNS
identification, or Clay conclusion is asserted.
-/

import YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap

namespace YMGap.Continuum.BF4PhysicalCubeCutoffUniformGapAlgebra

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap

local infix:50 " ≈ " => Q'.eqv

/-! This is the scale-free algebraic identity used by later denominator
    certificates.  It is intentionally stated for arbitrary positive `p,q`;
    specializing it to a changing cutoff is kept outside this module so that
    elaboration does not unfold the dependent BF4 energy carrier. -/
theorem one_sub_divPos_eqv_inverse
    (p q : Q') (hq : (0 : Q') < q) :
    ((1 : Q') - Q'.divPos p q hq) ≈
      Q'.divPos (q - p) q hq := by
  refine Q'.eqv_symm ?_
  show ((q - p) * Q'.recipPos q hq) ≈
    ((1 : Q') - Q'.divPos p q hq)
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv q (-p) (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_recipPos_eqv q hq)
      (Q'.neg_mul_eqv p (Q'.recipPos q hq))) ?_
  exact Q'.eqv_refl _

#print axioms one_sub_divPos_eqv_inverse

end YMGap.Continuum.BF4PhysicalCubeCutoffUniformGapAlgebra
