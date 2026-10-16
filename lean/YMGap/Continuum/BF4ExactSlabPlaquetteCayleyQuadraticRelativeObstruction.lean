/-
# Pointwise quadratic-relative Cayley obstruction

The directed commutator loop `x,y,-x,-y` has vanishing quadratic Cayley
coefficient but a strictly positive quartic deficit at every positive chart
scale.  Consequently no finite constant can dominate the exact pointwise
Cayley deficit by its quadratic term for all four directed chart vectors.

This rules out only that pointwise relative-linearization route.  It does not
rule out an averaged connected estimate, a comparison retaining the quartic
commutator term, or the required original-law denominator-relative bound.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCayleyPolynomial
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCayleyQuadraticRelativeObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem ac {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a+c ≈ b+d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h)
    (Q'.add_eqv_congr_left _ _ _ k)

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

/-- First coordinate axis used by the explicit commutator loop. -/
def commutatorXAxis : Triple := ⟨1, 0, 0⟩

/-- Second coordinate axis used by the explicit commutator loop. -/
def commutatorYAxis : Triple := ⟨0, 1, 0⟩

theorem commutator_H2 :
    H2 commutatorXAxis commutatorYAxis (neg3 commutatorXAxis)
      (neg3 commutatorYAxis) ≈ 0 := by
  decide

theorem commutator_H3 :
    H3 commutatorXAxis commutatorYAxis (neg3 commutatorXAxis)
      (neg3 commutatorYAxis) ≈ 0 := by
  decide

theorem commutator_H4 :
    H4 commutatorXAxis commutatorYAxis (neg3 commutatorXAxis)
      (neg3 commutatorYAxis) ≈ 64 := by
  decide

theorem commutator_H5 :
    H5 commutatorXAxis commutatorYAxis (neg3 commutatorXAxis)
      (neg3 commutatorYAxis) ≈ 0 := by
  decide

theorem commutator_H6 :
    H6 commutatorXAxis commutatorYAxis (neg3 commutatorXAxis)
      (neg3 commutatorYAxis) ≈ 0 := by
  decide

/-- The exact commutator-loop deficit is purely quartic. -/
theorem commutator_cayleyDeficit (e : Q') :
    cayleyDeficit e commutatorXAxis commutatorYAxis (neg3 commutatorXAxis)
      (neg3 commutatorYAxis) ≈ 64*((e*e)*(e*e)) := by
  have hcoeff :
      cayleyDeficit e commutatorXAxis commutatorYAxis (neg3 commutatorXAxis)
        (neg3 commutatorYAxis) ≈
        ((((e*e)*0+((e*e)*e)*0)+((e*e)*(e*e))*64)+
          (((e*e)*(e*e))*e)*0)+(((e*e)*(e*e))*(e*e))*0 := by
    unfold cayleyDeficit
    exact ac
      (ac
        (ac
          (ac (mc (Q'.eqv_refl _) commutator_H2)
            (mc (Q'.eqv_refl _) commutator_H3))
          (mc (Q'.eqv_refl _) commutator_H4))
        (mc (Q'.eqv_refl _) commutator_H5))
      (mc (Q'.eqv_refl _) commutator_H6)
  exact Q'.eqv_trans _ _ _ hcoeff
    (poly_identity_of_normal_eq
      (((((PolyExpr.var 0*PolyExpr.var 0)*0+
          ((PolyExpr.var 0*PolyExpr.var 0)*PolyExpr.var 0)*0)+
        ((PolyExpr.var 0*PolyExpr.var 0)*(PolyExpr.var 0*PolyExpr.var 0))*64)+
        (((PolyExpr.var 0*PolyExpr.var 0)*(PolyExpr.var 0*PolyExpr.var 0))*
          PolyExpr.var 0)*0)+
        (((PolyExpr.var 0*PolyExpr.var 0)*(PolyExpr.var 0*PolyExpr.var 0))*
          (PolyExpr.var 0*PolyExpr.var 0))*0)
      (64*((PolyExpr.var 0*PolyExpr.var 0)*
        (PolyExpr.var 0*PolyExpr.var 0)))
      (by decide) (fun _ => e))

/-- For positive chart scale, the commutator-loop deficit is strictly positive. -/
theorem commutator_cayleyDeficit_pos (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < cayleyDeficit e commutatorXAxis commutatorYAxis
      (neg3 commutatorXAxis) (neg3 commutatorYAxis) := by
  have he2 : (0 : Q') < e*e := Q'.mul_pos he he
  have he4 : (0 : Q') < (e*e)*(e*e) := Q'.mul_pos he2 he2
  have hquartic : (0 : Q') < 64*((e*e)*(e*e)) := Q'.mul_pos (by decide) he4
  exact Q'.pos_of_lt_of_le hquartic
    (Q'.ge_of_eqv (commutator_cayleyDeficit e))

/-- The exact normalized local deficit retains the same nonzero quartic
commutator contribution. -/
theorem commutator_normalizedCayleyDeficit (e : Q') :
    normalizedCayleyDeficit e commutatorXAxis commutatorYAxis
      (neg3 commutatorXAxis) (neg3 commutatorYAxis) ≈
      (64*((e*e)*(e*e))) *
        Q'.recipPos
          (cayleyDenominator e commutatorXAxis commutatorYAxis
            (neg3 commutatorXAxis) (neg3 commutatorYAxis))
          (cayleyDenominator_positive e commutatorXAxis commutatorYAxis
            (neg3 commutatorXAxis) (neg3 commutatorYAxis)) := by
  unfold normalizedCayleyDeficit
  exact mc (commutator_cayleyDeficit e) (Q'.eqv_refl _)

theorem commutator_normalizedCayleyDeficit_pos
    (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < normalizedCayleyDeficit e commutatorXAxis commutatorYAxis
      (neg3 commutatorXAxis) (neg3 commutatorYAxis) := by
  unfold normalizedCayleyDeficit
  exact Q'.mul_pos (commutator_cayleyDeficit_pos e he)
    (Q'.recipPos_pos _ (cayleyDenominator_positive e commutatorXAxis
      commutatorYAxis (neg3 commutatorXAxis) (neg3 commutatorYAxis)))

/-- No universal pointwise upper bound can compare the exact Cayley deficit to
only its quadratic term, even arbitrarily deep in the positive chart. -/
theorem no_universal_cayleyDeficit_quadratic_upper_bound
    (e : Q') (he : (0 : Q') < e) (C : Q') :
    ¬ ∀ a b c d : Triple,
      cayleyDeficit e a b c d ≤ C*((e*e)*H2 a b c d) := by
  intro hbound
  have hcomm := hbound commutatorXAxis commutatorYAxis
    (neg3 commutatorXAxis) (neg3 commutatorYAxis)
  have hright :
      C*((e*e)*H2 commutatorXAxis commutatorYAxis (neg3 commutatorXAxis)
        (neg3 commutatorYAxis)) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (mc (Q'.eqv_refl C)
        (mc (Q'.eqv_refl (e*e)) commutator_H2))
      (poly_identity_of_normal_eq
        ((PolyExpr.var 0)*(((PolyExpr.var 1*PolyExpr.var 1))*0))
        0 (by decide) (fun | 0 => C | _ => e))
  have hzero :
      cayleyDeficit e commutatorXAxis commutatorYAxis (neg3 commutatorXAxis)
        (neg3 commutatorYAxis) ≤ 0 :=
    Q'.le_trans' _ _ _ hcomm (Q'.le_of_eqv hright)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (commutator_cayleyDeficit_pos e he) hzero)

/-- Dividing by the exact positive local Cayley denominator does not repair
the failed universal pointwise comparison with the vanishing quadratic term. -/
theorem no_universal_normalizedCayleyDeficit_quadratic_upper_bound
    (e : Q') (he : (0 : Q') < e) (C : Q') :
    ¬ ∀ a b c d : Triple,
      normalizedCayleyDeficit e a b c d ≤ C*((e*e)*H2 a b c d) := by
  intro hbound
  have hcomm := hbound commutatorXAxis commutatorYAxis
    (neg3 commutatorXAxis) (neg3 commutatorYAxis)
  have hright :
      C*((e*e)*H2 commutatorXAxis commutatorYAxis (neg3 commutatorXAxis)
        (neg3 commutatorYAxis)) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (mc (Q'.eqv_refl C)
        (mc (Q'.eqv_refl (e*e)) commutator_H2))
      (poly_identity_of_normal_eq
        ((PolyExpr.var 0)*(((PolyExpr.var 1*PolyExpr.var 1))*0))
        0 (by decide) (fun | 0 => C | _ => e))
  have hzero :
      normalizedCayleyDeficit e commutatorXAxis commutatorYAxis
        (neg3 commutatorXAxis) (neg3 commutatorYAxis) ≤ 0 :=
    Q'.le_trans' _ _ _ hcomm (Q'.le_of_eqv hright)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (commutator_normalizedCayleyDeficit_pos e he) hzero)

end YMGap.Continuum.BF4ExactSlabPlaquetteCayleyQuadraticRelativeObstruction

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyQuadraticRelativeObstruction.commutator_cayleyDeficit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyQuadraticRelativeObstruction.no_universal_cayleyDeficit_quadratic_upper_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyQuadraticRelativeObstruction.commutator_normalizedCayleyDeficit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCayleyQuadraticRelativeObstruction.no_universal_normalizedCayleyDeficit_quadratic_upper_bound
