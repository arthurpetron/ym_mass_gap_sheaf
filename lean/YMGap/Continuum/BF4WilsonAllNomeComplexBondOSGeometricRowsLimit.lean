/-
# A geometric consecutive-error bound constructs original physical limit Rows

The squared triangle is iterated backwards from the first interval. A
quarter-rate consecutive bound gives a four-copy all-tail bound, with an
explicit computable Cauchy modulus. The input sequence already consists of
original physical Rows: no representatives of quotient classes are chosen.

This is completion machinery, not a proof that a particular Cayley product
has the required consecutive bound, and not a continuum or physical-time claim.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
import YMGap.Continuum.PositiveContractionResidual
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows CauchySequence ofRows distance distance_value value)
open YMGap.Continuum.BF4WilsonAllNomeDistance
  (completedDist completedDist_triangle completedDist_symm completedDist_zero_iff)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => distance hw0 hw1
local notation "V" => value hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

def quarter : Q' := Q'.mkPos 1 4 (by decide)

private theorem rat_le {a b : Q'} (h : a ≤ b) : RCle (rat a) (rat b) := by
  intro e he
  exact ⟨0,fun _ _ => Q'.le_trans' _ _ _ h
    (Q'.add_le_self_of_nonneg b e (Q'.le_of_lt he))⟩

private theorem rc_exchange (a b c d : RC) :
    RCadd (RCadd a b) (RCadd c d) = RCadd (RCadd a c) (RCadd b d) := by
  refine Quotient.inductionOn₂ a b ?_
  intro aa bb
  refine Quotient.inductionOn₂ c d ?_
  intro cc dd
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
      (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
      (by decide) (fun | 0 => aa.approx n | 1 => bb.approx n | 2 => cc.approx n | _ => dd.approx n)))

theorem distance_triangle (x y z : H) :
    RCle (D x z) (RCadd (RCadd (D x y) (D x y)) (RCadd (D y z) (D y z))) := by
  have h := RCadd_le_add
    (completedDist_triangle hw0 hw1 (V x).1 (V y).1 (V z).1)
    (completedDist_triangle hw0 hw1 (V x).2 (V y).2 (V z).2)
  let d11 := completedDist hw0 hw1 (V x).1 (V y).1
  let d12 := completedDist hw0 hw1 (V y).1 (V z).1
  let d21 := completedDist hw0 hw1 (V x).2 (V y).2
  let d22 := completedDist hw0 hw1 (V y).2 (V z).2
  change RCle (RCadd
      (completedDist hw0 hw1 (V x).1 (V z).1)
      (completedDist hw0 hw1 (V x).2 (V z).2))
    (RCadd (RCadd (RCadd d11 d11) (RCadd d12 d12))
      (RCadd (RCadd d21 d21) (RCadd d22 d22))) at h
  rw [rc_exchange (RCadd d11 d11) (RCadd d12 d12)
    (RCadd d21 d21) (RCadd d22 d22),
    rc_exchange d11 d11 d21 d21,rc_exchange d12 d12 d22 d22] at h
  simpa only [distance_value,d11,d12,d21,d22] using h

theorem distance_symm (x y : H) : D x y = D y x := by
  rw [distance_value,distance_value,completedDist_symm hw0 hw1 (V x).1 (V y).1,
    completedDist_symm hw0 hw1 (V x).2 (V y).2]

theorem distance_self (x : H) : D x x = RCzero := by
  rw [distance_value,(completedDist_zero_iff hw0 hw1 (V x).1 (V x).1).mpr rfl,
    (completedDist_zero_iff hw0 hw1 (V x).2 (V x).2).mpr rfl]
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => show Q'.eqv ((0 : Q')+0) 0 from by decide))

private theorem tail_step_coefficient (B : Q') (n : Nat) :
    Q'.eqv
      ((B*quarter^n+B*quarter^n)+
        (4*(B*quarter^(n+1))+4*(B*quarter^(n+1))))
      (4*(B*quarter^n)) := by
  rw [Q'.pow_succ]
  have h : Q'.eqv
      ((B*quarter^n+B*quarter^n)+
        (4*(B*(quarter*quarter^n))+4*(B*(quarter*quarter^n))))
      ((2+8*quarter)*(B*quarter^n)) :=
    poly_identity_of_normal_eq
      (.add
        (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.add (.mul (.const 4) (.mul (.var 0) (.mul (.var 2) (.var 1))))
          (.mul (.const 4) (.mul (.var 0) (.mul (.var 2) (.var 1))))))
      (.mul (.add (.const 2) (.mul (.const 8) (.var 2))) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => B | 1 => quarter^n | _ => quarter)
  exact Q'.eqv_trans _ _ _ h
    (Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv (2+8*quarter) 4))

private theorem budget_nonnegative (B : Q') (hB : (0 : Q') ≤ B) (n : Nat) :
    (0 : Q') ≤ 4*(B*quarter^n) := Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ hB (Q'.pow_nonneg quarter (by decide) n))

/-- Backwards squared-triangle induction controls EVERY later term from
the starting index; no finite sum or summability assumption is hidden. -/
theorem geometric_tail_bound (X : Nat → H) (B : Q') (hB : (0 : Q') ≤ B)
    (hstep : ∀ n, RCle (D (X n) (X (n+1))) (rat (B*quarter^n))) :
    ∀ k n, RCle (D (X n) (X (n+k))) (rat (4*(B*quarter^n))) := by
  intro k
  induction k with
  | zero =>
      intro n
      rw [Nat.add_zero,distance_self]
      exact rat_le (budget_nonnegative B hB n)
  | succ k ih =>
      intro n
      have htail := ih (n+1)
      rw [show (n+1)+k = n+(k+1) by omega] at htail
      have h := RCle_trans (distance_triangle hw0 hw1 (X n) (X (n+1)) (X (n+(k+1))))
        (RCadd_le_add (RCadd_le_add (hstep n) (hstep n))
          (RCadd_le_add htail htail))
      have hcoef : RCadd
          (RCadd (rat (B*quarter^n)) (rat (B*quarter^n)))
          (RCadd (rat (4*(B*quarter^(n+1)))) (rat (4*(B*quarter^(n+1))))) =
          rat (4*(B*quarter^n)) :=
        Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => tail_step_coefficient B n))
      rw [hcoef] at h
      exact h

private theorem tail_tolerance (B : Q') (hB : (0 : Q') ≤ B) (e : Q')
    (he : (0 : Q') < e) (n : Nat) (hn : geometricCutoff quarter (4*B) e ≤ n) :
    RCle (rat (4*(B*quarter^n))) (rat e) := by
  have h := geometric_bound (q := quarter) (C := 4*B)
    (by decide) (by decide) (Q'.mul_nonneg _ _ (by decide) hB) he n hn
  apply rat_le
  have hc : Q'.eqv (4*(B*quarter^n)) (quarter^n*(4*B)) :=
    poly_identity_of_normal_eq
      (.mul (.const 4) (.mul (.var 0) (.var 1)))
      (.mul (.var 1) (.mul (.const 4) (.var 0))) (by decide)
      (fun | 0 => B | _ => quarter^n)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hc) h

/-- Construct the existing physical Cauchy object with its explicit modulus.
The only estimate consumed is a consecutive bound on the supplied Rows. -/
def cauchyOfConsecutive (X : Nat → Rows hw0 hw1 (width := width))
    (B : Q') (hB : (0 : Q') ≤ B)
    (hstep : ∀ n, RCle (D (ofRows hw0 hw1 (X n)) (ofRows hw0 hw1 (X (n+1))))
      (rat (B*quarter^n))) : CauchySequence hw0 hw1 (width := width) where
  seq := X
  modulus := geometricCutoff quarter (4*B)
  bound := by
    intro e he m n hm hn
    rcases Nat.le_total m n with hmn | hnm
    · have htail := geometric_tail_bound hw0 hw1 (fun j => ofRows hw0 hw1 (X j))
        B hB hstep (n-m) m
      rw [Nat.add_sub_of_le hmn] at htail
      exact RCle_trans htail (tail_tolerance B hB e he m hm)
    · rw [distance_symm]
      have htail := geometric_tail_bound hw0 hw1 (fun j => ofRows hw0 hw1 (X j))
        B hB hstep (m-n) n
      rw [Nat.add_sub_of_le hnm] at htail
      exact RCle_trans htail (tail_tolerance B hB e he n hn)

#print axioms distance_triangle
#print axioms distance_symm
#print axioms distance_self
#print axioms geometric_tail_bound
#print axioms cauchyOfConsecutive

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
