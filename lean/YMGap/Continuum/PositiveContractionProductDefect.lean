/-
# A dimension-independent product-defect potential

For a positive symmetric contraction P, positivity of I-P at 2x-y gives
Phi_x(Py) <= Phi_x(y) + 4 <x,(I-P)x>, where
Phi_x(y) = <y,y> - 4<x,y> + 3<x,x>.
Also 2(<x,x>-<x,y>) <= Phi_x(y). Thus a sequence of such steps has
defect at most twice the sum of its fixed-reference local defects.
No commutation, inverse, square root or spectral theorem is required.

The moving-reference telescope below also allows simultaneous isometric
coordinate motion. The concrete consumer is the original cyclic heat
composition. The factor is TWO; this does not assert the sharper factor-one
product inequality or control the signed interacting endpoint correction.
-/

import YMGap.Continuum.PositiveContractionResidual
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.PositiveContractionProductDefect

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PositiveContractionOneStepForm
open YMGap.Continuum.PositiveContractionResidual
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- The potential retains the actual mixed pairing, not an absolute value. -/
def potential (D : GNSData) (x y : D.V) : Q' :=
  D.B y y + -(4 * D.B x y) + 3 * D.B x x

theorem potential_self (D : GNSData) (x : D.V) : potential D x x ≈ 0 :=
  poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.mul (.const 4) (.var 0))))
      (.mul (.const 3) (.var 0))) (.const 0) (by decide) (fun _ => D.B x x)

/-- The nonnegative squared distance is the exact slack in this bound. -/
theorem twice_defect_le_potential (D : GNSData) (x y : D.V) :
    2 * (D.B x x + -(D.B x y)) ≤ potential D x y := by
  have h := D.toPreInnerForm.nonnegQuad 1 (-1) x y
  apply Q'.le_of_sub_nonneg
  refine Q'.le_trans' _ _ _ h (Q'.le_of_eqv ?_)
  exact poly_identity_of_normal_eq
    (.add (.add (.mul (.mul (.const 1) (.const 1)) (.var 0))
      (.mul (.mul (.const 2) (.mul (.const 1) (.neg (.const 1)))) (.var 1)))
      (.mul (.mul (.neg (.const 1)) (.neg (.const 1))) (.var 2)))
    (.add (.add (.add (.var 2) (.neg (.mul (.const 4) (.var 1))))
      (.mul (.const 3) (.var 0)))
      (.neg (.mul (.const 2) (.add (.var 0) (.neg (.var 1))))))
    (by decide) (fun | 0 => D.B x x | 1 => D.B x y | _ => D.B y y)

/-- One actual positive contraction increases the potential by at most four
times its local defect on the unchanged reference x. -/
theorem potential_step (D : GNSData) (P : D.V → D.V)
    (hsa : ∀ a b, D.B a (P b) ≈ D.B (P a) b)
    (hpos : ∀ a, (0 : Q') ≤ D.B a (P a))
    (hupper : ∀ a, D.B a (P a) ≤ D.B a a) (x y : D.V) :
    potential D x (P y) ≤ potential D x y + 4 * (D.B x x + -(D.B x (P x))) := by
  let E := oneStepGNSData D (residual D P)
    (residual_symmetric D P hsa) (residual_nonnegative D P hupper)
  have hq := E.toPreInnerForm.nonnegQuad 2 (-1) x y
  have hp : (2 * 2 * E.B x x + 2 * (2 * -1) * E.B x y + -1 * -1 * E.B y y) ≈
      2 * 2 * (D.B x x + -(D.B x (P x))) +
        2 * (2 * -1) * (D.B x y + -(D.B x (P y))) +
        -1 * -1 * (D.B y y + -(D.B y (P y))) :=
    Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ (residual_pairing D P x x))
        (Q'.mul_eqv_congr_left _ _ _ (residual_pairing D P x y)))
      (Q'.mul_eqv_congr_left _ _ _ (residual_pairing D P y y))
  have hn := square_form_bound D P hsa hpos Q'.zero_le_one
    (fun a => Q'.le_trans' _ _ _ (hupper a) (Q'.ge_of_eqv (Q'.one_mul_eqv _))) y
  have hn' : D.B (P y) (P y) ≤ D.B y (P y) :=
    Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have hs := Q'.zero_le_add _ _
    (Q'.le_trans' _ _ _ hq (Q'.le_of_eqv hp)) (Q'.sub_nonneg_of_le hn')
  apply Q'.le_of_sub_nonneg
  refine Q'.le_trans' _ _ _ hs (Q'.le_of_eqv ?_)
  exact poly_identity_of_normal_eq
    (.add
      (.add (.add (.mul (.mul (.const 2) (.const 2)) (.add (.var 0) (.neg (.var 1))))
        (.mul (.mul (.const 2) (.mul (.const 2) (.neg (.const 1))))
          (.add (.var 2) (.neg (.var 3)))))
        (.mul (.mul (.neg (.const 1)) (.neg (.const 1))) (.add (.var 4) (.neg (.var 5)))))
      (.add (.var 5) (.neg (.var 6))))
    (.add
      (.add (.add (.add (.var 4) (.neg (.mul (.const 4) (.var 2)))) (.mul (.const 3) (.var 0)))
        (.mul (.const 4) (.add (.var 0) (.neg (.var 1)))))
      (.neg (.add (.add (.var 6) (.neg (.mul (.const 4) (.var 3)))) (.mul (.const 3) (.var 0)))))
    (by decide) (fun
      | 0 => D.B x x | 1 => D.B x (P x) | 2 => D.B x y
      | 3 => D.B x (P y) | 4 => D.B y y | 5 => D.B y (P y)
      | _ => D.B (P y) (P y))

/-- Telescope on the actual two paths. A moving reference is allowed; its
isometry and local estimates must be proved by the concrete consumer. -/
theorem path_potential_bound (D : GNSData) (x y : Nat → D.V) (e : Nat → Q')
    (hzero : potential D (x 0) (y 0) ≈ 0)
    (hstep : ∀ i, potential D (x (i+1)) (y (i+1)) ≤
      potential D (x i) (y i) + 4 * e i) (n : Nat) :
    potential D (x n) (y n) ≤ 4 * finSum e n := by
  induction n with
  | zero =>
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hzero)
        (Q'.ge_of_eqv (Q'.mul_zero_eqv 4))
  | succ n ih =>
      exact Q'.le_trans' _ _ _ (hstep n)
        (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ ih)
          (Q'.ge_of_eqv (Q'.mul_add_eqv 4 (finSum e n) (e n))))

/-- Uniform factor two, independent of path length; there is no assumption
that different steps commute. -/
theorem path_defect_bound (D : GNSData) (x y : Nat → D.V) (e : Nat → Q')
    (hzero : potential D (x 0) (y 0) ≈ 0)
    (hstep : ∀ i, potential D (x (i+1)) (y (i+1)) ≤
      potential D (x i) (y i) + 4 * e i) (n : Nat) :
    D.B (x n) (x n) + -(D.B (x n) (y n)) ≤ 2 * finSum e n := by
  have h := Q'.le_trans' _ _ _ (twice_defect_le_potential D (x n) (y n))
    (path_potential_bound D x y e hzero hstep n)
  apply q_cancel_left (by decide : (0 : Q') < 2)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
    (poly_identity_of_normal_eq (.mul (.const 4) (.var 0))
      (.mul (.const 2) (.mul (.const 2) (.var 0))) (by decide) (fun _ => finSum e n)))

end YMGap.Continuum.PositiveContractionProductDefect

#print axioms YMGap.Continuum.PositiveContractionProductDefect.potential_self
#print axioms YMGap.Continuum.PositiveContractionProductDefect.twice_defect_le_potential
#print axioms YMGap.Continuum.PositiveContractionProductDefect.potential_step
#print axioms YMGap.Continuum.PositiveContractionProductDefect.path_potential_bound
#print axioms YMGap.Continuum.PositiveContractionProductDefect.path_defect_bound
