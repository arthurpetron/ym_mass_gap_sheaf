/-
# Two tests with their common unit component removed

The exact centered Gram inequality keeps the mixed response correction.
Replacing the second test norm by a supplied cap requires only positivity
of the first centered norm. No inverse of either test norm is taken.
The concrete consumer is the original terminal-source Young energy bound.
-/

import YMGap.Continuum.GNSUnitVacuumProjection
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.GNSUnitCenteredGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSUnitVacuumProjection
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

/-- Removing the unit component preserves a nonnegative squared norm. -/
theorem centered_nonnegative (D : GNSData) (o : D.V)
    (ho : D.B o o ≈ 1) (p : D.V) :
    (0 : Q') ≤ D.B p p - D.B p o * D.B p o :=
  Q'.le_trans' _ _ _ (D.self_nonneg (center D o p))
    (Q'.le_of_eqv (center_diag_eqv D o ho p))

/-- The sharp two-test Gram bound retains BOTH actual means. -/
theorem centered_cauchySchwarz (D : GNSData) (o : D.V)
    (ho : D.B o o ≈ 1) (p q : D.V) :
    (D.B p q - D.B p o * D.B q o) *
        (D.B p q - D.B p o * D.B q o) ≤
      (D.B p p - D.B p o * D.B p o) *
        (D.B q q - D.B q o * D.B q o) := by
  have hpq := center_pairing_eqv D o ho p q
  have hpp := center_diag_eqv D o ho p
  have hqq := center_diag_eqv D o ho q
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul hpq hpq))
    (Q'.le_trans' _ _ _ (D.cauchy_schwarz (center D o p) (center D o q))
      (Q'.le_of_eqv (qmul hpp hqq)))

/-- An upper cap on the uncentered test gives a nonnegative centered cap. -/
theorem centered_cap_nonnegative (D : GNSData) (o : D.V)
    (ho : D.B o o ≈ 1) (q : D.V) (U : Q') (hU : D.B q q ≤ U) :
    (0 : Q') ≤ U - D.B q o * D.B q o :=
  Q'.le_trans' _ _ _ (centered_nonnegative D o ho q)
    (Q'.add_le_add_right _ _ (-(D.B q o * D.B q o)) hU)

/-- Capping one test does not discard its computed mixed response. -/
theorem capped_centered_cauchySchwarz (D : GNSData) (o : D.V)
    (ho : D.B o o ≈ 1) (p q : D.V) (U : Q') (hU : D.B q q ≤ U) :
    (D.B p q - D.B p o * D.B q o) *
        (D.B p q - D.B p o * D.B q o) ≤
      (D.B p p - D.B p o * D.B p o) *
        (U - D.B q o * D.B q o) :=
  Q'.le_trans' _ _ _ (centered_cauchySchwarz D o ho p q)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.add_le_add_right _ _ (-(D.B q o * D.B q o)) hU)
      (centered_nonnegative D o ho p))

/-- Joint retained responses in an exact energy decomposition. This is a
cleared inequality, valid even when the centered test cap vanishes. -/
theorem joint_energy_budget (D : GNSData) (o : D.V)
    (ho : D.B o o ≈ 1) (p q : D.V) (U E C : Q')
    (hU : D.B q q ≤ U) (hE : 4*E+D.B p p ≈ 2*C) :
    let J := D.B p o
    let M := D.B q o
    let K := U-M*M
    let X := D.B p q-J*M
    4*K*E+K*(J*J)+X*X ≤ 2*K*C := by
  dsimp only
  let J := D.B p o
  let M := D.B q o
  let K := U-M*M
  let X := D.B p q-J*M
  have h := Q'.add_le_add_left (4*K*E+K*(J*J)) _ _
    (capped_centered_cauchySchwarz D o ho p q U hU)
  have halg : 4*K*E+K*(J*J)+(D.B p p-J*J)*K ≈
      K*(4*E+D.B p p) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.const 4) (.var 0)) (.var 1))
        (.mul (.var 0) (.mul (.var 2) (.var 2))))
        (.mul (.add (.var 3) (.neg (.mul (.var 2) (.var 2)))) (.var 0)))
      (.mul (.var 0) (.add (.mul (.const 4) (.var 1)) (.var 3)))
      (by decide) (fun | 0 => K | 1 => E | 2 => J | _ => D.B p p)
  have hright : K*(4*E+D.B p p) ≈ 2*K*C :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left K _ _ hE)
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.const 2) (.var 1)))
        (.mul (.mul (.const 2) (.var 0)) (.var 1))
        (by decide) (fun | 0 => K | _ => C))
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ halg hright))

#print axioms centered_nonnegative
#print axioms centered_cauchySchwarz
#print axioms centered_cap_nonnegative
#print axioms capped_centered_cauchySchwarz
#print axioms joint_energy_budget

end YMGap.Continuum.GNSUnitCenteredGram
