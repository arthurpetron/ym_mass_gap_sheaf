/-
M2s -- a bare-to-physical comparison that permits nonperturbative RG
renormalization of the bare heat-kernel margin.

The older `HKPhysicalComparison` makes the physical and bare margins
additively `O(a)`-close.  `HKPhysicalLinearMarginTail` proves that this forces
their finiteness behavior to agree.  That is too restrictive when the bare
rate diverges but the desired physical rate stays finite.

This replacement inserts an explicit scale-dependent renormalization factor
`Z_j` before comparing to the physical margin.  The factor is part of the
same-object RG input; no value or asymptotic law for it is assumed here.  A
linear bound on `Z_j (1-w_j^3)` plus the comparison's `O(a)` residual produces
the physical `LinearMarginTail` used by the exact-log certificate.
-/

import YMGap.Continuum.HKPhysicalLinearMarginTail

namespace YMGap.Continuum.RenormalizedHKPhysicalComparison

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.PhysicalSeparatorLinearTail

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The renormalized comparison -/

/-- One-sided upper comparison between the physical margin and a renormalized
bare heat-kernel margin, with a linearly small residual.  The independent BF4
same-object contraction supplies the lower physical rate. -/
structure RenormalizedHKComparison
    (P : PhysicalSeparator) (A : PhysicalSpacing) : Type where
  w : Nat -> Q'
  w_nonnegative : forall j : Nat, (0 : Q') <= w j
  w_lt_one : forall j : Nat, w j < (1 : Q')
  Z : Nat -> Q'
  Z_nonnegative : forall j : Nat, (0 : Q') <= Z j
  delta : Nat -> Q'
  delta_nonnegative : forall j : Nat, (0 : Q') <= delta j
  physical_margin_le : forall j : Nat,
    P.physMargin j <= Z j * heatKernelMargin (w j) + delta j
  Lambda : Q'
  residualCoefficient : Q'
  residual : forall j : Nat,
    delta j <= (residualCoefficient * A.spacing j) * Lambda

/-! ## 2. The renormalized bare upper input -/

/-- Eventual `O(a)` control after the nonperturbative RG factor has acted on
the bare heat-kernel margin. -/
structure RenormalizedBareLinearTail
    {P : PhysicalSeparator} {A : PhysicalSpacing}
    (H : RenormalizedHKComparison P A) : Type where
  start : Nat
  ceiling : Q'
  margin_le : forall j : Nat, start <= j ->
    H.Z j * heatKernelMargin (H.w j) <= ceiling * A.spacing j

namespace RenormalizedBareLinearTail

variable {P : PhysicalSeparator} {A : PhysicalSpacing}
    {H : RenormalizedHKComparison P A}

/-- The comparison residual in coefficient-times-spacing order. -/
theorem residual_le
    (_B : RenormalizedBareLinearTail H) (j : Nat) :
    H.delta j <= (H.residualCoefficient * H.Lambda) * A.spacing j := by
  have hreorder :
      (H.residualCoefficient * A.spacing j) * H.Lambda ≈
        (H.residualCoefficient * H.Lambda) * A.spacing j := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv H.residualCoefficient (A.spacing j) H.Lambda) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left H.residualCoefficient
        (A.spacing j * H.Lambda) (H.Lambda * A.spacing j)
        (Q'.mul_comm_eqv (A.spacing j) H.Lambda)) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv H.residualCoefficient H.Lambda (A.spacing j))
  exact Q'.le_trans' _ _ _ (H.residual j) (Q'.le_of_eqv hreorder)

/-- The total coefficient after adding the renormalized bare and residual
contributions. -/
def physicalCoefficient (B : RenormalizedBareLinearTail H) : Q' :=
  B.ceiling + H.residualCoefficient * H.Lambda

/-- The renormalized bare bound and the linearly small residual produce the
physical linear-margin tail without requiring the unrenormalized bare rate to
be finite. -/
def toPhysicalLinearMarginTail
    (B : RenormalizedBareLinearTail H) : LinearMarginTail P A where
  start := B.start
  ceiling := B.physicalCoefficient
  margin_le := fun j hj => by
    have hsum :
        H.Z j * heatKernelMargin (H.w j) + H.delta j <=
          B.ceiling * A.spacing j +
            (H.residualCoefficient * H.Lambda) * A.spacing j :=
      Q'.add_le_add (B.margin_le j hj) (B.residual_le j)
    have hfactor :
        B.ceiling * A.spacing j +
            (H.residualCoefficient * H.Lambda) * A.spacing j ≈
          B.physicalCoefficient * A.spacing j := by
      unfold physicalCoefficient
      exact Q'.eqv_symm
        (Q'.add_mul_eqv B.ceiling
          (H.residualCoefficient * H.Lambda) (A.spacing j))
    exact Q'.le_trans' _ _ _ (H.physical_margin_le j)
      (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hfactor))

@[simp] theorem toPhysicalLinearMarginTail_start
    (B : RenormalizedBareLinearTail H) :
    B.toPhysicalLinearMarginTail.start = B.start := rfl

@[simp] theorem toPhysicalLinearMarginTail_ceiling
    (B : RenormalizedBareLinearTail H) :
    B.toPhysicalLinearMarginTail.ceiling = B.physicalCoefficient := rfl

end RenormalizedBareLinearTail

end YMGap.Continuum.RenormalizedHKPhysicalComparison

#print axioms YMGap.Continuum.RenormalizedHKPhysicalComparison.RenormalizedBareLinearTail.residual_le
#print axioms YMGap.Continuum.RenormalizedHKPhysicalComparison.RenormalizedBareLinearTail.toPhysicalLinearMarginTail
