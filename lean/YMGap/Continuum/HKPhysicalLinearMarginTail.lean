/-
M2r -- reduce the physical linear-margin seam through the existing
bare-to-physical comparison.

`PhysicalSeparator.HKPhysicalComparison` already states that the physical
margin is at most the bare heat-kernel margin plus a residual, and that the
residual is `O(a)`.  Consequently the only additional upper estimate needed
at this interface is an `O(a)` bound for the bare heat-kernel margin itself.

This file performs that composition constructively.  It does not construct an
`HKPhysicalComparison` or prove the bare heat-kernel bound; those are the
same-object RG and dimensional-transmutation inputs named below.
-/

import YMGap.Continuum.PhysicalSeparatorLinearTail

namespace YMGap.Continuum.HKPhysicalLinearMarginTail

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.PhysicalSeparatorLinearTail

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The remaining bare-margin upper input -/

/-- Eventual `O(a)` control of the bare heat-kernel margin appearing in an
existing bare-to-physical comparison. -/
structure BareHeatKernelLinearMarginTail
    {P : PhysicalSeparator} (A : PhysicalSpacing)
    (H : HKPhysicalComparison P A.spacing) : Type where
  start : Nat
  ceiling : Q'
  margin_le : forall j : Nat, start <= j ->
    heatKernelMargin (H.w j) <= ceiling * A.spacing j

/-- Constructive divergence witness for the bare heat-kernel rate: every
proposed eventual linear ceiling is exceeded at an explicitly returned later
scale. -/
structure BareHeatKernelRateEscapesLinearCeilings
    {P : PhysicalSeparator} (A : PhysicalSpacing)
    (H : HKPhysicalComparison P A.spacing) : Type where
  escape : forall start : Nat, forall ceiling : Q',
    Σ' j : Nat, start <= j ∧
      ceiling * A.spacing j < heatKernelMargin (H.w j)

namespace BareHeatKernelLinearMarginTail

variable {P : PhysicalSeparator} {A : PhysicalSpacing}
    {H : HKPhysicalComparison P A.spacing}

/-! ## 2. The residual coefficient is already present -/

/-- The coefficient of the residual's linear spacing bound. -/
def residualCoefficient
    (_B : BareHeatKernelLinearMarginTail A H) : Q' :=
  H.resC * H.Λ

/-- The residual field of `HKPhysicalComparison` is exactly an `O(a)` bound
after commuting the spacing and scale factors. -/
theorem residual_le
    (B : BareHeatKernelLinearMarginTail A H) (j : Nat) :
    H.δ j <= B.residualCoefficient * A.spacing j := by
  have hreorder :
      (H.resC * A.spacing j) * H.Λ ≈
        (H.resC * H.Λ) * A.spacing j := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv H.resC (A.spacing j) H.Λ) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left H.resC
        (A.spacing j * H.Λ) (H.Λ * A.spacing j)
        (Q'.mul_comm_eqv (A.spacing j) H.Λ)) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv H.resC H.Λ (A.spacing j))
  exact Q'.le_trans' _ _ _ (H.residual j) (Q'.le_of_eqv hreorder)

/-! ## 3. Bare plus residual gives the physical linear tail -/

/-- The combined physical-margin coefficient. -/
def physicalCoefficient
    (B : BareHeatKernelLinearMarginTail A H) : Q' :=
  B.ceiling + B.residualCoefficient

/-- An `O(a)` bare heat-kernel margin and the comparison's built-in `O(a)`
residual produce the exact `LinearMarginTail` consumed by the full-log
certificate. -/
def toLinearMarginTail
    (B : BareHeatKernelLinearMarginTail A H) : LinearMarginTail P A where
  start := B.start
  ceiling := B.physicalCoefficient
  margin_le := fun j hj => by
    have hsum :
        heatKernelMargin (H.w j) + H.δ j <=
          B.ceiling * A.spacing j +
            B.residualCoefficient * A.spacing j :=
      Q'.add_le_add (B.margin_le j hj) (B.residual_le j)
    have hfactor :
        B.ceiling * A.spacing j +
            B.residualCoefficient * A.spacing j ≈
          B.physicalCoefficient * A.spacing j := by
      unfold physicalCoefficient
      exact Q'.eqv_symm
        (Q'.add_mul_eqv B.ceiling B.residualCoefficient (A.spacing j))
    exact Q'.le_trans' _ _ _ (H.physMargin_le j)
      (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hfactor))

/-- Conversely, because `HKPhysicalComparison` is two-sided and its residual
is `O(a)`, an `O(a)` physical margin forces the bare heat-kernel margin to be
`O(a)` as well.  This theorem makes explicit that the comparison cannot turn a
divergent bare rate into a finite physical rate while retaining its present
residual scaling. -/
def ofPhysicalLinearMarginTail
    (H : HKPhysicalComparison P A.spacing)
    (L : LinearMarginTail P A) :
    BareHeatKernelLinearMarginTail A H where
  start := L.start
  ceiling := L.ceiling + H.resC * H.Λ
  margin_le := fun j hj => by
    have hreorder :
        (H.resC * A.spacing j) * H.Λ ≈
          (H.resC * H.Λ) * A.spacing j := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv H.resC (A.spacing j) H.Λ) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left H.resC
          (A.spacing j * H.Λ) (H.Λ * A.spacing j)
          (Q'.mul_comm_eqv (A.spacing j) H.Λ)) ?_
      exact Q'.eqv_symm
        (Q'.mul_assoc_eqv H.resC H.Λ (A.spacing j))
    have hresidual :
        H.δ j <= (H.resC * H.Λ) * A.spacing j :=
      Q'.le_trans' _ _ _ (H.residual j) (Q'.le_of_eqv hreorder)
    have hsum :
        P.physMargin j + H.δ j <=
          L.ceiling * A.spacing j +
            (H.resC * H.Λ) * A.spacing j :=
      Q'.add_le_add (L.margin_le j hj) hresidual
    have hfactor :
        L.ceiling * A.spacing j +
            (H.resC * H.Λ) * A.spacing j ≈
          (L.ceiling + H.resC * H.Λ) * A.spacing j :=
      Q'.eqv_symm
        (Q'.add_mul_eqv L.ceiling (H.resC * H.Λ) (A.spacing j))
    exact Q'.le_trans' _ _ _ (H.physMargin_ge j)
      (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hfactor))

/-- **No-go for the present additive comparison.**  If the bare rate escapes
every eventual linear ceiling, then the two-sided `O(a)` comparison is
incompatible with an `O(a)` physical margin. -/
theorem physicalLinearMargin_impossible_of_bare_escape
    (H : HKPhysicalComparison P A.spacing)
    (escape : BareHeatKernelRateEscapesLinearCeilings A H)
    (physical : LinearMarginTail P A) : False := by
  let bare : BareHeatKernelLinearMarginTail A H :=
    ofPhysicalLinearMarginTail H physical
  obtain ⟨j, hj, hstrict⟩ := escape.escape bare.start bare.ceiling
  have hle := bare.margin_le j hj
  exact Int.lt_irrefl _ (Q'.lt_of_le_of_lt hle hstrict)

@[simp] theorem toLinearMarginTail_start
    (B : BareHeatKernelLinearMarginTail A H) :
    B.toLinearMarginTail.start = B.start := rfl

@[simp] theorem toLinearMarginTail_ceiling
    (B : BareHeatKernelLinearMarginTail A H) :
    B.toLinearMarginTail.ceiling = B.physicalCoefficient := rfl

end BareHeatKernelLinearMarginTail

end YMGap.Continuum.HKPhysicalLinearMarginTail

#print axioms YMGap.Continuum.HKPhysicalLinearMarginTail.BareHeatKernelLinearMarginTail.residual_le
#print axioms YMGap.Continuum.HKPhysicalLinearMarginTail.BareHeatKernelLinearMarginTail.toLinearMarginTail
#print axioms YMGap.Continuum.HKPhysicalLinearMarginTail.BareHeatKernelLinearMarginTail.ofPhysicalLinearMarginTail
#print axioms YMGap.Continuum.HKPhysicalLinearMarginTail.BareHeatKernelLinearMarginTail.physicalLinearMargin_impossible_of_bare_escape
