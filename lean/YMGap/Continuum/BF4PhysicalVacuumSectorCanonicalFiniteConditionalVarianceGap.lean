/-
# The canonical finite Poincare rate is a conditional-variance fraction

Every fixed physical BF4 vacuum sector already has an explicit strict rate
from finite positive-edge paths.  The law of total variance shows that its
complement is exactly a lower conditional-variance fraction.  This module
makes that statement constructive by returning the previously defined
`CentralPhysicalFiniteConditionalVarianceGapData` at every finite coupling,
cutoff, and half-volume.

The resulting fraction is positive at each fixed finite sector but contains
the finite edge floor and path scale.  No cutoff-, volume-, coupling-, beta-,
or lattice-spacing-uniform lower bound is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
`noncomputable`, or enlarged heartbeat budget is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
import YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVarianceGapBridge
import YMGap.Continuum.HeatKernelPos

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFiniteConditionalVarianceGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVarianceGapBridge
open YMGap.Continuum.HKPos

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The explicit complementary fraction -/

/-- The fraction of stationary variance left after conditioning is the
complement of the canonical finite-sector Poincare rate. -/
def centralPhysicalFiniteCanonicalConditionalVarianceFraction
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  (1 : Q') +
    (-centralPhysicalFiniteVacuumSectorPoincareRate
      w hw cutoff half)

theorem centralPhysicalFiniteCanonicalConditionalVarianceFraction_pos
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') <
      centralPhysicalFiniteCanonicalConditionalVarianceFraction
        w hw cutoff half := by
  unfold centralPhysicalFiniteCanonicalConditionalVarianceFraction
  exact one_sub_pos
    (centralPhysicalFiniteVacuumSectorPoincareRate_lt_one
      w hw cutoff half)

theorem centralPhysicalFiniteCanonicalConditionalVarianceFraction_le_one
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteCanonicalConditionalVarianceFraction
        w hw cutoff half ≤ (1 : Q') := by
  have hnonpositive :
      -centralPhysicalFiniteVacuumSectorPoincareRate
          w hw cutoff half ≤ (0 : Q') :=
    Q'.nonpos_neg_of_nonneg
      (centralPhysicalFiniteVacuumSectorPoincareRate_nonnegative
        w hw cutoff half)
  unfold centralPhysicalFiniteCanonicalConditionalVarianceFraction
  exact Q'.le_trans' _ ((1 : Q') + 0) _
    (Q'.add_le_add_left 1 _ _ hnonpositive)
    (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1)))

private theorem one_sub_one_sub_eqv_local (rate : Q') :
    (1 : Q') + (-((1 : Q') + (-rate))) ≈ rate := by
  have hneg :
      (-((1 : Q') + (-rate))) ≈ (-(1 : Q')) + rate := by
    refine Q'.eqv_trans _ ((-(1 : Q')) + (-(-rate))) _
      (Q'.neg_add_eqv 1 (-rate)) ?_
    exact Q'.add_eqv_congr_left (-(1 : Q')) _ _
      (Q'.neg_neg_eqv rate)
  refine Q'.eqv_trans _ ((1 : Q') + ((-(1 : Q')) + rate)) _
    (Q'.add_eqv_congr_left 1 _ _ hneg) ?_
  refine Q'.eqv_trans _ (((1 : Q') + (-(1 : Q'))) + rate) _
    (Q'.eqv_symm (Q'.add_assoc_eqv 1 (-1) rate)) ?_
  refine Q'.eqv_trans _ ((0 : Q') + rate) _
    (Q'.add_eqv_congr_right _ _ rate
      (Q'.add_neg_self_eqv 1)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' rate)

/-- Subtracting the complementary fraction from one recovers the exact
canonical finite Poincare rate. -/
theorem one_sub_centralPhysicalFiniteCanonicalConditionalVarianceFraction_eqv_rate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (1 : Q') +
        (-centralPhysicalFiniteCanonicalConditionalVarianceFraction
          w hw cutoff half) ≈
      centralPhysicalFiniteVacuumSectorPoincareRate
        w hw cutoff half := by
  unfold centralPhysicalFiniteCanonicalConditionalVarianceFraction
  exact one_sub_one_sub_eqv_local
    (centralPhysicalFiniteVacuumSectorPoincareRate
      w hw cutoff half)

/-! ## 2. Canonical finite conditional-variance data -/

/-- Every fixed finite physical BF4 vacuum sector has a witnessed positive
conditional-variance fraction.  Its possible degeneration with cutoff and
volume remains explicit in the returned rational. -/
def centralPhysicalFiniteCanonicalConditionalVarianceGapData
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    CentralPhysicalFiniteConditionalVarianceGapData
      w hw cutoff half where
  fraction := centralPhysicalFiniteCanonicalConditionalVarianceFraction
    w hw cutoff half
  fraction_pos :=
    centralPhysicalFiniteCanonicalConditionalVarianceFraction_pos
      w hw cutoff half
  fraction_le_one :=
    centralPhysicalFiniteCanonicalConditionalVarianceFraction_le_one
      w hw cutoff half
  conditionalVarianceMargin := by
    intro coefficient hcenter
    apply
      (centralPhysicalFiniteVacuumSector_formBound_iff_halfConditionalVarianceMargin
        w hw cutoff half coefficient
        (centralPhysicalFiniteCanonicalConditionalVarianceFraction
          w hw cutoff half)).mp
    have hpoincare :=
      centralPhysicalFiniteVacuumSector_matrix_le_poincareRate_mul_diagonal
        w hw cutoff half coefficient hcenter
    refine Q'.le_trans' _ _ _ hpoincare ?_
    exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_right
        (centralPhysicalFiniteVacuumSectorPoincareRate
          w hw cutoff half)
        ((1 : Q') +
          (-centralPhysicalFiniteCanonicalConditionalVarianceFraction
            w hw cutoff half))
        (centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw cutoff half coefficient)
        (Q'.eqv_symm
          (one_sub_centralPhysicalFiniteCanonicalConditionalVarianceFraction_eqv_rate
            w hw cutoff half)))

end YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFiniteConditionalVarianceGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFiniteConditionalVarianceGap.centralPhysicalFiniteCanonicalConditionalVarianceFraction_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFiniteConditionalVarianceGap.centralPhysicalFiniteCanonicalConditionalVarianceFraction_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFiniteConditionalVarianceGap.one_sub_centralPhysicalFiniteCanonicalConditionalVarianceFraction_eqv_rate
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFiniteConditionalVarianceGap.centralPhysicalFiniteCanonicalConditionalVarianceGapData
