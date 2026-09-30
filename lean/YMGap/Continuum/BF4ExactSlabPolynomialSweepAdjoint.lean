/-
# The actual polynomial sweep has a bounded-degree reverse adjoint

The finite conditional inverse approximants are symmetric in the ORIGINAL
weighted form. Reversing their literal schedule gives the exact pairing
adjoint. Since that schedule also visits every original link, its output
degrees are bounded independently of the test input degree.

Consequently an input orthogonal to the stated bounded-degree test space
has a null polynomial sweep output. This is an exact weighted-radical
statement, not invertibility of a monomial Gram, a gap, or an OS-time claim.
-/

import YMGap.Continuum.BF4ExactSlabPolynomialConditionalAdjoint
import YMGap.Continuum.BF4ExactSlabPolynomialSweepApproximation

namespace YMGap.Continuum.BF4ExactSlabPolynomialSweepAdjoint

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabPhysicalScheduleIndex
open YMGap.Continuum.BF4ExactSlabPolynomialSweepDegree
open YMGap.Continuum.BF4ExactSlabPolynomialConditionalAdjoint
open YMGap.Continuum.SU2QuaternionBlockDegreeBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "S" => polynomialSweep hw0 hw1 K extent hK

private theorem singleton_valid (i : PhysicalLink extent) :
    ∀ j, j ∈ [i.val] → j ∈ boundaryCompleteSlabLinks extent := by
  intro j hj
  have he : j = i.val := List.mem_singleton.mp hj
  subst j
  exact i.property

theorem polynomialUpdate_symmetric (i : PhysicalLink extent) (n : Nat)
    (p q : (F).V) :
    (F).B (polynomialUpdate hw0 hw1 K extent hK i n p) q ≈
      (F).B p (polynomialUpdate hw0 hw1 K extent hK i n q) :=
  conditionalApproximation_symmetric hw0 hw1 K extent hK [i.val]
    (singleton_valid extent i) p q n

theorem polynomialSweep_append (n : Nat) (xs ys : List (PhysicalLink extent))
    (p : (F).V) : S n (xs ++ ys) p = S n ys (S n xs p) := by
  induction xs generalizing p with
  | nil => rfl
  | cons i rest ih => exact ih (polynomialUpdate hw0 hw1 K extent hK i n p)

/-- Exact weighted adjoint; no commutation between neighboring updates. -/
theorem polynomialSweep_adjoint_reverse (n : Nat) (xs : List (PhysicalLink extent))
    (p q : (F).V) : (F).B (S n xs p) q ≈ (F).B p (S n xs.reverse q) := by
  induction xs generalizing p with
  | nil => exact Q'.eqv_refl _
  | cons i rest ih =>
      change (F).B (S n rest (polynomialUpdate hw0 hw1 K extent hK i n p)) q ≈ _
      rw [List.reverse_cons, polynomialSweep_append]
      exact Q'.eqv_trans _ _ _ (ih _)
        (polynomialUpdate_symmetric hw0 hw1 K extent hK i n p (S n rest.reverse q))

/-- The ORIGINAL reverse schedule's degree budget, not a free feature cutoff. -/
def dualDegreeBudget (w : Q') (K extent n block : Nat) : Nat :=
  sweepDegreeBudget w K extent block n (schedule extent).reverse

theorem reverseSweep_degree_bound (n block : Nat)
    (hb : block < (boundaryCompleteSlabLinks extent).length) (q : (F).V) :
    DegreeLE block (dualDegreeBudget w K extent n block)
      (S n (schedule extent).reverse q).val := by
  apply polynomialSweep_selected_degree hw0 hw1 K extent hK
  rw [List.map_reverse, List.mem_reverse]
  exact physical_schedule_index_covers extent block (List.mem_range.mpr hb)

/-- Bounded-degree dual orthogonality kills the polynomial output in the
actual weighted radical, including sphere relations and other null vectors. -/
theorem polynomialSweep_null_of_dual_orthogonal (n : Nat) (p : (F).V)
    (horth : ∀ q : (F).V,
      (∀ block, block < (boundaryCompleteSlabLinks extent).length →
        DegreeLE block (dualDegreeBudget w K extent n block) q.val) →
      (F).B p q ≈ 0) :
    (F).rad (S n (schedule extent) p) (F).zero := by
  apply ((F).rad_zero_iff _).mpr
  exact Q'.eqv_trans _ _ _
    (polynomialSweep_adjoint_reverse hw0 hw1 K extent hK n (schedule extent)
      p (S n (schedule extent) p))
    (horth _ (fun block hb =>
      reverseSweep_degree_bound hw0 hw1 K extent hK n block hb _))

/-- The finite weighted moment data determine the output class: no chosen
representative, Gram inverse, or presumed basis independence is required. -/
theorem polynomialSweep_rad_of_dual_pairings (n : Nat) (p q : (F).V)
    (hmom : ∀ r : (F).V,
      (∀ block, block < (boundaryCompleteSlabLinks extent).length →
        DegreeLE block (dualDegreeBudget w K extent n block) r.val) →
      (F).B p r ≈ (F).B q r) :
    (F).rad (S n (schedule extent) p) (S n (schedule extent) q) := by
  let d := (F).sub (S n (schedule extent) p) (S n (schedule extent) q)
  have hpair : (F).B (S n (schedule extent) p) d ≈
      (F).B (S n (schedule extent) q) d :=
    Q'.eqv_trans _ _ _
      (polynomialSweep_adjoint_reverse hw0 hw1 K extent hK n (schedule extent) p d)
      (Q'.eqv_trans _ _ _
        (hmom _ (fun block hb =>
          reverseSweep_degree_bound hw0 hw1 K extent hK n block hb d))
        (Q'.eqv_symm
          (polynomialSweep_adjoint_reverse hw0 hw1 K extent hK n (schedule extent) q d)))
  change (F).B d d ≈ 0
  exact Q'.eqv_trans _ _ _ ((F).B_add_left _ _ d)
    (Q'.eqv_trans _ _ _
      (QPoly.q_add_congr hpair ((F).B_neg_left _ d))
      (OSReconstructionProgress.q_add_neg_self _))

end YMGap.Continuum.BF4ExactSlabPolynomialSweepAdjoint

#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepAdjoint.polynomialUpdate_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepAdjoint.polynomialSweep_append
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepAdjoint.polynomialSweep_adjoint_reverse
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepAdjoint.dualDegreeBudget
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepAdjoint.reverseSweep_degree_bound
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepAdjoint.polynomialSweep_null_of_dual_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepAdjoint.polynomialSweep_rad_of_dual_pairings
