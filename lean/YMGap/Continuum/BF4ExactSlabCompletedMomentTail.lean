/-
# Finite original-weighted moments control the completed sweep tail

Use the actual reverse-sweep adjoint on dense test vectors. Its polynomial
approximation has a finite monomial span. A completed input annihilating
that span pairs only against the uniformly small reverse approximation
error. Constructive dense norm duality gives the SAME tail bound without
choosing representatives, inverting a Gram matrix, or imposing exact zero
moments on an approximating sequence.

This is a fixed-volume conditional-dynamics statement. The finite moment
sector has no new strict bound; no conditional-patch, spatial/scaling,
OS-time, or physical Hamiltonian gap is asserted. The tail bound concerns
one sweep; invariance of its finite-moment annihilator is not asserted.
-/

import YMGap.Continuum.BF4ExactSlabFiniteMomentTail
import YMGap.Continuum.BF4ExactSlabFullActionScalar
import YMGap.Continuum.GNSProjectionSweepAdjoint
import YMGap.Continuum.GNSDenseDualNormBound
import YMGap.Continuum.QuaternionHaarCompletedMonomialSpan

namespace YMGap.Continuum.BF4ExactSlabCompletedMomentTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSFiniteSweepApproximation
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabPolynomialSweepDegree
open YMGap.Continuum.BF4ExactSlabPolynomialSweepApproximation
open YMGap.Continuum.BF4ExactSlabPolynomialSweepAdjoint
open YMGap.Continuum.BF4ExactSlabBlockConditionalApproximationError
open YMGap.Continuum.BF4ExactSlabFiniteMomentTail
open YMGap.Continuum.BF4ExactSlabFullActionScalar
open YMGap.Continuum.SU2QuaternionBlockDegreeBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK

/-- A finite family of exact completed pairings. This is a proposition, not
a claimed decision procedure for equality of arbitrary constructive reals. -/
def MomentZero (n : Nat) (x : GNSCompletionSpace F) : Prop :=
  ∀ m (hm : m ∈ dualMonomials w K extent n),
    (F).cinnerCompl x (embedV F
      ⟨[(m, 1)], dualMonomials_supported w K extent n m hm⟩) = RCzero

/-- Finite moment orthogonality extends by rational linearity to the whole
actual dual polynomial span; dependent monomials cause no problem. -/
theorem momentZero_dual_orthogonal (n : Nat) (x : GNSCompletionSpace F)
    (hx : MomentZero hw0 hw1 K extent hK n x) (q : (F).V)
    (hq : ∀ block, block < (boundaryCompleteSlabLinks extent).length →
      DegreeLE block (dualDegreeBudget w K extent n block) q.val) :
    (F).cinnerCompl x (embedV F q) = RCzero := by
  exact QuaternionHaarCompletedMonomialSpan.completedPair_zero_of_test_list
    _ _ _ x q.val q.property (dualMonomials w K extent n)
    (dualMonomials_supported w K extent n)
    (dualMonomials_cover hw0 hw1 K extent hK n q hq) hx

/-- The original reverse sweep obeys the SAME cutoff and error budget;
reversing the schedule changes neither its length nor the singleton errors. -/
theorem reverseSweep_approximation_error (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (n : Nat)
    (hn : sweepCutoff w extent epsilon ≤ n) (q : (F).V) :
    RCle (GNSTransferMetric.distanceSq F
      ((P).sweep (schedule extent).reverse (embedV F q))
      (embedV F (polynomialSweep hw0 hw1 K extent hK n
        (schedule extent).reverse q)))
      (RCscale epsilon (normSq (embedV F q))) := by
  let delta := stepTolerance epsilon (schedule extent).length
  have h := polynomialSweep_error hw0 hw1 K extent hK
    (schedule extent).reverse delta (stepTolerance_pos hepsilon _)
    (stepTolerance_le_one epsilon (Q'.le_of_lt hepsilon) _) n hn q
  rw [List.length_reverse] at h
  exact RCle_trans h (RCscale_scalar_mono
    (stepTolerance_coefficient_le epsilon (Q'.le_of_lt hepsilon) _)
    ((F).cinner_self_nonneg (embedV F q)))

private theorem sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (Q'.eqv_of_eq (Q'.add_zero' (A.approx n)))))

/-- Orthogonality to the actual bounded-degree dual space gives a tail bound
on EVERY completed input, with no moment-preserving density assumption. -/
theorem completed_tail_of_dual_orthogonal (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (x : GNSCompletionSpace F)
    (horth : ∀ q : (F).V,
      (∀ block, block < (boundaryCompleteSlabLinks extent).length →
        DegreeLE block (dualDegreeBudget w K extent
          (sweepCutoff w extent epsilon) block) q.val) →
      (F).cinnerCompl x (embedV F q) = RCzero) :
    RCle (normSq ((P).sweep (schedule extent) x))
      (RCscale epsilon (normSq x)) := by
  let n := sweepCutoff w extent epsilon
  let error (q : (F).V) := (F).cSub
    ((P).sweep (schedule extent).reverse (embedV F q))
    (embedV F (polynomialSweep hw0 hw1 K extent hK n
      (schedule extent).reverse q))
  apply GNSDenseDualNormBound.norm_le_of_dense_approximate_dual
    (fullScalarData hw0 hw1 K extent hK) x
    ((P).sweep (schedule extent) x) epsilon hepsilon error
  · intro q
    have hz := horth
      (polynomialSweep hw0 hw1 K extent hK n (schedule extent).reverse q)
      (fun block hb => reverseSweep_degree_bound hw0 hw1 K extent hK n block hb q)
    change (F).cinnerCompl ((P).sweep (schedule extent) x) (embedV F q) =
      (F).cinnerCompl x (error q)
    rw [(P).sweep_adjoint_reverse]
    change (F).cinnerCompl x ((P).sweep (schedule extent).reverse (embedV F q)) =
      (F).cinnerCompl x ((F).cSub _ _)
    rw [(F).cinnerCompl_comm x ((F).cSub _ _), (F).cinnerCompl_cSub_left,
      (F).cinnerCompl_comm _ x, (F).cinnerCompl_comm _ x, hz, sub_zero]
  · intro q
    exact reverseSweep_approximation_error hw0 hw1 K extent hK
      epsilon hepsilon n (Nat.le_refl n) q

/-- The SAME finite family of weighted moments controls the whole completed
tail, at the existing explicit epsilon-dependent inverse cutoff. The finite
core itself remains unbounded; this is not a vacuum-complement gap. -/
theorem completed_sweep_tail_bound (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (x : GNSCompletionSpace F)
    (hx : MomentZero hw0 hw1 K extent hK (sweepCutoff w extent epsilon) x) :
    RCle (normSq ((P).sweep (schedule extent) x))
      (RCscale epsilon (normSq x)) :=
  completed_tail_of_dual_orthogonal hw0 hw1 K extent hK epsilon hepsilon x
    (momentZero_dual_orthogonal hw0 hw1 K extent hK
      (sweepCutoff w extent epsilon) x hx)

/-- The earlier executable dense check implies the completed predicate.
No equality test on arbitrary completed vectors is asserted. -/
theorem momentZero_of_check (n : Nat) (p : (F).V)
    (hcheck : momentZeroCheck w K extent n p.val = true) :
    MomentZero hw0 hw1 K extent hK n (embedV F p) := by
  intro m hm
  let q : (F).V := ⟨[(m, 1)], dualMonomials_supported w K extent n m hm⟩
  have hz : Q'.eqv ((F).B p q) 0 :=
    of_decide_eq_true (List.all_eq_true.mp hcheck m hm)
  have he : (F).cinnerCompl (embedV F p) (embedV F q) =
      Quotient.mk crealSetoid (ofQ' ((F).B p q)) := (F).cinnerCompl_embed p q
  change (F).cinnerCompl (embedV F p) (embedV F q) = RCzero
  rw [he]
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => hz))

/-- Equal finite moment data control the difference of the ACTUAL completed
sweep outputs. No polynomial representative of either completed input is
chosen, and the finite data are not claimed to determine the input itself. -/
theorem completed_sweep_difference_of_moments (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (x y : GNSCompletionSpace F)
    (hmom : ∀ m (hm : m ∈ dualMonomials w K extent (sweepCutoff w extent epsilon)),
      let q : (F).V := ⟨[(m, 1)],
        dualMonomials_supported w K extent (sweepCutoff w extent epsilon) m hm⟩;
      (F).cinnerCompl x (embedV F q) = (F).cinnerCompl y (embedV F q)) :
    RCle (normSq ((F).cSub ((P).sweep (schedule extent) x)
      ((P).sweep (schedule extent) y)))
      (RCscale epsilon (normSq ((F).cSub x y))) := by
  have hz : MomentZero hw0 hw1 K extent hK (sweepCutoff w extent epsilon)
      ((F).cSub x y) := by
    intro m hm
    rw [(F).cinnerCompl_cSub_left, hmom m hm]
    generalize (F).cinnerCompl y _ = a
    exact Quotient.inductionOn a (fun A => Quotient.sound (CReal.sub_self_eqv_zero A))
  have h := completed_sweep_tail_bound hw0 hw1 K extent hK epsilon hepsilon
    ((F).cSub x y) hz
  rw [GNSFiniteSweepApproximation.Family.sweep_sub] at h
  exact h

#print axioms MomentZero
#print axioms momentZero_dual_orthogonal
#print axioms reverseSweep_approximation_error
#print axioms completed_tail_of_dual_orthogonal
#print axioms completed_sweep_tail_bound
#print axioms momentZero_of_check
#print axioms completed_sweep_difference_of_moments

end YMGap.Continuum.BF4ExactSlabCompletedMomentTail
