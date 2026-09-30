/-
# A finite original-weighted moment check controls all omitted dense inputs

The dual feature list is computed from the ACTUAL reverse polynomial sweep's
degree budget. If all these weighted moments vanish, its forward polynomial
output is null in the original weighted quotient. The previously proved
all-input approximation error then bounds the TRUE conditional sweep.

This is a finite test of input moments, not a principal matrix truncation.
The original weight and sphere radical are retained. No useful bound on the
remaining finite moment sector, completed finite-rank extension, patch-to-
global theorem, physical OS time, or continuum gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPolynomialSweepAdjoint
import YMGap.Continuum.SU2QuaternionBoundedMonomials
import YMGap.Continuum.QuaternionHaarWeightedMonomialSpan

namespace YMGap.Continuum.BF4ExactSlabFiniteMomentTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabPolynomialSweepDegree
open YMGap.Continuum.BF4ExactSlabPolynomialSweepApproximation
open YMGap.Continuum.BF4ExactSlabPolynomialSweepAdjoint
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockDegreeBound
open YMGap.Continuum.SU2QuaternionBoundedMonomials
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarWeightedMonomialSpan
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- A returned FINITE list covering every reverse-sweep output monomial.
It can contain algebraically dependent or repeated physical functions. -/
def dualMonomials (w : Q') (K extent n : Nat) : List (List Nat) :=
  monomials (boundaryCompleteSlabLinks extent).length
    (dualDegreeBudget w K extent n)

/-- Executable exact test using the ORIGINAL full-action weighted moments.
No matrix inverse, floating point, or external solver is trusted. -/
def momentZeroCheck (w : Q') (K extent n : Nat) (p : RatPoly) : Bool :=
  (dualMonomials w K extent n).all (fun m => decide
    (weightedPair (boundaryCompleteSlabLinks extent).length
      (fullWeight w K extent) p [(m, 1)] ≈ 0))

/-- Every finite test is an actual supported original polynomial; no
out-of-carrier test vectors are silently admitted by the enumeration. -/
theorem dualMonomials_supported (w : Q') (K extent n : Nat) (m : List Nat)
    (hm : m ∈ dualMonomials w K extent n) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length [(m, 1)] := by
  intro t ht
  have he : t = (m, 1) := List.mem_singleton.mp ht
  subst t
  exact length_le_of_mem_monomials _ _ m hm

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK

theorem dualMonomials_cover (n : Nat) (q : (F).V)
    (hq : ∀ block, block < (boundaryCompleteSlabLinks extent).length →
      DegreeLE block (dualDegreeBudget w K extent n block) q.val) :
    ∀ t, t ∈ q.val → t.1 ∈ dualMonomials w K extent n := by
  intro t ht
  exact mem_monomials_of_degree
    (boundaryCompleteSlabLinks extent).length (dualDegreeBudget w K extent n)
    t.1 (q.property t ht) (fun block hb => hq block hb t ht)

/-- The Boolean check supplies every bounded-degree dual pairing, even
for test polynomials with arbitrarily many repeated or dependent terms. -/
theorem momentZeroCheck_dual_orthogonal (n : Nat) (p : (F).V)
    (hcheck : momentZeroCheck w K extent n p.val = true) (q : (F).V)
    (hq : ∀ block, block < (boundaryCompleteSlabLinks extent).length →
      DegreeLE block (dualDegreeBudget w K extent n block) q.val) :
    (F).B p q ≈ 0 := by
  apply weightedPair_zero_of_test_list _ _ p.val q.val
    (dualMonomials w K extent n)
    (dualMonomials_cover hw0 hw1 K extent hK n q hq)
  intro m hm
  exact of_decide_eq_true (List.all_eq_true.mp hcheck m hm)

/-- The finite check annihilates the polynomial approximation in the SAME
weighted radical, not as a false literal-zero polynomial identity. -/
theorem polynomialSweep_null_of_check (n : Nat) (p : (F).V)
    (hcheck : momentZeroCheck w K extent n p.val = true) :
    (F).rad (polynomialSweep hw0 hw1 K extent hK n (schedule extent) p) (F).zero :=
  polynomialSweep_null_of_dual_orthogonal hw0 hw1 K extent hK n p
    (momentZeroCheck_dual_orthogonal hw0 hw1 K extent hK n p hcheck)

private theorem cSub_zero (D : GNSData) (x : GNSCompletionSpace D) :
    D.cSub x (embedV D D.zero) = x := by
  apply GNSDenseCompletionLaws.eq_of_pairings_equal
  intro z
  rw [D.cinnerCompl_cSub_left, D.cinnerCompl_embedZero_left]
  generalize D.cinnerCompl x z = a
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (Q'.eqv_of_eq (Q'.add_zero' (A.approx n)))))

/-- Actual omitted-input control: all supported inputs passing the returned
finite original-weighted moment test have true sweep squared norm <=epsilon
times their input norm. There is no input-degree restriction. -/
theorem physicalSweep_tail_bound (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (p : (F).V)
    (hcheck : momentZeroCheck w K extent (sweepCutoff w extent epsilon) p.val = true) :
    RCle (normSq ((P).sweep (schedule extent) (embedV F p)))
      (RCscale epsilon (normSq (embedV F p))) := by
  have hrad := polynomialSweep_null_of_check hw0 hw1 K extent hK
    (sweepCutoff w extent epsilon) p hcheck
  have hembed : embedV F (approximation hw0 hw1 K extent hK epsilon p) =
      embedV F (F).zero := Quotient.sound (embed_null_of_rad F hrad)
  have h := approximation_error hw0 hw1 K extent hK epsilon hepsilon p
  rw [hembed] at h
  change RCle (normSq ((F).cSub
    ((P).sweep (schedule extent) (embedV F p)) (embedV F (F).zero))) _ at h
  rw [cSub_zero] at h
  exact h

end YMGap.Continuum.BF4ExactSlabFiniteMomentTail

#print axioms YMGap.Continuum.BF4ExactSlabFiniteMomentTail.dualMonomials
#print axioms YMGap.Continuum.BF4ExactSlabFiniteMomentTail.momentZeroCheck
#print axioms YMGap.Continuum.BF4ExactSlabFiniteMomentTail.dualMonomials_supported
#print axioms YMGap.Continuum.BF4ExactSlabFiniteMomentTail.dualMonomials_cover
#print axioms YMGap.Continuum.BF4ExactSlabFiniteMomentTail.momentZeroCheck_dual_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFiniteMomentTail.polynomialSweep_null_of_check
#print axioms YMGap.Continuum.BF4ExactSlabFiniteMomentTail.physicalSweep_tail_bound
