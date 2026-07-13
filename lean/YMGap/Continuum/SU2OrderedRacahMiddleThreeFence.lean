/-
# The all-positive middle-label-three support fence

The natural symmetric successor to the middle-label-two near-stretched
family has labels

  `(n,3,n; 2n-1; n+1,n+1)`

and inner/outer contraction orders `(1,1)` in both bracketings.  It is
admissible and all labels and contractions are positive, but its Racah
support is still only the two adjacent indices `2n,2n+1`.

The arithmetic fence below explains why this is not an accident.  In the
near-stretched range, the support radius for middle label three is bounded
by `min(min k p) (3-max k p)`.  Radius at least two would force both
`k,p >= 2` and `max k p <= 1`, a contradiction.  Thus an all-positive
middle-label-three family cannot be the first three-summand family.
-/

import YMGap.Continuum.SU2OrderedRacahNearStretchedTwoTerm

namespace YMGap.Continuum.SU2OrderedRacahMiddleThreeFence

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SixJKernel
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2DirectRightFixedOutputSections

def middleThreeN (u : Nat) : Nat := u + 4
def middleThreeD (u : Nat) : Nat := 2 * u + 7
def middleThreeT0 (u : Nat) : Nat := 2 * u + 8
def middleThreeT1 (u : Nat) : Nat := 2 * u + 9

/-- The natural all-positive left channel for middle label three. -/
def middleThreeLeftChannel (u : Nat) :
    FixedLeftCGChannel (middleThreeN u) 3 (middleThreeN u)
      (middleThreeD u) where
  k := 1
  k_le := by unfold middleThreeN; omega
  r := 1
  r_le := by unfold middleThreeN; omega
  degree_eq := by unfold middleThreeN middleThreeD; omega

/-- The natural all-positive right channel for middle label three. -/
def middleThreeRightChannel (u : Nat) :
    FixedRightCGChannel (middleThreeN u) 3 (middleThreeN u)
      (middleThreeD u) where
  p := 1
  p_le := by unfold middleThreeN; omega
  r := 1
  r_le := by unfold middleThreeN; omega
  degree_eq := by unfold middleThreeN middleThreeD; omega

/-- All four contraction orders are exactly one. -/
theorem middleThree_contraction_orders (u : Nat) :
    (middleThreeLeftChannel u).k = 1 ∧
    (middleThreeLeftChannel u).r = 1 ∧
    (middleThreeRightChannel u).p = 1 ∧
    (middleThreeRightChannel u).r = 1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Both intermediate labels are exactly `n+1`. -/
theorem middleThree_intermediates (u : Nat) :
    (middleThreeLeftChannel u).intermediate = middleThreeN u + 1 ∧
    (middleThreeRightChannel u).intermediate = middleThreeN u + 1 := by
  constructor
  · change middleThreeN u + 3 - 2 * 1 = middleThreeN u + 1
    unfold middleThreeN
    omega
  · change 3 + middleThreeN u - 2 * 1 = middleThreeN u + 1
    unfold middleThreeN
    omega

/-- Exact six-label admissibility of the natural middle-three family. -/
theorem middleThree_valid6 (u : Nat) :
    valid6 (middleThreeN u) 3 (middleThreeN u) (middleThreeD u)
      (middleThreeN u + 1) (middleThreeN u + 1) = true := by
  have hsmall : fusionOK (middleThreeN u) 3 (middleThreeN u + 1) = true :=
    (fusionOK_iff_ladder (middleThreeN u) 3 (middleThreeN u + 1)).2
      ⟨1, by unfold middleThreeN; omega, by omega,
        by unfold middleThreeN; omega⟩
  have hlarge : fusionOK (middleThreeN u) (middleThreeD u)
      (middleThreeN u + 1) = true :=
    (fusionOK_iff_ladder (middleThreeN u) (middleThreeD u)
      (middleThreeN u + 1)).2
      ⟨u + 3, by unfold middleThreeN; omega,
        by unfold middleThreeD; omega,
        by unfold middleThreeN middleThreeD; omega⟩
  unfold valid6
  simp only [hsmall, hlarge, Bool.true_and]

/-- The seven Racah parameters expose lower endpoint `2n` and upper endpoint
`2n+1`; the remaining upper parameter is one unit larger. -/
theorem middleThree_racah_parameters (u : Nat) :
    (middleThreeN u + 3 + (middleThreeN u + 1)) / 2 = u + 6 ∧
    (middleThreeN u + middleThreeD u + (middleThreeN u + 1)) / 2 =
      middleThreeT0 u ∧
    (middleThreeN u + 3 + (middleThreeN u + 1)) / 2 = u + 6 ∧
    (middleThreeN u + middleThreeD u + (middleThreeN u + 1)) / 2 =
      middleThreeT0 u ∧
    (middleThreeN u + 3 + middleThreeN u + middleThreeD u) / 2 =
      middleThreeT1 u ∧
    (3 + (middleThreeN u + 1) + middleThreeD u +
        (middleThreeN u + 1)) / 2 = 2 * u + 10 ∧
    (middleThreeN u + (middleThreeN u + 1) + middleThreeN u +
        (middleThreeN u + 1)) / 2 = middleThreeT1 u := by
  unfold middleThreeN middleThreeD middleThreeT0 middleThreeT1
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

/-- The lower endpoint is in the Racah support. -/
theorem middleThree_tGuard_at_T0 (u : Nat) :
    tGuard (u + 6) (middleThreeT0 u) (u + 6) (middleThreeT0 u)
      (middleThreeT1 u) (2 * u + 10) (middleThreeT1 u)
      (middleThreeT0 u) = true := by
  unfold tGuard middleThreeT0 middleThreeT1
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  exact ⟨by omega, by omega⟩

/-- The upper endpoint is in the Racah support. -/
theorem middleThree_tGuard_at_T1 (u : Nat) :
    tGuard (u + 6) (middleThreeT0 u) (u + 6) (middleThreeT0 u)
      (middleThreeT1 u) (2 * u + 10) (middleThreeT1 u)
      (middleThreeT1 u) = true := by
  unfold tGuard middleThreeT0 middleThreeT1
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  exact ⟨by omega, by omega⟩

/-- Every supported index lies in the two-point interval.  Since
`middleThreeT1 u = middleThreeT0 u + 1`, the preceding endpoint lemmas and
this bound identify the support exactly. -/
theorem middleThree_tGuard_bounds (u t : Nat)
    (h : tGuard (u + 6) (middleThreeT0 u) (u + 6) (middleThreeT0 u)
      (middleThreeT1 u) (2 * u + 10) (middleThreeT1 u) t = true) :
    middleThreeT0 u ≤ t ∧ t ≤ middleThreeT1 u := by
  unfold tGuard at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold middleThreeT0 middleThreeT1 at *
  constructor <;> omega

/-- Arithmetic obstruction to three adjacent terms for middle label three.
The hypotheses spell out positivity and strict interiority of the two inner
orders; the contradiction itself is the incompatible lower/upper support
bounds. -/
theorem middleThree_positive_orders_no_three_radius
    (k p : Nat) (hkPos : 1 ≤ k) (hkLt : k < 3)
    (hpPos : 1 ≤ p) (hpLt : p < 3) :
    ¬ 2 ≤ min (min k p) (3 - max k p) := by
  intro h
  have hlower : 2 ≤ min k p := (Nat.le_min.mp h).1
  have hupper : 2 ≤ 3 - max k p := (Nat.le_min.mp h).2
  have hk2 : 2 ≤ k := (Nat.le_min.mp hlower).1
  have hkmax : k ≤ max k p := Nat.le_max_left k p
  omega

end YMGap.Continuum.SU2OrderedRacahMiddleThreeFence

#print axioms YMGap.Continuum.SU2OrderedRacahMiddleThreeFence.middleThree_valid6
#print axioms YMGap.Continuum.SU2OrderedRacahMiddleThreeFence.middleThree_tGuard_at_T0
#print axioms YMGap.Continuum.SU2OrderedRacahMiddleThreeFence.middleThree_tGuard_at_T1
#print axioms YMGap.Continuum.SU2OrderedRacahMiddleThreeFence.middleThree_tGuard_bounds
#print axioms YMGap.Continuum.SU2OrderedRacahMiddleThreeFence.middleThree_positive_orders_no_three_radius
