/-
Dirichlet-energy coordinates for the fixed-center lower-six recovery slack.

The denominator-cleared polynomial is exact, but too large to expose its sign
mechanism directly.  Before taking a finite difference, the same slack is a
finite sum of literal adjacent-root squares, one left boundary square, and one
Gaussian moment debt with profile `12u + u^3`.  This file records that
regrouping without estimates or sampled constants.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryClearing

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryEnergy

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryCellCompression
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem recovery_energy_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "recovery_energy_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               recovery_energy_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- The lower-six profile written as the explicit moment-debt coefficient
`12u + u^3`. -/
def lowerSixRecoveryEnergyProfile (k : Nat) : Q' :=
  Q'.ofNat 12 * harmU k +
    (harmU k * harmU k) * harmU k

theorem lowerSixDirichletProfile_eqv_recoveryEnergyProfile (k : Nat) :
    lowerSixDirichletProfile k ≈ lowerSixRecoveryEnergyProfile k := by
  unfold lowerSixDirichletProfile lowerSixRecoveryEnergyProfile
  recovery_energy_ring

/-- Exact fixed-center Dirichlet energy.  `thetaDirichletCell w n` is the
literal square
`(n*w^(n^2) - (n+1)*w^((n+1)^2))^2`; the second term is the left boundary
square, and the final term is the sole signed moment debt. -/
def lowerSixFixedCenterEnergy (k c : Nat) : Q' :=
  Q'.ofNat 4 *
      finSum (fun j => thetaDirichletCell (harmW k) (j + 1)) (2 * c) +
    Q'.ofNat 4 * integerThetaTerm (harmW k) 1 +
    -(lowerSixRecoveryEnergyProfile k * lowerSixFixedIntegerMass k c)

private theorem lowerSixDirichletBlock_eqv_energy (k : Nat) : ∀ N,
    finSum (fun j => lowerSixDirichletIncrement k (j + 1)) N ≈
      Q'.ofNat 4 *
          finSum (fun j => thetaDirichletCell (harmW k) (j + 1)) N +
        -(lowerSixDirichletProfile k *
          finSum (fun j => integerThetaTerm (harmW k) (j + 1)) N)
  | 0 => by
      simp only [finSum_zero]
      recovery_energy_ring
  | N + 1 => by
      simp only [finSum_succ]
      refine Q'.eqv_trans _
        ((Q'.ofNat 4 *
              finSum (fun j => thetaDirichletCell (harmW k) (j + 1)) N +
            -(lowerSixDirichletProfile k *
              finSum (fun j => integerThetaTerm (harmW k) (j + 1)) N)) +
          lowerSixDirichletIncrement k (N + 1)) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _
          (lowerSixDirichletBlock_eqv_energy k N)
      · unfold lowerSixDirichletIncrement
        recovery_energy_ring

/-- The exposed fixed-center slack is exactly the square-energy expression. -/
theorem lowerSixFixedCenterSlack_eqv_energy (k c : Nat) :
    lowerSixFixedCenterSlack k c ≈ lowerSixFixedCenterEnergy k c := by
  have hblock := lowerSixDirichletBlock_eqv_energy k (2 * c)
  unfold lowerSixFixedCenterSlack lowerSixFixedCenterEnergy
    lowerSixFixedIntegerMass
  refine Q'.eqv_trans _
    (Q'.ofNat 4 * integerThetaTerm (harmW k) 1 +
      (Q'.ofNat 4 *
          finSum (fun j => thetaDirichletCell (harmW k) (j + 1)) (2 * c) +
        -(lowerSixDirichletProfile k *
          finSum (fun j => integerThetaTerm (harmW k) (j + 1)) (2 * c)))) _
    (Q'.add_eqv_congr_left _ _ _ hblock) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat 4 * integerThetaTerm (harmW k) 1 +
      (Q'.ofNat 4 *
          finSum (fun j => thetaDirichletCell (harmW k) (j + 1)) (2 * c) +
        -(lowerSixRecoveryEnergyProfile k *
          finSum (fun j => integerThetaTerm (harmW k) (j + 1)) (2 * c)))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_right _ _ _
            (lowerSixDirichletProfile_eqv_recoveryEnergyProfile k))))
  · recovery_energy_ring

/-- Sparse theta coordinates and Dirichlet-energy coordinates are identical.
This is the exact, estimate-free regrouping used by the symbolic positivity
attack. -/
theorem lowerSixFixedCenterSparseSlack_eqv_energy (k c : Nat) :
    lowerSixFixedCenterSparseSlack k c ≈
      lowerSixFixedCenterEnergy k c := by
  exact Q'.eqv_trans _ (lowerSixFixedCenterSlack k c) _
    (Q'.eqv_symm (lowerSixFixedCenterSlack_eqv_sparse k c))
    (lowerSixFixedCenterSlack_eqv_energy k c)

/-- The raw within-cell drop is therefore exactly the adjacent difference of
the two finite energies. -/
theorem lowerSixFixedCenterDrop_eqv_energyDrop (k c : Nat) :
    lowerSixFixedCenterDrop k c ≈
      lowerSixFixedCenterEnergy k c +
        -lowerSixFixedCenterEnergy (k + 1) c := by
  unfold lowerSixFixedCenterDrop
  exact Q'.add_eqv_congr'
    (lowerSixFixedCenterSparseSlack_eqv_energy k c)
    (Q'.neg_eqv_congr _ _
      (lowerSixFixedCenterSparseSlack_eqv_energy (k + 1) c))

/-! ## Exact anchors for a normalized monotonicity route -/

/-- Dimensionless within-cell drop.  The factor `2D^2`, with `D=k+2`,
is chosen so that a unit lower bound is stable under the physical
square-root-cell traversal; no sign cancellation is hidden in this
definition. -/
def lowerSixNormalizedWithinCellDrop (k c : Nat) : Q' :=
  Q'.ofNat (2 * (k + 2) * (k + 2)) * lowerSixFixedCenterDrop k c

/-- Dimensionless even-to-odd endpoint drop. -/
def lowerSixNormalizedEvenOddEndpointDrop (m : Nat) : Q' :=
  Q'.ofNat (12 * lowerSixEvenCenterRightDen m) *
    lowerSixEvenOddEndpointDrop m

/-- Dimensionless odd-to-even endpoint drop. -/
def lowerSixNormalizedOddEvenEndpointDrop (m : Nat) : Q' :=
  Q'.ofNat (12 * lowerSixOddCenterRightDen m) *
    lowerSixOddEvenEndpointDrop m

private theorem recovery_energy_ofNat_pos {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  rcases n with _ | n
  · omega
  · exact Q'.ofNat_succ_pos n

/-- A unit lower bound for the normalized within-cell drop is already enough
to recover the raw sign needed by the traversal.  This is a constructive
cancellation lemma: the normalizing factor is an explicitly positive natural
number. -/
theorem lowerSixFixedCenterDrop_nonnegative_of_normalized_unit
    {k c : Nat}
    (h : (1 : Q') ≤ lowerSixNormalizedWithinCellDrop k c) :
    (0 : Q') ≤ lowerSixFixedCenterDrop k c := by
  have hk2 : 0 < k + 2 := by omega
  have hfactorNat : 0 < 2 * (k + 2) * (k + 2) :=
    Nat.mul_pos (Nat.mul_pos (by omega) hk2) hk2
  have hscaled : (0 : Q') ≤ lowerSixNormalizedWithinCellDrop k c :=
    Q'.le_trans' _ _ _ Q'.zero_le_one h
  unfold lowerSixNormalizedWithinCellDrop at hscaled
  exact Q'.nonneg_of_mul_pos
    (recovery_energy_ofNat_pos hfactorNat) hscaled

/-- Constructively cancel the positive even-endpoint normalization. -/
theorem lowerSixEvenOddEndpointDrop_nonnegative_of_normalized_unit
    {m : Nat} (hm : 1 ≤ m)
    (h : (1 : Q') ≤ lowerSixNormalizedEvenOddEndpointDrop m) :
    (0 : Q') ≤ lowerSixEvenOddEndpointDrop m := by
  have hmm : 1 ≤ m * m := Nat.mul_le_mul hm hm
  have hquad : 2 ≤ 2 * m * m := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hmm
  have hfactorNat : 0 < 12 * lowerSixEvenCenterRightDen m := by
    unfold lowerSixEvenCenterRightDen
    omega
  have hscaled : (0 : Q') ≤ lowerSixNormalizedEvenOddEndpointDrop m :=
    Q'.le_trans' _ _ _ Q'.zero_le_one h
  unfold lowerSixNormalizedEvenOddEndpointDrop at hscaled
  exact Q'.nonneg_of_mul_pos
    (recovery_energy_ofNat_pos hfactorNat) hscaled

/-- Constructively cancel the positive odd-endpoint normalization. -/
theorem lowerSixOddEvenEndpointDrop_nonnegative_of_normalized_unit
    {m : Nat} (hm : 1 ≤ m)
    (h : (1 : Q') ≤ lowerSixNormalizedOddEvenEndpointDrop m) :
    (0 : Q') ≤ lowerSixOddEvenEndpointDrop m := by
  have hfactorNat : 0 < 12 * lowerSixOddCenterRightDen m := by
    unfold lowerSixOddCenterRightDen
    omega
  have hscaled : (0 : Q') ≤ lowerSixNormalizedOddEvenEndpointDrop m :=
    Q'.le_trans' _ _ _ Q'.zero_le_one h
  unfold lowerSixNormalizedOddEvenEndpointDrop at hscaled
  exact Q'.nonneg_of_mul_pos
    (recovery_energy_ofNat_pos hfactorNat) hscaled

/-- Exact first physical within-cell anchor (`D=50,c=10`). -/
theorem lowerSixNormalizedWithinCellDrop_48_10_unit :
    (1 : Q') ≤ lowerSixNormalizedWithinCellDrop 48 10 := by
  unfold lowerSixNormalizedWithinCellDrop lowerSixFixedCenterDrop
    lowerSixFixedCenterSparseSlack lowerSixFixedIntegerMass
    lowerSixFixedHalfMass
    integerThetaTerm halfThetaTerm harmW harmU oneSub unit qpow
  decide

/-- Exact first even-to-odd center-transition anchor (`m=5`). -/
theorem lowerSixNormalizedEvenOddEndpointDrop_5_unit :
    (1 : Q') ≤ lowerSixNormalizedEvenOddEndpointDrop 5 := by
  unfold lowerSixNormalizedEvenOddEndpointDrop lowerSixEvenOddEndpointDrop
    lowerSixEvenCenterRightDen lowerSixEvenCenterRightScale
    lowerSixOddCenterRightScale lowerSixFixedCenterSparseSlack
    lowerSixFixedIntegerMass lowerSixFixedHalfMass
    integerThetaTerm halfThetaTerm harmW harmU oneSub unit qpow
  decide

/-- Exact first odd-to-even center-transition anchor (`m=5`). -/
theorem lowerSixNormalizedOddEvenEndpointDrop_5_unit :
    (1 : Q') ≤ lowerSixNormalizedOddEvenEndpointDrop 5 := by
  unfold lowerSixNormalizedOddEvenEndpointDrop lowerSixOddEvenEndpointDrop
    lowerSixOddCenterRightDen lowerSixOddCenterRightScale
    lowerSixEvenCenterRightScale lowerSixFixedCenterSparseSlack
    lowerSixFixedIntegerMass lowerSixFixedHalfMass
    integerThetaTerm halfThetaTerm harmW harmU oneSub unit qpow
  decide

/-- Raw within-cell sign at the first physical scale. -/
theorem lowerSixFixedCenterDrop_48_10_nonnegative :
    (0 : Q') ≤ lowerSixFixedCenterDrop 48 10 :=
  lowerSixFixedCenterDrop_nonnegative_of_normalized_unit
    lowerSixNormalizedWithinCellDrop_48_10_unit

/-- Raw even-to-odd endpoint sign at the first center transition. -/
theorem lowerSixEvenOddEndpointDrop_5_nonnegative :
    (0 : Q') ≤ lowerSixEvenOddEndpointDrop 5 :=
  lowerSixEvenOddEndpointDrop_nonnegative_of_normalized_unit (by omega)
    lowerSixNormalizedEvenOddEndpointDrop_5_unit

/-- Raw odd-to-even endpoint sign at the first center transition. -/
theorem lowerSixOddEvenEndpointDrop_5_nonnegative :
    (0 : Q') ≤ lowerSixOddEvenEndpointDrop 5 :=
  lowerSixOddEvenEndpointDrop_nonnegative_of_normalized_unit (by omega)
    lowerSixNormalizedOddEvenEndpointDrop_5_unit

#print axioms lowerSixDirichletProfile_eqv_recoveryEnergyProfile
#print axioms lowerSixFixedCenterSlack_eqv_energy
#print axioms lowerSixFixedCenterSparseSlack_eqv_energy
#print axioms lowerSixFixedCenterDrop_eqv_energyDrop
#print axioms lowerSixFixedCenterDrop_nonnegative_of_normalized_unit
#print axioms lowerSixEvenOddEndpointDrop_nonnegative_of_normalized_unit
#print axioms lowerSixOddEvenEndpointDrop_nonnegative_of_normalized_unit
#print axioms lowerSixNormalizedWithinCellDrop_48_10_unit
#print axioms lowerSixNormalizedEvenOddEndpointDrop_5_unit
#print axioms lowerSixNormalizedOddEvenEndpointDrop_5_unit
#print axioms lowerSixFixedCenterDrop_48_10_nonnegative
#print axioms lowerSixEvenOddEndpointDrop_5_nonnegative
#print axioms lowerSixOddEvenEndpointDrop_5_nonnegative

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryEnergy
