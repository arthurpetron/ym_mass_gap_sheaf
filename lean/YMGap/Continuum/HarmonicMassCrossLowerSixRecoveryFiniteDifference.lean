/-
Sparse finite-difference coordinates for the compressed lower-six recovery
slack.

After the artificial right-window split has been removed, the remaining
finite block is a sparse theta polynomial: one integer-theta mass, one
half-integer-theta mass, and the terminal integer mode.  This is the useful
coordinate for antitonicity inside a fixed square-root-center cell and at
the alternating even/odd right endpoints.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryCellCompression
import YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryCellCompression
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaCross
open YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem recovery_fd_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "recovery_fd_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               recovery_fd_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- Integer-theta mass in the fixed center block `1,…,2c`. -/
def lowerSixFixedIntegerMass (k c : Nat) : Q' :=
  finSum (fun j => integerThetaTerm (harmW k) (j + 1)) (2 * c)

/-- Half-integer-theta mass on the same fixed center block. -/
def lowerSixFixedHalfMass (k c : Nat) : Q' :=
  finSum (fun j => halfThetaTerm (harmW k) (j + 1)) (2 * c)

/-- Sparse theta-polynomial form of the fixed-center recovery slack. -/
def lowerSixFixedCenterSparseSlack (k c : Nat) : Q' :=
  (qpow ((1 : Q') + harmW k) 3 +
      -(Q'.ofNat 6 * (harmU k * harmU k))) *
      lowerSixFixedIntegerMass k c +
    -(Q'.ofNat 8 * (harmW k * lowerSixFixedHalfMass k c)) +
    Q'.ofNat 4 *
      integerThetaTerm (harmW k) (2 * c + 1)

private theorem finSum_lowerSixDirichletIncrement_fixed (k : Nat) : ∀ N,
    finSum (fun j => lowerSixDirichletIncrement k (j + 1)) N ≈
      Q'.ofNat 4 *
          finSum (fun j => thetaDirichletCell (harmW k) (j + 1)) N +
        -(lowerSixDirichletProfile k *
          finSum (fun j => integerThetaTerm (harmW k) (j + 1)) N)
  | 0 => by
      simp only [finSum_zero]
      recovery_fd_ring
  | N + 1 => by
      simp only [finSum_succ]
      refine Q'.eqv_trans _
        ((Q'.ofNat 4 *
              finSum (fun j => thetaDirichletCell (harmW k) (j + 1)) N +
            -(lowerSixDirichletProfile k *
              finSum (fun j => integerThetaTerm (harmW k) (j + 1)) N)) +
          lowerSixDirichletIncrement k (N + 1)) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _
          (finSum_lowerSixDirichletIncrement_fixed k N)
      · unfold lowerSixDirichletIncrement
        recovery_fd_ring

private theorem lower_six_profile_difference (k : Nat) :
    sevenDirichletProfile k ≈
      lowerSixDirichletProfile k + harmU k * harmU k := by
  unfold sevenDirichletProfile lowerSixDirichletProfile
  recovery_fd_ring

private def recoveryDirPolyL : RingNormaliser.PolyExpr :=
  let B := RingNormaliser.PolyExpr.var 0
  let D := RingNormaliser.PolyExpr.var 1
  let q := RingNormaliser.PolyExpr.var 2
  let I := RingNormaliser.PolyExpr.var 3
  .add (.mul (.const 4) B)
    (.add (.mul (.const 4) D) (.neg (.mul q I)))

private def recoveryDirPolyR : RingNormaliser.PolyExpr :=
  let B := RingNormaliser.PolyExpr.var 0
  let D := RingNormaliser.PolyExpr.var 1
  let q := RingNormaliser.PolyExpr.var 2
  let I := RingNormaliser.PolyExpr.var 3
  let u := RingNormaliser.PolyExpr.var 4
  let E := RingNormaliser.PolyExpr.var 5
  .add
    (.add (.mul (.mul u u) I) (.mul (.const 4) E))
    (.neg
      (.add
        (.add (.mul (.add q (.mul u u)) I)
          (.mul (.const 4) (.add E (.neg B))))
        (.neg (.mul (.const 4) D))))

private theorem recoveryDirPoly_normal :
    RingNormaliser.normalize recoveryDirPolyL =
      RingNormaliser.normalize recoveryDirPolyR := by
  decide

private theorem recovery_dir_algebra (B D q I u E : Q') :
    Q'.ofNat 4 * B + (Q'.ofNat 4 * D + -(q * I)) ≈
      ((u * u) * I + Q'.ofNat 4 * E) +
        -((q + u * u) * I + Q'.ofNat 4 * (E + -B) +
          -(Q'.ofNat 4 * D)) := by
  simpa [recoveryDirPolyL, recoveryDirPolyR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      recoveryDirPolyL recoveryDirPolyR recoveryDirPoly_normal
      (fun
        | 0 => B
        | 1 => D
        | 2 => q
        | 3 => I
        | 4 => u
        | _ => E))

private def recoveryGapPolyL : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  let I := RingNormaliser.PolyExpr.var 1
  let E := RingNormaliser.PolyExpr.var 2
  let R := RingNormaliser.PolyExpr.var 3
  .add
    (.add (.mul (.mul u u) I) (.mul (.const 4) E))
    (.neg (.add (.mul (.mul (.const 7) (.mul u u)) I) (.neg R)))

private def recoveryGapPolyR : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  let I := RingNormaliser.PolyExpr.var 1
  let E := RingNormaliser.PolyExpr.var 2
  let R := RingNormaliser.PolyExpr.var 3
  .add (.add R (.neg (.mul (.mul (.const 6) (.mul u u)) I)))
    (.mul (.const 4) E)

private theorem recoveryGapPoly_normal :
    RingNormaliser.normalize recoveryGapPolyL =
      RingNormaliser.normalize recoveryGapPolyR := by
  decide

private theorem recovery_gap_algebra (u I E R : Q') :
    ((u * u) * I + Q'.ofNat 4 * E) +
        -(Q'.ofNat 7 * (u * u) * I + -R) ≈
      R + -(Q'.ofNat 6 * (u * u) * I) + Q'.ofNat 4 * E := by
  simpa [recoveryGapPolyL, recoveryGapPolyR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      recoveryGapPolyL recoveryGapPolyR recoveryGapPoly_normal
      (fun | 0 => u | 1 => I | 2 => E | _ => R))

private def recoverySparsePolyL : RingNormaliser.PolyExpr :=
  let A := RingNormaliser.PolyExpr.var 0
  let I := RingNormaliser.PolyExpr.var 1
  let w := RingNormaliser.PolyExpr.var 2
  let H := RingNormaliser.PolyExpr.var 3
  let u := RingNormaliser.PolyExpr.var 4
  let E := RingNormaliser.PolyExpr.var 5
  .add
    (.add (.mul A I) (.neg (.mul (.const 8) (.mul w H))))
    (.add (.neg (.mul (.mul (.const 6) (.mul u u)) I))
      (.mul (.const 4) E))

private def recoverySparsePolyR : RingNormaliser.PolyExpr :=
  let A := RingNormaliser.PolyExpr.var 0
  let I := RingNormaliser.PolyExpr.var 1
  let w := RingNormaliser.PolyExpr.var 2
  let H := RingNormaliser.PolyExpr.var 3
  let u := RingNormaliser.PolyExpr.var 4
  let E := RingNormaliser.PolyExpr.var 5
  .add
    (.add (.mul (.add A (.neg (.mul (.const 6) (.mul u u)))) I)
      (.neg (.mul (.const 8) (.mul w H))))
    (.mul (.const 4) E)

private theorem recoverySparsePoly_normal :
    RingNormaliser.normalize recoverySparsePolyL =
      RingNormaliser.normalize recoverySparsePolyR := by
  decide

private theorem recovery_sparse_algebra (A I w H u E : Q') :
    (A * I + -(Q'.ofNat 8 * (w * H))) +
        (-(Q'.ofNat 6 * (u * u) * I) + Q'.ofNat 4 * E) ≈
      (A + -(Q'.ofNat 6 * (u * u))) * I +
        -(Q'.ofNat 8 * (w * H)) + Q'.ofNat 4 * E := by
  simpa [recoverySparsePolyL, recoverySparsePolyR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      recoverySparsePolyL recoverySparsePolyR recoverySparsePoly_normal
      (fun
        | 0 => A
        | 1 => I
        | 2 => w
        | 3 => H
        | 4 => u
        | _ => E))

/-- Exact sparse-polynomial reconstruction of the compressed fixed-center
slack.  No inequality or sampled coefficient is used. -/
theorem lowerSixFixedCenterSlack_eqv_sparse (k c : Nat) :
    lowerSixFixedCenterSlack k c ≈
      lowerSixFixedCenterSparseSlack k c := by
  let N := 2 * c
  let u := harmU k
  let w := harmW k
  let I := finSum (fun j => integerThetaTerm w (j + 1)) N
  let H := finSum (fun j => halfThetaTerm w (j + 1)) N
  let D := finSum (fun j => thetaDirichletCell w (j + 1)) N
  let B := integerThetaTerm w 1
  let E := integerThetaTerm w (N + 1)
  let p := sevenDirichletProfile k
  let q := lowerSixDirichletProfile k
  let G := finSum (fun j => sevenUnitCellGap k (j + 1)) N
  let R := finSum (fun j => growingThetaResidualCell w (j + 1)) N
  let A := qpow ((1 : Q') + w) 3
  have hlow :
      finSum (fun j => lowerSixDirichletIncrement k (j + 1)) N ≈
        Q'.ofNat 4 * D + -(q * I) := by
    dsimp only [N, w, D, q, I]
    exact finSum_lowerSixDirichletIncrement_fixed k (2 * c)
  have hdir :
      G ≈
        p * I + Q'.ofNat 4 * (E + -B) + -(Q'.ofNat 4 * D) := by
    dsimp only [G, p, I, E, B, D, N, w]
    exact finSum_sevenUnitCellGap_dirichlet k (2 * c)
  have hgap :
      G ≈ Q'.ofNat 7 * (u * u) * I + -R := by
    dsimp only [G, u, I, R, N, w]
    exact finSum_sevenUnitCellGap_eqv k (2 * c)
  have hres :
      R ≈ A * I + -(Q'.ofNat 8 * (w * H)) := by
    dsimp only [R, A, I, H, N]
    exact finSum_residualCell_eqv w (2 * c)
  have hp : p ≈ q + u * u := by
    dsimp only [p, q, u]
    exact lower_six_profile_difference k
  unfold lowerSixFixedCenterSlack lowerSixFixedCenterSparseSlack
    lowerSixFixedIntegerMass lowerSixFixedHalfMass
  dsimp only [N, u, w, I, H, D, B, E, p, q, G, R, A] at hlow hdir hgap hres hp ⊢
  change
    Q'.ofNat 4 * B +
        finSum (fun j => lowerSixDirichletIncrement k (j + 1)) N ≈
      (A + -(Q'.ofNat 6 * (u * u))) * I +
        -(Q'.ofNat 8 * (w * H)) + Q'.ofNat 4 * E
  refine Q'.eqv_trans _
    (Q'.ofNat 4 * B + (Q'.ofNat 4 * D + -(q * I))) _
    (Q'.add_eqv_congr_left (Q'.ofNat 4 * B) _ _ hlow) ?_
  have hdirProfile :
      p * I + Q'.ofNat 4 * (E + -B) + -(Q'.ofNat 4 * D) ≈
        (q + u * u) * I + Q'.ofNat 4 * (E + -B) +
          -(Q'.ofNat 4 * D) := by
    exact Q'.add_eqv_congr_right _ _ (-(Q'.ofNat 4 * D))
      (Q'.add_eqv_congr_right _ _ (Q'.ofNat 4 * (E + -B))
        (Q'.mul_eqv_congr_right _ _ I hp))
  have halgDir :
      Q'.ofNat 4 * B + (Q'.ofNat 4 * D + -(q * I)) ≈
        ((u * u) * I + Q'.ofNat 4 * E) +
          -(p * I + Q'.ofNat 4 * (E + -B) +
            -(Q'.ofNat 4 * D)) := by
    refine Q'.eqv_trans _
      (((u * u) * I + Q'.ofNat 4 * E) +
        -((q + u * u) * I + Q'.ofNat 4 * (E + -B) +
          -(Q'.ofNat 4 * D))) _ (recovery_dir_algebra B D q I u E) ?_
    exact Q'.add_eqv_congr_left ((u * u) * I + Q'.ofNat 4 * E) _ _
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hdirProfile))
  refine Q'.eqv_trans _
    (((u * u) * I + Q'.ofNat 4 * E) +
      -(p * I + Q'.ofNat 4 * (E + -B) +
        -(Q'.ofNat 4 * D))) _ halgDir ?_
  refine Q'.eqv_trans _
    (((u * u) * I + Q'.ofNat 4 * E) + -G) _ ?_ ?_
  · exact Q'.add_eqv_congr_left ((u * u) * I + Q'.ofNat 4 * E) _ _
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hdir))
  refine Q'.eqv_trans _
    (((u * u) * I + Q'.ofNat 4 * E) +
      -(Q'.ofNat 7 * (u * u) * I + -R)) _
    (Q'.add_eqv_congr_left ((u * u) * I + Q'.ofNat 4 * E) _ _
      (Q'.neg_eqv_congr _ _ hgap)) ?_
  refine Q'.eqv_trans _
    (R + -(Q'.ofNat 6 * (u * u) * I) + Q'.ofNat 4 * E) _
    (recovery_gap_algebra u I E R) ?_
  refine Q'.eqv_trans _
    (R + (-(Q'.ofNat 6 * (u * u) * I) + Q'.ofNat 4 * E)) _
    (Q'.add_assoc_eqv R (-(Q'.ofNat 6 * (u * u) * I))
      (Q'.ofNat 4 * E)) ?_
  refine Q'.eqv_trans _
    ((A * I + -(Q'.ofNat 8 * (w * H))) +
      (-(Q'.ofNat 6 * (u * u) * I) + Q'.ofNat 4 * E)) _
    (Q'.add_eqv_congr_right _ _
      (-(Q'.ofNat 6 * (u * u) * I) + Q'.ofNat 4 * E) hres) ?_
  exact recovery_sparse_algebra A I w H u E

/-- Cleared one-step drop inside a fixed center cell.  Proving this
nonnegative is exactly the within-cell antitonicity target. -/
def lowerSixFixedCenterDrop (k c : Nat) : Q' :=
  lowerSixFixedCenterSparseSlack k c +
    -lowerSixFixedCenterSparseSlack (k + 1) c

/-- The two right-endpoint families supplied by the exact center-band
decomposition. -/
def lowerSixEvenCenterRightScale (m : Nat) : Nat :=
  2 * m * m + 2 * m - 3

def lowerSixOddCenterRightScale (m : Nat) : Nat :=
  2 * m * (m + 1) + 2 * m - 1

/-- Alternating even-to-odd endpoint drop. -/
def lowerSixEvenOddEndpointDrop (m : Nat) : Q' :=
  lowerSixFixedCenterSparseSlack (lowerSixEvenCenterRightScale m) (2 * m) +
    -lowerSixFixedCenterSparseSlack
      (lowerSixOddCenterRightScale m) (2 * m + 1)

/-- Alternating odd-to-next-even endpoint drop. -/
def lowerSixOddEvenEndpointDrop (m : Nat) : Q' :=
  lowerSixFixedCenterSparseSlack (lowerSixOddCenterRightScale m) (2 * m + 1) +
    -lowerSixFixedCenterSparseSlack
      (lowerSixEvenCenterRightScale (m + 1)) (2 * (m + 1))

/-! ## Denominator-cleared polynomial targets -/

/-- Largest power of the harmonic weight in the fixed block through mode
`2c`, attained by the terminal mode `2c+1`. -/
def lowerSixCenterMaxExponent (c : Nat) : Nat :=
  2 * ((2 * c + 1) * (2 * c + 1))

/-- Common denominator exponent after also clearing the cubic profile. -/
def lowerSixCenterClearingExponent (c : Nat) : Nat :=
  lowerSixCenterMaxExponent c + 3

/-- Cubic numerator
`D^3 * ((1 + (D-1)/D)^3 - 6/D^2) = (2D-1)^3 - 6D`. -/
def lowerSixCenterCubicNumerator (D : Nat) : Q' :=
  qpow (Q'.ofNat (2 * D) + -(1 : Q')) 3 +
    -(Q'.ofNat (6 * D))

/-- Denominator-cleared sparse center slack.  For `D=k+2`, multiplication
of `lowerSixFixedCenterSparseSlack k c` by
`D^(lowerSixCenterClearingExponent c)` yields this exact integer polynomial.
The exponent differences are nontruncated on every summand in the physical
domain `j < 2c`. -/
def lowerSixClearedCenterSlack (D c : Nat) : Q' :=
  let N := 2 * c
  let M := lowerSixCenterMaxExponent c
  let intPart := finSum (fun j =>
    let n := j + 1
    let e := 2 * (n * n)
    ((lowerSixCenterCubicNumerator D * Q'.ofNat (n * n)) *
      qpow (Q'.ofNat (D - 1)) e) *
      qpow (Q'.ofNat D) (M - e)) N
  let halfPart := finSum (fun j =>
    let n := j + 1
    let e := 2 * (n * (n + 1))
    (Q'.ofNat (n * (n + 1)) *
      qpow (Q'.ofNat (D - 1)) (e + 1)) *
      qpow (Q'.ofNat D) (M + 2 - e)) N
  let terminal :=
    (Q'.ofNat (4 * ((N + 1) * (N + 1))) *
      qpow (Q'.ofNat (D - 1)) M) * qpow (Q'.ofNat D) 3
  intPart + -(Q'.ofNat 8 * halfPart) + terminal

/-- Cleared within-cell drop.  Its nonnegativity is the exact polynomial
target for `S(D,c) >= S(D+1,c)`. -/
def lowerSixWithinCellClearedDrop (D c : Nat) : Q' :=
  let L := lowerSixCenterClearingExponent c
  qpow (Q'.ofNat (D + 1)) L * lowerSixClearedCenterSlack D c +
    -(qpow (Q'.ofNat D) L * lowerSixClearedCenterSlack (D + 1) c)

/-- Exact physical domain in which both consecutive denominators have the
same square-root center `c`. -/
def LowerSixWithinCenterCell (D c : Nat) : Prop :=
  2 ≤ D ∧ 10 ≤ c ∧
    c * c ≤ 2 * D + 1 ∧
    2 * (D + 1) + 1 < (c + 1) * (c + 1)

/-- Right-endpoint denominators (`D=k+2`) for the even and odd center
families. -/
def lowerSixEvenCenterRightDen (m : Nat) : Nat :=
  2 * m * m + 2 * m - 1

def lowerSixOddCenterRightDen (m : Nat) : Nat :=
  2 * m * (m + 1) + 2 * m + 1

/-- Cleared even-center to odd-center right-endpoint drop. -/
def lowerSixEvenOddEndpointClearedDrop (m : Nat) : Q' :=
  let De := lowerSixEvenCenterRightDen m
  let Do := lowerSixOddCenterRightDen m
  let Le := lowerSixCenterClearingExponent (2 * m)
  let Lo := lowerSixCenterClearingExponent (2 * m + 1)
  qpow (Q'.ofNat Do) Lo * lowerSixClearedCenterSlack De (2 * m) +
    -(qpow (Q'.ofNat De) Le *
      lowerSixClearedCenterSlack Do (2 * m + 1))

/-- Cleared odd-center to next-even-center right-endpoint drop. -/
def lowerSixOddEvenEndpointClearedDrop (m : Nat) : Q' :=
  let Do := lowerSixOddCenterRightDen m
  let De := lowerSixEvenCenterRightDen (m + 1)
  let Lo := lowerSixCenterClearingExponent (2 * m + 1)
  let Le := lowerSixCenterClearingExponent (2 * (m + 1))
  qpow (Q'.ofNat De) Le *
      lowerSixClearedCenterSlack Do (2 * m + 1) +
    -(qpow (Q'.ofNat Do) Lo *
      lowerSixClearedCenterSlack De (2 * (m + 1)))

/-- The single terminal polynomial required by the finite bridge.  Here
`D=8191`, `k=D-2=8189`, and `thetaWindowCenter k=127`. -/
def lowerSixTerminalCenterPolynomial : Q' :=
  lowerSixClearedCenterSlack 8191 127

#print axioms lowerSixFixedCenterSlack_eqv_sparse

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
