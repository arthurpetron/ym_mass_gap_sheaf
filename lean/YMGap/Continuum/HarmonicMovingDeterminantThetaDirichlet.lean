/-
Crossing-adapted Dirichlet successor for the growing-head theta residual.

`HarmonicMovingDeterminantThetaAbel` is a frozen checkpoint.  This file
turns its exact adjacent-cell square identity into a cumulative finite
Dirichlet payment formula.  The remaining inequality is thereby exposed in
the same finite rational substrate, with both endpoint terms retained.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaAbel

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaCross
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem dirichlet_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "dirichlet_ring" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, show (1 : Q').num = 1 from rfl,
               show (1 : Q').den = 1 from rfl,
               Q'.neg_den, dirichlet_neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one]; ac_rfl))

private def profilePolyL : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  .mul u (.add (.add (.const 12) u) (.mul u u))

private def profilePolyR : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  let x := RingNormaliser.PolyExpr.add (.const 1)
    (.add (.const 1) (.neg u))
  .add
    (.add (.mul (.const 7) (.mul u u))
      (.neg (.mul (.mul (.mul (.const 1) x) x) x)))
    (.const 8)

private theorem profilePoly_normal :
    RingNormaliser.normalize profilePolyL =
      RingNormaliser.normalize profilePolyR := by
  decide

private theorem profile_identity (u : Q') :
    u * ((Q'.ofNat 12 + u) + u * u) ≈
      (Q'.ofNat 7 * (u * u) +
        -qpow ((1 : Q') + ((1 : Q') + -u)) 3) + Q'.ofNat 8 := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    profilePolyL profilePolyR profilePoly_normal (fun _ => u)
  simpa [profilePolyL, profilePolyR, RingNormaliser.eval, qpow] using h

private def cellRearrangePolyL : RingNormaliser.PolyExpr :=
  let U := RingNormaliser.PolyExpr.var 0
  let A := RingNormaliser.PolyExpr.var 1
  let I := RingNormaliser.PolyExpr.var 2
  let J := RingNormaliser.PolyExpr.var 3
  let D := RingNormaliser.PolyExpr.var 4
  .add (.mul (.add U (.neg A)) I)
    (.add (.mul (.const 4) (.add I J))
      (.neg (.mul (.const 4) D)))

private def cellRearrangePolyR : RingNormaliser.PolyExpr :=
  let U := RingNormaliser.PolyExpr.var 0
  let A := RingNormaliser.PolyExpr.var 1
  let I := RingNormaliser.PolyExpr.var 2
  let J := RingNormaliser.PolyExpr.var 3
  let D := RingNormaliser.PolyExpr.var 4
  .add
    (.add (.mul (.add (.add U (.neg A)) (.const 8)) I)
      (.mul (.const 4) (.add J (.neg I))))
    (.neg (.mul (.const 4) D))

private theorem cellRearrangePoly_normal :
    RingNormaliser.normalize cellRearrangePolyL =
      RingNormaliser.normalize cellRearrangePolyR := by
  decide

private theorem cell_rearrange_identity (U A I J D : Q') :
    (U + -A) * I +
        (Q'.ofNat 4 * (I + J) + -(Q'.ofNat 4 * D)) ≈
      (U + -A + Q'.ofNat 8) * I +
          Q'.ofNat 4 * (J + -I) + -(Q'.ofNat 4 * D) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    cellRearrangePolyL cellRearrangePolyR cellRearrangePoly_normal
    (fun
      | 0 => U
      | 1 => A
      | 2 => I
      | 3 => J
      | _ => D)
  simpa [cellRearrangePolyL, cellRearrangePolyR,
    RingNormaliser.eval] using h

private def cumulativeStepPolyL : RingNormaliser.PolyExpr :=
  let p := RingNormaliser.PolyExpr.var 0
  let S := RingNormaliser.PolyExpr.var 1
  let x := RingNormaliser.PolyExpr.var 2
  let y := RingNormaliser.PolyExpr.var 3
  let b := RingNormaliser.PolyExpr.var 4
  let E := RingNormaliser.PolyExpr.var 5
  let d := RingNormaliser.PolyExpr.var 6
  .add
    (.add (.add (.mul p S) (.mul (.const 4) (.add x (.neg b))))
      (.neg (.mul (.const 4) E)))
    (.add (.add (.mul p x) (.mul (.const 4) (.add y (.neg x))))
      (.neg (.mul (.const 4) d)))

private def cumulativeStepPolyR : RingNormaliser.PolyExpr :=
  let p := RingNormaliser.PolyExpr.var 0
  let S := RingNormaliser.PolyExpr.var 1
  let x := RingNormaliser.PolyExpr.var 2
  let y := RingNormaliser.PolyExpr.var 3
  let b := RingNormaliser.PolyExpr.var 4
  let E := RingNormaliser.PolyExpr.var 5
  let d := RingNormaliser.PolyExpr.var 6
  .add (.add (.mul p (.add S x))
    (.mul (.const 4) (.add y (.neg b))))
    (.neg (.mul (.const 4) (.add E d)))

private theorem cumulativeStepPoly_normal :
    RingNormaliser.normalize cumulativeStepPolyL =
      RingNormaliser.normalize cumulativeStepPolyR := by
  decide

private theorem cumulative_step_identity (p S x y b E d : Q') :
    ((p * S + Q'.ofNat 4 * (x + -b)) + -(Q'.ofNat 4 * E)) +
        ((p * x + Q'.ofNat 4 * (y + -x)) + -(Q'.ofNat 4 * d)) ≈
      (p * (S + x) + Q'.ofNat 4 * (y + -b)) +
        -(Q'.ofNat 4 * (E + d)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    cumulativeStepPolyL cumulativeStepPolyR cumulativeStepPoly_normal
    (fun
      | 0 => p
      | 1 => S
      | 2 => x
      | 3 => y
      | 4 => b
      | 5 => E
      | _ => d)
  simpa [cumulativeStepPolyL, cumulativeStepPolyR,
    RingNormaliser.eval] using h

private theorem cumulative_zero_identity (p x : Q') :
    (0 : Q') ≈
      (p * 0 + Q'.ofNat 4 * (x + -x)) + -(Q'.ofNat 4 * 0) := by
  have hp : p * 0 ≈ (0 : Q') := Q'.mul_zero_eqv p
  have hx : Q'.ofNat 4 * (x + -x) ≈ (0 : Q') :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _ (Q'.add_neg_self_eqv x))
      (Q'.mul_zero_eqv (Q'.ofNat 4))
  have hn : -(Q'.ofNat 4 * 0) ≈ -(0 : Q') :=
    Q'.neg_eqv_congr _ _ (Q'.mul_zero_eqv (Q'.ofNat 4))
  have hright :
      (p * 0 + Q'.ofNat 4 * (x + -x)) + -(Q'.ofNat 4 * 0) ≈
        ((0 : Q') + 0) + -0 :=
    Q'.add_eqv_congr' (Q'.add_eqv_congr' hp hx) hn
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (by decide))
    (Q'.eqv_symm hright)

/-- The exact bulk coefficient left after the adjacent half-theta term is
written as a trapezoid minus a Dirichlet square. -/
def sevenDirichletProfile (k : Nat) : Q' :=
  harmU k *
    ((Q'.ofNat 12 + harmU k) + harmU k * harmU k)

theorem sevenDirichletProfile_eqv (k : Nat) :
    sevenDirichletProfile k ≈
      (Q'.ofNat 7 * (harmU k * harmU k) +
        -qpow ((1 : Q') + harmW k) 3) + Q'.ofNat 8 := by
  unfold sevenDirichletProfile harmW oneSub
  exact profile_identity (harmU k)

/-- Per-cell crossing compensation: the signed seven-unit gap is an explicit
positive-profile mass, a telescoping boundary increment, and the negative
Dirichlet square. -/
theorem sevenUnitCellGap_dirichlet (k n : Nat) :
    sevenUnitCellGap k n ≈
      sevenDirichletProfile k * integerThetaTerm (harmW k) n +
        Q'.ofNat 4 *
          (integerThetaTerm (harmW k) (n + 1) +
            -integerThetaTerm (harmW k) n) +
        -(Q'.ofNat 4 * thetaDirichletCell (harmW k) n) := by
  let I := integerThetaTerm (harmW k) n
  let J := integerThetaTerm (harmW k) (n + 1)
  let D := thetaDirichletCell (harmW k) n
  let A := qpow ((1 : Q') + harmW k) 3
  let U := Q'.ofNat 7 * (harmU k * harmU k)
  have hh := halfTheta_trapezoid_dirichlet (harmW k) n
  have hp := sevenDirichletProfile_eqv k
  unfold sevenUnitCellGap growingThetaResidualCell
  refine Q'.eqv_trans _
    ((U + -A) * I + Q'.ofNat 8 *
      (harmW k * halfThetaTerm (harmW k) n)) _ (by
        dsimp only [U, A, I]
        dirichlet_ring) ?_
  refine Q'.eqv_trans _
    ((U + -A) * I +
      (Q'.ofNat 4 * (I + J) + -(Q'.ofNat 4 * D))) _
    (Q'.add_eqv_congr_left ((U + -A) * I) _ _ (by
      dsimp only [I, J, D]
      exact hh)) ?_
  refine Q'.eqv_trans _
    ((U + -A + Q'.ofNat 8) * I +
      Q'.ofNat 4 * (J + -I) + -(Q'.ofNat 4 * D)) _
    (cell_rearrange_identity U A I J D) ?_
  have hprofile : (U + -A + Q'.ofNat 8) * I ≈
      sevenDirichletProfile k * I :=
    Q'.mul_eqv_congr_right _ _ I (Q'.eqv_symm (by
      dsimp only [U, A]
      exact hp))
  have hfirst := Q'.add_eqv_congr_right _ _
    (Q'.ofNat 4 * (J + -I)) hprofile
  exact Q'.add_eqv_congr_right _ _ (-(Q'.ofNat 4 * D)) hfirst

/-- Finite telescoping of the crossing-adapted cell formula. -/
theorem finSum_sevenUnitCellGap_dirichlet (k : Nat) : ∀ N : Nat,
    finSum (fun j => sevenUnitCellGap k (j + 1)) N ≈
      sevenDirichletProfile k *
          finSum (fun j => integerThetaTerm (harmW k) (j + 1)) N +
        Q'.ofNat 4 *
          (integerThetaTerm (harmW k) (N + 1) +
            -integerThetaTerm (harmW k) 1) +
        -(Q'.ofNat 4 *
          finSum (fun j => thetaDirichletCell (harmW k) (j + 1)) N)
  | 0 => by
      simp only [finSum_zero, Nat.zero_add]
      exact cumulative_zero_identity _ _
  | N + 1 => by
      simp only [finSum_succ]
      refine Q'.eqv_trans _
        ((sevenDirichletProfile k *
              finSum (fun j => integerThetaTerm (harmW k) (j + 1)) N +
            Q'.ofNat 4 *
              (integerThetaTerm (harmW k) (N + 1) +
                -integerThetaTerm (harmW k) 1) +
            -(Q'.ofNat 4 *
              finSum (fun j => thetaDirichletCell (harmW k) (j + 1)) N)) +
          sevenUnitCellGap k (N + 1)) _
        (Q'.add_eqv_congr_right _ _ _
          (finSum_sevenUnitCellGap_dirichlet k N)) ?_
      refine Q'.eqv_trans _
        ((sevenDirichletProfile k *
              finSum (fun j => integerThetaTerm (harmW k) (j + 1)) N +
            Q'.ofNat 4 *
              (integerThetaTerm (harmW k) (N + 1) +
                -integerThetaTerm (harmW k) 1) +
            -(Q'.ofNat 4 *
              finSum (fun j => thetaDirichletCell (harmW k) (j + 1)) N)) +
          (sevenDirichletProfile k * integerThetaTerm (harmW k) (N + 1) +
            Q'.ofNat 4 *
              (integerThetaTerm (harmW k) (N + 1 + 1) +
                -integerThetaTerm (harmW k) (N + 1)) +
            -(Q'.ofNat 4 * thetaDirichletCell (harmW k) (N + 1)))) _
        (Q'.add_eqv_congr_left _ _ _
          (sevenUnitCellGap_dirichlet k (N + 1))) ?_
      exact cumulative_step_identity
        (sevenDirichletProfile k)
        (finSum (fun j => integerThetaTerm (harmW k) (j + 1)) N)
        (integerThetaTerm (harmW k) (N + 1))
        (integerThetaTerm (harmW k) (N + 1 + 1))
        (integerThetaTerm (harmW k) 1)
        (finSum (fun j => thetaDirichletCell (harmW k) (j + 1)) N)
        (thetaDirichletCell (harmW k) (N + 1))

/-- Exact cumulative Dirichlet payment for the physical seven-unit gap. -/
theorem sevenUnitResidualGap_dirichlet (k : Nat) :
    sevenUnitResidualGap k ≈
      sevenDirichletProfile k *
          integerThetaSum (harmW k) (growingAnchor k) +
        Q'.ofNat 4 *
          (integerThetaTerm (harmW k) (growingAnchor k + 2) +
            -integerThetaTerm (harmW k) 1) +
        -(Q'.ofNat 4 *
          finSum (fun j => thetaDirichletCell (harmW k) (j + 1))
            (growingAnchor k + 1)) := by
  refine Q'.eqv_trans _ _ _ (sevenUnitResidualGap_eqv_cellSum k) ?_
  have h := finSum_sevenUnitCellGap_dirichlet k (growingAnchor k + 1)
  unfold integerThetaSum
  have hend : growingAnchor k + 1 + 1 = growingAnchor k + 2 := by omega
  rw [hend] at h
  exact h

/-! ## Exact endpoint-free Poincare core -/

def sevenDirichletCoreGap (k : Nat) : Q' :=
  sevenDirichletProfile k *
      integerThetaSum (harmW k) (growingAnchor k) +
    -(Q'.ofNat 4 * integerThetaTerm (harmW k) 1) +
    -(Q'.ofNat 4 *
      finSum (fun j => thetaDirichletCell (harmW k) (j + 1))
        (growingAnchor k + 1))

private def boundaryRearrangePolyL : RingNormaliser.PolyExpr :=
  let P := RingNormaliser.PolyExpr.var 0
  let S := RingNormaliser.PolyExpr.var 1
  let E := RingNormaliser.PolyExpr.var 2
  let B := RingNormaliser.PolyExpr.var 3
  let D := RingNormaliser.PolyExpr.var 4
  .add (.add (.mul P S) (.mul (.const 4) (.add E (.neg B))))
    (.neg (.mul (.const 4) D))

private def boundaryRearrangePolyR : RingNormaliser.PolyExpr :=
  let P := RingNormaliser.PolyExpr.var 0
  let S := RingNormaliser.PolyExpr.var 1
  let E := RingNormaliser.PolyExpr.var 2
  let B := RingNormaliser.PolyExpr.var 3
  let D := RingNormaliser.PolyExpr.var 4
  .add
    (.add (.add (.mul P S) (.neg (.mul (.const 4) B)))
      (.neg (.mul (.const 4) D)))
    (.mul (.const 4) E)

private theorem boundaryRearrangePoly_normal :
    RingNormaliser.normalize boundaryRearrangePolyL =
      RingNormaliser.normalize boundaryRearrangePolyR := by
  decide

private theorem boundary_rearrange_identity (P S E B D : Q') :
    (P * S + Q'.ofNat 4 * (E + -B)) + -(Q'.ofNat 4 * D) ≈
      ((P * S + -(Q'.ofNat 4 * B)) + -(Q'.ofNat 4 * D)) +
        Q'.ofNat 4 * E := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    boundaryRearrangePolyL boundaryRearrangePolyR boundaryRearrangePoly_normal
    (fun
      | 0 => P
      | 1 => S
      | 2 => E
      | 3 => B
      | _ => D)
  simpa [boundaryRearrangePolyL, boundaryRearrangePolyR,
    RingNormaliser.eval] using h

theorem sevenUnitResidualGap_eqv_core_endpoint (k : Nat) :
    sevenUnitResidualGap k ≈
      sevenDirichletCoreGap k +
        Q'.ofNat 4 *
          integerThetaTerm (harmW k) (growingAnchor k + 2) := by
  refine Q'.eqv_trans _ _ _ (sevenUnitResidualGap_dirichlet k) ?_
  unfold sevenDirichletCoreGap
  exact boundary_rearrange_identity
    (sevenDirichletProfile k)
    (integerThetaSum (harmW k) (growingAnchor k))
    (integerThetaTerm (harmW k) (growingAnchor k + 2))
    (integerThetaTerm (harmW k) 1)
    (finSum (fun j => thetaDirichletCell (harmW k) (j + 1))
      (growingAnchor k + 1))

private theorem harmonic_integerThetaTerm_nonnegative (k n : Nat) :
    (0 : Q') ≤ integerThetaTerm (harmW k) n := by
  unfold integerThetaTerm
  exact Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
    (qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _)

theorem sevenUnitResidualGap_nonnegative_of_core {k : Nat}
    (hcore : (0 : Q') ≤ sevenDirichletCoreGap k) :
    (0 : Q') ≤ sevenUnitResidualGap k := by
  have hend : (0 : Q') ≤ Q'.ofNat 4 *
      integerThetaTerm (harmW k) (growingAnchor k + 2) :=
    Q'.mul_nonneg _ _ (by decide)
      (harmonic_integerThetaTerm_nonnegative k (growingAnchor k + 2))
  have hsum := Q'.zero_le_add _ _ hcore hend
  exact Q'.le_trans' _ _ _ hsum
    (Q'.ge_of_eqv (sevenUnitResidualGap_eqv_core_endpoint k))

/-- Exact first-scale audit of the stronger endpoint-free Poincare core. -/
theorem seven_dirichlet_core_gap_k38 :
    (0 : Q') ≤ sevenDirichletCoreGap 38 := by
  unfold sevenDirichletCoreGap sevenDirichletProfile thetaDirichletCell
    thetaRootTerm integerThetaSum integerThetaTerm growingAnchor harmW harmU
    ReciprocalBernoulliUpper.oneSub unit finSum qpow
  decide

/-- Pointwise Dirichlet allocation is false even at the first cell.  The
Poincare payment must retain a dynamically moving central window. -/
theorem pointwise_dirichlet_profile_fails_k38_n1 :
    ¬ (Q'.ofNat 4 * thetaDirichletCell (harmW 38) 1 ≤
      sevenDirichletProfile 38 * integerThetaTerm (harmW 38) 1) := by
  unfold sevenDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm harmW harmU ReciprocalBernoulliUpper.oneSub unit qpow
  decide

#print axioms sevenDirichletProfile
#print axioms sevenDirichletProfile_eqv
#print axioms sevenUnitCellGap_dirichlet
#print axioms finSum_sevenUnitCellGap_dirichlet
#print axioms sevenUnitResidualGap_dirichlet
#print axioms sevenDirichletCoreGap
#print axioms sevenUnitResidualGap_eqv_core_endpoint
#print axioms sevenUnitResidualGap_nonnegative_of_core
#print axioms seven_dirichlet_core_gap_k38
#print axioms pointwise_dirichlet_profile_fails_k38_n1

end YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet
