/-
The coefficient-two harmonic mass cross in exact two-weight theta form.

The already-proved seven-Pascal closure controls the weaker rotated-shell
moving determinant.  Its one-scale residual estimate cannot simply be reused
with coefficient two (an exact counterexample is recorded below).  This file
instead exposes the strictly sharper cross-scale Pascal invariant required by
the GNS margin recursion.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalPhysicalClosure

namespace YMGap.Continuum.HarmonicMassCrossPascalReduction

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMovingDeterminantAllTail
open YMGap.Continuum.HarmonicMovingDeterminantRecurrence
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaCross
open YMGap.Continuum.HarmonicThetaCumulativeResidual
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem sharp_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "sharp_ring" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, sharp_neg_num_cast,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem mul_eqv_congr {a b c d : Q'}
    (hab : a ≈ b) (hcd : c ≈ d) : a * c ≈ b * d := by
  exact Q'.eqv_trans _ (b * c) _
    (Q'.mul_eqv_congr_right a b c hab)
    (Q'.mul_eqv_congr_left b c d hcd)

private theorem le_sub_of_add_le_local {a b c : Q'} (h : a + b ≤ c) :
    a ≤ c + -b := by
  have hs := Q'.add_le_add_right (a + b) c (-b) h
  have hleft : (a + b) + -b ≈ a := by
    refine Q'.eqv_trans _ (a + (b + -b)) _ (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ (a + 0) _
      (Q'.add_eqv_congr_left a _ _ (Q'.add_neg_self_eqv b)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' a)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hs

private def massCrossPolyL : RingNormaliser.PolyExpr :=
  .add (.mul (.var 3) (.var 0)) (.neg (.mul (.var 1) (.var 2)))

private def massCrossPolyR : RingNormaliser.PolyExpr :=
  .add
    (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
    (.neg (.mul (.add (.var 2) (.neg (.var 3))) (.var 0)))

private theorem massCrossPoly_normal :
    RingNormaliser.normalize massCrossPolyL =
      RingNormaliser.normalize massCrossPolyR := by decide

private theorem mass_cross_algebra (D0 A0 D1 A1 : Q') :
    A1 * D0 + -(A0 * D1) ≈
      (D0 + -A0) * D1 + -((D1 + -A1) * D0) := by
  simpa [massCrossPolyL, massCrossPolyR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      massCrossPolyL massCrossPolyR massCrossPoly_normal
      (fun | 0 => D0 | 1 => A0 | 2 => D1 | _ => A1))

private def scaleCrossPolyL : RingNormaliser.PolyExpr :=
  .mul (.mul (.var 0) (.var 1))
    (.add (.mul (.var 2) (.var 5)) (.neg (.mul (.var 3) (.var 4))))

private def scaleCrossPolyR : RingNormaliser.PolyExpr :=
  .add
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 5)))
    (.neg (.mul (.mul (.var 1) (.var 3)) (.mul (.var 0) (.var 4))))

private theorem scaleCrossPoly_normal :
    RingNormaliser.normalize scaleCrossPolyL =
      RingNormaliser.normalize scaleCrossPolyR := by decide

private theorem scale_cross_algebra (q0 q1 U0 U1 D0 D1 : Q') :
    (q0 * q1) * (U0 * D1 + -(U1 * D0)) ≈
      (q0 * U0) * (q1 * D1) + -((q1 * U1) * (q0 * D0)) := by
  simpa [scaleCrossPolyL, scaleCrossPolyR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      scaleCrossPolyL scaleCrossPolyR scaleCrossPoly_normal
      (fun | 0 => q0 | 1 => q1 | 2 => U0 | 3 => U1 | 4 => D0 | _ => D1))

private def physicalDeficitPolyL : RingNormaliser.PolyExpr :=
  .mul (.const 8) (.add (.var 0) (.neg (.var 1)))

private def physicalDeficitPolyR : RingNormaliser.PolyExpr :=
  .add
    (.mul (.add (.const 8) (.neg (.var 2))) (.var 0))
    (.add (.mul (.var 2) (.var 0)) (.neg (.mul (.const 8) (.var 1))))

private theorem physicalDeficitPoly_normal :
    RingNormaliser.normalize physicalDeficitPolyL =
      RingNormaliser.normalize physicalDeficitPolyR := by decide

private theorem physical_deficit_algebra (I A F : Q') :
    Q'.ofNat 8 * (I + -A) ≈
      (Q'.ofNat 8 + -F) * I + (F * I + -(Q'.ofNat 8 * A)) := by
  simpa [physicalDeficitPolyL, physicalDeficitPolyR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      physicalDeficitPolyL physicalDeficitPolyR physicalDeficitPoly_normal
      (fun | 0 => I | 1 => A | _ => F))

private def eightCorePolyL : RingNormaliser.PolyExpr :=
  .mul (.const 8)
    (.add
      (.add (.mul (.var 1) (.var 2))
        (.mul (.const 2) (.mul (.var 4) (.mul (.var 2) (.var 3)))))
      (.neg (.mul (.var 0) (.var 3))))

private def eightCorePolyR : RingNormaliser.PolyExpr :=
  .add
    (.add (.mul (.mul (.const 8) (.var 1)) (.var 2))
      (.mul (.mul (.const 16) (.var 4)) (.mul (.var 2) (.var 3))))
    (.neg (.mul (.mul (.const 8) (.var 0)) (.var 3)))

private theorem eightCorePoly_normal :
    RingNormaliser.normalize eightCorePolyL =
      RingNormaliser.normalize eightCorePolyR := by decide

private theorem eight_core_algebra (T0 T1 I0 I1 u2 : Q') :
    Q'.ofNat 8 *
        ((T1 * I0 + (Q'.ofNat 2 * u2) * (I0 * I1)) + -(T0 * I1)) ≈
      ((Q'.ofNat 8 * T1) * I0 +
        (Q'.ofNat 16 * u2) * (I0 * I1)) +
        -((Q'.ofNat 8 * T0) * I1) := by
  let a := T1 * I0
  let b := (Q'.ofNat 2 * u2) * (I0 * I1)
  let c := T0 * I1
  refine Q'.eqv_trans _
    ((Q'.ofNat 8 * a + Q'.ofNat 8 * b) +
      -(Q'.ofNat 8 * c)) _ ?_ ?_
  · refine Q'.eqv_trans _
      (Q'.ofNat 8 * (a + b) + Q'.ofNat 8 * (-c)) _
      (Q'.mul_add_eqv _ _ _) ?_
    exact Q'.add_eqv_congr'
      (Q'.mul_add_eqv _ _ _) (Q'.mul_neg_eqv _ _)
  refine Q'.add_eqv_congr'
    (Q'.add_eqv_congr' ?_ ?_) ?_
  · dsimp only [a]
    exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  · dsimp only [b]
    refine Q'.eqv_trans _
      ((Q'.ofNat 8 * Q'.ofNat 2) * (u2 * (I0 * I1))) _ ?_ ?_
    · sharp_ring
    refine Q'.eqv_trans _
      (Q'.ofNat 16 * (u2 * (I0 * I1))) _
      (Q'.mul_eqv_congr_right _ _ _ (by decide)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  · apply Q'.neg_eqv_congr
    dsimp only [c]
    exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

private def residualCorePolyL : RingNormaliser.PolyExpr :=
  .add
    (.add
      (.mul (.add (.mul (.var 1) (.var 3)) (.var 5)) (.var 2))
      (.mul (.mul (.const 16) (.var 6)) (.mul (.var 2) (.var 3))))
    (.neg (.mul (.add (.mul (.var 0) (.var 2)) (.var 4)) (.var 3)))

private def residualCorePolyR : RingNormaliser.PolyExpr :=
  .add
    (.add
      (.mul (.add (.add (.var 1) (.mul (.const 16) (.var 6)))
          (.neg (.var 0))) (.mul (.var 2) (.var 3)))
      (.mul (.var 5) (.var 2)))
    (.neg (.mul (.var 4) (.var 3)))

private theorem residualCorePoly_normal :
    RingNormaliser.normalize residualCorePolyL =
      RingNormaliser.normalize residualCorePolyR := by decide

private theorem residual_core_algebra
    (M0 M1 I0 I1 R0 R1 u2 : Q') :
    (((M1 * I1 + R1) * I0 +
        (Q'.ofNat 16 * u2) * (I0 * I1)) +
        -((M0 * I0 + R0) * I1)) ≈
      ((((M1 + Q'.ofNat 16 * u2) + -M0) * (I0 * I1) + R1 * I0) +
        -(R0 * I1)) := by
  simpa [residualCorePolyL, residualCorePolyR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      residualCorePolyL residualCorePolyR residualCorePoly_normal
      (fun | 0 => M0 | 1 => M1 | 2 => I0 | 3 => I1 | 4 => R0 | 5 => R1 | _ => u2))

/-- Integer theta normalizer at the actual quadratic cutoff. -/
def physicalIntegerTheta (k : Nat) : Q' :=
  integerThetaSum (harmW k) (Ncut k)

/-- Half-integer theta numerator at the actual quadratic cutoff. -/
def physicalHalfTheta (k : Nat) : Q' :=
  halfThetaSum (harmW k) (Ncut k)

/-- Cleared physical mass numerator `I_k-w_k H_k`. -/
def physicalThetaDeficit (k : Nat) : Q' :=
  physicalIntegerTheta k + -(harmW k * physicalHalfTheta k)

/-- The common-cutoff Pascal residual at the actual quadratic cutoff. -/
def physicalPascalResidual (k : Nat) : Q' :=
  cumulativeScaledThetaResidual (harmW k) (Ncut k)

/-- Exact coefficient-two two-weight core.  Its nonnegativity is the sharp
cross determinant after both positive Peter--Weyl normalizers are cleared. -/
def sharpMassThetaCore (k : Nat) : Q' :=
  physicalThetaDeficit (k + 1) * physicalIntegerTheta k +
    (Q'.ofNat 2 * (harmU k * harmU k)) *
      (physicalIntegerTheta k * physicalIntegerTheta (k + 1)) +
    -(physicalThetaDeficit k * physicalIntegerTheta (k + 1))

/-- Scalar reserve left after exposing both physical Pascal residuals. -/
def sharpMassMainScalar (k : Nat) : Q' :=
  retuneMarginEight (k + 1) +
    Q'.ofNat 16 * (harmU k * harmU k) + -(retuneMarginEight k)

theorem physicalIntegerTheta_nonnegative (k : Nat) :
    (0 : Q') ≤ physicalIntegerTheta k := by
  unfold physicalIntegerTheta
  exact HarmonicThetaLinearCarrier.harmonic_integerThetaSum_nonnegative k (Ncut k)

/-- The physical deficit is exactly the old `(D-A)` numerator after theta
rescaling. -/
theorem harmW_sq_mul_D_sub_A_eqv_deficit (k : Nat) :
    qpow (harmW k) 2 * (harmonicD k + -harmonicA k) ≈
      physicalThetaDeficit k := by
  have hD := coordNormSq_theta_eqv (harmW k) (Ncut k)
  have hA := adjCorr_theta_eqv (harmW k) (Ncut k)
  have hw2 : qpow (harmW k) 2 ≈ harmW k * harmW k := by
    change ((1 : Q') * harmW k) * harmW k ≈ harmW k * harmW k
    exact Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv _)
  unfold harmonicD harmonicA physicalThetaDeficit physicalIntegerTheta
    physicalHalfTheta
  refine Q'.eqv_trans _
    (qpow (harmW k) 2 * coordNormSq (harmW k) (Ncut k) +
      -(qpow (harmW k) 2 * adjCorr (harmW k) (Ncut k))) _ ?_ ?_
  · sharp_ring
  refine Q'.add_eqv_congr' hD ?_
  apply Q'.neg_eqv_congr
  refine Q'.eqv_trans _
    ((harmW k * harmW k) * adjCorr (harmW k) (Ncut k)) _
    (Q'.mul_eqv_congr_right _ _ _ hw2) ?_
  refine Q'.eqv_trans _
    (harmW k * (harmW k * adjCorr (harmW k) (Ncut k))) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  exact Q'.mul_eqv_congr_left (harmW k) _ _ hA

/-- Scaling the raw determinant by the two positive theta factors gives the
exact difference of the two physical theta deficits. -/
theorem scaled_harmonicMassCross_eqv_deficit_cross (k : Nat) :
    (qpow (harmW k) 2 * qpow (harmW (k + 1)) 2) * harmonicMassCross k ≈
      physicalThetaDeficit k * physicalIntegerTheta (k + 1) +
        -(physicalThetaDeficit (k + 1) * physicalIntegerTheta k) := by
  let q0 := qpow (harmW k) 2
  let q1 := qpow (harmW (k + 1)) 2
  let D0 := harmonicD k
  let D1 := harmonicD (k + 1)
  let A0 := harmonicA k
  let A1 := harmonicA (k + 1)
  let T0 := physicalThetaDeficit k
  let T1 := physicalThetaDeficit (k + 1)
  let I0 := physicalIntegerTheta k
  let I1 := physicalIntegerTheta (k + 1)
  have hT0 : q0 * (D0 + -A0) ≈ T0 := by
    simpa [q0, D0, A0, T0] using harmW_sq_mul_D_sub_A_eqv_deficit k
  have hT1 : q1 * (D1 + -A1) ≈ T1 := by
    simpa [q1, D1, A1, T1] using harmW_sq_mul_D_sub_A_eqv_deficit (k + 1)
  have hI0 : q0 * D0 ≈ I0 := by
    simpa [q0, D0, I0, physicalIntegerTheta] using
      (coordNormSq_theta_eqv (harmW k) (Ncut k))
  have hI1 : q1 * D1 ≈ I1 := by
    simpa [q1, D1, I1, physicalIntegerTheta] using
      (coordNormSq_theta_eqv (harmW (k + 1)) (Ncut (k + 1)))
  have hcross : harmonicMassCross k ≈
      (D0 + -A0) * D1 + -((D1 + -A1) * D0) := by
    dsimp only [D0, A0, D1, A1]
    unfold harmonicMassCross
    exact mass_cross_algebra _ _ _ _
  refine Q'.eqv_trans _
    ((q0 * (D0 + -A0)) * (q1 * D1) +
      -((q1 * (D1 + -A1)) * (q0 * D0))) _ ?_ ?_
  · dsimp only [q0, q1, D0, D1, A0, A1]
    refine Q'.eqv_trans _
      ((qpow (harmW k) 2 * qpow (harmW (k + 1)) 2) *
        (((harmonicD k + -harmonicA k) * harmonicD (k + 1)) +
          -((harmonicD (k + 1) + -harmonicA (k + 1)) * harmonicD k))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ hcross
    · exact scale_cross_algebra _ _ _ _ _ _
  exact Q'.add_eqv_congr'
    (mul_eqv_congr hT0 hI1)
    (Q'.neg_eqv_congr _ _ (mul_eqv_congr hT1 hI0))

/-- `invSqTerm 2 k` is exactly `u_k²`. -/
theorem invSqTerm_eqv_harmU_sq (k : Nat) :
    invSqTerm 2 (by decide) k ≈ harmU k * harmU k := by
  unfold invSqTerm harmU unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    Int.one_mul, Int.mul_one]
  push_cast
  rfl

/-- Nonnegativity of the sharp theta core proves the Clay-critical
coefficient-two determinant bound. -/
theorem harmonicMassCross_le_two_invSq_of_sharpThetaCore (k : Nat)
    (hcore : (0 : Q') ≤ sharpMassThetaCore k) :
    harmonicMassCross k ≤
      (Q'.ofNat 2 * invSqTerm 2 (by decide) k) *
        (harmonicD k * harmonicD (k + 1)) := by
  let q0 := qpow (harmW k) 2
  let q1 := qpow (harmW (k + 1)) 2
  let S := q0 * q1
  let X := harmonicMassCross k
  let B := Q'.ofNat 2 * invSqTerm 2 (by decide) k
  let P := harmonicD k * harmonicD (k + 1)
  let T0 := physicalThetaDeficit k
  let T1 := physicalThetaDeficit (k + 1)
  let I0 := physicalIntegerTheta k
  let I1 := physicalIntegerTheta (k + 1)
  have htheta : T0 * I1 + -(T1 * I0) ≤
      (Q'.ofNat 2 * (harmU k * harmU k)) * (I0 * I1) := by
    dsimp only [sharpMassThetaCore, T0, T1, I0, I1] at hcore
    have hle : T0 * I1 ≤
        T1 * I0 + (Q'.ofNat 2 * (harmU k * harmU k)) * (I0 * I1) :=
      Q'.le_of_sub_nonneg hcore
    exact Q'.sub_le_of_le_add hle
  have hX := scaled_harmonicMassCross_eqv_deficit_cross k
  have hP : S * P ≈ I0 * I1 := by
    dsimp only [S, P, q0, q1, I0, I1]
    have h0 := coordNormSq_theta_eqv (harmW k) (Ncut k)
    have h1 := coordNormSq_theta_eqv (harmW (k + 1)) (Ncut (k + 1))
    refine Q'.eqv_trans _
      ((qpow (harmW k) 2 * harmonicD k) *
        (qpow (harmW (k + 1)) 2 * harmonicD (k + 1))) _
      (by sharp_ring) ?_
    exact mul_eqv_congr h0 h1
  have hB : B ≈ Q'.ofNat 2 * (harmU k * harmU k) := by
    dsimp only [B]
    exact Q'.mul_eqv_congr_left _ _ _ (invSqTerm_eqv_harmU_sq k)
  have hscaled : S * X ≤ S * (B * P) := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by simpa [S, X, T0, T1, I0, I1] using hX))
      (Q'.le_trans' _ _ _ htheta (Q'.ge_of_eqv (by
        refine Q'.eqv_trans _
          (B * (S * P)) _ (by sharp_ring) ?_
        exact Q'.eqv_trans _ (B * (I0 * I1)) _
          (Q'.mul_eqv_congr_left B _ _ hP)
          (Q'.mul_eqv_congr_right _ _ (I0 * I1) hB))))
  have hS : (0 : Q') < S := by
    dsimp only [S, q0, q1]
    exact Q'.mul_pos (qpow_pos (harmW_pos k) 2)
      (qpow_pos (harmW_pos (k + 1)) 2)
  exact Q'.le_of_mul_le_mul_left hscaled hS

/-- Exact physical Pascal decomposition at a common cutoff. -/
theorem eight_mul_physicalThetaDeficit_eqv (k : Nat) :
    Q'.ofNat 8 * physicalThetaDeficit k ≈
      retuneMarginEight k * physicalIntegerTheta k +
        physicalPascalResidual k := by
  unfold physicalThetaDeficit physicalIntegerTheta physicalHalfTheta
    physicalPascalResidual retuneMarginEight cumulativeScaledThetaResidual
  exact physical_deficit_algebra _ _ _

/-- Exact two-weight Pascal normal form for the sharp mass core. -/
theorem eight_mul_sharpMassThetaCore_eqv (k : Nat) :
    Q'.ofNat 8 * sharpMassThetaCore k ≈
      (sharpMassMainScalar k *
          (physicalIntegerTheta k * physicalIntegerTheta (k + 1)) +
        physicalPascalResidual (k + 1) * physicalIntegerTheta k) +
      -(physicalPascalResidual k * physicalIntegerTheta (k + 1)) := by
  let T0 := physicalThetaDeficit k
  let T1 := physicalThetaDeficit (k + 1)
  let I0 := physicalIntegerTheta k
  let I1 := physicalIntegerTheta (k + 1)
  let M0 := retuneMarginEight k
  let M1 := retuneMarginEight (k + 1)
  let R0 := physicalPascalResidual k
  let R1 := physicalPascalResidual (k + 1)
  let u2 := harmU k * harmU k
  have h0 : Q'.ofNat 8 * T0 ≈ M0 * I0 + R0 := by
    simpa [T0, I0, M0, R0] using eight_mul_physicalThetaDeficit_eqv k
  have h1 : Q'.ofNat 8 * T1 ≈ M1 * I1 + R1 := by
    simpa [T1, I1, M1, R1] using eight_mul_physicalThetaDeficit_eqv (k + 1)
  unfold sharpMassThetaCore sharpMassMainScalar
  dsimp only [T0, T1, I0, I1, M0, M1, R0, R1, u2] at h0 h1 ⊢
  refine Q'.eqv_trans _
    ((Q'.ofNat 8 * T1) * I0 +
      (Q'.ofNat 16 * u2) * (I0 * I1) +
      -((Q'.ofNat 8 * T0) * I1)) _ ?_ ?_
  · exact eight_core_algebra T0 T1 I0 I1 u2
  refine Q'.eqv_trans _
    ((M1 * I1 + R1) * I0 +
      (Q'.ofNat 16 * u2) * (I0 * I1) +
      -((M0 * I0 + R0) * I1)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ I0 h1) (Q'.eqv_refl _))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ I1 h0))
  exact residual_core_algebra M0 M1 I0 I1 R0 R1 u2

private theorem harmonic_unit_drop_le_sq (k : Nat) :
    harmU k + -harmU (k + 1) ≤ harmU k * harmU k := by
  unfold harmU
  change Q'.mkPos 1 (k + 2) (by omega) +
      -(Q'.mkPos 1 (k + 3) (by omega)) ≤
    Q'.mkPos 1 (k + 2) (by omega) * Q'.mkPos 1 (k + 2) (by omega)
  show _ * (_ : Int) ≤ _ * (_ : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.neg_den, sharp_neg_num_cast,
    Q'.mkPos_num, Q'.mkPos_den, Int.add_mul,
    Int.neg_mul, Int.one_mul, Int.mul_one]
  push_cast
  let m : Int := (k : Int) + 2
  change (m + 1) * (m * m) + -(m * (m * m)) ≤ m * (m + 1)
  have hleft : (m + 1) * (m * m) + -(m * (m * m)) = m * m := by
    rw [Int.add_mul, Int.one_mul]
    omega
  rw [hleft]
  exact Int.mul_le_mul_of_nonneg_left (by omega) (by dsimp [m]; omega)

/-- The cubic retune profile leaves at least three inverse-square units for
the cross-scale Pascal residual. -/
theorem three_harmU_sq_le_sharpMassMainScalar (k : Nat) :
    Q'.ofNat 3 * (harmU k * harmU k) ≤ sharpMassMainScalar k := by
  let u2 := harmU k * harmU k
  let d := harmU k + -harmU (k + 1)
  let drop := retuneMarginEight k + -retuneMarginEight (k + 1)
  have hd : d ≤ u2 := by
    simpa [d, u2] using harmonic_unit_drop_le_sq k
  have h12 := Q'.mul_le_mul_of_nonneg_left d u2 (Q'.ofNat 12) hd (by decide)
  have h13 : Q'.ofNat 12 * d + u2 ≤ Q'.ofNat 13 * u2 := by
    have hadd := Q'.add_le_add_right _ _ u2 h12
    have hcoef : Q'.ofNat 12 + Q'.ofNat 1 ≈ Q'.ofNat 13 := by decide
    have heq : Q'.ofNat 12 * u2 + u2 ≈ Q'.ofNat 13 * u2 := by
      refine Q'.eqv_trans _ (Q'.ofNat 12 * u2 + Q'.ofNat 1 * u2) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv u2))
      refine Q'.eqv_trans _ ((Q'.ofNat 12 + Q'.ofNat 1) * u2) _
        (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
      · exact Q'.mul_eqv_congr_right _ _ u2 hcoef
    exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv heq)
  have hdrop : drop ≤ Q'.ofNat 13 * u2 := by
    exact Q'.le_trans' _ _ _
      (by simpa [drop, d, u2] using retuneMarginEight_drop_upper k) h13
  have hcoef : Q'.ofNat 3 + Q'.ofNat 13 ≈ Q'.ofNat 16 := by decide
  have hright : Q'.ofNat 3 * u2 + Q'.ofNat 13 * u2 ≈
      Q'.ofNat 16 * u2 := by
    refine Q'.eqv_trans _ ((Q'.ofNat 3 + Q'.ofNat 13) * u2) _
      (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
    exact Q'.mul_eqv_congr_right _ _ u2 hcoef
  have hM : retuneMarginEight k ≤
      retuneMarginEight (k + 1) + Q'.ofNat 13 * u2 := by
    have haddM := Q'.add_le_add_left (retuneMarginEight (k + 1))
      drop (Q'.ofNat 13 * u2) hdrop
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by
      dsimp only [drop]
      exact Q'.add_sub_cancel_eqv _ _))
      haddM
  have hM3 := Q'.add_le_add_left (Q'.ofNat 3 * u2) _ _ hM
  have hM16 : Q'.ofNat 3 * u2 + retuneMarginEight k ≤
      retuneMarginEight (k + 1) + Q'.ofNat 16 * u2 := by
    exact Q'.le_trans' _ _ _ hM3 (Q'.le_of_eqv (by
      refine Q'.eqv_trans _
        (retuneMarginEight (k + 1) +
          (Q'.ofNat 3 * u2 + Q'.ofNat 13 * u2)) _
        (by sharp_ring) ?_
      exact Q'.add_eqv_congr_left _ _ _ hright))
  have hout := le_sub_of_add_le_local hM16
  simpa [sharpMassMainScalar, u2] using hout

/-- The exact sharpened residual needed after the scalar reserve is spent.
This is cross-scale and normalized; unlike the false one-scale coefficient-two
bound, it retains the favorable next residual. -/
def PhysicalPascalCrossResidual (k : Nat) : Prop :=
  physicalPascalResidual k * physicalIntegerTheta (k + 1) ≤
    physicalPascalResidual (k + 1) * physicalIntegerTheta k +
      (Q'.ofNat 3 * (harmU k * harmU k)) *
        (physicalIntegerTheta k * physicalIntegerTheta (k + 1))

theorem sharpMassThetaCore_nonnegative_of_physicalPascalCross
    (k : Nat) (hcross : PhysicalPascalCrossResidual k) :
    (0 : Q') ≤ sharpMassThetaCore k := by
  let I0 := physicalIntegerTheta k
  let I1 := physicalIntegerTheta (k + 1)
  let R0 := physicalPascalResidual k
  let R1 := physicalPascalResidual (k + 1)
  let u2 := harmU k * harmU k
  let M := sharpMassMainScalar k
  have hI0 := physicalIntegerTheta_nonnegative k
  have hI1 := physicalIntegerTheta_nonnegative (k + 1)
  have hP : (0 : Q') ≤ I0 * I1 := Q'.mul_nonneg _ _ hI0 hI1
  have hmain := three_harmU_sq_le_sharpMassMainScalar k
  have hmainP := Q'.mul_le_mul_of_nonneg_right _ _ (I0 * I1) hmain hP
  have hres : R0 * I1 ≤ R1 * I0 + (Q'.ofNat 3 * u2) * (I0 * I1) := by
    simpa [PhysicalPascalCrossResidual, I0, I1, R0, R1, u2] using hcross
  have hres' : R0 * I1 ≤ M * (I0 * I1) + R1 * I0 := by
    have hadd := Q'.add_le_add_left (R1 * I0) _ _ hmainP
    exact Q'.le_trans' _ _ _ hres
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  have hscaled0 : (0 : Q') ≤ Q'.ofNat 8 * sharpMassThetaCore k := by
    have hsub := Q'.sub_nonneg_of_le hres'
    exact Q'.le_trans' _ _ _ hsub
      (Q'.le_of_eqv (Q'.eqv_symm (by
        simpa [M, I0, I1, R0, R1] using eight_mul_sharpMassThetaCore_eqv k)))
  have hmul : Q'.ofNat 8 * (0 : Q') ≤
      Q'.ofNat 8 * sharpMassThetaCore k :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv _)) hscaled0
  exact Q'.le_of_mul_le_mul_left hmul (by decide)

/-- Complete exact consumer for the GNS recursion's coefficient-two cross. -/
theorem harmonicMassCross_le_two_invSq_of_physicalPascalCross
    (k : Nat) (hcross : PhysicalPascalCrossResidual k) :
    harmonicMassCross k ≤
      (Q'.ofNat 2 * invSqTerm 2 (by decide) k) *
        (harmonicD k * harmonicD (k + 1)) :=
  harmonicMassCross_le_two_invSq_of_sharpThetaCore k
    (sharpMassThetaCore_nonnegative_of_physicalPascalCross k hcross)

/-! Exact fences around tempting but invalid shortcuts. -/

/-- The seven-Pascal one-scale residual cannot be paid with only two units at
the first tail scale.  Thus the existing full moving-determinant proof does
not imply the sharp cross by a coefficient substitution. -/
theorem old_pascal_two_unit_bound_fails_k38 :
    ¬ (normalizedDemandCoeff 38 * growingPascalResidual 38 ≤
      Q'.ofNat 2 * (harmU 38 * harmU 38) *
        integerThetaSum (harmW 38) (growingAnchor 38)) := by decide

/-- Even the growing-head Pascal residual ratio is not monotone without a
quantitative cross-scale reserve. -/
theorem growingPascalResidual_ratio_antitone_fails_k38 :
    ¬ (growingPascalResidual 38 *
          integerThetaSum (harmW 39) (growingAnchor 39) ≤
        growingPascalResidual 39 *
          integerThetaSum (harmW 38) (growingAnchor 38)) := by decide

/-- The sharpened cross orientation has real room at the tail anchor: one
inverse-square unit already repairs the false zero-reserve ratio at `k=38`.
This is an exact character-sum check, not a measured constant. -/
theorem growingPascalResidual_one_unit_cross_k38 :
    growingPascalResidual 38 *
        integerThetaSum (harmW 39) (growingAnchor 39) ≤
      growingPascalResidual 39 *
          integerThetaSum (harmW 38) (growingAnchor 38) +
        (harmU 38 * harmU 38) *
          (integerThetaSum (harmW 38) (growingAnchor 38) *
            integerThetaSum (harmW 39) (growingAnchor 39)) := by decide

#print axioms harmW_sq_mul_D_sub_A_eqv_deficit
#print axioms scaled_harmonicMassCross_eqv_deficit_cross
#print axioms harmonicMassCross_le_two_invSq_of_sharpThetaCore
#print axioms eight_mul_physicalThetaDeficit_eqv
#print axioms eight_mul_sharpMassThetaCore_eqv
#print axioms three_harmU_sq_le_sharpMassMainScalar
#print axioms sharpMassThetaCore_nonnegative_of_physicalPascalCross
#print axioms harmonicMassCross_le_two_invSq_of_physicalPascalCross
#print axioms old_pascal_two_unit_bound_fails_k38
#print axioms growingPascalResidual_ratio_antitone_fails_k38
#print axioms growingPascalResidual_one_unit_cross_k38

end YMGap.Continuum.HarmonicMassCrossPascalReduction
