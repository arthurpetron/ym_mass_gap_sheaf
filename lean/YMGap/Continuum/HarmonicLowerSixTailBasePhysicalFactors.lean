/-
# Physical meanings of the Base clearing factors

The structured Base polynomial uses the exact integer clearings

* `L1C = 2520 * (D+1)^8 * lowerSixTailNextSlopeFloor`, and
* `U0C = 22680 * D^9 * lowerSixTailOldSlopeCeiling`.

Both identities are derived here.  The first comes from the public
slope-floor bridge after positive-factor cancellation.  The second is
obtained from a closed 16-scaled polynomial identity and the ninth-order
Taylor bridge; no division enters either proof.
-/

import YMGap.Continuum.HarmonicLowerSixTailBaseSemanticEvaluation
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorSemantic
import YMGap.Constructive.ExpAddConv

namespace YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicLowerSixExactCertificate
open YMGap.Continuum.HarmonicLowerSixSecondFluxSign
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorSemantic
open YMGap.Continuum.HarmonicLowerSixTailSecondFluxLocalBound
open YMGap.Continuum.HarmonicLowerSixTailSlopeFloorCertificate
open YMGap.Continuum.HarmonicLowerSixTailSlopeFloorCertificateData
open YMGap.Continuum.HarmonicLowerSixTailTaylorNineCertificate
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.TensorBernsteinHomogeneousCertificate

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr

/- Kernel-checked normalizer for Q' polynomial rearrangements.  The tactic
reduces `eqv` to exact integer cross multiplication and closes only with
primitive integer identities plus associativity/commutativity. -/
private theorem semantic_neg_num (a : Q') : (-a).num = -a.num := rfl
private theorem semantic_ofInt_num (z : Int) : (Q'.ofInt z).num = z := rfl
private theorem semantic_ofInt_den (z : Int) :
    ((Q'.ofInt z).den : Int) = 1 := rfl

local macro "semantic_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp_all only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               semantic_neg_num, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               semantic_ofInt_num, semantic_ofInt_den,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             try ac_rfl))

private theorem mul_eqv_congr₂ {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ (a' * b) _
    (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

private theorem qpow_two_eqv_mul (x : Q') :
    RingNormaliser.qpow x 2 ≈ x * x := by
  change ((1 : Q') * x) * x ≈ x * x
  exact Q'.mul_eqv_congr_right _ _ x (Q'.one_mul_eqv x)

private theorem ofNat_sub_eqv (a b : Nat) (h : b ≤ a) :
    Q'.ofNat (a - b) ≈ Q'.ofNat a + -(Q'.ofNat b) := by
  change (Int.ofNat (a - b)) * 1 =
    (Int.ofNat a * 1 + (-Int.ofNat b) * 1) * 1
  simp
  omega

private def tailBaseDNEnvironment (D N : Q') : Nat → Q'
  | 0 => D
  | 1 => N
  | _ => 0

private theorem eval_bivariatePowerExpr_swap (D N : Q') :
    ∀ terms : List (Nat × Nat × Int),
      RingNormaliser.eval (tailBaseRawEnvironment D N)
          (bivariatePowerExpr
            (terms.map (fun (d, n, coefficient) =>
              (n, d, coefficient)))) ≈
        RingNormaliser.eval (tailBaseDNEnvironment D N)
          (bivariatePowerExpr terms)
  | [] => Q'.eqv_refl 0
  | (d, n, coefficient) :: rest => by
      change
        Q'.ofInt coefficient *
              (RingNormaliser.qpow N n * RingNormaliser.qpow D d) +
            RingNormaliser.eval (tailBaseRawEnvironment D N)
              (bivariatePowerExpr
                (rest.map (fun (d, n, coefficient) =>
                  (n, d, coefficient)))) ≈
          Q'.ofInt coefficient *
              (RingNormaliser.qpow D d * RingNormaliser.qpow N n) +
            RingNormaliser.eval (tailBaseDNEnvironment D N)
              (bivariatePowerExpr rest)
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left (Q'.ofInt coefficient) _ _
          (Q'.mul_comm_eqv _ _))
        (eval_bivariatePowerExpr_swap D N rest)

/-- The locally swapped sparse L1 expression evaluates to the public cleared
next-slope polynomial. -/
theorem tailBaseL1ClearedExpr_eval (D N : Q') :
    RingNormaliser.eval (tailBaseRawEnvironment D N)
        tailBaseL1ClearedExpr ≈
      lowerSixTailNextSlopeFloorCleared D N := by
  unfold lowerSixTailNextSlopeFloorCleared
  change
    RingNormaliser.eval (tailBaseRawEnvironment D N)
        (bivariatePowerExpr
          (lowerSixTailNextSlopeFloorClearedTerms.map
            (fun (d, n, coefficient) => (n, d, coefficient)))) ≈
      RingNormaliser.eval (tailBaseDNEnvironment D N)
        (bivariatePowerExpr lowerSixTailNextSlopeFloorClearedTerms)
  exact eval_bivariatePowerExpr_swap D N
    lowerSixTailNextSlopeFloorClearedTerms

private theorem tailBase_den_mul_harmU (k : Nat) :
    Q'.ofNat (k + 2) * harmU k ≈ (1 : Q') := by
  exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (tail_harmU_mul_den k)

/-- The public ninth-order Taylor clearing at the old physical denominator. -/
theorem tailBaseTaylor9Cleared_oldPower (k n : Nat) (hn : 4 ≤ n) :
    tailTaylor9Cleared (Q'.ofNat (k + 2)) (Q'.ofNat n) ≈
      (Q'.ofNat 362880 *
          RingNormaliser.qpow (Q'.ofNat (k + 2)) 9) *
        lowerSixTailOldPowerLower k n := by
  have h := tailTaylor9Cleared_physical_bridge
    (tailBase_den_mul_harmU k) n hn
  simpa [lowerSixTailOldPowerLower] using h

private theorem tailBase_nextDen_eqv (k : Nat) :
    Q'.ofNat (k + 2) + Q'.ofInt 1 ≈ Q'.ofNat (k + 3) := by
  simpa [show k + 2 + 1 = k + 3 by omega] using
    Q'.eqv_symm (Q'.ofNat_add_eqv (k + 2) 1)

private theorem tailBase_nextDen_mul_harmU (k : Nat) :
    (Q'.ofNat (k + 2) + Q'.ofInt 1) * harmU (k + 1) ≈
      (1 : Q') := by
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (tailBase_nextDen_eqv k))
    (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (by simpa [show k + 1 + 2 = k + 3 by omega] using
        tail_harmU_mul_den (k + 1)))

/-- Instantiated scaled physical bridge for the next-slope clearing. -/
theorem tailBaseSlopeFloorCleared_physical_scaled
    (k n : Nat) (hn : 4 ≤ n) :
    Q'.ofNat 144 *
        ((Q'.ofNat (k + 2) + Q'.ofInt 1) *
          lowerSixTailNextSlopeFloorCleared
            (Q'.ofNat (k + 2)) (Q'.ofNat n)) ≈
      (Q'.ofNat 362880 *
          RingNormaliser.qpow
            (Q'.ofNat (k + 2) + Q'.ofInt 1) 9) *
        lowerSixTailNextSlopeFloor k n := by
  have h := slopeFloorCleared_physical_bridge
    (tailBase_nextDen_mul_harmU k) n hn
  simpa [lowerSixTailNextSlopeFloor,
    lowerSixTailNextPowerUpper] using h

/-- Unscaled exact meaning of the next-slope integer clearing. -/
theorem tailBaseSlopeFloorCleared_physical
    (k n : Nat) (hn : 4 ≤ n) :
    lowerSixTailNextSlopeFloorCleared
        (Q'.ofNat (k + 2)) (Q'.ofNat n) ≈
      Q'.ofNat 2520 *
        RingNormaliser.qpow
          (Q'.ofNat (k + 2) + Q'.ofInt 1) 8 *
        lowerSixTailNextSlopeFloor k n := by
  let Dp := Q'.ofNat (k + 2) + Q'.ofInt 1
  let Lc := lowerSixTailNextSlopeFloorCleared
    (Q'.ofNat (k + 2)) (Q'.ofNat n)
  let L := lowerSixTailNextSlopeFloor k n
  have hbridge := tailBaseSlopeFloorCleared_physical_scaled k n hn
  have hpow : RingNormaliser.qpow Dp 9 ≈
      Dp * RingNormaliser.qpow Dp 8 := by
    have hadd := RingNormaliser.qpow_add Dp 1 8
    have hone : RingNormaliser.qpow Dp 1 ≈ Dp := by
      change (1 : Q') * Dp ≈ Dp
      exact Q'.one_mul_eqv Dp
    exact Q'.eqv_trans _ _ _ hadd
      (Q'.mul_eqv_congr_right _ _ (RingNormaliser.qpow Dp 8) hone)
  have htarget :
      (Q'.ofNat 144 * Dp) *
          (Q'.ofNat 2520 * RingNormaliser.qpow Dp 8 * L) ≈
        (Q'.ofNat 362880 * RingNormaliser.qpow Dp 9) * L := by
    refine Q'.eqv_trans _
      (Q'.ofNat 362880 *
        (Dp * RingNormaliser.qpow Dp 8) * L) _ ?_ ?_
    · semantic_ring
    · exact Q'.mul_eqv_congr_right _ _ L
        (Q'.mul_eqv_congr_left (Q'.ofNat 362880) _ _
          (Q'.eqv_symm hpow))
  have hscaled :
      (Q'.ofNat 144 * Dp) * Lc ≈
        (Q'.ofNat 144 * Dp) *
          (Q'.ofNat 2520 * RingNormaliser.qpow Dp 8 * L) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat 144) Dp Lc)
      (Q'.eqv_trans _ _ _ hbridge (Q'.eqv_symm htarget))
  have hDpos : (0 : Q') < Q'.ofNat (k + 2) := by
    rw [show k + 2 = (k + 1) + 1 by omega]
    exact Q'.ofNat_succ_pos (k + 1)
  have hDpPos : (0 : Q') < Dp := by
    dsimp only [Dp]
    exact Q'.add_pos hDpos (by decide)
  have hfactor : (0 : Q') < Q'.ofNat 144 * Dp :=
    Q'.mul_pos (by decide) hDpPos
  simpa only [Dp, Lc, L] using Q'.mul_left_cancel_of_pos hfactor hscaled

/-- The locally swapped L1 expression has its exact production value. -/
theorem tailBaseL1ClearedExpr_physical
    (k n : Nat) (hn : 4 ≤ n) :
    RingNormaliser.eval
        (tailBaseRawEnvironment (Q'.ofNat (k + 2)) (Q'.ofNat n))
        tailBaseL1ClearedExpr ≈
      Q'.ofNat 2520 *
        RingNormaliser.qpow
          (Q'.ofNat (k + 2) + Q'.ofInt 1) 8 *
        lowerSixTailNextSlopeFloor k n :=
  Q'.eqv_trans _ _ _
    (tailBaseL1ClearedExpr_eval (Q'.ofNat (k + 2)) (Q'.ofNat n))
    (tailBaseSlopeFloorCleared_physical k n hn)

/-! ## Old-slope clearing -/

private def tailBaseU0IdentityN : PE := .var 0
private def tailBaseU0IdentityD : PE := .var 1

private def tailBaseU0IdentityLeft : PE :=
  .mul (.const 16) tailBaseU0ClearedExpr

private def tailBaseU0IdentityRight : PE :=
  .add
    (.mul (.const 362880)
      (.mul tailBaseU0IdentityN (.pow tailBaseU0IdentityD 9)))
    (.neg
      (.mul (.add tailBaseU0IdentityN (.const 1))
        envelopeSemanticPrefix9))

private theorem tailBaseU0Identity_normal :
    fastNormalize tailBaseU0IdentityLeft =
      fastNormalize tailBaseU0IdentityRight := by
  rfl

/-- Exact meaning of the old-slope integer clearing. -/
theorem tailBaseU0ClearedExpr_physical
    (k n : Nat) (hn : 4 ≤ n) :
    RingNormaliser.eval
        (tailBaseRawEnvironment (Q'.ofNat (k + 2)) (Q'.ofNat n))
        tailBaseU0ClearedExpr ≈
      Q'.ofNat 22680 *
        RingNormaliser.qpow (Q'.ofNat (k + 2)) 9 *
        lowerSixTailOldSlopeCeiling k n := by
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat n
  let Uc := RingNormaliser.eval (tailBaseRawEnvironment D N)
    tailBaseU0ClearedExpr
  let U := lowerSixTailOldSlopeCeiling k n
  let T := lowerSixTailOldPowerLower k n
  have hid := eval_eqv_of_fastNormalize_eq tailBaseU0IdentityLeft
    tailBaseU0IdentityRight tailBaseU0Identity_normal
    (tailBaseRawEnvironment D N)
  have hprefix :
      RingNormaliser.eval (tailBaseRawEnvironment D N)
          envelopeSemanticPrefix9 ≈
        (Q'.ofNat 362880 * RingNormaliser.qpow D 9) * T := by
    exact Q'.eqv_trans _ _ _
      (by
        simpa only [D, N, tailBaseRawEnvironment, envelopeSemanticRho] using
          envelopeSemanticPrefix9_eval D N)
      (by simpa only [D, N, T] using tailBaseTaylor9Cleared_oldPower k n hn)
  have hscaled :
      Q'.ofNat 16 * Uc ≈
        Q'.ofNat 16 *
          (Q'.ofNat 22680 * RingNormaliser.qpow D 9 * U) := by
    refine Q'.eqv_trans _
      (Q'.ofNat 362880 * (N * RingNormaliser.qpow D 9) +
        -((N + Q'.ofInt 1) *
          RingNormaliser.eval (tailBaseRawEnvironment D N)
            envelopeSemanticPrefix9)) _ ?_ ?_
    · simpa only [tailBaseU0IdentityLeft, tailBaseU0IdentityRight,
        tailBaseU0IdentityN, tailBaseU0IdentityD, Uc,
        RingNormaliser.eval] using hid
    · refine Q'.eqv_trans _
        (Q'.ofNat 362880 * (N * RingNormaliser.qpow D 9) +
          -((N + Q'.ofInt 1) *
            ((Q'.ofNat 362880 * RingNormaliser.qpow D 9) * T))) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_left (N + Q'.ofInt 1) _ _ hprefix))
      · have hNsucc : Q'.ofNat (n + 1) ≈ N + Q'.ofInt 1 := by
          dsimp only [N]
          simpa only using Q'.ofNat_add_eqv n 1
        have hUalt : N + -((N + Q'.ofInt 1) * T) ≈ U := by
          dsimp only [U, T, N]
          unfold lowerSixTailOldSlopeCeiling
          exact Q'.add_eqv_congr_left _ _ _
            (Q'.neg_eqv_congr _ _
              (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hNsucc)))
        refine Q'.eqv_trans _
          (Q'.ofNat 16 *
            ((Q'.ofNat 22680 * RingNormaliser.qpow D 9) *
              (N + -((N + Q'.ofInt 1) * T)))) _ ?_ ?_
        · semantic_ring
        · exact Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_left _ _ _ hUalt)
  have hfactor : (0 : Q') < Q'.ofNat 16 := by decide
  simpa only [Uc, U, D] using Q'.mul_left_cancel_of_pos hfactor hscaled

/-! ## Remaining exact physical factors -/

/-- The polynomial `D^2 - 1` is the embedded natural drift denominator. -/
theorem tailBaseRExpr_physical (k n : Nat) :
    RingNormaliser.eval
        (tailBaseRawEnvironment (Q'.ofNat (k + 2)) (Q'.ofNat n))
        tailBaseRExpr ≈
      Q'.ofNat (driftDen k) := by
  let D := Q'.ofNat (k + 2)
  have hD2 : RingNormaliser.qpow D 2 ≈
      Q'.ofNat ((k + 2) * (k + 2)) :=
    Q'.eqv_trans _ _ _ (qpow_two_eqv_mul D)
      (Q'.eqv_symm
        (HeatKernelRGStep.ofNat_mul_eqv (k + 2) (k + 2)))
  have hsquarePos : 0 < (k + 2) * (k + 2) :=
    Nat.mul_pos (by omega) (by omega)
  have hsub := ofNat_sub_eqv ((k + 2) * (k + 2)) 1 hsquarePos
  change RingNormaliser.qpow D 2 + Q'.ofInt (-1) ≈
    Q'.ofNat (driftDen k)
  refine Q'.eqv_trans _
    (Q'.ofNat ((k + 2) * (k + 2)) + -(Q'.ofNat 1)) _ ?_ ?_
  · exact Q'.add_eqv_congr' hD2 (by decide)
  · unfold driftDen
    exact Q'.eqv_symm hsub

/-- Evaluation of the small structured `2FNUM` expression is the public
scaled drift factor. -/
theorem tailBaseTwoFExpr_eval (D N : Q') :
    RingNormaliser.eval (tailBaseRawEnvironment D N) tailBaseTwoFExpr ≈
      qDriftFactorScaled D N := by
  let R := RingNormaliser.qpow D 2 + Q'.ofInt (-1)
  let H := Q'.ofNat 2 * R + Q'.ofInt 1
  let N2 := RingNormaliser.qpow N 2
  change
    (Q'.ofNat 2 * RingNormaliser.qpow R 4 +
        Q'.ofNat 2 * (N2 * (H * RingNormaliser.qpow R 2))) +
        (N2 * (N2 + Q'.ofInt (-1))) * RingNormaliser.qpow H 2 ≈
      (Q'.ofNat 2 * RingNormaliser.qpow R 4 +
        (((Q'.ofNat 2 * N2) * H) * RingNormaliser.qpow R 2)) +
        (N2 * (N2 + -(1 : Q'))) * RingNormaliser.qpow H 2
  semantic_ring

/-- At physical integer inputs, `2FNUM` is exactly
`2 * (D^2-1)^4 * lowerSixQuadraticTaylorFactor`. -/
theorem tailBaseTwoFExpr_physical (k n : Nat) :
    RingNormaliser.eval
        (tailBaseRawEnvironment (Q'.ofNat (k + 2)) (Q'.ofNat n))
        tailBaseTwoFExpr ≈
      (Q'.ofNat 2 *
        RingNormaliser.qpow
          (RingNormaliser.eval
            (tailBaseRawEnvironment (Q'.ofNat (k + 2)) (Q'.ofNat n))
            tailBaseRExpr) 4) *
        lowerSixQuadraticTaylorFactor k n := by
  have hscaled := qDriftFactorScaled_eq_physical k n
  have hR := tailBaseRExpr_physical k n
  exact Q'.eqv_trans _ _ _
    (tailBaseTwoFExpr_eval (Q'.ofNat (k + 2)) (Q'.ofNat n))
    (Q'.eqv_trans _ _ _ hscaled
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
          (RingNormaliser.qpow_eqv_congr (Q'.eqv_symm hR) 4))))

/-- Clearing identity for the exact lower-six Dirichlet profile:
`D^3 * profile(k) = 12 D^2 + 1`. -/
theorem tailBaseDenCube_mul_profile (k : Nat) :
    RingNormaliser.qpow (Q'.ofNat (k + 2)) 3 *
        lowerSixDirichletProfile k ≈
      Q'.ofNat 12 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 2 +
        Q'.ofInt 1 := by
  let D := Q'.ofNat (k + 2)
  let u := harmU k
  have hDu : D * u ≈ (1 : Q') := tailBase_den_mul_harmU k
  have hD2 : RingNormaliser.qpow D 2 ≈ D * D :=
    qpow_two_eqv_mul D
  have hD3 : RingNormaliser.qpow D 3 ≈
      RingNormaliser.qpow D 2 * D := by
    have hadd := RingNormaliser.qpow_add D 2 1
    have hone : RingNormaliser.qpow D 1 ≈ D := by
      change (1 : Q') * D ≈ D
      exact Q'.one_mul_eqv D
    exact Q'.eqv_trans _ _ _ hadd
      (Q'.mul_eqv_congr_left (RingNormaliser.qpow D 2) _ _ hone)
  have hDuSq : RingNormaliser.qpow D 2 * (u * u) ≈ (1 : Q') := by
    refine Q'.eqv_trans _ ((D * D) * (u * u)) _
      (Q'.mul_eqv_congr_right _ _ (u * u) hD2) ?_
    refine Q'.eqv_trans _ ((D * u) * (D * u)) _ (by semantic_ring) ?_
    exact Q'.eqv_trans _ ((1 : Q') * 1) _
      (mul_eqv_congr₂ hDu hDu) (Q'.one_mul_eqv 1)
  unfold lowerSixDirichletProfile
  dsimp only [D, u] at hDu hD2 hD3 hDuSq ⊢
  refine Q'.eqv_trans _
    ((RingNormaliser.qpow (Q'.ofNat (k + 2)) 2 *
        Q'.ofNat (k + 2)) *
      (harmU k *
        (Q'.ofNat 12 + harmU k * harmU k))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hD3
  refine Q'.eqv_trans _
    (RingNormaliser.qpow (Q'.ofNat (k + 2)) 2 *
      ((Q'.ofNat (k + 2) * harmU k) *
        (Q'.ofNat 12 + harmU k * harmU k))) _ (by semantic_ring) ?_
  refine Q'.eqv_trans _
    (RingNormaliser.qpow (Q'.ofNat (k + 2)) 2 *
      ((1 : Q') * (Q'.ofNat 12 + harmU k * harmU k))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hDu)
  refine Q'.eqv_trans _
    (Q'.ofNat 12 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 2 +
      RingNormaliser.qpow (Q'.ofNat (k + 2)) 2 *
        (harmU k * harmU k)) _ (by semantic_ring) ?_
  exact Q'.add_eqv_congr_left _ _ _ hDuSq

/-- Shifted form of the profile clearing at denominator `D+1`. -/
theorem tailBaseNextDenCube_mul_profile (k : Nat) :
    RingNormaliser.qpow
          (Q'.ofNat (k + 2) + Q'.ofInt 1) 3 *
        lowerSixDirichletProfile (k + 1) ≈
      Q'.ofNat 12 *
          RingNormaliser.qpow
            (Q'.ofNat (k + 2) + Q'.ofInt 1) 2 +
        Q'.ofInt 1 := by
  let Dp := Q'.ofNat (k + 2) + Q'.ofInt 1
  let Dnext := Q'.ofNat (k + 3)
  have hDp : Dp ≈ Dnext := tailBase_nextDen_eqv k
  have hphysical := tailBaseDenCube_mul_profile (k + 1)
  have hleft :
      RingNormaliser.qpow Dp 3 * lowerSixDirichletProfile (k + 1) ≈
        RingNormaliser.qpow Dnext 3 *
          lowerSixDirichletProfile (k + 1) :=
    Q'.mul_eqv_congr_right _ _ _
      (RingNormaliser.qpow_eqv_congr hDp 3)
  have hright :
      Q'.ofNat 12 * RingNormaliser.qpow Dnext 2 + Q'.ofInt 1 ≈
        Q'.ofNat 12 * RingNormaliser.qpow Dp 2 + Q'.ofInt 1 :=
    Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 12) _ _
        (RingNormaliser.qpow_eqv_congr (Q'.eqv_symm hDp) 2))
  simpa only [Dp, Dnext, show k + 1 + 2 = k + 3 by omega] using
    Q'.eqv_trans _ _ _ hleft (Q'.eqv_trans _ _ _ hphysical hright)

/-- Evaluation of the non-carrier core of the Base envelope. -/
private def tailBaseCorePExpr : PE :=
  let N : PE := .var 0
  let D : PE := .var 1
  .add
    (.add
      (.add
        (.add
          (.neg (.mul (.const 15750) (.mul N (.pow D 4))))
          (.neg (.mul (.const 45560) (.mul (.pow N 3) (.pow D 3)))))
        (.mul (.const 10976) (.mul (.pow N 5) (.pow D 2))))
      (.neg (.mul (.const 30848) (.mul (.pow N 7) D))))
    (.neg (.mul (.const 4608) (.pow N 9)))

private def tailBaseCoreJExpr : PE :=
  let N : PE := .var 0
  let D : PE := .var 1
  .add
    (.add
      (.add
        (.add
          (.add
            (.add
              (.add
                (.add
                  (.add
                    (.mul (.const 192) (.mul N (.pow D 4)))
                    (.mul (.const 384) (.mul (.pow N 3) (.pow D 3))))
                  (.neg (.mul (.const 6) (.mul N (.pow D 3)))))
                (.neg (.mul (.const 384) (.mul (.pow N 5) (.pow D 2)))))
              (.mul (.const 576) (.mul (.pow N 4) (.pow D 2))))
            (.mul (.const 184) (.mul (.pow N 3) (.pow D 2))))
          (.mul (.const 224) (.mul (.pow N 5) D)))
        (.neg (.mul (.const 256) (.pow N 7))))
      (.mul (.const 576) (.pow N 6)))
    (.mul (.const 3) (.pow D 3))

private def tailBaseCoreStagedExpr : PE :=
  let D : PE := .var 1
  .add
    (.add (.neg tailBaseCorePExpr)
      (.mul (.const 15630) (.pow D 4)))
    (.mul (.const 60)
      (.mul (.pow D 2)
        (.add tailBaseCoreJExpr
          (.neg (.mul (.const 6) (.pow D 3))))))

private theorem tailBaseCoreExpr_staged :
    tailBaseCoreExpr = tailBaseCoreStagedExpr := by
  rfl

private theorem tailBaseCorePExpr_eval (D N : Q') :
    RingNormaliser.eval (tailBaseRawEnvironment D N) tailBaseCorePExpr ≈
      lowerSixHermiteSecondFluxPoly D N := by
  change
    -(Q'.ofNat 15750 * (N * RingNormaliser.qpow D 4)) +
      -(Q'.ofNat 45560 *
        (RingNormaliser.qpow N 3 * RingNormaliser.qpow D 3)) +
      Q'.ofNat 10976 *
        (RingNormaliser.qpow N 5 * RingNormaliser.qpow D 2) +
      -(Q'.ofNat 30848 * (RingNormaliser.qpow N 7 * D)) +
      -(Q'.ofNat 4608 * RingNormaliser.qpow N 9) ≈
      lowerSixHermiteSecondFluxPoly D N
  unfold lowerSixHermiteSecondFluxPoly
  semantic_ring

private theorem tailBaseCoreJExpr_eval (D N : Q') :
    RingNormaliser.eval (tailBaseRawEnvironment D N) tailBaseCoreJExpr ≈
      lowerSixDiscreteHermiteFluxPoly D N := by
  change
    Q'.ofNat 192 * (N * RingNormaliser.qpow D 4) +
      Q'.ofNat 384 *
        (RingNormaliser.qpow N 3 * RingNormaliser.qpow D 3) +
      -(Q'.ofNat 6 * (N * RingNormaliser.qpow D 3)) +
      -(Q'.ofNat 384 *
        (RingNormaliser.qpow N 5 * RingNormaliser.qpow D 2)) +
      Q'.ofNat 576 *
        (RingNormaliser.qpow N 4 * RingNormaliser.qpow D 2) +
      Q'.ofNat 184 *
        (RingNormaliser.qpow N 3 * RingNormaliser.qpow D 2) +
      Q'.ofNat 224 * (RingNormaliser.qpow N 5 * D) +
      -(Q'.ofNat 256 * RingNormaliser.qpow N 7) +
      Q'.ofNat 576 * RingNormaliser.qpow N 6 +
      Q'.ofNat 3 * RingNormaliser.qpow D 3 ≈
      lowerSixDiscreteHermiteFluxPoly D N
  unfold lowerSixDiscreteHermiteFluxPoly
  semantic_ring

theorem tailBaseCoreExpr_eval (D N : Q') :
    RingNormaliser.eval (tailBaseRawEnvironment D N) tailBaseCoreExpr ≈
      (-lowerSixHermiteSecondFluxPoly D N) +
        Q'.ofNat 15630 * RingNormaliser.qpow D 4 +
        Q'.ofNat 60 * RingNormaliser.qpow D 2 *
          (lowerSixDiscreteHermiteFluxPoly D N +
            -(Q'.ofNat 6 * RingNormaliser.qpow D 3)) := by
  rw [tailBaseCoreExpr_staged]
  change
    (-RingNormaliser.eval (tailBaseRawEnvironment D N)
          tailBaseCorePExpr) +
          Q'.ofNat 15630 * RingNormaliser.qpow D 4 +
          Q'.ofNat 60 *
            (RingNormaliser.qpow D 2 *
            (RingNormaliser.eval (tailBaseRawEnvironment D N)
                tailBaseCoreJExpr +
              -(Q'.ofNat 6 * RingNormaliser.qpow D 3))) ≈
      (-lowerSixHermiteSecondFluxPoly D N) +
        Q'.ofNat 15630 * RingNormaliser.qpow D 4 +
        Q'.ofNat 60 * RingNormaliser.qpow D 2 *
          (lowerSixDiscreteHermiteFluxPoly D N +
            -(Q'.ofNat 6 * RingNormaliser.qpow D 3))
  have hleft :
      (-RingNormaliser.eval (tailBaseRawEnvironment D N)
          tailBaseCorePExpr) +
          Q'.ofNat 15630 * RingNormaliser.qpow D 4 ≈
        (-lowerSixHermiteSecondFluxPoly D N) +
          Q'.ofNat 15630 * RingNormaliser.qpow D 4 :=
    Q'.add_eqv_congr_right _ _ _
      (Q'.neg_eqv_congr _ _ (tailBaseCorePExpr_eval D N))
  have hinner :
      RingNormaliser.eval (tailBaseRawEnvironment D N)
            tailBaseCoreJExpr +
          -(Q'.ofNat 6 * RingNormaliser.qpow D 3) ≈
        lowerSixDiscreteHermiteFluxPoly D N +
          -(Q'.ofNat 6 * RingNormaliser.qpow D 3) :=
    Q'.add_eqv_congr_right _ _ _ (tailBaseCoreJExpr_eval D N)
  have houter :
      Q'.ofNat 60 *
          (RingNormaliser.qpow D 2 *
            (RingNormaliser.eval (tailBaseRawEnvironment D N)
                tailBaseCoreJExpr +
              -(Q'.ofNat 6 * RingNormaliser.qpow D 3))) ≈
        (Q'.ofNat 60 * RingNormaliser.qpow D 2) *
          (lowerSixDiscreteHermiteFluxPoly D N +
            -(Q'.ofNat 6 * RingNormaliser.qpow D 3)) := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (Q'.ofNat 60) (RingNormaliser.qpow D 2) _))
      (Q'.mul_eqv_congr_left _ _ _ hinner)
  exact Q'.add_eqv_congr' hleft houter

/-- Evaluation of the common denominator expression. -/
theorem tailBaseDenExpr_eval (D N : Q') :
    RingNormaliser.eval (tailBaseRawEnvironment D N) tailBaseDenExpr ≈
      RingNormaliser.qpow D 18 *
        (RingNormaliser.qpow
            (RingNormaliser.qpow D 2 + Q'.ofInt (-1)) 4 *
          RingNormaliser.qpow (D + Q'.ofInt 1) 15) := by
  exact Q'.eqv_refl _

#print axioms tailBaseL1ClearedExpr_eval
#print axioms tailBaseTaylor9Cleared_oldPower
#print axioms tailBaseSlopeFloorCleared_physical_scaled
#print axioms tailBaseSlopeFloorCleared_physical
#print axioms tailBaseL1ClearedExpr_physical
#print axioms tailBaseU0ClearedExpr_physical
#print axioms tailBaseRExpr_physical
#print axioms tailBaseTwoFExpr_eval
#print axioms tailBaseTwoFExpr_physical
#print axioms tailBaseDenCube_mul_profile
#print axioms tailBaseNextDenCube_mul_profile
#print axioms tailBaseCoreExpr_eval
#print axioms tailBaseDenExpr_eval

end YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge
