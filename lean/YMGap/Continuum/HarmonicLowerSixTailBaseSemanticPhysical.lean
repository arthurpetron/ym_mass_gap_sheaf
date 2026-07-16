/-
# Physical semantics of the frozen lower-six Base rows

This module is the stable endpoint of the Base certificate bridge.  It
combines the coefficient-row identity with the exact physical meanings of
the five structured factors.  All power and profile clearings are staged in
small congruence lemmas; the dense certificate is never re-expanded.
-/

import YMGap.Continuum.HarmonicLowerSixTailBasePhysicalFactors

namespace YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicLowerSixTailBaseCertificate
open YMGap.Continuum.HarmonicLowerSixTailBaseSemanticRows
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorSemantic
open YMGap.Continuum.HarmonicLowerSixTailSecondFluxLocalBound
open YMGap.Continuum.HarmonicLowerSixSecondFluxSign
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.RawGridSemanticTransport

local infix:50 " ≈ " => Q'.eqv

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

private theorem qpow_one_eqv (x : Q') :
    RingNormaliser.qpow x 1 ≈ x := by
  change (1 : Q') * x ≈ x
  exact Q'.one_mul_eqv x

private theorem qpow_two_eqv_mul (x : Q') :
    RingNormaliser.qpow x 2 ≈ x * x := by
  change ((1 : Q') * x) * x ≈ x * x
  exact Q'.mul_eqv_congr_right _ _ x (Q'.one_mul_eqv x)

private theorem qpow_eight_square_eqv_fifteen_mul (x : Q') :
    RingNormaliser.qpow x 8 * RingNormaliser.qpow x 8 ≈
      RingNormaliser.qpow x 15 * x := by
  have h88 : RingNormaliser.qpow x 16 ≈
      RingNormaliser.qpow x 8 * RingNormaliser.qpow x 8 := by
    simpa only using RingNormaliser.qpow_add x 8 8
  have h151 : RingNormaliser.qpow x 16 ≈
      RingNormaliser.qpow x 15 * RingNormaliser.qpow x 1 := by
    simpa only using RingNormaliser.qpow_add x 15 1
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm h88)
    (Q'.eqv_trans _ _ _ h151
      (Q'.mul_eqv_congr_left (RingNormaliser.qpow x 15) _ _
        (qpow_one_eqv x)))

private theorem qpow_nine_square_eqv_eighteen (x : Q') :
    RingNormaliser.qpow x 9 * RingNormaliser.qpow x 9 ≈
      RingNormaliser.qpow x 18 := by
  have h99 : RingNormaliser.qpow x 18 ≈
      RingNormaliser.qpow x 9 * RingNormaliser.qpow x 9 := by
    simpa only using RingNormaliser.qpow_add x 9 9
  exact Q'.eqv_symm h99

private theorem nextClearedSquare_algebra (x L : Q') :
    RingNormaliser.qpow
        (Q'.ofNat 2520 * RingNormaliser.qpow x 8 * L) 2 ≈
      (Q'.ofNat 2520 * Q'.ofNat 2520) *
        ((RingNormaliser.qpow x 15 * x) * (L * L)) := by
  refine Q'.eqv_trans _
    ((Q'.ofNat 2520 * RingNormaliser.qpow x 8 * L) *
      (Q'.ofNat 2520 * RingNormaliser.qpow x 8 * L)) _
      (qpow_two_eqv_mul _) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat 2520 * Q'.ofNat 2520) *
      ((RingNormaliser.qpow x 8 * RingNormaliser.qpow x 8) *
        (L * L))) _ (by semantic_ring) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_right _ _ (L * L)
      (qpow_eight_square_eqv_fifteen_mul x))

private theorem oldClearedSquare_algebra (D U : Q') :
    RingNormaliser.qpow
        (Q'.ofNat 22680 * RingNormaliser.qpow D 9 * U) 2 ≈
      (Q'.ofNat 22680 * Q'.ofNat 22680) *
        (RingNormaliser.qpow D 18 * (U * U)) := by
  refine Q'.eqv_trans _
    ((Q'.ofNat 22680 * RingNormaliser.qpow D 9 * U) *
      (Q'.ofNat 22680 * RingNormaliser.qpow D 9 * U)) _
      (qpow_two_eqv_mul _) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat 22680 * Q'.ofNat 22680) *
      ((RingNormaliser.qpow D 9 * RingNormaliser.qpow D 9) *
        (U * U))) _ (by semantic_ring) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_right _ _ (U * U)
      (qpow_nine_square_eqv_eighteen D))

private theorem nextProfileClearing_algebra
    (x profile : Q')
    (hprofile : RingNormaliser.qpow x 3 * profile ≈
      Q'.ofNat 12 * RingNormaliser.qpow x 2 + Q'.ofInt 1) :
    RingNormaliser.qpow x 13 *
        (Q'.ofNat 12 * RingNormaliser.qpow x 2 + Q'.ofInt 1) ≈
      (RingNormaliser.qpow x 15 * x) * profile := by
  have h133 : RingNormaliser.qpow x 13 * RingNormaliser.qpow x 3 ≈
      RingNormaliser.qpow x 15 * x := by
    have ha : RingNormaliser.qpow x 16 ≈
        RingNormaliser.qpow x 13 * RingNormaliser.qpow x 3 := by
      simpa only using RingNormaliser.qpow_add x 13 3
    have hb : RingNormaliser.qpow x 16 ≈
        RingNormaliser.qpow x 15 * RingNormaliser.qpow x 1 := by
      simpa only using RingNormaliser.qpow_add x 15 1
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm ha)
      (Q'.eqv_trans _ _ _ hb
        (Q'.mul_eqv_congr_left _ _ _ (qpow_one_eqv x)))
  refine Q'.eqv_trans _
    (RingNormaliser.qpow x 13 *
      (RingNormaliser.qpow x 3 * profile)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hprofile)
  refine Q'.eqv_trans _
    ((RingNormaliser.qpow x 13 * RingNormaliser.qpow x 3) * profile) _
      (by semantic_ring) ?_
  exact Q'.mul_eqv_congr_right _ _ profile h133

private theorem oldProfileClearing_algebra
    (D profile : Q')
    (hprofile : RingNormaliser.qpow D 3 * profile ≈
      Q'.ofNat 12 * RingNormaliser.qpow D 2 + Q'.ofInt 1) :
    D * ((Q'.ofNat 12 * RingNormaliser.qpow D 2 + Q'.ofInt 1) *
        RingNormaliser.qpow D 15) ≈
      RingNormaliser.qpow D 18 * (D * profile) := by
  have h315 : RingNormaliser.qpow D 3 * RingNormaliser.qpow D 15 ≈
      RingNormaliser.qpow D 18 := by
    exact Q'.eqv_symm (by
      simpa only using RingNormaliser.qpow_add D 3 15)
  refine Q'.eqv_trans _
    (D * ((RingNormaliser.qpow D 3 * profile) *
      RingNormaliser.qpow D 15)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left D _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hprofile))
  refine Q'.eqv_trans _
    ((RingNormaliser.qpow D 3 * RingNormaliser.qpow D 15) *
      (D * profile)) _ (by semantic_ring) ?_
  exact Q'.mul_eqv_congr_right _ _ (D * profile) h315

private theorem physicalModeSquare (n : Nat) :
    RingNormaliser.qpow (Q'.ofNat n) 2 ≈ Q'.ofNat (n * n) := by
  exact Q'.eqv_trans _ _ _ (qpow_two_eqv_mul (Q'.ofNat n))
    (Q'.eqv_symm
      (HeatKernelRGStep.ofNat_mul_eqv n n))

/-- The five structured factors evaluate to the exact common-denominator
clearing of the production Base expression. -/
theorem eval_tailBaseStructuredExpression_physical
    (k n : Nat) (hn : 4 ≤ n) :
    RingNormaliser.eval
        (tailBaseRawEnvironment (Q'.ofNat (k + 2)) (Q'.ofNat n))
        tailBaseStructuredExpression ≈
      (Q'.ofNat 178605 *
        envelopeSemanticDenominatorValue (Q'.ofNat (k + 2))) *
        lowerSixTailEnvelopeBase k n := by
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat n
  let rho := tailBaseRawEnvironment D N
  let Dp := D + Q'.ofInt 1
  let R := RingNormaliser.qpow D 2 + Q'.ofInt (-1)
  let R4 := RingNormaliser.qpow R 4
  let D2 := RingNormaliser.qpow D 2
  let D3 := RingNormaliser.qpow D 3
  let D4 := RingNormaliser.qpow D 4
  let D6 := RingNormaliser.qpow D 6
  let D9 := RingNormaliser.qpow D 9
  let D15 := RingNormaliser.qpow D 15
  let D18 := RingNormaliser.qpow D 18
  let Dp2 := RingNormaliser.qpow Dp 2
  let Dp8 := RingNormaliser.qpow Dp 8
  let Dp13 := RingNormaliser.qpow Dp 13
  let Dp15 := RingNormaliser.qpow Dp 15
  let den0 := D18 * (R4 * Dp15)
  let N2 := Q'.ofNat (n * n)
  let F := lowerSixQuadraticTaylorFactor k n
  let L := lowerSixTailNextSlopeFloor k n
  let U := lowerSixTailOldSlopeCeiling k n
  let profileNext := lowerSixDirichletProfile (k + 1)
  let profileOld := lowerSixDirichletProfile k
  let core :=
    (-lowerSixHermiteSecondFluxPoly D N) +
      Q'.ofNat 15630 * D4 +
      Q'.ofNat 60 * D2 *
        (lowerSixDiscreteHermiteFluxPoly D N +
          -(Q'.ofNat 6 * D3))
  let common := (Q'.ofNat 178605 * den0) * D6
  let carrier0 :=
    Dp * F * (Q'.ofNat 4 * (L * L) + -(profileNext * N2)) +
      -(D * (Q'.ofNat 4 * (U * U) + -(profileOld * N2)))
  let contribution1 := common *
    (Q'.ofNat 2880 * (Dp * F * (Q'.ofNat 4 * (L * L))))
  let contribution2 := common *
    (Q'.ofNat 2880 * (Dp * F * (-(profileNext * N2))))
  let contribution3 := common *
    (Q'.ofNat 2880 * (-(D * (Q'.ofNat 4 * (U * U)))))
  let contribution4 := common *
    (Q'.ofNat 2880 * (-(D * (-(profileOld * N2)))))

  have hcore : RingNormaliser.eval rho tailBaseCoreExpr ≈ core := by
    change
      RingNormaliser.eval (tailBaseRawEnvironment D N) tailBaseCoreExpr ≈
        (-lowerSixHermiteSecondFluxPoly D N) +
          Q'.ofNat 15630 * RingNormaliser.qpow D 4 +
          Q'.ofNat 60 * RingNormaliser.qpow D 2 *
            (lowerSixDiscreteHermiteFluxPoly D N +
              -(Q'.ofNat 6 * RingNormaliser.qpow D 3))
    exact tailBaseCoreExpr_eval D N
  have hden : RingNormaliser.eval rho tailBaseDenExpr ≈ den0 := by
    change
      RingNormaliser.eval (tailBaseRawEnvironment D N) tailBaseDenExpr ≈
        RingNormaliser.qpow D 18 *
          (RingNormaliser.qpow
              (RingNormaliser.qpow D 2 + Q'.ofInt (-1)) 4 *
            RingNormaliser.qpow (D + Q'.ofInt 1) 15)
    exact tailBaseDenExpr_eval D N
  have htwo : RingNormaliser.eval rho tailBaseTwoFExpr ≈
      (Q'.ofNat 2 * R4) * F := by
    have h0 := tailBaseTwoFExpr_physical k n
    have hR : RingNormaliser.eval rho tailBaseRExpr ≈ R := by
      dsimp only [rho, R, D, N]
      change
        RingNormaliser.qpow (Q'.ofNat (k + 2)) 2 + Q'.ofInt (-1) ≈
          RingNormaliser.qpow (Q'.ofNat (k + 2)) 2 + Q'.ofInt (-1)
      exact Q'.eqv_refl _
    exact Q'.eqv_trans _ _ _ h0
      (Q'.mul_eqv_congr_right _ _ F
        (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
          (RingNormaliser.qpow_eqv_congr hR 4)))
  have hL : RingNormaliser.eval rho tailBaseL1ClearedExpr ≈
      Q'.ofNat 2520 * Dp8 * L := by
    dsimp only [rho, Dp8, Dp, D, N, L]
    exact tailBaseL1ClearedExpr_physical k n hn
  have hU : RingNormaliser.eval rho tailBaseU0ClearedExpr ≈
      Q'.ofNat 22680 * D9 * U := by
    dsimp only [rho, D9, D, N, U]
    exact tailBaseU0ClearedExpr_physical k n hn
  have hN2 : RingNormaliser.qpow N 2 ≈ N2 := by
    dsimp only [N, N2]
    exact physicalModeSquare n
  have hnextProfile : Dp13 *
      (Q'.ofNat 12 * Dp2 + Q'.ofInt 1) ≈
        (Dp15 * Dp) * profileNext := by
    dsimp only [Dp13, Dp2, Dp15, profileNext]
    exact nextProfileClearing_algebra Dp
      (lowerSixDirichletProfile (k + 1))
      (tailBaseNextDenCube_mul_profile k)
  have holdProfile : D *
      ((Q'.ofNat 12 * D2 + Q'.ofInt 1) * D15) ≈
        D18 * (D * profileOld) := by
    dsimp only [D2, D15, D18, profileOld]
    exact oldProfileClearing_algebra D (lowerSixDirichletProfile k)
      (tailBaseDenCube_mul_profile k)
  have hLsquare : RingNormaliser.qpow
      (RingNormaliser.eval rho tailBaseL1ClearedExpr) 2 ≈
        (Q'.ofNat 2520 * Q'.ofNat 2520) *
          ((Dp15 * Dp) * (L * L)) := by
    exact Q'.eqv_trans _ _ _ (RingNormaliser.qpow_eqv_congr hL 2)
      (nextClearedSquare_algebra Dp L)
  have hUsquare : RingNormaliser.qpow
      (RingNormaliser.eval rho tailBaseU0ClearedExpr) 2 ≈
        (Q'.ofNat 22680 * Q'.ofNat 22680) *
          (D18 * (U * U)) := by
    exact Q'.eqv_trans _ _ _ (RingNormaliser.qpow_eqv_congr hU 2)
      (oldClearedSquare_algebra D U)

  have hpiece0 : RingNormaliser.eval rho tailBaseStructuredPiece0Expr ≈
      Q'.ofNat 178605 * (core * den0) := by
    change Q'.ofNat 178605 *
      (RingNormaliser.eval rho tailBaseCoreExpr *
        RingNormaliser.eval rho tailBaseDenExpr) ≈ _
    exact Q'.mul_eqv_congr_left _ _ _ (mul_eqv_congr₂ hcore hden)
  have hpiece1 : RingNormaliser.eval rho tailBaseStructuredPiece1Expr ≈
      contribution1 := by
    change Q'.ofNat 162 *
      (D18 *
        (RingNormaliser.eval rho tailBaseTwoFExpr *
          (RingNormaliser.qpow
            (RingNormaliser.eval rho tailBaseL1ClearedExpr) 2 * D6))) ≈ _
    refine Q'.eqv_trans _
      (Q'.ofNat 162 *
        (D18 *
          (((Q'.ofNat 2 * R4) * F) *
            (((Q'.ofNat 2520 * Q'.ofNat 2520) *
              ((Dp15 * Dp) * (L * L))) * D6)))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left D18 _ _
          (mul_eqv_congr₂ htwo
            (Q'.mul_eqv_congr_right _ _ D6 hLsquare)))
    · dsimp only [contribution1, common, den0]
      semantic_ring
  have hnextProfileD6 :
      (Q'.ofNat 12 * Dp2 + Q'.ofInt 1) * (Dp13 * D6) ≈
        (((Dp15 * Dp) * profileNext) * D6) := by
    refine Q'.eqv_trans _
      ((Dp13 * (Q'.ofNat 12 * Dp2 + Q'.ofInt 1)) * D6) _
        (by semantic_ring) ?_
    exact Q'.mul_eqv_congr_right _ _ D6 hnextProfile
  have hpiece2 : RingNormaliser.eval rho tailBaseStructuredPiece2Expr ≈
      contribution2 := by
    change
      -(Q'.ofNat 257191200 *
        (D18 *
          (RingNormaliser.eval rho tailBaseTwoFExpr *
            (RingNormaliser.qpow N 2 *
              ((Q'.ofNat 12 * Dp2 + Q'.ofInt 1) *
                (Dp13 * D6)))))) ≈ _
    refine Q'.eqv_trans _
      (-(Q'.ofNat 257191200 *
        (D18 *
          (((Q'.ofNat 2 * R4) * F) *
            (N2 * ((((Dp15 * Dp) * profileNext) * D6))))))) _ ?_ ?_
    · exact Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left D18 _ _
            (mul_eqv_congr₂ htwo
              (mul_eqv_congr₂ hN2 hnextProfileD6))))
    · dsimp only [contribution2, common, den0]
      semantic_ring
  have hpiece3 : RingNormaliser.eval rho tailBaseStructuredPiece3Expr ≈
      contribution3 := by
    change
      -(Q'.ofNat 4 *
        (D *
          (R4 *
            (Dp15 *
              (RingNormaliser.qpow
                (RingNormaliser.eval rho tailBaseU0ClearedExpr) 2 * D6))))) ≈ _
    refine Q'.eqv_trans _
      (-(Q'.ofNat 4 *
        (D *
          (R4 *
            (Dp15 *
              (((Q'.ofNat 22680 * Q'.ofNat 22680) *
                (D18 * (U * U))) * D6)))))) _ ?_ ?_
    · exact Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left D _ _
            (Q'.mul_eqv_congr_left R4 _ _
              (Q'.mul_eqv_congr_left Dp15 _ _
                (Q'.mul_eqv_congr_right _ _ D6 hUsquare)))))
    · dsimp only [contribution3, common, den0]
      semantic_ring
  have holdProfileD6 :
      D * ((Q'.ofNat 12 * D2 + Q'.ofInt 1) * (D15 * D6)) ≈
        (D18 * (D * profileOld)) * D6 := by
    refine Q'.eqv_trans _
      ((D * ((Q'.ofNat 12 * D2 + Q'.ofInt 1) * D15)) * D6) _
        (by semantic_ring) ?_
    exact Q'.mul_eqv_congr_right _ _ D6 holdProfile
  have hpiece4 : RingNormaliser.eval rho tailBaseStructuredPiece4Expr ≈
      contribution4 := by
    change
      Q'.ofNat 514382400 *
        (D *
          (R4 *
            (Dp15 *
              (RingNormaliser.qpow N 2 *
                ((Q'.ofNat 12 * D2 + Q'.ofInt 1) *
                  (D15 * D6)))))) ≈ _
    refine Q'.eqv_trans _
      (Q'.ofNat 514382400 *
        (R4 *
          (Dp15 *
            (N2 * ((D18 * (D * profileOld)) * D6))))) _ ?_ ?_
    · refine Q'.eqv_trans _
        (Q'.ofNat 514382400 *
          (R4 *
            (Dp15 *
              (RingNormaliser.qpow N 2 *
                (D * ((Q'.ofNat 12 * D2 + Q'.ofInt 1) *
                  (D15 * D6))))))) _ (by semantic_ring) ?_
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left R4 _ _
          (Q'.mul_eqv_congr_left Dp15 _ _
            (mul_eqv_congr₂ hN2 holdProfileD6)))
    · dsimp only [contribution4, common, den0]
      semantic_ring

  have hsplit : RingNormaliser.eval rho tailBaseStructuredExpression ≈
      RingNormaliser.eval rho tailBaseStructuredPiece0Expr +
        (RingNormaliser.eval rho tailBaseStructuredPiece1Expr +
          (RingNormaliser.eval rho tailBaseStructuredPiece2Expr +
            (RingNormaliser.eval rho tailBaseStructuredPiece3Expr +
              RingNormaliser.eval rho tailBaseStructuredPiece4Expr))) := by
    exact Q'.eqv_refl _
  have hpieces : RingNormaliser.eval rho tailBaseStructuredExpression ≈
      Q'.ofNat 178605 * (core * den0) +
        (contribution1 + (contribution2 + (contribution3 + contribution4))) :=
    Q'.eqv_trans _ _ _ hsplit
      (Q'.add_eqv_congr' hpiece0
        (Q'.add_eqv_congr' hpiece1
          (Q'.add_eqv_congr' hpiece2
            (Q'.add_eqv_congr' hpiece3 hpiece4))))
  have hcarrierSum :
      contribution1 + (contribution2 + (contribution3 + contribution4)) ≈
        common * (Q'.ofNat 2880 * carrier0) := by
    dsimp only [contribution1, contribution2, contribution3, contribution4,
      carrier0]
    semantic_ring
  have hDpNext : Dp ≈ Q'.ofNat (k + 3) := by
    dsimp only [Dp, D]
    simpa only [show k + 2 + 1 = k + 3 by omega] using
      Q'.eqv_symm (Q'.ofNat_add_eqv (k + 2) 1)
  have hcarrier : carrier0 ≈ lowerSixTailCarrierLower k n := by
    unfold lowerSixTailCarrierLower
    dsimp only [carrier0, D, N2, F, L, U, profileNext, profileOld]
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hDpNext))
  have hD6 : D6 ≈ D2 * D4 := by
    dsimp only [D6, D2, D4]
    simpa only using RingNormaliser.qpow_add D 2 4
  have hcontributions :
      contribution1 + (contribution2 + (contribution3 + contribution4)) ≈
        (Q'.ofNat 178605 * den0) *
          (Q'.ofNat 60 * D2 *
            (Q'.ofNat 48 * D4 * lowerSixTailCarrierLower k n)) := by
    refine Q'.eqv_trans _ _ _ hcarrierSum ?_
    refine Q'.eqv_trans _
      (common *
        (Q'.ofNat 2880 * lowerSixTailCarrierLower k n)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left common _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 2880) _ _ hcarrier)
    · refine Q'.eqv_trans _
        (((Q'.ofNat 178605 * den0) * (D2 * D4)) *
          (Q'.ofNat 2880 * lowerSixTailCarrierLower k n)) _ ?_ ?_
      · dsimp only [common]
        exact Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left (Q'.ofNat 178605 * den0) _ _ hD6)
      · semantic_ring
  have hbaseShape :
      core + Q'.ofNat 60 * D2 *
          (Q'.ofNat 48 * D4 * lowerSixTailCarrierLower k n) ≈
        lowerSixTailEnvelopeBase k n := by
    unfold lowerSixTailEnvelopeBase
    dsimp only [core, D, N, D2, D3, D4]
    semantic_ring
  have hden0 : den0 ≈ envelopeSemanticDenominatorValue D := by
    have hneg : Q'.ofInt (-1) ≈ -(1 : Q') := by decide
    have hone : Q'.ofInt 1 ≈ (1 : Q') := by decide
    unfold envelopeSemanticDenominatorValue envelopeSemanticCommonValue
    dsimp only [den0, D18, R4, R, Dp15, Dp]
    exact Q'.mul_eqv_congr_left _ _ _
      (mul_eqv_congr₂
        (RingNormaliser.qpow_eqv_congr
          (Q'.add_eqv_congr_left _ _ _ hneg) 4)
        (RingNormaliser.qpow_eqv_congr
          (Q'.add_eqv_congr_left D _ _ hone) 15))
  refine Q'.eqv_trans _
    (Q'.ofNat 178605 * (core * den0) +
      (Q'.ofNat 178605 * den0) *
        (Q'.ofNat 60 * D2 *
          (Q'.ofNat 48 * D4 * lowerSixTailCarrierLower k n))) _
      (Q'.eqv_trans _ _ _ hpieces
        (Q'.add_eqv_congr_left _ _ _ hcontributions)) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat 178605 * den0) *
      (core + Q'.ofNat 60 * D2 *
        (Q'.ofNat 48 * D4 * lowerSixTailCarrierLower k n))) _
      (by semantic_ring) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat 178605 * den0) * lowerSixTailEnvelopeBase k n) _
      (Q'.mul_eqv_congr_left _ _ _ hbaseShape) ?_
  dsimp only [D] at hden0 ⊢
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 178605) _ _ hden0)

/-- Stable row-level endpoint consumed by the production envelope closure. -/
theorem evalRawRows_tailBaseSemanticTotalRows_physical
    (k n : Nat) (hn : 4 ≤ n) :
    evalRawRows
        (tailBaseRawEnvironment (Q'.ofNat (k + 2)) (Q'.ofNat n))
        tailBaseSemanticTotalRows ≈
      (Q'.ofNat 178605 *
        envelopeSemanticDenominatorValue (Q'.ofNat (k + 2))) *
        lowerSixTailEnvelopeBase k n := by
  let rho := tailBaseRawEnvironment (Q'.ofNat (k + 2)) (Q'.ofNat n)
  have hraw := evalRaw_tailBaseRawPolynomial_rows rho
  have hstructured := evalRaw_tailBaseRawPolynomial_structuredExpression rho
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hraw)
    (Q'.eqv_trans _ _ _ hstructured
      (eval_tailBaseStructuredExpression_physical k n hn))

/-- Stable dense-certificate endpoint: the frozen diagonal evaluator has its
exact physical common-denominator meaning. -/
theorem tailBaseCleared_physical (k n : Nat) (hn : 4 ≤ n) :
    tailBaseCleared (Q'.ofNat (k + 2)) (Q'.ofNat n) ≈
      (Q'.ofNat 178605 *
        envelopeSemanticDenominatorValue (Q'.ofNat (k + 2))) *
        lowerSixTailEnvelopeBase k n := by
  exact Q'.eqv_trans _ _ _
    (tailBaseCleared_eqv_structuredExpression
      (Q'.ofNat (k + 2)) (Q'.ofNat n))
    (eval_tailBaseStructuredExpression_physical k n hn)

#print axioms eval_tailBaseStructuredExpression_physical
#print axioms evalRawRows_tailBaseSemanticTotalRows_physical
#print axioms tailBaseCleared_physical

end YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge
