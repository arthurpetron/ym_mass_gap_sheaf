/-
Positive first Hermite flux on the physical left prefix.

The flux polynomial is regrouped into factors of `D-N^2` and
`D^2-N^4`.  On the square-root prefix with `N=n+1`, both are nonnegative,
so the flux-square substitution in the seventh-order carrier is order-safe.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticSquareWindow

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticFluxSign

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow

local infix:50 " ≈ " => Q'.eqv

private theorem ringQpow_nonnegative {a : Q'} (ha : (0 : Q') ≤ a) :
    ∀ n, (0 : Q') ≤ RingNormaliser.qpow a n
  | 0 => by
      show (0 : Q') ≤ (1 : Q')
      decide
  | n + 1 => Q'.mul_nonneg _ _ (ringQpow_nonnegative ha n) ha

private abbrev PE := RingNormaliser.PolyExpr

private def pPowFour : PE := .pow (.var 0) 4

private def pPowTwoSquare : PE :=
  .mul (.pow (.var 0) 2) (.pow (.var 0) 2)

private theorem pPowFour_normal :
    RingNormaliser.normalize pPowFour =
      RingNormaliser.normalize pPowTwoSquare := by decide

private theorem qpow_four_eqv_square_two (x : Q') :
    RingNormaliser.qpow x 4 ≈
      RingNormaliser.qpow x 2 * RingNormaliser.qpow x 2 := by
  simpa [pPowFour, pPowTwoSquare, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pPowFour pPowTwoSquare pPowFour_normal (fun _ => x))

private theorem ofNat_square_eqv_qpow_two (n : Nat) :
    Q'.ofNat (n * n) ≈ RingNormaliser.qpow (Q'.ofNat n) 2 := by
  refine Q'.eqv_trans _ (Q'.ofNat n * Q'.ofNat n) _
    (HeatKernelRGStep.ofNat_mul_eqv n n) ?_
  unfold RingNormaliser.qpow
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm (Q'.one_mul_eqv (Q'.ofNat n)))

private def pFluxPositiveDecomposition : PE :=
  let D : PE := .var 0
  let N : PE := .var 1
  let D2 := .pow D 2
  let D3 := .pow D 3
  let N2 := .pow N 2
  let N3 := .pow N 3
  let N4 := .pow N 4
  let N5 := .pow N 5
  let N6 := .pow N 6
  .add
    (.add
      (.add
        (.add
          (.add
            (.add
              (.mul (.mul (.mul (.const 6) N) D3)
                (.add (.mul (.const 32) D) (.neg (.const 1))))
              (.mul (.mul (.mul (.const 384) N3) D2)
                (.add D (.neg N2))))
            (.mul (.mul (.const 224) N5) (.add D (.neg N2))))
          (.mul (.mul (.const 32) N3) (.add D2 (.neg N4))))
        (.mul (.mul (.const 152) N3) D2))
      (.mul (.mul (.const 576) N4) D2))
    (.add (.mul (.const 576) N6) (.mul (.const 3) D3))

private def pFluxOriginal : PE :=
  let D : PE := .var 0
  let N : PE := .var 1
  let D2 := .pow D 2
  let D3 := .pow D 3
  let D4 := .pow D 4
  let N3 := .pow N 3
  let N4 := .pow N 4
  let N5 := .pow N 5
  let N6 := .pow N 6
  let N7 := .pow N 7
  .add
    (.add
      (.add
        (.add
          (.add
            (.add
              (.add
                (.add
                  (.add (.mul (.mul (.const 192) N) D4)
                    (.mul (.mul (.const 384) N3) D3))
                  (.neg (.mul (.mul (.const 6) N) D3)))
                (.neg (.mul (.mul (.const 384) N5) D2)))
              (.mul (.mul (.const 576) N4) D2))
            (.mul (.mul (.const 184) N3) D2))
          (.mul (.mul (.const 224) N5) D))
        (.neg (.mul (.const 256) N7)))
      (.mul (.const 576) N6))
    (.mul (.const 3) D3)

private theorem pFluxPositiveDecomposition_normal :
    RingNormaliser.normalize pFluxOriginal =
      RingNormaliser.normalize pFluxPositiveDecomposition := by decide

private theorem flux_positive_decomposition (D N : Q') :
    lowerSixDiscreteHermiteFluxPoly D N ≈
      let D2 := RingNormaliser.qpow D 2
      let D3 := RingNormaliser.qpow D 3
      let N2 := RingNormaliser.qpow N 2
      let N3 := RingNormaliser.qpow N 3
      let N4 := RingNormaliser.qpow N 4
      let N5 := RingNormaliser.qpow N 5
      let N6 := RingNormaliser.qpow N 6
      Q'.ofNat 6 * N * D3 * (Q'.ofNat 32 * D + -(1 : Q')) +
        Q'.ofNat 384 * N3 * D2 * (D + -N2) +
        Q'.ofNat 224 * N5 * (D + -N2) +
        Q'.ofNat 32 * N3 * (D2 + -N4) +
        Q'.ofNat 152 * N3 * D2 +
        Q'.ofNat 576 * N4 * D2 +
        (Q'.ofNat 576 * N6 + Q'.ofNat 3 * D3) := by
  simpa [pFluxOriginal, pFluxPositiveDecomposition,
    lowerSixDiscreteHermiteFluxPoly, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pFluxOriginal pFluxPositiveDecomposition
      pFluxPositiveDecomposition_normal (fun | 0 => D | _ => N))

private theorem next_index_sq_le_den
    {k n : Nat} (hk : 390 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    (n + 1) * (n + 1) ≤ k + 2 := by
  let c := thetaWindowCenter k
  let D := k + 2
  let N := n + 1
  have hc9 : 9 ≤ c := thetaWindowCenter_ge_nine (by omega)
  have h2n : 2 * n ≤ c := by
    dsimp only [c]
    unfold thetaWindowLeft at hn
    omega
  have h2N : 2 * N ≤ c + 2 := by
    dsimp only [N]
    omega
  have hsquare : (2 * N) * (2 * N) ≤ (c + 2) * (c + 2) :=
    Nat.mul_le_mul h2N h2N
  have hcsq : c * c ≤ 2 * D + 1 := by
    dsimp only [c, D, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have h6c : 6 * c ≤ c * c := by
    have h := Nat.mul_le_mul_right c (show 6 ≤ c by omega)
    simpa [Nat.mul_comm] using h
  have hmargin : 4 * c + 5 ≤ 2 * D := by omega
  have hright : (c + 2) * (c + 2) ≤ 4 * D := by
    have hexpand : (c + 2) * (c + 2) = c * c + 4 * c + 4 := by
      simp only [Nat.add_mul, Nat.mul_add]
      omega
    rw [hexpand]
    omega
  have hfour : 4 * (N * N) ≤ 4 * D := by
    calc
      4 * (N * N) = (2 * N) * (2 * N) := by ac_rfl
      _ ≤ (c + 2) * (c + 2) := hsquare
      _ ≤ 4 * D := hright
  have hcancel : N * N ≤ D :=
    Nat.le_of_mul_le_mul_left hfour (by decide)
  simpa only [N, D] using hcancel

/-- The outgoing first Hermite flux is nonnegative on the physical left
prefix. -/
theorem lowerSixDiscreteHermiteFluxPoly_next_nonnegative_large
    {k n : Nat} (hk : 390 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    (0 : Q') ≤ lowerSixDiscreteHermiteFluxPoly
      (Q'.ofNat (k + 2)) (Q'.ofNat (n + 1)) := by
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat (n + 1)
  let D2 := RingNormaliser.qpow D 2
  let D3 := RingNormaliser.qpow D 3
  let N2 := RingNormaliser.qpow N 2
  let N3 := RingNormaliser.qpow N 3
  let N4 := RingNormaliser.qpow N 4
  let N5 := RingNormaliser.qpow N 5
  let N6 := RingNormaliser.qpow N 6
  have hD0 : (0 : Q') ≤ D := HeatKernelRGStep.zero_le_ofNat _
  have hN0 : (0 : Q') ≤ N := HeatKernelRGStep.zero_le_ofNat _
  have hD2 : (0 : Q') ≤ D2 := ringQpow_nonnegative hD0 2
  have hD3 : (0 : Q') ≤ D3 := ringQpow_nonnegative hD0 3
  have hN2 : (0 : Q') ≤ N2 := ringQpow_nonnegative hN0 2
  have hN3 : (0 : Q') ≤ N3 := ringQpow_nonnegative hN0 3
  have hN4 : (0 : Q') ≤ N4 := ringQpow_nonnegative hN0 4
  have hN5 : (0 : Q') ≤ N5 := ringQpow_nonnegative hN0 5
  have hN6 : (0 : Q') ≤ N6 := ringQpow_nonnegative hN0 6
  have hnat := next_index_sq_le_den hk hn
  have hND : N2 ≤ D := by
    have hcast : Q'.ofNat ((n + 1) * (n + 1)) ≤ Q'.ofNat (k + 2) := by
      exact Q'.ofNat_le_ofNat hnat
    have heq := ofNat_square_eqv_qpow_two (n + 1)
    dsimp only [N2, N, D]
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq) hcast
  have hgap : (0 : Q') ≤ D + -N2 := Q'.sub_nonneg_of_le hND
  have hN4D2 : N4 ≤ D2 := by
    have hmul := Q'.mul_le_mul_of_nonneg hND hND hD0 hN2
    have hN4eq : N4 ≈ N2 * N2 := by
      dsimp only [N4, N2]
      exact qpow_four_eqv_square_two N
    have hD2eq : D2 ≈ D * D := by
      dsimp only [D2, RingNormaliser.qpow]
      exact Q'.mul_eqv_congr_right _ _ _
        (Q'.one_mul_eqv D)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hN4eq)
      (Q'.le_trans' _ _ _ hmul (Q'.ge_of_eqv hD2eq))
  have hgap2 : (0 : Q') ≤ D2 + -N4 := Q'.sub_nonneg_of_le hN4D2
  have h32 : (1 : Q') ≤ Q'.ofNat 32 * D := by
    have hnat32 : 1 ≤ 32 * (k + 2) := by omega
    have hcast : Q'.ofNat 1 ≤ Q'.ofNat (32 * (k + 2)) := by
      exact Q'.ofNat_le_ofNat hnat32
    have heq := HeatKernelRGStep.ofNat_mul_eqv 32 (k + 2)
    dsimp only [D]
    exact Q'.le_trans' _ _ _ hcast (Q'.le_of_eqv heq)
  have hfirst : (0 : Q') ≤ Q'.ofNat 32 * D + -(1 : Q') :=
    Q'.sub_nonneg_of_le h32
  have h0 : (0 : Q') ≤
      Q'.ofNat 6 * N * D3 * (Q'.ofNat 32 * D + -(1 : Q')) :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide) hN0) hD3) hfirst
  have h1 : (0 : Q') ≤ Q'.ofNat 384 * N3 * D2 * (D + -N2) :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide) hN3) hD2) hgap
  have h2 : (0 : Q') ≤ Q'.ofNat 224 * N5 * (D + -N2) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hN5) hgap
  have h3 : (0 : Q') ≤ Q'.ofNat 32 * N3 * (D2 + -N4) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hN3) hgap2
  have h4 : (0 : Q') ≤ Q'.ofNat 152 * N3 * D2 :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hN3) hD2
  have h5 : (0 : Q') ≤ Q'.ofNat 576 * N4 * D2 :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hN4) hD2
  have h6 : (0 : Q') ≤ Q'.ofNat 576 * N6 + Q'.ofNat 3 * D3 :=
    Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (by decide) hN6)
      (Q'.mul_nonneg _ _ (by decide) hD3)
  have hsum := Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.zero_le_add _ _
          (Q'.zero_le_add _ _
            (Q'.zero_le_add _ _ h0 h1) h2) h3) h4) h5) h6
  have heq := flux_positive_decomposition D N
  dsimp only [D, N, D2, D3, N2, N3, N4, N5, N6] at hsum heq ⊢
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv heq)

#print axioms lowerSixDiscreteHermiteFluxPoly_next_nonnegative_large

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticFluxSign
