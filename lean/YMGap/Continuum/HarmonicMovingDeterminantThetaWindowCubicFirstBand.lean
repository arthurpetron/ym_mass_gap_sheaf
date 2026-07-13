/-
First-band transport for the cubic theta-window carrier.

The predecessor establishes the three-factor Bernoulli upper bound for the
root slope, but its threshold audit is only the full six-cell prefix at
`k = 38`.  This file adds the missing order bridge: whenever the exact root
slope is nonnegative, the cubic carrier is a pointwise lower bound for the
exact Abel carrier.  It then checks every prefix, uniformly as a statement,
through the complete first square-root band `38 <= k <= 47` (the band on
which the window center is nine).

The finite band is deliberately not presented as an all-scale proof.  Its
remaining residual is the symbolic polynomial prefix estimate after the
integer square-root center changes.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFirstBand

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCentral
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCumulative
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

/-- The unweighted cubic lower carrier at a central-window offset. -/
def thetaCubicCentralCarrier (k j : Nat) : Q' :=
  let n := thetaWindowLeft k + j
  sevenDirichletProfile k * Q'.ofNat (n * n) +
    -(Q'.ofNat 4 *
      (thetaCubicRightCarrier k n * thetaCubicRightCarrier k n))

/-- Inclusive Abel prefix of the cubic lower carrier. -/
def thetaCubicAbelPrefix (k p : Nat) : Q' :=
  abelPrefix (thetaCubicCentralCarrier k) p

/-- The cubic carrier lies below the exact central carrier as soon as the
exact root slope is nonnegative.  This is the square-order bridge absent from
the threshold-only audit. -/
theorem thetaCubicCentralCarrier_le_exact {k j : Nat}
    (hk : 38 ≤ k)
    (hn : thetaWindowLeft k + j ≤ thetaWindowCenter k)
    (hroot : (0 : Q') ≤ thetaRootSlope k (thetaWindowLeft k + j)) :
    thetaCubicCentralCarrier k j ≤ thetaCentralCarrier k j := by
  let n := thetaWindowLeft k + j
  have hslope : thetaRootSlope k n ≤ thetaCubicRightCarrier k n :=
    thetaRootSlope_le_cubicCarrier_on_window hk hn
  have hcubic : (0 : Q') ≤ thetaCubicRightCarrier k n :=
    Q'.le_trans' _ _ _ hroot hslope
  have hsq :
      thetaRootSlope k n * thetaRootSlope k n ≤
        thetaCubicRightCarrier k n * thetaCubicRightCarrier k n :=
    Q'.mul_le_mul_of_nonneg hslope hslope hcubic hroot
  have hfour := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4) hsq (by decide)
  have hneg := Q'.neg_le_neg hfour
  dsimp only [thetaCubicCentralCarrier, thetaCentralCarrier, n]
  exact Q'.add_le_add_left
    (sevenDirichletProfile k *
      Q'.ofNat ((thetaWindowLeft k + j) * (thetaWindowLeft k + j)))
    _ _ hneg

/-- Prefix-level transport from the cubic lower carrier to the exact Abel
carrier.  Only nonnegativity of the exact root slopes in the prefix is needed
in addition to the predecessor's uniform cubic upper bound. -/
theorem thetaCentralAbelPrefix_nonnegative_of_cubic {k p : Nat}
    (hk : 38 ≤ k)
    (hp : p ≤ thetaWindowCenter k - thetaWindowLeft k)
    (hroot : ∀ j, j ≤ p →
      (0 : Q') ≤ thetaRootSlope k (thetaWindowLeft k + j))
    (hcubic : (0 : Q') ≤ thetaCubicAbelPrefix k p) :
    (0 : Q') ≤ thetaCentralAbelPrefix k p := by
  have hsum : thetaCubicAbelPrefix k p ≤ thetaCentralAbelPrefix k p := by
    unfold thetaCubicAbelPrefix thetaCentralAbelPrefix abelPrefix
    apply YMGap.Continuum.CubeRatioBounds.fsum_mono_lt
    intro j hj
    have hjp : j ≤ p := by omega
    have hleft : thetaWindowLeft k ≤ thetaWindowCenter k := by
      unfold thetaWindowLeft
      exact Nat.div_le_self _ 2
    have hn : thetaWindowLeft k + j ≤ thetaWindowCenter k := by
      omega
    exact thetaCubicCentralCarrier_le_exact hk hn (hroot j hjp)
  exact Q'.le_trans' _ _ _ hcubic hsum

/-- The integer-square-root center is constant on the first complete band. -/
theorem thetaWindowCenter_eq_nine_firstBand {k : Nat}
    (hk0 : 38 ≤ k) (hk1 : k ≤ 47) :
    thetaWindowCenter k = 9 := by
  have hlo : 9 ≤ thetaWindowCenter k := thetaWindowCenter_ge_nine hk0
  have hsq : thetaWindowCenter k * thetaWindowCenter k ≤
      thetaWindowLength k := by
    unfold thetaWindowCenter
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hlen : thetaWindowLength k ≤ 99 := by
    unfold thetaWindowLength
    omega
  have hlt : thetaWindowCenter k < 10 := by
    rcases Nat.lt_or_ge (thetaWindowCenter k) 10 with h | h
    · exact h
    · have h100 : 100 ≤
          thetaWindowCenter k * thetaWindowCenter k := by
        exact Nat.mul_le_mul h h
      omega
  omega

theorem thetaWindowLeft_eq_four_firstBand {k : Nat}
    (hk0 : 38 ≤ k) (hk1 : k ≤ 47) :
    thetaWindowLeft k = 4 := by
  unfold thetaWindowLeft
  rw [thetaWindowCenter_eq_nine_firstBand hk0 hk1]

/-- All inclusive cubic-carrier prefixes are nonnegative on every scale in
the first complete square-root band, not only at `k = 38`. -/
theorem thetaCubicAbelPrefix_firstBand_nonnegative {k p : Nat}
    (hk0 : 38 ≤ k) (hk1 : k ≤ 47)
    (hp : p ≤ thetaWindowCenter k - thetaWindowLeft k) :
    (0 : Q') ≤ thetaCubicAbelPrefix k p := by
  have hc := thetaWindowCenter_eq_nine_firstBand hk0 hk1
  have hl := thetaWindowLeft_eq_four_firstBand hk0 hk1
  have hk : k = 38 ∨ k = 39 ∨ k = 40 ∨ k = 41 ∨ k = 42 ∨
      k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 := by
    omega
  have hp' : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := by
    omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold thetaCubicAbelPrefix abelPrefix thetaCubicCentralCarrier
      thetaCubicRightCarrier thetaThreeFactorLower thetaLinearBernoulliFactor
      sevenDirichletProfile thetaWindowLeft thetaWindowCenter thetaWindowLength
      harmW harmU ReciprocalBernoulliUpper.oneSub unit
      ChebOrthoMidpointEst.isqrt ChebOrthoMidpointEst.isqrtAux fsum <;>
    decide

/-- The sign-based pointwise transport cannot be applied blindly across the
whole first band: at `k = 42` the first cubic cell is not a lower bound for the
exact cell.  This exact fence forces any all-scale proof to retain cumulative
cancellation (or split the initial sign-changing cell). -/
theorem cubic_pointwise_transport_fails_k42_left :
    ¬ (thetaCubicCentralCarrier 42 0 ≤ thetaCentralCarrier 42 0) := by
  unfold thetaCubicCentralCarrier thetaCentralCarrier thetaCubicRightCarrier
    thetaThreeFactorLower thetaLinearBernoulliFactor thetaRootSlope
    sevenDirichletProfile thetaWindowLeft thetaWindowCenter thetaWindowLength
    harmW harmU ReciprocalBernoulliUpper.oneSub unit
    ChebOrthoMidpointEst.isqrt ChebOrthoMidpointEst.isqrtAux qpow
  decide

/-- Despite the pointwise fence, the exact cumulative Abel prefixes themselves
remain nonnegative on the entire first square-root band. -/
theorem thetaCentralAbelPrefix_firstBand_nonnegative {k p : Nat}
    (hk0 : 38 ≤ k) (hk1 : k ≤ 47)
    (hp : p ≤ thetaWindowCenter k - thetaWindowLeft k) :
    (0 : Q') ≤ thetaCentralAbelPrefix k p := by
  have hc := thetaWindowCenter_eq_nine_firstBand hk0 hk1
  have hl := thetaWindowLeft_eq_four_firstBand hk0 hk1
  have hk : k = 38 ∨ k = 39 ∨ k = 40 ∨ k = 41 ∨ k = 42 ∨
      k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 := by
    omega
  have hp' : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := by
    omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold thetaCentralAbelPrefix abelPrefix thetaCentralCarrier thetaRootSlope
      sevenDirichletProfile thetaWindowLeft thetaWindowCenter thetaWindowLength
      harmW harmU ReciprocalBernoulliUpper.oneSub unit
      ChebOrthoMidpointEst.isqrt ChebOrthoMidpointEst.isqrtAux fsum qpow <;>
    decide

/-- The exact central reserve is therefore nonnegative at every scale in the
first square-root band.  The unclosed part of the physical payment is now the
left/right-tail comparison, not the central Abel block. -/
theorem thetaProofCentralReserve_firstBand_nonnegative {k : Nat}
    (hk0 : 38 ≤ k) (hk1 : k ≤ 47) :
    (0 : Q') ≤ thetaProofCentralReserve k := by
  apply thetaProofCentralReserve_nonnegative_of_prefix
  intro p hp
  exact thetaCentralAbelPrefix_firstBand_nonnegative hk0 hk1 hp

#print axioms thetaCubicCentralCarrier
#print axioms thetaCubicAbelPrefix
#print axioms thetaCubicCentralCarrier_le_exact
#print axioms thetaCentralAbelPrefix_nonnegative_of_cubic
#print axioms thetaWindowCenter_eq_nine_firstBand
#print axioms thetaWindowLeft_eq_four_firstBand
#print axioms thetaCubicAbelPrefix_firstBand_nonnegative
#print axioms cubic_pointwise_transport_fails_k42_left
#print axioms thetaCentralAbelPrefix_firstBand_nonnegative
#print axioms thetaProofCentralReserve_firstBand_nonnegative

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFirstBand
