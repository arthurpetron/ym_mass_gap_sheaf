/-
Exact normal form and a pairing fence for the lower-six quadratic drift
payment.  This scratch module is intentionally outside the production import
graph.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment

namespace YMGap.Continuum.ScratchLowerSixQuadraticPaymentMechanism

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftScaleStep
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossWindow
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowDifference
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem mechanism_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "mechanism_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               mechanism_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- The second-order Taylor factor retained at mode `n`. -/
def lowerSixQuadraticTaylorFactor (k n : Nat) : Q' :=
  lowerSixWeightDriftFloor k n + lowerSixWeightDriftQuadratic k n

/-- The one-mode cross-scale carrier after the linear and quadratic drift
payments are recombined. -/
def lowerSixQuadraticTaylorCarrier (k n : Nat) : Q' :=
  Q'.ofNat (k + 3) * lowerSixQuadraticTaylorFactor k n *
      lowerSixModeCarrier (k + 1) n +
    -(Q'.ofNat (k + 2) * lowerSixModeCarrier k n)

/-- Exact pointwise recombination: the separately introduced linear and
quadratic carriers are one Taylor carrier, with no inequality loss. -/
theorem linear_add_quadratic_eqv_taylorCarrier (k n : Nat) :
    lowerSixScaledLinearDriftCarrier k n +
        lowerSixScaledDriftQuadratic k n ≈
      lowerSixQuadraticTaylorCarrier k n := by
  unfold lowerSixScaledLinearDriftCarrier lowerSixScaledDriftQuadratic
    lowerSixQuadraticTaylorCarrier lowerSixQuadraticTaylorFactor
  mechanism_ring

/-- The old-weighted second-order Taylor suffix. -/
def lowerSixQuadraticTaylorSuffix (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixModeWeight k (thetaWindowRight k + 1 + j) *
      lowerSixQuadraticTaylorCarrier k
        (thetaWindowRight k + 1 + j))
    (growingAnchor k - thetaWindowRight k)

private theorem mechanism_finSum_eqv_congr (f g : Nat → Q') : ∀ N,
    (∀ j, j < N → f j ≈ g j) → finSum f N ≈ finSum g N
  | 0, _ => Q'.eqv_refl 0
  | N + 1, h => by
      rw [finSum_succ, finSum_succ]
      exact Q'.add_eqv_congr'
        (mechanism_finSum_eqv_congr f g N
          (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N))))
        (h N (Nat.lt_succ_self N))

/-- Exact sum-level normal form.  The target payment is therefore a single
signed finite sum: the exact prefix followed by the Taylor carriers. -/
theorem linearSuffix_add_quadraticSuffix_eqv_taylorSuffix (k : Nat) :
    lowerSixScaledLinearCrossWindowSuffix k +
        lowerSixScaledQuadraticCrossWindowSuffix k ≈
      lowerSixQuadraticTaylorSuffix k := by
  let N := growingAnchor k - thetaWindowRight k
  let W := fun j => lowerSixModeWeight k (thetaWindowRight k + 1 + j)
  let L := fun j => lowerSixScaledLinearDriftCarrier k
    (thetaWindowRight k + 1 + j)
  let Q := fun j => lowerSixScaledDriftQuadratic k
    (thetaWindowRight k + 1 + j)
  let T := fun j => lowerSixQuadraticTaylorCarrier k
    (thetaWindowRight k + 1 + j)
  have hterm : ∀ j, j < N →
      W j * L j + W j * Q j ≈ W j * T j := by
    intro j _
    refine Q'.eqv_trans _ (W j * (L j + Q j)) _ ?_ ?_
    · exact Q'.eqv_symm (Q'.mul_add_eqv (W j) (L j) (Q j))
    · exact Q'.mul_eqv_congr_left (W j) _ _
        (linear_add_quadratic_eqv_taylorCarrier k
          (thetaWindowRight k + 1 + j))
  have hsum := mechanism_finSum_eqv_congr
    (fun j => W j * L j + W j * Q j)
    (fun j => W j * T j) N hterm
  unfold lowerSixScaledLinearCrossWindowSuffix
    lowerSixScaledQuadraticCrossWindowSuffix
    lowerSixQuadraticTaylorSuffix
  dsimp only [N, W, L, Q, T] at hsum ⊢
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (RationalTail.finSum_add
        (fun j => lowerSixModeWeight k
          (thetaWindowRight k + 1 + j) *
            lowerSixScaledLinearDriftCarrier k
              (thetaWindowRight k + 1 + j))
        (fun j => lowerSixModeWeight k
          (thetaWindowRight k + 1 + j) *
            lowerSixScaledDriftQuadratic k
              (thetaWindowRight k + 1 + j))
        (growingAnchor k - thetaWindowRight k))) hsum

/-- The payment inequality follows exactly from nonnegativity of the unified
Taylor sum.  This is the useful target for any Abel or polynomial-clearing
argument. -/
theorem quadratic_payment_of_taylor_sum_nonnegative {k : Nat}
    (h : (0 : Q') ≤ lowerSixScaledCrossWindowPrefix k +
      lowerSixQuadraticTaylorSuffix k) :
    -lowerSixScaledLinearCrossPaymentResidual k ≤
      lowerSixScaledQuadraticCrossWindowSuffix k := by
  have hnormal :
      lowerSixScaledLinearCrossPaymentResidual k +
          lowerSixScaledQuadraticCrossWindowSuffix k ≈
        lowerSixScaledCrossWindowPrefix k +
          lowerSixQuadraticTaylorSuffix k := by
    unfold lowerSixScaledLinearCrossPaymentResidual
    exact Q'.eqv_trans _
      (lowerSixScaledCrossWindowPrefix k +
        (lowerSixScaledLinearCrossWindowSuffix k +
          lowerSixScaledQuadraticCrossWindowSuffix k)) _
      (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _
        (linearSuffix_add_quadraticSuffix_eqv_taylorSuffix k))
  have hsum : (0 : Q') ≤
      lowerSixScaledLinearCrossPaymentResidual k +
        lowerSixScaledQuadraticCrossWindowSuffix k :=
    Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.eqv_symm hnormal))
  have hcomm : (0 : Q') ≤
      lowerSixScaledQuadraticCrossWindowSuffix k +
        lowerSixScaledLinearCrossPaymentResidual k :=
    Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have hrewrite :
      lowerSixScaledQuadraticCrossWindowSuffix k +
          -(-lowerSixScaledLinearCrossPaymentResidual k) ≈
        lowerSixScaledQuadraticCrossWindowSuffix k +
          lowerSixScaledLinearCrossPaymentResidual k :=
    Q'.add_eqv_congr_left _ _ _
      (Q'.neg_neg_eqv (lowerSixScaledLinearCrossPaymentResidual k))
  have hsub : (0 : Q') ≤
      lowerSixScaledQuadraticCrossWindowSuffix k +
        -(-lowerSixScaledLinearCrossPaymentResidual k) :=
    Q'.le_trans' _ _ _ hcomm
      (Q'.le_of_eqv (Q'.eqv_symm hrewrite))
  exact Q'.le_of_sub_nonneg hsub

/-- A tempting cellwise strategy is false: at the first induction scale,
the first adverse prefix cell (mode 9) is not paid by the first quadratic
suffix cell (mode 28).  Thus the proof must preserve cumulative cancellation
before pairing against the quadratic block. -/
theorem first_aligned_quadratic_pair_fails_k247 :
    ¬ ((0 : Q') ≤
      lowerSixScaledCrossTerm 247 8 +
        lowerSixModeWeight 247 (thetaWindowRight 247 + 1) *
          lowerSixScaledDriftQuadratic 247
            (thetaWindowRight 247 + 1)) := by
  unfold lowerSixScaledCrossTerm lowerSixWeightedAbelTerm
    lowerSixAbelCarrier lowerSixAbelWeight lowerSixModeCarrier
    lowerSixModeWeight lowerSixDirichletProfile thetaRootSlope
    lowerSixScaledDriftQuadratic lowerSixWeightDriftQuadratic
    lowerSixQuadraticCoeff lowerSixDriftExcess thetaWindowRight
    thetaWindowCenter thetaWindowLength driftDen harmW harmU oneSub unit qpow
  decide

/-! ## Exact Hermite-flux skeleton of the uniform tail mechanism

Put `D = k+2`, `h = D^{-1/2}`, and `y = n h`.  Formal expansion of the
unified Taylor carrier has successive Gaussian-weighted density polynomials
`H0`, `h H1`, and `h^2 H2`.  The following are exact polynomial identities,
not analytic limit assertions.  They identify the cancellations that a
finite-`D` discrete-flux proof has to preserve. -/

def hermiteLeadingDensity (y : Q') : Q' :=
  Q'.ofNat 32 * RingNormaliser.qpow y 6 +
    -(Q'.ofNat 72 * RingNormaliser.qpow y 4) +
    Q'.ofNat 8 * RingNormaliser.qpow y 2 + 4

def hermiteLeadingFlux (y : Q') : Q' :=
  Q'.ofNat 8 * y + Q'.ofNat 16 * RingNormaliser.qpow y 3 +
    -(Q'.ofNat 16 * RingNormaliser.qpow y 5)

def hermiteLeadingFluxDerivative (y : Q') : Q' :=
  Q'.ofNat 8 + Q'.ofNat 48 * RingNormaliser.qpow y 2 +
    -(Q'.ofNat 80 * RingNormaliser.qpow y 4)

private abbrev PE := RingNormaliser.PolyExpr
private def pc (n : Int) : PE := .const n
private def pv : PE := .var 0
private def padd (a b : PE) : PE := .add a b
private def pmul (a b : PE) : PE := .mul a b
private def pneg (a : PE) : PE := .neg a
private def ppow (a : PE) (n : Nat) : PE := .pow a n

private def pHermiteLeadingDensity : PE :=
  padd (padd (padd
    (pmul (pc 32) (ppow pv 6))
    (pneg (pmul (pc 72) (ppow pv 4))))
    (pmul (pc 8) (ppow pv 2))) (pc 4)

private def pHermiteLeadingFlux : PE :=
  padd (padd (pmul (pc 8) pv)
    (pmul (pc 16) (ppow pv 3)))
    (pneg (pmul (pc 16) (ppow pv 5)))

private def pHermiteLeadingFluxDerivative : PE :=
  padd (padd (pc 8) (pmul (pc 48) (ppow pv 2)))
    (pneg (pmul (pc 80) (ppow pv 4)))

private def pHermiteLeadingL : PE :=
  pmul (pc 2) pHermiteLeadingDensity

private def pHermiteLeadingR : PE :=
  padd pHermiteLeadingFluxDerivative
    (pneg (pmul (pmul (pc 4) pv) pHermiteLeadingFlux))

private theorem pHermiteLeading_normal :
    RingNormaliser.normalize pHermiteLeadingL =
      RingNormaliser.normalize pHermiteLeadingR := by decide

/-- `2 H0` is the Gaussian-weighted formal derivative of the leading flux:
`2 H0 = flux' - 4 y flux`.  Hence its continuum Gaussian moment is exactly
zero; the finite proof should realize the corresponding discrete telescope. -/
theorem hermiteLeading_flux_identity (y : Q') :
    Q'.ofNat 2 * hermiteLeadingDensity y ≈
      hermiteLeadingFluxDerivative y +
        -(Q'.ofNat 4 * y * hermiteLeadingFlux y) := by
  simpa [pHermiteLeadingL, pHermiteLeadingR,
    pHermiteLeadingDensity, pHermiteLeadingFlux,
    pHermiteLeadingFluxDerivative, pc, pv, padd, pmul, pneg, ppow,
    hermiteLeadingDensity, hermiteLeadingFlux,
    hermiteLeadingFluxDerivative, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pHermiteLeadingL pHermiteLeadingR pHermiteLeading_normal
      (fun _ => y))

def hermiteFirstDensity (y : Q') : Q' :=
  -(Q'.ofNat 64 * RingNormaliser.qpow y 7) +
    Q'.ofNat 192 * RingNormaliser.qpow y 5 +
    -(Q'.ofNat 112 * RingNormaliser.qpow y 3)

def hermiteFirstFlux (y : Q') : Q' :=
  Q'.ofNat 16 * RingNormaliser.qpow y 6 +
    -(Q'.ofNat 24 * RingNormaliser.qpow y 4) +
    Q'.ofNat 4 * RingNormaliser.qpow y 2 + 2

def hermiteFirstFluxDerivative (y : Q') : Q' :=
  Q'.ofNat 96 * RingNormaliser.qpow y 5 +
    -(Q'.ofNat 96 * RingNormaliser.qpow y 3) +
    Q'.ofNat 8 * y

private def pHermiteFirstDensity : PE :=
  padd (padd
    (pneg (pmul (pc 64) (ppow pv 7)))
    (pmul (pc 192) (ppow pv 5)))
    (pneg (pmul (pc 112) (ppow pv 3)))

private def pHermiteFirstFlux : PE :=
  padd (padd (padd
    (pmul (pc 16) (ppow pv 6))
    (pneg (pmul (pc 24) (ppow pv 4))))
    (pmul (pc 4) (ppow pv 2))) (pc 2)

private def pHermiteFirstFluxDerivative : PE :=
  padd (padd
    (pmul (pc 96) (ppow pv 5))
    (pneg (pmul (pc 96) (ppow pv 3))))
    (pmul (pc 8) pv)

private def pHermiteFirstR : PE :=
  padd pHermiteFirstFluxDerivative
    (pneg (pmul (pmul (pc 4) pv) pHermiteFirstFlux))

private theorem pHermiteFirst_normal :
    RingNormaliser.normalize pHermiteFirstDensity =
      RingNormaliser.normalize pHermiteFirstR := by decide

/-- The first correction is another exact Gaussian flux.  Its half-line
integral is the boundary value `-2`, which is cancelled by the endpoint and
Euler half-cell contributions of the augmented first mode. -/
theorem hermiteFirst_flux_identity (y : Q') :
    hermiteFirstDensity y ≈
      hermiteFirstFluxDerivative y +
        -(Q'.ofNat 4 * y * hermiteFirstFlux y) := by
  simpa [pHermiteFirstDensity, pHermiteFirstR, pHermiteFirstFlux,
    pHermiteFirstFluxDerivative, pc, pv, padd, pmul, pneg, ppow,
    hermiteFirstDensity, hermiteFirstFlux,
    hermiteFirstFluxDerivative, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pHermiteFirstDensity pHermiteFirstR pHermiteFirst_normal
      (fun _ => y))

/-- Three times the second correction, cleared of its coefficient
denominator. -/
def hermiteSecondClearedDensity (y : Q') : Q' :=
  Q'.ofNat 1792 * RingNormaliser.qpow y 8 +
    -(Q'.ofNat 8192 * RingNormaliser.qpow y 6) +
    Q'.ofNat 9152 * RingNormaliser.qpow y 4 +
    -(Q'.ofNat 2112 * RingNormaliser.qpow y 2)

def hermiteSecondFlux (y : Q') : Q' :=
  -(Q'.ofNat 448 * RingNormaliser.qpow y 7) +
    Q'.ofNat 1264 * RingNormaliser.qpow y 5 +
    -(Q'.ofNat 708 * RingNormaliser.qpow y 3) +
    -(Q'.ofNat 3 * y)

def hermiteSecondFluxDerivative (y : Q') : Q' :=
  -(Q'.ofNat 3136 * RingNormaliser.qpow y 6) +
    Q'.ofNat 6320 * RingNormaliser.qpow y 4 +
    -(Q'.ofNat 2124 * RingNormaliser.qpow y 2) +
    -(Q'.ofNat 3)

private def pHermiteSecondDensity : PE :=
  padd (padd (padd
    (pmul (pc 1792) (ppow pv 8))
    (pneg (pmul (pc 8192) (ppow pv 6))))
    (pmul (pc 9152) (ppow pv 4)))
    (pneg (pmul (pc 2112) (ppow pv 2)))

private def pHermiteSecondFlux : PE :=
  padd (padd (padd
    (pneg (pmul (pc 448) (ppow pv 7)))
    (pmul (pc 1264) (ppow pv 5)))
    (pneg (pmul (pc 708) (ppow pv 3))))
    (pneg (pmul (pc 3) pv))

private def pHermiteSecondFluxDerivative : PE :=
  padd (padd (padd
    (pneg (pmul (pc 3136) (ppow pv 6)))
    (pmul (pc 6320) (ppow pv 4)))
    (pneg (pmul (pc 2124) (ppow pv 2))))
    (pneg (pc 3))

private def pHermiteSecondR : PE :=
  padd (padd (pc 3) pHermiteSecondFluxDerivative)
    (pneg (pmul (pmul (pc 4) pv) pHermiteSecondFlux))

private theorem pHermiteSecond_normal :
    RingNormaliser.normalize pHermiteSecondDensity =
      RingNormaliser.normalize pHermiteSecondR := by decide

/-- Load-bearing positive asymptotic residue: after multiplying the second
density by `24`, it is **three copies of the Gaussian mass** plus an exact
Gaussian flux.  Thus the uncancelled coefficient is `3/24 = 1/8`, explaining
the observed strict `D^{-1/2}` margin without importing a measured number. -/
theorem hermiteSecond_positive_mass_plus_flux_identity (y : Q') :
    hermiteSecondClearedDensity y ≈
      Q'.ofNat 3 + hermiteSecondFluxDerivative y +
        -(Q'.ofNat 4 * y * hermiteSecondFlux y) := by
  simpa [pHermiteSecondDensity, pHermiteSecondR, pHermiteSecondFlux,
    pHermiteSecondFluxDerivative, pc, pv, padd, pmul, pneg, ppow,
    hermiteSecondClearedDensity, hermiteSecondFlux,
    hermiteSecondFluxDerivative, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pHermiteSecondDensity pHermiteSecondR pHermiteSecond_normal
      (fun _ => y))

/-! ## Actual finite-`D` discrete flux

The modified Hermite flux below includes the forward-difference corrections
through order `D^{-1}`.  It is written after clearing the common denominator
`48 D^4`; hence every coefficient is integral. -/

/-- Cleared modified-Hermite flux polynomial.  If `D=k+2` and `N=n`, this is
`48 D^4` times
`4N + 8N^3/D - 8N^5/D^2 + 12N^4/D^2
 - (16/3)N^7/D^4 + (14/3)N^5/D^3 + (23/6)N^3/D^2
 - N/(8D) + 1/(16D) + 12N^6/D^4`. -/
def lowerSixDiscreteHermiteFluxPoly (D N : Q') : Q' :=
  let D2 := RingNormaliser.qpow D 2
  let D3 := RingNormaliser.qpow D 3
  let D4 := RingNormaliser.qpow D 4
  let N3 := RingNormaliser.qpow N 3
  let N4 := RingNormaliser.qpow N 4
  let N5 := RingNormaliser.qpow N 5
  let N6 := RingNormaliser.qpow N 6
  let N7 := RingNormaliser.qpow N 7
  Q'.ofNat 192 * N * D4 +
    Q'.ofNat 384 * N3 * D3 +
    -(Q'.ofNat 6 * N * D3) +
    -(Q'.ofNat 384 * N5 * D2) +
    Q'.ofNat 576 * N4 * D2 +
    Q'.ofNat 184 * N3 * D2 +
    Q'.ofNat 224 * N5 * D +
    -(Q'.ofNat 256 * N7) +
    Q'.ofNat 576 * N6 +
    Q'.ofNat 3 * D3

/-- Actual old-Gaussian-weighted discrete flux numerator. -/
def lowerSixDiscreteHermiteFluxNumerator (k n : Nat) : Q' :=
  lowerSixModeWeight k n *
    lowerSixDiscreteHermiteFluxPoly (Q'.ofNat (k + 2)) (Q'.ofNat n)

/-- One actual unified Taylor summand. -/
def lowerSixQuadraticTaylorWeightedTerm (k n : Nat) : Q' :=
  lowerSixModeWeight k n * lowerSixQuadraticTaylorCarrier k n

/-- The positive cleared `1/(8D)` Gaussian-mass term. -/
def lowerSixDiscreteHermiteMassNumerator (k n : Nat) : Q' :=
  Q'.ofNat 6 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3 *
    lowerSixModeWeight k n

/-- Exact finite-`D` remainder after subtracting the forward flux difference
and the positive Gaussian-mass term from `48 D^4` times the actual Taylor
summand.  Its sum, rather than its pointwise sign, is the remaining analytic
estimate. -/
def lowerSixDiscreteHermiteRemainder (k n : Nat) : Q' :=
  Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
      lowerSixQuadraticTaylorWeightedTerm k n +
    -(lowerSixDiscreteHermiteFluxNumerator k (n + 1) +
      -lowerSixDiscreteHermiteFluxNumerator k n) +
    -lowerSixDiscreteHermiteMassNumerator k n

private def pFiniteFluxL : PE := .var 0

private def pFiniteFluxR : PE :=
  .add (.add (.var 1) (.var 2))
    (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2)))

private theorem pFiniteFlux_normal :
    RingNormaliser.normalize pFiniteFluxL =
      RingNormaliser.normalize pFiniteFluxR := by decide

private theorem finite_flux_reassemble (A B C : Q') :
    A ≈ B + C + (A + -B + -C) := by
  simpa [pFiniteFluxL, pFiniteFluxR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pFiniteFluxL pFiniteFluxR pFiniteFlux_normal
      (fun | 0 => A | 1 => B | _ => C))

/-- Exact division-free finite-`D` Hermite-flux decomposition of the actual
unified Taylor term. -/
theorem lowerSixQuadraticTaylorWeightedTerm_finite_flux (k n : Nat) :
    Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
        lowerSixQuadraticTaylorWeightedTerm k n ≈
      (lowerSixDiscreteHermiteFluxNumerator k (n + 1) +
          -lowerSixDiscreteHermiteFluxNumerator k n) +
        lowerSixDiscreteHermiteMassNumerator k n +
        lowerSixDiscreteHermiteRemainder k n := by
  unfold lowerSixDiscreteHermiteRemainder
  exact finite_flux_reassemble _ _ _

private def pForwardDifferenceStepL : PE :=
  .add (.add (.var 0) (.neg (.var 1)))
    (.add (.var 2) (.neg (.var 0)))

private def pForwardDifferenceStepR : PE :=
  .add (.var 2) (.neg (.var 1))

private theorem pForwardDifferenceStep_normal :
    RingNormaliser.normalize pForwardDifferenceStepL =
      RingNormaliser.normalize pForwardDifferenceStepR := by decide

private theorem forwardDifference_step (x a b : Q') :
    (x + -a) + (b + -x) ≈ b + -a := by
  simpa [pForwardDifferenceStepL, pForwardDifferenceStepR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pForwardDifferenceStepL pForwardDifferenceStepR
      pForwardDifferenceStep_normal
      (fun | 0 => x | 1 => a | _ => b))

/-- Constructive finite forward-difference telescope over `Q'`. -/
private theorem mechanism_finSum_forwardDifference (F : Nat → Q') : ∀ N,
    finSum (fun j => F (j + 1) + -F j) N ≈ F N + -F 0
  | 0 => Q'.eqv_symm (Q'.add_neg_self_eqv (F 0))
  | N + 1 => by
      rw [finSum_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (mechanism_finSum_forwardDifference F N)) ?_
      exact forwardDifference_step (F N) (F 0) (F (N + 1))

/-- Summing the exact finite-`D` decomposition leaves only the two flux
endpoints, the positive Gaussian-mass sum, and the summed remainder.  The
summed remainder is therefore the sole interior analytic residual. -/
theorem lowerSixQuadraticTaylorWeightedFinSum_finite_flux (k N : Nat) :
    Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
        finSum (fun j => lowerSixQuadraticTaylorWeightedTerm k (j + 1)) N ≈
      (lowerSixDiscreteHermiteFluxNumerator k (N + 1) +
          -lowerSixDiscreteHermiteFluxNumerator k 1) +
        finSum (fun j => lowerSixDiscreteHermiteMassNumerator k (j + 1)) N +
        finSum (fun j => lowerSixDiscreteHermiteRemainder k (j + 1)) N := by
  let C := Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4
  let dF := fun j =>
    lowerSixDiscreteHermiteFluxNumerator k (j + 2) +
      -lowerSixDiscreteHermiteFluxNumerator k (j + 1)
  let M := fun j => lowerSixDiscreteHermiteMassNumerator k (j + 1)
  let R := fun j => lowerSixDiscreteHermiteRemainder k (j + 1)
  let T := fun j => lowerSixQuadraticTaylorWeightedTerm k (j + 1)
  have hpoint : ∀ j, C * T j ≈ (dF j + M j) + R j := by
    intro j
    dsimp only [C, T, dF, M, R]
    simpa [Nat.add_assoc] using
      (lowerSixQuadraticTaylorWeightedTerm_finite_flux k (j + 1))
  have hsum : finSum (fun j => C * T j) N ≈
      finSum (fun j => (dF j + M j) + R j) N :=
    RationalTail.finSum_eqv_congr _ _ hpoint N
  have hflux : finSum dF N ≈
      lowerSixDiscreteHermiteFluxNumerator k (N + 1) +
        -lowerSixDiscreteHermiteFluxNumerator k 1 := by
    simpa [dF, Nat.add_assoc] using
      (mechanism_finSum_forwardDifference
        (fun j => lowerSixDiscreteHermiteFluxNumerator k (j + 1)) N)
  have hdm : finSum (fun j => dF j + M j) N ≈
      finSum dF N + finSum M N :=
    RationalTail.finSum_add dF M N
  have hdm' : finSum (fun j => dF j + M j) N ≈
      (lowerSixDiscreteHermiteFluxNumerator k (N + 1) +
          -lowerSixDiscreteHermiteFluxNumerator k 1) + finSum M N :=
    Q'.eqv_trans _ _ _ hdm
      (Q'.add_eqv_congr_right _ _ _ hflux)
  dsimp only [C, T, dF, M, R] at hsum hdm' ⊢
  refine Q'.eqv_trans _ _ _
    (RationalTail.const_mul_finSum
      (fun j => lowerSixQuadraticTaylorWeightedTerm k (j + 1))
      (Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4) N) ?_
  refine Q'.eqv_trans _ _ _ hsum ?_
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_add
      (fun j =>
        (lowerSixDiscreteHermiteFluxNumerator k (j + 2) +
            -lowerSixDiscreteHermiteFluxNumerator k (j + 1)) +
          lowerSixDiscreteHermiteMassNumerator k (j + 1))
      (fun j => lowerSixDiscreteHermiteRemainder k (j + 1)) N) ?_
  exact Q'.add_eqv_congr_right _ _ _ hdm'

/-- Arbitrary-start form of the exact telescope, matching a physical suffix
or any later moment block without reindexing it back to mode one. -/
theorem lowerSixQuadraticTaylorWeightedFinSumFrom_finite_flux
    (k S N : Nat) :
    Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
        finSum (fun j => lowerSixQuadraticTaylorWeightedTerm k (S + j)) N ≈
      (lowerSixDiscreteHermiteFluxNumerator k (S + N) +
          -lowerSixDiscreteHermiteFluxNumerator k S) +
        finSum (fun j => lowerSixDiscreteHermiteMassNumerator k (S + j)) N +
        finSum (fun j => lowerSixDiscreteHermiteRemainder k (S + j)) N := by
  let C := Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4
  let dF := fun j =>
    lowerSixDiscreteHermiteFluxNumerator k (S + (j + 1)) +
      -lowerSixDiscreteHermiteFluxNumerator k (S + j)
  let M := fun j => lowerSixDiscreteHermiteMassNumerator k (S + j)
  let R := fun j => lowerSixDiscreteHermiteRemainder k (S + j)
  let T := fun j => lowerSixQuadraticTaylorWeightedTerm k (S + j)
  have hpoint : ∀ j, C * T j ≈ (dF j + M j) + R j := by
    intro j
    dsimp only [C, T, dF, M, R]
    simpa [Nat.add_assoc] using
      (lowerSixQuadraticTaylorWeightedTerm_finite_flux k (S + j))
  have hsum : finSum (fun j => C * T j) N ≈
      finSum (fun j => (dF j + M j) + R j) N :=
    RationalTail.finSum_eqv_congr _ _ hpoint N
  have hflux : finSum dF N ≈
      lowerSixDiscreteHermiteFluxNumerator k (S + N) +
        -lowerSixDiscreteHermiteFluxNumerator k S := by
    simpa [dF, Nat.add_assoc] using
      (mechanism_finSum_forwardDifference
        (fun j => lowerSixDiscreteHermiteFluxNumerator k (S + j)) N)
  have hdm : finSum (fun j => dF j + M j) N ≈
      finSum dF N + finSum M N :=
    RationalTail.finSum_add dF M N
  have hdm' : finSum (fun j => dF j + M j) N ≈
      (lowerSixDiscreteHermiteFluxNumerator k (S + N) +
          -lowerSixDiscreteHermiteFluxNumerator k S) + finSum M N :=
    Q'.eqv_trans _ _ _ hdm
      (Q'.add_eqv_congr_right _ _ _ hflux)
  dsimp only [C, T, dF, M, R] at hsum hdm' ⊢
  refine Q'.eqv_trans _ _ _
    (RationalTail.const_mul_finSum
      (fun j => lowerSixQuadraticTaylorWeightedTerm k (S + j))
      (Q'.ofNat 48 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4) N) ?_
  refine Q'.eqv_trans _ _ _ hsum ?_
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_add
      (fun j =>
        (lowerSixDiscreteHermiteFluxNumerator k (S + (j + 1)) +
            -lowerSixDiscreteHermiteFluxNumerator k (S + j)) +
          lowerSixDiscreteHermiteMassNumerator k (S + j))
      (fun j => lowerSixDiscreteHermiteRemainder k (S + j)) N) ?_
  exact Q'.add_eqv_congr_right _ _ _ hdm'

/-- The finite remainder is not pointwise nonnegative.  This closed fence
rules out discarding it cell by cell; the next estimate must sum it through
the same discrete flux/moment calculus. -/
theorem discreteHermiteRemainder_pointwise_nonnegative_fails_k247_n15 :
    ¬ ((0 : Q') ≤ lowerSixDiscreteHermiteRemainder 247 15) := by
  unfold lowerSixDiscreteHermiteRemainder
    lowerSixDiscreteHermiteMassNumerator
    lowerSixDiscreteHermiteFluxNumerator lowerSixDiscreteHermiteFluxPoly
    lowerSixQuadraticTaylorWeightedTerm lowerSixQuadraticTaylorCarrier
    lowerSixQuadraticTaylorFactor lowerSixWeightDriftFloor
    lowerSixWeightDriftQuadratic lowerSixQuadraticCoeff
    lowerSixDriftExcess lowerSixModeWeight lowerSixModeCarrier
    lowerSixDirichletProfile thetaRootSlope driftDen harmW harmU
    oneSub unit RingNormaliser.qpow qpow
  decide

#print axioms linear_add_quadratic_eqv_taylorCarrier
#print axioms linearSuffix_add_quadraticSuffix_eqv_taylorSuffix
#print axioms quadratic_payment_of_taylor_sum_nonnegative
#print axioms first_aligned_quadratic_pair_fails_k247
#print axioms hermiteLeading_flux_identity
#print axioms hermiteFirst_flux_identity
#print axioms hermiteSecond_positive_mass_plus_flux_identity
#print axioms lowerSixQuadraticTaylorWeightedTerm_finite_flux
#print axioms lowerSixQuadraticTaylorWeightedFinSum_finite_flux
#print axioms lowerSixQuadraticTaylorWeightedFinSumFrom_finite_flux
#print axioms discreteHermiteRemainder_pointwise_nonnegative_fails_k247_n15

end YMGap.Continuum.ScratchLowerSixQuadraticPaymentMechanism
