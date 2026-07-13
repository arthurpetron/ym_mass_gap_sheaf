/-
All-scale crossing invariant for the cubic theta-window carrier.

The finite-band predecessor proves every cubic Abel prefix through `k = 47`.
The remaining all-scale problem cannot be attacked cellwise: the predecessor
also gives an exact counterexample to that transport.  This file instead
records the algebraic invariant behind a cumulative proof.  After clearing
the common harmonic denominator, the cubic root slope divided by its mode is
monotone.  Consequently its sign can cross at most once, which is the first
step toward showing that negative cubic cells form a terminal suffix and that
only endpoint prefix estimates need be paid.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFirstBand

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCrossing

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFirstBand
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem cubicCrossing_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "cubic_crossing_ring" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Q'.neg_den, cubicCrossing_neg_num_cast,
               Int.natCast_mul, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.neg_zero,
               Int.zero_mul, Int.mul_zero, Int.one_mul, Int.mul_one];
             try ac_rfl))

/-- Cubic power with a fixed association, used only for denominator
clearing. -/
def qcube (x : Q') : Q' := (x * x) * x

/-- Numerator obtained by multiplying the cubic root carrier by `D^3`:
`N D^3 - (N+1)(D-1)(D-N)^2`. -/
def thetaCubicSlopePolynomial (D N : Q') : Q' :=
  N * qcube D +
    -((N + 1) * ((D + -1) * ((D + -N) * (D + -N))))

/-- The exact positive reserve in the normalized-slope crossing identity. -/
def thetaCubicCrossReserve (D N : Q') : Q' :=
  (D + -1) *
    (D * D + (Q'.ofNat 2 * (N * (N + 1))) * (D + -(N + 1)))

private def slopePolyExpr
    (D N : RingNormaliser.PolyExpr) : RingNormaliser.PolyExpr :=
  let one := RingNormaliser.PolyExpr.const 1
  let cubeD := .mul (.mul D D) D
  let Np1 := .add N one
  let Dm1 := .add D (.neg one)
  let DmN := .add D (.neg N)
  .add (.mul N cubeD)
    (.neg (.mul Np1 (.mul Dm1 (.mul DmN DmN))))

private def cubicCrossingPolyL : RingNormaliser.PolyExpr :=
  let D := RingNormaliser.PolyExpr.var 0
  let N := RingNormaliser.PolyExpr.var 1
  let one := RingNormaliser.PolyExpr.const 1
  let Np1 := .add N one
  let Dm1 := .add D (.neg one)
  let DmNp1 := .add D (.neg Np1)
  let reserve := .mul Dm1
    (.add (.mul D D)
      (.mul (.mul (.const 2) (.mul N Np1)) DmNp1))
  .add (.mul Np1 (slopePolyExpr D N)) reserve

private def cubicCrossingPolyR : RingNormaliser.PolyExpr :=
  let D := RingNormaliser.PolyExpr.var 0
  let N := RingNormaliser.PolyExpr.var 1
  let one := RingNormaliser.PolyExpr.const 1
  .mul N (slopePolyExpr D (.add N one))

private theorem cubicCrossingPoly_normal :
    RingNormaliser.normalize cubicCrossingPolyL =
      RingNormaliser.normalize cubicCrossingPolyR := by
  decide

/-- Exact cleared identity:

`N S_D(N+1) - (N+1) S_D(N)
   = (D-1)(D^2 + 2N(N+1)(D-N-1))`.

No estimate is used here; this is the polynomial source of the one-crossing
invariant. -/
theorem thetaCubicSlopePolynomial_crossing (D N : Q') :
    (N + 1) * thetaCubicSlopePolynomial D N +
        thetaCubicCrossReserve D N ≈
      N * thetaCubicSlopePolynomial D (N + 1) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    cubicCrossingPolyL cubicCrossingPolyR cubicCrossingPoly_normal
    (fun
      | 0 => D
      | _ => N)
  simpa [cubicCrossingPolyL, cubicCrossingPolyR, slopePolyExpr,
    thetaCubicSlopePolynomial, thetaCubicCrossReserve, qcube,
    RingNormaliser.eval] using h

/-- The crossing reserve is nonnegative throughout the natural range
`1 ≤ D`, `0 ≤ N`, and `N+1 ≤ D`. -/
theorem thetaCubicCrossReserve_nonnegative {D N : Q'}
    (hD : (1 : Q') ≤ D) (hN : (0 : Q') ≤ N)
    (hND : N + 1 ≤ D) :
    (0 : Q') ≤ thetaCubicCrossReserve D N := by
  have hDm1 : (0 : Q') ≤ D + -1 := Q'.sub_nonneg_of_le hD
  have hD0 : (0 : Q') ≤ D :=
    Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1) hD
  have hNp1 : (0 : Q') ≤ N + 1 :=
    Q'.zero_le_add _ _ hN (by decide)
  have htail : (0 : Q') ≤ D + -(N + 1) :=
    Q'.sub_nonneg_of_le hND
  have hDsq : (0 : Q') ≤ D * D := Q'.mul_nonneg D D hD0 hD0
  have hNN : (0 : Q') ≤ N * (N + 1) :=
    Q'.mul_nonneg _ _ hN hNp1
  have htwoNN : (0 : Q') ≤ Q'.ofNat 2 * (N * (N + 1)) :=
    Q'.mul_nonneg _ _ (by decide) hNN
  have hcorr :
      (0 : Q') ≤ (Q'.ofNat 2 * (N * (N + 1))) * (D + -(N + 1)) :=
    Q'.mul_nonneg _ _ htwoNN htail
  have hinside := Q'.zero_le_add _ _ hDsq hcorr
  unfold thetaCubicCrossReserve
  exact Q'.mul_nonneg _ _ hDm1 hinside

/-- Cross-multiplied monotonicity of the normalized cleared cubic slope.
This form avoids division by `N(N+1)` and remains meaningful at `N = 0`. -/
theorem thetaCubicSlopePolynomial_normalized_mono {D N : Q'}
    (hD : (1 : Q') ≤ D) (hN : (0 : Q') ≤ N)
    (hND : N + 1 ≤ D) :
    (N + 1) * thetaCubicSlopePolynomial D N ≤
      N * thetaCubicSlopePolynomial D (N + 1) := by
  have hreserve := thetaCubicCrossReserve_nonnegative hD hN hND
  have hadd := Q'.add_le_self_of_nonneg
    ((N + 1) * thetaCubicSlopePolynomial D N)
    (thetaCubicCrossReserve D N) hreserve
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv (thetaCubicSlopePolynomial_crossing D N))

private def cubeThreeFactorPolyL : RingNormaliser.PolyExpr :=
  let D := RingNormaliser.PolyExpr.var 0
  let L := RingNormaliser.PolyExpr.var 1
  let W := RingNormaliser.PolyExpr.var 2
  .mul (.mul (.mul D D) D) (.mul (.mul L L) W)

private def cubeThreeFactorPolyR : RingNormaliser.PolyExpr :=
  let D := RingNormaliser.PolyExpr.var 0
  let L := RingNormaliser.PolyExpr.var 1
  let W := RingNormaliser.PolyExpr.var 2
  .mul (.mul D W) (.mul (.mul D L) (.mul D L))

private theorem cubeThreeFactorPoly_normal :
    RingNormaliser.normalize cubeThreeFactorPolyL =
      RingNormaliser.normalize cubeThreeFactorPolyR := by
  decide

private theorem cube_three_factor_regroup (D L W : Q') :
    qcube D * ((L * L) * W) ≈
      (D * W) * ((D * L) * (D * L)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    cubeThreeFactorPolyL cubeThreeFactorPolyR cubeThreeFactorPoly_normal
    (fun
      | 0 => D
      | 1 => L
      | _ => W)
  simpa [cubeThreeFactorPolyL, cubeThreeFactorPolyR, qcube,
    RingNormaliser.eval] using h

private def carrierScalePolyL : RingNormaliser.PolyExpr :=
  let N := RingNormaliser.PolyExpr.var 0
  let A := RingNormaliser.PolyExpr.var 1
  let C := RingNormaliser.PolyExpr.var 2
  .mul (.add N (.neg (.mul (.add N (.const 1)) A))) C

private def carrierScalePolyR : RingNormaliser.PolyExpr :=
  let N := RingNormaliser.PolyExpr.var 0
  let A := RingNormaliser.PolyExpr.var 1
  let C := RingNormaliser.PolyExpr.var 2
  .add (.mul N C)
    (.neg (.mul (.add N (.const 1)) (.mul C A)))

private theorem carrierScalePoly_normal :
    RingNormaliser.normalize carrierScalePolyL =
      RingNormaliser.normalize carrierScalePolyR := by
  decide

private theorem carrier_scale_rearrange (N A C : Q') :
    (N + -((N + 1) * A)) * C ≈
      N * C + -((N + 1) * (C * A)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    carrierScalePolyL carrierScalePolyR carrierScalePoly_normal
    (fun
      | 0 => N
      | 1 => A
      | _ => C)
  simpa [carrierScalePolyL, carrierScalePolyR,
    RingNormaliser.eval] using h

/-- The harmonic denominator clears the final Bernoulli factor exactly. -/
theorem harmonicDen_mul_harmW (k : Nat) :
    Q'.ofNat (k + 2) * harmW k ≈ Q'.ofNat (k + 2) + -1 := by
  unfold harmW harmU ReciprocalBernoulliUpper.oneSub
    SummableInverseSquare.unit
  cubic_crossing_ring <;> omega

/-- The same denominator clears each linear Bernoulli factor exactly. -/
theorem harmonicDen_mul_thetaLinearFactor (k n : Nat) :
    Q'.ofNat (k + 2) * thetaLinearBernoulliFactor (harmW k) n ≈
      Q'.ofNat (k + 2) + -Q'.ofNat n := by
  unfold thetaLinearBernoulliFactor harmW harmU
    ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit
  cubic_crossing_ring <;> simp only [Int.mul_comm] <;> omega

/-- Exact bridge from the actual cubic carrier to its cleared polynomial
model.  Thus the abstract crossing certificate above applies without an
approximation or an inferred normalization. -/
theorem thetaCubicRightCarrier_mul_denCube (k n : Nat) :
    thetaCubicRightCarrier k n * qcube (Q'.ofNat (k + 2)) ≈
      thetaCubicSlopePolynomial (Q'.ofNat (k + 2)) (Q'.ofNat n) := by
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat n
  let L := thetaLinearBernoulliFactor (harmW k) n
  let W := harmW k
  have hW : D * W ≈ D + -1 := harmonicDen_mul_harmW k
  have hL : D * L ≈ D + -N :=
    harmonicDen_mul_thetaLinearFactor k n
  have hsq : (D * L) * (D * L) ≈
      (D + -N) * (D + -N) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (D * L) hL) ?_
    exact Q'.mul_eqv_congr_left (D + -N) _ _ hL
  have hscaled : qcube D * ((L * L) * W) ≈
      (D + -1) * ((D + -N) * (D + -N)) := by
    refine Q'.eqv_trans _ _ _ (cube_three_factor_regroup D L W) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ ((D * L) * (D * L)) hW) ?_
    exact Q'.mul_eqv_congr_left (D + -1) _ _ hsq
  have hrearrange := carrier_scale_rearrange N ((L * L) * W) (qcube D)
  have hstart :
      (N + -((N + 1) * ((L * L) * W))) * qcube D ≈
        N * qcube D + -((N + 1) *
          ((D + -1) * ((D + -N) * (D + -N)))) := by
    refine Q'.eqv_trans _ _ _ hrearrange ?_
    exact Q'.add_eqv_congr_left (N * qcube D) _ _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left (N + 1) _ _ hscaled))
  have hNp1 : Q'.ofNat (n + 1) ≈ N + 1 := by
    dsimp only [N]
    exact Q'.ofNat_add_eqv n 1
  have hcarrier : thetaCubicRightCarrier k n ≈
      N + -((N + 1) * ((L * L) * W)) := by
    unfold thetaCubicRightCarrier thetaThreeFactorLower
    dsimp only [N, L, W]
    exact Q'.add_eqv_congr_left (Q'.ofNat n) _ _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _
          ((thetaLinearBernoulliFactor (harmW k) n *
            thetaLinearBernoulliFactor (harmW k) n) * harmW k) hNp1))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (qcube D) hcarrier) ?_
  refine Q'.eqv_trans _ _ _ hstart ?_
  dsimp only [D, N, L, W]
  unfold thetaCubicSlopePolynomial
  exact Q'.eqv_refl _

#print axioms qcube
#print axioms thetaCubicSlopePolynomial
#print axioms thetaCubicCrossReserve
#print axioms thetaCubicSlopePolynomial_crossing
#print axioms thetaCubicCrossReserve_nonnegative
#print axioms thetaCubicSlopePolynomial_normalized_mono
#print axioms harmonicDen_mul_harmW
#print axioms harmonicDen_mul_thetaLinearFactor
#print axioms thetaCubicRightCarrier_mul_denCube

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCrossing
