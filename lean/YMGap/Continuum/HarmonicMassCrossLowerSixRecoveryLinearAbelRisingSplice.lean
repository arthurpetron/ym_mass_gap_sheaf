/-
# Exact rising-prefix coordinates for the cumulative linear Abel payment

The complementary increment has a certified falling suffix, but replacing the
carrier prefix there by one terminal scalar loses the small payment margin.
This module keeps the full prefix dependence.  It first proves exact closed
forms for the two quadratic-weighted finite geometric sums occurring in the
linear carrier.  Their combination gives a denominator-cleared formula for
every next-scale carrier prefix, with no division and no numerical input.

The final section splices any pointwise estimate in this sharp prefix
coordinate to the already-certified falling suffix.  Thus the remaining
post-bootstrap work is a single explicit numerator inequality rather than an
uncontrolled finite sum.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPrefixVariation

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelRisingSplice

set_option maxHeartbeats 500000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryDropCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelCumulativePayment
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelFluxLocation
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelFluxUnimodality
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPrefixVariation
open YMGap.Continuum.HarmonicMovingDeterminantThetaCross
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem rising_splice_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "rising_splice_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               rising_splice_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.natCast_mul,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private abbrev PE := RingNormaliser.PolyExpr
private def pc (n : Int) : PE := .const n
private def pv (n : Nat) : PE := .var n
private def pa (x y : PE) : PE := .add x y
private def pm (x y : PE) : PE := .mul x y
private def pn (x : PE) : PE := .neg x
private def pp (x : PE) (n : Nat) : PE := .pow x n

private def pOneSubCube : PE :=
  pp (pa (pc 1) (pn (pv 0))) 3

/- Variables are `r = v0`, `q = v1`, and `z = v2`. -/
private def pSquareBoundaryAt (r q : PE) : PE :=
  let q2 := pm q q
  let twoq2 := pm (pc 2) q2
  let twoq := pm (pc 2) q
  let leading := pm (pa q (pc 1)) (pa q (pc 1))
  let middle := pm (pa (pc 1) (pn (pa twoq2 twoq))) r
  let trailing := pm q2 (pm r r)
  pa (pa leading middle) trailing

private def pSquareBoundary : PE :=
  pSquareBoundaryAt (pv 0) (pv 1)

private def pSquareNumeratorAt (r q z : PE) : PE :=
  pa (pa (pc 1) r) (pn (pm z (pSquareBoundaryAt r q)))

private def pSquareNumerator : PE :=
  pSquareNumeratorAt (pv 0) (pv 1) (pv 2)

private def pAdjacentBoundaryAt (r q : PE) : PE :=
  pa (pa
      (pm (pa q (pc 1)) (pa q (pc 2)))
      (pn (pm (pm (pm (pc 2) q) (pa q (pc 2))) r)))
    (pm (pm q (pa q (pc 1))) (pm r r))

private def pAdjacentBoundary : PE :=
  pAdjacentBoundaryAt (pv 0) (pv 1)

private def pAdjacentNumeratorAt (r q z : PE) : PE :=
  pa (pc 2) (pn (pm z (pAdjacentBoundaryAt r q)))

private def pAdjacentNumerator : PE :=
  pAdjacentNumeratorAt (pv 0) (pv 1) (pv 2)

private def pSquareStepL : PE :=
  let q := pv 1
  let z := pv 2
  pa pSquareNumerator
    (pm (pm (pm (pa q (pc 1)) (pa q (pc 1))) z) pOneSubCube)

private def pSquareStepR : PE :=
  let r := pv 0
  let q := pv 1
  let z := pv 2
  pSquareNumeratorAt r (pa q (pc 1)) (pm z r)

private def pAdjacentStepL : PE :=
  let q := pv 1
  let z := pv 2
  pa pAdjacentNumerator
    (pm (pm (pm (pa q (pc 1)) (pa q (pc 2))) z) pOneSubCube)

private def pAdjacentStepR : PE :=
  let r := pv 0
  let q := pv 1
  let z := pv 2
  pAdjacentNumeratorAt r (pa q (pc 1)) (pm z r)

private theorem pSquareStep_normal :
    RingNormaliser.normalize pSquareStepL =
      RingNormaliser.normalize pSquareStepR := by decide

private theorem pAdjacentStep_normal :
    RingNormaliser.normalize pAdjacentStepL =
      RingNormaliser.normalize pAdjacentStepR := by decide

private def pSquareBase : PE :=
  pSquareNumeratorAt (pv 0) (pc 0) (pc 1)

private def pAdjacentBase : PE :=
  pAdjacentNumeratorAt (pv 0) (pc 0) (pc 1)

private theorem pSquareBase_normal :
    RingNormaliser.normalize (pc 0) =
      RingNormaliser.normalize pSquareBase := by decide

private theorem pAdjacentBase_normal :
    RingNormaliser.normalize (pc 0) =
      RingNormaliser.normalize pAdjacentBase := by decide

private theorem eval_eqv_congr (e : PE) {rho sigma : Nat → Q'}
    (h : ∀ i, rho i ≈ sigma i) :
    RingNormaliser.eval rho e ≈ RingNormaliser.eval sigma e := by
  induction e with
  | const z => exact Q'.eqv_refl _
  | var i => exact h i
  | add a b iha ihb =>
      exact Q'.add_eqv_congr' iha ihb
  | mul a b iha ihb =>
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ iha)
        (Q'.mul_eqv_congr_left _ _ _ ihb)
  | neg a ih => exact Q'.neg_eqv_congr _ _ ih
  | pow a n ih => exact RingNormaliser.qpow_eqv_congr ih n

private theorem ofNat_succ_eqv (n : Nat) :
    Q'.ofNat (n + 1) ≈ Q'.ofNat n + (1 : Q') := by
  exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1)
    (Q'.add_eqv_congr_left _ _ _ (by decide))

/-! ## Exact quadratic geometric moments -/

def lowerSixRecoverySquareGeomMoment (r : Q') (N : Nat) : Q' :=
  finSum (fun j =>
    (Q'.ofNat (j + 1) * Q'.ofNat (j + 1)) * qpow r j) N

def lowerSixRecoveryAdjacentGeomMoment (r : Q') (N : Nat) : Q' :=
  finSum (fun j =>
    (Q'.ofNat (j + 1) * Q'.ofNat (j + 2)) * qpow r j) N

def lowerSixRecoverySquareGeomNumerator (r : Q') (N : Nat) : Q' :=
  RingNormaliser.eval
    (fun | 0 => r | 1 => Q'.ofNat N | _ => qpow r N)
    pSquareNumerator

def lowerSixRecoveryAdjacentGeomNumerator (r : Q') (N : Nat) : Q' :=
  RingNormaliser.eval
    (fun | 0 => r | 1 => Q'.ofNat N | _ => qpow r N)
    pAdjacentNumerator

private theorem square_step_algebra (r q z : Q') :
    RingNormaliser.eval
        (fun | 0 => r | 1 => q | _ => z) pSquareNumerator +
      (((q + (1 : Q')) * (q + (1 : Q'))) * z) *
        qpow ((1 : Q') + -r) 3 ≈
      RingNormaliser.eval
        (fun | 0 => r | 1 => q + (1 : Q') | _ => z * r)
        pSquareNumerator := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    pSquareStepL pSquareStepR pSquareStep_normal
    (fun | 0 => r | 1 => q | _ => z)
  simpa [pSquareStepL, pSquareStepR, pSquareNumerator,
    pSquareNumeratorAt, pSquareBoundary, pSquareBoundaryAt, pOneSubCube,
    RingNormaliser.eval, pa, pm, pn, pp, pc, pv]
    using h

private theorem adjacent_step_algebra (r q z : Q') :
    RingNormaliser.eval
        (fun | 0 => r | 1 => q | _ => z) pAdjacentNumerator +
      (((q + (1 : Q')) * (q + (2 : Q'))) * z) *
        qpow ((1 : Q') + -r) 3 ≈
      RingNormaliser.eval
        (fun | 0 => r | 1 => q + (1 : Q') | _ => z * r)
        pAdjacentNumerator := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    pAdjacentStepL pAdjacentStepR pAdjacentStep_normal
    (fun | 0 => r | 1 => q | _ => z)
  simpa [pAdjacentStepL, pAdjacentStepR, pAdjacentNumerator,
    pAdjacentNumeratorAt, pAdjacentBoundary, pAdjacentBoundaryAt,
    pOneSubCube, RingNormaliser.eval, pa, pm, pn, pp, pc, pv]
    using h

/-- Exact finite identity
`(1-r)^3 sum_(j<N) (j+1)^2 r^j = squareNumerator(r,N)`.
The theorem is division-free and valid at every rational base. -/
theorem lowerSixRecoverySquareGeomMoment_closed (r : Q') : ∀ N,
    lowerSixRecoverySquareGeomMoment r N *
        qpow ((1 : Q') + -r) 3 ≈
      lowerSixRecoverySquareGeomNumerator r N
  | 0 => by
      change (0 : Q') * qpow ((1 : Q') + -r) 3 ≈
        lowerSixRecoverySquareGeomNumerator r 0
      refine Q'.eqv_trans _ (0 : Q') _
        (RingNormaliser.q_zero_mul _) ?_
      have h := RingNormaliser.poly_identity_of_normal_eq
        (pc 0) pSquareBase pSquareBase_normal
        (fun | 0 => r | _ => (0 : Q'))
      simpa [lowerSixRecoverySquareGeomNumerator, pSquareNumerator,
        pSquareBase, pSquareNumeratorAt, pSquareBoundaryAt,
        RingNormaliser.eval, pa, pm, pn, pc, pv, qpow] using h
  | N + 1 => by
      rw [show lowerSixRecoverySquareGeomMoment r (N + 1) =
          lowerSixRecoverySquareGeomMoment r N +
            (Q'.ofNat (N + 1) * Q'.ofNat (N + 1)) * qpow r N by
        rfl]
      let q := Q'.ofNat N
      let z := qpow r N
      let S := lowerSixRecoverySquareGeomMoment r N
      have ih := lowerSixRecoverySquareGeomMoment_closed r N
      have hq : Q'.ofNat (N + 1) ≈ q + (1 : Q') := by
        dsimp only [q]
        exact ofNat_succ_eqv N
      have hterm :
          (Q'.ofNat (N + 1) * Q'.ofNat (N + 1)) * z ≈
            ((q + (1 : Q')) * (q + (1 : Q'))) * z := by
        exact Q'.mul_eqv_congr_right _ _ z
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _ hq)
            (Q'.mul_eqv_congr_left _ _ _ hq))
      have hleft :
          (S + (Q'.ofNat (N + 1) * Q'.ofNat (N + 1)) * z) *
              qpow ((1 : Q') + -r) 3 ≈
            (S + ((q + (1 : Q')) * (q + (1 : Q'))) * z) *
              qpow ((1 : Q') + -r) 3 :=
        Q'.mul_eqv_congr_right _ _ _
          (Q'.add_eqv_congr_left S _ _ hterm)
      have hdistrib :
          (S + ((q + (1 : Q')) * (q + (1 : Q'))) * z) *
              qpow ((1 : Q') + -r) 3 ≈
            S * qpow ((1 : Q') + -r) 3 +
              (((q + (1 : Q')) * (q + (1 : Q'))) * z) *
                qpow ((1 : Q') + -r) 3 :=
        RingNormaliser.q_add_mul _ _ _
      have hreplace :
          S * qpow ((1 : Q') + -r) 3 +
              (((q + (1 : Q')) * (q + (1 : Q'))) * z) *
                qpow ((1 : Q') + -r) 3 ≈
            RingNormaliser.eval
                (fun | 0 => r | 1 => q | _ => z) pSquareNumerator +
              (((q + (1 : Q')) * (q + (1 : Q'))) * z) *
                qpow ((1 : Q') + -r) 3 := by
        exact Q'.add_eqv_congr_right _ _ _ ih
      have hstep := square_step_algebra r q z
      have hsuccZ : z * r = qpow r (N + 1) := rfl
      have htarget :
          RingNormaliser.eval
              (fun | 0 => r | 1 => q + (1 : Q') | _ => z * r)
              pSquareNumerator ≈
            lowerSixRecoverySquareGeomNumerator r (N + 1) := by
        unfold lowerSixRecoverySquareGeomNumerator
        apply eval_eqv_congr
        intro i
        cases i with
        | zero => exact Q'.eqv_refl _
        | succ i =>
          cases i with
          | zero => exact Q'.eqv_symm hq
          | succ i =>
            rw [hsuccZ]
            exact Q'.eqv_refl _
      dsimp only [S, z, q] at ih hleft hdistrib hreplace hstep htarget ⊢
      exact Q'.eqv_trans _ _ _ hleft
        (Q'.eqv_trans _ _ _ hdistrib
          (Q'.eqv_trans _ _ _ hreplace
            (Q'.eqv_trans _ _ _ hstep htarget)))

/-- Exact finite identity
`(1-r)^3 sum_(j<N) (j+1)(j+2) r^j = adjacentNumerator(r,N)`. -/
theorem lowerSixRecoveryAdjacentGeomMoment_closed (r : Q') : ∀ N,
    lowerSixRecoveryAdjacentGeomMoment r N *
        qpow ((1 : Q') + -r) 3 ≈
      lowerSixRecoveryAdjacentGeomNumerator r N
  | 0 => by
      change (0 : Q') * qpow ((1 : Q') + -r) 3 ≈
        lowerSixRecoveryAdjacentGeomNumerator r 0
      refine Q'.eqv_trans _ (0 : Q') _
        (RingNormaliser.q_zero_mul _) ?_
      have h := RingNormaliser.poly_identity_of_normal_eq
        (pc 0) pAdjacentBase pAdjacentBase_normal
        (fun | 0 => r | _ => (0 : Q'))
      simpa [lowerSixRecoveryAdjacentGeomNumerator, pAdjacentNumerator,
        pAdjacentBase, pAdjacentNumeratorAt, pAdjacentBoundaryAt,
        RingNormaliser.eval, pa, pm, pn, pc, pv, qpow] using h
  | N + 1 => by
      rw [show lowerSixRecoveryAdjacentGeomMoment r (N + 1) =
          lowerSixRecoveryAdjacentGeomMoment r N +
            (Q'.ofNat (N + 1) * Q'.ofNat (N + 2)) * qpow r N by
        rfl]
      let q := Q'.ofNat N
      let z := qpow r N
      let S := lowerSixRecoveryAdjacentGeomMoment r N
      have hq1 : Q'.ofNat (N + 1) ≈ q + (1 : Q') := by
        dsimp only [q]
        exact ofNat_succ_eqv N
      have hq2 : Q'.ofNat (N + 2) ≈ q + (2 : Q') := by
        refine Q'.eqv_trans _ (Q'.ofNat (N + 1) + (1 : Q')) _ ?_ ?_
        · exact ofNat_succ_eqv (N + 1)
        refine Q'.eqv_trans _ ((q + (1 : Q')) + (1 : Q')) _
          (Q'.add_eqv_congr_right _ _ _ hq1) ?_
        exact Q'.eqv_trans _ (q + ((1 : Q') + (1 : Q'))) _
          (Q'.add_assoc_eqv q 1 1)
          (Q'.add_eqv_congr_left q _ _ (by decide))
      have hterm :
          (Q'.ofNat (N + 1) * Q'.ofNat (N + 2)) * z ≈
            ((q + (1 : Q')) * (q + (2 : Q'))) * z := by
        exact Q'.mul_eqv_congr_right _ _ z
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _ hq1)
            (Q'.mul_eqv_congr_left _ _ _ hq2))
      have hleft :
          (S + (Q'.ofNat (N + 1) * Q'.ofNat (N + 2)) * z) *
              qpow ((1 : Q') + -r) 3 ≈
            (S + ((q + (1 : Q')) * (q + (2 : Q'))) * z) *
              qpow ((1 : Q') + -r) 3 :=
        Q'.mul_eqv_congr_right _ _ _
          (Q'.add_eqv_congr_left S _ _ hterm)
      have hdistrib :
          (S + ((q + (1 : Q')) * (q + (2 : Q'))) * z) *
              qpow ((1 : Q') + -r) 3 ≈
            S * qpow ((1 : Q') + -r) 3 +
              (((q + (1 : Q')) * (q + (2 : Q'))) * z) *
                qpow ((1 : Q') + -r) 3 :=
        RingNormaliser.q_add_mul _ _ _
      have ih := lowerSixRecoveryAdjacentGeomMoment_closed r N
      have hreplace :
          S * qpow ((1 : Q') + -r) 3 +
              (((q + (1 : Q')) * (q + (2 : Q'))) * z) *
                qpow ((1 : Q') + -r) 3 ≈
            RingNormaliser.eval
                (fun | 0 => r | 1 => q | _ => z) pAdjacentNumerator +
              (((q + (1 : Q')) * (q + (2 : Q'))) * z) *
                qpow ((1 : Q') + -r) 3 := by
        exact Q'.add_eqv_congr_right _ _ _ ih
      have hstep := adjacent_step_algebra r q z
      have hsuccZ : z * r = qpow r (N + 1) := rfl
      have htarget :
          RingNormaliser.eval
              (fun | 0 => r | 1 => q + (1 : Q') | _ => z * r)
              pAdjacentNumerator ≈
            lowerSixRecoveryAdjacentGeomNumerator r (N + 1) := by
        unfold lowerSixRecoveryAdjacentGeomNumerator
        apply eval_eqv_congr
        intro i
        cases i with
        | zero => exact Q'.eqv_refl _
        | succ i =>
          cases i with
          | zero => exact Q'.eqv_symm hq1
          | succ i =>
            rw [hsuccZ]
            exact Q'.eqv_refl _
      dsimp only [S, z, q] at ih hleft hdistrib hreplace hstep htarget ⊢
      exact Q'.eqv_trans _ _ _ hleft
        (Q'.eqv_trans _ _ _ hdistrib
          (Q'.eqv_trans _ _ _ hreplace
            (Q'.eqv_trans _ _ _ hstep htarget)))

/-! ## Exact next-carrier prefix numerator -/

/-- The scale-local coefficient multiplying the square geometric moment. -/
def lowerSixRecoveryLinearCarrierCore (k : Nat) : Q' :=
  qpow ((1 : Q') + harmW k) 3 +
    -(Q'.ofNat 6 * (harmU k * harmU k))

/-- Exact two-moment form of a carrier prefix of length `N`. -/
def lowerSixRecoveryLinearCarrierGeomPrefix (k N : Nat) : Q' :=
  let w := harmW k
  let r := qpow w 6
  let s := qpow w 8
  lowerSixRecoveryLinearCarrierCore k *
      lowerSixRecoverySquareGeomMoment r N +
    -(Q'.ofNat 8 * qpow w 3 *
      lowerSixRecoveryAdjacentGeomMoment s N)

private theorem linearSixPower_eqv_geom (w : Q') (j : Nat) :
    qpow w (6 * j) ≈ qpow (qpow w 6) j := by
  exact Q'.eqv_symm (HeatKernelRGStep.qpow_qpow w 6 j)

private theorem linearOddPower_eqv_geomEight (w : Q') (j : Nat) :
    qpow w (6 * j) * qpow w (2 * (j + 1) + 1) ≈
      qpow w 3 * qpow (qpow w 8) j := by
  have htotal : 6 * j + (2 * (j + 1) + 1) = 8 * j + 3 := by omega
  have hjoin := Q'.eqv_symm
    (HeatKernelRGStep.qpow_add w (6 * j) (2 * (j + 1) + 1))
  rw [htotal] at hjoin
  have hsplit := HeatKernelRGStep.qpow_add w (8 * j) 3
  have hiter := HeatKernelRGStep.qpow_qpow w 8 j
  exact Q'.eqv_trans _ _ _ hjoin
    (Q'.eqv_trans _ _ _ hsplit
      (Q'.eqv_trans _
        (qpow (qpow w 8) j * qpow w 3) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hiter))
        (Q'.mul_comm_eqv _ _)))

/-- A single linear carrier is exactly the difference of a square-moment
geometric term at ratio `w^6` and an adjacent-moment term at ratio `w^8`. -/
theorem lowerSixRecoveryLinearCarrier_eqv_geomTerms (k j : Nat) :
    lowerSixRecoveryLinearCarrier k j ≈
      lowerSixRecoveryLinearCarrierCore k *
        ((Q'.ofNat (j + 1) * Q'.ofNat (j + 1)) *
          qpow (qpow (harmW k) 6) j) +
      -(Q'.ofNat 8 * qpow (harmW k) 3 *
        ((Q'.ofNat (j + 1) * Q'.ofNat (j + 2)) *
          qpow (qpow (harmW k) 8) j)) := by
  let w := harmW k
  let u := harmU k
  let n := Q'.ofNat (j + 1)
  let m := Q'.ofNat (j + 2)
  let a := qpow ((1 : Q') + w) 3
  let q6 := qpow w (6 * j)
  let qo := qpow w (2 * (j + 1) + 1)
  let rj := qpow (qpow w 6) j
  let sj := qpow (qpow w 8) j
  have h6 : q6 ≈ rj := by
    dsimp only [q6, rj]
    exact linearSixPower_eqv_geom w j
  have h8 : q6 * qo ≈ qpow w 3 * sj := by
    dsimp only [q6, qo, sj]
    exact linearOddPower_eqv_geomEight w j
  have halgebra :
      n * q6 *
          (n * a + -(Q'.ofNat 8 * (m * qo)) +
            -(Q'.ofNat 6 * (u * u) * n)) ≈
        (a + -(Q'.ofNat 6 * (u * u))) * ((n * n) * q6) +
          -(Q'.ofNat 8 * ((n * m) * (q6 * qo))) := by
    rising_splice_ring
  have hreplace :
      (a + -(Q'.ofNat 6 * (u * u))) * ((n * n) * q6) +
          -(Q'.ofNat 8 * ((n * m) * (q6 * qo))) ≈
        (a + -(Q'.ofNat 6 * (u * u))) * ((n * n) * rj) +
          -(Q'.ofNat 8 * qpow w 3 * ((n * m) * sj)) := by
    refine Q'.add_eqv_congr' ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left (n * n) _ _ h6)
    · apply Q'.neg_eqv_congr
      refine Q'.eqv_trans _
        (Q'.ofNat 8 * ((n * m) * (qpow w 3 * sj))) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left (Q'.ofNat 8) _ _
          (Q'.mul_eqv_congr_left (n * m) _ _ h8)
      · rising_splice_ring
  unfold lowerSixRecoveryLinearCarrier lowerSixRecoveryModeSlope
    thetaResidualCellSlope lowerSixRecoveryLinearCarrierCore
  dsimp only [w, u, n, m, a, q6, qo, rj, sj] at halgebra hreplace ⊢
  exact Q'.eqv_trans _ _ _ halgebra hreplace

/-- Summing the single-mode factorization gives an exact two-geometric-moment
formula for every prefix length. -/
theorem lowerSixRecoveryLinearCarrier_finSum_eqv_geomPrefix (k : Nat) : ∀ N,
    finSum (fun j => lowerSixRecoveryLinearCarrier k j) N ≈
      lowerSixRecoveryLinearCarrierGeomPrefix k N
  | 0 => by
      unfold lowerSixRecoveryLinearCarrierGeomPrefix
        lowerSixRecoverySquareGeomMoment
        lowerSixRecoveryAdjacentGeomMoment finSum
      dsimp only
      rising_splice_ring
  | N + 1 => by
      rw [finSum_succ]
      let w := harmW k
      let r := qpow w 6
      let s := qpow w 8
      let A := lowerSixRecoveryLinearCarrierCore k
      let B := Q'.ofNat 8 * qpow w 3
      let M2 := lowerSixRecoverySquareGeomMoment r N
      let M12 := lowerSixRecoveryAdjacentGeomMoment s N
      let t2 := (Q'.ofNat (N + 1) * Q'.ofNat (N + 1)) * qpow r N
      let t12 := (Q'.ofNat (N + 1) * Q'.ofNat (N + 2)) * qpow s N
      have ih := lowerSixRecoveryLinearCarrier_finSum_eqv_geomPrefix k N
      have ht := lowerSixRecoveryLinearCarrier_eqv_geomTerms k N
      change finSum (fun j => lowerSixRecoveryLinearCarrier k j) N ≈
        A * M2 + -(B * M12) at ih
      change lowerSixRecoveryLinearCarrier k N ≈
        A * t2 + -(B * t12) at ht
      change finSum (fun j => lowerSixRecoveryLinearCarrier k j) N +
          lowerSixRecoveryLinearCarrier k N ≈
        A * (M2 + t2) + -(B * (M12 + t12))
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' ih ht) (by rising_splice_ring)

/-- Product of the two positive geometric denominators used to clear a
carrier prefix. -/
def lowerSixRecoveryLinearCarrierPrefixDen (k : Nat) : Q' :=
  let w := harmW k
  qpow ((1 : Q') + -qpow w 6) 3 *
    qpow ((1 : Q') + -qpow w 8) 3

/-- Explicit division-free numerator of the next-carrier prefix. -/
def lowerSixRecoveryLinearCarrierPrefixNumerator (k N : Nat) : Q' :=
  let w := harmW k
  let r := qpow w 6
  let s := qpow w 8
  let d6 := qpow ((1 : Q') + -r) 3
  let d8 := qpow ((1 : Q') + -s) 3
  lowerSixRecoveryLinearCarrierCore k *
      lowerSixRecoverySquareGeomNumerator r N * d8 +
    -(Q'.ofNat 8 * qpow w 3 *
      lowerSixRecoveryAdjacentGeomNumerator s N * d6)

private theorem clear_two_moments_algebra
    (A B M2 M12 d6 d8 : Q') :
    (A * M2 + -(B * M12)) * (d6 * d8) ≈
      A * (M2 * d6) * d8 + -(B * (M12 * d8) * d6) := by
  rising_splice_ring

/-- Every next-carrier prefix has one exact denominator-cleared numerator.
This is the sharp `p`-dependent coordinate retained by the Abel splice. -/
theorem lowerSixRecoveryNextCarrierPrefix_mul_den_eqv_numerator
    (k p : Nat) :
    lowerSixRecoveryNextCarrierPrefix k p *
        lowerSixRecoveryLinearCarrierPrefixDen (k + 1) ≈
      lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (p + 1) := by
  let K := k + 1
  let N := p + 1
  let w := harmW K
  let r := qpow w 6
  let s := qpow w 8
  let d6 := qpow ((1 : Q') + -r) 3
  let d8 := qpow ((1 : Q') + -s) 3
  let A := lowerSixRecoveryLinearCarrierCore K
  let B := Q'.ofNat 8 * qpow w 3
  let M2 := lowerSixRecoverySquareGeomMoment r N
  let M12 := lowerSixRecoveryAdjacentGeomMoment s N
  let U2 := lowerSixRecoverySquareGeomNumerator r N
  let U12 := lowerSixRecoveryAdjacentGeomNumerator s N
  have hprefix := lowerSixRecoveryLinearCarrier_finSum_eqv_geomPrefix K N
  have h2 := lowerSixRecoverySquareGeomMoment_closed r N
  have h12 := lowerSixRecoveryAdjacentGeomMoment_closed s N
  change M2 * d6 ≈ U2 at h2
  change M12 * d8 ≈ U12 at h12
  have hden : lowerSixRecoveryLinearCarrierPrefixDen K ≈ d6 * d8 :=
    Q'.eqv_refl _
  have hgeom : lowerSixRecoveryLinearCarrierGeomPrefix K N ≈
      A * M2 + -(B * M12) := Q'.eqv_refl _
  have hnum :
      A * U2 * d8 + -(B * U12 * d6) ≈
        lowerSixRecoveryLinearCarrierPrefixNumerator K N :=
    Q'.eqv_refl _
  have hstart :
      lowerSixRecoveryNextCarrierPrefix k p *
          lowerSixRecoveryLinearCarrierPrefixDen K ≈
        lowerSixRecoveryLinearCarrierGeomPrefix K N * (d6 * d8) := by
    unfold lowerSixRecoveryNextCarrierPrefix
    exact Q'.eqv_trans _
      (finSum (fun j => lowerSixRecoveryLinearCarrier K j) N *
        lowerSixRecoveryLinearCarrierPrefixDen K) _
      (Q'.eqv_refl _) (Q'.eqv_trans _
        (lowerSixRecoveryLinearCarrierGeomPrefix K N *
          lowerSixRecoveryLinearCarrierPrefixDen K) _
        (Q'.mul_eqv_congr_right _ _ _ hprefix)
        (Q'.mul_eqv_congr_left _ _ _ hden))
  refine Q'.eqv_trans _ _ _ hstart ?_
  refine Q'.eqv_trans _ ((A * M2 + -(B * M12)) * (d6 * d8)) _
    (Q'.mul_eqv_congr_right _ _ _ hgeom) ?_
  refine Q'.eqv_trans _
    (A * (M2 * d6) * d8 + -(B * (M12 * d8) * d6)) _
    (clear_two_moments_algebra A B M2 M12 d6 d8) ?_
  refine Q'.eqv_trans _ (A * U2 * d8 + -(B * U12 * d6)) _ ?_ hnum
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ d8
      (Q'.mul_eqv_congr_left A _ _ h2))
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_right _ _ d6
        (Q'.mul_eqv_congr_left B _ _ h12)))

/-- The geometric clearing denominator is strictly positive at every
harmonic scale. -/
theorem lowerSixRecoveryLinearCarrierPrefixDen_pos (k : Nat) :
    (0 : Q') < lowerSixRecoveryLinearCarrierPrefixDen k := by
  have hwlt : harmW k < (1 : Q') := by
    unfold harmW ReciprocalBernoulliUpper.oneSub
    exact BakryEmery.one_sub_lt_one (harmU_pos k)
  have h6lt : qpow (harmW k) 6 < (1 : Q') := by
    simpa only [show 6 = 5 + 1 by omega] using
      (HeatKernelGap.qpow_succ_lt_one (harmW_nonneg k) hwlt 5)
  have h8lt : qpow (harmW k) 8 < (1 : Q') := by
    simpa only [show 8 = 7 + 1 by omega] using
      (HeatKernelGap.qpow_succ_lt_one (harmW_nonneg k) hwlt 7)
  have hd6 : (0 : Q') < (1 : Q') + -qpow (harmW k) 6 :=
    DefectRecursionPrimary.sub_pos_of_lt h6lt
  have hd8 : (0 : Q') < (1 : Q') + -qpow (harmW k) 8 :=
    DefectRecursionPrimary.sub_pos_of_lt h8lt
  unfold lowerSixRecoveryLinearCarrierPrefixDen
  exact Q'.mul_pos
    (BondMovingScaledNorm.qpow_pos hd6 3)
    (BondMovingScaledNorm.qpow_pos hd8 3)

/-- Any bound on the explicit cleared numerator transports back to the actual
carrier prefix.  This is the symbolic consumer for all later numerator
estimates. -/
theorem lowerSixRecoveryNextCarrierPrefix_le_of_numerator
    {k p : Nat} {B : Q'}
    (h : lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (p + 1) ≤
      B * lowerSixRecoveryLinearCarrierPrefixDen (k + 1)) :
    lowerSixRecoveryNextCarrierPrefix k p ≤ B := by
  let D := lowerSixRecoveryLinearCarrierPrefixDen (k + 1)
  have hrepr :=
    lowerSixRecoveryNextCarrierPrefix_mul_den_eqv_numerator k p
  have hmul : lowerSixRecoveryNextCarrierPrefix k p * D ≤ B * D :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hrepr) h
  exact BakryEmery.le_of_mul_le_mul_right_pos
    (lowerSixRecoveryLinearCarrierPrefixDen_pos (k + 1)) hmul

/-- A nonnegative prefix gives a nonnegative cleared numerator. -/
theorem lowerSixRecoveryLinearCarrierPrefixNumerator_nonnegative
    {k p : Nat}
    (hprefix : (0 : Q') ≤ lowerSixRecoveryNextCarrierPrefix k p) :
    (0 : Q') ≤
      lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (p + 1) := by
  let D := lowerSixRecoveryLinearCarrierPrefixDen (k + 1)
  have hD0 : (0 : Q') ≤ D :=
    Q'.le_of_lt (lowerSixRecoveryLinearCarrierPrefixDen_pos (k + 1))
  have hmul : (0 : Q') ≤ lowerSixRecoveryNextCarrierPrefix k p * D :=
    Q'.mul_nonneg _ _ hprefix hD0
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_of_eqv
      (lowerSixRecoveryNextCarrierPrefix_mul_den_eqv_numerator k p))

/-! ## Cleared Abel splice and payment consumer -/

/-- Abel variation term with the full carrier prefix replaced by its exact
cleared numerator. -/
def lowerSixRecoveryClearedAbelVariationTerm (k p : Nat) : Q' :=
  lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (p + 1) *
    lowerSixRecoveryComplementVariation k p

/-- The complete complement debt after clearing the single positive prefix
denominator. -/
def lowerSixRecoveryClearedAbelDebt (k c : Nat) : Q' :=
  let L := 2 * c - 1
  lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (L + 1) *
      lowerSixRecoveryComplementScaleIncrement k L +
    finSum (fun p => lowerSixRecoveryClearedAbelVariationTerm k p) L

private theorem cleared_abel_term_mul_den (k p : Nat) :
    lowerSixRecoveryAbelVariationTerm k p *
        lowerSixRecoveryLinearCarrierPrefixDen (k + 1) ≈
      lowerSixRecoveryClearedAbelVariationTerm k p := by
  have hp := lowerSixRecoveryNextCarrierPrefix_mul_den_eqv_numerator k p
  unfold lowerSixRecoveryAbelVariationTerm
    lowerSixRecoveryClearedAbelVariationTerm
  refine Q'.eqv_trans _
    ((lowerSixRecoveryNextCarrierPrefix k p *
        lowerSixRecoveryLinearCarrierPrefixDen (k + 1)) *
      lowerSixRecoveryComplementVariation k p) _ ?_ ?_
  · refine Q'.eqv_trans _
      (lowerSixRecoveryNextCarrierPrefix k p *
        (lowerSixRecoveryComplementVariation k p *
          lowerSixRecoveryLinearCarrierPrefixDen (k + 1))) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      (lowerSixRecoveryNextCarrierPrefix k p *
        (lowerSixRecoveryLinearCarrierPrefixDen (k + 1) *
          lowerSixRecoveryComplementVariation k p)) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  · exact Q'.mul_eqv_congr_right _ _ _ hp

private theorem finSum_cleared_abel_terms (k L : Nat) :
    finSum (fun p => lowerSixRecoveryAbelVariationTerm k p) L *
        lowerSixRecoveryLinearCarrierPrefixDen (k + 1) ≈
      finSum (fun p => lowerSixRecoveryClearedAbelVariationTerm k p) L := by
  refine Q'.eqv_trans _
    (finSum (fun p =>
      lowerSixRecoveryAbelVariationTerm k p *
        lowerSixRecoveryLinearCarrierPrefixDen (k + 1)) L) _
    (RationalTail.finSum_mul_const _ _ _) ?_
  exact RationalTail.finSum_eqv_congr _ _
    (fun p => cleared_abel_term_mul_den k p) L

/-- Exact sharp splice: the original complement debt multiplied by one
positive scale denominator is the terminal numerator plus the full sequence
of `p`-dependent numerator variations. -/
theorem lowerSixRecoveryLinearComplementDebt_mul_den_eqv_clearedAbel
    {k c : Nat} (hc : 1 ≤ c) :
    lowerSixRecoveryLinearComplementDebt k c *
        lowerSixRecoveryLinearCarrierPrefixDen (k + 1) ≈
      lowerSixRecoveryClearedAbelDebt k c := by
  let L := 2 * c - 1
  let D := lowerSixRecoveryLinearCarrierPrefixDen (k + 1)
  have hab := lowerSixRecoveryLinearComplementDebt_eqv_abel
    (k := k) (c := c) hc
  have hterminal :=
    lowerSixRecoveryNextCarrierPrefix_mul_den_eqv_numerator k L
  have hsum := finSum_cleared_abel_terms k L
  change finSum (fun p => lowerSixRecoveryAbelVariationTerm k p) L * D ≈
    finSum (fun p => lowerSixRecoveryClearedAbelVariationTerm k p) L at hsum
  change lowerSixRecoveryLinearComplementDebt k c ≈
      lowerSixRecoveryNextCarrierPrefix k L *
          lowerSixRecoveryComplementScaleIncrement k L +
        finSum (fun p => lowerSixRecoveryAbelVariationTerm k p) L at hab
  have hterminalTerm :
      (lowerSixRecoveryNextCarrierPrefix k L *
          lowerSixRecoveryComplementScaleIncrement k L) * D ≈
        lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (L + 1) *
          lowerSixRecoveryComplementScaleIncrement k L := by
    refine Q'.eqv_trans _
      ((lowerSixRecoveryNextCarrierPrefix k L * D) *
        lowerSixRecoveryComplementScaleIncrement k L) _ ?_ ?_
    · refine Q'.eqv_trans _
        (lowerSixRecoveryNextCarrierPrefix k L *
          (lowerSixRecoveryComplementScaleIncrement k L * D)) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _
        (lowerSixRecoveryNextCarrierPrefix k L *
          (D * lowerSixRecoveryComplementScaleIncrement k L)) _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    · exact Q'.mul_eqv_congr_right _ _ _ hterminal
  have hdef :
      lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (L + 1) *
          lowerSixRecoveryComplementScaleIncrement k L +
        finSum (fun p => lowerSixRecoveryClearedAbelVariationTerm k p) L ≈
      lowerSixRecoveryClearedAbelDebt k c := Q'.eqv_refl _
  refine Q'.eqv_trans _
    ((lowerSixRecoveryNextCarrierPrefix k L *
          lowerSixRecoveryComplementScaleIncrement k L +
        finSum (fun p => lowerSixRecoveryAbelVariationTerm k p) L) * D) _
    (Q'.mul_eqv_congr_right _ _ _ hab) ?_
  refine Q'.eqv_trans _
    ((lowerSixRecoveryNextCarrierPrefix k L *
          lowerSixRecoveryComplementScaleIncrement k L) * D +
      finSum (fun p => lowerSixRecoveryAbelVariationTerm k p) L * D) _
    (Q'.add_mul_eqv _ _ _) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hterminalTerm hsum) hdef

/-- Symbolic post-bootstrap payment consumer in the exact prefix-numerator
coordinate.  Proving its single displayed cleared inequality pays the entire
complement debt and terminal mode, with no loss. -/
theorem lowerSixRecoveryLinearPayment_of_clearedAbelPayment
    {k c : Nat} (hc : 1 ≤ c)
    (hpay : lowerSixRecoveryClearedAbelDebt k c +
        -(lowerSixRecoveryTerminalDrop k (2 * c) *
          lowerSixRecoveryLinearCarrierPrefixDen (k + 1)) ≤
      lowerSixRecoveryLinearScaleReserve k c *
        lowerSixRecoveryLinearCarrierPrefixDen (k + 1)) :
    -lowerSixRecoveryLinearDriftDebt k c ≤
      lowerSixRecoveryLinearScaleReserve k c := by
  let D := lowerSixRecoveryLinearCarrierPrefixDen (k + 1)
  have hdebt :=
    lowerSixRecoveryLinearComplementDebt_mul_den_eqv_clearedAbel
      (k := k) (c := c) hc
  have hscaled :
      (lowerSixRecoveryLinearComplementDebt k c +
          -lowerSixRecoveryTerminalDrop k (2 * c)) * D ≤
        lowerSixRecoveryLinearScaleReserve k c * D := by
    have hleft :
        (lowerSixRecoveryLinearComplementDebt k c +
            -lowerSixRecoveryTerminalDrop k (2 * c)) * D ≈
          lowerSixRecoveryClearedAbelDebt k c +
            -(lowerSixRecoveryTerminalDrop k (2 * c) * D) := by
      refine Q'.eqv_trans _
        (lowerSixRecoveryLinearComplementDebt k c * D +
          (-lowerSixRecoveryTerminalDrop k (2 * c)) * D) _
        (Q'.add_mul_eqv _ _ _) ?_
      exact Q'.add_eqv_congr' hdebt
        (Q'.neg_mul_eqv _ _)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hpay
  have hunscaled :
      lowerSixRecoveryLinearComplementDebt k c +
          -lowerSixRecoveryTerminalDrop k (2 * c) ≤
        lowerSixRecoveryLinearScaleReserve k c :=
    BakryEmery.le_of_mul_le_mul_right_pos
      (lowerSixRecoveryLinearCarrierPrefixDen_pos (k + 1)) hscaled
  exact lowerSixRecoveryLinearPayment_of_complementPayment hunscaled

/-- On the certified falling suffix, the sharp cleared variation terms are
termwise nonnegative.  This is the exact splice of the new numerator
coordinate to the previously proved suffix geometry. -/
theorem lowerSixRecoveryClearedAbelVariationTerm_tail_nonnegative
    {k r : Nat} (hr1 : 1 ≤ r)
    (hthreshold : k + 2 ≤ lowerSixRecoveryComplementExponent r)
    (hcarrier : (0 : Q') ≤ lowerSixRecoveryLinearCarrier (k + 1) r)
    (hprefix : (0 : Q') ≤ lowerSixRecoveryNextCarrierPrefix k r) :
    ∀ d, (0 : Q') ≤
      lowerSixRecoveryClearedAbelVariationTerm k (r + d) := by
  intro d
  have hp : (0 : Q') ≤ lowerSixRecoveryNextCarrierPrefix k (r + d) :=
    lowerSixRecoveryNextCarrierPrefix_nonnegative_mono (by omega)
      hcarrier hprefix
  have hnum := lowerSixRecoveryLinearCarrierPrefixNumerator_nonnegative hp
  have hfall :=
    lowerSixRecoveryComplementScaleIncrement_tail_antitone_of_exponent_ge_scale
      hr1 hthreshold d
  have hvar := lowerSixRecoveryComplementVariation_nonnegative_of_descent
    (by simpa only [Nat.add_assoc] using hfall)
  unfold lowerSixRecoveryClearedAbelVariationTerm
  exact Q'.mul_nonneg _ _ hnum hvar

/-! ## Kernel fence against a scalar-terminal truncation -/

/-- At the first post-bootstrap physical cell, the first variation term after
the carrier-prefix crossing is strictly positive.  Hence the falling suffix
cannot be discarded in favor of the Abel terminal term alone; its full
`p`-dependent prefix profile is load-bearing. -/
theorem lowerSixRecoveryTerminalOnlyAbelCap_648_25_fails :
    (0 : Q') < lowerSixRecoveryAbelVariationTerm 648 25 := by
  unfold lowerSixRecoveryAbelVariationTerm
    lowerSixRecoveryNextCarrierPrefix
    lowerSixRecoveryLinearCarrier lowerSixRecoveryModeSlope
    thetaResidualCellSlope lowerSixRecoveryComplementVariation
    lowerSixRecoveryComplementScaleIncrement
    lowerSixRecoveryComplementWeight harmW harmU
    ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit
    finSum qpow
  decide

#print axioms lowerSixRecoverySquareGeomMoment_closed
#print axioms lowerSixRecoveryAdjacentGeomMoment_closed
#print axioms lowerSixRecoveryLinearCarrier_eqv_geomTerms
#print axioms lowerSixRecoveryLinearCarrier_finSum_eqv_geomPrefix
#print axioms lowerSixRecoveryNextCarrierPrefix_mul_den_eqv_numerator
#print axioms lowerSixRecoveryLinearCarrierPrefixDen_pos
#print axioms lowerSixRecoveryNextCarrierPrefix_le_of_numerator
#print axioms lowerSixRecoveryLinearCarrierPrefixNumerator_nonnegative
#print axioms lowerSixRecoveryLinearComplementDebt_mul_den_eqv_clearedAbel
#print axioms lowerSixRecoveryLinearPayment_of_clearedAbelPayment
#print axioms lowerSixRecoveryClearedAbelVariationTerm_tail_nonnegative
#print axioms lowerSixRecoveryTerminalOnlyAbelCap_648_25_fails

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelRisingSplice
