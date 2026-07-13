/-
Raw even/odd endpoint polynomials before the square-root-band substitution.

Keeping the harmonic denominator `D` independent avoids the exponential
intermediate expansion caused by substituting a quadratic expression directly
into `D^6`.  These identities are the first stage of that substitution.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpoint

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointRaw

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpoint

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr
private def pc (n : Int) : PE := .const n
private def padd (a b : PE) : PE := .add a b
private def pmul (a b : PE) : PE := .mul a b
private def pneg (a : PE) : PE := .neg a
private def psub (a b : PE) : PE := padd a (pneg b)
private def ppow (a : PE) (n : Nat) : PE := .pow a n

def qIntPoly (x : Q') : List Int → Q'
  | [] => 0
  | a :: as => Q'.ofInt a + x * qIntPoly x as

private def pIntPoly (x : PE) : List Int → PE
  | [] => pc 0
  | a :: as => padd (pc a) (pmul x (pIntPoly x as))

private def pTerm (c : Int) (D X : PE) (d x : Nat) : PE :=
  pmul (pc c) (pmul (ppow D d) (ppow X x))

private def pAntiderivative (D X : PE) : PE :=
  padd (pTerm (-840) D X 6 1) <|
  padd (pTerm 1960 D X 5 3) <|
  padd (pTerm (-420) D X 5 2) <|
  padd (pTerm 140 D X 5 1) <|
  padd (pTerm (-672) D X 4 5) <|
  padd (pTerm (-1260) D X 4 4) <|
  padd (pTerm (-490) D X 4 3) <|
  padd (pTerm 735 D X 4 2) <|
  padd (pTerm 847 D X 4 1) <|
  padd (pTerm 560 D X 3 6) <|
  padd (pTerm 1344 D X 3 5) <|
  padd (pTerm 140 D X 3 4) <|
  padd (pTerm (-1890) D X 3 3) <|
  padd (pTerm (-805) D X 3 2) <|
  padd (pTerm 651 D X 3 1) <|
  padd (pTerm (-120) D X 2 7) <|
  padd (pTerm (-980) D X 2 6) <|
  padd (pTerm (-84) D X 2 5) <|
  padd (pTerm 1960 D X 2 4) <|
  padd (pTerm 420 D X 2 3) <|
  padd (pTerm (-980) D X 2 2) <|
  padd (pTerm (-216) D X 2 1) <|
  padd (pTerm 240 D X 1 7) <|
  padd (pTerm 280 D X 1 6) <|
  padd (pTerm (-840) D X 1 5) <|
  padd (pTerm (-560) D X 1 4) <|
  padd (pTerm 840 D X 1 3) <|
  padd (pTerm 280 D X 1 2) <|
  padd (pTerm (-240) D X 1 1) <|
  padd (pTerm (-120) D X 0 7) <|
  padd (pTerm 140 D X 0 6) <|
  padd (pTerm 252 D X 0 5) <|
  padd (pTerm (-280) D X 0 4) <|
  padd (pTerm (-140) D X 0 3) <|
  padd (pTerm 140 D X 0 2)
    (pTerm 8 D X 0 1)

private def evenR5 (m : Q') : Q' := qIntPoly m [12, 61, 98]
private def evenR4 (m : Q') : Q' :=
  qIntPoly m [120, 2159, 6526, 7404, 2976]
private def evenR3 (m : Q') : Q' :=
  qIntPoly m [351, 2774, 6196, 5424, 1680]
private def evenR2 (m : Q') : Q' :=
  qIntPoly m [18, 1907, 9048, 14262, 8355, 1270]
private def evenR1 (m : Q') : Q' :=
  qIntPoly m [-2, 9, 264, 786, 789, 254]
private def evenR0 (m : Q') : Q' :=
  qIntPoly m [-2, -103, 348, 4062, 7425, 3810]

/-- `210` times the full cleared even-centre block `n=m,...,2m`,
expressed before imposing the relation between `D` and `m`. -/
def thetaCubicEvenRawFormula (D m : Q') : Q' :=
  -(Q'.ofInt 840 * (m + Q'.ofInt 1) * RingNormaliser.qpow D 6) +
    (Q'.ofInt 140 * (m + Q'.ofInt 1) * evenR5 m * RingNormaliser.qpow D 5 +
      (-(Q'.ofInt 7 * (m + Q'.ofInt 1) * evenR4 m * RingNormaliser.qpow D 4) +
        (Q'.ofInt 21 * m * (m + Q'.ofInt 1) * evenR3 m * RingNormaliser.qpow D 3 +
          (-(Q'.ofInt 12 * m * (m + Q'.ofInt 1) * evenR2 m * RingNormaliser.qpow D 2) +
            (Q'.ofInt 120 * m * (m + Q'.ofInt 1) * evenR1 m * D +
              -(Q'.ofInt 4 * m * (m + Q'.ofInt 1) * evenR0 m))))))

private def pEvenRawEndpoint (D m : PE) : PE :=
  padd (pneg (pmul (pmul (pc 840) (padd m (pc 1))) (ppow D 6))) <|
  padd (pmul (pmul (pmul (pc 140) (padd m (pc 1)))
      (pIntPoly m [12, 61, 98])) (ppow D 5)) <|
  padd (pneg (pmul (pmul (pmul (pc 7) (padd m (pc 1)))
      (pIntPoly m [120, 2159, 6526, 7404, 2976])) (ppow D 4))) <|
  padd (pmul (pmul (pmul (pmul (pc 21) m) (padd m (pc 1)))
      (pIntPoly m [351, 2774, 6196, 5424, 1680])) (ppow D 3)) <|
  padd (pneg (pmul (pmul (pmul (pmul (pc 12) m) (padd m (pc 1)))
      (pIntPoly m [18, 1907, 9048, 14262, 8355, 1270])) (ppow D 2)))
    (padd (pmul (pmul (pmul (pmul (pc 120) m) (padd m (pc 1)))
        (pIntPoly m [-2, 9, 264, 786, 789, 254])) D)
      (pneg (pmul (pmul (pmul (pc 4) m) (padd m (pc 1)))
        (pIntPoly m [-2, -103, 348, 4062, 7425, 3810]))))

/-- The raw endpoint in its exact reflected polynomial representation. -/
def thetaCubicEvenRawEndpoint (D m : Q') : Q' :=
  RingNormaliser.eval (fun | 0 => D | _ => m)
    (pEvenRawEndpoint (.var 0) (.var 1))

theorem thetaCubicEvenRawEndpoint_eq_formula (D m : Q') :
    thetaCubicEvenRawEndpoint D m ≈ thetaCubicEvenRawFormula D m := by
  simp only [thetaCubicEvenRawEndpoint, thetaCubicEvenRawFormula,
    pEvenRawEndpoint, evenR5, evenR4, evenR3, evenR2, evenR1, evenR0,
    pIntPoly, qIntPoly, pc, padd, pmul, pneg, ppow, RingNormaliser.eval]
  exact Q'.eqv_refl _

private theorem antiderivative_eq_local (D X : Q') :
    thetaCubicCellAntiderivative D X ≈
      RingNormaliser.eval (fun | 0 => D | _ => X)
        (pAntiderivative (.var 0) (.var 1)) := by
  unfold thetaCubicCellAntiderivative
  exact Q'.eqv_refl _

private def pEvenEndpointL : PE :=
  let D : PE := .var 0
  let m : PE := .var 1
  psub (pAntiderivative D (padd (pmul (pc 2) m) (pc 1)))
    (pAntiderivative D m)

private def pEvenEndpointR : PE :=
  pEvenRawEndpoint (.var 0) (.var 1)

private theorem pEvenEndpoint_normal :
    RingNormaliser.normalize pEvenEndpointL =
      RingNormaliser.normalize pEvenEndpointR := by decide

/-- Exact raw even endpoint identity, with `D` still independent. -/
theorem thetaCubicEvenEndpoint_eq_raw (D m : Q') :
    thetaCubicCellAntiderivative D (Q'.ofNat 2 * m + 1) +
        -thetaCubicCellAntiderivative D m ≈
      thetaCubicEvenRawEndpoint D m := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    pEvenEndpointL pEvenEndpointR pEvenEndpoint_normal
    (fun | 0 => D | _ => m)
  have hx : Q'.ofNat 2 * m + 1 ≈
      Q'.ofInt 2 * m + Q'.ofInt 1 := by
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ m (by decide)) (by decide)
  have htop0 := thetaCubicCellAntiderivative_eqv_congr
    (Q'.eqv_refl D) hx
  have htop1 := antiderivative_eq_local D (Q'.ofInt 2 * m + Q'.ofInt 1)
  have hbot := antiderivative_eq_local D m
  have hleft :
      thetaCubicCellAntiderivative D (Q'.ofNat 2 * m + 1) +
          -thetaCubicCellAntiderivative D m ≈
        RingNormaliser.eval (fun | 0 => D | _ => m) pEvenEndpointL := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ htop0 htop1)
        (Q'.neg_eqv_congr _ _ hbot)) ?_
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _ _ _ hleft ?_
  refine Q'.eqv_trans _ _ _ h ?_
  unfold thetaCubicEvenRawEndpoint pEvenEndpointR
  exact Q'.eqv_refl _

private def oddR5 (m : Q') : Q' := qIntPoly m [51, 131, 98]
private def oddR4 (m : Q') : Q' :=
  qIntPoly m [2925, 12337, 18514, 12108, 2976]
private def oddR3 (m : Q') : Q' :=
  qIntPoly m [1525, 8473, 17986, 18212, 8864, 1680]
private def oddR2 (m : Q') : Q' :=
  qIntPoly m [2100, 12259, 26184, 25032, 10295, 1270]
private def oddR1 (m : Q') : Q' :=
  qIntPoly m [84, 601, 1608, 2016, 1177, 254]
private def oddR0 (m : Q') : Q' :=
  qIntPoly m [420, 3569, 11604, 17892, 13245, 3810]

/-- `210` times the full cleared odd-centre block `n=m,...,2m+1`,
before imposing the relation between `D` and `m`. -/
def thetaCubicOddRawFormula (D m : Q') : Q' :=
  -(Q'.ofInt 840 * (m + Q'.ofInt 2) * RingNormaliser.qpow D 6) +
    (Q'.ofInt 140 * (m + Q'.ofInt 2) * oddR5 m * RingNormaliser.qpow D 5 +
      (-(Q'.ofInt 7 * (m + Q'.ofInt 2) * oddR4 m * RingNormaliser.qpow D 4) +
        (Q'.ofInt 21 * (m + Q'.ofInt 2) * oddR3 m * RingNormaliser.qpow D 3 +
          (-(Q'.ofInt 12 * (m + Q'.ofInt 1) * (m + Q'.ofInt 2) *
              oddR2 m * RingNormaliser.qpow D 2) +
            (Q'.ofInt 120 * (m + Q'.ofInt 1) * (m + Q'.ofInt 2) * oddR1 m * D +
              -(Q'.ofInt 4 * (m + Q'.ofInt 1) * (m + Q'.ofInt 2) * oddR0 m))))))

private def pOddRawEndpoint (D m : PE) : PE :=
  padd (pneg (pmul (pmul (pc 840) (padd m (pc 2))) (ppow D 6))) <|
  padd (pmul (pmul (pmul (pc 140) (padd m (pc 2)))
      (pIntPoly m [51, 131, 98])) (ppow D 5)) <|
  padd (pneg (pmul (pmul (pmul (pc 7) (padd m (pc 2)))
      (pIntPoly m [2925, 12337, 18514, 12108, 2976])) (ppow D 4))) <|
  padd (pmul (pmul (pmul (pc 21) (padd m (pc 2)))
      (pIntPoly m [1525, 8473, 17986, 18212, 8864, 1680])) (ppow D 3)) <|
  padd (pneg (pmul (pmul (pmul (pmul (pc 12) (padd m (pc 1)))
      (padd m (pc 2)))
      (pIntPoly m [2100, 12259, 26184, 25032, 10295, 1270])) (ppow D 2)))
    (padd (pmul (pmul (pmul (pmul (pc 120) (padd m (pc 1)))
        (padd m (pc 2)))
        (pIntPoly m [84, 601, 1608, 2016, 1177, 254])) D)
      (pneg (pmul (pmul (pmul (pc 4) (padd m (pc 1)))
        (padd m (pc 2)))
        (pIntPoly m [420, 3569, 11604, 17892, 13245, 3810]))))

def thetaCubicOddRawEndpoint (D m : Q') : Q' :=
  RingNormaliser.eval (fun | 0 => D | _ => m)
    (pOddRawEndpoint (.var 0) (.var 1))

theorem thetaCubicOddRawEndpoint_eq_formula (D m : Q') :
    thetaCubicOddRawEndpoint D m ≈ thetaCubicOddRawFormula D m := by
  simp only [thetaCubicOddRawEndpoint, thetaCubicOddRawFormula,
    pOddRawEndpoint, oddR5, oddR4, oddR3, oddR2, oddR1, oddR0,
    pIntPoly, qIntPoly, pc, padd, pmul, pneg, ppow, RingNormaliser.eval]
  exact Q'.eqv_refl _

private def pOddEndpointL : PE :=
  let D : PE := .var 0
  let m : PE := .var 1
  psub (pAntiderivative D (padd (pmul (pc 2) m) (pc 2)))
    (pAntiderivative D m)

private def pOddEndpointR : PE := pOddRawEndpoint (.var 0) (.var 1)

private theorem pOddEndpoint_normal :
    RingNormaliser.normalize pOddEndpointL =
      RingNormaliser.normalize pOddEndpointR := by decide

/-- Exact raw odd endpoint identity, with `D` still independent. -/
theorem thetaCubicOddEndpoint_eq_raw (D m : Q') :
    thetaCubicCellAntiderivative D (Q'.ofNat 2 * m + 2) +
        -thetaCubicCellAntiderivative D m ≈
      thetaCubicOddRawEndpoint D m := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    pOddEndpointL pOddEndpointR pOddEndpoint_normal
    (fun | 0 => D | _ => m)
  have hx : Q'.ofNat 2 * m + 2 ≈
      Q'.ofInt 2 * m + Q'.ofInt 2 := by
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ m (by decide)) (by decide)
  have htop0 := thetaCubicCellAntiderivative_eqv_congr
    (Q'.eqv_refl D) hx
  have htop1 := antiderivative_eq_local D (Q'.ofInt 2 * m + Q'.ofInt 2)
  have hbot := antiderivative_eq_local D m
  have hleft :
      thetaCubicCellAntiderivative D (Q'.ofNat 2 * m + 2) +
          -thetaCubicCellAntiderivative D m ≈
        RingNormaliser.eval (fun | 0 => D | _ => m) pOddEndpointL := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ htop0 htop1)
        (Q'.neg_eqv_congr _ _ hbot)) ?_
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _ _ _ hleft ?_
  refine Q'.eqv_trans _ _ _ h ?_
  unfold thetaCubicOddRawEndpoint pOddEndpointR
  exact Q'.eqv_refl _

#print axioms qIntPoly
#print axioms thetaCubicEvenRawFormula
#print axioms thetaCubicEvenRawEndpoint
#print axioms thetaCubicEvenRawEndpoint_eq_formula
#print axioms thetaCubicEvenEndpoint_eq_raw
#print axioms thetaCubicOddRawFormula
#print axioms thetaCubicOddRawEndpoint
#print axioms thetaCubicOddRawEndpoint_eq_formula
#print axioms thetaCubicOddEndpoint_eq_raw

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointRaw
